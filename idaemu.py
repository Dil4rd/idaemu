#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import math
import recordclass
import enum

import idaapi
import ida_idaapi
import ida_name

from unicorn import *
from unicorn.x86_const import *
from unicorn.arm_const import *
from unicorn.arm64_const import *
from struct import unpack, pack, unpack_from, calcsize
from idc import get_qword, get_bytes, read_selection_start, read_selection_end, here, get_item_size
from ida_lines import generate_disasm_line, GENDSM_FORCE_CODE, GENDSM_MULTI_LINE, GENDSM_REMOVE_TAGS
from idautils import XrefsTo

PAGE_ALIGN = 0x1000  # 4k

COMPILE_GCC = 1
COMPILE_MSVC = 2

TRACE_OFF = 0
TRACE_DATA_READ = 1
TRACE_DATA_WRITE = 2
TRACE_CODE = 4

def target_to_ea(target):
    # convert target to address
    address = ida_idaapi.BADADDR
    if type(target) is str: 
        address = ida_name.get_name_ea(ida_idaapi.BADADDR, target)
    elif type(target) is int:
        address = target
    return address

class CpuExtensions(enum.IntFlag):
    ARM_VFP = 1

class MemRange(recordclass.RecordClass):
    address: int
    size: int

class Heap(object):
    def __init__(self, mem_range: MemRange, uc=None):
        self.mem_range = mem_range
        self.chunks_busy = {}
        self.chunks_free = {mem_range.address: mem_range.size}
        self.uc = None

    def _init_uc(self, uc):
        self.uc = uc

    def alloc(self, size: int) -> int:
        # round size to 8 byte border
        size = math.ceil(size/8) * 8
        # find free chunk of the same size
        addr = None
        for fchunk_addr, fchunk_size in self.chunks_free.items():
            if fchunk_size < size:
                continue
            addr = fchunk_addr
            del self.chunks_free[fchunk_addr]
            if fchunk_size > size:
                new_fchunk_addr = fchunk_addr + size
                new_fchunk_size = fchunk_size - size
                self.chunks_free[new_fchunk_addr] = new_fchunk_size
            break
        if addr is None:
            raise Exception(f"Heap: Can't allocated {size:d} bytes")
        self.chunks_busy[addr] = size
        return addr

    def alloc_bytes(self, content: bytes) -> int:
        addr = self.alloc(len(content))
        self.uc.mem_write(addr, content)
        return addr

    def calloc(self, size):
        addr = self.alloc(size)
        self.uc.mem_write(addr, b'\0'*size)
        return addr

    def free(self, addr):
        if addr not in self.chunks_busy.keys():
            raise Exception(f"Heap: trying to free unknown chunk at 0x{addr:x}")
        size = self.chunks_busy[addr]
        # TODO: heap defragmenation ??
        self.chunks_free[addr] = size
        del self.chunks_busy[addr]

class Emu(object):
    def __init__(self, arch, mode, compiler=COMPILE_GCC, \
                    stack=MemRange(0x0f000000, 3*PAGE_ALIGN), \
                    heap=MemRange(0x0e000000, 0x100*PAGE_ALIGN)):
        assert (arch in [UC_ARCH_X86, UC_ARCH_ARM, UC_ARCH_ARM64])
        self.arch = arch
        self.mode = mode
        self.compiler = compiler
        self.stack = stack
        self.heap = Heap(heap)
        self.data = []
        self.regs = []
        self.uc = None
        self.cpu_extensions = 0
        self.trace_option = TRACE_OFF
        self.trace_buf = []
        self.altFunc = {}
        self._init()

    def _add_trace(self, logInfo):
        self.trace_buf.append(logInfo)

    # callback for tracing invalid memory access (READ or WRITE, FETCH)
    def _hook_mem_invalid(self, uc, access, address, size, value, user_data):
        addr = self._align_addr(address)
        uc.mem_map(addr, PAGE_ALIGN)
        data = self._get_origin_data(addr, PAGE_ALIGN)
        uc.mem_write(addr, data)
        return True

    def _hook_mem_access(self, uc, access, address, size, value, user_data):
        if access == UC_MEM_WRITE and self.trace_option & TRACE_DATA_WRITE:
            self._add_trace("### Memory WRITE at 0x%x, data size = %u, data value = 0x%x" \
                           % (address, size, value))
        elif access == UC_MEM_READ and self.trace_option & TRACE_DATA_READ:
            self._add_trace("### Memory READ at 0x%x, data size = %u" \
                           % (address, size))

    def _hook_code(self, uc, address, size, user_data):
        if self.trace_option & TRACE_CODE:
            disasm = generate_disasm_line(address, GENDSM_FORCE_CODE|GENDSM_MULTI_LINE|GENDSM_REMOVE_TAGS)
            self._add_trace(f"### Trace instruction at address={address:#x}, size={size:d}:\t{disasm!s}")
        if address in self.altFunc.keys():
            func, argc, balance = self.altFunc[address]
            try:
                sp = uc.reg_read(self.REG_SP)
                if self.REG_RA is None:
                    RA = unpack(self.pack_fmt, str(uc.mem_read(sp, self.step)))[0]
                    sp += self.step
                else:
                    RA = uc.reg_read(self.REG_RA)

                args = []
                i = 0
                while i < argc and i < len(self.REG_ARGS):
                    args.append(uc.reg_read(self.REG_ARGS[i]))
                    i += 1
                sp2 = sp
                while i < argc:
                    args.append(unpack(self.pack_fmt, str(uc.mem_read(sp2, self.step)))[0])
                    sp2 += self.step
                    i += 1

                res = func(self, uc, args)
                if type(res) != int: res = 0
                uc.reg_write(self.REG_RES, res)
                uc.reg_write(self.REG_PC, RA)
                if balance:
                    uc.reg_write(self.REG_SP, sp2)
                else:
                    uc.reg_write(self.REG_SP, sp)
            except Exception as e:
                self._add_trace("alt exception: %s" % e)

    def _align_addr(self, addr):
        return addr // PAGE_ALIGN * PAGE_ALIGN

    def _get_origin_data(self, address, size):
        res = []
        for offset in range(0, size, 64):
            tmp = get_bytes(address + offset, 64)
            if tmp == None:
                res.extend([pack("<Q", get_qword(address + offset + i)) for i in range(0, 64, 8)])
            else:
                res.append(tmp)
        res = b''.join(res)
        return res[:size]

    def _init(self):
        if self.arch == UC_ARCH_X86:
            if self.mode == UC_MODE_16:
                self.step = 2
                self.pack_fmt = '<H'
                self.REG_PC = UC_X86_REG_IP
                self.REG_SP = UC_X86_REG_SP
                self.REG_RA = None
                self.REG_RES = UC_X86_REG_AX
                self.REG_ARGS = []
            elif self.mode == UC_MODE_32:
                self.step = 4
                self.pack_fmt = '<I'
                self.REG_PC = UC_X86_REG_EIP
                self.REG_SP = UC_X86_REG_ESP
                self.REG_RA = None
                self.REG_RES = UC_X86_REG_EAX
                self.REG_ARGS = []
            elif self.mode == UC_MODE_64:
                self.step = 8
                self.pack_fmt = '<Q'
                self.REG_PC = UC_X86_REG_RIP
                self.REG_SP = UC_X86_REG_RSP
                self.REG_RA = None
                self.REG_RES = UC_X86_REG_RAX
                if self.compiler == COMPILE_GCC:
                    self.REG_ARGS = [UC_X86_REG_RDI, UC_X86_REG_RSI, UC_X86_REG_RDX, UC_X86_REG_RCX,
                                     UC_X86_REG_R8, UC_X86_REG_R9]
                elif self.compiler == COMPILE_MSVC:
                    self.REG_ARGS = [UC_X86_REG_RCX, UC_X86_REG_RDX, UC_X86_REG_R8, UC_X86_REG_R9]
        elif self.arch == UC_ARCH_ARM:
            if self.mode == UC_MODE_ARM:
                self.step = 4
                self.pack_fmt = '<I'
            elif self.mode == UC_MODE_THUMB:
                self.step = 2
                self.pack_fmt = '<H'
            self.REG_PC = UC_ARM_REG_PC
            self.REG_SP = UC_ARM_REG_SP
            self.REG_RA = UC_ARM_REG_LR
            self.REG_RES = UC_ARM_REG_R0
            self.REG_ARGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
        elif self.arch == UC_ARCH_ARM64:
            self.step = 8
            self.pack_fmt = '<Q'
            self.REG_PC = UC_ARM64_REG_PC
            self.REG_SP = UC_ARM64_REG_SP
            self.REG_RA = UC_ARM64_REG_LR
            self.REG_RES = UC_ARM64_REG_X0
            self.REG_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2, UC_ARM64_REG_X3,
                             UC_ARM64_REG_X4, UC_ARM64_REG_X5, UC_ARM64_REG_X6, UC_ARM64_REG_X7]

    def _init_stack(self):
        stack_ea = self._align_addr(self.stack.address)
        self.uc.mem_map(stack_ea, (self.stack.size + 1) * PAGE_ALIGN)
        sp = stack_ea + self.stack.size * PAGE_ALIGN
        self.uc.reg_write(self.REG_SP, sp)

    def _init_heap(self):
        heap_ea = self.heap.mem_range.address
        self.uc.mem_map(heap_ea, self.heap.mem_range.size)
        self.heap._init_uc(self.uc)

    def _init_arg_value(self, arg):
        if type(arg) is int:
            return arg
        if type(arg) in (bytes, bytearray):
            return self.heap.alloc_bytes(bytes(arg))
        raise NotImplemented(f"Can't pass argument of type {type(arg)}")

    def _init_args(self, RA, args):
        # set return address
        if self.REG_RA is None:
            self.uc.mem_write(sp, pack(self.pack_fmt, RA))
        else:
            self.uc.reg_write(self.REG_RA, RA)

        # pass some arguments via regs
        i = 0
        while i < len(self.REG_ARGS) and i < len(args):
            self.uc.reg_write(self.REG_ARGS[i], self._init_arg_value(args[i]))
            i += 1
        # other arguments pass via stack
        while i < len(args):
            sp += self.step
            self.uc.mem_write(sp, pack(self.pack_fmt, self._init_arg_value(args[i])))
            i += 1

    def _get_bits(self, value, offset):
        mask = 1 << offset
        return 1 if (value & mask) > 0 else 0

    def _show_regs(self):
        print(">>> regs:")
        try:
            if self.arch == UC_ARCH_ARM:
                R0 = self.uc.reg_read(UC_ARM_REG_R0)
                R1 = self.uc.reg_read(UC_ARM_REG_R1)
                R2 = self.uc.reg_read(UC_ARM_REG_R2)
                R3 = self.uc.reg_read(UC_ARM_REG_R3)
                R4 = self.uc.reg_read(UC_ARM_REG_R4)
                R5 = self.uc.reg_read(UC_ARM_REG_R5)
                R6 = self.uc.reg_read(UC_ARM_REG_R6)
                R7 = self.uc.reg_read(UC_ARM_REG_R7)
                R8 = self.uc.reg_read(UC_ARM_REG_R8)
                R9 = self.uc.reg_read(UC_ARM_REG_R9)
                R10 = self.uc.reg_read(UC_ARM_REG_R10)
                R11 = self.uc.reg_read(UC_ARM_REG_R11)
                R12 = self.uc.reg_read(UC_ARM_REG_R12)
                SP = self.uc.reg_read(UC_ARM_REG_SP) # R13
                PC = self.uc.reg_read(UC_ARM_REG_PC)
                LR = self.uc.reg_read(UC_ARM_REG_LR)
                print("    R0 = 0x%x, R1 = 0x%x, R2 = 0x%x" % (R0, R1, R2))
                print("    R3 = 0x%x, R4 = 0x%x, R5 = 0x%x" % (R3, R4, R5))
                print("    R6 = 0x%x, R7 = 0x%x, R8 = 0x%x" % (R6, R7, R8))
                print("    R9 = 0x%x, R10 = 0x%x, R11 = 0x%x" % (R9, R10, R11))
                print("    R12 = 0x%x" % R12)
                print("    SP = 0x%x" % SP)
                print("    PC = 0x%x, LR = 0x%x" % (PC, LR))
            elif self.arch == UC_ARCH_ARM64:
                X0 = self.uc.reg_read(UC_ARM64_REG_X0)
                X1 = self.uc.reg_read(UC_ARM64_REG_X1)
                X2 = self.uc.reg_read(UC_ARM64_REG_X2)
                X3 = self.uc.reg_read(UC_ARM64_REG_X3)
                X4 = self.uc.reg_read(UC_ARM64_REG_X4)
                X5 = self.uc.reg_read(UC_ARM64_REG_X5)
                X6 = self.uc.reg_read(UC_ARM64_REG_X6)
                X7 = self.uc.reg_read(UC_ARM64_REG_X7)
                X8 = self.uc.reg_read(UC_ARM64_REG_X8)
                X9 = self.uc.reg_read(UC_ARM64_REG_X9)
                X10 = self.uc.reg_read(UC_ARM64_REG_X10)
                X11 = self.uc.reg_read(UC_ARM64_REG_X11)
                X12 = self.uc.reg_read(UC_ARM64_REG_X12)
                X13 = self.uc.reg_read(UC_ARM64_REG_X13)
                X14 = self.uc.reg_read(UC_ARM64_REG_X14)
                X15 = self.uc.reg_read(UC_ARM64_REG_X15)
                X16 = self.uc.reg_read(UC_ARM64_REG_X16)
                X17 = self.uc.reg_read(UC_ARM64_REG_X17)
                X18 = self.uc.reg_read(UC_ARM64_REG_X18)
                X19 = self.uc.reg_read(UC_ARM64_REG_X19)
                X20 = self.uc.reg_read(UC_ARM64_REG_X20)
                X21 = self.uc.reg_read(UC_ARM64_REG_X21)
                X22 = self.uc.reg_read(UC_ARM64_REG_X22)
                X23 = self.uc.reg_read(UC_ARM64_REG_X23)
                X24 = self.uc.reg_read(UC_ARM64_REG_X24)
                X25 = self.uc.reg_read(UC_ARM64_REG_X25)
                X26 = self.uc.reg_read(UC_ARM64_REG_X26)
                X27 = self.uc.reg_read(UC_ARM64_REG_X27)
                X28 = self.uc.reg_read(UC_ARM64_REG_X28)
                X29 = self.uc.reg_read(UC_ARM64_REG_X29)
                SP = self.uc.reg_read(UC_ARM64_REG_SP) # X30
                PC = self.uc.reg_read(UC_ARM64_REG_PC)
                LR = self.uc.reg_read(UC_ARM64_REG_LR)
                print("    X0 = 0x%x, X1 = 0x%x, X2 = 0x%x" % (X0, X1, X2))
                print("    X3 = 0x%x, X4 = 0x%x, X5 = 0x%x" % (X3, X4, X5))
                print("    X6 = 0x%x, X7 = 0x%x, X8 = 0x%x" % (X6, X7, X8))
                print("    X9 = 0x%x, X10 = 0x%x, X11 = 0x%x" % (X9, X10, X11))
                print("    X12 = 0x%x, X13 = 0x%x, X14 = 0x%x" % (X12, X13, X14))
                print("    X15 = 0x%x, X16 = 0x%x, X17 = 0x%x" % (X15, X16, X17))
                print("    X18 = 0x%x, X19 = 0x%x, X20 = 0x%x" % (X18, X19, X20))
                print("    X21 = 0x%x, X22 = 0x%x, X23 = 0x%x" % (X21, X22, X23))
                print("    X24 = 0x%x, X25 = 0x%x, X26 = 0x%x" % (X24, X25, X26))
                print("    X27 = 0x%x, X28 = 0x%x, X29 = 0x%x" % (X27, X28, X29))
                print("    SP = 0x%x" % SP)
                print("    PC = 0x%x, LR = 0x%x" % (PC, LR))
            elif self.arch == UC_ARCH_X86:
                eflags = None
                if self.mode == UC_MODE_16:
                    ax = self.uc.reg_read(UC_X86_REG_AX)
                    bx = self.uc.reg_read(UC_X86_REG_BX)
                    cx = self.uc.reg_read(UC_X86_REG_CX)
                    dx = self.uc.reg_read(UC_X86_REG_DX)
                    di = self.uc.reg_read(UC_X86_REG_SI)
                    si = self.uc.reg_read(UC_X86_REG_DI)
                    bp = self.uc.reg_read(UC_X86_REG_BP)
                    sp = self.uc.reg_read(UC_X86_REG_SP)
                    ip = self.uc.reg_read(UC_X86_REG_IP)
                    eflags = self.uc.reg_read(UC_X86_REG_EFLAGS)

                    print("    AX = 0x%x BX = 0x%x CX = 0x%x DX = 0x%x" % (ax, bx, cx, dx))
                    print("    DI = 0x%x SI = 0x%x BP = 0x%x SP = 0x%x" % (di, si, bp, sp))
                    print("    IP = 0x%x" % ip)
                elif self.mode == UC_MODE_32:
                    eax = self.uc.reg_read(UC_X86_REG_EAX)
                    ebx = self.uc.reg_read(UC_X86_REG_EBX)
                    ecx = self.uc.reg_read(UC_X86_REG_ECX)
                    edx = self.uc.reg_read(UC_X86_REG_EDX)
                    edi = self.uc.reg_read(UC_X86_REG_ESI)
                    esi = self.uc.reg_read(UC_X86_REG_EDI)
                    ebp = self.uc.reg_read(UC_X86_REG_EBP)
                    esp = self.uc.reg_read(UC_X86_REG_ESP)
                    eip = self.uc.reg_read(UC_X86_REG_EIP)
                    eflags = self.uc.reg_read(UC_X86_REG_EFLAGS)

                    print("    EAX = 0x%x EBX = 0x%x ECX = 0x%x EDX = 0x%x" % (eax, ebx, ecx, edx))
                    print("    EDI = 0x%x ESI = 0x%x EBP = 0x%x ESP = 0x%x" % (edi, esi, ebp, esp))
                    print("    EIP = 0x%x" % eip)
                elif self.mode == UC_MODE_64:
                    rax = self.uc.reg_read(UC_X86_REG_RAX)
                    rbx = self.uc.reg_read(UC_X86_REG_RBX)
                    rcx = self.uc.reg_read(UC_X86_REG_RCX)
                    rdx = self.uc.reg_read(UC_X86_REG_RDX)
                    rdi = self.uc.reg_read(UC_X86_REG_RSI)
                    rsi = self.uc.reg_read(UC_X86_REG_RDI)
                    rbp = self.uc.reg_read(UC_X86_REG_RBP)
                    rsp = self.uc.reg_read(UC_X86_REG_RSP)
                    rip = self.uc.reg_read(UC_X86_REG_RIP)
                    r8 = self.uc.reg_read(UC_X86_REG_R8)
                    r9 = self.uc.reg_read(UC_X86_REG_R9)
                    r10 = self.uc.reg_read(UC_X86_REG_R10)
                    r11 = self.uc.reg_read(UC_X86_REG_R11)
                    r12 = self.uc.reg_read(UC_X86_REG_R12)
                    r13 = self.uc.reg_read(UC_X86_REG_R13)
                    r14 = self.uc.reg_read(UC_X86_REG_R14)
                    r15 = self.uc.reg_read(UC_X86_REG_R15)
                    eflags = self.uc.reg_read(UC_X86_REG_EFLAGS)

                    print("    RAX = 0x%x RBX = 0x%x RCX = 0x%x RDX = 0x%x" % (rax, rbx, rcx, rdx))
                    print("    RDI = 0x%x RSI = 0x%x RBP = 0x%x RSP = 0x%x" % (rdi, rsi, rbp, rsp))
                    print("    R8 = 0x%x R9 = 0x%x R10 = 0x%x R11 = 0x%x R12 = 0x%x " \
                          "R13 = 0x%x R14 = 0x%x R15 = 0x%x" % (r8, r9, r10, r11, r12, r13, r14, r15))
                    print("    RIP = 0x%x" % rip)
                if eflags:
                    print("    EFLAGS:")
                    print("    CF=%d PF=%d AF=%d ZF=%d SF=%d TF=%d IF=%d DF=%d OF=%d IOPL=%d " \
                          "NT=%d RF=%d VM=%d AC=%d VIF=%d VIP=%d ID=%d"
                          % (self._get_bit(eflags, 0),
                             self._get_bit(eflags, 2),
                             self._get_bit(eflags, 4),
                             self._get_bit(eflags, 6),
                             self._get_bit(eflags, 7),
                             self._get_bit(eflags, 8),
                             self._get_bit(eflags, 9),
                             self._get_bit(eflags, 10),
                             self._get_bit(eflags, 11),
                             self._get_bit(eflags, 12) + self._get_bit(eflags, 13) * 2,
                             self._get_bit(eflags, 14),
                             self._get_bit(eflags, 16),
                             self._get_bit(eflags, 17),
                             self._get_bit(eflags, 18),
                             self._get_bit(eflags, 19),
                             self._get_bit(eflags, 20),
                             self._get_bit(eflags, 21)))
        except UcError as e:
            print("#ERROR: %s" % e)

    def _init_data(self):
        for address, data, init in self.data:
            addr = self._align_addr(address)
            size = PAGE_ALIGN
            while size < len(data): size += PAGE_ALIGN
            self.uc.mem_map(addr, size)
            if init: self.uc.mem_write(addr, self._get_origin_data(addr, size))
            self.uc.mem_write(address, data)

    def _init_platform_regs(self):
        if self.arch == UC_ARCH_ARM:
            if self.cpu_extensions & CpuExtensions.ARM_VFP:
                # FP/NEON support at EL1 (qemu and unicorn works on EL1)
                cpacr = self.uc.reg_read(UC_ARM64_REG_CPACR_EL1)
                self.uc.reg_write(UC_ARM64_REG_CPACR_EL1, cpacr|(3<<20)) # set FPEN bits
                ### set some flags, like at https://github.com/in7egral/idaemu
                regval = self.curUC.reg_read(UC_ARM_REG_C1_C0_2)
                regval |= (0xF << 20)
                self.curUC.reg_write(UC_ARM_REG_C1_C0_2, regval)
                self.curUC.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
        elif self.arch == UC_ARCH_ARM64:
            if self.cpu_extensions & CpuExtensions.ARM_VFP:
                # FP/NEON support at EL1 (qemu and unicorn works on EL1)
                cpacr = self.uc.reg_read(UC_ARM64_REG_CPACR_EL1)
                self.uc.reg_write(UC_ARM64_REG_CPACR_EL1, cpacr|(3<<20)) # set FPEN bits

    def _init_regs(self):
        self._init_platform_regs()
        #
        for reg, value in self.regs:
            self.uc.reg_write(reg, value)

    def _emulate(self, startAddr, stopAddr, args=[], timeout=0, count=0):
        try:
            # renew trace buffer and UC
            self.trace_buf = []
            self.uc = Uc(self.arch, self.mode)

            self._init_stack()
            self._init_heap()
            self._init_args(stopAddr, args)

            self._init_data()
            self._init_regs()

            # add the invalid memory access hook
            self.uc.hook_add(UC_HOOK_MEM_READ_UNMAPPED | UC_HOOK_MEM_WRITE_UNMAPPED | \
                        UC_HOOK_MEM_FETCH_UNMAPPED, self._hook_mem_invalid)

            # add the trace hook
            if self.trace_option & (TRACE_DATA_READ | TRACE_DATA_WRITE):
                self.uc.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, self._hook_mem_access)
            self.uc.hook_add(UC_HOOK_CODE, self._hook_code)

            # start emulate
            if self.mode == UC_MODE_THUMB:
                # Start at ADDRESS | 1 to indicate THUMB mode.
                uc.emu_start(startAddr | 1, stopAddr, timeout=timeout, count=count)
            else:
                uc.emu_start(startAddr, stopAddr, timeout=timeout, count=count)
        except UcError as e:
            print("#ERROR: %s" % e)

    # set data before emulation
    def set_data(self, address, data, init=False):
        self.data.append((address, data, init))

    # set registers before emulation
    def set_reg(self, reg, value):
        self.regs.append((reg, value))

    def show_regs(self, *regs):
        if self.uc == None:
            print("current uc is none.")
            return
        for reg in regs:
            print("0x%x" % self.uc.reg_read(reg))

    def read_stack(self, fmt, count):
        if self.uc == None:
            print("current uc is none.")
            return
        stackData = []
        stackPointer = self.uc.reg_read(self.REG_SP)
        for i in range(count):
            dataSize = calcsize(fmt)
            data = self.uc.mem_read(stackPointer + i * dataSize, dataSize)
            st = unpack_from(fmt, data)
            stackData.append((stackPointer + i * dataSize, st[0]))
        return stackData

    def show_data(self, fmt, addr, count=1):
        if self.uc == None:
            print("current uc is none.")
            return
        if count > 1: print('[')
        for i in range(count):
            dataSize = calcsize(fmt)
            data = self.uc.mem_read(addr + i * dataSize, dataSize)
            if count > 1: print('    ', end='')
            st = unpack_from(fmt, data)
            if count > 1: print(',')
        print(']') if count > 1 else print('')

    def set_trace(self, opt):
        if opt != TRACE_OFF:
            self.trace_option |= opt
        else:
            self.trace_option = TRACE_OFF

    def show_trace(self):
        logs = "\n".join(self.trace_buf)
        print(logs)

    def alt(self, target, func, argc, balance=False):
        """
        If call the target, will call the func instead.
        the arguments of func : func(emu, uc, args)
        """
        assert (callable(func))
        # convert target to address
        address = target_to_ea(target)
        # check target address
        if address == ida_idaapi.BADADDR:
            raise Exception(f"Wrong target: {target}")
        # add hook
        self.altFunc[address] = (func, argc, balance)

    def eFunc(self, target=None, retAddr=None, args=[]):
        if target == None: target = here()
        address = target_to_ea(target)
        func = idaapi.get_func(address)
        if retAddr == None:
            refs = [ref.frm for ref in XrefsTo(func.start_ea, 0)]
            if len(refs) != 0:
                retAddr = refs[0] + get_item_size(refs[0])
            else:
                print("Please offer the return address.")
                return
        self._emulate(func.start_ea, retAddr, args)
        res = self.uc.reg_read(self.REG_RES)
        return res

    def eBlock(self, codeStart=None, codeEnd=None):
        if codeStart == None: codeStart = read_selection_start()
        if codeEnd == None: codeEnd = read_selection_end()
        self._emulate(codeStart, codeEnd)
        self._show_regs()

    def eUntilAddress(self, startAddr, stopAddr, args=[], TimeOut=0, Count=0):
        self._emulate(startAddr=startAddr, stopAddr=stopAddr, args=args, TimeOut=TimeOut, Count=Count)
        self._show_regs()
