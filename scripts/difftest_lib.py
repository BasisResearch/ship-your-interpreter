#!/usr/bin/env python3
"""difftest_lib — shared machinery for differential-testing the BMC encoder.

`experiments/smt/DIFFTEST-PLAN.md`.  The encoder (`experiments/smt/ReflectSpan.lean`
+ `ReflectResiduals.lean`) says what the machine does across a span; the emulator
(`riscv-lean/lean_emulator`, the exact proof model) shows what it actually does.
This module holds the three things both sides are read through:

* `Image`  — the proof ELF's loaded bytes + an independent RISC-V decoder.  It is
  deliberately NOT the encoder's decoder: two decoders that agree is evidence,
  one decoder checked against itself is not.
* `Trace`  — the emulator's `--trace-all` rows (`LeanRiscv.traceLoop`).
* `EncTable` — the encoder's own per-instruction answer (`#emit_step_table`).
"""
import os
import re
import sys
from array import array

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROOF_ELF = os.path.join(ROOT, "c", "while-riscv-htif.elf")
BMC_DIR = os.path.join(ROOT, "experiments", "smt", "bmc")

M64 = (1 << 64) - 1


def sx(v, bits):
    """Sign-extend a `bits`-wide value to a Python int."""
    m = 1 << (bits - 1)
    return (v ^ m) - m


# ------------------------------------------------------------------ ELF image
class Image:
    """PT_LOAD bytes of an ELF64, addressed by virtual address."""

    def __init__(self, path):
        self.path = path
        b = open(path, "rb").read()
        self.raw = b
        rd = lambda o, n: int.from_bytes(b[o:o + n], "little")
        phoff = rd(0x20, 8)
        phentsize = rd(0x36, 2)
        phnum = rd(0x38, 2)
        self.segs = []
        for i in range(phnum):
            o = phoff + i * phentsize
            if rd(o, 4) == 1:  # PT_LOAD
                self.segs.append((rd(o + 0x10, 8), rd(o + 0x08, 8), rd(o + 0x20, 8)))
        self.entry = rd(0x18, 8)

    def byte(self, va):
        for v, off, sz in self.segs:
            if v <= va < v + sz:
                return self.raw[off + (va - v)]
        return 0

    def word(self, va):
        for v, off, sz in self.segs:
            if v <= va < v + sz and va + 4 <= v + sz:
                return int.from_bytes(self.raw[off + (va - v):off + (va - v) + 4], "little")
        return sum(self.byte(va + i) << (8 * i) for i in range(4))

    def mapped(self, va):
        return any(v <= va < v + sz for v, off, sz in self.segs)

    def text_bytes(self):
        """The bytes of the first PT_LOAD segment's [0x80000000, code_hi) range —
        used only to assert that a corpus ELF's code image is the proof ELF's."""
        v, off, sz = self.segs[0]
        return self.raw[off:off + sz]


# ------------------------------------------------------- independent decoder
class Ins:
    __slots__ = ("pc", "w", "op", "f3", "f7", "rd", "rs1", "rs2", "kind", "imm", "target")

    def __repr__(self):
        return f"<{self.kind} pc={self.pc:#x} rd={self.rd} rs1={self.rs1} rs2={self.rs2} imm={self.imm}>"


_LOADW = {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}
_STOREW = {0: 1, 1: 2, 2: 4, 3: 8}


def decode(pc, w):
    """A plain RISC-V RV64I decode, written against the ISA manual rather than
    against `Vsa/Sim/BlockDecode.lean`.  `kind` is a short mnemonic string."""
    i = Ins()
    i.pc, i.w = pc, w
    i.op = w & 0x7F
    i.f3 = (w >> 12) & 7
    i.f7 = (w >> 25) & 0x7F
    i.rd = (w >> 7) & 0x1F
    i.rs1 = (w >> 15) & 0x1F
    i.rs2 = (w >> 20) & 0x1F
    i.imm = 0
    i.target = None
    immI = sx((w >> 20) & 0xFFF, 12)
    immS = sx((((w >> 25) & 0x7F) << 5) | ((w >> 7) & 0x1F), 12)
    op, f3, f7 = i.op, i.f3, i.f7
    if op == 0x37:
        i.kind, i.imm = "lui", sx(w & 0xFFFFF000, 32)
    elif op == 0x17:
        i.kind, i.imm = "auipc", sx(w & 0xFFFFF000, 32)
    elif op == 0x6F:
        imm = (((w >> 31) & 1) << 20) | (((w >> 12) & 0xFF) << 12) | \
              (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3FF) << 1)
        i.kind, i.imm = "jal", sx(imm, 21)
        i.target = (pc + i.imm) & M64
    elif op == 0x67:
        i.kind, i.imm = "jalr", immI
    elif op == 0x63:
        imm = (((w >> 31) & 1) << 12) | (((w >> 7) & 1) << 11) | \
              (((w >> 25) & 0x3F) << 5) | (((w >> 8) & 0xF) << 1)
        i.kind = {0: "beq", 1: "bne", 4: "blt", 5: "bge", 6: "bltu", 7: "bgeu"}.get(f3, "b?")
        i.imm = sx(imm, 13)
        i.target = (pc + i.imm) & M64
    elif op == 0x03:
        i.kind = {0: "lb", 1: "lh", 2: "lw", 3: "ld", 4: "lbu", 5: "lhu", 6: "lwu"}.get(f3, "l?")
        i.imm = immI
    elif op == 0x23:
        i.kind = {0: "sb", 1: "sh", 2: "sw", 3: "sd"}.get(f3, "s?")
        i.imm = immS
    elif op == 0x13:
        i.imm = immI
        i.kind = {0: "addi", 2: "slti", 3: "sltiu", 4: "xori", 6: "ori", 7: "andi"}.get(f3)
        if f3 == 1:
            i.kind = "slli"
        elif f3 == 5:
            i.kind = "srli" if (w >> 26) == 0 else "srai"
        if i.kind is None:
            i.kind = "i?"
    elif op == 0x1B:
        i.imm = immI
        if f3 == 0:
            i.kind = "addiw"
        elif f3 == 1:
            i.kind = "slliw"
        elif f3 == 5:
            i.kind = "srliw" if f7 == 0 else "sraiw"
        else:
            i.kind = "iw?"
    elif op == 0x33:
        i.kind = {(0, 0): "add", (0, 0x20): "sub", (1, 0): "sll", (2, 0): "slt",
                  (3, 0): "sltu", (4, 0): "xor", (5, 0): "srl", (5, 0x20): "sra",
                  (6, 0): "or", (7, 0): "and"}.get((f3, f7), "r?")
    elif op == 0x3B:
        i.kind = {(0, 0): "addw", (0, 0x20): "subw", (1, 0): "sllw",
                  (5, 0): "srlw", (5, 0x20): "sraw"}.get((f3, f7), "rw?")
    elif op == 0x73:
        i.kind = "sys"
    else:
        i.kind = "?"
    return i


def is_call(i):
    return (i.kind == "jal" or i.kind == "jalr") and i.rd == 1


def is_ret(i):
    return i.kind == "jalr" and i.rd == 0 and i.rs1 == 1 and i.imm == 0


# ------------------------------------------------------------------- traces
MK_NONE, MK_LOAD, MK_STORE = 0, 1, 2


class Trace:
    """`--trace-all` rows from `LeanRiscv.traceLoop`, column-major.

    `regs[i*31 + (r-1)]` is register `r` (1..31) BEFORE step `i`; `x0` is zero and
    not stored.  `mk/mw/maddr/mpre/mpost` carry the memory operand when there is
    one."""

    def __init__(self, path, name=None):
        self.path = path
        self.name = name or os.path.basename(path)
        pc = array("Q"); npc = array("Q"); step = array("Q")
        regs = array("Q")
        mk = array("B"); mw = array("B")
        maddr = array("Q"); mpre = array("Q"); mpost = array("Q")
        self.fuel_out = False
        with open(path, "r") as f:
            for line in f:
                if not line.startswith("T\t"):
                    if line.startswith("TRACE-FUEL-OUT"):
                        self.fuel_out = True
                    continue
                fl = line.rstrip("\n").split("\t")
                step.append(int(fl[1]))
                pc.append(int(fl[2], 16))
                npc.append(int(fl[3], 16))
                for j in range(4, 35):
                    regs.append(int(fl[j], 16))
                if len(fl) > 35:
                    tag = fl[35]
                    mk.append(MK_LOAD if tag[0] == "L" else MK_STORE)
                    mw.append(int(tag[1:]))
                    maddr.append(int(fl[36], 16))
                    mpre.append(int(fl[37], 16))
                    mpost.append(int(fl[38], 16))
                else:
                    mk.append(MK_NONE); mw.append(0)
                    maddr.append(0); mpre.append(0); mpost.append(0)
        self.pc, self.npc, self.step = pc, npc, step
        self.regs = regs
        self.mk, self.mw, self.maddr, self.mpre, self.mpost = mk, mw, maddr, mpre, mpost
        self.n = len(pc)
        self.depth = None

    def reg(self, i, r):
        return 0 if r == 0 else self.regs[i * 31 + (r - 1)]

    def sp(self, i):
        return self.regs[i * 31 + 1]

    def ra(self, i):
        return self.regs[i * 31 + 0]

    def regs_at(self, i):
        base = i * 31
        return [0] + list(self.regs[base:base + 31])

    def compute_depth(self, img):
        """Shadow call depth, one entry per row: the depth BEFORE the row's step.

        A `jal`/`jalr` writing `ra` pushes; a `jalr x0, 0(ra)` pops.  `longjmp`
        (the interpreter's runtime-error path) unwinds without returning, so a
        row whose `npc` is not where the shadow stack expects resets the depth to
        the deepest frame whose return address matches.  That keeps every span
        instance frame-accurate even on the error corpus."""
        d = array("i", bytes(4 * self.n))
        stack = []
        cur = 0
        for i in range(self.n):
            d[i] = cur
            p = self.pc[i]
            ins = decode(p, img.word(p))
            if is_call(ins):
                stack.append((p + 4) & M64)
                cur += 1
            elif is_ret(ins):
                if stack:
                    stack.pop()
                cur = max(0, cur - 1)
            else:
                # a non-returning transfer that lands on a pending return address
                # (longjmp) unwinds to that frame
                nx = self.npc[i]
                if nx != (p + 4) & M64 and stack and nx in stack:
                    k = len(stack) - 1 - stack[::-1].index(nx)
                    del stack[k:]
                    cur = len(stack)
        self.depth = d
        return d


# --------------------------------------------------- the encoder's step table
class EncTable:
    """`#emit_step_table` output: pc -> (class, fields...)."""

    def __init__(self, path):
        self.rows = {}
        with open(path) as f:
            next(f)
            for line in f:
                fl = line.rstrip("\n").split("\t")
                self.rows[int(fl[0], 16)] = (fl[2], fl[3:])

    def get(self, pc):
        return self.rows.get(pc)


def read_tsv(path):
    with open(path) as f:
        hdr = f.readline().rstrip("\n").split("\t")
        out = []
        for line in f:
            if not line.strip():
                continue
            fl = line.rstrip("\n").split("\t")
            out.append(dict(zip(hdr, fl + [""] * (len(hdr) - len(fl)))))
        return out
