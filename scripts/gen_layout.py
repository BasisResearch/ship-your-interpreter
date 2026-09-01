#!/usr/bin/env python3
"""Generate Vsa/Sim/rows/LayoutGround.lean — the M6 Layout ground-truth decides.

The concrete refinement Layout (`Vsa.Sim.LayoutInstance.interpRunLayout`) and its
geometry constants (`interpRunEntry`/`interpRunCode`/`stackSL`/`spEntry`/…) were
hand-typed from `nm c/while-riscv-htif.elf`.  This generator re-reads the ELF
symbol table and EMITS the machine-checked tie: one `rfl`/`Iff.rfl` theorem per
constant, equating the Lean definition with the symbol value read from the binary
at generation time.  If the ELF and the Lean constants ever drift, the emitted
file fails to elaborate — the same ground-truth discipline as the decode table
(`experiments/gen_decode_table.py`, the model for this generator).

Self-verification (MANDATORY — the genseg lesson): after emitting, the script
runs `lake env lean` on the file and greps the output for `sorryAx` and errors;
it exits nonzero (and says so) unless the file is green and axiom-clean.

Usage: python3 scripts/gen_layout.py [--no-verify]
"""
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ELF = os.path.join(ROOT, 'c', 'while-riscv-htif.elf')
OUT = os.path.join(ROOT, 'Vsa', 'Sim', 'rows', 'LayoutGround.lean')
OUT_JT = os.path.join(ROOT, 'Vsa', 'Sim', 'rows', 'LayoutJumpTableGen.lean')
OUT_VP = os.path.join(ROOT, 'Vsa', 'Sim', 'rows', 'LayoutVpTableGen.lean')

# --------------------------------------------------------------------------
# The `eval_expr` `.rodata` jump table (M6 dispatch): base `0x80019f58`, one
# 4-byte little-endian slot per `ExprKind` tag (`c/src/ast.h` enum, 11 tags).
# The dispatch reads slot `k` at `base + 4*k`, then jumps to
# `base + (Int32) slot`.  This generator reads the slot bytes out of the ELF
# `.rodata` at generation time, computes each arm PC, CROSS-CHECKS the ones
# already pinned elsewhere in the proof (the two known generator bug classes:
# a false `decide` → sorryAx, and a zero-pinned / drifted byte read), and emits
# one `KindSlotPinned k armPC m` theorem per tag so every arm gets its 9
# dispatch bytes from ONE generator run (`EvalSimCommon.KindSlotPinned`).
# --------------------------------------------------------------------------
JUMP_TABLE_BASE = 0x80019f58

# `ExprKind` tag -> C name (c/src/ast.h: EX_INT..EX_FN, 11 tags 0..10).
TAG_NAMES = ['EX_INT', 'EX_STR', 'EX_BOOL', 'EX_NULL', 'EX_VAR', 'EX_ASSIGN',
             'EX_BINARY', 'EX_LOGICAL', 'EX_UNARY', 'EX_CALL', 'EX_FN']
NTAGS = len(TAG_NAMES)

# Cross-check anchors: arm PCs already pinned in the proof (grep for
# `KindSlotPinned <k> (0x…` / the per-kind `*SlotPinned` theorems).  A drift
# here means the ELF changed or a byte read is wrong — hard-abort.
EXPECTED_ARM_PC = {
    0: 0x80003408,   # EvalSimCommon.int_slot_kindPinned
    1: 0x80003414,   # EvalStrSim.StrSlotPinned
    2: 0x80003420,   # EvalBoolSim.BoolSlotPinned
    3: 0x8000342c,   # EvalNullSim.NullSlotPinned
    4: 0x80003434,   # EvalVarSim.VarSlotPinned
    7: 0x8000355c,   # EvalLogical (KindSlotPinned 7)
    8: 0x800035e0,   # EvalUnary  (KindSlotPinned 8)
    9: 0x800031b0,   # EvalCall   callArmPC
    10: 0x800033c4,  # FnArmSeams.AllocBuildStagingLink.hpc (the EX_FN arm front)
}


def parse_objdump_s(text):
    """`objdump -s` hex dump -> {addr: byte}."""
    mem = {}
    line_re = re.compile(r'^ ([0-9a-f]{4,16}) ')
    for line in text.splitlines():
        m = line_re.match(line)
        if not m:
            continue
        addr = int(m.group(1), 16)
        data = line[m.end():m.end() + 36]  # 4 groups of 8 hex chars + spaces
        for g in range(4):
            chunk = data[g * 9:g * 9 + 8]
            for k in range(4):
                pair = chunk[2 * k:2 * k + 2] if len(chunk) >= 2 * k + 2 else ''
                if re.fullmatch(r'[0-9a-f]{2}', pair):
                    mem[addr + g * 4 + k] = int(pair, 16)
    return mem


def read_jump_table(elf):
    """Read the 11 dispatch slots out of `.rodata`, compute each arm PC, and
    cross-check the known anchors.  Returns [(k, [b0,b1,b2,b3], arm_pc)]."""
    text = subprocess.run(['objdump', '-s', '--section=.rodata', elf],
                          check=True, capture_output=True, text=True).stdout
    mem = parse_objdump_s(text)
    slots = []
    for k in range(NTAGS):
        bs = []
        for i in range(4):
            a = JUMP_TABLE_BASE + 4 * k + i
            b = mem.get(a)
            if b is None:
                sys.exit(f'gen_layout.py: jump-table slot {k} byte @0x{a:x} '
                         f'absent from .rodata (zero-pinned-lds bug class)')
            bs.append(b)
        off = bs[0] | bs[1] << 8 | bs[2] << 16 | bs[3] << 24
        if off & 0x80000000:          # sign-extend the 32-bit offset
            off -= 0x100000000
        arm_pc = (JUMP_TABLE_BASE + off) & 0xffffffffffffffff
        exp = EXPECTED_ARM_PC.get(k)
        if exp is not None and arm_pc != exp:
            sys.exit(f'gen_layout.py: jump-table slot {k} ({TAG_NAMES[k]}) '
                     f'computed arm PC 0x{arm_pc:x} != expected 0x{exp:x} '
                     f'(ELF drift or bad byte read); aborting')
        slots.append((k, bs, arm_pc))
    return slots


def emit_jump_table(slots):
    lines = []
    for k, bs, arm_pc in slots:
        byte_hs = ' '.join(f'{b:02x}' for b in bs)
        prem = '\n'.join(
            f'    (h{i} : m[(jumpTableBase + 4 * {k} + {i} : Nat)]? '
            f'= some (0x{bs[i]:02x} : BitVec 8))' for i in range(4))
        wits = ', '.join(f'0x{bs[i]:02x}#8' for i in range(4))
        lines.append(f'''/-- `{TAG_NAMES[k]}` (tag {k}) jump-table slot @ `0x{JUMP_TABLE_BASE + 4*k:x}`:
bytes `{byte_hs}` (LE offset) → arm PC `0x{arm_pc:x}` = `jumpTableBase + (Int32)`.
Read from the ELF `.rodata` at generation time; the sign-extended reassembly is
machine-checked by `decide`. -/
theorem groundSlot_{k} {{m : Mem}}
{prem} :
    KindSlotPinned {k} (0x{arm_pc:x}#64) m :=
  ⟨{wits}, h0, h1, h2, h3, by
    apply BitVec.eq_of_toNat_eq; simp only [jumpTableBase]; decide⟩

#print axioms groundSlot_{k}
''')
    table_rows = '\n'.join(
        f'  {k:2d}  {TAG_NAMES[k]:9s}  0x{JUMP_TABLE_BASE + 4*k:x}  '
        f'{"".join(f"{b:02x} " for b in bs).strip()}  0x{arm_pc:x}'
        for k, bs, arm_pc in slots)
    body = '\n'.join(lines)
    return f'''import Vsa.Sim.EvalSimCommon

/-!
# `LayoutJumpTableGen` — the M6 `eval_expr` dispatch jump-table slot pins

GENERATED by `scripts/gen_layout.py` from `objdump -s --section=.rodata
c/while-riscv-htif.elf`.  DO NOT hand-edit — regenerate.

The `EX_*` dispatch reads a 4-byte offset from the `.rodata` jump table at
`jumpTableBase = 0x{JUMP_TABLE_BASE:x}`, slot `k` (the `ExprKind` tag, `c/src/ast.h`)
living at `jumpTableBase + 4*k`, then jumps to `jumpTableBase + (Int32) offset`.
This file emits ONE `EvalSimCommon.KindSlotPinned k armPC m` theorem per tag —
the per-arm dispatch coupling every leaf/arm row threads down to the Layout —
so a single generator run supplies all 11 arms' slot facts at once (each arm
consumes its `groundSlot_<k>` from its own 4 byte pins).

Slot table (tag, name, slot addr, LE bytes, arm PC), read from the fixed ELF:

{table_rows}

The arm PCs of the tags already pinned in the proof (int/str/bool/null/var/
logical/unary/call/fn) are cross-checked against their known values at
generation time (`EXPECTED_ARM_PC`); a drift hard-aborts the generator.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code

namespace Vsa.Sim.LayoutJumpTableGen

{body}
end Vsa.Sim.LayoutJumpTableGen
'''


# --------------------------------------------------------------------------
# The `value_print` `.rodata` jump table (per-value renderer dispatch): base
# `0x80019f10`, one 4-byte little-endian slot per `RuntimeRepr` kind tag
# (`c/src/value.c` enum, 6 tags 0..5 — null/bool/int/str/closure/native).  The
# dispatch head at `0x80002908` does `lwu a5,0(a0)` (the kind), then reads slot
# `k` at `base + 4*k` and jumps to `base + (Int32) slot` (the `jr a5`).  Mirror of
# the eval_expr table generator: read the slot bytes from `.rodata`, compute each
# arm PC, cross-check against `vpHandler`'s pinned arm PCs (a drift → hard-abort),
# and emit one `VpSlotPinned k armPC m` theorem per tag.
# --------------------------------------------------------------------------
VP_TABLE_BASE = 0x80019f10

# `RuntimeRepr` kind tag -> C name (c/src/value.c: null/bool/int/str/closure/native).
VP_TAG_NAMES = ['VP_NULL', 'VP_BOOL', 'VP_INT', 'VP_STR', 'VP_CLOSURE', 'VP_NATIVE']
VP_NTAGS = len(VP_TAG_NAMES)

# Cross-check anchors: the arm PCs pinned in `vpHandler`
# (`Vsa/Sim/rows/ValuePrintContract.lean`).  A drift means the ELF changed or a
# byte read is wrong — hard-abort.
VP_EXPECTED_ARM_PC = {
    0: 0x8000295c,   # null  → j fwrite
    1: 0x80002974,   # bool  → j fputs
    2: 0x80002990,   # int   → j fprintf
    3: 0x800029a4,   # str   → j fputs
    4: 0x80002928,   # closure → j fprintf
    5: 0x80002948,   # native → j fprintf
}


def read_table(elf, base, ntags, tag_names, expected):
    """Read `ntags` dispatch slots of a `.rodata` jump table at `base`, compute
    each arm PC, cross-check the anchors.  Returns [(k, [b0,b1,b2,b3], arm_pc)]."""
    text = subprocess.run(['objdump', '-s', '--section=.rodata', elf],
                          check=True, capture_output=True, text=True).stdout
    mem = parse_objdump_s(text)
    slots = []
    for k in range(ntags):
        bs = []
        for i in range(4):
            a = base + 4 * k + i
            b = mem.get(a)
            if b is None:
                sys.exit(f'gen_layout.py: table@0x{base:x} slot {k} byte @0x{a:x} '
                         f'absent from .rodata (zero-pinned-lds bug class)')
            bs.append(b)
        off = bs[0] | bs[1] << 8 | bs[2] << 16 | bs[3] << 24
        if off & 0x80000000:          # sign-extend the 32-bit offset
            off -= 0x100000000
        arm_pc = (base + off) & 0xffffffffffffffff
        exp = expected.get(k)
        if exp is not None and arm_pc != exp:
            sys.exit(f'gen_layout.py: table@0x{base:x} slot {k} ({tag_names[k]}) '
                     f'computed arm PC 0x{arm_pc:x} != expected 0x{exp:x} '
                     f'(ELF drift or bad byte read); aborting')
        slots.append((k, bs, arm_pc))
    return slots


def emit_vp_table(slots):
    lines = []
    for k, bs, arm_pc in slots:
        byte_hs = ' '.join(f'{b:02x}' for b in bs)
        prem = '\n'.join(
            f'    (h{i} : m[(vpJumpTableBase + 4 * {k} + {i} : Nat)]? '
            f'= some (0x{bs[i]:02x} : BitVec 8))' for i in range(4))
        wits = ', '.join(f'0x{bs[i]:02x}#8' for i in range(4))
        lines.append(f'''/-- `{VP_TAG_NAMES[k]}` (tag {k}) value_print jump-table slot @ `0x{VP_TABLE_BASE + 4*k:x}`:
bytes `{byte_hs}` (LE offset) → arm PC `0x{arm_pc:x}` = `vpJumpTableBase + (Int32)`.
Read from the ELF `.rodata` at generation time; the sign-extended reassembly is
machine-checked by `decide`. -/
theorem vpGroundSlot_{k} {{m : Mem}}
{prem} :
    VpSlotPinned {k} (0x{arm_pc:x}#64) m :=
  ⟨{wits}, h0, h1, h2, h3, by
    apply BitVec.eq_of_toNat_eq; simp only [vpJumpTableBase]; decide⟩

#print axioms vpGroundSlot_{k}
''')
    table_rows = '\n'.join(
        f'  {k:2d}  {VP_TAG_NAMES[k]:10s}  0x{VP_TABLE_BASE + 4*k:x}  '
        f'{"".join(f"{b:02x} " for b in bs).strip()}  0x{arm_pc:x}'
        for k, bs, arm_pc in slots)
    body = '\n'.join(lines)
    return f'''import Vsa.Sim.EvalSimCommon

/-!
# `LayoutVpTableGen` — the `value_print` dispatch jump-table slot pins

GENERATED by `scripts/gen_layout.py` from `objdump -s --section=.rodata
c/while-riscv-htif.elf`.  DO NOT hand-edit — regenerate.

`value_print`'s dispatch head (`0x80002908`) reads a 4-byte offset from the
`.rodata` jump table at `vpJumpTableBase = 0x{VP_TABLE_BASE:x}`, slot `k` (the
`RuntimeRepr` kind tag, `c/src/value.c`) living at `vpJumpTableBase + 4*k`, then
jumps (`jr a5`) to `vpJumpTableBase + (Int32) offset`.  This file emits ONE
`VpSlotPinned k armPC m` theorem per tag — the per-kind dispatch coupling the
`value_print` dispatch seg threads down to memory — so a single generator run
supplies all 6 arms' slot facts (each kind consumes its `vpGroundSlot_<k>` from
its own 4 byte pins).  Mirrors `LayoutJumpTableGen` (the eval_expr table).

Slot table (tag, name, slot addr, LE bytes, arm PC), read from the fixed ELF:

{table_rows}

The arm PCs are cross-checked against `vpHandler`'s pinned values
(`VP_EXPECTED_ARM_PC`) at generation time; a drift hard-aborts the generator.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code

namespace Vsa.Sim.LayoutVpTableGen

/-- The `value_print` `.rodata` jump-table base `0x{VP_TABLE_BASE:x}`. -/
def vpJumpTableBase : Nat := 0x{VP_TABLE_BASE:x}

/-- `VpSlotPinned k armPC m` — the four bytes of `value_print` jump-table slot `k`
in `m` are `t0..t3`, and their sign-extended little-endian reassembly plus the
table base equals the kind's landing arm PC `armPC` (`= vpHandler v` for the value
`v` of kind `k`).  The `value_print` analogue of `EvalSimCommon.KindSlotPinned`
(different table base `0x{VP_TABLE_BASE:x}`, 6 tags). -/
def VpSlotPinned (k : Nat) (armPC : BitVec 64) (m : Mem) : Prop :=
  ∃ t0 t1 t2 t3 : BitVec 8,
    m[(vpJumpTableBase + 4 * k + 0 : Nat)]? = some t0 ∧
    m[(vpJumpTableBase + 4 * k + 1 : Nat)]? = some t1 ∧
    m[(vpJumpTableBase + 4 * k + 2 : Nat)]? = some t2 ∧
    m[(vpJumpTableBase + 4 * k + 3 : Nat)]? = some t3 ∧
    (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))
      + BitVec.ofNat 64 vpJumpTableBase) = armPC

{body}
end Vsa.Sim.LayoutVpTableGen
'''


# The symbols the concrete Layout instantiation pins (LayoutInstance.lean).
SYMBOLS = ['interp_run', 'main', 'eval_expr', 'exec_stmt', 'runtime_error',
           '_exit', '__stack_top', '__stack_size', 'tohost']


def read_symbols(elf):
    out = subprocess.run(['nm', elf], check=True, capture_output=True, text=True).stdout
    vals = {}
    for line in out.splitlines():
        m = re.match(r'^([0-9a-fA-F]+)\s+\S\s+(\S+)$', line.strip())
        if m and m.group(2) in SYMBOLS:
            vals[m.group(2)] = int(m.group(1), 16)
    missing = [s for s in SYMBOLS if s not in vals]
    if missing:
        sys.exit(f'gen_layout.py: symbols missing from {elf}: {missing}')
    return vals


def hx(n):
    return f'0x{n:x}'


def emit(vals):
    interp_run = vals['interp_run']
    main = vals['main']
    stack_top = vals['__stack_top']
    stack_size = vals['__stack_size']
    return f'''import Vsa.Sim.LayoutInstance

/-!
# `LayoutGround` — the M6 Layout constants tied to the ELF ground truth

GENERATED by `scripts/gen_layout.py` from `nm c/while-riscv-htif.elf`.
DO NOT hand-edit — regenerate.

One theorem per concrete Layout constant (`Vsa/Sim/LayoutInstance.lean`),
equating the Lean definition with the symbol value read from the fixed binary at
generation time.  A drift between the ELF and the hand-typed constants makes
this file fail to elaborate.  `ground_atInterpRun` additionally pins the SHAPE
of the concrete refinement `Layout`'s program-point predicate — the entry PC and
the `(a0, a1)` AST-array ABI — against the `interp_run` symbol address.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.Sim.LayoutInstance

namespace Vsa.Sim.LayoutGround

/-- `interp_run` = `{hx(interp_run)}` (ELF symbol table). -/
theorem ground_interpRunEntry : interpRunEntry = {hx(interp_run)} := rfl

/-- `interp_run` code region `[{hx(interp_run)}, {hx(main)})` (up to `main`). -/
theorem ground_interpRunCode :
    interpRunCode = ({hx(interp_run)}, {hx(main)} - {hx(interp_run)}) := rfl

/-- `eval_expr` = `{hx(vals['eval_expr'])}` (ELF symbol table). -/
theorem ground_evalExprEntry : evalExprEntry = {hx(vals['eval_expr'])} := rfl

/-- `exec_stmt` = `{hx(vals['exec_stmt'])}` (ELF symbol table). -/
theorem ground_execStmtEntry : execStmtEntry = {hx(vals['exec_stmt'])} := rfl

/-- `runtime_error` = `{hx(vals['runtime_error'])}` (ELF symbol table). -/
theorem ground_runtimeErrorEntry : runtimeErrorEntry = {hx(vals['runtime_error'])} := rfl

/-- `_exit` = `{hx(vals['_exit'])}` (ELF symbol table). -/
theorem ground_exitEntry : exitEntry = {hx(vals['_exit'])} := rfl

/-- The C-stack region `[__stack_top - __stack_size, __stack_top)` =
`[{hx(stack_top - stack_size)}, {hx(stack_top)})` (linker symbols). -/
theorem ground_stackSL :
    stackSL = {{ lo := {hx(stack_top - stack_size)}, hi := {hx(stack_top)} }} := rfl

/-- The entry stack pointer `__stack_top` = `{hx(stack_top)}`. -/
theorem ground_spEntry : spEntry = {hx(stack_top)} := rfl

/-- The HTIF `tohost` cell = `{hx(vals['tohost'])}` (ELF symbol table). -/
theorem ground_tohostAddr : Vsa.Sim.tohostAddr = {hx(vals['tohost'])} := rfl

/-- **The concrete refinement `Layout`'s program-point shape**, pinned to the
`interp_run` symbol: `interpRunLayout.atInterpRun c a n` is exactly
"PC = `{hx(interp_run)}`, `a0` = the AST-array base `a`, `a1` = the length `n`". -/
theorem ground_atInterpRun (c : Config) (a n : Nat) :
    interpRunLayout.atInterpRun c a n ↔
      (c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 {hx(interp_run)}) ∧
       c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 a) ∧
       c.σ.regs.get? Register.x11 = some (BitVec.ofNat 64 n)) :=
  Iff.rfl

#print axioms ground_interpRunEntry
#print axioms ground_interpRunCode
#print axioms ground_evalExprEntry
#print axioms ground_execStmtEntry
#print axioms ground_runtimeErrorEntry
#print axioms ground_exitEntry
#print axioms ground_stackSL
#print axioms ground_spEntry
#print axioms ground_tohostAddr
#print axioms ground_atInterpRun

end Vsa.Sim.LayoutGround
'''


def write_if_changed(path, content):
    try:
        with open(path) as f:
            unchanged = f.read() == content
    except FileNotFoundError:
        unchanged = False
    if not unchanged:
        with open(path, 'w') as f:
            f.write(content)
    print(f'gen_layout.py: emitted {path} '
          f'({"unchanged" if unchanged else "updated"})')
    return unchanged


def self_verify(path, content):
    """MANDATORY self-verification (the genseg lesson): elaborate the emitted
    file, hard-error on any lean error, on `sorryAx` (false-decide bug class),
    on an axiom-audit count mismatch, or on an unexpected axiom."""
    r = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT,
                       capture_output=True, text=True)
    output = r.stdout + r.stderr
    if r.returncode != 0:
        print(output)
        sys.exit(f'gen_layout.py: SELF-VERIFY FAILED ({path}) — '
                 f'lake env lean errored')
    if 'sorryAx' in output:
        print(output)
        sys.exit(f'gen_layout.py: SELF-VERIFY FAILED ({path}) — '
                 f'sorryAx in axiom audit')
    audits = (output.count('depends on axioms')
              + output.count('does not depend on any axioms'))
    expected = content.count('#print axioms')
    if audits != expected:
        print(output)
        sys.exit(f'gen_layout.py: SELF-VERIFY FAILED ({path}) — {audits} '
                 f'axiom audits, expected {expected}')
    bad = [ln for ln in output.splitlines() if 'depends on axioms' in ln
           and not re.search(r"\[(propext, )?(Classical\.choice, )?(Quot\.sound)?\]|\[\]", ln)]
    if bad:
        print('\n'.join(bad))
        sys.exit(f'gen_layout.py: SELF-VERIFY FAILED ({path}) — '
                 f'unexpected axioms')
    print(f'gen_layout.py: self-verify OK ({path}: '
          f'{audits} axiom audits, no sorryAx)')


def main():
    vals = read_symbols(ELF)
    content = emit(vals)
    write_if_changed(OUT, content)
    for s in SYMBOLS:
        print(f'  {s:14s} = 0x{vals[s]:x}')

    slots = read_jump_table(ELF)
    content_jt = emit_jump_table(slots)
    write_if_changed(OUT_JT, content_jt)
    for k, bs, arm_pc in slots:
        print(f'  slot {k:2d} {TAG_NAMES[k]:9s} '
              f'{"".join(f"{b:02x} " for b in bs).strip():12s} -> 0x{arm_pc:x}')

    vp_slots = read_table(ELF, VP_TABLE_BASE, VP_NTAGS, VP_TAG_NAMES,
                          VP_EXPECTED_ARM_PC)
    content_vp = emit_vp_table(vp_slots)
    write_if_changed(OUT_VP, content_vp)
    for k, bs, arm_pc in vp_slots:
        print(f'  vp slot {k:2d} {VP_TAG_NAMES[k]:10s} '
              f'{"".join(f"{b:02x} " for b in bs).strip():12s} -> 0x{arm_pc:x}')

    if '--no-verify' in sys.argv[1:]:
        return
    self_verify(OUT, content)
    self_verify(OUT_JT, content_jt)
    self_verify(OUT_VP, content_vp)


if __name__ == '__main__':
    main()
