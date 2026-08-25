-- twin_spec: generated from Vsa/Sim/Code/LldFmt.lean (sha256 d7334e24ea46)
-- twin_spec: delta scripts/deltas/fnfmt_from_lldfmt.json (sha256 cfe27865b3ba)
-- twin_spec: do not hand-edit; edit the delta and re-run scripts/twin_spec.py
import Vsa.Elf

/-!
# Code byte pins for the static `"<fn %s>"` format string (`FnFmtLoaded`)

The WHILE interpreter's `stringify` (closure arm, `interp.c`) calls
`snprintf(buf, sizeof buf, "<fn %s>", name)` — the format is a `.rodata`
string in `c/while-riscv-htif.elf`:

    800192c8  3c 66 6e 20 25 73 3e 00      "<fn %s>\0"

8 bytes pinned (the NUL included so the whole `[vfmt, vfmt+8)` window is
image-determined) for the closure-printing arm (M4 `Call`/closure stringify)
— the same consumer pattern as `LldFmtLoaded` (this module's twin source).
-/

namespace Vsa.Sim.Code

open Std

def fnFmtChunk0 (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x800192c8 : Nat)]? = some (0x3c : BitVec 8) ∧
  mem[(0x800192c9 : Nat)]? = some (0x66 : BitVec 8) ∧
  mem[(0x800192ca : Nat)]? = some (0x6e : BitVec 8) ∧
  mem[(0x800192cb : Nat)]? = some (0x20 : BitVec 8) ∧
  mem[(0x800192cc : Nat)]? = some (0x25 : BitVec 8) ∧
  mem[(0x800192cd : Nat)]? = some (0x73 : BitVec 8) ∧
  mem[(0x800192ce : Nat)]? = some (0x3e : BitVec 8) ∧
  mem[(0x800192cf : Nat)]? = some (0x00 : BitVec 8)

def FnFmtLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop := fnFmtChunk0 mem

theorem fnFmt_bytes {mem : ExtHashMap Nat (BitVec 8)} (h : FnFmtLoaded mem) :
    mem[(0x800192c8 : Nat)]? = some (0x3c : BitVec 8) ∧
    mem[(0x800192c9 : Nat)]? = some (0x66 : BitVec 8) ∧
    mem[(0x800192ca : Nat)]? = some (0x6e : BitVec 8) ∧
    mem[(0x800192cb : Nat)]? = some (0x20 : BitVec 8) ∧
    mem[(0x800192cc : Nat)]? = some (0x25 : BitVec 8) ∧
    mem[(0x800192cd : Nat)]? = some (0x73 : BitVec 8) ∧
    mem[(0x800192ce : Nat)]? = some (0x3e : BitVec 8) ∧
    mem[(0x800192cf : Nat)]? = some (0x00 : BitVec 8) := h

end Vsa.Sim.Code
