import Vsa.Elf

/-!
# Code byte pins for the static `"%lld"` format string (`LldFmtLoaded`)

The WHILE interpreter's `stringify` (int arm, `0x800030c0`) calls
`snprintf(buf, 64, "%lld", v)` with the format pointer `a2 = 0x800192c0` —
a `.rodata` string in `c/while-riscv-htif.elf`:

    800192c0  25 6c 6c 64 00 00 00 00      "%lld\0" (+ 3 padding zeros)

8 bytes pinned (the padding included so the whole `[vfmt, vfmt+8)` window the
svfprintf layout hypotheses quantify over is image-determined).
-/

namespace Vsa.Sim.Code

open Std

def lldFmtChunk0 (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x800192c0 : Nat)]? = some (0x25 : BitVec 8) ∧
  mem[(0x800192c1 : Nat)]? = some (0x6c : BitVec 8) ∧
  mem[(0x800192c2 : Nat)]? = some (0x6c : BitVec 8) ∧
  mem[(0x800192c3 : Nat)]? = some (0x64 : BitVec 8) ∧
  mem[(0x800192c4 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x800192c5 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x800192c6 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x800192c7 : Nat)]? = some (0x00 : BitVec 8)

def LldFmtLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop := lldFmtChunk0 mem

theorem lldFmt_bytes {mem : ExtHashMap Nat (BitVec 8)} (h : LldFmtLoaded mem) :
    mem[(0x800192c0 : Nat)]? = some (0x25 : BitVec 8) ∧
    mem[(0x800192c1 : Nat)]? = some (0x6c : BitVec 8) ∧
    mem[(0x800192c2 : Nat)]? = some (0x6c : BitVec 8) ∧
    mem[(0x800192c3 : Nat)]? = some (0x64 : BitVec 8) ∧
    mem[(0x800192c4 : Nat)]? = some (0x00 : BitVec 8) ∧
    mem[(0x800192c5 : Nat)]? = some (0x00 : BitVec 8) ∧
    mem[(0x800192c6 : Nat)]? = some (0x00 : BitVec 8) ∧
    mem[(0x800192c7 : Nat)]? = some (0x00 : BitVec 8) := h

end Vsa.Sim.Code
