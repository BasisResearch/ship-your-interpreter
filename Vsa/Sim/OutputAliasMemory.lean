import Vsa.MemRepr
import Vsa.Sim.Code.FixedImage

/-! Finite byte memories for the concrete Loaded-boundary audit. -/

namespace Vsa.Sim.OutputAliasLoaded

open Vsa.MemRepr

/-- Populate a finite interval with a byte function. The construction is used
symbolically; its lookup theorem avoids enumerating the whole RAM interval. -/
def finiteMemory (byte : Nat → BitVec 8) (base : Nat) : Nat → Mem
  | 0 => ∅
  | n + 1 => (finiteMemory byte base n).insert (base + n) (byte (base + n))

theorem finiteMemory_get (byte : Nat → BitVec 8) (base n a : Nat)
    (hlo : base ≤ a) (hhi : a < base + n) :
    (finiteMemory byte base n)[a]? = some (byte a) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [finiteMemory, Std.ExtHashMap.getElem?_insert]
    by_cases he : base + n = a
    · subst a
      simp
    · simp only [beq_iff_eq, he, ↓reduceIte]
      exact ih (by omega)

theorem finiteMemory_get_none (byte : Nat → BitVec 8) (base n a : Nat)
    (hout : a < base ∨ base + n ≤ a) :
    (finiteMemory byte base n)[a]? = none := by
  induction n with
  | zero => simp [finiteMemory]
  | succ n ih =>
    rw [finiteMemory, Std.ExtHashMap.getElem?_insert,
      if_neg (by simp only [beq_iff_eq]; omega)]
    exact ih (by omega)

/-- Little-endian reading directly from a byte function. -/
def byteRead (byte : Nat → BitVec 8) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (byte a).toNat + 256 * byteRead byte (a + 1) n

theorem finiteMemory_readLE (byte : Nat → BitVec 8) (base n a width : Nat)
    (hlo : base ≤ a) (hhi : a + width ≤ base + n) :
    readLE (finiteMemory byte base n) a width = some (byteRead byte a width) := by
  induction width generalizing a with
  | zero => rfl
  | succ width ih =>
    rw [readLE, finiteMemory_get byte base n a hlo (by omega)]
    simp only [bind, Option.bind]
    rw [ih (a + 1) (by omega) (by omega)]
    rfl

/-- All RAM bytes, including every stack byte, are present. -/
def ramMemory (byte : Nat → BitVec 8) : Mem :=
  finiteMemory byte 0x80000000 0x08000000

theorem ramMemory_get (byte : Nat → BitVec 8) (a : Nat)
    (hlo : 0x80000000 ≤ a) (hhi : a < 0x88000000) :
    (ramMemory byte)[a]? = some (byte a) :=
  finiteMemory_get byte _ _ a hlo hhi

theorem ramMemory_lookup (byte : Nat → BitVec 8) (a : Nat) :
    (ramMemory byte)[a]? =
      if 0x80000000 ≤ a ∧ a < 0x88000000 then some (byte a) else none := by
  split
  · rename_i h
    exact ramMemory_get byte a h.1 h.2
  · rename_i h
    exact finiteMemory_get_none byte _ _ a (by omega)

theorem ramMemory_readLE (byte : Nat → BitVec 8) (a width : Nat)
    (hlo : 0x80000000 ≤ a) (hhi : a + width ≤ 0x88000000) :
    readLE (ramMemory byte) a width = some (byteRead byte a width) :=
  finiteMemory_readLE byte _ _ a width hlo hhi

#print axioms finiteMemory_get
#print axioms finiteMemory_get_none
#print axioms ramMemory_lookup
#print axioms ramMemory_readLE

end Vsa.Sim.OutputAliasLoaded
