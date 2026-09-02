import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim

/-!
# Post-47i OBSTRUCTION — the amended `memExt` conjunct is STILL over-quantified.

The wave-47i amendment to the 6 unary/logical residuals (TermRouting.lean)
replaced the refuted `hMcallPop` oracle with a "honest pair":
  (presence) ∀ mcall agree-off-[SL.lo,sp) → bytes present on
             [sp-1120,sp) ∪ [aExpr+4,aExpr+8);
  (memExt)   ∀ mcall agree-off-[SL.lo,sp) → MemExtends m0 mcall.
Both are IDENTICAL across all 6 Resid and are the last two conjuncts each must
CONCLUDE from EvalEntry + operand facts.

This file machine-checks memExt is FALSE as stated: its ∀ ranges over EVERY
mem agreeing with m0 off [SL.lo,sp), including one DELETING an m0-defined byte
inside [SL.lo,sp). MemExtends demands m0-byte presence, so the deleting witness
refutes it. EvalEntry's pins on m0/SL/sp do NOT force [SL.lo,sp) empty, so this
survives the 47i entry-carry amendment (distinct from the pre-47i B2 sp_headroom
refutation, which the entry-carry DID fix).

CONSUMER (EvalNegSim3.lean:344): evalNegSim uses hMemExtRes only for the ONE
structured mcall from blockB_unary (writeMap-chain ⇒ MemExtends TRUE). Honest
amendment: carry the specific mcall's MemExtends as a field, not ∀-mcall.
-/

def MemExtProbe : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ mcall : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
      MemExtends m0 mcall

theorem memExtProbe_false : ¬ MemExtProbe := by
  intro h
  let SL : StackLayout := ⟨0, 1000000⟩
  let sp : BitVec 64 := 16#64
  let m0 : Mem := (∅ : Mem).insert 0 (0#8)
  let mcall : Mem := (∅ : Mem)
  have hsp : sp.toNat = 16 := by decide
  have hagree : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]? := by
    intro a ha
    have ha0 : (0 == a) = false := by
      by_cases he : 0 = a
      · exfalso; apply ha; rw [← he]
        exact ⟨Nat.le_refl 0, by show (0:Nat) < sp.toNat; rw [hsp]; decide⟩
      · simp [he]
    show mcall[a]? = m0[a]?
    rw [show (mcall[a]? : Option (BitVec 8)) = none from by
          simp only [mcall, Std.ExtHashMap.getElem?_empty]]
    rw [show (m0[a]? : Option (BitVec 8)) = none from by
          simp only [m0, Std.ExtHashMap.getElem?_insert, ha0]
          rw [if_neg (by decide), Std.ExtHashMap.getElem?_empty]]
  have hme := h SL sp m0 mcall hagree
  have hm00 : m0[0]? = some (0#8) := by
    show m0[0]? = some (0#8)
    simp only [m0, Std.ExtHashMap.getElem?_insert]; simp
  obtain ⟨b', hb'⟩ := hme 0 (0#8) hm00
  have hmc0 : (mcall[0]? : Option (BitVec 8)) = none := by
    show mcall[0]? = none; simp only [mcall, Std.ExtHashMap.getElem?_empty]
  rw [hmc0] at hb'
  exact absurd hb' (by simp)


#print axioms memExtProbe_false
