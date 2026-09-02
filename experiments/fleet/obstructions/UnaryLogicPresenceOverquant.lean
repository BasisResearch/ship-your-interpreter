import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim

/-!
# Post-47i OBSTRUCTION — the amended `presence` conjunct is over-quantified too.
Companion to UnaryLogicMemExtOverquant.lean. The presence conjunct demands bytes
PRESENT in an arbitrary off-stack-agreeing mcall on [sp-1120,sp) ∪ [aExpr+4,+8);
[sp-1120,sp) ⊆ [SL.lo,sp) (the window mcall may zero), so an empty mcall refutes
it. Consumer needs it only for the structured post-call mcall (blockB wrote it);
∀-mcall discards that. Same amendment shape as memExt.
-/

-- The presence conjunct, isolated: for any mcall agreeing with m0 OFF [SL.lo,sp),
-- bytes are PRESENT on [sp-1120,sp) ∪ [aExpr+4,aExpr+8).  The [sp-1120,sp) window
-- ⊆ [SL.lo,sp) (the very window mcall may zero), so pick mcall empty there.
def PresProbe : Prop :=
  ∀ (SL : StackLayout) (sp aExpr : BitVec 64) (m0 : Mem),
    ∀ mcall : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
      ∀ a : Nat,
        (sp.toNat - 1120 ≤ a ∧ a < sp.toNat) ∨
          (aExpr.toNat + 4 ≤ a ∧ a < aExpr.toNat + 8) →
        (∃ b, mcall[a]? = some b)

theorem presProbe_false : ¬ PresProbe := by
  intro h
  -- SL.lo=0, sp=1120 (so [0,1120) is the window and sp-1120 = 0). aExpr huge so
  -- second disjunct picks a in-window addr 0. m0 arbitrary (empty), mcall empty.
  let SL : StackLayout := ⟨0, 1000000⟩
  let sp : BitVec 64 := 1120#64
  let aExpr : BitVec 64 := 0#64
  let m0 : Mem := (∅ : Mem)
  let mcall : Mem := (∅ : Mem)
  have hsp : sp.toNat = 1120 := by decide
  have hagree : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]? := by
    intro a _; rfl
  -- a = 0 ∈ [sp-1120, sp) = [0,1120)
  have hin : (sp.toNat - 1120 ≤ 0 ∧ 0 < sp.toNat) ∨
      (aExpr.toNat + 4 ≤ 0 ∧ 0 < aExpr.toNat + 8) := by
    left; rw [hsp]; exact ⟨by decide, by decide⟩
  obtain ⟨b, hb⟩ := h SL sp aExpr m0 mcall hagree 0 hin
  have : (mcall[0]? : Option (BitVec 8)) = none := by
    show mcall[0]? = none; simp only [mcall, Std.ExtHashMap.getElem?_empty]
  rw [this] at hb
  exact absurd hb (by simp)


#print axioms presProbe_false
