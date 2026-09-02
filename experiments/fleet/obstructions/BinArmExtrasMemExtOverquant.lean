import Vsa.Sim.rows.BinArmBridge
open Vsa.MemRepr Vsa.Alloc Vsa.Sim Vsa.While
open LeanRV64DExecutable Sail Register

/-- The `BinArmExtras.mem_ext` conjunct, isolated as the same over-quant shape
prove-unary refuted for the unary residuals.  If FALSE, `BinIntCellResid`
(which packs a full `BinArmExtras`) is NOT entry-derivable — cure A as literally
stated (add EvalEntry hyp only) is insufficient; the `frame_pop`/`mem_ext`/`x13_pres`
closures must ALSO be dropped/threaded (same class as cure B). -/
def BinArmMemExtProbe : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ m : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m[a]? = m0[a]?) →
      MemExtends m0 m

theorem binArmMemExtProbe_false : ¬ BinArmMemExtProbe := by
  intro h
  let SL : StackLayout := ⟨0, 1000000⟩
  let sp : BitVec 64 := 16#64
  let m0 : Mem := (∅ : Mem).insert 0 (0#8)
  let m : Mem := (∅ : Mem)
  have hsp : sp.toNat = 16 := by decide
  have hagree : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m[a]? = m0[a]? := by
    intro a ha
    have ha0 : (0 == a) = false := by
      by_cases he : 0 = a
      · exfalso; apply ha; rw [← he]
        exact ⟨Nat.le_refl 0, by show (0:Nat) < sp.toNat; rw [hsp]; decide⟩
      · simp [he]
    show m[a]? = m0[a]?
    rw [show (m[a]? : Option (BitVec 8)) = none from by
          simp only [m, Std.ExtHashMap.getElem?_empty]]
    rw [show (m0[a]? : Option (BitVec 8)) = none from by
          simp only [m0, Std.ExtHashMap.getElem?_insert, ha0]
          rw [if_neg (by decide), Std.ExtHashMap.getElem?_empty]]
  have hme := h SL sp m0 m hagree
  have hm00 : m0[0]? = some (0#8) := by
    show m0[0]? = some (0#8); simp only [m0, Std.ExtHashMap.getElem?_insert]; simp
  obtain ⟨b', hb'⟩ := hme 0 (0#8) hm00
  have hmc0 : (m[0]? : Option (BitVec 8)) = none := by
    show m[0]? = none; simp only [m, Std.ExtHashMap.getElem?_empty]
  rw [hmc0] at hb'; exact absurd hb' (by simp)

#print axioms binArmMemExtProbe_false
