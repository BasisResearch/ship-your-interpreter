import Vsa.Compiler.RTBase

/-!
# Leaf runtime routines: truthiness and string printing

`run_tr`: `truthy` leaves `trW tag payload` in `a0`. `run_ps`: `printstr`
appends the characters of a string object to the console.
-/

namespace Vsa.Compiler

open Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- Truthiness of a value word pair. -/
def trW (t p : BitVec 64) : BitVec 64 :=
  if t = 0 then 0 else if t.toInt < 3 then (if p = 0 then 0 else 1) else 1

section
variable {code : List Ins} (hfit : Fits code)
include hfit

theorem run_tr (hseg : Seg code trPos (trCode trPos)) {L : GRegs} {m : Mem}
    {o : Array String} {t p r : BitVec 64}
    (h10 : Has L a0 t) (h11 : Has L a1 p) (hr : Has L ra r) (hal : r.toNat % 4 = 0) :
    Reaches code ⟨pcOf trPos, L, m, o⟩ (fun B => B.pc = r ∧ B.mem = m ∧ B.out = o ∧
      Has B.regs a0 (trW t p) ∧ Keep [t0, a0] L B.regs) := by
  have k10 := has_mem h10 (by decide); have k11 := has_mem h11 (by decide)
  have k1 := has_mem hr (by decide)
  have e10 := srcVal_of_has h10; have e11 := srcVal_of_has h11; have e1 := srcVal_of_has hr
  simp only [a0, a1, ra] at k10 k11 k1 e10 e11 e1
  have hK : ∀ v L', Keep [t0, a0] L L' → Keep [t0, a0] L (gset L' 10 v) :=
    fun v L' h => h.gset (by decide)
  have hF : ∀ L', Keep [t0, a0] L L' → trW t p = 0 →
      Reaches code ⟨pcOf 136, L', m, o⟩ (fun B => B.pc = r ∧ B.mem = m ∧ B.out = o ∧
        Has B.regs a0 (trW t p) ∧ Keep [t0, a0] L B.regs) := by
    intro L' hL' hz
    have k1' : 1 ∈ keysG L' := by
      rw [show (1 : Nat) = ra from rfl]; exact has_mem (hL'.has (by decide) hr) (by decide)
    have e1' : srcVal 1 L' = r := srcVal_of_has (hL'.has (r := ra) (by decide) hr)
    apply run_at' hfit hseg 8 136 rfl
    wp_simp [trCode, trPos, scPos, cpPos, itPos, psPos, k1', e1']
    refine ⟨hal, reach_here ⟨rfl, rfl, rfl, ?_, hK _ _ hL'⟩⟩
    rw [hz]; exact Has.set_self _ _ (by decide) (by decide)
  apply run_at' hfit hseg 0 trPos rfl
  wp_simp [trCode, trPos, scPos, cpPos, itPos, psPos, k10, k11, k1, e10, e11, e1]
  split
  · next ht => exact hF L (Keep.refl _ _) (by simp [trW, ht])
  · next ht =>
    split
    · next hlt =>
      apply run_at' hfit hseg 5 133 rfl
      wp_simp [trCode, trPos, scPos, cpPos, itPos, psPos, k10, k11, k1, e10, e11, e1]
      split
      · next hp =>
        exact hF _ ((Keep.refl _ _).gset (by decide))
          (by unfold trW; rw [if_neg ht, if_pos (by omega), if_pos hp])
      · next hp =>
        refine ⟨hal, reach_here ⟨rfl, rfl, rfl, ?_, hK _ _ ((Keep.refl _ _).gset (by decide))⟩⟩
        have : trW t p = 1 := by unfold trW; rw [if_neg ht, if_pos (by omega), if_neg hp]
        rw [this]; exact Has.set_self _ _ (by decide) (by decide)
    · next hlt =>
      refine ⟨hal, reach_here ⟨rfl, rfl, rfl, ?_, hK _ _ ((Keep.refl _ _).gset (by decide))⟩⟩
      have : trW t p = 1 := by unfold trW; rw [if_neg ht, if_neg (by omega)]
      rw [this]; exact Has.set_self _ _ (by decide) (by decide)

/-- Registers `printstr` may change. -/
def psClob : List Nat := [t0, t1, t2, s2, s3]

/-- The `printstr` loop head with `j` characters left. -/
def PsInv (L0 : GRegs) (m : Mem) (o : Array String) (p : Nat) (cs : List Char) (r : BitVec 64)
    (j : Nat) (A : AM) : Prop :=
  A.pc = pcOf 16 ∧ A.mem = m ∧ j ≤ cs.length ∧ Has A.regs t0 (BitVec.ofNat 64 j) ∧
    Has A.regs t1 (BitVec.ofNat 64 (p + 8 + 8 * (cs.length - j))) ∧ Has A.regs ra r ∧
    Keep psClob L0 A.regs ∧ ostr A.out = ostr o ++ String.ofList (cs.take (cs.length - j))

theorem run_ps (hseg : Seg code psPos (psCode psPos)) {L : GRegs} {m : Mem} {o : Array String}
    {p : Nat} {cs : List Char} {r : BitVec 64}
    (h11 : Has L a1 (BitVec.ofNat 64 p)) (hr : Has L ra r) (hal : r.toNat % 4 = 0)
    (hs : StrW m p cs) :
    Reaches code ⟨pcOf psPos, L, m, o⟩ (fun B => B.pc = r ∧ B.mem = m ∧
      ostr B.out = ostr o ++ String.ofList cs ∧ Keep psClob L B.regs) := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hlo := hs.lo; have hhi := hs.hi
  have hpn : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat]; omega
  -- the loop
  have hloop : ∀ j A, PsInv L m o p cs r j A → Reaches code A (fun B => B.pc = r ∧ B.mem = m ∧
      ostr B.out = ostr o ++ String.ofList cs ∧ Keep psClob L B.regs) := by
    refine loop_run (fun j A hA => ?_) (fun A hA => ?_)
    · obtain ⟨hpc, hm, hj, h5, h6, h1, hk, ho⟩ := hA
      obtain ⟨pc, L', m', o'⟩ := A
      simp only at hpc hm h5 h6 h1 hk ho; subst hpc hm
      have k5 := has_mem h5 (by decide); have k6 := has_mem h6 (by decide)
      have k1 := has_mem h1 (by decide)
      have e5 := srcVal_of_has h5; have e6 := srcVal_of_has h6; have e1 := srcVal_of_has h1
      simp only [t0, t1, ra] at k5 k6 k1 e5 e6 e1
      have hi : cs.length - (j + 1) < cs.length := by omega
      have hq : p + 8 + 8 * (cs.length - (j + 1)) < 2 ^ 64 := by omega
      have hqn : (BitVec.ofNat 64 (p + 8 + 8 * (cs.length - (j + 1)))).toNat
          = p + 8 + 8 * (cs.length - (j + 1)) := by rw [BitVec.toNat_ofNat]; omega
      have hc := hs.chars _ hi
      have hsm := hs.small _ (List.getElem_mem hi)
      have hpc : putcWord 0 + BitVec.ofNat 64 (cs[cs.length - (j + 1)]).toNat
          = putcWord (BitVec.ofNat 8 (cs[cs.length - (j + 1)]).toNat) := putcWord_add _ hsm
      have hj0 : BitVec.ofNat 64 (j + 1) ≠ 0 := by
        intro h; have := congrArg BitVec.toNat h; simp at this; omega
      apply run_at' hfit hseg 2 16 rfl
      wp_simp [psCode, psPos, putcR, hqn, hc, k5, k6, k1, e5, e6, e1, hpc, hj0]
      refine ⟨⟨by omega, by omega, .inr (by omega)⟩, reach_here ⟨rfl, rfl, by omega, ?_, ?_, ?_, ?_, ?_⟩⟩
      · exact Has.set_self _ _ (by decide) (by decide)
      · have e : p + 8 + 8 * (cs.length - (j + 1)) + 8 = p + 8 + 8 * (cs.length - j) := by omega
        rw [e]; exact (Has.set_self _ _ (by decide) (by decide)).set_other (by decide)
      · refine Keep.has (S := psClob) ?_ (by decide) h1
        refine (((((((Keep.refl _ _).gset ?_).gset ?_).gset ?_).gset ?_).gset ?_).gset ?_) <;> decide
      · refine (((((((hk.gset ?_).gset ?_).gset ?_).gset ?_).gset ?_).gset ?_)) <;> decide
      · rw [ostr_push, ho, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsm, Char.ofNat_toNat, toString_char,
          String.append_assoc, ← String.ofList_append]
        congr 2
        rw [show cs.length - j = cs.length - (j + 1) + 1 by omega, List.take_succ,
          List.getElem?_eq_getElem hi]
        rfl
    · obtain ⟨hpc, hm, hj, h5, h6, h1, hk, ho⟩ := hA
      obtain ⟨pc, L', m', o'⟩ := A
      simp only at hpc hm h5 h6 h1 hk ho; subst hpc hm
      have k5 := has_mem h5 (by decide); have k1 := has_mem h1 (by decide)
      have e5 := srcVal_of_has h5; have e1 := srcVal_of_has h1
      simp only [t0, ra] at k5 k1 e5 e1
      apply run_at' hfit hseg 2 16 rfl
      wp_simp [psCode, psPos, putcR, k5, k1, e5]
      apply run_at' hfit hseg 31 45 rfl
      wp_simp [psCode, psPos, k1, e1]
      refine ⟨hal, reach_here ⟨rfl, rfl, ?_, hk⟩⟩
      simpa using ho
  -- entry
  have k11 := has_mem h11 (by decide); have k1 := has_mem hr (by decide)
  have e11 := srcVal_of_has h11; have e1 := srcVal_of_has hr
  simp only [a1, ra] at k11 k1 e11 e1
  apply run_block hfit hseg 0 2 psPos rfl
    (KP := fun L' m' o' => PsInv L m o p cs r cs.length ⟨pcOf 16, L', m', o'⟩)
    (fun L' m' o' h => hloop _ _ h) (by simp [psCode])
  wp_simp [psCode, psPos, hpn, k11, k1, e11, e1, hs.len]
  refine ⟨⟨by omega, by omega, .inr (by omega)⟩, rfl, rfl, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Has.set_self _ _ (by decide) (by decide)).set_other (by decide)
  · simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    exact Has.set_self _ _ (by decide) (by decide)
  · exact ((hr.set_other (by decide)).set_other (by decide))
  · exact (((Keep.refl _ _).gset (by decide)).gset (by decide))
  · simp

end

end Vsa.Compiler
