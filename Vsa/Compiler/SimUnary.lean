import Vsa.Compiler.SimComp

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem posOK_le {a b : Nat} (h : PosOK b) (hab : a ≤ b) : PosOK a := by unfold PosOK at *; omega

theorem EPost.regs {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env : Addr}
    {Γ : List (List String)} {sp fs k : Nat} {A : AM} {n : Nat} {st' : St} {v : Value} {V' : View}
    {B : AM} (hp : EPost code T V st d env Γ sp fs k A n st' v V' B) {pc : BitVec 64} {L' : GRegs}
    {S : List Nat} (hS : Scratch S) (hk : Keep S B.regs L') {w : Value} (hv : InA V'.H B.mem V'.h L' w)
    {n' : Nat} (hn : n ≤ n') :
    EPost code T V st d env Γ sp fs k A n' st' w V' ⟨pc, L', B.mem, B.out⟩ where
  ms := hp.ms.transport (B := ⟨pc, L', B.mem, B.out⟩) hS hk (Agree.refl _ _ _) (ObjAgree.refl _ _) rfl
  val := hv
  grow := hp.grow
  within := hp.within.mono hn
  stack := hp.stack
  obj := hp.obj

theorem trW_repr {H : CloMap} {m : Mem} {h : Nat} {v : Value} {t p : BitVec 64} (hv : VRepr H m h v t p) :
    trW t p = if v.truthy then 1 else 0 := by
  cases v with
  | null => obtain ⟨rfl, rfl⟩ := hv; rfl
  | bool b => obtain ⟨rfl, rfl⟩ := hv; cases b <;> rfl
  | int n =>
    obtain ⟨rfl, rfl, h1, h2⟩ := hv
    by_cases hn : n = 0
    · subst hn; decide
    · have : BitVec.ofInt 64 n ≠ 0 := fun e => hn (ofInt_inj ⟨h1, h2⟩ ⟨by decide, by decide⟩ (by rw [e]; rfl))
      unfold trW
      rw [if_neg (by decide), if_pos (by decide), if_neg this]
      simp [Value.truthy, hn]
  | str s => obtain ⟨rfl, -⟩ := hv; rfl
  | closure a => obtain ⟨rfl, -⟩ := hv; rfl
  | native f => obtain ⟨rfl, -⟩ := hv; rfl

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem sNeg {st : St} {d : Nat} {env : Addr} {e : Expr} {st' : St} {n : Int} {m : Nat}
    (hE : ESpec code T st d env e st' (.int n) m) :
    ESpec code T st d env (.unary .neg e) st' (.int (wrap64 (-n))) m := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp
  simp only [gexpr, errUnlessEq, List.append_assoc] at hseg hP ⊢
  obtain ⟨s1, s2⟩ := hseg.append
  simp only [List.length_append, List.length_cons, List.length_nil] at hP ⊢
  refine hE.bind hm hA hwf s1 (posOK_le hP (by omega)) (by simpa [tE] using htmp)
    (fun B h1 h2 => .inl ⟨h1, h2⟩) fun V1 B hpc hp => ?_
  obtain ⟨t, p, h10, h11, hv⟩ := hp.val
  obtain ⟨rfl, rfl, hI⟩ := hv
  obtain ⟨pc, L, mm, o⟩ := B
  simp only at hpc h10 h11; subst hpc
  have k10 := has_mem h10 (by decide); have e10 := srcVal_of_has h10
  have k11 := has_mem h11 (by decide); have e11 := srcVal_of_has h11
  simp only [a0, a1] at k10 e10 k11 e11
  apply run_whole hR.fits s2
  wp_simp [k10, e10, k11, e11]
  apply run_from hR.fits s2 3 _ (by omega) (by simp)
  wp_simp [k10, e10, k11, e11]
  refine reach_here (.inr ⟨by first | rfl | (congr 1; omega), V1, ?_⟩)
  refine hp.regs (S := [t0, a1]) (by decide) ?_ ?_ (Nat.le_refl _)
  · reg_simp []; exact Keep.refl _ _
  · refine ⟨2, 0 - BitVec.ofInt 64 n, by reg_simp []; exact h10, by reg_simp [], rfl, ?_, wrap64_range _⟩
    rw [ofInt_wrap64, BitVec.ofInt_neg]; simp

theorem sNot {st : St} {d : Nat} {env : Addr} {e : Expr} {st' : St} {v : Value} {m : Nat}
    (hE : ESpec code T st d env e st' v m) :
    ESpec code T st d env (.unary .not e) st' (.bool (!v.truthy)) m := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp
  simp only [gexpr, List.append_assoc] at hseg hP ⊢
  obtain ⟨s1, s2⟩ := hseg.append
  simp only [List.length_append, List.length_cons, List.length_nil] at hP ⊢
  refine hE.bind hm hA hwf s1 (posOK_le hP (by omega)) (by simpa [tE] using htmp)
    (fun B h1 h2 => .inl ⟨h1, h2⟩) fun V1 B hpc hp => ?_
  obtain ⟨t, p, h10, h11, hv⟩ := hp.val
  obtain ⟨pc, L, mm, o⟩ := B
  simp only at hpc h10 h11; subst hpc
  have hq : PosOK (pos + (gexpr T Γ k pos e).length + 1) := posOK_le hP (by omega)
  apply run_whole hR.fits s2
  wp_simp [hq]
  refine ex_bind (run_tr hR.fits hR.tr (L := gset L 1 (pcOf (pos + (gexpr T Γ k pos e).length + 1)))
    (m := mm) (o := o) (by reg_simp []; exact h10) (by reg_simp []; exact h11) (by reg_simp [])
    (pcOf_aligned hq)) ?_
  rintro ⟨pc2, L2, m2, o2⟩ ⟨hpc2, hm2, ho2, h10', hk2⟩
  simp only at hpc2 hm2 ho2 h10' hk2; subst hpc2 hm2 ho2
  have k10 := has_mem h10' (by decide); have e10 := srcVal_of_has h10'
  simp only [a0] at k10 e10
  apply run_from hR.fits s2 1 _ (by omega) (by simp)
  wp_simp [k10, e10]
  refine reach_here (.inr ⟨by first | rfl | (congr 1; omega), V1, ?_⟩)
  refine hp.regs (S := [1, t0, a0, a1]) (by decide) ?_ ?_ (Nat.le_refl _)
  · have := (Keep.gset (Keep.refl [1, t0, a0, a1] L) (v := pcOf (pos + (gexpr T Γ k pos e).length + 1))
      (by decide : 1 ∈ [1, t0, a0, a1])).trans (hk2.mono (by decide))
    reg_simp []; exact this
  · refine ⟨1, 1#64 - trW t p, by reg_simp [], by reg_simp [], rfl, ?_⟩
    rw [trW_repr hv]; cases v.truthy <;> rfl

end

end Vsa.Compiler
