import Vsa.Compiler.SimBlock

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem run_cond {st : St} {d : Nat} {env : Addr} {c : Expr} {st1 : St} {v : Value} {n : Nat}
    (hE : ESpec code T st d env c st1 v n) {V : View} {C : GCtx} {sp fs pos tgt : Nat} {A : AM}
    (hm : MS code T V st d env C.Γ sp fs A) (hA : A.pc = pcOf pos) (hwf : WfE T C.Γ c)
    (hseg : Seg code pos (gexpr T C.Γ 0 pos c ++ [Call (pos + (gexpr T C.Γ 0 pos c).length) trPos] ++
      jmpIfZero (pos + (gexpr T C.Γ 0 pos c).length + 1) tgt))
    (hP : PosOK (pos + (gexpr T C.Γ 0 pos c).length + 3)) (htgt : PosOK tgt) (htmp : 16 + 16 * tE c ≤ fs) :
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      ∃ V1, SPost code T V st d env C sp fs (if v.truthy then pos + (gexpr T C.Γ 0 pos c).length + 3 else tgt)
        A n st1 .normal V1 B) := by
  obtain ⟨s12, s3⟩ := hseg.append
  obtain ⟨s1, s2⟩ := s12.append
  simp only [List.length_append, List.length_singleton] at s3
  refine hE.bind hm hA hwf s1 (posOK_le hP (by omega)) (by omega) (fun B h1 h2 => .inl ⟨h1, h2⟩)
    fun V1 B hpc hp => ?_
  obtain ⟨t, p, h10, h11, hv⟩ := hp.val
  obtain ⟨pc1, L1, m1, o1⟩ := B
  simp only at hpc h10 h11 hv; subst hpc
  have hq1 : PosOK (pos + (gexpr T C.Γ 0 pos c).length + 1) := posOK_le hP (by omega)
  apply run_whole hR.fits s2
  wp_simp [hq1]
  refine ex_bind (run_tr hR.fits hR.tr (L := gset L1 1 (pcOf (pos + (gexpr T C.Γ 0 pos c).length + 1)))
    (m := m1) (o := o1) (by reg_simp []; exact h10) (by reg_simp []; exact h11) (by reg_simp [])
    (pcOf_aligned hq1)) ?_
  rintro ⟨pc2, L2, m2, o2⟩ ⟨hpc2, hm2, ho2, g10, hk2⟩
  simp only at hpc2 hm2 ho2 g10 hk2; subst hpc2 hm2 ho2
  rw [trW_repr hv] at g10
  have k10 := has_mem g10 (by decide); have e10 := srcVal_of_has g10
  simp only [a0] at k10 e10
  have hk : Keep [1, t0, a0] L1 L2 := (Keep.gset (Keep.refl _ L1) (by decide)).trans (hk2.mono (by decide))
  have hmC := fun pc' => hp.ms.transport (B := ⟨pc', L2, m2, o2⟩) (S := [1, t0, a0]) (by decide) hk
    (Agree.refl _ _ _) (ObjAgree.refl _ _) rfl
  apply run_jumps hR.fits s3
  cases hvt : v.truthy
  · wp_simp [jmpIfZero, k10, e10, htgt, hvt]
    exact reach_here (.inr ⟨V1, ⟨by simp, hmC _⟩, hp.grow, hp.within, hp.stack, hp.obj⟩)
  · wp_simp [jmpIfZero, k10, e10, hP, hvt]
    exact reach_here (.inr ⟨V1, ⟨by simp, hmC _⟩, hp.grow, hp.within, hp.stack, hp.obj⟩)

end

end Vsa.Compiler
