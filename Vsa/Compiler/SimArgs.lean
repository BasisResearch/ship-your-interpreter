import Vsa.Compiler.SimDefs

/-!
# Forward simulation: argument lists
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem aNil (st : St) (d : Nat) (env : Addr) : ASpec code T st d env [] st [] 0 := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp hlen
  obtain ⟨pc, L, m, o⟩ := A
  simp only at hA; subst hA
  refine reach_here (.inr ⟨by simp [gargs], V, hm, fun j hj => by simp at hj, VGrow.refl _ _, Within.refl _ _,
    StackKeep.refl _ _ _ _, ObjAgree.refl _ _⟩)

theorem aCons {st : St} {d : Nat} {env : Addr} {e : Expr} {es : List Expr} {st1 st2 : St} {v : Value}
    {vs : List Value} {ne nes : Nat} (hE : ESpec code T st d env e st1 v ne)
    (hA : ASpec code T st1 d env es st2 vs nes) : ASpec code T st d env (e :: es) st2 (v :: vs) (ne + nes) := by
  intro V Γ sp fs k pos A hm hpc hwf hseg hP htmp hlen
  obtain ⟨hwe, hwes⟩ := hwf
  simp only [tArgs] at htmp
  simp only [List.length_cons] at hlen
  have hal := hm.stk.al
  have e4 : (storeTmp k).length = 4 := by simp [storeTmp]
  simp only [gargs, List.append_assoc] at hseg hP ⊢
  obtain ⟨s1, s2⟩ := hseg.append
  obtain ⟨s2, s3⟩ := s2.append
  simp only [List.length_append, e4] at hP s3 ⊢
  have s3 := s3.cast (pos' := pos + ((gexpr T Γ k pos e).length + 4)) (by omega)
  refine hE.bind hm hpc hwe s1 (posOK_le hP (by omega)) (by omega)
    (fun B h1 h2 => .inl ⟨h1, Room.not_mono h2 (by omega)⟩) fun V1 B1 hpc1 hp1 => ?_
  obtain ⟨t1, q1, h10, h11, hv1⟩ := hp1.val
  obtain ⟨pc1, L1, m1, o1⟩ := B1
  simp only at hpc1 h10 h11 hv1; subst hpc1
  refine run_storeTmp hR.fits s2 hp1.ms.hsp hp1.ms.stk (by omega) h10 h11 fun L2 hk2 => ?_
  obtain ⟨hmC, hoC⟩ := hp1.ms.stored (pc := pcOf (pos + (gexpr T Γ k pos e).length + 4)) (j := k) (by omega)
    (S := [t6]) (by decide) hk2 (t := t1) (p := q1)
  have hlt := InTmp.stored hv1 hal hoC
  refine reaches_pc (q' := pos + ((gexpr T Γ k pos e).length + 4)) (by omega) ?_
  refine ex_bind (hA V1 Γ sp fs (k + 1) _ _ hmC rfl hwes s3 (posOK_le hP (by omega)) (by omega) (by omega)) ?_
  rintro B (⟨h1, h2⟩ | ⟨h1, V2, hp2⟩)
  · exact reach_here (.inl ⟨h1, Room.not_within h2 hp1.within (by omega)⟩)
  · refine reach_here (.inr ⟨by rw [h1]; congr 1; omega, V2, ?_⟩)
    exact {
      ms := hp2.ms
      tmps := fun j hj => by
        cases j with
        | zero => exact hlt.grow hp2.grow.hpre hp2.obj hp2.grow.le hp2.stack (by omega) (by omega)
        | succ j =>
          have := hp2.tmps j (by simpa using hj)
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using this
      grow := hp1.grow.trans hp2.grow
      within := hp1.within.add hp2.within
      stack := hp1.stack.trans ((StackKeep.stored hal (Nat.le_refl _) (by omega)).trans (hp2.stack.mono (by omega)))
      obj := hp1.obj.trans (hoC.trans hp2.obj (Nat.le_refl _)) hp1.grow.le }

end

end Vsa.Compiler
