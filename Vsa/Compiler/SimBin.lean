import Vsa.Compiler.SimTmp

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem Room.not_mono {V : View} {n n' : Nat} (h : ¬ Room V n) (hn : n ≤ n') : ¬ Room V n' :=
  fun hr => h (hr.mono hn)

theorem Room.not_within {V V' : View} {n1 n2 n : Nat} (h : ¬ Room V' n2) (hw : Within V V' n1)
    (hn : n1 + n2 ≤ n) : ¬ Room V n := fun hr => h (Room.of_within hw (hr.mono hn))

theorem VGrow.heap {V : View} {s : Store} {h' : Nat} (hh : V.h ≤ h') : VGrow V s (V.withH h') s :=
  ⟨Grows.refl _ _, List.prefix_refl _, Nat.le_refl _, hh⟩

theorem ObjPtr.of_le {h h' : Nat} (hp : ObjPtr h) (hh : h ≤ h') (hr : h' ≤ objEnd) (hal : h' % 8 = 0) :
    ObjPtr h' := ⟨by have := hp.lo; omega, hr, hal⟩

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem sBinary {st : St} {d : Nat} {env : Addr} {op : BinOp} {l r : Expr} {st1 st2 : St}
    {lv rv v : Value} {nl nr : Nat} (hEl : ESpec code T st d env l st1 lv nl)
    (hEr : ESpec code T st1 d env r st2 rv nr) (hbin : binOpSem st2.store op lv rv = some v) :
    ESpec code T st d env (.binary op l r) st2 v (nl + nr + binOpCost st2.store op lv rv) := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp
  obtain ⟨hwl, hwr⟩ := hwf
  simp only [tE] at htmp
  have htl : 16 + 16 * (k + tE l) ≤ fs := by omega
  have htr : 16 + 16 * ((k + 1) + tE r) ≤ fs := by omega
  have htk : 16 + 16 * (k + 1) ≤ fs := by omega
  have hal := hm.stk.al
  have e4 : (storeTmp k).length = 4 := by simp [storeTmp]
  have e4' : (loadTmp k).length = 4 := by simp [loadTmp]
  simp only [gexpr, List.append_assoc] at hseg hP ⊢
  obtain ⟨s1, s2⟩ := hseg.append
  obtain ⟨s2, s3⟩ := s2.append
  obtain ⟨s3, s4⟩ := s3.append
  obtain ⟨s4, s5⟩ := s4.append
  obtain ⟨s5, s6⟩ := s5.append
  simp only [List.length_append, List.length_cons, List.length_nil, e4, e4', Nat.zero_add,
    Nat.reduceAdd] at hP s3 s4 s5 s6 ⊢
  obtain ⟨X, hX⟩ : ∃ X, pos + (gexpr T Γ k pos l).length + 4 +
      (gexpr T Γ (k + 1) (pos + (gexpr T Γ k pos l).length + 4) r).length = X := ⟨_, rfl⟩
  rw [hX] at s4 s5 s6 hP
  try rw [hX]
  have s6 := s6.cast (pos' := X + 6) (by omega)
  refine hEl.bind hm hA hwl s1 (posOK_le hP (by omega)) htl
    (fun B h1 h2 => .inl ⟨h1, Room.not_mono h2 (by omega)⟩) fun V1 B1 hpc1 hp1 => ?_
  obtain ⟨t1, q1, h10, h11, hv1⟩ := hp1.val
  obtain ⟨pc1, L1, m1, o1⟩ := B1
  simp only at hpc1 h10 h11 hv1; subst hpc1
  refine run_storeTmp hR.fits s2 hp1.ms.hsp hp1.ms.stk htk h10 h11 fun L2 hk2 => ?_
  obtain ⟨hmC, hoC⟩ := hp1.ms.stored (pc := pcOf (pos + (gexpr T Γ k pos l).length + 4)) htk
    (S := [t6]) (by decide) hk2 (t := t1) (p := q1)
  have hlt := InTmp.stored hv1 hal hoC
  refine hEr.bind hmC rfl hwr s3 (posOK_le hP (by omega)) htr
    (fun B h1 h2 => .inl ⟨h1, Room.not_within h2 hp1.within (by omega)⟩) fun V2 D hpc2 hp2 => ?_
  obtain ⟨t2, q2, g10, g11, hv2⟩ := hp2.val
  obtain ⟨pcD, LD, mD, oD⟩ := D
  simp only at hpc2 g10 g11 hv2; subst hpc2
  rw [hX]
  have hlt2 := hlt.grow hp2.grow.hpre hp2.obj hp2.grow.le hp2.stack (by omega) (by omega)
  have k10 := has_mem g10 (by decide); have e10 := srcVal_of_has g10
  have k11 := has_mem g11 (by decide); have e11 := srcVal_of_has g11
  simp only [a0, a1] at k10 e10 k11 e11
  apply run_whole hR.fits s4
  wp_simp [k10, e10, k11, e11]
  refine run_loadTmp hR.fits s5 (by reg_simp []; exact hp2.ms.hsp) hp2.ms.stk htk fun L3 hk3 g10' g11' => ?_
  have hops : Operands V2.H mD V2.h L3 lv rv (rdW mD (sp + 16 + 16 * k)) (rdW mD (sp + 16 + 16 * k + 8)) t2 q2 :=
    ⟨g10', g11', hk3.has (by decide) (by reg_simp []), hk3.has (by decide) (by reg_simp []), hlt2, hv2⟩
  refine reaches_pc (q' := X + 6) (by omega) ?_
  refine ex_bind (run_op hR (s := st2.store) hops s6 (posOK_le hP (by omega)) hbin
    (hk3.has (by decide) (by reg_simp []; exact hp2.ms.ho)) hp2.ms.img.ptr hp2.ms.img.fixed
    hp2.ms.img.fixedHi hp2.ms.rel.clo hp2.ms.rel.inj) ?_
  rintro ⟨pcE, LE, mE, oE⟩ ⟨hoE, hE⟩
  simp only at hoE hE; subst hoE
  rcases hE with ⟨hpcE, hov⟩ | ⟨hpcE, h', ret⟩
  · refine reach_here (.inl ⟨hpcE, fun hr => ?_⟩)
    have := hp1.within.2; have := hp2.within.2; have := hr.2
    omega
  · have hkE : Keep addClob LD LE :=
      Keep.trans (by reg_simp []; exact Keep.refl _ _) ((hk3.mono (by decide)).trans ret.keep)
    have hstep : HeapStep mD mE V2.h h' :=
      ⟨ret.grow, hp2.ms.img.ptr.of_le ret.grow ret.room ret.al, ret.frame⟩
    obtain ⟨hb1, hb2, hb3⟩ := hm.stk.bounds
    have hl : stackLo = objEnd := rfl
    refine reach_here (.inr ⟨by show pcE = _; rw [hpcE]; congr 1; omega, V2.withH h', ?_⟩)
    exact {
      ms := hp2.ms.heap (pc := pcE) hstep (S := addClob) (by decide) hkE ret.hp
      val := ret.val
      grow := hp1.grow.trans (hp2.grow.trans (VGrow.heap ret.grow))
      within := ⟨by have := hp1.within.1; have := hp2.within.1; simp only [View.withH]; omega,
        by have := hp1.within.2; have := hp2.within.2; have := ret.within; simp only [View.withH]; omega⟩
      stack := hp1.stack.trans ((StackKeep.stored hal (Nat.le_refl _) htk).trans
        ((hp2.stack.mono (by omega)).trans ⟨hstep.stack (by omega), hstep.stack (by omega)⟩))
      obj := hp1.obj.trans (hoC.trans (hp2.obj.trans hstep.obj hp2.grow.le) (Nat.le_refl _))
        hp1.grow.le }

end

end Vsa.Compiler
