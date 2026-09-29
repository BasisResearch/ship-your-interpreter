import Vsa.Compiler.SimBin

/-!
# Forward simulation: short-circuit operators
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

/-- The value a short-circuit operator yields without its right operand. -/
def logShort : LogOp → Bool
  | .or => true
  | .and => false

theorem EPost.comp {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env : Addr}
    {Γ : List (List String)} {sp fs k : Nat} {A B B' C : AM} {n1 n2 : Nat} {st1 st2 : St} {v1 v2 : Value}
    {V1 V2 : View} (h1 : EPost code T V st d env Γ sp fs k A n1 st1 v1 V1 B)
    (h2 : EPost code T V1 st1 d env Γ sp fs k B' n2 st2 v2 V2 C) (hm : B'.mem = B.mem) :
    EPost code T V st d env Γ sp fs k A (n1 + n2) st2 v2 V2 C where
  ms := h2.ms
  val := h2.val
  grow := h1.grow.trans h2.grow
  within := h1.within.add h2.within
  stack := h1.stack.trans (hm ▸ h2.stack)
  obj := h1.obj.trans (hm ▸ h2.obj) h1.grow.le

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

/-- The left operand decides: `true || _` and `false && _`. -/
theorem sLogShort {op : LogOp} {st : St} {d : Nat} {env : Addr} {l r : Expr} {st1 : St} {lv : Value}
    {n : Nat} (hE : ESpec code T st d env l st1 lv n) (ht : lv.truthy = logShort op) :
    ESpec code T st d env (.logical op l r) st1 (.bool (logShort op)) n := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp
  obtain ⟨hwl, -⟩ := hwf
  simp only [tE] at htmp
  cases op
  all_goals
    simp only [gexpr, jmpIfNonzero, jmpIfZero, List.append_assoc] at hseg hP ⊢
    obtain ⟨s1, s2⟩ := hseg.append
    obtain ⟨s2, s3⟩ := s2.append
    obtain ⟨s3, s4⟩ := s3.append
    obtain ⟨s4, s5⟩ := s4.append
    obtain ⟨s5, s6⟩ := s5.append
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hP s3 s4 s5 s6 ⊢
    obtain ⟨X, hX⟩ : ∃ X, pos + (gexpr T Γ k pos l).length + 3 +
        (gexpr T Γ k (pos + (gexpr T Γ k pos l).length + 3) r).length = X := ⟨_, rfl⟩
    have s6 := s6.cast (pos' := X + 4) (by omega)
    refine hE.bind hm hA hwl s1 (posOK_le hP (by omega)) (by omega)
      (fun B h1 h2 => .inl ⟨h1, h2⟩) fun V1 B1 hpc1 hp1 => ?_
    obtain ⟨t1, q1, h10, h11, hv1⟩ := hp1.val
    obtain ⟨pc1, L1, m1, o1⟩ := B1
    simp only at hpc1 h10 h11 hv1; subst hpc1
    have hq1 : PosOK (pos + (gexpr T Γ k pos l).length + 1) := posOK_le hP (by omega)
    apply run_whole hR.fits s2
    wp_simp [hq1]
    refine ex_bind (run_tr hR.fits hR.tr (L := gset L1 1 (pcOf (pos + (gexpr T Γ k pos l).length + 1)))
      (m := m1) (o := o1) (by reg_simp []; exact h10) (by reg_simp []; exact h11) (by reg_simp [])
      (pcOf_aligned hq1)) ?_
    rintro ⟨pc2, L2, m2, o2⟩ ⟨hpc2, hm2, ho2, g10, hk2⟩
    simp only at hpc2 hm2 ho2 g10 hk2; subst hpc2 hm2 ho2
    rw [trW_repr hv1, ht] at g10
    have k10 := has_mem g10 (by decide); have e10 := srcVal_of_has g10
    simp only [a0] at k10 e10
    apply run_jumps hR.fits s3
    wp_simp [logShort, k10, e10]
    rw [hX]
    apply run_whole hR.fits s6
    wp_simp []
    refine reach_here (.inr ⟨?_, V1, hp1.regs (S := [1, t0, a0, a1]) (by decide) ?_ ?_ (Nat.le_refl _)⟩)
    · show pcOf _ = pcOf _; congr 1 <;> omega
    · reg_simp []; exact (Keep.gset (Keep.refl _ L1) (by decide)).trans (hk2.mono (by decide))
    · exact ⟨_, _, by reg_simp [], by reg_simp [] <;> rfl, rfl, rfl⟩

/-- Both operands run: `false || r` and `true && r`. -/
theorem sLogFull {op : LogOp} {st : St} {d : Nat} {env : Addr} {l r : Expr} {st1 st2 : St}
    {lv rv : Value} {nl nr : Nat} (hEl : ESpec code T st d env l st1 lv nl) (ht : lv.truthy = !logShort op)
    (hEr : ESpec code T st1 d env r st2 rv nr) :
    ESpec code T st d env (.logical op l r) st2 (.bool rv.truthy) (nl + nr) := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp
  obtain ⟨hwl, hwr⟩ := hwf
  simp only [tE] at htmp
  cases op
  all_goals
    simp only [gexpr, jmpIfNonzero, jmpIfZero, List.append_assoc] at hseg hP ⊢
    obtain ⟨s1, s2⟩ := hseg.append
    obtain ⟨s2, s3⟩ := s2.append
    obtain ⟨s3, s4⟩ := s3.append
    obtain ⟨s4, s5⟩ := s4.append
    obtain ⟨s5, s6⟩ := s5.append
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hP s3 s4 s5 s6 ⊢
    obtain ⟨Y, hY⟩ : ∃ Y, pos + (gexpr T Γ k pos l).length = Y := ⟨_, rfl⟩
    obtain ⟨X, hX⟩ : ∃ X, pos + (gexpr T Γ k pos l).length + 3 +
        (gexpr T Γ k (pos + (gexpr T Γ k pos l).length + 3) r).length = X := ⟨_, rfl⟩
    have s4 := s4.cast (pos' := pos + (gexpr T Γ k pos l).length + 3) (by omega)
    have s5 := s5.cast (pos' := X) (by omega)
    refine hEl.bind hm hA hwl s1 (posOK_le hP (by omega)) (by omega)
      (fun B h1 h2 => .inl ⟨h1, Room.not_mono h2 (by omega)⟩) fun V1 B1 hpc1 hp1 => ?_
    obtain ⟨t1, q1, h10, h11, hv1⟩ := hp1.val
    obtain ⟨pc1, L1, m1, o1⟩ := B1
    simp only at hpc1 h10 h11 hv1; subst hpc1
    have hq1 : PosOK (pos + (gexpr T Γ k pos l).length + 1) := posOK_le hP (by omega)
    apply run_whole hR.fits s2
    wp_simp [hq1]
    refine ex_bind (run_tr hR.fits hR.tr (L := gset L1 1 (pcOf (pos + (gexpr T Γ k pos l).length + 1)))
      (m := m1) (o := o1) (by reg_simp []; exact h10) (by reg_simp []; exact h11) (by reg_simp [])
      (pcOf_aligned hq1)) ?_
    rintro ⟨pc2, L2, m2, o2⟩ ⟨hpc2, hm2, ho2, g10, hk2⟩
    simp only at hpc2 hm2 ho2 g10 hk2; subst hpc2 hm2 ho2
    rw [trW_repr hv1, ht] at g10
    have k10 := has_mem g10 (by decide); have e10 := srcVal_of_has g10
    simp only [a0] at k10 e10
    apply run_jumps hR.fits s3
    wp_simp [logShort, k10, e10]
    have hmC := hp1.ms.transport (B := ⟨pcOf (pos + (gexpr T Γ k pos l).length + 3), L2, m2, o2⟩)
      (S := [1, t0, a0]) (by decide) ((Keep.gset (Keep.refl _ L1) (by decide)).trans (hk2.mono (by decide)))
      (Agree.refl _ _ _) (ObjAgree.refl _ _) rfl
    refine hEr.bind hmC rfl hwr s4 (posOK_le hP (by omega)) (by omega)
      (fun B h1 h2 => .inl ⟨h1, Room.not_within h2 hp1.within (by omega)⟩) fun V2 D hpc3 hp2 => ?_
    obtain ⟨t3, q3, g10', g11', hv2⟩ := hp2.val
    obtain ⟨pc3, L3, m3, o3⟩ := D
    simp only at hpc3 g10' g11' hv2; subst hpc3
    rw [hX]
    have hq2 : PosOK (X + 1) := posOK_le hP (by omega)
    apply run_whole hR.fits s5
    wp_simp [hq2]
    refine ex_bind (run_tr hR.fits hR.tr (L := gset L3 1 (pcOf (X + 1))) (m := m3) (o := o3)
      (by reg_simp []; exact g10') (by reg_simp []; exact g11') (by reg_simp []) (pcOf_aligned hq2)) ?_
    rintro ⟨pc4, L4, m4, o4⟩ ⟨hpc4, hm4, ho4, g10'', hk4⟩
    simp only at hpc4 hm4 ho4 g10'' hk4; subst hpc4 hm4 ho4
    rw [trW_repr hv2] at g10''
    have k10' := has_mem g10'' (by decide); have e10' := srcVal_of_has g10''
    simp only [a0] at k10' e10'
    apply run_from hR.fits s5 1 _ rfl (by simp)
    wp_simp [k10', e10']
    refine reach_here (.inr ⟨?_, V2, (hp1.comp hp2 rfl).regs (S := [1, t0, a0, a1]) (by decide) ?_ ?_
      (Nat.le_refl _)⟩)
    · show pcOf _ = pcOf _; congr 1 <;> omega
    · reg_simp []; exact (Keep.gset (Keep.refl _ L3) (by decide)).trans (hk4.mono (by decide))
    · refine ⟨1, if rv.truthy then 1 else 0, by reg_simp [], by reg_simp [], rfl, ?_⟩
      cases rv.truthy <;> rfl

end

end Vsa.Compiler
