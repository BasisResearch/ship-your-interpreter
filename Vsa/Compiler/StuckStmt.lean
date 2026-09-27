import Vsa.Compiler.StuckCall

/-!
# Failure of statements

A statement (list) without an execution fails at its first part without an
execution. Loops go around with less fuel: a `while` iteration passes its
condition code, a `for` iteration its back jump, so each takes at least one
step before the loop is failed again (`IHn`).
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR
variable {n : Nat} {st : St} {d : Nat} {env : Addr}

omit hR in
theorem fExprS {e : Expr} (ih : EStuck code T n st d env e) : SStuck code T n st d env (.expr e) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp hne
  exact ih V C.Γ sp fs 0 pos A hm hA hwf hseg hP (by simpa [tS] using htmp)
    (fun ⟨st', v, D⟩ => hne ⟨st', _, .expr _ _ _ _ _ _ D⟩)

omit hR in
theorem fVarInit {x : String} {e : Expr} (ih : EStuck code T n st d env e) :
    SStuck code T n st d env (.varDecl x (some e)) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp hne
  simp only [gstmt] at hseg hP
  obtain ⟨s1, -⟩ := hseg.append
  simp only [List.length_append] at hP
  exact ih V C.Γ sp fs 0 pos A hm hA hwf.2 s1 (posOK_le hP (by omega)) (by simpa [tS] using htmp)
    (fun ⟨st', v, D⟩ => hne ⟨_, _, .varInit _ _ _ _ _ _ _ D⟩)

omit hR in
theorem fRet {e : Expr} (ih : EStuck code T n st d env e) : SStuck code T n st d env (.ret (some e)) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp hne
  simp only [gstmt] at hseg hP
  obtain ⟨s1, -⟩ := hseg.append
  simp only [List.length_append] at hP
  exact ih V C.Γ sp fs 0 pos A hm hA hwf s1 (posOK_le hP (by omega)) (by simpa [tS] using htmp)
    (fun ⟨st', v, D⟩ => hne ⟨_, _, .ret _ _ _ _ _ _ D⟩)

theorem fBlockS {ss : List Stmt} (ih : ∀ st env, QStuck code T n st d env ss) :
    SStuck code T n st d env (.block ss) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp hne
  obtain ⟨hL, hwss⟩ := hwf
  simp only [gstmt] at hseg hP
  obtain ⟨s12, -⟩ := hseg.append
  obtain ⟨s1, s2⟩ := s12.append
  have e4 : (enterFrame (frameNames [] ss) pos).length = 4 := rfl
  simp only [List.length_append, e4, List.length_singleton] at hP s2
  apply Fail.of_reaches
  refine ex_bind (run_enterFrame hR hm hA hL (frameNames_nodup _ _) s1 (posOK_le hP (by omega))) ?_
  rintro B (⟨h1, -⟩ | ⟨hpcB, hE⟩)
  · exact reach_here (fail_err hR h1)
  exact reach_here (ih _ _ _ (C.enter (frameNames [] ss)) sp fs _ B hE.ms hpcB hwss (hctx.enter _) s2
    (posOK_le hP (by omega)) (by simpa [tS] using htmp)
    (fun ⟨st', t, D⟩ => hne ⟨st', t, .block _ _ _ _ _ _ _ _ rfl D⟩))

theorem fIfNone {c : Expr} {t : Stmt} (ihc : ∀ st, EStuck code T n st d env c)
    (iht : ∀ st, SStuck code T n st d env t) : SStuck code T n st d env (.ifStmt c t none) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp hne
  obtain ⟨hwc, hwt, -⟩ := hwf
  simp only [tS] at htmp
  simp only [gstmt] at hseg hP
  obtain ⟨h5, -⟩ := hseg.append
  obtain ⟨h4, -⟩ := h5.append
  obtain ⟨hcond, sct⟩ := h4.append
  simp only [List.length_append, List.length_singleton, jmpIfZero, List.length_cons, List.length_nil] at sct hP
  have sct := sct.cast (pos' := pos + (gexpr T C.Γ 0 pos c).length + 3) (by omega)
  by_cases hec : HasE st d env c
  rotate_left
  · obtain ⟨s12, -⟩ := hcond.append
    obtain ⟨s1, -⟩ := s12.append
    exact ihc st V C.Γ sp fs 0 pos A hm hA hwc s1 (posOK_le hP (by omega)) (by omega) hec
  obtain ⟨st1, v, Dc⟩ := hec
  obtain ⟨nc, hE⟩ := spec_e hR (T := T) Dc
  cases hvt : v.truthy
  · exact absurd ⟨st1, .normal, .ifNone _ _ _ _ _ _ _ Dc hvt⟩ hne
  apply Fail.of_reaches
  refine ex_bind (run_cond hR hE hm hA hwc hcond (posOK_le hP (by omega)) (posOK_le hP (by omega)) (by omega)) ?_
  rintro B (⟨h1, -⟩ | ⟨V1, hp1⟩)
  · exact reach_here (fail_err hR h1)
  rw [hvt, if_pos rfl] at hp1
  obtain ⟨hpc1, hm1⟩ := hp1.out
  exact reach_here (iht st1 V1 C sp fs _ B hm1 hpc1 hwt hctx sct (posOK_le hP (by omega)) (by omega)
    (fun ⟨st2, t2, D⟩ => hne ⟨st2, t2, .ifTrue _ _ _ _ _ _ _ _ _ _ Dc hvt D⟩))

theorem fIfSome {c : Expr} {t e : Stmt} (ihc : ∀ st, EStuck code T n st d env c)
    (iht : ∀ st, SStuck code T n st d env t) (ihe : ∀ st, SStuck code T n st d env e) :
    SStuck code T n st d env (.ifStmt c t (some e)) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp hne
  obtain ⟨hwc, hwt, hwe⟩ := hwf
  simp only [tS] at htmp
  simp only [gstmt] at hseg hP
  obtain ⟨h5, sce⟩ := hseg.append
  obtain ⟨h4, -⟩ := h5.append
  obtain ⟨hcond, sct⟩ := h4.append
  simp only [List.length_append, List.length_singleton, jmpIfZero, List.length_cons, List.length_nil] at sct sce hP
  have sct := sct.cast (pos' := pos + (gexpr T C.Γ 0 pos c).length + 3) (by omega)
  have sce := sce.cast (pos' := pos + (gexpr T C.Γ 0 pos c).length + 3 + (gstmt T C (pos + (gexpr T C.Γ 0 pos c).length
    + 3) t).length + 1) (by omega)
  by_cases hec : HasE st d env c
  rotate_left
  · obtain ⟨s12, -⟩ := hcond.append
    obtain ⟨s1, -⟩ := s12.append
    exact ihc st V C.Γ sp fs 0 pos A hm hA hwc s1 (posOK_le hP (by omega)) (by omega) hec
  obtain ⟨st1, v, Dc⟩ := hec
  obtain ⟨nc, hE⟩ := spec_e hR (T := T) Dc
  apply Fail.of_reaches
  refine ex_bind (run_cond hR hE hm hA hwc hcond (posOK_le hP (by omega)) (posOK_le hP (by omega)) (by omega)) ?_
  rintro B (⟨h1, -⟩ | ⟨V1, hp1⟩)
  · exact reach_here (fail_err hR h1)
  cases hvt : v.truthy
  · rw [hvt] at hp1
    simp only [Bool.false_eq_true, if_false] at hp1
    obtain ⟨hpc1, hm1⟩ := hp1.out
    exact reach_here (ihe st1 V1 C sp fs _ B hm1 hpc1 hwe hctx sce (posOK_le hP (by omega)) (by omega)
      (fun ⟨st2, t2, D⟩ => hne ⟨st2, t2, .ifFalse _ _ _ _ _ _ _ _ _ _ Dc hvt D⟩))
  · rw [hvt, if_pos rfl] at hp1
    obtain ⟨hpc1, hm1⟩ := hp1.out
    exact reach_here (iht st1 V1 C sp fs _ B hm1 hpc1 hwt hctx sct (posOK_le hP (by omega)) (by omega)
      (fun ⟨st2, t2, D⟩ => hne ⟨st2, t2, .ifTrue _ _ _ _ _ _ _ _ _ _ Dc hvt D⟩))

theorem fWhile {c : Expr} {b : Stmt} (ihc : ∀ st, EStuck code T n st d env c)
    (ihb : ∀ st, SStuck code T n st d env b) (IHn : ∀ m < n, ∀ st, SStuck code T m st d env (.whileStmt c b)) :
    SStuck code T n st d env (.whileStmt c b) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp hne
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact .inr ⟨A, .refl _⟩
  have hwf' := hwf
  have htmp' := htmp
  have hseg' := hseg
  have hP' := hP
  obtain ⟨hwc, hwb⟩ := hwf
  simp only [tS] at htmp
  obtain ⟨hcond, sb, sJ, hlen, hlb, hw1, hw2⟩ := while_segs hseg
  rw [hlen] at hP
  have hwbd : wBody T C pos c = pos + (gexpr T C.Γ 0 pos c).length + 3 := rfl
  have hPx : PosOK (wExit T C pos c b) := posOK_le hP (by omega)
  have hPpos : PosOK pos := posOK_le hP (by omega)
  have hPb : PosOK (wBody T C pos c) := posOK_le hP (by omega)
  by_cases hec : HasE st d env c
  rotate_left
  · obtain ⟨s12, -⟩ := hcond.append
    obtain ⟨s1, -⟩ := s12.append
    exact ihc st V C.Γ sp fs 0 pos A hm hA hwc s1 (posOK_le hP (by omega)) (by omega) hec
  obtain ⟨st1, v, Dc⟩ := hec
  obtain ⟨nc, hE⟩ := spec_e hR (T := T) Dc
  cases hvt : v.truthy
  · exact absurd ⟨st1, .normal, .whileFalse _ _ _ _ _ _ _ Dc hvt⟩ hne
  obtain ⟨B, ⟨k1, hk1⟩, hB⟩ := run_cond hR hE hm hA hwc hcond (posOK_le hP (by omega)) hPx (by omega)
  rcases hB with ⟨h1, -⟩ | ⟨V1, hp1⟩
  · exact Fail.of_star ⟨k1, hk1⟩ (fail_err hR h1)
  rw [hvt, if_pos rfl] at hp1
  obtain ⟨hpc1, hm1⟩ := hp1.out
  have hk1p : 1 ≤ k1 := hk1.pos_of_pc (by
    rw [hA, hpc1]; intro h; have := pcOf_inj hPpos (by rw [← hwbd]; exact hPb) h; omega)
  have hctxb := hctx.loop hPx hPpos
  have hPe : PosOK (wBody T C pos c + (gstmt T (C.loop (wExit T C pos c b) pos) (wBody T C pos c) b).length) := by
    rw [hlb]; exact posOK_le hP (by omega)
  by_cases heb : HasS st1 d env b
  rotate_left
  · exact Fail.of_star ⟨k1, hk1⟩ (ihb st1 V1 (C.loop (wExit T C pos c b) pos) sp fs (wBody T C pos c) B hm1 hpc1 hwb
      hctxb sb hPe (by omega) heb)
  obtain ⟨st2, tb, Db⟩ := heb
  have hst : tb = .normal ∨ tb = .cont := by
    cases tb with
    | normal => exact .inl rfl
    | cont => exact .inr rfl
    | brk => exact absurd ⟨st2, .normal, .whileBreak _ _ _ _ _ _ _ _ Dc hvt Db⟩ hne
    | ret rv => exact absurd ⟨st2, .ret rv, .whileRet _ _ _ _ _ _ _ _ _ Dc hvt Db⟩ hne
  have hne2 : ¬ HasS st2 d env (.whileStmt c b) := fun ⟨st3, t3, D3⟩ =>
    hne ⟨st3, t3, .whileLoop _ _ _ _ _ _ _ _ _ _ _ Dc hvt Db hst D3⟩
  obtain ⟨nb, hS⟩ := spec_s hR (T := T) Db
  obtain ⟨B', ⟨k2, hk2⟩, hB'⟩ := hS V1 (C.loop (wExit T C pos c b) pos) sp fs (wBody T C pos c) B hm1 hpc1 hwb
    hctxb sb hPe (by omega)
  rcases hB' with ⟨h1, -⟩ | ⟨V2, hp2⟩
  · exact Fail.of_star ⟨k1 + k2, hk1.trans hk2⟩ (fail_err hR h1)
  have hback : ∃ k3 B3, StarN code k3 B' B3 ∧ B3.pc = pcOf pos ∧ MS code T V2 st2 d env C.Γ sp fs B3 := by
    rcases hst with rfl | rfl
    · obtain ⟨hpc2, hm2⟩ := hp2.out
      rw [hlb, show wBody T C pos c + (wExit T C pos c b - 1 - wBody T C pos c) = wExit T C pos c b - 1 by omega]
        at hpc2
      obtain ⟨pcB, LB, mB, oB⟩ := B'
      exact ⟨1, _, .step (step_jump hR.fits sJ.head hpc2 (posOK_le hP (by omega)) hPpos) (.refl _), rfl,
        hm2.setpc _⟩
    · obtain ⟨hpc2, hm2⟩ := ExitAt.here hp2.out
      exact ⟨0, B', .refl _, hpc2, hm2⟩
  obtain ⟨k3, B3, hk3, hpc3, hm3⟩ := hback
  exact Fail.of_prefix (hk1.trans (hk2.trans hk3))
    (IHn _ (by omega) st2 V2 C sp fs pos B3 hm3 hpc3 hwf' hctx hseg' hP' htmp' hne2)

/-- A `for` loop without an execution fails from its condition. -/
theorem fFL {cnd step : Option Expr} {b : Stmt} (ihc : ∀ c, cnd = some c → ∀ st, EStuck code T n st d env c)
    (ihb : ∀ st, SStuck code T n st d env b) (ihs : ∀ e, step = some e → ∀ st, EStuck code T n st d env e)
    (IHn : ∀ m < n, ∀ st, FLStuck code T m st d env cnd step b) : FLStuck code T n st d env cnd step b := by
  intro V C pos init sp fs A hok hm hA hne
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact .inr ⟨A, .refl _⟩
  have ho := for_order T C pos init cnd step b
  have hPe := hok.pend
  have htmp := hok.tmp
  rw [tS_for] at htmp
  by_cases hfc : ∃ st1, ForCond st d env cnd st1
  rotate_left
  · cases cnd with
    | none => exact absurd ⟨st, .none _ _ _⟩ hfc
    | some c =>
      by_cases hec : HasE st d env c
      · obtain ⟨st1, v, Dc⟩ := hec
        cases hvt : v.truthy
        · exact absurd ⟨st1, .normal, .condFalse _ _ _ _ _ _ _ _ Dc hvt⟩ hne
        · exact absurd ⟨st1, .some _ _ _ _ _ _ Dc hvt⟩ hfc
      have hcc := hok.segs.cc
      simp only [fCc] at hcc
      obtain ⟨s12, -⟩ := hcc.append
      obtain ⟨s1, -⟩ := s12.append
      simp only [tOE] at htmp
      have hpb : fPb T C pos init (some c) b = fHd T C pos init b +
          (gexpr T (fC1 C init b).Γ 0 (fHd T C pos init b) c).length + 3 := by simp [fPb, fLc]; omega
      exact ihc c rfl st V (fC1 C init b).Γ sp fs 0 _ A hm hA hok.wc s1 (posOK_le hPe (by omega)) (by omega) hec
  obtain ⟨st1, Dfc⟩ := hfc
  obtain ⟨nc, Cc⟩ := ForCondCost.exists Dfc
  obtain ⟨B, ⟨k1, hk1⟩, hB⟩ := (sim_all (T := T) hR).fc Cc V C pos init step b sp fs A hok hm hA
  rcases hB with ⟨h1, -⟩ | ⟨V1, hp1⟩
  · exact Fail.of_star ⟨k1, hk1⟩ (fail_err hR h1)
  have hbl := fBody_length T C pos init cnd step b
  have hctxb := (hok.ctx.enter (forNames init b)).loop
    (posOK_le hPe (by omega) : PosOK (fEx T C pos init cnd step b))
    (posOK_le hPe (by omega) : PosOK (fPs T C pos init cnd b))
  by_cases heb : HasS st1 d env b
  rotate_left
  · obtain ⟨hpc1, hm1⟩ := hp1.out
    exact Fail.of_star ⟨k1, hk1⟩ (ihb st1 V1 ((fC1 C init b).loop (fEx T C pos init cnd step b)
      (fPs T C pos init cnd b)) sp fs (fPb T C pos init cnd b) B hm1 hpc1 hok.wb hctxb hok.segs.body
      (by rw [hbl]; exact posOK_le hPe (by omega)) (by omega) heb)
  obtain ⟨st2, tb, Db⟩ := heb
  have hst : tb = .normal ∨ tb = .cont := by
    cases tb with
    | normal => exact .inl rfl
    | cont => exact .inr rfl
    | brk => exact absurd ⟨st2, .normal, .bodyBreak _ _ _ _ _ _ _ _ Dfc Db⟩ hne
    | ret rv => exact absurd ⟨st2, .ret rv, .bodyRet _ _ _ _ _ _ _ _ _ Dfc Db⟩ hne
  obtain ⟨nb, hS⟩ := spec_s hR (T := T) Db
  obtain ⟨B', ⟨k2, hk2⟩, hB'⟩ := for_body hR hS hok hp1
  rcases hB' with ⟨h1, -⟩ | ⟨V2, hp2⟩
  · exact Fail.of_star ⟨k1 + k2, hk1.trans hk2⟩ (fail_err hR h1)
  have hps : B'.pc = pcOf (fPs T C pos init cnd b) ∧ MS code T V2 st2 d env (fC1 C init b).Γ sp fs B' := by
    rcases hst with rfl | rfl
    · exact hp2.out
    · exact ExitAt.here hp2.out
  by_cases hes : ∃ st3, ExecStep st2 d env step st3
  rotate_left
  · cases step with
    | none => exact absurd ⟨st2, .none _ _ _⟩ hes
    | some e =>
      have hee : ¬ HasE st2 d env e := fun ⟨st3, v, De⟩ => hes ⟨st3, .some _ _ _ _ _ _ De⟩
      have hcs := hok.segs.cs
      simp only [fCs] at hcs ho
      simp only [tOE] at htmp
      exact Fail.of_star ⟨k1 + k2, hk1.trans hk2⟩ (ihs e rfl st2 V2 (fC1 C init b).Γ sp fs 0 _ B' hps.2 hps.1
        hok.ws hcs (posOK_le hPe (by omega)) (by omega) hee)
  obtain ⟨st3, Dst⟩ := hes
  have hne3 : ¬ HasFL st3 d env cnd step b := fun ⟨st4, t4, D4⟩ =>
    hne ⟨st4, t4, .loop _ _ _ _ _ _ _ _ _ _ _ _ Dfc Db hst Dst D4⟩
  obtain ⟨ns, Cs⟩ := ExecStepCost.exists Dst
  obtain ⟨B'', ⟨k3, hk3⟩, hB''⟩ := (sim_all (T := T) hR).xs Cs V2 C pos init cnd b sp fs B' hok hps.2 hps.1
  rcases hB'' with ⟨h1, -⟩ | ⟨V3, hp3⟩
  · exact Fail.of_star ⟨_, (hk1.trans hk2).trans hk3⟩ (fail_err hR h1)
  obtain ⟨hpc3, hm3⟩ := hp3.out
  have e1 : fEx T C pos init cnd step b - 1 = fPs T C pos init cnd b + (fCs T C pos init cnd step b).length := by
    omega
  rw [e1] at hpc3
  obtain ⟨pc3, L3, m3, o3⟩ := B''
  have hj := step_jump hR.fits (hok.segs.jmp.cast e1).head hpc3 (posOK_le hPe (by omega)) (posOK_le hPe (by omega))
  exact Fail.of_prefix (hk1.trans (hk2.trans (hk3.trans (.step hj (.refl _)))))
    (IHn _ (by omega) st3 V3 C pos init sp fs _ hok (hm3.setpc _) rfl hne3)

theorem fFor {init : Option Stmt} {cnd step : Option Expr} {b : Stmt}
    (ihi : ∀ s, init = some s → ∀ st env, SStuck code T n st d env s)
    (ihl : ∀ st env, FLStuck code T n st d env cnd step b) : SStuck code T n st d env (.forStmt init cnd step b) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp hne
  obtain ⟨hL120, hwi, hwc, hws, hwb⟩ := hwf
  have hsegs := ForSegs.of hseg
  have hlen := for_len T C pos init cnd step b
  rw [hlen] at hP
  have ho := for_order T C pos init cnd step b
  have hok : ForOK code T C pos init cnd step b fs := ⟨hsegs, hP, hwi, hwc, hws, hwb, hctx, htmp⟩
  apply Fail.of_reaches
  refine ex_bind (run_enterFrame hR hm hA hL120 (addNames_nodup _ List.nodup_nil) hsegs.ent
    (posOK_le hP (by omega))) ?_
  rintro B (⟨h1, -⟩ | ⟨hpcB, hE⟩)
  · exact reach_here (fail_err hR h1)
  by_cases hi : ∃ st1, ExecInit ⟨(st.store.allocFrame (some env)).1, st.out⟩ d st.store.frames.size init st1
  · obtain ⟨st1, Di⟩ := hi
    obtain ⟨ni, Ci⟩ := ExecInitCost.exists Di
    refine ex_bind ((sim_all (T := T) hR).xi Ci _ C pos cnd step b sp fs B hok hE.ms hpcB) ?_
    rintro B' (⟨h1, -⟩ | ⟨V1, hp1⟩)
    · exact reach_here (fail_err hR h1)
    obtain ⟨hpc1, hm1⟩ := hp1.out
    exact reach_here (ihl st1 _ V1 C pos init sp fs B' hok hm1 hpc1
      (fun ⟨st2, t, D⟩ => hne ⟨st2, t, .forStart _ _ _ _ _ _ _ _ _ _ _ _ rfl Di D⟩))
  · cases init with
    | none => exact absurd ⟨_, .none _ _ _⟩ hi
    | some s =>
      have hns : ¬ HasS ⟨(st.store.allocFrame (some env)).1, st.out⟩ d st.store.frames.size s :=
        fun ⟨st1, t, D⟩ => hi ⟨st1, .some _ _ _ _ _ _ D⟩
      have hci := hok.segs.ci
      have hl := fCi_length T C pos (some s) b
      simp only [fCi] at hci hl
      have hPh : PosOK (fHd T C pos (some s) b) := posOK_le hok.pend (by omega)
      have htmp' := hok.tmp
      simp only [tS] at htmp'
      have hctx' : CtxOK ((fC1 C (some s) b).swallow (fHd T C pos (some s) b)) := (hok.ctx.enter _).swallow hPh
      exact reach_here (ihi s rfl _ _ _ ((fC1 C (some s) b).swallow (fHd T C pos (some s) b)) sp fs (pos + 4) B
        hE.ms hpcB hok.wi hctx' hci (by rw [hl]; exact hPh) (by omega) hns)

omit hR in
theorem fNil : QStuck code T n st d env [] :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hne => absurd ⟨st, .normal, .nil _ _ _⟩ hne

theorem fCons {s : Stmt} {ss : List Stmt} (ihs : ∀ st, SStuck code T n st d env s)
    (ihss : ∀ st, QStuck code T n st d env ss) : QStuck code T n st d env (s :: ss) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp hne
  obtain ⟨hws, hwss⟩ := hwf
  simp only [gseq] at hseg hP
  obtain ⟨s1, s2⟩ := hseg.append
  simp only [List.length_append] at hP
  simp only [tSeq] at htmp
  by_cases hes : HasS st d env s
  rotate_left
  · exact ihs st V C sp fs pos A hm hA hws hctx s1 (posOK_le hP (by omega)) (by omega) hes
  obtain ⟨st1, t, Ds⟩ := hes
  by_cases ht : t = .normal
  rotate_left
  · exact absurd ⟨st1, t, .consAbrupt _ _ _ _ _ _ _ Ds ht⟩ hne
  subst ht
  obtain ⟨ns, hS⟩ := spec_s hR (T := T) Ds
  apply Fail.of_reaches
  refine ex_bind (hS V C sp fs pos A hm hA hws hctx s1 (posOK_le hP (by omega)) (by omega)) ?_
  rintro B (⟨h1, -⟩ | ⟨V1, hp⟩)
  · exact reach_here (fail_err hR h1)
  obtain ⟨hpc, hm1⟩ := hp.out
  exact reach_here (ihss st1 V1 C sp fs _ B hm1 hpc hwss hctx s2 (by rw [← Nat.add_assoc] at hP; exact hP)
    (by omega) (fun ⟨st', t', D⟩ => hne ⟨st', t', .consNormal _ _ _ _ _ _ _ _ Ds D⟩))

end

end Vsa.Compiler
