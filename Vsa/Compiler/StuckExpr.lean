import Vsa.Compiler.StuckDefs
import Vsa.Compiler.R6Stuck
import Vsa.Compiler.R6Reg

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem run_op_none {H : CloMap} {s : Store} {m : Mem} {h : Nat} {L : GRegs} {o : Array String} {op : BinOp}
    {l r : Value} {t1 p1 t2 p2 : BitVec 64} {q : Nat} (hops : Operands H m h L l r t1 p1 t2 p2)
    (hseg : Seg code q (opCode q op)) (hq : PosOK (q + (opCode q op).length))
    (hbin : binOpSem s op l r = none) (h8 : Has L hpO (BitVec.ofNat 64 h)) (hh : ObjPtr h)
    (hfx : FixedOK m) (hfb : fixedAddr 7 + 40 ≤ h) (hc : CloOK H s m h) :
    Reaches code ⟨pcOf q, L, m, o⟩ (fun B => B.pc = pcOf errPos) := by
  have hq1 : PosOK (q + 1) := posOK_le hq (by cases op <;> simp [opCode])
  have hal1 := pcOf_aligned hq1
  cases op with
  | add =>
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_add hR (s := s) (hops.gset1 _) (by reg_simp []; exact h8) (by reg_simp []) hal1
      hh hfx hfb hc) ?_
    rintro B ⟨-, hB⟩
    rw [hbin] at hB
    exact hB
  | sub =>
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_sub hR (s := s) (hops.gset1 _) (by reg_simp []) hal1) ?_
    rintro B ⟨-, -, hB⟩
    rw [hbin] at hB
    exact hB
  | mul =>
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_mul hR (s := s) (hops.gset1 _) (by reg_simp []) hal1) ?_
    rintro B ⟨-, -, hB⟩
    rw [hbin] at hB
    exact hB
  | div =>
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_div hR (s := s) (hops.gset1 _) (by reg_simp []) hal1) ?_
    rintro B ⟨-, -, hB⟩
    rw [hbin] at hB
    exact hB
  | mod =>
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_mod hR (s := s) (hops.gset1 _) (by reg_simp []) hal1) ?_
    rintro B ⟨-, -, hB⟩
    rw [hbin] at hB
    exact hB
  | eq => simp [binOpSem] at hbin
  | ne => simp [binOpSem] at hbin
  | lt =>
    have hq2 : PosOK (q + 1 + 1) := posOK_le hq (by simp [opCode])
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_cmp hR (s := s) (op := .lt) (by simp [IsOrd]) (hops.gset14 _ |>.gset1 _)
      (by reg_simp []; rfl) (by reg_simp []) (pcOf_aligned hq2)) ?_
    rintro B ⟨-, -, hB⟩
    rw [hbin] at hB
    exact hB
  | le =>
    have hq2 : PosOK (q + 1 + 1) := posOK_le hq (by simp [opCode])
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_cmp hR (s := s) (op := .le) (by simp [IsOrd]) (hops.gset14 _ |>.gset1 _)
      (by reg_simp []; rfl) (by reg_simp []) (pcOf_aligned hq2)) ?_
    rintro B ⟨-, -, hB⟩
    rw [hbin] at hB
    exact hB
  | gt =>
    have hq2 : PosOK (q + 1 + 1) := posOK_le hq (by simp [opCode])
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_cmp hR (s := s) (op := .gt) (by simp [IsOrd]) (hops.gset14 _ |>.gset1 _)
      (by reg_simp []; rfl) (by reg_simp []) (pcOf_aligned hq2)) ?_
    rintro B ⟨-, -, hB⟩
    rw [hbin] at hB
    exact hB
  | ge =>
    have hq2 : PosOK (q + 1 + 1) := posOK_le hq (by simp [opCode])
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_cmp hR (s := s) (op := .ge) (by simp [IsOrd]) (hops.gset14 _ |>.gset1 _)
      (by reg_simp []; rfl) (by reg_simp []) (pcOf_aligned hq2)) ?_
    rintro B ⟨-, -, hB⟩
    rw [hbin] at hB
    exact hB

variable {n : Nat} {st : St} {d : Nat} {env : Addr}

theorem fVar (x : String) : EStuck code T n st d env (.var x) := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp hne
  have hnone : st.store.get? env x = none := by
    cases h : st.store.get? env x with
    | none => rfl
    | some v => exact absurd ⟨st, v, .var _ _ _ _ _ h⟩ hne
  obtain ⟨pc, L, m, o⟩ := A
  simp only at hA; subst hA
  obtain ⟨f, hFa⟩ := hm.chn.head'
  obtain ⟨fr, hfr⟩ := hm.chn.frame
  have hlt : env < st.store.frames.size := (Array.getElem?_eq_some_iff.mp hfr).1
  have hlen := gexpr_var_length T Γ k pos x
  rw [hlen] at hP
  have he := hm.henv
  rw [View.fa_eq hFa] at he
  simp only [gexpr, varCode] at hseg
  obtain ⟨s1, s2⟩ := hseg.append
  apply Fail.of_reaches
  apply run_whole hR.fits s1
  wp_simp [he.wp]
  refine reaches_mono (walk_read hR.fits hm.rel x (pos + 1 + walkLen (hereLen 7 x) Γ)
    (by rw [Nat.add_assoc]; exact hP) hm.chn
    (pos + 1) f _ o hFa s2 (by reg_simp [])) ?_
  rintro B ⟨-, -, -, hB⟩
  rw [← get?_eq hm.rel.parents hlt x, hnone] at hB
  exact fail_err hR hB

theorem fAssign {x : String} {e : Expr} (ih : ∀ st, EStuck code T n st d env e) :
    EStuck code T n st d env (.assign x e) := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp hne
  simp only [tE] at htmp
  have h := And.intro hseg hP
  simp only [gexpr, setCode, ↓segP_app, List.length_cons, List.length_nil, Nat.zero_add] at h
  obtain ⟨⟨s1, p1⟩, ⟨s2, -⟩, s3, p3⟩ := h
  rw [walkCode_length x _ 8 writeHere (fun l p => writeHere_length x l p _) Γ _] at p3
  by_cases he : HasE st d env e
  rotate_left
  · exact ih st V Γ sp fs k pos A hm hA hwf s1 p1 htmp he
  obtain ⟨st1, v, D⟩ := he
  obtain ⟨m1, hE⟩ := spec_e hR (T := T) D
  have hset : st1.store.set? env x v = none := by
    cases h : st1.store.set? env x v with
    | none => rfl
    | some s'' => exact absurd ⟨_, v, .assign _ _ _ _ _ _ _ _ D h⟩ hne
  apply Fail.of_reaches
  refine hE.bind hm hA hwf s1 p1 htmp
    (fun B h1 _ => fail_err hR h1) fun V1 B hpc hp => ?_
  obtain ⟨t, p, h10, h11, hv⟩ := hp.val
  obtain ⟨pc1, L1, m1, o1⟩ := B
  simp only at hpc h10 h11 hv; subst hpc
  have hms := hp.ms
  obtain ⟨f, hFa⟩ := hms.chn.head'
  obtain ⟨fr, hfr⟩ := hms.chn.frame
  have hlt : env < st1.store.frames.size := (Array.getElem?_eq_some_iff.mp hfr).1
  have he := hms.henv
  rw [View.fa_eq hFa] at he
  apply run_whole hR.fits s2
  wp_simp [he.wp]
  refine reaches_mono (walk_write hR.fits hms.rel x _ p3 hv hms.chn
    _ f _ o1 hFa s3 (by reg_simp []) (by reg_simp []; exact h10) (by reg_simp []; exact h11)) ?_
  rintro B ⟨-, -, hB⟩
  have hset' := hset
  unfold Store.set? at hset'
  rw [set_gas hms.rel.parents x v env _ hlt] at hset'
  rw [hset'] at hB
  exact fail_err hR hB.1

theorem fNeg {e : Expr} (ih : ∀ st, EStuck code T n st d env e) : EStuck code T n st d env (.unary .neg e) := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp hne
  have h := And.intro hseg hP
  simp only [gexpr, errUnlessEq, List.append_assoc, List.cons_append, List.nil_append, ↓segP_app,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at h
  obtain ⟨⟨s1, p1⟩, s2, p2⟩ := h
  have htmp' : 16 + 16 * (k + tE e) ≤ fs := by simpa [tE] using htmp
  by_cases he : HasE st d env e
  rotate_left
  · exact ih st V Γ sp fs k pos A hm hA hwf s1 p1 htmp' he
  obtain ⟨st1, v, D⟩ := he
  obtain ⟨m1, hE⟩ := spec_e hR (T := T) D
  have hni : tagOf v ≠ 2 := by
    cases v with
    | int i => exact absurd ⟨st1, _, .neg _ _ _ _ _ i D⟩ hne
    | _ => simp only [tagOf]; decide
  apply Fail.of_reaches
  refine hE.bind hm hA hwf s1 p1 htmp'
    (fun B h1 _ => fail_err hR h1) fun V1 B hpc hp => ?_
  obtain ⟨t, p, h10, h11, hv⟩ := hp.val
  rw [hv.tag] at h10
  obtain ⟨pc, L, mm, o⟩ := B
  simp only at hpc h10 h11; subst hpc
  apply run_whole hR.fits s2
  wp_simp [h10.wp]
  have htg : ¬ tagOf v = 2#64 := hni
  rw [if_neg htg]
  exact reach_here (fail_err hR (B := ⟨_, _, _, _⟩) rfl)

theorem fNot {e : Expr} (ih : ∀ st, EStuck code T n st d env e) : EStuck code T n st d env (.unary .not e) := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp hne
  simp only [gexpr, List.append_assoc] at hseg hP
  obtain ⟨⟨s1, p1⟩, -⟩ := segP_app.mp ⟨hseg, hP⟩
  refine ih st V Γ sp fs k pos A hm hA hwf s1 p1 (by simpa [tE] using htmp) ?_
  rintro ⟨st1, v, D⟩
  exact hne ⟨st1, _, .not _ _ _ _ _ _ D⟩

theorem fBinary {op : BinOp} {l r : Expr} (ihl : ∀ st, EStuck code T n st d env l)
    (ihr : ∀ st, EStuck code T n st d env r) : EStuck code T n st d env (.binary op l r) := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp hne
  obtain ⟨hwl, hwr⟩ := hwf
  simp only [tE] at htmp
  have htl : 16 + 16 * (k + tE l) ≤ fs := by omega
  have htr : 16 + 16 * ((k + 1) + tE r) ≤ fs := by omega
  have htk : 16 + 16 * (k + 1) ≤ fs := by omega
  have hal := hm.stk.al
  have h := And.intro hseg hP
  simp only [gexpr, storeTmp, loadTmp, List.append_assoc, ↓segP_app, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.reduceAdd] at h
  obtain ⟨⟨s1, p1⟩, ⟨s2, -⟩, ⟨s3, p3⟩, ⟨s4, -⟩, ⟨s5, -⟩, s6, p6⟩ := h
  by_cases hel : HasE st d env l
  rotate_left
  · exact ihl st V Γ sp fs k pos A hm hA hwl s1 p1 htl hel
  obtain ⟨st1, lv, Dl⟩ := hel
  obtain ⟨nl, hEl⟩ := spec_e hR (T := T) Dl
  apply Fail.of_reaches
  refine hEl.bind hm hA hwl s1 p1 htl
    (fun B h1 _ => fail_err hR h1) fun V1 B1 hpc1 hp1 => ?_
  obtain ⟨t1, q1, h10, h11, hv1⟩ := hp1.val
  obtain ⟨pc1, L1, m1, o1⟩ := B1
  simp only at hpc1 h10 h11 hv1; subst hpc1
  refine run_storeTmp hR.fits s2 hp1.ms.hsp hp1.ms.stk htk h10 h11 fun L2 hk2 => ?_
  obtain ⟨hmC, hoC⟩ := hp1.ms.stored (pc := pcOf (pos + (gexpr T Γ k pos l).length + 4)) htk
    (S := [t6]) (by decide) hk2 (t := t1) (p := q1)
  have hlt := InTmp.stored hv1 hal hoC
  by_cases her : HasE st1 d env r
  rotate_left
  · exact reach_here (ihr st1 V1 Γ sp fs (k + 1) _ _ hmC rfl hwr s3 p3 htr her)
  obtain ⟨st2, rv, Dr⟩ := her
  obtain ⟨nr, hEr⟩ := spec_e hR (T := T) Dr
  have hbin : binOpSem st2.store op lv rv = none := by
    cases h : binOpSem st2.store op lv rv with
    | none => rfl
    | some v => exact absurd ⟨st2, v, .binary _ _ _ _ _ _ _ _ _ _ _ Dl Dr h⟩ hne
  refine hEr.bind hmC rfl hwr s3 p3 htr
    (fun B h1 _ => fail_err hR h1) fun V2 D hpc2 hp2 => ?_
  obtain ⟨t2, q2, g10, g11, hv2⟩ := hp2.val
  obtain ⟨pcD, LD, mD, oD⟩ := D
  simp only at hpc2 g10 g11 hv2; subst hpc2
  have hlt2 := hlt.grow hp2.grow.hpre hp2.obj hp2.grow.le hp2.stack (by omega) (by omega)
  apply run_whole hR.fits s4
  wp_simp [g10.wp, g11.wp]
  refine run_loadTmp hR.fits s5 (by reg_simp []; exact hp2.ms.hsp) hp2.ms.stk htk fun L3 hk3 g10' g11' => ?_
  have hops : Operands V2.H mD V2.h L3 lv rv (rdW mD (sp + 16 + 16 * k)) (rdW mD (sp + 16 + 16 * k + 8)) t2 q2 :=
    ⟨g10', g11', hk3.has (by decide) (by reg_simp []), hk3.has (by decide) (by reg_simp []), hlt2, hv2⟩
  refine reaches_mono (run_op_none hR (s := st2.store) hops s6 p6 hbin
    (hk3.has (by decide) (by reg_simp []; exact hp2.ms.ho)) hp2.ms.img.ptr hp2.ms.img.fixed
    hp2.ms.img.fixedHi hp2.ms.rel.clo) fun B hB => fail_err hR hB

theorem fLogical {op : LogOp} {l r : Expr} (ihl : ∀ st, EStuck code T n st d env l)
    (ihr : ∀ st, EStuck code T n st d env r) : EStuck code T n st d env (.logical op l r) := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp hne
  obtain ⟨hwl, hwr⟩ := hwf
  simp only [tE] at htmp
  by_cases hel : HasE st d env l
  rotate_left
  · cases op
    all_goals
      simp only [gexpr, List.append_assoc] at hseg hP
      obtain ⟨⟨s1, p1⟩, -⟩ := segP_app.mp ⟨hseg, hP⟩
      exact ihl st V Γ sp fs k pos A hm hA hwl s1 p1 (by omega) hel
  obtain ⟨st1, lv, Dl⟩ := hel
  obtain ⟨nl, hEl⟩ := spec_e hR (T := T) Dl
  have ht : lv.truthy = !logShort op := by
    cases op with
    | or =>
      cases h : lv.truthy
      · rfl
      · exact absurd ⟨st1, _, .orTrue _ _ _ _ _ _ _ Dl h⟩ hne
    | and =>
      cases h : lv.truthy
      · exact absurd ⟨st1, _, .andFalse _ _ _ _ _ _ _ Dl h⟩ hne
      · rfl
  have her : ¬ HasE st1 d env r := by
    rintro ⟨st2, rv, Dr⟩
    cases op
    all_goals first
      | exact hne ⟨st2, _, .orFalse _ _ _ _ _ _ _ _ _ Dl (by simpa [logShort] using ht) Dr⟩
      | exact hne ⟨st2, _, .andTrue _ _ _ _ _ _ _ _ _ Dl (by simpa [logShort] using ht) Dr⟩
  cases op
  all_goals
    have h := And.intro hseg hP
    simp only [gexpr, jmpIfNonzero, jmpIfZero, List.append_assoc, ↓segP_app, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.reduceAdd] at h
    obtain ⟨⟨s1, -⟩, ⟨s2, p2⟩, ⟨s3, -⟩, ⟨s4, p4⟩, -⟩ := h
    apply Fail.of_reaches
    refine reaches_mono (hEl.bindTr hR (R := Fail code n) hm hA hwl s1 s2 p2 (by omega) (Within.refl V 0)
      (Nat.le_refl _) fun V1 B1 L2 hp1 hk2 g10 => ?_) fun B hB => hB.elim (fun h => fail_err hR h.1) id
    apply run_jumps hR.fits s3
    wp_simp [logShort, ht, g10.wp, Bool.not_false, Bool.not_true]
    exact reach_here (.inr (ihr st1 V1 Γ sp fs k (pos + (gexpr T Γ k pos l).length + 3) _ (hp1.ms.keep hk2) rfl hwr
      s4 p4 (by omega) her))

theorem fCall {f : Expr} {args : List Expr} (ihf : ∀ st, EStuck code T n st d env f)
    (iha : ∀ st, AStuck code T n st d env args) (ihc : ∀ st fv vs, CStuck code T n st d fv vs) :
    EStuck code T n st d env (.call f args) := by
  intro V Γ sp fs k pos A hm hpc hwf hseg hP htmp hne
  obtain ⟨hwf1, hwa⟩ := hwf
  simp only [tE] at htmp
  have hal := hm.stk.al
  have hsh : tArgs (k + 1) args ≤ tArgs 1 args + k := by
    have := tArgs_shift args 1 k; rwa [Nat.add_comm 1 k] at this
  by_cases hmax : maxArgs < args.length
  · simp only [gexpr, hmax, ite_true] at hseg hP
    obtain ⟨⟨s1, p1⟩, s2, -⟩ := segP_app.mp ⟨hseg, hP⟩
    by_cases hef : HasE st d env f
    rotate_left
    · exact ihf st V Γ sp fs k pos A hm hpc hwf1 s1 p1 (by omega) hef
    obtain ⟨st1, fv, Df⟩ := hef
    obtain ⟨nf, hE⟩ := spec_e hR (T := T) Df
    apply Fail.of_reaches
    refine hE.bind hm hpc hwf1 s1 p1 (by omega)
      (fun B h1 _ => fail_err hR h1) fun V1 B1 hpc1 hp1 => ?_
    obtain ⟨pc1, L1, m1, o1⟩ := B1
    simp only at hpc1; subst hpc1
    apply run_whole hR.fits s2
    wp_simp []
    exact reach_here (fail_err hR (B := ⟨_, _, _, _⟩) rfl)
  have h := And.intro hseg hP
  simp only [gexpr, hmax, if_false, storeTmp, List.append_assoc, ↓segP_app, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.reduceAdd] at h
  obtain ⟨⟨s1, p1⟩, ⟨s2, -⟩, ⟨s3, p3⟩, s4, p4⟩ := h
  by_cases hef : HasE st d env f
  rotate_left
  · exact ihf st V Γ sp fs k pos A hm hpc hwf1 s1 p1 (by omega) hef
  obtain ⟨st1, fv, Df⟩ := hef
  obtain ⟨nf, hE⟩ := spec_e hR (T := T) Df
  apply Fail.of_reaches
  refine hE.bind hm hpc hwf1 s1 p1 (by omega)
    (fun B h1 _ => fail_err hR h1) fun V1 B1 hpc1 hp1 => ?_
  obtain ⟨t1, q1, h10, h11, hv1⟩ := hp1.val
  obtain ⟨pc1, L1, m1, o1⟩ := B1
  simp only at hpc1 h10 h11 hv1; subst hpc1
  refine run_storeTmp hR.fits s2 hp1.ms.hsp hp1.ms.stk (by omega) h10 h11 fun L2 hk2 => ?_
  obtain ⟨hmC, hoC⟩ := hp1.ms.stored (pc := pcOf (pos + (gexpr T Γ k pos f).length + 4)) (j := k) (by omega)
    (S := [t6]) (by decide) hk2 (t := t1) (p := q1)
  have hlt := InTmp.stored hv1 hal hoC
  by_cases hea : HasA st1 d env args
  rotate_left
  · exact reach_here (iha st1 V1 Γ sp fs (k + 1) _ _ hmC rfl hwa s3 p3 (by omega) (by omega) hea)
  obtain ⟨st2, vs, Da⟩ := hea
  obtain ⟨na, hA, hvl⟩ := spec_a hR (T := T) Da
  have hnc : ¬ HasC st2 d fv vs := fun ⟨st3, v, Dc⟩ =>
    hne ⟨st3, v, .call _ _ _ _ _ _ _ _ _ _ _ Df (by omega) Da Dc⟩
  refine ex_bind (hA V1 Γ sp fs (k + 1) _ _ hmC rfl hwa s3 p3 (by omega) (by omega)) ?_
  rintro D (⟨h1, -⟩ | ⟨hpcD, V2, hp2⟩)
  · exact reach_here (fail_err hR h1)
  have hlt2 := hlt.grow hp2.grow.hpre hp2.obj hp2.grow.le hp2.stack (by omega) (by omega)
  obtain ⟨pcD, LD, mD, oD⟩ := D
  simp only at hpcD; subst hpcD
  exact reach_here (ihc st2 fv vs V2 env Γ sp fs k _ _ hp2.ms rfl hlt2 hp2.tmps (by omega) (hvl ▸ s4)
    (by rw [hvl]; exact p4) (by omega) hnc)

theorem fArgs {e : Expr} {es : List Expr} (ihe : ∀ st, EStuck code T n st d env e)
    (ihes : ∀ st, AStuck code T n st d env es) : AStuck code T n st d env (e :: es) := by
  intro V Γ sp fs k pos A hm hpc hwf hseg hP htmp hlen hne
  obtain ⟨hwe, hwes⟩ := hwf
  simp only [tArgs] at htmp
  simp only [List.length_cons] at hlen
  have hal := hm.stk.al
  simp only [gargs, storeTmp, List.append_assoc] at hseg hP
  have h := And.intro hseg hP
  simp only [↓segP_app, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    ← Nat.add_assoc] at h
  obtain ⟨⟨s1, p1⟩, ⟨s2, -⟩, s3, p3⟩ := h
  by_cases hee : HasE st d env e
  rotate_left
  · exact ihe st V Γ sp fs k pos A hm hpc hwe s1 p1 (by omega) hee
  obtain ⟨st1, v, De⟩ := hee
  obtain ⟨ne, hE⟩ := spec_e hR (T := T) De
  have hnes : ¬ HasA st1 d env es := fun ⟨st2, vs, Des⟩ => hne ⟨st2, _, .cons _ _ _ _ _ _ _ _ _ De Des⟩
  apply Fail.of_reaches
  refine hE.bind hm hpc hwe s1 p1 (by omega)
    (fun B h1 _ => fail_err hR h1) fun V1 B1 hpc1 hp1 => ?_
  obtain ⟨t1, q1, h10, h11, hv1⟩ := hp1.val
  obtain ⟨pc1, L1, m1, o1⟩ := B1
  simp only at hpc1 h10 h11 hv1; subst hpc1
  refine run_storeTmp hR.fits s2 hp1.ms.hsp hp1.ms.stk (by omega) h10 h11 fun L2 hk2 => ?_
  obtain ⟨hmC, -⟩ := hp1.ms.stored (pc := pcOf (pos + (gexpr T Γ k pos e).length + 4)) (j := k) (by omega)
    (S := [t6]) (by decide) hk2 (t := t1) (p := q1)
  exact reach_here (ihes st1 V1 Γ sp fs (k + 1) _ _ hmC rfl hwes s3 p3 (by omega) (by omega) hnes)

end

end Vsa.Compiler
