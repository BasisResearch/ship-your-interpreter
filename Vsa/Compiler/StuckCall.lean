import Vsa.Compiler.StuckExpr

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem StarN.pos_of_ne {code : List Ins} {k : Nat} {A B : AM} (h : StarN code k A B) (hne : A ≠ B) : 1 ≤ k := by
  cases h with
  | refl => exact absurd rfl hne
  | step => omega

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem run_entry_bad {q nv d : Nat} {Γc : List (List String)} {cd : ClosureData}
    (hseg : Seg code q (fnCode T Γc cd.params cd.body q))
    (hP : PosOK (q + (fnCode T Γc cd.params cd.body q).length)) (hwf : WfFn T Γc cd.params cd.body) {J : AM}
    (hJ : J.pc = pcOf q) (h14 : Has J.regs a4 (BitVec.ofNat 64 nv)) (h24 : Has J.regs depR (BitVec.ofNat 64 d))
    (hnv : nv ≤ maxArgs) (hd : d ≤ maxCallDepth) (hbad : nv ≠ cd.params.length ∨ ¬ d < maxCallDepth) :
    Reaches code J (fun B => B.pc = pcOf errPos) := by
  obtain ⟨hwP, -, -, -⟩ := hwf
  have hmc : maxCallDepth = 1000 := rfl
  have hma : maxArgs = 32 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hPb : PosOK (fnBody cd.params q) := posOK_le hP (by
    rw [fnCode_eq]; simp only [List.length_append, fnHead_length, paramCopies_length, List.length_singleton]
    simp only [fnBody]; omega)
  have hfb : fnBody cd.params q = q + 14 + 8 * cd.params.length + 1 := rfl
  rw [fnCode_eq] at hseg
  obtain ⟨sPre, -⟩ := hseg.append
  obtain ⟨sPre, -⟩ := sPre.append
  obtain ⟨sH, -⟩ := sPre.append
  obtain ⟨pc0, L0, m0, o0⟩ := J
  simp only at hJ h14 h24; subst hJ
  have k14 := has_mem h14 (by decide); have e14 := srcVal_of_has h14
  have k24 := has_mem h24 (by decide); have e24 := srcVal_of_has h24
  simp only [a4, depR] at k14 e14 k24 e24
  by_cases hlen : nv = cd.params.length
  · have hd' : ¬ d < 1000 := by
      rcases hbad with h | h
      · exact absurd hlen h
      · exact h
    apply run_jumps hR.fits sH
    wp_simp [fnHead, errUnlessEq, k14, e14, BitVec.ofInt_natCast, hlen]
    rw [show q + 1 + 2 = q + 3 from rfl]
    apply run_jumps hR.fits (sH.drop 3)
    have hd'' : ¬ (d : Int) < 1000 := by omega
    wp_simp [fnHead, errUnlessEq, k24, e24, toInt_ofNat_small d (by omega), hd'']
    exact reach_here rfl
  · have hne : ¬ BitVec.ofNat 64 nv = BitVec.ofNat 64 cd.params.length := by
      intro h
      have := congrArg BitVec.toNat h
      rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
      exact hlen this
    apply run_jumps hR.fits sH
    wp_simp [fnHead, errUnlessEq, k14, e14, BitVec.ofInt_natCast, hne]
    exact reach_here rfl

variable {n : Nat}

theorem fNotCallable {st : St} {d : Nat} {fv : Value} {vs : List Value} (h1 : ∀ a, fv ≠ .closure a)
    (h2 : ∀ f, fv ≠ .native f) : CStuck code T n st d fv vs := by
  intro V env Γ sp fs k pos A hm hA hf hvs hmax hseg hP htmp hne
  have hs := CCSegs.of hseg
  obtain ⟨pc0, L0, m0, o0⟩ := A
  simp only at hA; subst hA
  have ht : rdW m0 (sp + 16 + 16 * k) = tagOf fv := hf.tag
  apply Fail.of_reaches
  refine reaches_mono (run_dispatch hR hs hP hm.hsp hm.stk (by omega)) ?_
  rintro B ⟨-, -, -, -, hpc⟩
  rw [ht] at hpc
  have he : dispTgt k vs.length pos (tagOf fv) (rdW m0 (sp + 16 + 16 * k + 8)) = errPos := by
    cases fv with
    | closure a => exact absurd rfl (h1 a)
    | native f => exact absurd rfl (h2 f)
    | _ => simp [dispTgt, tagOf]
  rw [he] at hpc
  exact fail_err hR hpc

theorem fAssert {st : St} {d : Nat} {vs : List Value} : CStuck code T n st d (.native .assert) vs := by
  intro V env Γ sp fs k pos A hm hA hf hvs' hmax hseg hP htmp hne
  have hs := CCSegs.of hseg
  obtain ⟨pc, L, m, o⟩ := A
  simp only at hA; subst hA
  obtain ⟨ht5, hp2⟩ : rdW m (sp + 16 + 16 * k) = 5 ∧ rdW m (sp + 16 + 16 * k + 8) = 2 := hf
  apply Fail.of_reaches
  refine ex_bind (run_dispatch hR hs hP hm.hsp hm.stk (by omega)) ?_
  rintro ⟨pc1, L1, m1, o1⟩ ⟨hm1, ho1, hk1, -, hpc1⟩
  simp only at hm1 ho1 hk1 hpc1; subst hm1 ho1 hpc1
  rw [ht5, hp2] at *
  simp only [dispTgt, show (5 : BitVec 64) ≠ 4 by decide, show (2 : BitVec 64) ≠ 0 by decide,
    show (2 : BitVec 64) ≠ 1 by decide, if_false, if_true] at *
  have ha := hs.asrt
  have hle : ccPR k vs.length pos ≤ pos + (callCode k vs.length pos).length := by
    rw [ccFin_eq]; simp only [ccFin, ccCL_eq, ccPL_eq]; omega
  by_cases hm12 : vs.length = 1 ∨ vs.length = 2
  rotate_left
  · have ea : ccAssert k vs.length pos = [J (pos + 15) errPos] := by simp [ccAssert, hm12]
    have hq : PosOK (pos + 15 + 1) := posOK_le hP (by rw [ccPR_eq, ea] at hle; simp at hle; omega)
    rw [ea] at ha
    apply run_jumps hR.fits ha
    wp_simp []
    exact reach_here (fail_err hR (B := ⟨_, _, _, _⟩) rfl)
  obtain ⟨v, w, hvs⟩ : ∃ v w, vs = [v] ∨ vs = [v, w] := by
    rcases vs with _ | ⟨v, _ | ⟨w, _ | ⟨u, rest⟩⟩⟩
    · simp at hm12
    · exact ⟨v, v, .inl rfl⟩
    · exact ⟨v, w, .inr rfl⟩
    · simp at hm12
  have hfl : v.truthy = false := by
    cases h : v.truthy
    · rfl
    · exact absurd ⟨st, _, .assertOk _ _ _ v w hvs h⟩ hne
  have hv0 : InTmp V.H m1 V.h sp (k + 1) v := by
    have := hvs' 0 (by rcases hvs with rfl | rfl <;> simp)
    rcases hvs with rfl | rfl <;> simpa using this
  have ea : ccAssert k vs.length pos = loadTmp (k + 1) ++ [Call (pos + 15 + 4) trPos] ++
      jmpIfZero (pos + 15 + 5) errPos ++ [mvi a0 0, mvi a1 0] := by simp [ccAssert, hm12]
  rw [ea] at ha
  obtain ⟨s1, -⟩ := ha.append
  obtain ⟨s1, s3⟩ := s1.append
  obtain ⟨s1, s2⟩ := s1.append
  have e4 : (loadTmp (k + 1)).length = 4 := by simp [loadTmp]
  simp only [List.length_append, e4, List.length_singleton, jmpIfZero, List.length_cons, List.length_nil] at s2 s3
  have hpos : pos + 15 + 9 ≤ ccFin k vs.length pos := by
    have hPR : ccPR k vs.length pos = pos + 15 + 9 + 1 := by simp only [ccPR_eq, ea]; simp [loadTmp, jmpIfZero]
    simp only [ccFin, ccCL_eq, ccPL_eq]; omega
  have hfin := ccFin_eq k vs.length pos
  have hq : PosOK (pos + 15 + 4 + 1) := posOK_le hP (by omega)
  refine run_loadTmp hR.fits s1 (hk1.has (by decide) hm.hsp) hm.stk (by omega) fun L2 hk2 g10 g11 => ?_
  apply run_whole hR.fits (s2.cast (pos' := pos + 15 + 4) (by omega))
  wp_simp [hq]
  refine ex_bind (run_tr hR.fits hR.tr (L := gset L2 1 (pcOf (pos + 15 + 4 + 1))) (m := m1) (o := o1)
    (by reg_simp []; exact g10) (by reg_simp []; exact g11) (by reg_simp []) (pcOf_aligned hq)) ?_
  rintro ⟨pc3, L3, m3, o3⟩ ⟨hpc3, hm3, ho3, g10', hk3⟩
  simp only at hpc3 hm3 ho3 g10' hk3; subst hpc3 hm3 ho3
  have hv0' : VRepr V.H m3 V.h v (rdW m3 (sp + 16 + 16 * (k + 1))) (rdW m3 (sp + 16 + 16 * (k + 1) + 8)) := hv0
  rw [trW_repr hv0', hfl] at g10'
  have k10 := has_mem g10' (by decide); have e10 := srcVal_of_has g10'
  simp only [a0] at k10 e10
  apply run_jumps hR.fits (s3.cast (pos' := pos + 15 + 5) (by omega))
  wp_simp [k10, e10]
  exact reach_here (fail_err hR (B := ⟨_, _, _, _⟩) rfl)

theorem fClosure {st : St} {d : Nat} {a : Addr} {vs : List Value}
    (IHq : ∀ m < n, ∀ st d env ss, QStuck code T m st d env ss) : CStuck code T n st d (.closure a) vs := by
  intro V env Γ sp fs k pos A hm hA hf hvs hmax hseg hP htmp hne
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact .inr ⟨A, .refl _⟩
  obtain ⟨ht4, hpa⟩ : rdW A.mem (sp + 16 + 16 * k) = 4 ∧
      V.H[a]? = some (rdW A.mem (sp + 16 + 16 * k + 8)).toNat := hf
  generalize hPw : rdW A.mem (sp + 16 + 16 * k + 8) = pw at hpa
  obtain ⟨cd, hcd⟩ : ∃ cd, st.store.closures[a]? = some cd := by
    have hlt : a < V.H.length := (List.getElem?_eq_some_iff.mp hpa).1
    rw [hm.rel.clo.len] at hlt
    exact ⟨_, Array.getElem?_eq_getElem hlt⟩
  obtain ⟨q, Γc, hc1, hc2, hc3, hc4, hc5, hc6⟩ := hm.clo a cd pw.toNat hcd hpa
  obtain ⟨dA, cA, hco⟩ := hm.rel.clo.obj a cd pw.toNat hcd hpa
  have hco1 := hco.lo; have hco2 := hco.hi; have hco3 := hco.al; have hptr := hm.img.ptr.hi
  have hob : objBase = 0x90000000 := rfl
  have hoe : objEnd = 0xE0000000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hmc : maxCallDepth = 1000 := rfl
  have hpw : pw = BitVec.ofNat 64 pw.toNat := by simp
  generalize hP' : pw.toNat = P at hpw hpa hc1 hc2 hco hco1 hco2 hco3
  subst hpw
  have hqq : PosOK q := posOK_le hc5 (by omega)
  have hdd := hm.stk.depth

  have hr : Reaches code A (fun B => Fail code n B ∨ (vs.length = cd.params.length ∧ d < maxCallDepth) ∧
      ∃ J, Entered code T V st d cd Γc vs sp (frameSize cd.body) q
        (pcOf (ccCL k vs.length pos + 6)) (BitVec.ofNat 64 (V.fa env)) J B) := by
    refine ex_bind (run_cloJump hR hm hA ht4 hPw (toNat_ofNat_lt (by omega)) (by unfold LdOK; omega) hc2 hqq
      hseg hP htmp) fun J hJ => ?_
    by_cases hok : vs.length = cd.params.length ∧ d < maxCallDepth
    · have hmq := hm.transport (B := J) (S := [a2, a3, a4, t3, ra, t0, t1, t2, t6]) (by decide) hJ.keep
        (by rw [hJ.mem]; exact Agree.refl _ _ _) (by rw [hJ.mem]; exact ObjAgree.refl _ _) hJ.out
      refine reaches_mono (run_entry hR (k := k) hmq hcd hpa (by rw [hJ.mem]; exact hc1) hc3 hc4 hc5 hc6
        hok.1 hok.2 hJ.pc hJ.hra hJ.h12 hJ.h13 hJ.h14 (by rw [hJ.mem]; exact hvs) htmp hmax) ?_
      rintro E (⟨h1, -⟩ | hE)
      · exact .inl (fail_err hR h1)
      · exact .inr ⟨hok, J, hE⟩
    · have hbad : vs.length ≠ cd.params.length ∨ ¬ d < maxCallDepth := by
        by_cases h : vs.length = cd.params.length
        · exact .inr fun hd => hok ⟨h, hd⟩
        · exact .inl h
      refine reaches_mono (run_entry_bad hR hc4 hc5 hc6 hJ.pc hJ.h14
        (hJ.keep.has (by decide) hm.hdep) hmax hdd hbad) fun B hB => .inl (fail_err hR hB)
  obtain ⟨E, ⟨j, hj⟩, hE⟩ := hr
  rcases hE with hF | ⟨⟨hlen, hdc⟩, J, hE⟩
  · exact Fail.of_star ⟨j, hj⟩ hF
  have hj1 : 1 ≤ j := hj.pos_of_ne (fun h => by
    subst h
    have e1 := srcVal_of_has hm.hdep; have e2 := srcVal_of_has hE.ms.hdep
    rw [e1] at e2
    have := congrArg BitVec.toNat e2
    rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
    omega)

  have hc4' := hc4
  rw [fnCode_eq] at hc4'
  obtain ⟨-, sRest⟩ := hc4'.append
  obtain ⟨sBody, -⟩ := sRest.append
  simp only [List.length_append, fnHead_length, paramCopies_length, List.length_singleton] at sBody
  have hpb : q + (14 + 8 * cd.params.length + 1) = fnBody cd.params q := by simp [fnBody]; omega
  rw [hpb] at sBody
  have hSh : (fnCtx (frameNames cd.params cd.body :: Γc) (fnBody cd.params q +
      (gseq T (fnCtx (frameNames cd.params cd.body :: Γc) 0) (fnBody cd.params q) cd.body).length + 2)).Sh
      (fnCtx (frameNames cd.params cd.body :: Γc) 0) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hlb := gseq_len T hSh (fnBody cd.params q) cd.body
  have hPend : PosOK (fnBody cd.params q + (gseq T (fnCtx (frameNames cd.params cd.body :: Γc) 0)
      (fnBody cd.params q) cd.body).length + 8) := posOK_le hc5 (by
    rw [fnCode_eq]; simp only [List.length_append, fnHead_length, paramCopies_length, List.length_singleton,
      fnPost, List.length_cons, List.length_nil, hlb]; simp [fnBody]; omega)
  have hctx := fnCtx_ok (frameNames cd.params cd.body) Γc (posOK_le hPend (by omega) : PosOK (fnBody cd.params q +
    (gseq T (fnCtx (frameNames cd.params cd.body :: Γc) 0) (fnBody cd.params q) cd.body).length + 2))
  have hPb : PosOK (fnBody cd.params q + (gseq T (fnCtx (frameNames cd.params cd.body :: Γc)
      (fnBody cd.params q + (gseq T (fnCtx (frameNames cd.params cd.body :: Γc) 0) (fnBody cd.params q)
        cd.body).length + 2)) (fnBody cd.params q) cd.body).length) := by
    rw [hlb]; exact posOK_le hPend (by omega)
  by_cases hq : HasQ ⟨entryStore st.store cd vs, st.out⟩ (d + 1) st.store.frames.size cd.body
  rotate_left
  · exact Fail.of_prefix hj (IHq (n - j) (by omega) _ _ _ _ _ _ (sp - frameSize cd.body) (frameSize cd.body) _ E
      hE.ms hE.pc hc6.2.2.2 hctx sBody hPb (by simp [frameSize]) hq)
  obtain ⟨st', t, D⟩ := hq
  obtain ⟨nb, hQ⟩ := spec_q hR (T := T) D
  have hesc : t = .brk ∨ t = .cont := by
    cases t with
    | normal => exact absurd ⟨st', .null, .closure _ _ _ _ _ _ _ _ _ _ hcd hlen hdc
        rfl D (.inl ⟨rfl, rfl⟩)⟩ hne
    | ret v => exact absurd ⟨st', v, .closure _ _ _ _ _ _ _ _ _ _ hcd hlen hdc
        rfl D (.inr rfl)⟩ hne
    | brk => exact .inl rfl
    | cont => exact .inr rfl
  refine Fail.of_star ⟨j, hj⟩ (Fail.of_err_or hR (P := fun _ => True) ?_)
  refine reaches_mono (hQ _ _ (sp - frameSize cd.body) (frameSize cd.body) _ E hE.ms hE.pc hc6.2.2.2 hctx sBody hPb
    (by simp [frameSize])) ?_
  rintro B (⟨h1, -⟩ | ⟨V', hpost⟩)
  · exact .inl ⟨h1, trivial⟩
  · have ho := hpost.out
    rcases hesc with rfl | rfl <;> exact .inl ⟨ho, trivial⟩

end

end Vsa.Compiler
