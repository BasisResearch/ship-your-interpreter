import VsaIris.Interp.Case.{ARM}T
import VsaIris.Interp.LeafErr

/-!
# `{ARM}`, partial mode (family `fnLit`, INTERP_DESIGN.md §6, §4.2, lane E1)

`caseP_{ARM}`: `eval_expr` on a function literal meets its partial spec in the
uncounted regime. `malloc(16)` may return NULL: the `beqz` goes to the arm's
out-of-memory block (`oom80003e28`, H5's `wp_oomBlock` through `ev_oom`),
which aborts with `exit(1)`; otherwise the total case's runs build the
closure and return with `EvalE.fn`. Stated at `Core := evalCore` with
`leafErrCtx` (the binary image `exit` runs from). Template:
`scripts/iris_arms/templates/fnLit_P.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg {ARM}P_run2o {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret aE : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709550528#64) (hA : ldv .ld Mt (s.toNat - 1088) = aE) :
    IW live m (leafView aX.toNat 0)
    (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) Q 0x{R2}#64 R Mt
  by ix_run hlive using [h2, hA, hsf] at 0x{BR}


#ix_seg {ARM}P_runOom {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709550528#64) :
    IW live m (leafView aX.toNat 0)
    (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) Q 0x{E1TO}#64 R Mt
  by ix_run hlive using [h2, hsf] at 0x{OOM}

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.VsaHeap VsaIris.Newlib

#ix_piece {ARM}P_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1) (A : AllocSpecs live)
    {N : NativeAddrs} {inp : Nat}
    (HN : NewlibHoles) (hcl : CodeLive live)
    {st : St} {d env : Nat} {nm : Option String} {ps : List String} {body : List Stmt} :
    leafErrCtx inp ∗
      evalSpecsP (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp (evalCore N vsaLayoutP vsaRoomB inp) ⊢
      evalSpecP_body (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp
        (evalCore N vsaLayoutP vsaRoomB inp) st d env (.fn nm ps body) by
  iintro ⟨#HE, #-⟩
  unfold evalSpecP_body fnSpecAbort
  iintro %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  ihave ⟨Hw, -, #Ht⟩ := world_allocText N vsaLayoutP vsaRoomB inp _ st d $$ Hw
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  have hn := leafNode_fn hrepr hgeo
  have hneed' : 1088 + allocHeadroom ≤ evalNeed (.fn nm ps body) d := by
    unfold evalNeed stackBudget allocHeadroom; simp only [Expr.stackNeed, evalFrame]; omega
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hs' : 0x87800000 + 1088 ≤ s.toNat := by omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hq1 := hslg.al; have hq2 := hslg.lo; have hq3 := hslg.hi
  have hneed1 : 1088 ≤ evalNeed (.fn nm ps body) d := by unfold allocHeadroom at hneed'; omega
  ihave ⟨Hst, HF⟩ := stackScratch_frame (f := 1088#64) hsg.le hneed1 $$ Hst
  rw [hsF, hsf, show (1088#64).toNat = 1088 from rfl]
  ihave ⟨%Mt0, Hms, %hdj⟩ := ms_intro_sret $$ [Hpc Hra Hregs HF Hslot]
  · iframe Hpc Hra Hregs Hslot; unfold blockOwn; iexact HF
  -- run 1: prologue, kind dispatch, `malloc(16)`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(textOwn allocText ∗ leafErrCtx inp ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (s + 18446744073709550528#64) (evalNeed (.fn nm ps body) d - 1088) ∗
      world N vsaLayoutP vsaRoomB inp .uncounted st d ∗
      ((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.fn nm ps body) st' v⌝ ∗
          evalPost N vsaLayoutP vsaRoomB inp .uncounted st' d (.fn nm ps body) v sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt (evalCore N vsaLayoutP vsaRoomB inp) s (evalNeed (.fn nm ps body) d) ∗
          slot24 sret.toNat -∗ (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Ht HE Hdv Hms Hcode Hro Hfb Hst Hw; iexact Hk
  intro F'
  unfold evalEntryPC
  refine {ARM}T_run1 hlive hsf hs' hs2 hs3 hx1 hx2 hx3 (by ix_reg; exact hregs.a0)
    (by ix_reg; exact hregs.a1) (by ix_reg; exact hregs.a2) (by ix_reg; exact hregs.a3)
    (by ix_reg; exact hregs.sp) hn.kind hn.kindu ?_
  intros
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  have hRA1 : ldv .ld Mt1 (s.toNat - 1088 + 1080) = ret := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS01 : ldv .ld Mt1 (s.toNat - 1088 + 1072) = rv 8 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS11 : ldv .ld Mt1 (s.toNat - 1088 + 1064) = rv 9 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS21 : ldv .ld Mt1 (s.toNat - 1088 + 1056) = rv 18 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hA1 : ldv .ld Mt1 (s.toNat - 1088) = aE := by
    subst hMt1; ix_fwd; try (ix_reg; try exact hregs.a3)
  have e10 : R1 10 = 16#64 := by subst hR1; ix_reg
  have e2 : R1 2 = s + 18446744073709550528#64 := by subst hR1; ix_reg
  have e8 : R1 8 = aX := by subst hR1; ix_reg; try exact hregs.a2
  have e9 : R1 9 = sret := by subst hR1; ix_reg; try exact hregs.a0
  have hk1 : KeepRegs [19, 20, 21, 22, 23, 24, 25, 26, 27] rv R1 := by
    subst hR1; intro y hy
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  unfold F'
  iintro ⟨⟨#Ht, #HE, #Hcode, #Hro, #Hfb, Hst, Hw, Hk⟩, Hms⟩
  -- `malloc(16)`, charged `closureBytes`
  unfold world worldE
  icases Hw with ⟨%H, %B, Hh, Hs, Hc, Hio, Hi, %hB, #Hbw⟩
  ihave ⟨Hs, %⟨heNZ, -, -⟩⟩ := storeRepr_frameInfo N $$ [Hs Hfb]
  · iframe Hs Hfb
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow (n := evalNeed (.fn nm ps body) d - 1088)
    (m := allocHeadroom) (by rw [hsf]; omega) (by omega) $$ Hst
  iapply ms_callMalloc A (wpW _) (i := 0x{J}) (R := R1)
    (jalx_{J} live (fun p hp => hlive _ (interp_code_{J} p hp)))
    interp_code_{J} (by decide) .uncounted H closureBytes
    (by rw [e10]; exact ⟨by decide, by decide⟩)
    (by rw [e2]; exact ⟨by rw [hsf]; unfold allocHeadroom Vsa.Sim.tohostAddr; omega,
      by rw [hsf]; omega, by rw [hsf]; omega⟩)
  simp only [Regime.plus_uncounted]
  iframe Ht Hcode Hms Hh
  isplitl [Hst]
  · rw [e2]; iexact Hst
  iintro %R2 %hkeep2 Hst Hres Hms
  rw [e2]
  ihave Hst := stackScratch_widen (n := evalNeed (.fn nm ps body) d - 1088) (m := allocHeadroom)
    (by rw [hsf]; omega) (by omega) $$ [Hslack Hst]
  · iframe Hslack Hst

#ix_piece {ARM}P_pOom from {ARM}P_p1 by
  unfold mallocRes
  icases Hres with (⟨%⟨hp0, -⟩, Hh⟩ | ⟨%⟨hfresh, hp16⟩, Hh, Hblk⟩)
  · -- NULL: `beqz` to the out-of-memory block
    ihave ⟨Herr, -⟩ := ErrnoOwn.heapRes_errno _ _ $$ Hh
    ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
    · iframe Hcode Hro
    iapply wp_swpF (wpW _) (F := iprop(leafErrCtx inp ∗ codeRes ∗
        stackScratch (s + 18446744073709550528#64) (evalNeed (.fn nm ps body) d - 1088) ∗
        Stdio.stdioOwn ∗ Stdio.errnoOwn ∗ consoleOwn st.out ∗
        (abortAt (evalCore N vsaLayoutP vsaRoomB inp) s (evalNeed (.fn nm ps body) d) ∗
          slot24 sret.toNat -∗ (wpW (vsaModel live)).W Φ)))
    rotate_left
    · ihave Hk := and_elim_r $$ Hk
      iframe HE Hdv Hms Hcode Hst Hio Herr Hc Hk
    intro F'
    refine {ARM}P_run2o (aX := aX) (s := s) (sret := sret) (aE := aE) hlive hsf hs' hs2 hs3
      (by ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2) hA1 ?_
    intros
    refine it_{BR} hlive (fun _ => ?_) (fun hc => absurd (by
      simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hp0) hc)
    refine {ARM}P_runOom (aX := aX) (s := s) (sret := sret) hlive hsf hs' hs2 hs3
      (by ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2) ?_
    intros
    apply swp_closeRM
    intro R3 Mt3 hR3 hMt3
    unfold F'
    iintro ⟨⟨#HE, #Hcode, Hst, Hio, Herr, Hc, Hk⟩, Hms⟩
    iapply ev_oom (wpW _) (N := N) (L := vsaLayoutP) (Room := vsaRoomB) (inp := inp) HN hcl
      OomSites.oom80003e28_ok (s := s) (sret := sret) (n := evalNeed (.fn nm ps body) d) hsg
      ⟨by omega, by unfold Vsa.Sim.tohostAddr; omega,
        by show s.toNat - evalNeed (.fn nm ps body) d + 768 ≤ (evalSP s).toNat
           have : 2176 ≤ evalNeed (.fn nm ps body) d := by
             unfold evalNeed stackBudget; simp only [Expr.stackNeed, evalFrame]; omega
           rw [hsf]; omega,
        by show (evalSP s).toNat + 1032 ≤ s.toNat
           rw [hsf]; omega, hs2, by rw [hsf]; omega,
        by unfold fwriteNeed; rw [hsf]; omega⟩
      hdj (R := R3) (M := Mt3)
      (by subst hR3; ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2)
    rw [show BitVec.ofNat 64 OomSites.oom80003e28.head = 0x80003e28#64 from rfl]
    iframe HE Hcode Hms Hst Hio Herr Hc Hk

#ix_piece {ARM}P_p2 from {ARM}P_pOom by
  -- the fresh block joins the run's bytes
  rw [e10, show (16#64 : BitVec 64).toNat = 16 from rfl]
  rw [e10] at hfresh
  obtain ⟨hpne, hplo, hphi, -⟩ := hfresh.destruct
  unfold blockOwn
  ihave ⟨%g, Hblk⟩ := ownSet_fn _ $$ Hblk
  ihave ⟨%Mb, Hblk⟩ := ownSet_mem _ g $$ Hblk
  ihave ⟨%M2, Hms, %⟨hag, -, hdb⟩⟩ := ms_join $$ [Hms Hblk]
  · iframe Hms Hblk
  have hA2 : ldv .ld M2 (s.toNat - 1088) = aE := by
    rw [ldv_ld_agree (M := Mt1) (fun i hi => hag _ (Or.inl (by simp only [VsaIris.InExt]; omega)))]
    exact hA1
  have hsp2 : ∀ c, c = 1080 ∨ c = 1072 ∨ c = 1064 ∨ c = 1056 →
      ldv .ld M2 (s.toNat - 1088 + c) = ldv .ld Mt1 (s.toNat - 1088 + c) := by
    intro c hc
    exact ldv_ld_agree (fun i hi => hag _ (Or.inl (by
      simp only [VsaIris.InExt]; rcases hc with rfl | rfl | rfl | rfl <;> omega)))
  have hdbI : (R2 10).toNat + 16 ≤ sret.toNat ∨ sret.toNat + 24 ≤ (R2 10).toNat := by
    have := inExt_disj (a := sret.toNat) (n := 24) (c := (R2 10).toNat) (k := 16) (by decide)
      (by decide) (fun b h1 h2 => hdb b (Or.inr h1) h2)
    omega
  simp only [vsaLayoutP, Vsa.Sim.DlHeap.heapStart, Vsa.Sim.DlHeap.heapEnd] at hplo hphi
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (s + 18446744073709550528#64) (evalNeed (.fn nm ps body) d - 1088) ∗
      heapRes vsaLayoutP vsaRoomB .uncounted (((R2 10).toNat, 16) :: H) ∗
      storeRepr N st.store B ∗ consoleOwn st.out ∗ Stdio.stdioOwn ∗ interpCtxE inp d (errAny inp) ∗
      Newlib.binImg ∗
      ((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.fn nm ps body) st' v⌝ ∗
          evalPost N vsaLayoutP vsaRoomB inp .uncounted st' d (.fn nm ps body) v sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt (evalCore N vsaLayoutP vsaRoomB inp) s (evalNeed (.fn nm ps body) d) ∗
          slot24 sret.toNat -∗ (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms Hcode Hro Hfb Hst Hh Hs Hc Hio Hi Hbw Hk
  intro F'
  refine {ARM}T_run2 (aX := aX) (s := s) (sret := sret) (pv := R2 10) (aE := aE) hlive hsf hs'
    hs2 hs3 (by ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2) hA2 ?_
  intros
  refine it_{BR} hlive (fun hc => absurd (by
    simp only [upd_apply, Nat.reduceEqDiff, ite_false] at hc
    exact congrArg BitVec.toNat hc) hpne) (fun hnz => ?_)
  refine {ARM}T_run3 (aX := aX) (s := s) (sret := sret) (pv := R2 10) (aE := aE) (ret := ret)
    (v8 := rv 8) (v9 := rv 9) (v18 := rv 18) hlive hsf hs' hs2 hs3 hal hq1 hq2 hq3
    (inExt_disj (by decide) (by decide) hdj) hp16 hplo hphi hdbI
    (toNat_add_field (by omega) (by decide)) (toNat_add_field (by omega) (by decide))
    (by ix_reg) (by ix_reg)
    (by ix_reg; rw [hkeep2 8 (by decide) (by decide)]; exact e8)
    (by ix_reg; rw [hkeep2 9 (by decide) (by decide)]; exact e9)
    (by ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2)
    ?_ ?_ ?_ ?_ ?_
  · rw [hoff 1080 (by decide), hsp2 1080 (by omega)]; exact hRA1
  · rw [hoff 1072 (by decide), hsp2 1072 (by omega)]; exact hS01
  · rw [hoff 1064 (by decide), hsp2 1064 (by omega)]; exact hS11
  · rw [hoff 1056 (by decide), hsp2 1056 (by omega)]; exact hS21
  apply swp_closeM
  intro Mt3 hMt3
  unfold F'
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hh, Hs, Hc, Hio, Hi, #Hbw, Hk⟩, Hms⟩

#ix_piece {ARM}P_p3 from {ARM}P_p2 by
  -- the closure object and the result
  rcases halloc : st.store.allocClosure ⟨env, nm, ps, body⟩ with ⟨store', a⟩
  have eB0 : imgLE (imgM Mt3) (R2 10).toNat 8 = aX.toNat := by
    rw [← imgW_toNat, ← ldv_ld_imgW]; subst hMt3; ix_fwd
  have eB8 : imgLE (imgM Mt3) ((R2 10).toNat + 8) 8 = aE.toNat := by
    rw [← imgW_toNat, ← ldv_ld_imgW]; subst hMt3; ix_fwd
  have eS0 : (imgW (imgM Mt3) sret.toNat).toNat % 2 ^ 32 = 4 := by
    rw [imgW_low4]; subst hMt3; rw [imgLE_store4_hit]; rfl
  have eS8 : imgW (imgM Mt3) (sret.toNat + 8) = R2 10 := by
    rw [← ldv_ld_imgW]; subst hMt3; ix_fwd
  have ha : a = st.store.closures.size := by
    simp only [Store.allocClosure, Prod.mk.injEq] at halloc; exact halloc.2.symm
  have hcl : store'.closures.toList = st.store.closures.toList ++ [⟨env, nm, ps, body⟩] := by
    simp only [Store.allocClosure, Prod.mk.injEq] at halloc; rw [← halloc.1]; simp
  have hfr : store'.frames = st.store.frames := by
    simp only [Store.allocClosure, Prod.mk.injEq] at halloc; rw [← halloc.1]
  have hbody : Stmt.stackNeedList body ≤ perCallBudget ∧
      Stmt.bodiesBoundList perCallBudget body = true := by
    simp only [Expr.bodiesBound, Bool.and_eq_true, decide_eq_true_eq] at hbb; exact hbb
  ihave ⟨Hms, Hblk⟩ := ms_split (S := frS (s.toNat - 1088) sret.toNat)
    (T := InExt ((R2 10).toNat, 16)) (fun b h1 h2 => hdb b h1 h2) $$ Hms
  ihave #HaE := astEG_of_view hrepr hgeo $$ Hro
  have hobj : ClosObj (imgM Mt3) (R2 10).toNat aX.toNat aE.toNat :=
    ⟨hpne, heNZ, eB0, eB8, fun k hk => by
      simp only [VsaIris.InExt] at hk
      exact ⟨by omega, by omega, Or.inr (by unfold Vsa.Sim.tohostAddr; omega),
        by omega, Or.inr (by unfold Vsa.Sim.tohostAddr; omega)⟩⟩
  iapply (wpW (vsaModel live)).fupd
  imod storeRepr_allocClosure (N := N) (s := st.store) (s' := store') (B := B)
    (cd := ⟨env, nm, ps, body⟩) (p := (R2 10).toNat) (q := aX.toNat) (e := aE.toNat)
    (img := imgM Mt3) hcl hfr hobj hbody $$ [Hs Hblk] with ⟨Hs, #Hca⟩
  · iframe Hs Hblk HaE Hfb
  imodintro
  ihave ⟨Hpc, Hra, Hregs, HS, Hval⟩ := ms_exit_sret N (v := .closure a) hdj $$ [Hms]
  · iframe Hms
    unfold valImg
    rw [eS8, ha]
    simp only [valOf]
    iframe Hca
    ipureintro; exact ⟨eS0, hpne⟩
  ihave Hst := evalFrame_join hsg.le hneed1 $$ [Hst HS]
  · iframe Hst HS
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  ihave Hk := and_elim_l $$ Hk
  iapply Hk $$ Hpc Hra
  iexists ⟨store', st.out⟩, (.closure a)
  isplitl []
  · ipureintro; exact EvalE.fn st d env nm ps body store' a halloc
  unfold evalPost
  iexists _
  iframe Hregs Hst Hval
  isplitl []
  · ipureintro
    intro y hy
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
    all_goals ix_keep [hkeep2, hk1]
  unfold world worldE
  iexists ((R2 10).toNat, 16) :: H, B
  iframe Hh Hs Hc Hio Hi
  isplitr
  · ipureintro; exact fun b hb => List.mem_cons_of_mem _ (hB b hb)
  · iexact Hbw

#ix_chain caseP_{ARM} := [{ARM}P_p1, {ARM}P_pOom, {ARM}P_p2, {ARM}P_p3]

end VsaIris.Interp
