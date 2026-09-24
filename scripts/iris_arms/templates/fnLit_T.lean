import VsaIris.Interp.LeafCalls
import VsaIris.Interp.EnvScan

/-!
# `{ARM}`, total mode (family `fnLit`, INTERP_DESIGN.md §6, lane E1)

`caseT_{ARM}`: `eval_expr` on a function literal meets its total,
derivation-indexed spec in the counted regime, charged `closureBytes`. The
prologue runs to `jal malloc` (`ms_callMalloc`: `malloc(16)` cannot fail when
counted); the fresh block joins the run's bytes (`ms_join`), the run stores the
node and the environment into it and the closure into `sret`, and returns; the
block is then discarded to read-only and becomes closure `st.closures.size`
of the store (`storeRepr_allocClosure`). Template:
`scripts/iris_arms/templates/fnLit_T.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg {ARM}T_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE inp sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 8 ≤ 0x100000000)
    (hx3 : aX.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h10 : R 10 = sret) (h11 : R 11 = inp) (h12 : R 12 = aX) (h13 : R 13 = aE) (h2 : R 2 = s)
    (hk : ldv .lw m aX.toNat = {TAG}#64) (hku : ldv .lwu m aX.toNat = {TAG}#64) :
    IW live m (leafView aX.toNat 0)
    (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) Q 0x80003164#64 R Mt
  by ix_run hlive using [h10, h11, h12, h13, h2, hk, hku, hsf] at 0x{J}


#ix_seg {ARM}T_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret pv aE : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709550528#64) (hA : ldv .ld Mt (s.toNat - 1088) = aE) :
    IW live m (leafView aX.toNat 0)
    (fun b => (InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) ∨ InExt (pv.toNat, 16) b)
    Q 0x{R2}#64 R Mt
  by ix_run hlive using [h2, hA, hsf] at 0x{BR}


#ix_seg {ARM}T_run3 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret pv aE ret v8 v9 v18 : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : ret.toNat % 4 = 0)
    (hq1 : sret.toNat % 8 = 0) (hq2 : tohostAddr + 16 ≤ sret.toNat)
    (hq3 : sret.toNat + 24 ≤ 0x100000000)
    (hdj : s.toNat - 1088 + 1088 ≤ sret.toNat ∨ sret.toNat + 24 ≤ s.toNat - 1088)
    (hp1 : pv.toNat % 16 = 0) (hp2 : 0x8001c170 ≤ pv.toNat) (hp3 : pv.toNat + 16 ≤ 0x87800000)
    (hdb : pv.toNat + 16 ≤ sret.toNat ∨ sret.toNat + 24 ≤ pv.toNat)
    (e8 : (sret + 8#64).toNat = sret.toNat + 8) (p8 : (pv + 8#64).toNat = pv.toNat + 8)
    (h10 : R 10 = pv) (h13 : R 13 = aE) (h8 : R 8 = aX) (h9 : R 9 = sret)
    (h2 : R 2 = s + 18446744073709550528#64)
    (hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18) :
    IW live m (leafView aX.toNat 0)
    (fun b => (InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) ∨ InExt (pv.toNat, 16) b)
    Q 0x{R3}#64 R Mt
  by ix_run hlive using [h10, h13, h8, h9, h2, hRA, hS0, hS1, hS2, hsf, hal, e8, p8]


open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.VsaHeap

#ix_piece {ARM}T_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1) (A : AllocSpecs live)
    {N : NativeAddrs} {inp : Nat}
    {st : St} {d env : Nat} {nm : Option String} {ps : List String} {body : List Stmt}
    {store' : Store} {a : Addr}
    (halloc : st.store.allocClosure ⟨env, nm, ps, body⟩ = (store', a))
    (D : EvalECost st d env (.fn nm ps body) ⟨store', st.out⟩ (.closure a) closureBytes) :
    textOwn allocText ⊢ evalSpecT_body (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp st d env
      (.fn nm ps body) ⟨store', st.out⟩ (.closure a) closureBytes D by
  iintro #Ht
  unfold evalSpecT_body fnSpecW
  iintro %k %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
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
  iapply wp_swpF (twpW _) (F := iprop(textOwn allocText ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (s + 18446744073709550528#64) (evalNeed (.fn nm ps body) d - 1088) ∗
      world N vsaLayoutP vsaRoomB inp (.counted (k + closureBytes)) st d ∗
      (PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N vsaLayoutP vsaRoomB inp (.counted k) ⟨store', st.out⟩ d
        (.fn nm ps body) (.closure a) sret s rv -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Ht Hdv Hms Hcode Hro Hfb Hst Hw; iexact Hk
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
  iintro ⟨⟨#Ht, #Hcode, #Hro, #Hfb, Hst, Hw, Hk⟩, Hms⟩
  -- `malloc(16)`, charged `closureBytes`
  unfold world worldE
  icases Hw with ⟨%H, %B, Hh, Hs, Hc, Hio, Hi, %hB⟩
  ihave ⟨Hs, %⟨heNZ, -, -⟩⟩ := storeRepr_frameInfo N $$ [Hs Hfb]
  · iframe Hs Hfb
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow (n := evalNeed (.fn nm ps body) d - 1088)
    (m := allocHeadroom) (by rw [hsf]; omega) (by omega) $$ Hst
  iapply ms_callMalloc A (twpW _) (i := 0x{J}) (R := R1)
    (jalx_{J} live (fun p hp => hlive _ (interp_code_{J} p hp)))
    interp_code_{J} (by decide) (.counted k) H closureBytes
    (by rw [e10]; exact ⟨by decide, by decide⟩)
    (by rw [e2]; exact ⟨by rw [hsf]; unfold allocHeadroom Vsa.Sim.tohostAddr; omega,
      by rw [hsf]; omega, by rw [hsf]; omega⟩)
  simp only [Regime.plus_counted]
  iframe Ht Hcode Hms Hh
  isplitl [Hst]
  · rw [e2]; iexact Hst
  iintro %R2 %hkeep2 Hst Hres Hms
  unfold mallocRes
  icases Hres with (⟨%⟨-, hbad⟩, -⟩ | ⟨%⟨hfresh, hp16⟩, Hh, Hblk⟩)
  · cases hbad
  rw [e2]
  ihave Hst := stackScratch_widen (n := evalNeed (.fn nm ps body) d - 1088) (m := allocHeadroom)
    (by rw [hsf]; omega) (by omega) $$ [Hslack Hst]
  · iframe Hslack Hst

#ix_piece {ARM}T_p2 from {ARM}T_p1 by
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
  iapply wp_swpF (twpW _) (F := iprop(codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (s + 18446744073709550528#64) (evalNeed (.fn nm ps body) d - 1088) ∗
      heapRes vsaLayoutP vsaRoomB (.counted k) (((R2 10).toNat, 16) :: H) ∗
      storeRepr N st.store B ∗ consoleOwn st.out ∗ Stdio.stdioOwn ∗ interpCtxE inp d (errAny inp) ∗
      (PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N vsaLayoutP vsaRoomB inp (.counted k) ⟨store', st.out⟩ d
        (.fn nm ps body) (.closure a) sret s rv -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms Hcode Hro Hfb Hst Hh Hs Hc Hio Hi Hk
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
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hh, Hs, Hc, Hio, Hi, Hk⟩, Hms⟩

#ix_piece {ARM}T_p3 from {ARM}T_p2 by
  -- the closure object and the result
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
  ihave #HaX := astEG_astE _ _ $$ HaE
  iapply (twpW (vsaModel live)).fupd
  imod storeRepr_allocClosure (N := N) (s := st.store) (s' := store') (B := B)
    (cd := ⟨env, nm, ps, body⟩) (p := (R2 10).toNat) (q := aX.toNat) (e := aE.toNat)
    (img := imgM Mt3) hcl hfr hpne heNZ eB0 eB8 hbody $$ [Hs Hblk] with ⟨Hs, #Hca⟩
  · iframe Hs Hblk HaX Hfb
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
  iapply Hk $$ Hpc Hra
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
  ipureintro; exact fun b hb => List.mem_cons_of_mem _ (hB b hb)

#ix_chain caseT_{ARM} := [{ARM}T_p1, {ARM}T_p2, {ARM}T_p3]

end VsaIris.Interp
