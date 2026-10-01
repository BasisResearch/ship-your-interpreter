import VsaIris.Interp.Case.VarT
import VsaIris.Interp.EnvScan
import VsaIris.Interp.SymInterp

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg FnLitT_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE inp sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 8 ≤ 0x100000000)
    (hx3 : aX.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h10 : R 10 = sret) (h11 : R 11 = inp) (h12 : R 12 = aX) (h13 : R 13 = aE) (h2 : R 2 = s)
    (hk : ldv .lw m aX.toNat = 10#64) (hku : ldv .lwu m aX.toNat = 10#64) :
    IW live m (leafView aX.toNat 0)
    (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) Q 0x80003164#64 R Mt
  by sym_run hlive using [h10, h11, h12, h13, h2, hk, hku, hsf] at 0x800033cc

#ix_seg FnLitT_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret pv aE : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709550528#64) (hA : ldv .ld Mt (s.toNat - 1088) = aE) :
    IW live m (leafView aX.toNat 0)
    (fun b => (InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) ∨ InExt (pv.toNat, 16) b)
    Q 0x800033d0#64 R Mt
  by sym_run hlive using [h2, hA, hsf] at 0x800033d4

#ix_seg FnLitT_run3 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
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
    Q 0x800033d8#64 R Mt
  by sym_run hlive using [h10, h13, h8, h9, h2, hRA, hS0, hS1, hS2, hsf, hal, e8, p8]

#ix_seg FnLitP_run2o {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret aE : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709550528#64) (hA : ldv .ld Mt (s.toNat - 1088) = aE) :
    IW live m (leafView aX.toNat 0)
    (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) Q 0x800033d0#64 R Mt
  by sym_run hlive using [h2, hA, hsf] at 0x800033d4

#ix_seg FnLitP_runOom {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709550528#64) :
    IW live m (leafView aX.toNat 0)
    (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) Q 0x80003e1c#64 R Mt
  by sym_run hlive using [h2, hsf] at 0x80003e28

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.VsaHeap VsaIris.Newlib

/- The function-literal arm from its entry, for any `Wp` and regime `ρ`: `malloc` of the closure
object, its two stores and the exit, or the out-of-memory error when `malloc` fails. -/
#ix_piece fnLitTail_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    (A : AllocSpecs live) {N : NativeAddrs} {inp : Nat} {ρ : Regime}
    {st : St} {d env : Nat} {nm : Option String} {ps : List String} {body : List Stmt}
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {aE aX s ret sret : BitVec 64}
    {rv : Nat → BitVec 64} {Mt : Mem} {K : IProp GF}
    (ent : EvalEntry s ret sret aE aX (BitVec.ofNat 64 inp) rv (evalNeed (.fn nm ps body) d)
      (.fn nm ps body) m P)
    (hexit : ∀ store' a, st.store.allocClosure ⟨env, nm, ps, body⟩ = (store', a) →
      ExitK Wp Φ N s ret sret rv (evalNeed (.fn nm ps body) d) (.closure a)
        (world N vsaLayoutP vsaRoomB inp ρ ⟨store', st.out⟩ d) K)
    (hoom : ρ = .uncounted →
      EvalAbort Wp Φ N vsaLayoutP vsaRoomB inp (.fn nm ps body) d s sret K) :
    ArmAt Wp Φ (entryF P m env aE s (evalNeed (.fn nm ps body) d) sret
      (world N vsaLayoutP vsaRoomB inp (ρ.plus closureBytes) st d) K)
      evalEntryPC (upd rv 1 ret) (InExt (s.toNat - 1088, 1088)) Mt by
  have hn := leafNode_fn ent.repr ent.ok
  have g := ent.geo; have hregs := ent.regs; have hsg := g.sg; have hbb := ent.bb
  have hneed' : 1088 + allocHeadroom ≤ evalNeed (.fn nm ps body) d := by
    unfold evalNeed stackBudget allocHeadroom; simp only [Expr.stackNeed, evalFrame]; omega
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs' := g.lo; have hs2 := g.hi; have hs3 := g.al; have hs4 := hsg.le; have hal := g.ral
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hq1 := g.slg.al; have hq2 := g.slg.lo; have hq3 := g.slg.hi
  have hneed1 := g.need
  unfold ArmAt entryF evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  ihave ⟨Hw, -, #Ht⟩ := world_allocText N vsaLayoutP vsaRoomB inp _ st d $$ Hw
  ihave ⟨%Mt0, Hms, %⟨-, hdj⟩⟩ := ms_join_sret $$ [$]
  ihave #Hdv := roOwn_data hn.view $$ [$]
  iapply wp_swpF Wp
  rotate_left
  · icombine Ht Hcode Hro Hfb Hst Hw Hk as HF; isplitl []; iexact Hdv; iframe HF Hms
  intro F'
  unfold evalEntryPC
  refine FnLitT_run1 hlive hsf hs' hs2 hs3 hx1 hx2 hx3 (by ix_reg; exact hregs.a0)
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
  unfold world worldE
  icases Hw with ⟨%H, %B, Hh, Hs, Hc, Hio, Hi, %hB, #Hbw⟩
  ihave ⟨Hs, %⟨heNZ, -, -⟩⟩ := storeRepr_frameInfo N $$ [$]
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow (n := evalNeed (.fn nm ps body) d - 1088)
    (m := allocHeadroom) (by rw [hsf]; omega) (by omega) $$ Hst
  iapply ms_callMalloc A Wp (i := 0x800033cc) (R := R1)
    ((step% jalx 0x800033cc) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
    (interp_code (by decide)) (by decide) ρ H closureBytes
    (by rw [e10]; exact ⟨by decide, by decide⟩)
    (by rw [e2]; exact ⟨by rw [hsf]; unfold allocHeadroom Vsa.Sim.tohostAddr; omega,
      by rw [hsf]; omega, by rw [hsf]; omega⟩)
  iframe Ht Hcode Hms Hh
  isplitl [Hst]
  · rw [e2]; iexact Hst
  iintro %R2 %hkeep2 Hst Hres Hms
  rw [e2]
  ihave Hst := stackScratch_widen (n := evalNeed (.fn nm ps body) d - 1088) (m := allocHeadroom)
    (by rw [hsf]; omega) (by omega) $$ [$]
  unfold mallocRes

#ix_piece fnLitTail_p2 from fnLitTail_p1 by
  icases Hres with (⟨%⟨hp0, hρ⟩, Hh⟩ | ⟨%⟨hfresh, hp16⟩, Hh, Hblk⟩)
  · have Ab := hoom hρ
    obtain ⟨jb, hok⟩ := Ab.ctx
    have hK := Ab.k; unfold AbortK at hK
    ihave ⟨#HE, Hk⟩ := hK $$ Hk
    ihave #HL := leafErrCtx_of_errCtx hok.geom hok.lt $$ HE
    ihave ⟨Herr, -⟩ := ErrnoOwn.heapRes_errno _ _ $$ Hh
    ihave #Hdv := roOwn_data hn.view $$ [$]
    iapply wp_swpF Wp
    rotate_left
    · icombine HL Hcode Hst Hio Herr Hc Hk as HF; isplitl []; iexact Hdv; iframe HF Hms
    intro F'
    refine FnLitP_run2o (aX := aX) (s := s) (sret := sret) (aE := aE) hlive hsf hs' hs2 hs3
      (by ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2) hA1 ?_
    intros
    refine (step% it 0x800033d4) hlive (fun _ => ?_) (fun hc => absurd (by
      simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hp0) hc)
    refine FnLitP_runOom (aX := aX) (s := s) (sret := sret) hlive hsf hs' hs2 hs3
      (by ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2) ?_
    intros
    apply swp_closeRM
    intro R3 Mt3 hR3 hMt3
    unfold F'
    iintro ⟨⟨#HL, #Hcode, Hst, Hio, Herr, Hc, Hk⟩, Hms⟩
    have hlo := hsg.lo; unfold Vsa.Sim.LayoutInstance.stackSL at hlo; simp only at hlo
    iapply ev_oom Wp (N := N) (L := vsaLayoutP) (Room := vsaRoomB) (inp := inp) Ab.holes Ab.code
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
    iframe HL Hcode Hms Hst Hio Herr Hc Hk

#ix_piece fnLitTail_p3 from fnLitTail_p2 by
  rw [e10, show (16#64 : BitVec 64).toNat = 16 from rfl]
  rw [e10] at hfresh
  obtain ⟨hpne, hplo, hphi, -⟩ := hfresh.destruct
  unfold blockOwn
  ihave ⟨%g, Hblk⟩ := ownSet_fn _ $$ Hblk
  ihave ⟨%Mb, Hblk⟩ := ownSet_mem _ g $$ Hblk
  ihave ⟨%M2, Hms, %⟨hag, -, hdb⟩⟩ := ms_join $$ [$]
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
  ihave #Hdv := roOwn_data hn.view $$ [$]
  iapply wp_swpF Wp
  rotate_left
  · icombine Hcode Hro Hfb Hst Hh Hs Hc Hio Hi Hbw Hk as HF; isplitl []; iexact Hdv; iframe HF Hms
  intro F'
  refine FnLitT_run2 (aX := aX) (s := s) (sret := sret) (pv := R2 10) (aE := aE) hlive hsf hs'
    hs2 hs3 (by ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2) hA2 ?_
  intros
  refine (step% it 0x800033d4) hlive (fun hc => absurd (by
    simp only [upd_apply, Nat.reduceEqDiff, ite_false] at hc
    exact congrArg BitVec.toNat hc) hpne) (fun hnz => ?_)
  refine FnLitT_run3 (aX := aX) (s := s) (sret := sret) (pv := R2 10) (aE := aE) (ret := ret)
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

#ix_piece fnLitTail_p4 from fnLitTail_p3 by
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
  ihave #HaE := astEG_of_view ent.repr ent.ok $$ Hro
  have hobj : ClosObj (imgM Mt3) (R2 10).toNat aX.toNat aE.toNat :=
    ⟨hpne, heNZ, eB0, eB8, fun k hk => by
      simp only [VsaIris.InExt] at hk
      exact ⟨by omega, by omega, Or.inr (by unfold Vsa.Sim.tohostAddr; omega),
        by omega, Or.inr (by unfold Vsa.Sim.tohostAddr; omega)⟩⟩
  iapply Wp.fupd
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
  ihave Hst := evalFrame_join hsg.le hneed1 $$ [$]
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  iapply hexit store' a halloc _ ?_
  rotate_left
  · iframe Hpc Hra Hregs Hst Hval Hk
    unfold world worldE
    iexists ((R2 10).toNat, 16) :: H, B
    iframe Hh Hs Hc Hio Hi
    isplitr
    · ipureintro; exact fun b hb => List.mem_cons_of_mem _ (hB b hb)
    · iexact Hbw
  intro y hy
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals ix_keep [hkeep2, hk1]

#ix_chain fnLitTail := [fnLitTail_p1, fnLitTail_p2, fnLitTail_p3, fnLitTail_p4]

theorem caseT_FnLit {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1) (A : AllocSpecs live)
    {N : NativeAddrs} {inp : Nat}
    {st : St} {d env : Nat} {nm : Option String} {ps : List String} {body : List Stmt}
    {store' : Store} {a : Addr}
    (halloc : st.store.allocClosure ⟨env, nm, ps, body⟩ = (store', a))
    (D : EvalECost st d env (.fn nm ps body) ⟨store', st.out⟩ (.closure a) closureBytes) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp st d env
      (.fn nm ps body) ⟨store', st.out⟩ (.closure a) closureBytes D :=
  evalEntryT hlive D fun k _ _ _ _ _ _ _ _ _ _ ent => fnLitTail (twpW _) hlive A ent
    (ρ := .counted k) (fun _ _ h => by rw [halloc] at h; cases h; exact evalKT_exit)
    (fun h => by cases h)

end VsaIris.Interp
