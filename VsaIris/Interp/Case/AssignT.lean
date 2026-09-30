import VsaIris.Interp.Case.VarT
import VsaIris.Interp.SymInterp

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg AssignT_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE inp sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 24 ≤ 0x100000000)
    (hx3 : aX.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h10 : R 10 = sret) (h11 : R 11 = inp) (h12 : R 12 = aX) (h13 : R 13 = aE) (h2 : R 2 = s)
    (hk : ldv .lw m aX.toNat = 5#64) (hku : ldv .lwu m aX.toNat = 5#64) :
    IW live m (leafView aX.toNat 16) (InExt (s.toNat - 1088, 1088)) Q 0x80003164#64 R Mt
  by sym_run hlive using [h10, h11, h12, h13, h2, hk, hku, hsf] at 0x80003488

#ix_seg AssignT_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE w0 w1 w2 : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 24 ≤ 0x100000000)
    (hx3 : aX.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64)
    (hA : ldv .ld Mt (s.toNat - 1088) = aE)
    (hW0 : ldv .ld Mt (s + 18446744073709550528#64 + 240#64).toNat = w0)
    (hW1 : ldv .ld Mt (s + 18446744073709550528#64 + 248#64).toNat = w1)
    (hW2 : ldv .ld Mt (s + 18446744073709550528#64 + 256#64).toNat = w2) :
    IW live m (leafView aX.toNat 16) (InExt (s.toNat - 1088, 1088)) Q 0x8000348c#64 R Mt
  by sym_run hlive using [h8, h2, hA, hW0, hW1, hW2, hsf] at 0x800034b0

#ix_seg AssignT_run3 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret ret v8 v9 v18 w0 w1 w2 : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : ret.toNat % 4 = 0)
    (hq1 : sret.toNat % 8 = 0) (hq2 : tohostAddr + 16 ≤ sret.toNat)
    (hq3 : sret.toNat + 24 ≤ 0x100000000)
    (hdj : s.toNat - 1088 + 1088 ≤ sret.toNat ∨ sret.toNat + 24 ≤ s.toNat - 1088)
    (e8 : (sret + 8#64).toNat = sret.toNat + 8) (e16 : (sret + 16#64).toNat = sret.toNat + 16)
    (h9 : R 9 = sret) (h2 : R 2 = s + 18446744073709550528#64)
    (hW0 : ldv .ld Mt (s + 18446744073709550528#64 + 240#64).toNat = w0)
    (hW1 : ldv .ld Mt (s + 18446744073709550528#64 + 248#64).toNat = w1)
    (hW2 : ldv .ld Mt (s + 18446744073709550528#64 + 256#64).toNat = w2)
    (hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18) :
    IW live m (leafView aX.toNat 16)
    (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) Q 0x80003448#64 R Mt
  by sym_run hlive using [h9, h2, hW0, hW1, hW2, hRA, hS0, hS1, hS2, hsf, hal, e8, e16]

#ix_seg AssignP_run4 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret inp : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 24 ≤ 0x100000000)
    (hx3 : aX.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h18 : R 18 = inp) (h2 : R 2 = s + 18446744073709550528#64) :
    IW live m (leafView aX.toNat 16)
    (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) Q 0x800034b8#64 R Mt
  by sym_run hlive using [h8, h18, h2, hsf] at 0x800034e4

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.Newlib

/- The assign arm from its entry, for any `Wp`, given the mode's child call `call` (whose
continuation `Kc` holds the caller's `K` and the child's value): `env_set`, then the result
copy and the exit, or the runtime error when the name is unbound. -/
#ix_piece assignTail_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {ρ ρ' : Regime} {st : St}
    {d env : Nat} {x : String} {e : Expr} (hsetS : ⊢ envSetSpec (GF := GF) Wp N)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {aE aX s ret sret : BitVec 64}
    {rv : Nat → BitVec 64} {Mt : Mem} {K : IProp GF} {Rel : St → Value → Prop}
    {Kc : St → Value → BitVec 64 → BitVec 64 → BitVec 64 → IProp GF}
    (ent : EvalEntry s ret sret aE aX (BitVec.ofNat 64 inp) rv (evalNeed (.assign x e) d)
      (.assign x e) m P)
    (call : ∀ (qc : Nat) (R : Nat → BitVec 64) (M : Mem), ExprReprWithin m P qc e → qc < 2 ^ 64 →
      EvalRegs R (evalSP s + 240#64) (BitVec.ofNat 64 inp) (BitVec.ofNat 64 qc) aE (evalSP s) →
      (∀ R' w0 w1 w2 st' v, Rel st' v → KeepRegs calleeSaved R R' →
        ArmAt Wp Φ (evalArmF P m env aE (evalSP s) (evalNeed (.assign x e) d - 1088)
          (slot24 sret.toNat) (world N L Room inp ρ' st' d) (Kc st' v w0 w1 w2))
          0x8000348c#64 (upd R' 1 0x8000348c#64) (InExt (s.toNat - 1088, 1088))
          (slotWrite M (evalSP s + 240#64).toNat w0 w1 w2)) →
      ArmAt Wp Φ (entryF P m env aE s (evalNeed (.assign x e) d) sret (world N L Room inp ρ st d) K)
        0x80003488#64 R (InExt (s.toNat - 1088, 1088)) M)
    (hKc : ∀ st' v w0 w1 w2, Kc st' v w0 w1 w2 ⊢ K ∗ □ valOf N v w0 w1 w2)
    (hexit : ∀ st' v store'', Rel st' v → st'.store.set? env x v = some store'' →
      ExitK Wp Φ N s ret sret rv (evalNeed (.assign x e) d) v
        (world N L Room inp ρ' ⟨store'', st'.out⟩ d) K)
    (habort : ∀ st' v, Rel st' v → st'.store.set? env x v = none →
      EvalAbort Wp Φ N L Room inp (.assign x e) d s sret K) :
    ArmAt Wp Φ (entryF P m env aE s (evalNeed (.assign x e) d) sret (world N L Room inp ρ st d) K)
      evalEntryPC (upd rv 1 ret) (InExt (s.toNat - 1088, 1088)) Mt by
  obtain ⟨q, qc, hn, hfs, hch, hqc, hrc⟩ := leafNode_assign ent.repr ent.ok
  have g := ent.geo; have hregs := ent.regs; have hsg := g.sg
  have hqt : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfs.lt]
  have hneed' := g.need
  have hneed2 : 1088 + envGetNeed ≤ evalNeed (.assign x e) d - 1088 := by
    have := Expr.stackNeed_ge e
    unfold evalNeed stackBudget envGetNeed; simp only [Expr.stackNeed]; unfold evalFrame at this ⊢
    omega
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs' := g.lo; have hs2 := g.hi; have hs3 := g.al; have hs4 := hsg.le; have hal := g.ral
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hq1 := g.slg.al; have hq2 := g.slg.lo; have hq3 := g.slg.hi
  refine ArmAt.seg Wp hn.view ?_
  unfold evalEntryPC
  refine AssignT_run1 hlive hsf hs' hs2 hs3 hx1 hx2 hx3 (by ix_reg; exact hregs.a0)
    (by ix_reg; exact hregs.a1) (by ix_reg; exact hregs.a2) (by ix_reg; exact hregs.a3)
    (by ix_reg; exact hregs.sp) hn.kind hn.kindu ?_
  intros
  apply swp_closeM
  intro Mt1 hMt1
  have hRA1 : ldv .ld Mt1 (s.toNat - 1088 + 1080) = ret := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS01 : ldv .ld Mt1 (s.toNat - 1088 + 1072) = rv 8 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS11 : ldv .ld Mt1 (s.toNat - 1088 + 1064) = rv 9 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS21 : ldv .ld Mt1 (s.toNat - 1088 + 1056) = rv 18 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hA1 : ldv .ld Mt1 (s.toNat - 1088) = aE := by subst hMt1; ix_fwd
  refine call qc _ Mt1 hrc hqc ⟨by ix_reg, by ix_reg; exact hregs.a1, by ix_reg; exact hch,
    by ix_reg; exact hregs.a3, by ix_reg⟩ fun R1 w0 w1 w2 st' v hrel hkeep1 => ?_

#ix_piece assignTail_p2 from assignTail_p1 by
  refine ArmAt.seg Wp hn.view ?_
  refine AssignT_run2 (aE := aE) (w0 := w0) (w1 := w1) (w2 := w2) hlive hsf hs' hs2 hs3
    hx1 hx2 hx3 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ix_keep [hkeep1]
  · ix_keep [hkeep1]
  · ix_fwd; exact hA1
  · rw [hoff 240 (by decide)]; unfold slotWrite; ix_fwd
  · rw [hoff 248 (by decide)]; unfold slotWrite; ix_fwd
  · rw [hoff 256 (by decide)]; unfold slotWrite; ix_fwd
  intros
  apply swp_closeRM
  intro R2 M2 hR2 hM2
  have hM2' := hM2
  rw [hoff 64 (by decide), hoff 72 (by decide), hoff 80 (by decide), hoff 240 (by decide)] at hM2'
  have hsv2 : ∀ c, c = 1080 ∨ c = 1072 ∨ c = 1064 ∨ c = 1056 ∨ c = 240 ∨ c = 248 ∨ c = 256 →
      ldv .ld M2 (s.toNat - 1088 + c) = ldv .ld (slotWrite Mt1 (s.toNat - 1088 + 240) w0 w1 w2)
        (s.toNat - 1088 + c) := by
    intro c hc; rw [hM2']
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
  have hV0 : ldv .ld M2 (s.toNat - 1088 + 64) = w0 := by
    rw [hM2', ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_hit_eq _ _ rfl]
  have hV1 : ldv .ld M2 (s.toNat - 1088 + 64 + 8) = w1 := by
    rw [hM2', ldv_ld_miss _ _ (by omega), ldv_ld_hit_eq _ _ (by omega)]
  have hV2 : ldv .ld M2 (s.toNat - 1088 + 64 + 16) = w2 := by
    rw [hM2', ldv_ld_hit_eq _ _ (by omega)]
  have e10 : R2 10 = aE := by subst hR2; ix_reg
  have e11 : R2 11 = BitVec.ofNat 64 q := by subst hR2; ix_reg; try exact hfs.ptr
  have e12 : R2 12 = s + 18446744073709550528#64 + 64#64 := by subst hR2; ix_reg
  have e2 : R2 2 = s + 18446744073709550528#64 := by
    subst hR2; ix_reg; rw [keep_reg hkeep1 (by decide)]; ix_reg
  have e9 : R2 9 = sret := by
    subst hR2; ix_reg; rw [keep_reg hkeep1 (by decide)]; ix_reg; try exact hregs.a0
  have hk2 : KeepRegs [19, 20, 21, 22, 23, 24, 25, 26, 27] rv R2 := by
    subst hR2; intro y hy
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_keep [hkeep1]
  have ho : (R2 12).toNat = s.toNat - 1088 + 64 := by rw [e12]; exact hoff 64 (by decide)
  unfold evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  ihave ⟨Hk, #Hv⟩ := hKc st' v w0 w1 w2 $$ Hk
  ihave ⟨Hms, Hval⟩ := ms_carveVal N (S := InExt (s.toNat - 1088, 1088)) (a := s.toNat - 1088 + 64)
    (b := s.toNat - 1088 + 64) (img := imgM M2) (v := v)
    (fun b hb => by simp only [VsaIris.InExt] at hb ⊢; omega) rfl rfl rfl $$ [Hms]
  · iframe Hms
    simp only [valImg, ← ldv_ld_imgW]
    rw [hV0, hV1, hV2]; iexact Hv
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow (n := evalNeed (.assign x e) d - 1088)
    (m := envGetNeed) (by rw [hsf]; omega) (by omega) $$ Hst
  ihave ⟨Hw, #Hcx⟩ := world_codeX N L Room inp _ _ d $$ Hw
  ihave #Hgpv := codeRes_gpM $$ Hcode
  unfold world worldE
  icases Hw with ⟨%H, %B, Hh, Hs, Hc, Hio, Hi, %hB, #Hbw⟩
  ihave #Hset := hsetS
  unfold envSetSpec
  ihave #Hg := Hset $$ %st'.store %B %env %x %v %(R2 10) %(R2 11) %(R2 12) %(R2 2)
    %(getSaved.map fun j => (j, R2 j)) %(by simp [getSaved])
  ihave #Hx := strAt_of_cstringWithin hfs.str (sharedWin_of_readOK ent.ok) $$ Hro
  iapply ms_callEnv3 Wp (i := 0x800034b0) (entry := envSetPC) (R := R2)
    ((step% jalx 0x800034b0) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
    (interp_code (by decide)) (by decide)
    (φ := EnvSp (R2 2) envGetNeed ∧ SlotWin (R2 12).toNat)
    ⟨⟨(by rw [e2, hsf]; unfold htifLo envGetNeed; unfold Vsa.Sim.tohostAddr at *; omega),
       (by rw [e2, hsf]; omega), (by rw [e2, hsf]; omega)⟩,
     ⟨(by rw [ho]; omega), (by rw [ho]; omega),
       (by rw [ho]; unfold htifLo; unfold Vsa.Sim.tohostAddr at *; omega), (by rw [ho]; omega)⟩⟩
    (X := iprop(stackScratch (R2 2) envGetNeed ∗ frameAt env (R2 10).toNat ∗
      strAt (R2 11).toNat x ∗ valAt N (R2 12).toNat v ∗ storeRepr N st'.store B ∗ gp ↦ᵣ□ MallocFast.gpV ∗ codeX))
    (Y := fun res => iprop(stackScratch (R2 2) envGetNeed ∗ valAt N (R2 12).toNat v ∗
      setOut N st'.store B env x v res))
  iframe Hg Hcode Hms Hs Hgpv Hcx
  isplitl [Hst Hval]
  · rw [e2, e10, e11, hqt, ho]; iframe Hst Hfb Hx Hval
  iintro %R3 %hkeep3 ⟨Hst, Hval, Hso⟩ Hms
  rw [e2, ho]
  ihave Hst := stackScratch_widen (n := evalNeed (.assign x e) d - 1088) (m := envGetNeed)
    (by rw [hsf]; omega) (by omega) $$ [$]
  ihave ⟨%M3, Hms, %hag3⟩ := ms_uncarveVal N (S := InExt (s.toNat - 1088, 1088))
    (a := s.toNat - 1088 + 64) (fun b hb => by simp only [VsaIris.InExt] at hb ⊢; omega)
    $$ [$]
  ihave ⟨%M4, Hms, %⟨hag4, hdj⟩⟩ := ms_join_sret $$ [$]
  have htr : ∀ c, c = 1080 ∨ c = 1072 ∨ c = 1064 ∨ c = 1056 ∨ c = 240 ∨ c = 248 ∨ c = 256 →
      ldv .ld M4 (s.toNat - 1088 + c) = ldv .ld (slotWrite Mt1 (s.toNat - 1088 + 240) w0 w1 w2)
        (s.toNat - 1088 + c) := by
    intro c hc
    rw [← hsv2 c hc, ldv_ld_agree (M := M3) (fun i hi => hag4 _ (by
      simp only [VsaIris.InExt]; rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)),
      ldv_ld_agree (M := M2) (fun i hi => hag3 _ (by
      simp only [VsaIris.InExt]; rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      (by simp only [VsaIris.InExt]; rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega))]
  unfold setOut

#ix_piece assignTail_p3 from assignTail_p2 by
  rcases hset : st'.store.set? env x v with _ | store''
  · icases Hso with ⟨%hres, Hs⟩
    have A := habort st' v hrel hset
    obtain ⟨jb, hok⟩ := A.ctx
    have hK := A.k; unfold AbortK at hK
    ihave ⟨#HE, Hk⟩ := hK $$ Hk
    ihave #HL := leafErrCtx_of_errCtx hok.geom hok.lt $$ HE
    ihave Hw : world N L Room inp ρ' st' d $$ [Hh Hs Hc Hio Hi]
    · unfold world worldE; iexists H, B; iframe Hh Hs Hc Hio Hi; isplitr
      · ipureintro; exact hB
      · iexact Hbw
    ihave #Hdv := roOwn_data hn.view $$ [$]
    iapply wp_swpF Wp
    rotate_left
    · icombine HL Hcode Hx Hst Hw Hk as HF; isplitl []; iexact Hdv; iframe HF Hms
    intro F'
    refine (step% it 0x800034b4) hlive (fun hc => absurd (by
      simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hres) hc) (fun hz => ?_)
    refine AssignP_run4 (aX := aX) (s := s) (sret := sret) (inp := BitVec.ofNat 64 inp) hlive hsf
      hs' hs2 hs3 hx1 hx2 hx3 ?_ ?_ ?_ ?_
    · ix_reg; rw [hkeep3 8 (by decide) (by decide)]; subst hR2; ix_reg
      rw [keep_reg hkeep1 (by decide)]; ix_reg; try exact hregs.a2
    · ix_reg; rw [hkeep3 18 (by decide) (by decide)]; subst hR2; ix_reg
      rw [keep_reg hkeep1 (by decide)]; ix_reg; try exact hregs.a1
    · ix_reg; rw [hkeep3 2 (by decide) (by decide)]; exact e2
    intros
    apply swp_closeRM
    intro R5 Mt5 hR5 hMt5
    unfold F'
    iintro ⟨⟨#HL, #Hcode, #Hx, Hst, Hw, Hk⟩, Hms⟩
    iapply ev_rtErr Wp (N := N) (L := L) (Room := Room) (inp := inp) A.holes A.code
      ((step% jalx 0x800034e4) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
      (interp_code (by decide)) (sret := sret) (s := s) (n := evalNeed (.assign x e) d) (p := q)
      (x := x) (fun hro hs => assignFmt_ok hro hs 0#64) hfs.lt hsg
      (by have := A.room.room; unfold evalFrame at this; omega) hdj (R := R5) (M := Mt5)
      ⟨by subst hR5; ix_reg <;> rfl, by subst hR5; ix_reg <;> rfl, by subst hR5; ix_reg <;> rfl,
       by subst hR5; ix_reg; exact hfs.ptr, by subst hR5; ix_reg <;> rfl,
       by subst hR5; ix_reg; rw [hkeep3 2 (by decide) (by decide)]; exact e2⟩
    iframe HL Hcode Hx Hms Hst Hw Hk

#ix_piece assignTail_p4 from assignTail_p3 by
  icases Hso with ⟨%hres, Hs⟩
  ihave Hw : world N L Room inp ρ' ⟨store'', st'.out⟩ d $$ [Hh Hs Hc Hio Hi]
  · unfold world worldE; iexists H, B; iframe Hh Hs Hc Hio Hi; isplitr
    · ipureintro; exact hB
    · iexact Hbw
  ihave #Hdv := roOwn_data hn.view $$ [$]
  iapply wp_swpF Wp
  rotate_left
  · icombine Hcode Hst Hw Hv Hk as HF; isplitl []; iexact Hdv; iframe HF Hms
  intro F'
  refine (step% it 0x800034b4) hlive (fun hnz => ?_) (fun hc => absurd (by
    simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [hres]; decide) hc)
  refine AssignT_run3 (aX := aX) (s := s) (sret := sret) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) (w0 := w0) (w1 := w1) (w2 := w2) hlive hsf hs' hs2 hs3 hal hq1 hq2 hq3
    (inExt_disj (by decide) (by decide) hdj) (toNat_add_field (by omega) (by decide))
    (toNat_add_field (by omega) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ix_reg; rw [hkeep3 9 (by decide) (by decide)]; exact e9
  · ix_reg; rw [hkeep3 2 (by decide) (by decide)]; exact e2
  · rw [hoff 240 (by decide), htr 240 (by omega), slotWrite_ld0]
  · rw [hoff 248 (by decide), htr 248 (by omega), show s.toNat - 1088 + 248 = s.toNat - 1088 + 240 + 8 by omega,
      slotWrite_ld8]
  · rw [hoff 256 (by decide), htr 256 (by omega), show s.toNat - 1088 + 256 = s.toNat - 1088 + 240 + 16 by omega,
      slotWrite_ld16]
  · rw [hoff 1080 (by decide), htr 1080 (by omega), slotWrite_ld_miss _ _ _ _ (by omega)]; exact hRA1
  · rw [hoff 1072 (by decide), htr 1072 (by omega), slotWrite_ld_miss _ _ _ _ (by omega)]; exact hS01
  · rw [hoff 1064 (by decide), htr 1064 (by omega), slotWrite_ld_miss _ _ _ _ (by omega)]; exact hS11
  · rw [hoff 1056 (by decide), htr 1056 (by omega), slotWrite_ld_miss _ _ _ _ (by omega)]; exact hS21
  intros
  apply swp_closeM
  intro Mt5 hMt5
  unfold F'
  iintro ⟨⟨#Hcode, Hst, Hw, #Hv, Hk⟩, Hms⟩

#ix_piece assignTail_p5 from assignTail_p4 by
  have eW0 : imgW (imgM Mt5) sret.toNat = w0 := by
    rw [← ldv_ld_imgW]; subst hMt5; ix_fwd
  have eW1 : imgW (imgM Mt5) (sret.toNat + 8) = w1 := by
    rw [← ldv_ld_imgW]; subst hMt5; ix_fwd
  have eW2 : imgW (imgM Mt5) (sret.toNat + 16) = w2 := by
    rw [← ldv_ld_imgW]; subst hMt5; ix_fwd
  ihave ⟨Hpc, Hra, Hregs, HS, Hval⟩ := ms_exit_sret N hdj $$ [Hms]
  · iframe Hms
    unfold valImg
    rw [eW0, eW1, eW2]
    iexact Hv
  ihave Hst := evalFrame_join hsg.le hneed' $$ [$]
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  iapply hexit st' v store'' hrel hset _ ?_
  rotate_left
  · iframe Hpc Hra Hregs Hst Hval Hw Hk
  intro y hy
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals ix_keep [hkeep3, hk2]

#ix_chain assignTail := [assignTail_p1, assignTail_p2, assignTail_p3, assignTail_p4, assignTail_p5]

theorem caseT_Assign {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st' : St} {d env : Nat} {x : String} {e : Expr} {v : Value} {n : Nat} {store'' : Store}
    (De : EvalECost st d env e st' v n) (hset : st'.store.set? env x v = some store'')
    (D : EvalECost st d env (.assign x e) ⟨store'', st'.out⟩ v n)
    (he : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st' v n De)
    (hsetS : ⊢ envSetSpec (GF := GF) (twpW (vsaModel live)) N) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.assign x e)
        ⟨store'', st'.out⟩ v n D :=
  evalEntryT hlive D fun k Φ sret aE aX s ret rv P m Mt ent => assignTail (twpW _) hlive hsetS ent
    (ρ' := .counted k) (Rel := fun st1 v1 => st1 = st' ∧ v1 = v)
    (Kc := fun _ v1 w0 w1 w2 => iprop(evalKT (live := live) N L Room inp k ⟨store'', st'.out⟩ d
      (.assign x e) v sret s ret rv Φ ∗ □ valOf N v1 w0 w1 w2))
    (fun _ _ _ hrc hqc hr hk => ArmAt.callEvalT (jal_site% 0x80003488) hlive De he ent.geo
      (by have := evalNeed_assign x e d; unfold evalFrame at this; omega) (by decide) (by decide)
      (by simpa only [Expr.bodiesBound] using ent.bb) hrc ent.ok hqc hr
      fun R' w0 w1 w2 hkeep => hk R' w0 w1 w2 st' v ⟨rfl, rfl⟩ hkeep)
    (fun _ _ _ _ _ => .rfl)
    (fun _ _ _ ⟨h1, h2⟩ h => by subst h1 h2; rw [hset] at h; cases h; exact evalKT_exit)
    (fun _ _ ⟨h1, h2⟩ h => by subst h1 h2; simp [hset] at h)

end VsaIris.Interp
