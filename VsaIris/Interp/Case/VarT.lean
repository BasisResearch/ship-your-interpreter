import VsaIris.Interp.ArmEval
import VsaIris.Interp.LeafErr
import VsaIris.Interp.LeafCalls
import VsaIris.Interp.SpecEnv
import VsaIris.Interp.SymInterp

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg VarT_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE inp sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 16 ≤ 0x100000000)
    (hx3 : aX.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h10 : R 10 = sret) (h11 : R 11 = inp) (h12 : R 12 = aX) (h13 : R 13 = aE) (h2 : R 2 = s)
    (hk : ldv .lw m aX.toNat = 4#64) (hku : ldv .lwu m aX.toNat = 4#64) :
    IW live m (leafView aX.toNat 8)
    (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) Q 0x80003164#64 R Mt
  by sym_run hlive using [h10, h11, h12, h13, h2, hk, hku, hsf] at 0x80003440

#ix_seg ResultCopy_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {DA : List Nat} {s sret ret v8 v9 v18 w0 w1 w2 : BitVec 64}
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
    IW live m DA
    (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) Q 0x80003448#64 R Mt
  by sym_run hlive using [h9, h2, hW0, hW1, hW2, hRA, hS0, hS1, hS2, hsf, hal, e8, e16]

#ix_seg VarP_run3 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret inp : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 16 ≤ 0x100000000)
    (hx3 : aX.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h18 : R 18 = inp) (h2 : R 2 = s + 18446744073709550528#64) :
    IW live m (leafView aX.toNat 8)
    (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) Q 0x80003f80#64 R Mt
  by sym_run hlive using [h8, h18, h2, hsf] at 0x80003fac

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.Newlib

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- What an arm's runtime-error path on expression `e` needs: the error call and the abort
contract of the continuation `K`. -/
structure EvalAbort (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (e : Expr) (d : Nat)
    (s sret : BitVec 64) (K : IProp GF) : Prop where
  holes : NewlibHoles
  code : CodeLive live
  room : ErrRoom e d
  ctx : ∃ jb, ErrCtxOK inp jb
  k : AbortK Wp Φ inp (evalCore N L Room inp) s sret (evalNeed e d) K

end

/- The var arm from its entry, for any `Wp`: `env_get`, then the result copy and the exit, or
the runtime error when the name is unbound. -/
#ix_piece varArmTail_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {ρ : Regime} {st : St}
    {d env : Nat} {x : String} (hget : ⊢ envGetSpec (GF := GF) Wp N)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {aE aX s ret sret : BitVec 64}
    {rv : Nat → BitVec 64} {Mt : Mem} {K : IProp GF}
    (ent : EvalEntry s ret sret aE aX (BitVec.ofNat 64 inp) rv (evalNeed (.var x) d) (.var x) m P)
    (hexit : ∀ v, st.store.get? env x = some v →
      ExitK Wp Φ N s ret sret rv (evalNeed (.var x) d) v (world N L Room inp ρ st d) K)
    (habort : st.store.get? env x = none → EvalAbort Wp Φ N L Room inp (.var x) d s sret K) :
    ArmAt Wp Φ (entryF P m env aE s (evalNeed (.var x) d) sret (world N L Room inp ρ st d) K)
      evalEntryPC (upd rv 1 ret) (InExt (s.toNat - 1088, 1088)) Mt by
  obtain ⟨q, hn, hfs⟩ := leafNode_var ent.repr ent.ok
  have g := ent.geo; have hregs := ent.regs; have hsg := g.sg
  have hqt : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfs.lt]
  have hneed : 1088 + envGetNeed ≤ evalNeed (.var x) d := by
    unfold evalNeed stackBudget envGetNeed; simp only [Expr.stackNeed, evalFrame]; omega
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs' := g.lo; have hs2 := g.hi; have hs3 := g.al; have hs4 := hsg.le; have hal := g.ral
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hq1 := g.slg.al; have hq2 := g.slg.lo; have hq3 := g.slg.hi
  have hneed' := g.need
  unfold ArmAt entryF evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  ihave ⟨%Mt0, Hms, %⟨-, hdj⟩⟩ := ms_join_sret $$ [$]
  ihave #Hdv := roOwn_data hn.view $$ [$]
  iapply wp_swpF Wp
  rotate_left
  · icombine Hcode Hro Hfb Hst Hw Hk as HF; isplitl []; iexact Hdv; iframe HF Hms
  intro F'
  unfold evalEntryPC
  refine VarT_run1 hlive hsf hs' hs2 hs3 hx1 hx2 hx3 (by ix_reg; exact hregs.a0)
    (by ix_reg; exact hregs.a1) (by ix_reg; exact hregs.a2) (by ix_reg; exact hregs.a3)
    (by ix_reg; exact hregs.sp) hn.kind hn.kindu ?_
  intros
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  have hRA1 : ldv .ld Mt1 (s + 18446744073709550528#64 + 1080#64).toNat = ret := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS01 : ldv .ld Mt1 (s + 18446744073709550528#64 + 1072#64).toNat = rv 8 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS11 : ldv .ld Mt1 (s + 18446744073709550528#64 + 1064#64).toNat = rv 9 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS21 : ldv .ld Mt1 (s + 18446744073709550528#64 + 1056#64).toNat = rv 18 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have e10 : R1 10 = aE := by subst hR1; ix_reg; try exact hregs.a3
  have e11 : R1 11 = BitVec.ofNat 64 q := by subst hR1; ix_reg; try exact hfs.ptr
  have e12 : R1 12 = s + 18446744073709550528#64 + 240#64 := by subst hR1; ix_reg
  have e2 : R1 2 = s + 18446744073709550528#64 := by subst hR1; ix_reg
  have e9 : R1 9 = sret := by subst hR1; ix_reg; try exact hregs.a0
  have hk1 : KeepRegs [19, 20, 21, 22, 23, 24, 25, 26, 27] rv R1 := by
    subst hR1; intro y hy
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  have ho : (R1 12).toNat = s.toNat - 1088 + 240 := by rw [e12]; exact hoff 240 (by decide)
  have hslot : ∀ b, InExt ((R1 12).toNat, 24) b → frS (s.toNat - 1088) sret.toNat b := fun b hb => by
    rw [ho] at hb; simp only [frS, VsaIris.InExt] at hb ⊢; omega
  unfold F'
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hw, Hk⟩, Hms⟩
  ihave ⟨Hms, Hout⟩ := ms_carveSlot hslot $$ Hms
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow (n := evalNeed (.var x) d - 1088) (m := envGetNeed)
    (by rw [hsf]; omega) (by omega) $$ Hst
  ihave ⟨Hw, #Hcx⟩ := world_codeX N L Room inp _ _ d $$ Hw
  ihave #Hgpv := codeRes_gpM $$ Hcode
  ihave ⟨%B, Hs, Hwk⟩ := world_store N L Room inp _ st d $$ Hw
  ihave #Hget := hget
  unfold envGetSpec
  ihave #Hg := Hget $$ %st.store %B %env %x %(R1 10) %(R1 11) %(R1 12) %(R1 2)
    %(getSaved.map fun j => (j, R1 j)) %(by simp [getSaved])
  ihave #Hx := strAt_of_cstringWithin hfs.str (sharedWin_of_readOK ent.ok) $$ Hro
  iapply ms_callEnv3 Wp (i := 0x80003440) (entry := envGetPC) (R := R1)
    ((step% jalx 0x80003440) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
    (interp_code (by decide)) (by decide)
    (φ := EnvSp (R1 2) envGetNeed ∧ SlotWin (R1 12).toNat)
    ⟨⟨(by rw [e2, hsf]; unfold htifLo envGetNeed; unfold Vsa.Sim.tohostAddr at *; omega),
       (by rw [e2, hsf]; omega), (by rw [e2, hsf]; omega)⟩,
     ⟨(by rw [ho]; omega), (by rw [ho]; omega),
       (by rw [ho]; unfold htifLo; unfold Vsa.Sim.tohostAddr at *; omega), (by rw [ho]; omega)⟩⟩
    (X := iprop(stackScratch (R1 2) envGetNeed ∗ frameAt env (R1 10).toNat ∗
      strAt (R1 11).toNat x ∗ slot24 (R1 12).toNat ∗ storeRepr N st.store B ∗ gp ↦ᵣ□ MallocFast.gpV ∗ codeX))
    (Y := fun res => iprop(stackScratch (R1 2) envGetNeed ∗ storeRepr N st.store B ∗
      getOut N st.store env x (R1 12) res))
  iframe Hg Hcode Hms Hs Hout Hgpv Hcx
  isplitl [Hst]
  · rw [e2, e10, e11, hqt]; iframe Hst Hfb Hx
  iintro %R2 %hkeep2 ⟨Hst, Hs, Hget⟩ Hms
  rw [e2]
  ihave Hst := stackScratch_widen (n := evalNeed (.var x) d - 1088) (m := envGetNeed)
    (by rw [hsf]; omega) (by omega) $$ [$]
  ihave Hw := Hwk $$ Hs
  unfold getOut

#ix_piece varArmTail_p2 from varArmTail_p1 by
  rcases hgv : st.store.get? env x with _ | v
  ·
    icases Hget with ⟨%hres, Hout⟩
    ihave ⟨%Mt2, Hms⟩ := ms_unslot hslot $$ [$]
    have A := habort hgv
    obtain ⟨jb, hok⟩ := A.ctx
    have hK := A.k; unfold AbortK at hK
    ihave ⟨#HE, Hk⟩ := hK $$ Hk
    ihave #HL := leafErrCtx_of_errCtx hok.geom hok.lt $$ HE
    ihave #Hdv := roOwn_data hn.view $$ [$]
    iapply wp_swpF Wp
    rotate_left
    · icombine HL Hcode Hx Hst Hw Hk as HF; isplitl []; iexact Hdv; iframe HF Hms
    intro F'
    refine (step% it 0x80003444) hlive (fun _ => ?_) (fun hc => absurd (by
      simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hres) hc)
    refine VarP_run3 (aX := aX) (s := s) (sret := sret) (inp := BitVec.ofNat 64 inp) hlive hsf hs'
      hs2 hs3 hx1 hx2 hx3 ?_ ?_ ?_ ?_
    · ix_reg; rw [hkeep2 8 (by decide) (by decide)]; subst hR1; ix_reg; try exact hregs.a2
    · ix_reg; rw [hkeep2 18 (by decide) (by decide)]; subst hR1; ix_reg; try exact hregs.a1
    · ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2
    intros
    apply swp_closeRM
    intro R3 Mt3 hR3 hMt3
    unfold F'
    iintro ⟨⟨#HL, #Hcode, #Hx, Hst, Hw, Hk⟩, Hms⟩
    iapply ev_rtErr Wp (N := N) (L := L) (Room := Room) (inp := inp) A.holes A.code
      ((step% jalx 0x80003fac) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
      (interp_code (by decide)) (sret := sret) (s := s) (n := evalNeed (.var x) d) (p := q) (x := x)
      (fun hro hs => varFmt_ok hro hs 0#64) hfs.lt hsg
      (by have := A.room.room; unfold evalFrame at this; omega) hdj (R := R3) (M := Mt3)
      ⟨by subst hR3; ix_reg <;> rfl, by subst hR3; ix_reg <;> rfl, by subst hR3; ix_reg <;> rfl,
       by subst hR3; ix_reg; exact hfs.ptr, by subst hR3; ix_reg <;> rfl,
       by subst hR3; ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2⟩
    iframe HL Hcode Hx Hms Hst Hw Hk

#ix_piece varArmTail_p3 from varArmTail_p2 by
  icases Hget with ⟨%hres, Hval⟩
  ihave ⟨%w0, %w1, %w2, #Hv, Hms⟩ := ms_joinSlot N hslot $$ [$]
  ihave #Hdv := roOwn_data hn.view $$ [$]
  iapply wp_swpF Wp
  rotate_left
  · icombine Hcode Hst Hw Hv Hk as HF; isplitl []; iexact Hdv; iframe HF Hms
  intro F'
  refine (step% it 0x80003444) hlive (fun hc => by
    simp only [upd_apply, Nat.reduceEqDiff, ite_false] at hc; rw [hres] at hc; exact absurd hc (by decide))
    (fun hnz => ?_)
  refine ResultCopy_run (s := s) (sret := sret) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) (w0 := w0) (w1 := w1) (w2 := w2) hlive hsf hs' hs2 hs3 hal hq1 hq2 hq3
    (inExt_disj (by decide) (by decide) hdj) (toNat_add_field (by omega) (by decide))
    (toNat_add_field (by omega) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ix_reg; rw [hkeep2 9 (by decide) (by decide)]; exact e9
  · ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2
  · rw [hoff 240 (by decide), ho]; unfold slotWrite; ix_fwd
  · rw [hoff 248 (by decide), ho]; unfold slotWrite; ix_fwd
  · rw [hoff 256 (by decide), ho]; unfold slotWrite; ix_fwd
  · rw [hoff 1080 (by decide), ho]; unfold slotWrite; ix_fwd; rw [← hoff 1080 (by decide)]; exact hRA1
  · rw [hoff 1072 (by decide), ho]; unfold slotWrite; ix_fwd; rw [← hoff 1072 (by decide)]; exact hS01
  · rw [hoff 1064 (by decide), ho]; unfold slotWrite; ix_fwd; rw [← hoff 1064 (by decide)]; exact hS11
  · rw [hoff 1056 (by decide), ho]; unfold slotWrite; ix_fwd; rw [← hoff 1056 (by decide)]; exact hS21
  intros
  apply swp_closeM
  intro Mt3 hMt3
  unfold F'
  iintro ⟨⟨#Hcode, Hst, Hw, #Hv, Hk⟩, Hms⟩

#ix_piece varArmTail_p4 from varArmTail_p3 by
  have eW0 : imgW (imgM Mt3) sret.toNat = w0 := by
    rw [← ldv_ld_imgW]; subst hMt3; ix_fwd
  have eW1 : imgW (imgM Mt3) (sret.toNat + 8) = w1 := by
    rw [← ldv_ld_imgW]; subst hMt3; ix_fwd
  have eW2 : imgW (imgM Mt3) (sret.toNat + 16) = w2 := by
    rw [← ldv_ld_imgW]; subst hMt3; ix_fwd
  ihave ⟨Hpc, Hra, Hregs, HS, Hval⟩ := ms_exit_sret N hdj $$ [Hms]
  · iframe Hms
    unfold valImg
    rw [eW0, eW1, eW2]
    iexact Hv
  ihave Hst := evalFrame_join hsg.le hneed' $$ [$]
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  iapply hexit v hgv _ ?_
  rotate_left
  · iframe Hpc Hra Hregs Hst Hval Hw Hk
  intro y hy
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals ix_keep [hkeep2, hk1]

#ix_chain varArmTail := [varArmTail_p1, varArmTail_p2, varArmTail_p3, varArmTail_p4]

theorem caseT_Var {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d env : Nat} {x : String} {v : Value}
    (D : EvalECost st d env (.var x) st v 0)
    (hget : ⊢ envGetSpec (GF := GF) (twpW (vsaModel live)) N) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.var x) st v 0 D := by
  have hgv : st.store.get? env x = some v := by cases D; assumption
  exact evalEntryT hlive D fun _ _ _ _ _ _ _ _ _ _ _ ent => varArmTail (twpW _) hlive hget ent
    (fun _ h => by rw [hgv] at h; cases h; exact evalKT_exit) (fun h => by simp [hgv] at h)

end VsaIris.Interp
