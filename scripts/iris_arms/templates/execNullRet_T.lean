import VsaIris.Interp.ExecArm

/-!
# `{ARM}`, total mode (family `execNullRet`, lane E5)

`caseT_{ARM}`: `exec_stmt` on `{SM}` meets its dispatch-point spec
(`execDispT_body`), given `value_null`'s spec. The kind dispatch and the NULL
test are one run (`{ARM}_run1`, to the `jal value_null` at `0x{J1}` with the
frame slot `sp+16`); `value_null` fills the slot (`ms_callHelperSlot`); the
jump back (`{ARM}_run2`) reaches the shared `ret` exit `wp_execRetCopy`.
Template: `scripts/iris_arms/templates/execNullRet_T.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg {ARM}_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 16 ≤ 0x100000000)
    (hx3 : aS.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hk : ldv .lw m aS.toNat = {TAG}#64) (hku : ldv .lwu m aS.toNat = {TAG}#64)
    (hc : ldv .ld m (aS + {FOFF}#64).toNat = 0#64) :
    IW live m (stmtView aS.toNat {W}) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by rw [← upd_eq_self h16]
     ix_run hlive using [h8, h14, h2, hk, hku, hc, hsf] at 0x{J1}

#ix_seg {ARM}_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} :
    IW live m [] (InExt (s.toNat - 176, 176)) Q 0x{J1N}#64 R Mt
  by ix_run hlive at 0x80004138

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

theorem caseT_{ARM} {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d env : Nat}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p) :
    ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st d env ({SM}) st (.ret .null) 0
        (.{SEM} st d env) := by
  unfold execDispT_body
  iintro !> %Φ %k %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  unfold execDispPre
  icases Hpre with ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨hn, hc⟩ := {NODE} hrepr hgeo
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  have g1 : (execSP s + 16#64).toNat = s.toNat - 176 + 16 := hoff 16 (by decide)
  have hslg : SlotGeom (execSP s + 16#64) := by
    have := hfg.lo; have := hfg.hi; have := hfg.al
    refine ⟨?_, ?_, ?_⟩ <;> rw [g1] <;> (try unfold Vsa.Sim.tohostAddr) <;> omega
  simp only [Nat.add_zero]
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(codeRes ∗
      stackScratch (execSP s) (execNeed ({SM}) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted k) st d ∗
      execDispK (vsaModel live) N L Room inp (twpW (vsaModel live)) Φ (.counted k) st d
        ({SM}) (.ret .null) aRet s R ret v8 v9 v18 v19))
  rotate_left
  · iframe Hdv Hms Hcode Hst Hslot Hw; iexact HK
  intro F'
  unfold execDispPC
  refine {ARM}_run1 hlive hfg.sf hfg.lo hfg.hi hfg.al hn.lo hn.hi hn.off hf.regs.s0 hf.regs.a6
    hf.regs.a4 hf.regs.sp hn.kind hn.kindu hc ?_
  intros
  apply swp_closeRM
  intro R0 Mt1 hR0 hMt1
  unfold F'
  iintro ⟨⟨#Hcode, Hst, Hslot, Hw, HK⟩, Hms⟩
  -- value_null into the frame slot
  ihave Hvn := hvn $$ %(execSP s + 16#64)
  unfold valueNullSpec
  iapply ms_callHelperSlot (twpW _) (i := 0x{J1})
    (jalx_{J1} live (fun p hp => hlive _ (interp_code_{J1} p hp)))
    interp_code_{J1} (by decide) (a := execSP s + 16#64) (R := R0) (Mt := Mt1)
    (S := InExt (s.toNat - 176, 176)) (v := .null)
    (fun b hb => by simp only [VsaIris.InExt] at hb ⊢; rw [g1] at hb; omega) hslg
  iframe Hvn Hcode Hms
  isplitl []
  · ipureintro; subst hR0; ix_reg
  iintro %R1 %w0 %w1 %w2 %hkeep1 #Hv1 Hms
  have hk1 : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R (upd R1 1 (BitVec.ofNat 64 (0x{J1} + 4))) := by
    subst hR0
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_keep [hkeep1]
  have hsv1 : ExecSaved (slotWrite Mt1 (execSP s + 16#64).toNat w0 w1 w2) s ret v8 v9 v18 v19 := by
    have := hfg.lo; rw [hMt1]; ix_esaved hf.saved using hoff
  -- the jump to the `ret` exit
  iapply wp_swpF (twpW _) (text := interpText ++ dataOf ∅ [])
    (F := iprop(codeRes ∗ stackScratch (execSP s) (execNeed ({SM}) d - 176) ∗ slot24 aRet.toNat ∗
      □ valOf N .null w0 w1 w2 ∗ world N L Room inp (.counted k) st d ∗
      execDispK (vsaModel live) N L Room inp (twpW (vsaModel live)) Φ (.counted k) st d
        ({SM}) (.ret .null) aRet s R ret v8 v9 v18 v19))
  rotate_left
  · iframe Hcode Hms Hst Hslot Hv1 Hw HK
    iapply codeRes_text $$ Hcode
  intro F'
  refine {ARM}_run2 (m := ∅) (s := s) hlive ?_
  intros
  apply swp_closeRM
  intro R2 Mt2 hR2 hMt2
  have hcopy := wp_execRetCopy (N := N) (L := L) (Room := Room) (inp := inp) hlive (twpW _)
    (Φ := Φ) (ρ := .counted k) (st' := st) (d := d) (sm := {SM}) (v := .null) (aRet := aRet)
    (s := s) (ret := ret) (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) (w0 := w0) (w1 := w1)
    (w2 := w2) (R0 := R) (R := R2) (Mt := Mt2) hf.stack hf.slot hf.ral
    (by subst hR2 hR0; ix_reg; rw [keep_helper hkeep1 (by decide) (by decide)]; ix_reg; exact hf.regs.sp)
    (by subst hR2 hR0; ix_reg; rw [keep_helper hkeep1 (by decide) (by decide)]; ix_reg; exact hf.regs.s2)
    (by rw [hMt2]; exact hsv1) (by subst hR2; exact hk1)
    (by rw [hMt2, ← g1]; ix_fwd)
    (by rw [hMt2, show s.toNat - 176 + 24 = (execSP s + 16#64).toNat + 8 by omega]; ix_fwd)
    (by rw [hMt2, show s.toNat - 176 + 32 = (execSP s + 16#64).toNat + 16 by omega]; ix_fwd)
  unfold F'
  iintro ⟨⟨#Hcode, Hst, Hslot, #Hv1, Hw, HK⟩, Hms⟩
  iapply hcopy
  iframe Hcode Hms Hslot Hv1 Hst Hw HK

end VsaIris.Interp
