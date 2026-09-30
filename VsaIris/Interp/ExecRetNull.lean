import VsaIris.Interp.ExecDispOf
import VsaIris.Interp.SymInterp

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg ExecRetNull_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 16 ≤ 0x100000000)
    (hx3 : aS.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hk : ldv .lw m aS.toNat = 6#64) (hku : ldv .lwu m aS.toNat = 6#64)
    (hc : ldv .ld m (aS + 8#64).toNat = 0#64) :
    IW live m (stmtView aS.toNat 16) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by rw [← upd_eq_self h16]
     sym_run hlive using [h8, h14, h2, hk, hku, hc, hsf] at 0x800042f4

#ix_seg ExecRetNull_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} :
    IW live m [] (InExt (s.toNat - 176, 176)) Q 0x800042f8#64 R Mt
  by sym_run hlive at 0x80004138

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- `ret;` for every regime: the `value_null` bridge into the return slot, then the retslot
copy and the status-3 epilogue. -/
theorem retNullCore (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (vsaModel live))
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {st : St} {d env : Nat}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N Wp p)
    (Φ : Nat × String → IProp GF) (ρ : Regime) (aS aE aRet s : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (ret v8 v9 v18 v19 : BitVec 64) :
    execDispPre N L Room inp ρ st d env (.ret none) aS aE aRet s R Mt ret v8 v9 v18 v19 ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st d (.ret none) (.ret .null) aRet s R ret
        v8 v9 v18 v19 ⊢ Wp.W Φ := by
  unfold execDispPre
  iintro ⟨⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩, HK⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨hn, hc⟩ := retNullNode_of hrepr hgeo
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  have g1 : (execSP s + 16#64).toNat = s.toNat - 176 + 16 := hoff 16 (by decide)
  have hslg : SlotGeom (execSP s + 16#64) := by
    have := hfg.lo; have := hfg.hi; have := hfg.al
    refine ⟨?_, ?_, ?_⟩ <;> rw [g1] <;> (try unfold Vsa.Sim.tohostAddr) <;> omega
  ihave #Hdv := roOwn_data hn.view $$ [$]
  iapply wp_swpF Wp (F := iprop(codeRes ∗
      stackScratch (execSP s) (execNeed (.ret none) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp ρ st d ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st d
        (.ret none) (.ret .null) aRet s R ret v8 v9 v18 v19))
  rotate_left
  · iframe Hdv Hms Hcode Hst Hslot Hw; iexact HK
  intro F'
  unfold execDispPC
  refine ExecRetNull_run1 hlive hfg.sf hfg.lo hfg.hi hfg.al hn.lo hn.hi hn.off hf.regs.s0 hf.regs.a6
    hf.regs.a4 hf.regs.sp hn.kind hn.kindu hc ?_
  intros
  apply swp_closeRM
  intro R0 Mt1 hR0 hMt1
  unfold F'
  iintro ⟨⟨#Hcode, Hst, Hslot, Hw, HK⟩, Hms⟩

  ihave Hvn := hvn $$ %(execSP s + 16#64)
  unfold valueNullSpec
  iapply ms_callHelperSlot Wp (i := 0x800042f4)
    ((step% jalx 0x800042f4) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
    (interp_code (by decide)) (by decide) (a := execSP s + 16#64) (R := R0) (Mt := Mt1)
    (S := InExt (s.toNat - 176, 176)) (v := .null)
    (fun b hb => by simp only [VsaIris.InExt] at hb ⊢; rw [g1] at hb; omega) hslg
  iframe Hvn Hcode Hms
  isplitl []
  · ipureintro; subst hR0; ix_reg
  iintro %R1 %w0 %w1 %w2 %hkeep1 #Hv1 Hms
  have hk1 : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R (upd R1 1 (BitVec.ofNat 64 (0x800042f4 + 4))) := by
    subst hR0
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_keep [hkeep1]
  have hsv1 : ExecSaved (slotWrite Mt1 (execSP s + 16#64).toNat w0 w1 w2) s ret v8 v9 v18 v19 := by
    have := hfg.lo; rw [hMt1]; ix_esaved hf.saved using hoff

  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ [])
    (F := iprop(codeRes ∗ stackScratch (execSP s) (execNeed (.ret none) d - 176) ∗ slot24 aRet.toNat ∗
      □ valOf N .null w0 w1 w2 ∗ world N L Room inp ρ st d ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st d
        (.ret none) (.ret .null) aRet s R ret v8 v9 v18 v19))
  rotate_left
  · iframe Hcode Hms Hst Hslot Hv1 Hw HK
    iapply codeRes_text $$ Hcode
  intro F'
  refine ExecRetNull_run2 (m := ∅) (s := s) hlive ?_
  intros
  apply swp_closeRM
  intro R2 Mt2 hR2 hMt2
  have hcopy := wp_execRetCopy (N := N) (L := L) (Room := Room) (inp := inp) hlive Wp
    (Φ := Φ) (ρ := ρ) (st' := st) (d := d) (sm := .ret none) (v := .null) (aRet := aRet)
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

theorem retNullT (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {st : St} {d env : Nat}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p) :
    ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st d env (.ret none) st (.ret .null) 0
        (.retNull st d env) :=
  execDispT_of (GF := GF) _ (retNullCore hlive (twpW _) hvn)

theorem retNullP (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {Core : IProp GF} {st : St} {d env : Nat}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p) :
    ⊢ execDispP_body (GF := GF) (vsaModel live) N L Room inp Core st d env (.ret none) :=
  execDispP_of (GF := GF) (ExecS.retNull st d env) (retNullCore hlive (wpW _) hvn)

end

end VsaIris.Interp
