import VsaIris.Interp.SpecExecDisp
import VsaIris.Interp.SeqLoop

/-!
# `exec_stmt`'s entry spec from its dispatch-point spec (lane E5)

`execSpecT_of_disp` / `execSpecP_of_disp`: run the prologue
(`0x80003fe0`..`0x80004010`: `addi sp,sp,-176`, the five spills, the argument
moves, `li a6,8`, `auipc`/`addi a4`) and hand the dispatch-point spec its
state. Callers of `exec_stmt` through a `jal` (the block, while and for arms,
the closure body, `interp_run`) use the entry spec; the recursor proves the
dispatch-point spec (INTERP_DESIGN.md §10 "STATEMENT CHANGES (E5)").
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

/-- A frame address as a plain sum (`evalSP_off` for the 176-byte frame). -/
theorem execSP_offF {s : BitVec 64} (hsf : (execSP s).toNat = s.toNat - 176)
    (hs : s.toNat ≤ 0x100000000) (c : Nat) (hc : c < 4096) :
    (execSP s + BitVec.ofNat 64 c).toNat = s.toNat - 176 + c := by
  rw [BitVec.toNat_add, hsf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem execSP_eq (s : BitVec 64) : s - 176#64 = execSP s := by
  rw [BitVec.sub_eq_add_neg]; rfl

/-- The epilogue's `addi sp,sp,176` restores the entry `sp`. -/
theorem execSP_restore (s : BitVec 64) : execSP s + 176#64 = s := by
  rw [BitVec.add_assoc, show (18446744073709551440#64 + 176#64 : BitVec 64) = 0#64 by decide,
    BitVec.add_zero]

#ix_seg ExecProl_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s) :
    IW live m [] (InExt (s.toNat - 176, 176)) Q 0x80003fe0#64 R Mt
  by ix_run hlive using [h2, hsf] at 0x80004014


/-- The entry `sp` of an `exec_stmt` call with its budget: the frame's
geometry (`ExecFrameGeom`, the block loop's) and the frame's size. -/
theorem execFrameGeom_of {s : BitVec 64} {sm : Vsa.While.Stmt} {d : Nat}
    (hsg : StackGeom s (execNeed sm d)) : ExecFrameGeom s ∧ 176 ≤ execNeed sm d := by
  have hneed : 176 ≤ execNeed sm d := by
    have := Vsa.While.Stmt.stackNeed_ge sm; unfold execNeed stackBudget
    unfold Vsa.While.execFrame at this; omega
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  refine ⟨⟨?_, by omega, by omega, hs3⟩, hneed⟩
  have h := toNat_sub_frame (s := s) (f := 176#64) (by simp only [BitVec.toNat_ofNat]; omega)
  rwa [execSP_eq] at h

section Conv

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
variable {live : Nat → Prop} {inp : Nat}

/-- The code as a run's read-only text with an empty data view. -/
theorem codeRes_text (m : Mem) : codeRes (GF := GF) ⊢ roOwn roR (interpText ++ dataOf m []) := by
  rw [show interpText ++ dataOf m [] = interpText by simp [dataOf]]; exact .rfl

/-- **The prologue, for either WP**: from `exec_stmt`'s entry state (the
registers at `rv`, the stack below `s`), the run reaches the dispatch point
with the frame spilled; the dispatch-point continuation `K` then proves the
rest. -/
theorem wp_execProl (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {d : Nat} {sm : Stmt} {aS aE aRet s ret : BitVec 64}
    {rv : Nat → BitVec 64} {F : IProp GF}
    (hregs : ExecRegs rv (BitVec.ofNat 64 inp) aS aE aRet s) (hsg : StackGeom s (execNeed sm d))
    (hK : ∀ (R : Nat → BitVec 64) (Mt : Mem),
      DispRegs R (BitVec.ofNat 64 inp) aS aE aRet s → ExecSaved Mt s ret (rv 8) (rv 9) (rv 18) (rv 19) →
      KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] rv R →
      F ∗ codeRes ∗ ms execDispPC R (InExt (s.toNat - 176, 176)) Mt ∗
        stackScratch (execSP s) (execNeed sm d - 176) ⊢ Wp.W Φ) :
    F ∗ codeRes ∗ PC ↦ᵣ execEntryPC ∗ ra ↦ᵣ ret ∗ regFile rv ∗ stackScratch s (execNeed sm d) ⊢
      Wp.W Φ := by
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hsg
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  iintro ⟨HF, #Hcode, Hpc, Hra, Hregs, Hst⟩
  ihave ⟨Hst, Hfr⟩ := stackScratch_frame (f := 176#64) hsg.le hneed $$ Hst
  rw [execSP_eq, hfg.sf, show (176#64).toNat = 176 from rfl]
  ihave ⟨%Mt0, Hms⟩ := ms_intro $$ [Hpc Hra Hregs Hfr]
  · iframe Hpc Hra Hregs; unfold blockOwn; iexact Hfr
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ [])
    (F := iprop(F ∗ codeRes ∗ stackScratch (execSP s) (execNeed sm d - 176)))
  rotate_left
  · iframe HF Hst Hms Hcode
    iapply codeRes_text $$ Hcode
  intro F'
  unfold execEntryPC
  refine ExecProl_run (m := ∅) hlive hfg.sf hfg.lo hfg.hi hfg.al (by ix_reg; exact hregs.sp) ?_
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  have hsv : ExecSaved Mt1 s ret (rv 8) (rv 9) (rv 18) (rv 19) := by
    subst hMt1; constructor <;> (ix_fwd using [hoff]; ix_reg)
  refine .trans ?_ (hK R1 Mt1 ?_ hsv ?_)
  · unfold F'
    iintro ⟨⟨HF, #Hcode, Hst⟩, Hms⟩
    iframe HF Hcode Hst
    unfold execDispPC
    iexact Hms
  · subst hR1
    exact ⟨by ix_reg, by ix_reg; exact hregs.a1, by ix_reg; exact hregs.a0,
      by ix_reg; exact hregs.a3, by ix_reg; exact hregs.a2, by ix_reg, by ix_reg⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    subst hR1
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg

end Conv

section Specs

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- The registers `exec_stmt` returns with, as the entry spec states them. -/
theorem keep_of_execRet {rv R R' : Nat → BitVec 64} {s : BitVec 64} {status : Status}
    (hs : rv 2 = s) (hk : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] rv R)
    (h : ExecRet R R' s (rv 8) (rv 9) (rv 18) (rv 19) status) :
    KeepRegs calleeSaved rv R' ∧ R' 10 = statusCode status := by
  refine ⟨fun x hx => ?_, h.a0⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.sp.trans hs.symm
  · exact h.s0
  · exact h.s1
  · exact h.s2
  · exact h.s3
  all_goals exact (h.hi _ (by decide)).trans (hk _ (by decide))

/-- **The entry spec from the dispatch-point spec, total mode.** -/
theorem execSpecT_of_disp (hlive : ∀ p ∈ interpText, live p.1) {st : St} {d env : Nat} {sm : Stmt}
    {st' : St} {status : Status} {n : Nat} (D : ExecSCost st d env sm st' status n) :
    execDispT_body (GF := GF) (vsaModel live) N L Room inp st d env sm st' status n D ⊢
      execSpecT_body (vsaModel live) N L Room inp st d env sm st' status n D := by
  unfold execSpecT_body fnSpecW
  iintro #H %k %aS %aE %aRet %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold execPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  iapply wp_execProl (inp := inp) hlive (twpW _) (ret := ret) hregs hsg
    (F := iprop(□ astSG aS.toNat sm ∗ □ frameAt env aE.toNat ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted (k + n)) st d ∗
      (PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ execPost N L Room inp (.counted k) st' d sm status aRet s rv -∗
        (twpW (vsaModel live)).W Φ) ∗ execDispT_body (vsaModel live) N L Room inp st d env sm st' status n D))
  rotate_left
  · iframe Hpc Hra Hregs Hst Hcode Hast Hfb Hslot Hw Hk H
  intro R Mt hdr hsv hk
  iintro ⟨⟨#Hast, #Hfb, Hslot, Hw, Hk, #H⟩, #Hcode, Hms, Hst⟩
  unfold execDispT_body
  iapply H $$ %Φ %k %aS %aE %aRet %s %R %Mt %ret %(rv 8) %(rv 9) %(rv 18) %(rv 19) [Hms Hst Hslot Hw]
  · unfold execDispPre
    iframe Hms Hcode Hast Hfb Hst Hslot Hw
    ipureintro; exact ⟨hdr, hsv, hal, hsg, hslg, hbb⟩
  unfold execDispK
  iintro %R' %hret Hpc Hra Hregs Hst Hret Hw
  iapply Hk $$ Hpc Hra
  unfold execPost
  iexists R'
  iframe Hregs Hst Hret Hw
  ipureintro; exact keep_of_execRet hregs.sp hk hret

/-- **The entry spec from the dispatch-point spec, partial mode.** -/
theorem execSpecP_of_disp (hlive : ∀ p ∈ interpText, live p.1) (Core : IProp GF) {st : St}
    {d env : Nat} {sm : Stmt} :
    execDispP_body (GF := GF) (vsaModel live) N L Room inp Core st d env sm ⊢
      execSpecP_body (vsaModel live) N L Room inp Core st d env sm := by
  unfold execSpecP_body fnSpecAbort
  iintro #H %aS %aE %aRet %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold execPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  iapply wp_execProl (inp := inp) hlive (wpW _) (ret := ret) hregs hsg
    (F := iprop(□ astSG aS.toNat sm ∗ □ frameAt env aE.toNat ∗ slot24 aRet.toNat ∗
      world N L Room inp .uncounted st d ∗
      ((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' status, ⌜ExecS st d env sm st' status⌝ ∗
          execPost N L Room inp .uncounted st' d sm status aRet s rv) -∗ (wpW (vsaModel live)).W Φ) ∧
        (abortAt Core s (execNeed sm d) ∗ slot24 aRet.toNat -∗ (wpW (vsaModel live)).W Φ)) ∗
      execDispP_body (vsaModel live) N L Room inp Core st d env sm))
  rotate_left
  · iframe Hpc Hra Hregs Hst Hcode Hast Hfb Hslot Hw Hk H
  intro R Mt hdr hsv hk
  iintro ⟨⟨#Hast, #Hfb, Hslot, Hw, Hk, #H⟩, #Hcode, Hms, Hst⟩
  unfold execDispP_body
  iapply H $$ %Φ %aS %aE %aRet %s %R %Mt %ret %(rv 8) %(rv 9) %(rv 18) %(rv 19) [Hms Hst Hslot Hw]
  · unfold execDispPre
    iframe Hms Hcode Hast Hfb Hst Hslot Hw
    ipureintro; exact ⟨hdr, hsv, hal, hsg, hslg, hbb⟩
  isplit
  · iintro %st' %status %hE
    unfold execDispK
    iintro %R' %hret Hpc Hra Hregs Hst Hret Hw
    ihave Hk := and_elim_l $$ Hk
    iapply Hk $$ Hpc Hra
    iexists st', status
    unfold execPost
    isplitr
    · ipureintro; exact hE
    iexists R'
    iframe Hregs Hst Hret Hw
    ipureintro; exact keep_of_execRet hregs.sp hk hret
  · ihave Hk := and_elim_r $$ Hk
    iexact Hk

/-- The Löb hypothesis at the entry, from the one at the dispatch point. -/
theorem execSpecsP_of_disps (hlive : ∀ p ∈ interpText, live p.1) (Core : IProp GF) :
    execDispsP (GF := GF) (vsaModel live) N L Room inp Core ⊢
      execSpecsP (vsaModel live) N L Room inp Core := by
  unfold execDispsP execSpecsP
  iintro #H
  imodintro
  inext
  iintro %st %d %env %sm
  iapply execSpecP_of_disp hlive Core
  iapply H

end Specs

section Apply

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- The dispatch-point spec, total mode, as an entailment at given state. -/
theorem execDispT_apply {st : St} {d env : Nat} {sm : Stmt} {st' : St} {status : Status} {n : Nat}
    {D : ExecSCost st d env sm st' status n}
    (h : ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st d env sm st' status n D)
    (Φ : Nat × String → IProp GF) (k : Nat) (aS aE aRet s : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (ret v8 v9 v18 v19 : BitVec 64) :
    execDispPre N L Room inp (.counted (k + n)) st d env sm aS aE aRet s R Mt ret v8 v9 v18 v19 ∗
      execDispK (vsaModel live) N L Room inp (twpW (vsaModel live)) Φ (.counted k) st' d sm status
        aRet s R ret v8 v9 v18 v19 ⊢ (twpW (vsaModel live)).W Φ := by
  iintro ⟨Hpre, HK⟩
  ihave H := h
  unfold execDispT_body
  iapply H $$ %Φ %k %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK

/-- The dispatch-point spec, partial mode, as an entailment at given state. -/
theorem execDispP_apply {Core : IProp GF} {st : St} {d env : Nat} {sm : Stmt}
    (Φ : Nat × String → IProp GF) (aS aE aRet s : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (ret v8 v9 v18 v19 : BitVec 64) :
    execDispP_body (GF := GF) (vsaModel live) N L Room inp Core st d env sm ∗
      execDispPre N L Room inp .uncounted st d env sm aS aE aRet s R Mt ret v8 v9 v18 v19 ∗
      ((∀ (st' : St) (status : Status), ⌜ExecS st d env sm st' status⌝ -∗
          execDispK (vsaModel live) N L Room inp (wpW (vsaModel live)) Φ .uncounted st' d sm status
            aRet s R ret v8 v9 v18 v19) ∧
        (iprop(abortAt Core s (execNeed sm d) ∗ slot24 aRet.toNat) -∗ (wpW (vsaModel live)).W Φ))
      ⊢ (wpW (vsaModel live)).W Φ := by
  iintro ⟨H, Hpre, HK⟩
  unfold execDispP_body
  iapply H $$ %Φ %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK

/-- The Löb hypothesis at one statement. -/
theorem execDispsP_at (Core : IProp GF) (st : St) (d env : Nat) (sm : Stmt) :
    execDispsP (GF := GF) (vsaModel live) N L Room inp Core ⊢
      ▷ execDispP_body (vsaModel live) N L Room inp Core st d env sm := by
  unfold execDispsP
  iintro #H
  inext
  iapply H

end Apply

end VsaIris.Interp
