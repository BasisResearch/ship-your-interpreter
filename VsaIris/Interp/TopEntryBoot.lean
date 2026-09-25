import VsaIris.Interp.TopRunP
import VsaIris.Interp.TopBoundary
import VsaIris.Vsa.InterpImg

/-!
# `interp_run`'s entry resources from adequacy's (lane A, INTERP_DESIGN.md §5.2)

Adequacy hands the client one register points-to per entry of `topRegs`
(`sepL_of_regMap`, at `vsaReg c`) beside `bootRes` (`world_of_boundary`).
`interpRun_total_boot`/`interpRun_partial_boot` take `PC`, `ra`, the body's
register file and `codeRes`. This file supplies them:

* **the code** (`codeRes_of_boundary`): `interpText` is a slice of the fixed
  image (`interpText_img`, `Vsa/InterpImg.lean`), so `binImg` holds it
  persistently (`binImg_textOwn`); `gp`'s exclusive points-to becomes
  persistent by a ghost update (`reg_persist`);
* **the registers** (`topRegs_carve`): `topRegs` is `PC`, `ra`, `gp`, `tp` and
  `fRegs`; the values are the boundary's (`topRegs_ready`: `TopRegs`, and
  `s0 = &_impure_ptr` from `InterpRunReadyFacts.s0_impure`);
* **the runs** (`interpRun_total_top`, `interpRun_partial_top`): both boot
  theorems from `bootRes` and adequacy's registers. `tp` is not used.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.Inst VsaIris.Newlib VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.Sim.LayoutInstance Vsa.While Vsa.RuntimeRepr

/-! ## The interpreter's code is a slice of the fixed image -/

section Code

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **The interpreter's text from the image.** -/
theorem binImg_textOwn : binImg (GF := GF) ⊢ textOwn interpText :=
  binImg_sepL interpText interpText_img_mem

/-- A register points-to discarded to a read-only one. -/
theorem reg_persist (r : Nat) (v : BitVec 64) : (r ↦ᵣ v) ⊢@{IProp GF} |==> r ↦ᵣ□ v := by
  unfold regPointsTo
  iintro H
  iapply ghost_map_elem_persist $$ H

/-- The boundary's `gp` (`InterpRunPhysicalFacts.gp`) is the allocator's `gpV`. -/
theorem gpEntry_gpV : BitVec.ofNat 64 gpEntry = MallocFast.gpV := by decide

/-- **`codeRes` at the boundary**: adequacy's exclusive `gp` and the image. -/
theorem codeRes_of_boundary :
    iprop(gp ↦ᵣ MallocFast.gpV ∗ binImg) ⊢@{IProp GF} |==> codeRes := by
  unfold codeRes roOwn
  iintro ⟨Hgp, #Himg⟩
  ihave Hgp := reg_persist gp MallocFast.gpV $$ Hgp
  imod Hgp with #Hgp
  ihave #Ht := binImg_textOwn $$ Himg
  imodintro
  simp only [roR, sepL_cons, sepL_nil]
  isplitl []
  · isplitl []
    · iexact Hgp
    · iempintro
  · unfold textOwn at *
    iexact Ht

end Code

/-! ## The entry registers -/

section Regs

variable {c : Vsa.Machine.Config} {stmts count : Nat} {inp : BitVec 64} {N : NativeAddrs}
  {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}

theorem vsaReg_eq {n : Nat} {v : BitVec 64} (hn : n ≠ VsaIris.PC)
    (h : gprGet c.σ n = some v) : vsaReg c n = v := by
  rw [vsaReg_gpr hn, h]; rfl

/-- The boundary's register values at `interp_run`'s entry. -/
structure TopRegVals (c : Vsa.Machine.Config) (stmts count : Nat) : Prop where
  args : TopRegs (vsaReg c) stmts count
  s0 : vsaReg c 8 = 0x8001b970#64
  pc : vsaReg c VsaIris.PC = 0x800043ec#64
  ra : vsaReg c VsaIris.ra = 0x800045ec#64
  gp : vsaReg c gp = MallocFast.gpV

theorem topRegs_ready (F : InterpRunReadyFacts c stmts count inp N A φf φc aLeft) :
    TopRegVals c stmts count where
  args :=
    { sp := (vsaReg_eq (n := 2) (by decide) F.sp).trans (by decide)
      a0 := (vsaReg_eq (n := 10) (by decide) F.interp_arg).trans (by rw [F.interp_local]; rfl)
      a1 := vsaReg_eq (n := 11) (by decide) F.stmts_arg
      a2 := vsaReg_eq (n := 12) (by decide) F.count_arg
      a3 := vsaReg_eq (n := 13) (by decide) F.repl_arg }
  s0 := vsaReg_eq (n := 8) (by decide) F.s0_impure
  pc := by
    unfold vsaReg pcVal
    rw [if_pos rfl, F.pc]
    rfl
  ra := vsaReg_eq (n := 1) (by decide) F.ra
  gp := (vsaReg_eq (n := 3) (by decide) F.gp).trans gpEntry_gpV

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- `topRegs` as `PC`, `ra`, `gp`, `tp` and the body's registers. -/
theorem sepL_topRegs (f : Nat → BitVec 64) :
    sepL (GF := GF) topRegs (fun r => r ↦ᵣ f r) ⊢
      VsaIris.PC ↦ᵣ f VsaIris.PC ∗ VsaIris.ra ↦ᵣ f VsaIris.ra ∗ gp ↦ᵣ f gp ∗
        (4 : Nat) ↦ᵣ f 4 ∗ regFile f := by
  rw [show topRegs = VsaIris.PC :: VsaIris.ra :: 2 :: gp :: 4 :: List.range' 5 27 from rfl]
  unfold regFile
  rw [show fRegs = 2 :: List.range' 5 27 from rfl]
  simp only [sepL_cons]
  iintro ⟨Hpc, Hra, Hsp, Hgp, Htp, Hr⟩
  iframe Hpc Hra Hgp Htp Hsp Hr

/-- **Adequacy's registers as `interp_run`'s entry registers.** -/
theorem topRegs_carve (F : InterpRunReadyFacts c stmts count inp N A φf φc aLeft) :
    sepL (GF := GF) topRegs (fun r => r ↦ᵣ vsaReg c r) ⊢
      PC ↦ᵣ 0x800043ec#64 ∗ ra ↦ᵣ 0x800045ec#64 ∗ gp ↦ᵣ MallocFast.gpV ∗ (4 : Nat) ↦ᵣ vsaReg c 4 ∗
        regFile (vsaReg c) := by
  have V := topRegs_ready F
  rw [← V.pc, ← V.ra, ← V.gp]
  exact sepL_topRegs _

end Regs

/-! ## The runs from adequacy's resources -/

section Runs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- `bootRes` keeps the image (its `roOn CodeByte` is persistent). -/
theorem bootRes_binImg {c : Vsa.Machine.Config} {p : Program} (b : Boot c p) (ρ : Regime) :
    bootRes (GF := GF) b ρ ⊢ bootRes b ρ ∗ binImg := by
  unfold bootRes
  iintro ⟨Hw, Hfr, Hast, #Hcode, Hsh, Hstk, Hcal, Hoth⟩
  ihave #Himg := binImg_of_roOn b.ready.text_image b.ready.rodata_image $$ Hcode
  iframe Hw Hfr Hast Hcode Hsh Hstk Hcal Hoth Himg

/-- **`interp_run`'s entry from the boundary**: `bootRes` and adequacy's
registers give `interpRun_*_boot`'s precondition (and the unused `tp`). -/
theorem topEntry_of_regs {c : Vsa.Machine.Config} {p : Program} (b : Boot c p) (ρ : Regime) :
    bootRes (GF := GF) b ρ ∗ sepL topRegs (fun r => r ↦ᵣ vsaReg c r) ⊢@{IProp GF}
      |==> ((bootRes b ρ ∗ PC ↦ᵣ 0x800043ec#64 ∗ ra ↦ᵣ 0x800045ec#64 ∗ regFile (vsaReg c) ∗
        codeRes) ∗ (4 : Nat) ↦ᵣ vsaReg c 4) := by
  iintro ⟨Hb, Hr⟩
  ihave ⟨Hb, #Himg⟩ := bootRes_binImg b ρ $$ Hb
  ihave ⟨Hpc, Hra, Hgp, Htp, Hf⟩ := topRegs_carve b.ready $$ Hr
  imod codeRes_of_boundary $$ [Hgp] with #Hc
  · iframe Hgp Himg
  imodintro
  iframe Hb Hpc Hra Hf Hc Htp

/-- **`interp_run`'s whole run from adequacy's resources, total mode.** -/
theorem interpRun_total_top (H : NewlibHoles) (hlive : ∀ p ∈ interpText, live p.1)
    (hcl : CodeLive live) {c : Vsa.Machine.Config} {p : Program} (b : Boot c p) {st' : St}
    {n : Nat} (D : ExecSeqCost initSt 0 0 p st' .normal n)
    (hloop : interpSeqT_body (GF := GF) live b.N VsaHeap.vsaLayoutP VsaHeap.vsaRoomB inpTop initSt
      0 0 p st' .normal n D) :
    bootRes b (.counted n) ∗ sepL topRegs (fun r => r ↦ᵣ vsaReg c r) ⊢@{IProp GF}
      |==> (twpW (GF := GF) (vsaModel live)).W (fun v => iprop(⌜v = (0, st'.out)⌝)) :=
  (topEntry_of_regs b _).trans (bupd_mono (sep_elim_left.trans
    (interpRun_total_boot H hlive hcl b (topRegs_ready b.ready).args D hloop)))

/-- **`interp_run`'s whole run from adequacy's resources, partial mode.** -/
theorem interpRun_partial_top (H : NewlibHoles) (hlive : ∀ p ∈ interpText, live p.1)
    (hcl : CodeLive live) {c : Vsa.Machine.Config} {p : Program} (b : Boot c p)
    {Φ : Nat × String → IProp GF}
    (hspecs : errCtx (GF := GF) inpTop ⊢
      execSpecsP (vsaModel live) b.N VsaHeap.vsaLayoutP VsaHeap.vsaRoomB inpTop
        (evalCore b.N VsaHeap.vsaLayoutP VsaHeap.vsaRoomB inpTop))
    (hΦ0 : ∀ st', ExecSeq initSt 0 0 p st' .normal → ⊢ Φ (0, st'.out))
    (hΦe : ∀ e o, e ≠ 0 → ⊢ Φ (e, o)) :
    bootRes b .uncounted ∗ sepL topRegs (fun r => r ↦ᵣ vsaReg c r) ⊢@{IProp GF}
      |==> (wpW (GF := GF) (vsaModel live)).W Φ :=
  (topEntry_of_regs b _).trans (bupd_mono (sep_elim_left.trans
    (interpRun_partial_boot H hlive hcl b (topRegs_ready b.ready).args (topRegs_ready b.ready).s0
      hspecs hΦ0 hΦe)))

end Runs

#print axioms interpText_img
#print axioms codeRes_of_boundary
#print axioms topRegs_carve
#print axioms topEntry_of_regs
#print axioms interpRun_total_top
#print axioms interpRun_partial_top

end VsaIris.Interp
