import VsaIris.Vsa.MainErr
import Vsa.Sim.ExitPathSpans

/-!
# The `longjmp` landing: `interp_run` returns 1, `main` exits 70 (H5)

`longjmp(in->on_error, 1)` lands at `interp_run`'s `setjmp` return
(`0x80004428`) with `a0 = 1`, `sp` = `interp_run`'s frame and the callee-saved
registers of `interp_run`'s entry. The landing takes the `bnez`, stores
`in->call_depth = 0`, restores `interp_run`'s spills, returns 1 to `main`,
and `wp_mainErrTail` finishes with `exit(70)`. The chain is VSA's
`interpContChain` (`Vsa/Sim/ExitPathSpans.lean`):

```
80004428: bnez a0,80004508
80004508: ld a5,0(sp); li s5,1; sw zero,8(a5)
80004514: ld ra,168(sp); ld s0..s4,s6; mv a0,s5; ld s5,120(sp); addi sp,sp,176; ret
```
-/

namespace VsaIris.Newlib.Landing

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Sim VsaIris.Inst VsaIris.Interp VsaIris.Stdio VsaIris.Newlib.Sites VsaIris.Newlib.Exit
  VsaIris.Newlib.MainErr

/-! ## Segments: the `bnez` and `interp_run`'s `in`; the `call_depth` store; the epilogue -/

#derive_case land1Seg chain
  [] terminator ⟨0x80004428#64, 0x0e051063#32, 0x63#8, 0x10#8, 0x05#8, 0x0e#8,
      .br bop.BNE true, 10, 0, 0x00e0#13, 0#21, 0#12⟩ ;;
  [(0x80004508#64, 0x00013783#32),
   (0x8000450c#64, 0x00100a93#32)]

#derive_case land2Seg chain [(0x80004510#64, 0x0007a423#32)]

#derive_case land3Seg chain
  [(0x80004514#64, 0x0a813083#32),
   (0x80004518#64, 0x0a013403#32),
   (0x8000451c#64, 0x09813483#32),
   (0x80004520#64, 0x09013903#32),
   (0x80004524#64, 0x08813983#32),
   (0x80004528#64, 0x08013a03#32),
   (0x8000452c#64, 0x07013b03#32),
   (0x80004530#64, 0x000a8513#32),
   (0x80004534#64, 0x07813a83#32),
   (0x80004538#64, 0x0b010113#32)] terminator ⟨0x8000453c#64, 0x00008067#32, 0x67#8, 0x80#8,
      0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

/-- `interp_run`'s 176-byte frame in RAM above the HTIF words. -/
structure FrameI (sI : BitVec 64) : Prop where
  lo : Vsa.Sim.tohostAddr + 16 ≤ sI.toNat
  hi : sI.toNat + 176 ≤ 0x88000000
  align : sI.toNat % 16 = 0

/-- An `ld` of `interp_run`'s spill at `off`. -/
theorem frameLd {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr}
    {imgI : Nat → BitVec 8} {sI : BitVec 64} (off : Nat) (hk : a.kind = .ld)
    (hea : eaddrM a L = sI + sign_extend (m := 64) (BitVec.ofNat 12 off))
    (himm : (sign_extend (m := 64) (BitVec.ofNat 12 off) : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 176) (hg : FrameI sI)
    (hpin : ∀ k, sI.toNat ≤ k → k < sI.toNat + 176 → (m[k]?).getD 0 = imgI k) :
    MemFacts m L (imgWord imgI (sI.toNat + off)) a := by
  have h1 := hg.lo; have h2 := hg.hi
  unfold tohostAddr at h1
  refine ldFact hk (by rw [hea]; exact addr_off sI _ off himm (by omega)) (by omega) (by omega)
    (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))

abbrev l1L (v sI a5v s5v : BitVec 64) : GRegs := [(10, v), (2, sI), (15, a5v), (21, s5v)]

theorem land1_facts {m : Std.ExtHashMap Nat (BitVec 8)} {v sI a5v s5v : BitVec 64}
    {imgI : Nat → BitVec 8} (hcode : interpLandCodeLoaded m) (hv : v ≠ 0#64) (hg : FrameI sI)
    (hpin : ∀ k, sI.toNat ≤ k → k < sI.toNat + 176 → (m[k]?).getD 0 = imgI k) :
    ChainFacts m m (l1L v sI a5v s5v) [imgWord imgI sI.toNat] land1Seg := by
  unfold land1Seg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.interpLandCode_at_"
  · show (v != 0#64) = true
    simpa using hv
  · exact frameLd (off := 0) rfl rfl (by decide) (by decide) hg hpin

theorem land1_pc (v sI a5v s5v : BitVec 64) (imgI : Nat → BitVec 8) :
    evalBlocksPC 0x80004428#64 (SegEvalState.init (l1L v sI a5v s5v) [imgWord imgI sI.toNat])
      land1Seg = 0x80004510#64 := rfl

theorem land1_fin (v sI a5v s5v : BitVec 64) (imgI : Nat → BitVec 8) :
    finReg land1Seg (l1L v sI a5v s5v) [imgWord imgI sI.toNat] 10 = v ∧
    finReg land1Seg (l1L v sI a5v s5v) [imgWord imgI sI.toNat] 2 = sI ∧
    finReg land1Seg (l1L v sI a5v s5v) [imgWord imgI sI.toNat] 15 = imgW imgI sI.toNat ∧
    finReg land1Seg (l1L v sI a5v s5v) [imgWord imgI sI.toNat] 21 = 1#64 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show bytesVal .ld (imgWord imgI sI.toNat) = _; rw [bytesVal_imgWord]
  · show 0#64 + sign_extend (m := 64) (0x001#12) = _; decide

theorem land2_facts {m : Std.ExtHashMap Nat (BitVec 8)} {inp : BitVec 64}
    (hcode : interpLandCodeLoaded m)
    (hinp : 0x80000000 ≤ inp.toNat ∧ inp.toNat + 12 ≤ 0x100000000 ∧
      Vsa.Sim.tohostAddr + 16 ≤ inp.toNat ∧ inp.toNat % 4 = 0) :
    ChainFacts m m [(15, inp)] [] land2Seg := by
  obtain ⟨h1, h2, h3, h4⟩ := hinp
  unfold land2Seg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.interpLandCode_at_"
  exact swFact rfl (addr_off inp _ 8 (by decide) (by omega)) (by omega) (by omega) (by omega)
    (by omega)

theorem land2_log (inp : BitVec 64) :
    (segOut land2Seg [(15, inp)] []).log =
      [((inp + sign_extend (m := 64) (0x008#12)).toNat, 4, 0#64)] := rfl

theorem land2_pc (inp : BitVec 64) :
    evalBlocksPC 0x80004510#64 (SegEvalState.init [(15, inp)] []) land2Seg = 0x80004514#64 := rfl

abbrev l3L (sI rv s0v s1v s2v s3v s4v s6v a0v : BitVec 64) : GRegs :=
  [(2, sI), (1, rv), (8, s0v), (9, s1v), (18, s2v), (19, s3v), (20, s4v), (22, s6v), (10, a0v),
    (21, 1#64)]

abbrev l3Lds (sI : BitVec 64) (imgI : Nat → BitVec 8) : List (List (BitVec 8)) :=
  [imgWord imgI (sI.toNat + 168), imgWord imgI (sI.toNat + 160), imgWord imgI (sI.toNat + 152),
    imgWord imgI (sI.toNat + 144), imgWord imgI (sI.toNat + 136), imgWord imgI (sI.toNat + 128),
    imgWord imgI (sI.toNat + 112), imgWord imgI (sI.toNat + 120)]

theorem land3_facts {m : Std.ExtHashMap Nat (BitVec 8)}
    {sI rv s0v s1v s2v s3v s4v s6v a0v : BitVec 64} {imgI : Nat → BitVec 8}
    (hcode : interpLandCodeLoaded m) (hg : FrameI sI)
    (hra : imgW imgI (sI.toNat + 168) = 0x800045ec#64)
    (hpin : ∀ k, sI.toNat ≤ k → k < sI.toNat + 176 → (m[k]?).getD 0 = imgI k) :
    ChainFacts m m (l3L sI rv s0v s1v s2v s3v s4v s6v a0v) (l3Lds sI imgI) land3Seg := by
  unfold land3Seg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.interpLandCode_at_"
  · exact frameLd (off := 168) rfl rfl (by decide) (by decide) hg hpin
  · exact frameLd (off := 160) rfl rfl (by decide) (by decide) hg hpin
  · exact frameLd (off := 152) rfl rfl (by decide) (by decide) hg hpin
  · exact frameLd (off := 144) rfl rfl (by decide) (by decide) hg hpin
  · exact frameLd (off := 136) rfl rfl (by decide) (by decide) hg hpin
  · exact frameLd (off := 128) rfl rfl (by decide) (by decide) hg hpin
  · exact frameLd (off := 112) rfl rfl (by decide) (by decide) hg hpin
  · exact frameLd (off := 120) rfl rfl (by decide) (by decide) hg hpin
  · have e : ∀ x : BitVec 64, x = bytesVal .ld (imgWord imgI (sI.toNat + 168)) →
        (BitVec.update (x + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
      intro x hx; rw [hx, bytesVal_imgWord, hra]; decide
    exact e _ rfl

theorem land3_pc (sI rv s0v s1v s2v s3v s4v s6v a0v : BitVec 64) {imgI : Nat → BitVec 8}
    (hra : imgW imgI (sI.toNat + 168) = 0x800045ec#64) :
    evalBlocksPC 0x80004514#64
      (SegEvalState.init (l3L sI rv s0v s1v s2v s3v s4v s6v a0v) (l3Lds sI imgI)) land3Seg =
      0x800045ec#64 := by
  have e : ∀ x : BitVec 64, x = bytesVal .ld (imgWord imgI (sI.toNat + 168)) →
      BitVec.update (x + sign_extend (m := 64) (0x000#12)) 0 0#1 = 0x800045ec#64 := by
    intro x hx; rw [hx, bytesVal_imgWord, hra]; decide
  exact e _ rfl

theorem land3_fin (sI rv s0v s1v s2v s3v s4v s6v a0v : BitVec 64) {imgI : Nat → BitVec 8}
    (hra : imgW imgI (sI.toNat + 168) = 0x800045ec#64) :
    finReg land3Seg (l3L sI rv s0v s1v s2v s3v s4v s6v a0v) (l3Lds sI imgI) 2 =
      sI + sign_extend (m := 64) (0x0b0#12) ∧
    finReg land3Seg (l3L sI rv s0v s1v s2v s3v s4v s6v a0v) (l3Lds sI imgI) 1 = 0x800045ec#64 ∧
    finReg land3Seg (l3L sI rv s0v s1v s2v s3v s4v s6v a0v) (l3Lds sI imgI) 8 =
      imgW imgI (sI.toNat + 160) ∧
    finReg land3Seg (l3L sI rv s0v s1v s2v s3v s4v s6v a0v) (l3Lds sI imgI) 9 =
      imgW imgI (sI.toNat + 152) ∧
    finReg land3Seg (l3L sI rv s0v s1v s2v s3v s4v s6v a0v) (l3Lds sI imgI) 18 =
      imgW imgI (sI.toNat + 144) ∧
    finReg land3Seg (l3L sI rv s0v s1v s2v s3v s4v s6v a0v) (l3Lds sI imgI) 19 =
      imgW imgI (sI.toNat + 136) ∧
    finReg land3Seg (l3L sI rv s0v s1v s2v s3v s4v s6v a0v) (l3Lds sI imgI) 20 =
      imgW imgI (sI.toNat + 128) ∧
    finReg land3Seg (l3L sI rv s0v s1v s2v s3v s4v s6v a0v) (l3Lds sI imgI) 22 =
      imgW imgI (sI.toNat + 112) ∧
    finReg land3Seg (l3L sI rv s0v s1v s2v s3v s4v s6v a0v) (l3Lds sI imgI) 10 = 1#64 ∧
    finReg land3Seg (l3L sI rv s0v s1v s2v s3v s4v s6v a0v) (l3Lds sI imgI) 21 =
      imgW imgI (sI.toNat + 120) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show bytesVal .ld (imgWord imgI (sI.toNat + 168)) = _; rw [bytesVal_imgWord, hra]
  · show bytesVal .ld (imgWord imgI (sI.toNat + 160)) = _; rw [bytesVal_imgWord]
  · show bytesVal .ld (imgWord imgI (sI.toNat + 152)) = _; rw [bytesVal_imgWord]
  · show bytesVal .ld (imgWord imgI (sI.toNat + 144)) = _; rw [bytesVal_imgWord]
  · show bytesVal .ld (imgWord imgI (sI.toNat + 136)) = _; rw [bytesVal_imgWord]
  · show bytesVal .ld (imgWord imgI (sI.toNat + 128)) = _; rw [bytesVal_imgWord]
  · show bytesVal .ld (imgWord imgI (sI.toNat + 112)) = _; rw [bytesVal_imgWord]
  · show 1#64 + sign_extend (m := 64) (0x000#12) = _; decide
  · show bytesVal .ld (imgWord imgI (sI.toNat + 120)) = _; rw [bytesVal_imgWord]

/-! ## The rule -/

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The callee-saved registers `interp_run` restores, at their restored
values, and `s7`–`s11` from the landing. -/
def landSaved (sI : BitVec 64) (imgI : Nat → BitVec 8) (cs : Nat → BitVec 64) (r : Nat) :
    BitVec 64 :=
  if r = 9 then imgW imgI (sI.toNat + 152) else
  if r = 18 then imgW imgI (sI.toNat + 144) else
  if r = 19 then imgW imgI (sI.toNat + 136) else
  if r = 20 then imgW imgI (sI.toNat + 128) else
  if r = 21 then imgW imgI (sI.toNat + 120) else
  if r = 22 then imgW imgI (sI.toNat + 112) else cs r

/-- **The landing, then `exit(70)`**, for either WP. At `interp_run`'s
`setjmp` return with a nonzero `a0` and `sp` at `interp_run`'s frame
`sM - 176` (holding `in = sM + 272`, `main`'s link and `main`'s `s0`),
`in->call_depth`'s bytes, `main`'s saved pair, `err_msg` holding a C string,
the stack below and newlib's data: the run halts with code 70. -/
theorem wp_landing {Ierr : (Nat → BitVec 8) → Prop} (H : NewlibHolesAt Ierr)
    (live : Nat → Prop) (hlive : CodeLive live) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} (sM v rv : BitVec 64) (cs : Nat → BitVec 64) (o : String)
    (imgI imgT errImg : Nat → BitVec 8) (hsM : MainSp sM) (hv : v ≠ 0#64)
    (hinp : imgW imgI (sM - 176#64).toNat = sM + 272#64)
    (hraI : imgW imgI ((sM - 176#64).toNat + 168) = 0x800045ec#64)
    (hs0I : imgW imgI ((sM - 176#64).toNat + 160) = 0x8001b970#64)
    (hra : imgW imgT (sM.toNat + 760) = 0x80000038#64)
    (herr : ∃ k, k < 256 ∧ errImg (sM.toNat + 496 + k) = 0) :
    PC ↦ᵣ 0x80004428#64 ∗ (10 : Nat) ↦ᵣ v ∗ ra ↦ᵣ rv ∗ sp ↦ᵣ (sM - 176#64) ∗
      sepL [8, 9, 18, 19, 20, 21, 22] (fun r => iprop(∃ w, r ↦ᵣ w)) ∗
      sepL [23, 24, 25, 26, 27] (fun r => r ↦ᵣ cs r) ∗
      clobbered (argRegs.drop 1) ∗ clobbered tmpRegs ∗ gp ↦ᵣ□ gpV ∗ binImg ∗
      ownImg (InExt ((sM - 176#64).toNat, 176)) imgI ∗ blockOwn (sM.toNat + 280) 4 ∗
      stackScratch (sM - 176#64) (fprintfNeed - 176) ∗
      ownImg (InExt (sM.toNat + 752, 16)) imgT ∗ ownImg (InExt (sM.toNat + 496, 256)) errImg ∗
      stdioOwn ∗ consoleOwn o ∗ (∀ o', Φ (70, o ++ o'))
    ⊢ Wp.W Φ := by
  have h1 := hsM.lo; have h2 := hsM.hi; have h3 := hsM.align
  unfold fprintfNeed tohostAddr at h1
  have hsI : (sM - 176#64).toNat = sM.toNat - 176 := toNat_sub_frame (by simp; omega)
  have hg : FrameI (sM - 176#64) := ⟨by rw [hsI]; unfold tohostAddr; omega, by rw [hsI]; omega,
    by rw [hsI]; omega⟩
  have hcodeL := interpLandCode_text.live hlive
  unfold VsaIris.sp VsaIris.ra
  simp only [sepL_cons, sepL_nil]
  iintro ⟨Hpc, Ha0, Hra, Hsp, ⟨⟨%s0v, Hs0⟩, ⟨%s1v, Hs1⟩, ⟨%s2v, Hs2⟩, ⟨%s3v, Hs3⟩, ⟨%s4v, Hs4⟩,
    ⟨%s5v, Hs5⟩, ⟨%s6v, Hs6⟩, -⟩, Hs7, Hargs, Htmp, #Hgp, #Himg, HI, Hcd, Hscr, HT, Herr, Hstd,
    Hcon, HΦ⟩
  ihave #Hcode := instrAt_of_binImg interpLandCode_text $$ Himg
  ihave ⟨⟨%a5v, Ha5⟩, Hargs⟩ := clobbered_take (r := 15) (by decide) $$ Hargs
  ihave HI := (ownImg_range _ _ _).1 $$ HI
  -- the `bnez` and `ld a5,0(sp); li s5,1`
  iapply wp_segW live Wp land1Seg (l1L v (sM - 176#64) a5v s5v) [imgWord imgI (sM - 176#64).toNat]
    0x80004428#64 (codeFoot interpLandCodeBase interpLandCode ++ imgFoot (sM - 176#64).toNat 176 imgI)
    [] 2 (by decide)
    (by change ChainOK _ [10, 2, 15, 21] _; decide) (by change KeysOK [10, 2, 15, 21]; decide)
    (by change ∀ k ∈ wrChain land1Seg, k ∈ [10, 2, 15, 21]; decide)
    (fun a _ => trivial)
    (fun c hok' ⟨_, hMR, _, _⟩ => land1_facts
      (interpLandCodeLoaded_of (code_present hok' _
        (fun q hq => hMR q (List.mem_append_left _ hq)) hcodeL)) hv hg
      (imgFoot_pin hMR (fun q hq => List.mem_append_right _ hq)))
  have hpc1 := land1_pc v (sM - 176#64) a5v s5v imgI
  obtain ⟨e10, e2, e15, e21⟩ := land1_fin v (sM - 176#64) a5v s5v imgI
  simp only [l1L] at hpc1 e10 e2 e15 e21
  simp only [l1L, sepL_cons, sepL_nil, hpc1, e10, e2, e15, e21, hinp]
  iframe Hpc Ha0 Hsp Ha5 Hs5
  isplitr
  · iempintro
  isplitl [HI]
  · iapply (sepL_append _ _ _).2
    isplitr
    · rw [← instrAt_eq]; iexact Hcode
    iexact HI
  iintro Hpc ⟨Ha0, Hsp, Ha5, Hs5, -⟩ - HMR
  ihave ⟨-, HI⟩ := (sepL_append _ _ _).1 $$ HMR
  -- `sw zero,8(a5)`: `in->call_depth = 0`
  have hinpN : (sM + 272#64).toNat = sM.toNat + 272 := by
    rw [BitVec.toNat_add]; simp; omega
  have hin8 : (sM + 272#64 + sign_extend (m := 64) (0x008#12)).toNat = sM.toNat + 280 := by
    rw [addr_off _ _ 8 (by decide) (by omega), hinpN]
  ihave Hcd := blockOwn_range _ _ $$ Hcd
  ihave ⟨%Wcd, %hWcd, Hcd⟩ := sepL_byteAny_exists _ $$ Hcd
  iapply wp_segW live Wp land2Seg [(15, sM + 272#64)] [] 0x80004510#64
    (codeFoot interpLandCodeBase interpLandCode) Wcd 0 (by decide)
    (by change ChainOK _ [15] _; decide) (by change KeysOK [15]; decide)
    (by change ∀ k ∈ wrChain land2Seg, k ∈ [15]; decide)
    (fun a ha => by
      rw [land2_log, hin8]
      have : ¬ a ∈ List.range' (sM.toNat + 280) 4 := fun h => by
        rw [← hWcd] at h
        obtain ⟨q, hq, e⟩ := List.mem_map.mp h
        exact ha q hq e
      rw [List.mem_range'] at this
      simp only [OutL]
      refine ⟨?_, trivial⟩
      apply Classical.byContradiction; intro hc
      exact this ⟨a - (sM.toNat + 280), by omega, by omega⟩)
    (fun c hok' ⟨_, hMR, _, _⟩ => land2_facts
      (interpLandCodeLoaded_of (code_present hok' _ hMR hcodeL))
      ⟨by rw [hinpN]; omega, by rw [hinpN]; omega, by rw [hinpN]; unfold tohostAddr; omega,
        by rw [hinpN]; omega⟩)
  simp only [sepL_cons, sepL_nil, land2_pc]
  rw [← instrAt_eq]
  iframe Hpc Ha5 Hcd Hcode
  iintro Hpc ⟨Ha5, -⟩ - -
  -- `interp_run`'s epilogue and `ret` to `main`
  iapply wp_segW live Wp land3Seg (l3L (sM - 176#64) rv s0v s1v s2v s3v s4v s6v v)
    (l3Lds (sM - 176#64) imgI) 0x80004514#64
    (codeFoot interpLandCodeBase interpLandCode ++ imgFoot (sM - 176#64).toNat 176 imgI) [] 10
    (by decide)
    (by change ChainOK _ [2, 1, 8, 9, 18, 19, 20, 22, 10, 21] _; decide)
    (by change KeysOK [2, 1, 8, 9, 18, 19, 20, 22, 10, 21]; decide)
    (by change ∀ k ∈ wrChain land3Seg, k ∈ [2, 1, 8, 9, 18, 19, 20, 22, 10, 21]; decide)
    (fun a _ => trivial)
    (fun c hok' ⟨_, hMR, _, _⟩ => land3_facts
      (interpLandCodeLoaded_of (code_present hok' _
        (fun q hq => hMR q (List.mem_append_left _ hq)) hcodeL)) hg hraI
      (imgFoot_pin hMR (fun q hq => List.mem_append_right _ hq)))
  have hpc3 := land3_pc (sM - 176#64) rv s0v s1v s2v s3v s4v s6v v hraI
  obtain ⟨k2, k1, k8, k9, k18, k19, k20, k22, k10, k21⟩ :=
    land3_fin (sM - 176#64) rv s0v s1v s2v s3v s4v s6v v hraI
  simp only [l3L] at hpc3 k2 k1 k8 k9 k18 k19 k20 k22 k10 k21
  simp only [l3L, sepL_cons, sepL_nil, hpc3, k2, k1, k8, k9, k18, k19, k20, k22, k10, k21, hs0I]
  iframe Hpc Hsp Hra Hs0 Hs1 Hs2 Hs3 Hs4 Hs6 Ha0 Hs5
  isplitr
  · iempintro
  isplitl [HI]
  · iapply (sepL_append _ _ _).2
    isplitr
    · rw [← instrAt_eq]; iexact Hcode
    iexact HI
  iintro Hpc ⟨Hsp, Hra, Hs0, Hs1, Hs2, Hs3, Hs4, Hs6, Ha0, Hs5, -⟩ - HMR
  ihave ⟨-, HI⟩ := (sepL_append _ _ _).1 $$ HMR
  ihave HI := (ownImg_range _ _ _).2 $$ HI
  -- `main`'s error line and `exit(70)`
  have hsp : (sM - 176#64) + sign_extend (m := 64) (0x0b0#12) = sM := by
    rw [show (sign_extend (m := 64) (0x0b0#12) : BitVec 64) = 176#64 by decide,
      BitVec.sub_add_cancel]
  rw [hsp]
  iapply wp_mainErrTail H live hlive Wp sM 1#64 0x800045ec#64
    (landSaved (sM - 176#64) imgI cs) o imgT errImg hsM (by decide) hra herr
  unfold callFrame VsaIris.sp VsaIris.ra
  iframe Hpc Ha0 Hra Hs0 Hsp Htmp Hgp Himg HT Herr Hstd Hcon HΦ
  icases Hs7 with ⟨H23, H24, H25, H26, H27, -⟩
  isplitl [Ha5 Hargs]
  · iapply clobbered_put (r := 15) (rs := List.drop 1 argRegs) (by decide)
    iframe Hargs
    iexists _
    iexact Ha5
  isplitl [HI Hscr]
  · ihave HI := blockOwn_of_ownImg _ _ _ $$ HI
    iapply stackScratch_unframe (s := sM) (f := 176#64) (n := fprintfNeed)
      (by unfold fprintfNeed; omega) (by decide)
    rw [show (176#64 : BitVec 64).toNat = 176 from rfl]
    iframe Hscr HI
  rw [show List.drop 1 calleeSaved = [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] from rfl]
  simp only [sepL_cons, sepL_nil, landSaved]
  simp only [↓reduceIte, Nat.reduceEqDiff]
  iframe Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 H23 H24 H25 H26 H27

end Wp

end VsaIris.Newlib.Landing
