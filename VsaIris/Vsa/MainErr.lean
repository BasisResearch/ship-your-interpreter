import VsaIris.Vsa.Exit
import VsaIris.Vsa.SegImg
import VsaIris.Vsa.StdioRead
import Vsa.Sim.rows.ErrSegCrt0
import Vsa.Sim.Muldi3Spec

/-!
# `main`'s error line and `exit(70)` (H5)

`interp_run` returned nonzero to `main` (`0x800045ec`, `a0 ≠ 0`). `main` loads
`stderr` through `_impure_ptr`, calls `fprintf(stderr, "%s\n", in->err_msg)`
(`IrisHoles.newlib.fprintf`), returns 70 to `crt0`, whose `j exit` enters
`exit(70)` (`Exit.wp_exitCall`).

```
800045ec: bnez a0,80004600
80004600: ld a5,0(s0); addi a2,sp,496; auipc a1,0x15; addi a1,a1,-40; ld a0,24(a5)
80004614: jal fprintf
80004618: li a0,70; j 800045f0
800045f0: ld ra,760(sp); ld s0,752(sp); addi sp,sp,768; ret
80000038: j exit
```

`exit` runs at `main`'s stack top: its frame is `main`'s saved pair and its
newlib interior uses `err_msg` (`Newlib.exitHandlersNeed`).
-/

namespace VsaIris.Newlib.MainErr

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Sim VsaIris.Inst VsaIris.Interp VsaIris.Stdio VsaIris.Newlib.Sites VsaIris.Newlib.Exit

/-! ## Segments -/

#derive_case mainErrASeg chain
  [] terminator ⟨0x800045ec#64, 0x00051a63#32, 0x63#8, 0x1a#8, 0x05#8, 0x00#8,
      .br bop.BNE true, 10, 0, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x80004600#64, 0x00043783#32),
   (0x80004604#64, 0x1f010613#32),
   (0x80004608#64, 0x00015597#32),
   (0x8000460c#64, 0xfd858593#32),
   (0x80004610#64, 0x0187b503#32)]

#derive_case mainErrBSeg chain
  [(0x80004618#64, 0x04600513#32)] terminator ⟨0x8000461c#64, 0xfd5ff06f#32, 0x6f#8, 0xf0#8,
      0x5f#8, 0xfd#8, .j, 0, 0, 0#13, 0x1fffd4#21, 0#12⟩ ;;
  [(0x800045f0#64, 0x2f813083#32),
   (0x800045f4#64, 0x2f013403#32),
   (0x800045f8#64, 0x30010113#32)] terminator ⟨0x800045fc#64, 0x00008067#32, 0x67#8, 0x80#8,
      0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

abbrev aL (v a5v a2v a1v s0v sM : BitVec 64) : GRegs :=
  [(10, v), (15, a5v), (12, a2v), (11, a1v), (8, s0v), (2, sM)]

/-- The two stdio words `main` loads: `_impure_ptr`, then `_impure_data._stderr`. -/
abbrev aLds (simg : Nat → BitVec 8) : List (List (BitVec 8)) :=
  [imgWord simg consoleImpurePtrAddr, imgWord simg stderrPtrAddr]

/-- The read footprint of the two stdio words. -/
abbrev stdFoot (simg : Nat → BitVec 8) : List (Nat × DFrac × BitVec 8) :=
  imgFoot consoleImpurePtrAddr 8 simg ++ imgFoot stderrPtrAddr 8 simg

theorem a_facts {m : Std.ExtHashMap Nat (BitVec 8)} {v a5v a2v a1v sM : BitVec 64}
    {simg : Nat → BitVec 8} (hcode : mainErrCodeLoaded m) (hv : v ≠ 0#64)
    (hok : StdioOK simg)
    (hpin : ∀ k, (consoleImpurePtrAddr ≤ k ∧ k < consoleImpurePtrAddr + 8) ∨
      (stderrPtrAddr ≤ k ∧ k < stderrPtrAddr + 8) → (m[k]?).getD 0 = simg k) :
    ChainFacts m m (aL v a5v a2v a1v 0x8001b970#64 sM) (aLds simg) mainErrASeg := by
  unfold mainErrASeg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.mainErrCode_at_"
  · -- `bnez a0`: taken
    show (v != 0#64) = true
    simpa using hv
  · -- `ld a5,0(s0)`
    exact ldFact (img := simg) rfl rfl (by decide) (by decide) (by decide)
      (fun k hk => hpin _ (.inl ⟨by omega, by omega⟩))
  · -- `ld a0,24(a5)`, `a5` the loaded `_impure_ptr`
    have ha5 := hok.impure
    refine ldFact (img := simg) rfl ?_ (by decide) (by decide) (by decide)
      (fun k hk => hpin _ (.inr ⟨by omega, by omega⟩))
    have e : ∀ x : BitVec 64, x = bytesVal .ld (imgWord simg consoleImpurePtrAddr) +
        sign_extend (m := 64) (0x018#12) → x.toNat = stderrPtrAddr := by
      intro x hx; rw [hx, bytesVal_imgWord, ha5]; decide
    exact e _ rfl

theorem a_pc (v a5v a2v a1v s0v sM : BitVec 64) (simg : Nat → BitVec 8) :
    evalBlocksPC 0x800045ec#64 (SegEvalState.init (aL v a5v a2v a1v s0v sM) (aLds simg))
      mainErrASeg = 0x80004614#64 := rfl

theorem a_fin (v a5v a2v a1v s0v sM : BitVec 64) {simg : Nat → BitVec 8} (hok : StdioOK simg) :
    finReg mainErrASeg (aL v a5v a2v a1v s0v sM) (aLds simg) 10 = stderrFile ∧
    finReg mainErrASeg (aL v a5v a2v a1v s0v sM) (aLds simg) 15 = BitVec.ofNat 64 consoleReent ∧
    finReg mainErrASeg (aL v a5v a2v a1v s0v sM) (aLds simg) 12 =
      sM + sign_extend (m := 64) (0x1f0#12) ∧
    finReg mainErrASeg (aL v a5v a2v a1v s0v sM) (aLds simg) 11 = 0x800195e0#64 ∧
    finReg mainErrASeg (aL v a5v a2v a1v s0v sM) (aLds simg) 8 = s0v ∧
    finReg mainErrASeg (aL v a5v a2v a1v s0v sM) (aLds simg) 2 = sM := by
  refine ⟨?_, ?_, rfl, ?_, rfl, rfl⟩
  · show bytesVal .ld (imgWord simg stderrPtrAddr) = _
    rw [bytesVal_imgWord, hok.stderr]; rfl
  · show bytesVal .ld (imgWord simg consoleImpurePtrAddr) = _
    rw [bytesVal_imgWord, hok.impure]
  · show (0x80004608#64 + sign_extend (m := 64) ((0x00015#20) +++ (0x000#12))) +
      sign_extend (m := 64) (0xfd8#12) = _
    decide

abbrev bL (a0v rv s0v sM : BitVec 64) : GRegs := [(10, a0v), (1, rv), (8, s0v), (2, sM)]

/-- `main`'s saved pair: `ra` at `sp+760`, `s0` at `sp+752`. -/
abbrev bLds (sM : BitVec 64) (imgT : Nat → BitVec 8) : List (List (BitVec 8)) :=
  [imgWord imgT (sM.toNat + 760), imgWord imgT (sM.toNat + 752)]

/-- `main`'s stack pointer: its 768-byte frame in RAM above the HTIF words. -/
structure MainSp (sM : BitVec 64) : Prop where
  lo : Vsa.Sim.tohostAddr + 16 + fprintfNeed ≤ sM.toNat
  hi : sM.toNat + 768 ≤ 0x88000000
  align : sM.toNat % 16 = 0

theorem b_facts {m : Std.ExtHashMap Nat (BitVec 8)} {a0v rv s0v sM : BitVec 64}
    {imgT : Nat → BitVec 8} (hcode : mainErrCodeLoaded m) (hsM : MainSp sM)
    (hra : imgW imgT (sM.toNat + 760) = 0x80000038#64)
    (hpin : ∀ k, sM.toNat + 752 ≤ k → k < sM.toNat + 752 + 16 → (m[k]?).getD 0 = imgT k) :
    ChainFacts m m (bL a0v rv s0v sM) (bLds sM imgT) mainErrBSeg := by
  have h1 := hsM.lo; have h2 := hsM.hi; have h3 := hsM.align
  unfold fprintfNeed tohostAddr at h1
  unfold mainErrBSeg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.mainErrCode_at_"
  · -- `ld ra,760(sp)`
    have e : ∀ x : BitVec 64, x = sM + sign_extend (m := 64) (0x2f8#12) →
        x.toNat = sM.toNat + 760 := by
      intro x hx; rw [hx]; exact addr_off sM _ 760 (by decide) (by omega)
    exact ldFact (img := imgT) rfl (e _ rfl) (by omega) (by omega) (.inr (by unfold tohostAddr; omega))
      (fun k hk => hpin _ (by omega) (by omega))
  · -- `ld s0,752(sp)`
    have e : ∀ x : BitVec 64, x = sM + sign_extend (m := 64) (0x2f0#12) →
        x.toNat = sM.toNat + 752 := by
      intro x hx; rw [hx]; exact addr_off sM _ 752 (by decide) (by omega)
    exact ldFact (img := imgT) rfl (e _ rfl) (by omega) (by omega) (.inr (by unfold tohostAddr; omega))
      (fun k hk => hpin _ (by omega) (by omega))
  · -- `ret` to the loaded `ra`
    have e : ∀ x : BitVec 64, x = bytesVal .ld (imgWord imgT (sM.toNat + 760)) →
        (BitVec.update (x + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
      intro x hx; rw [hx, bytesVal_imgWord, hra]; decide
    exact e _ rfl

theorem b_pc (a0v rv s0v sM : BitVec 64) {imgT : Nat → BitVec 8}
    (hra : imgW imgT (sM.toNat + 760) = 0x80000038#64) :
    evalBlocksPC 0x80004618#64 (SegEvalState.init (bL a0v rv s0v sM) (bLds sM imgT))
      mainErrBSeg = 0x80000038#64 := by
  have e : ∀ x : BitVec 64, x = bytesVal .ld (imgWord imgT (sM.toNat + 760)) →
      BitVec.update (x + sign_extend (m := 64) (0x000#12)) 0 0#1 = 0x80000038#64 := by
    intro x hx; rw [hx, bytesVal_imgWord, hra]; decide
  exact e _ rfl

theorem b_fin (a0v rv s0v sM : BitVec 64) {imgT : Nat → BitVec 8}
    (hra : imgW imgT (sM.toNat + 760) = 0x80000038#64) :
    finReg mainErrBSeg (bL a0v rv s0v sM) (bLds sM imgT) 10 = 70#64 ∧
    finReg mainErrBSeg (bL a0v rv s0v sM) (bLds sM imgT) 1 = 0x80000038#64 ∧
    finReg mainErrBSeg (bL a0v rv s0v sM) (bLds sM imgT) 8 = imgW imgT (sM.toNat + 752) ∧
    finReg mainErrBSeg (bL a0v rv s0v sM) (bLds sM imgT) 2 =
      sM + sign_extend (m := 64) (0x300#12) := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · show 0#64 + sign_extend (m := 64) (0x046#12) = _; decide
  · show bytesVal .ld (imgWord imgT (sM.toNat + 760)) = _; rw [bytesVal_imgWord, hra]
  · show bytesVal .ld (imgWord imgT (sM.toNat + 752)) = _; rw [bytesVal_imgWord]

theorem crt0_facts {m : Std.ExtHashMap Nat (BitVec 8)} (hcode : crt0JCodeLoaded m) :
    ChainFacts m m [(10, (70#64 : BitVec 64))] [] crt0JSeg := by
  unfold crt0JSeg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.crt0JCode_at_"

theorem crt0_pc :
    evalBlocksPC 0x80000038#64 (SegEvalState.init [(10, (70#64 : BitVec 64))] []) crt0JSeg =
      0x80004764#64 := rfl

theorem crt0_fin : finReg crt0JSeg [(10, (70#64 : BitVec 64))] [] 10 = 70#64 := rfl

/-- `main`'s format `"%s\n"` (`0x800195e0`, `.rodata`). -/
def fmtLine : BitVec 64 := 0x800195e0#64

theorem fmtLine_ok {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) {errp : BitVec 64}
    (hs : ∃ t, CStrCov R rd errp.toNat t) : FmtArgsOK R rd fmtLine [errp] := by
  obtain ⟨t, ht⟩ := hs
  have hb : ∀ i, i < 4 → R (0x800195e0 + i) ∧ rd (0x800195e0 + i) = rodataByte (0x800195e0 + i) :=
    fun i hi => hro _ ⟨by omega, by omega⟩
  refine ⟨[0x25#8, 0x73#8, 0x0a#8], [.str], ⟨fun i hi => ?_, ?_⟩, by decide, by simp, ?_⟩
  · obtain ⟨hR, hrd⟩ := hb i (by simp at hi; omega)
    refine ⟨hR, ?_, ?_⟩
    · rw [show fmtLine.toNat = 0x800195e0 from rfl, hrd]
      have : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
      rcases this with rfl | rfl | rfl <;>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel
    · have : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
      rcases this with rfl | rfl | rfl <;>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide
  · obtain ⟨hR, hrd⟩ := hb 3 (by omega)
    exact ⟨hR, by rw [show fmtLine.toNat = 0x800195e0 from rfl]; simp only [List.length_cons,
      List.length_nil]; rw [hrd]; decide +kernel⟩
  · intro i hi _
    have : i = 0 := by simp at hi; omega
    subst this
    exact ⟨t, ht⟩

/-! ## The rule -/

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The two stdio windows `main` reads. -/
def StdWin (k : Nat) : Prop :=
  InExt (consoleImpurePtrAddr, 8) k ∨ InExt (stderrPtrAddr, 8) k

def stdWinList : List Nat := List.range' consoleImpurePtrAddr 8 ++ List.range' stderrPtrAddr 8

theorem stdWinList_nodup : stdWinList.Nodup := by decide

theorem stdWin_mem (k : Nat) : (stdioFoot k ∧ StdWin k) ↔ k ∈ stdWinList := by
  unfold stdWinList StdWin InExt stdioFoot InRange consoleImpurePtrAddr stderrPtrAddr consoleReent
  simp only [List.mem_append, List.mem_range']
  constructor
  · rintro ⟨_, h | h⟩
    · exact .inl ⟨k - 0x8001b970, by simp at h; omega, by simp at h; omega⟩
    · exact .inr ⟨k - (0x8001b538 + 24), by simp at h; omega, by simp at h; omega⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨by omega, .inl ⟨by simp, by simp; omega⟩⟩
    · exact ⟨by omega, .inr ⟨by simp, by simp; omega⟩⟩

theorem stdWin_iff (simg : Nat → BitVec 8) :
    ownSet (GF := GF) (fun k => stdioFoot k ∧ StdWin k) (fun k => k ↦ₘ simg k) ⊣⊢
      sepL (stdFoot simg) (fun p => p.1 ↦ₘ{p.2.1} p.2.2) := by
  have e : stdFoot simg = stdWinList.map (fun k => (k, DFrac.own 1, simg k)) := by
    unfold stdFoot imgFoot stdWinList; rw [List.map_append]
  rw [e, VsaIris.sepL_map]
  constructor
  · iintro H
    ihave H := ownSet_iff _ stdWin_mem $$ H
    iapply ownSet_to_sepL _ stdWinList_nodup $$ H
  · iintro H
    ihave H := sepL_to_ownSet _ stdWinList_nodup $$ H
    iapply ownSet_iff _ (fun k => (stdWin_mem k).symm) $$ H

theorem sepL_calleeSaved (f : Nat → BitVec 64) :
    sepL (GF := GF) calleeSaved (fun r => r ↦ᵣ f r) ⊣⊢
      (8 : Nat) ↦ᵣ f 8 ∗ sepL (calleeSaved.drop 1) (fun r => r ↦ᵣ f r) := by
  show sepL (8 :: calleeSaved.drop 1) _ ⊣⊢ _
  rw [sepL_cons]
  exact .rfl

/-- **`main`'s error line, then `exit(70)`**, for either WP. At `main`'s
`jal interp_run` link with a nonzero result, `s0 = &_impure_ptr`, `main`'s
stack (the saved pair `imgT` with `ra = crt0`'s link, and `fprintfNeed`
bytes below `sp`), `err_msg` holding a C string at `sp+496`, newlib's data in
its boundary state and the console at `o`: the run halts with code 70. -/
theorem wp_mainErrTail {Ierr : (Nat → BitVec 8) → Prop} (H : NewlibHolesAt Ierr)
    (live : Nat → Prop) (hlive : CodeLive live) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} (sM v rv : BitVec 64) (cs : Nat → BitVec 64) (o : String)
    (imgT errImg : Nat → BitVec 8) (hsM : MainSp sM) (hv : v ≠ 0#64)
    (hra : imgW imgT (sM.toNat + 760) = 0x80000038#64)
    (herr : ∃ k, k < 256 ∧ errImg (sM.toNat + 496 + k) = 0) :
    PC ↦ᵣ 0x800045ec#64 ∗ (10 : Nat) ↦ᵣ v ∗ ra ↦ᵣ rv ∗ (8 : Nat) ↦ᵣ 0x8001b970#64 ∗
      clobbered (argRegs.drop 1) ∗ callFrame sM fprintfNeed (calleeSaved.drop 1) cs ∗
      ownImg (InExt (sM.toNat + 752, 16)) imgT ∗ ownImg (InExt (sM.toNat + 496, 256)) errImg ∗
      stdioOwn ∗ consoleOwn o ∗ (∀ o', Φ (70, o ++ o'))
    ⊢ Wp.W Φ := by
  have h1 := hsM.lo; have h2 := hsM.hi; have h3 := hsM.align
  unfold fprintfNeed tohostAddr at h1
  have hcodeL := mainErrCode_text.live hlive
  unfold callFrame VsaIris.sp VsaIris.ra
  iintro ⟨Hpc, Ha0, Hra, Hs0, Hargs, ⟨Hsp, Hscr, Hsaved, Htmp, #Hgp, #Himg⟩, HT, Herr, Hstd,
    Hcon, HΦ⟩
  ihave #Hcode := instrAt_of_binImg mainErrCode_text $$ Himg
  -- `_impure_ptr` and `_impure_data._stderr`
  ihave ⟨%simg, %hok, Hw, Hrest⟩ := stdioAt_open StdioOK StdWin $$ Hstd
  ihave Hw := (stdWin_iff simg).1 $$ Hw
  ihave ⟨⟨%a5v, Ha5⟩, Hargs⟩ := clobbered_take (r := 15) (by decide) $$ Hargs
  ihave ⟨⟨%a2v, Ha2⟩, Hargs⟩ := clobbered_take (r := 12) (by decide) $$ Hargs
  ihave ⟨⟨%a1v, Ha1⟩, Hargs⟩ := clobbered_take (r := 11) (by decide) $$ Hargs
  iapply wp_segW live Wp mainErrASeg (aL v a5v a2v a1v 0x8001b970#64 sM) (aLds simg)
    0x800045ec#64 (codeFoot mainErrCodeBase mainErrCode ++ stdFoot simg) [] 5 (by decide)
    (by change ChainOK _ [10, 15, 12, 11, 8, 2] _; decide)
    (by change KeysOK [10, 15, 12, 11, 8, 2]; decide)
    (by change ∀ k ∈ wrChain mainErrASeg, k ∈ [10, 15, 12, 11, 8, 2]; decide)
    (fun a _ => trivial)
    (fun c hok' ⟨_, hMR, _, _⟩ => a_facts
      (mainErrCodeLoaded_of (code_present hok' _ (fun q hq => hMR q (List.mem_append_left _ hq))
        hcodeL)) hv hok
      (fun k hk => by
        rcases hk with hk | hk
        · exact imgFoot_pin (a := consoleImpurePtrAddr) (n := 8) hMR
            (fun q hq => List.mem_append_right _ (List.mem_append_left _ hq)) k hk.1 hk.2
        · exact imgFoot_pin (a := stderrPtrAddr) (n := 8) hMR
            (fun q hq => List.mem_append_right _ (List.mem_append_right _ hq)) k hk.1 hk.2))
  have hpc := a_pc v a5v a2v a1v 0x8001b970#64 sM simg
  obtain ⟨f10, f15, f12, f11, f8, f2⟩ := a_fin v a5v a2v a1v 0x8001b970#64 sM hok
  simp only [aL] at hpc f10 f15 f12 f11 f8 f2
  simp only [aL, sepL_cons, sepL_nil, hpc, f10, f15, f12, f11, f8, f2]
  iframe Hpc Ha0 Ha5 Ha2 Ha1 Hs0 Hsp
  isplitr
  · iempintro
  isplitl [Hw]
  · iapply (sepL_append _ _ _).2
    isplitr
    · rw [← instrAt_eq]; iexact Hcode
    iexact Hw
  iintro Hpc ⟨Ha0, Ha5, Ha2, Ha1, Hs0, Hsp, -⟩ - HMR
  ihave ⟨-, Hw⟩ := (sepL_append _ _ _).1 $$ HMR
  ihave Hw := (stdWin_iff simg).2 $$ Hw
  ihave Hstd := stdioAt_close StdioOK StdWin simg hok $$ [Hw Hrest]
  · iframe Hw Hrest
  -- `fprintf(stderr, "%s\n", in->err_msg)`
  let errp : BitVec 64 := sM + sign_extend (m := 64) (0x1f0#12)
  have herrp : errp.toNat = sM.toNat + 496 := addr_off sM _ 496 (by decide) (by omega)
  let Sown : Nat → Prop := InExt (sM.toNat + 496, 256)
  let rd : Nat → BitVec 8 := fun a => if rodataDom a then rodataByte a else errImg a
  have hoff : ∀ a, Sown a → ¬ rodataDom a := fun a ha hr => by
    simp only [Sown, InExt] at ha; unfold rodataDom at hr; omega
  have hfmt : FmtArgsOK (fun a => rodataDom a ∨ Sown a) rd fmtLine [errp] :=
    fmtLine_ok (fun a ha => ⟨.inl ha, by simp [rd, ha]⟩)
      (cstrCov_of_nul (n := 256) (fun i hi => .inr (by rw [herrp]; simp only [Sown, InExt]; omega))
        (by
          obtain ⟨k, hk, h0⟩ := herr
          refine ⟨k, hk, ?_⟩
          rw [herrp]
          have : ¬ rodataDom (sM.toNat + 496 + k) := hoff _ (by simp only [Sown, InExt]; omega)
          simp [rd, this, h0]))
  let cs' : Nat → BitVec 64 := fun r => if r = 8 then 0x8001b970#64 else cs r
  have hf := H.fprintf live Wp sM fmtLine [errp] cs' rodataDom Sown rd o hlive (by simp) hfmt
    ⟨by unfold fprintfNeed tohostAddr; omega, by omega, h3⟩
  have hjt : TextAt mainJalFprintf.pc mainJalFprintf.code := by decide
  have hj : JalExec (vsaModel live) mainJalFprintf.pc mainJalFprintf.code fprintfEntry :=
    JalSite.exec mainJalFprintf_cert live (hjt.live hlive)
  ihave #Hjal := instrAt_of_binImg hjt $$ Himg
  unfold fprintfSpec at hf
  ihave #Hf := hf
  iapply wp_callW Wp (v := rv) hj
  iframe Hjal Hf
  rw [show BitVec.ofNat 64 mainJalFprintf.pc = 0x80004614#64 from rfl,
    show BitVec.ofNat 64 (mainJalFprintf.pc + 4) = 0x80004618#64 from rfl]
  unfold VsaIris.ra
  iframe Hpc Hra
  isplitl [Ha0 Ha1 Ha2 Ha5 Hargs Herr Hstd Hcon Hsp Hscr Hs0 Hsaved Htmp]
  · unfold argsAt readable callFrame VsaIris.sp fmtLine
    simp only [List.cons_append, List.nil_append, List.zipIdx_cons, List.zipIdx_nil, sepL_cons,
      sepL_nil, List.length_cons, List.length_nil, Nat.add_zero, Nat.reduceAdd]
    iframe Ha0 Ha1 Ha2 Hstd Hcon Hsp Hscr Htmp Hgp
    isplitl [Ha5 Hargs]
    · rw [show List.drop 3 argRegs = [13, 14, 15, 16, 17] from rfl]
      iapply clobbered_put (r := 15) (rs := [13, 14, 15, 16, 17]) (by decide)
      rw [show ([13, 14, 15, 16, 17] : List Nat).erase 15 =
        (((List.drop 1 argRegs).erase 15).erase 12).erase 11 from rfl]
      iframe Hargs
      iexists _
      iexact Ha5
    isplitl [Herr]
    · isplitr
      · iapply roImg_congr (S := rodataDom) (f := rodataByte) (g := rd)
          (fun a ha => by simp [rd, ha])
        iapply binImg_rodata $$ Himg
      · iapply ownSet_congr (fun a ha => by simp [rd, hoff a ha]) $$ Herr
    isplitl [Hs0 Hsaved]
    · iapply (sepL_calleeSaved cs').2
      isplitl [Hs0]
      · rw [show cs' 8 = 0x8001b970#64 from rfl]
        iexact Hs0
      · rw [sepL_congr (l := List.drop 1 calleeSaved) (Φ := fun r => r ↦ᵣ cs' r)
          (Ψ := fun r => r ↦ᵣ cs r) (fun r hr => by
            have : r ≠ 8 := by intro e; subst e; revert hr; decide
            simp [cs', this])]
        iexact Hsaved
    iexact Himg
  -- `li a0,70; j; ld ra,760(sp); ld s0,752(sp); addi sp,sp,768; ret`
  unfold callFrame readable VsaIris.sp
  iintro Hpc Hra ⟨Hargs, ⟨Hro, Herr⟩, Hstd, ⟨%o', Hcon⟩, ⟨Hsp, Hscr, Hsaved, Htmp, -, -⟩⟩
  ihave ⟨Hs0, Hsaved⟩ := (sepL_calleeSaved cs').1 $$ Hsaved
  ihave ⟨⟨%a0v, Ha0⟩, Hargs⟩ := clobbered_take (r := 10) (by decide) $$ Hargs
  ihave HT := (ownImg_range _ _ _).1 $$ HT
  iapply wp_segW live Wp mainErrBSeg (bL a0v 0x80004618#64 (cs' 8) sM) (bLds sM imgT)
    0x80004618#64 (codeFoot mainErrCodeBase mainErrCode ++ imgFoot (sM.toNat + 752) 16 imgT) [] 5
    (by decide)
    (by change ChainOK _ [10, 1, 8, 2] _; decide) (by change KeysOK [10, 1, 8, 2]; decide)
    (by change ∀ k ∈ wrChain mainErrBSeg, k ∈ [10, 1, 8, 2]; decide)
    (fun a _ => trivial)
    (fun c hok' ⟨_, hMR, _, _⟩ => b_facts
      (mainErrCodeLoaded_of (code_present hok' _ (fun q hq => hMR q (List.mem_append_left _ hq))
        hcodeL)) hsM hra
      (imgFoot_pin hMR (fun q hq => List.mem_append_right _ hq)))
  have hpcB := b_pc a0v 0x80004618#64 (cs' 8) sM hra
  obtain ⟨g10, g1, g8, g2⟩ := b_fin a0v 0x80004618#64 (cs' 8) sM hra
  simp only [bL] at hpcB g10 g1 g8 g2
  simp only [bL, sepL_cons, sepL_nil, hpcB, g10, g1, g8, g2]
  iframe Hpc Ha0 Hra Hs0 Hsp
  isplitr
  · iempintro
  isplitl [HT]
  · iapply (sepL_append _ _ _).2
    isplitr
    · rw [← instrAt_eq]; iexact Hcode
    iexact HT
  iintro Hpc ⟨Ha0, Hra, Hs0, Hsp, -⟩ - HMR
  ihave ⟨-, HT⟩ := (sepL_append _ _ _).1 $$ HMR
  ihave HT := (ownImg_range _ _ _).2 $$ HT
  -- `crt0`'s `j exit`
  have hcrtL := crt0JCode_text.live hlive
  ihave #Hcrt := instrAt_of_binImg crt0JCode_text $$ Himg
  iapply wp_segW live Wp crt0JSeg [(10, (70#64 : BitVec 64))] [] 0x80000038#64
    (codeFoot crt0JCodeBase crt0JCode) [] 0 (by decide)
    (by change ChainOK _ [10] _; decide) (by change KeysOK [10]; decide)
    (by change ∀ k ∈ wrChain crt0JSeg, k ∈ [10]; decide)
    (fun a _ => trivial)
    (fun c hok' ⟨_, hMR, _, _⟩ => crt0_facts (crt0JCodeLoaded_of (code_present hok' _ hMR hcrtL)))
  simp only [sepL_cons, sepL_nil, crt0_pc, crt0_fin]
  rw [← instrAt_eq]
  iframe Hpc Ha0 Hcrt
  iintro Hpc ⟨Ha0, -⟩ - -
  -- `exit(70)` at `main`'s stack top
  have hs768 : (sM + sign_extend (m := 64) (0x300#12)).toNat = sM.toNat + 768 :=
    addr_off sM _ 768 (by decide) (by omega)
  iapply wp_exitCall H live hlive Wp (sM + sign_extend (m := 64) (0x300#12)) 0x80000038#64 70#64
    (imgW imgT (sM.toNat + 752)) cs (o ++ o') (by decide)
    ⟨by rw [hs768]; unfold exitNeed exitHandlersNeed tohostAddr; omega, by rw [hs768]; omega,
      by rw [hs768]; omega⟩
  unfold argsAt callFrame VsaIris.sp VsaIris.ra exitEntry
  simp only [List.zipIdx_cons, List.zipIdx_nil, sepL_cons, sepL_nil, Nat.add_zero,
    List.length_singleton]
  iframe Hpc Hra Hs0 Ha0 Hsp Htmp Hgp Himg Hcon
  isplitl [Hargs]
  · rw [show List.drop 1 argRegs = argRegs.erase 10 from rfl]; iexact Hargs
  isplitl [Herr HT Hsaved]
  · isplitl [Herr HT]
    · ihave He := blockOwn_of_ownImg (sM.toNat + 496) 256 rd $$ Herr
      ihave Ht := blockOwn_of_ownImg (sM.toNat + 752) 16 imgT $$ HT
      ihave Hb := blockOwn_join (sM.toNat + 496) 256 (sM.toNat + 752) 16 272 (by omega) (by omega)
        $$ [He Ht]
      · iframe He Ht
      unfold stackScratch
      rw [hs768]
      unfold exitNeed exitHandlersNeed
      iapply (blockOwn_cast (p := sM.toNat + 496) (n := 272)
        (p' := sM.toNat + 768 - (16 + 256)) (n' := 16 + 256) (by omega) rfl) $$ Hb
    · rw [← sepL_congr (l := List.drop 1 calleeSaved) (Φ := fun r => r ↦ᵣ cs' r)
        (Ψ := fun r => r ↦ᵣ cs r) (fun r hr => by
          have : r ≠ 8 := by intro e; subst e; revert hr; decide
          simp [cs', this])]
      iexact Hsaved
  isplitl [Hstd]
  · iapply stdioAt_mono (fun img h => .inr h) $$ Hstd
  iintro %o''
  rw [show (70#64 : BitVec 64).toNat = 70 from rfl, String.append_assoc]
  iapply HΦ

end Wp

end VsaIris.Newlib.MainErr
