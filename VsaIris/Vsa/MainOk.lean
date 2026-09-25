import VsaIris.Vsa.MainErr

/-!
# `main`'s normal line and `exit(0)` (lane A)

`interp_run` returned `0` to `main` (`0x800045ec`, `a0 = 0`). `main` restores
its saved pair and returns `0` to `crt0`, whose `j exit` enters `exit(0)`
(`Exit.wp_exitCall` with `quiet = true`: newlib's data is still at its
boundary state, so the output is exactly the console's).

```
800045ec: bnez a0,80004600          (not taken)
800045f0: ld ra,760(sp); ld s0,752(sp); addi sp,sp,768; ret
80000038: j exit
```

`exit` runs at `main`'s stack top: its frame is `main`'s saved pair and its
newlib interior uses `err_msg`, as on the error line (`MainErr`).
-/

namespace VsaIris.Newlib.MainOk

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Sim VsaIris.Inst VsaIris.Interp VsaIris.Stdio VsaIris.Newlib.Sites VsaIris.Newlib.Exit
  VsaIris.Newlib.MainErr

/-! ## Segments -/

#derive_case mainOkSeg chain
  [] terminator ⟨0x800045ec#64, 0x00051a63#32, 0x63#8, 0x1a#8, 0x05#8, 0x00#8,
      .br bop.BNE false, 10, 0, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x800045f0#64, 0x2f813083#32),
   (0x800045f4#64, 0x2f013403#32),
   (0x800045f8#64, 0x30010113#32)] terminator ⟨0x800045fc#64, 0x00008067#32, 0x67#8, 0x80#8,
      0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

theorem ok_facts {m : Std.ExtHashMap Nat (BitVec 8)} {rv s0v sM : BitVec 64}
    {imgT : Nat → BitVec 8} (hcode : mainErrCodeLoaded m) (hsM : MainSp sM)
    (hra : imgW imgT (sM.toNat + 760) = 0x80000038#64)
    (hpin : ∀ k, sM.toNat + 752 ≤ k → k < sM.toNat + 752 + 16 → (m[k]?).getD 0 = imgT k) :
    ChainFacts m m (bL 0#64 rv s0v sM) (bLds sM imgT) mainOkSeg := by
  have h1 := hsM.lo; have h2 := hsM.hi; have h3 := hsM.align
  unfold fprintfNeed at h1
  unfold mainOkSeg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.mainErrCode_at_"
  · -- `bnez a0`: not taken
    rfl
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

theorem ok_pc (rv s0v sM : BitVec 64) {imgT : Nat → BitVec 8}
    (hra : imgW imgT (sM.toNat + 760) = 0x80000038#64) :
    evalBlocksPC 0x800045ec#64 (SegEvalState.init (bL 0#64 rv s0v sM) (bLds sM imgT))
      mainOkSeg = 0x80000038#64 := by
  have e : ∀ x : BitVec 64, x = bytesVal .ld (imgWord imgT (sM.toNat + 760)) →
      BitVec.update (x + sign_extend (m := 64) (0x000#12)) 0 0#1 = 0x80000038#64 := by
    intro x hx; rw [hx, bytesVal_imgWord, hra]; decide
  exact e _ rfl

theorem ok_fin (rv s0v sM : BitVec 64) {imgT : Nat → BitVec 8}
    (hra : imgW imgT (sM.toNat + 760) = 0x80000038#64) :
    finReg mainOkSeg (bL 0#64 rv s0v sM) (bLds sM imgT) 10 = 0#64 ∧
    finReg mainOkSeg (bL 0#64 rv s0v sM) (bLds sM imgT) 1 = 0x80000038#64 ∧
    finReg mainOkSeg (bL 0#64 rv s0v sM) (bLds sM imgT) 8 = imgW imgT (sM.toNat + 752) ∧
    finReg mainOkSeg (bL 0#64 rv s0v sM) (bLds sM imgT) 2 =
      sM + sign_extend (m := 64) (0x300#12) := by
  refine ⟨rfl, ?_, ?_, rfl⟩
  · show bytesVal .ld (imgWord imgT (sM.toNat + 760)) = _; rw [bytesVal_imgWord, hra]
  · show bytesVal .ld (imgWord imgT (sM.toNat + 752)) = _; rw [bytesVal_imgWord]

theorem crt0_facts0 {m : Std.ExtHashMap Nat (BitVec 8)} (hcode : crt0JCodeLoaded m) :
    ChainFacts m m [(10, (0#64 : BitVec 64))] [] crt0JSeg := by
  unfold crt0JSeg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.crt0JCode_at_"

theorem crt0_pc0 :
    evalBlocksPC 0x80000038#64 (SegEvalState.init [(10, (0#64 : BitVec 64))] []) crt0JSeg =
      0x80004764#64 := rfl

theorem crt0_fin0 : finReg crt0JSeg [(10, (0#64 : BitVec 64))] [] 10 = 0#64 := rfl

/-! ## The rule -/

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **`main`'s normal line, then `exit(0)`**, for either WP. At `main`'s
`jal interp_run` link with `a0 = 0`, `main`'s saved pair `imgT` (`ra` =
`crt0`'s link), `err_msg`'s 256 bytes at `sp+496` (the stack `exit` uses),
newlib's data at its boundary state and the console at `o`: the run halts
with code 0 and output exactly `o`. -/
theorem wp_mainOkTail (H : NewlibHoles) (live : Nat → Prop) (hlive : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (sM rv s0v : BitVec 64) (cs : Nat → BitVec 64) (o : String) (imgT : Nat → BitVec 8)
    (hsM : MainSp sM) (hra : imgW imgT (sM.toNat + 760) = 0x80000038#64) :
    PC ↦ᵣ 0x800045ec#64 ∗ (10 : Nat) ↦ᵣ 0#64 ∗ ra ↦ᵣ rv ∗ (8 : Nat) ↦ᵣ s0v ∗
      clobbered (argRegs.drop 1) ∗ sp ↦ᵣ sM ∗ sepL (calleeSaved.drop 1) (fun r => r ↦ᵣ cs r) ∗
      clobbered tmpRegs ∗ gp ↦ᵣ□ gpV ∗ binImg ∗
      ownImg (InExt (sM.toNat + 752, 16)) imgT ∗ blockOwn (sM.toNat + 496) 256 ∗
      stdioOwn ∗ errnoOwn ∗ consoleOwn o ∗ Φ (0, o)
    ⊢ Wp.W Φ := by
  have h1 := hsM.lo; have h2 := hsM.hi; have h3 := hsM.align
  unfold fprintfNeed at h1
  have hcodeL := mainErrCode_text.live hlive
  unfold VsaIris.sp VsaIris.ra
  iintro ⟨Hpc, Ha0, Hra, Hs0, Hargs, Hsp, Hsaved, Htmp, #Hgp, #Himg, HT, Herr, Hstd, Hno, Hcon, HΦ⟩
  ihave #Hcode := instrAt_of_binImg mainErrCode_text $$ Himg
  ihave HT := (ownImg_range _ _ _).1 $$ HT
  -- `bnez a0` (not taken); `ld ra,760(sp); ld s0,752(sp); addi sp,sp,768; ret`
  iapply wp_segW live Wp mainOkSeg (bL 0#64 rv s0v sM) (bLds sM imgT)
    0x800045ec#64 (codeFoot mainErrCodeBase mainErrCode ++ imgFoot (sM.toNat + 752) 16 imgT) [] 4
    (by decide)
    (by change ChainOK _ [10, 1, 8, 2] _; decide) (by change KeysOK [10, 1, 8, 2]; decide)
    (by change ∀ k ∈ wrChain mainOkSeg, k ∈ [10, 1, 8, 2]; decide)
    (fun a _ => trivial)
    (fun c hok' ⟨_, hMR, _, _⟩ => ok_facts
      (mainErrCodeLoaded_of (code_present hok' _ (fun q hq => hMR q (List.mem_append_left _ hq))
        hcodeL)) hsM hra
      (imgFoot_pin hMR (fun q hq => List.mem_append_right _ hq)))
  have hpcB := ok_pc rv s0v sM hra
  obtain ⟨g10, g1, g8, g2⟩ := ok_fin rv s0v sM hra
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
  iapply wp_segW live Wp crt0JSeg [(10, (0#64 : BitVec 64))] [] 0x80000038#64
    (codeFoot crt0JCodeBase crt0JCode) [] 0 (by decide)
    (by change ChainOK _ [10] _; decide) (by change KeysOK [10]; decide)
    (by change ∀ k ∈ wrChain crt0JSeg, k ∈ [10]; decide)
    (fun a _ => trivial)
    (fun c hok' ⟨_, hMR, _, _⟩ => crt0_facts0 (crt0JCodeLoaded_of (code_present hok' _ hMR hcrtL)))
  simp only [sepL_cons, sepL_nil, crt0_pc0, crt0_fin0]
  rw [← instrAt_eq]
  iframe Hpc Ha0 Hcrt
  iintro Hpc ⟨Ha0, -⟩ - -
  -- `exit(0)` at `main`'s stack top, quietly
  have hs768 : (sM + sign_extend (m := 64) (0x300#12)).toNat = sM.toNat + 768 :=
    addr_off sM _ 768 (by decide) (by omega)
  iapply wp_exitCall H.at live hlive Wp (sM + sign_extend (m := 64) (0x300#12)) 0x80000038#64 0#64
    (imgW imgT (sM.toNat + 752)) cs o true (by decide)
    ⟨by rw [hs768]; unfold exitNeed exitHandlersNeed tohostAddr; omega, by rw [hs768]; omega,
      by rw [hs768]; omega⟩
  unfold argsAt callFrame VsaIris.sp VsaIris.ra exitEntry
  simp only [List.zipIdx_cons, List.zipIdx_nil, sepL_cons, sepL_nil, Nat.add_zero,
    List.length_singleton]
  iframe Hpc Hra Hs0 Ha0 Hsp Htmp Hgp Himg Hcon Hsaved
  isplitl [Hargs]
  · rw [show List.drop 1 argRegs = argRegs.erase 10 from rfl]; iexact Hargs
  isplitl [Herr HT]
  · ihave Ht := blockOwn_of_ownImg (sM.toNat + 752) 16 imgT $$ HT
    ihave Hb := blockOwn_join (sM.toNat + 496) 256 (sM.toNat + 752) 16 272 (by omega) (by omega)
      $$ [Herr Ht]
    · iframe Herr Ht
    unfold stackScratch
    rw [hs768]
    unfold exitNeed exitHandlersNeed
    iapply (blockOwn_cast (p := sM.toNat + 496) (n := 272)
      (p' := sM.toNat + 768 - (16 + 256)) (n' := 16 + 256) (by omega) rfl) $$ Hb
  isplitl [Hstd]
  · iapply stdioAt_mono (fun img h => .inl h) $$ Hstd
  isplitl [Hno]
  · iexact Hno
  iintro %o' %ho'
  rw [ho' trivial, String.append_empty, show (0#64 : BitVec 64).toNat = 0 from rfl]
  iexact HΦ

end Wp

end VsaIris.Newlib.MainOk
