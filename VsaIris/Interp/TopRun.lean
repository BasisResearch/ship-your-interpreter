import VsaIris.Interp.SeqLoopInterp
import VsaIris.Interp.Abort
import VsaIris.Vsa.Setjmp
import VsaIris.Interp.World
import VsaIris.Interp.Need
import VsaIris.Interp.NewlibCall
import VsaIris.Interp.LeafCalls
import VsaIris.Vsa.MainOk
import VsaIris.Interp.ExecDisp

/-!
# `interp_run`'s whole run, total mode (lane A, INTERP_DESIGN.md §4.4, §5.2)

From `interp_run`'s entry (`0x800043ec`, the boundary state of
`InterpRunPhysicalFacts`) to the machine's halt:

* **the prologue** (`wp_topPrologue`, either WP): the 176-byte frame's spills
  (`wp_topSpill`), `jal setjmp` (`ms_callSetjmp`, over H5's `setjmp_spec`;
  `wp_topSetjmp` turns `worldPre`'s exclusive `jmp_buf` into `world`'s
  read-only one), and the count test (`wp_topHead`): an empty program goes to
  the epilogue with `s5 = 0`, a nonempty one reaches the statement loop's head
  `0x8000448c` with exactly its preconditions (`TopLoopFacts`, `topLoopRes`);
* **the normal return** (`wp_topNormal`, either WP): the epilogue at
  `0x80004514` with `s5 = 0`, `ret` to `main`, `main`'s normal line and
  `exit(0)` (`MainOk.wp_mainOkTail`, quietly: the output is the console's);
* **the theorem** `interpRun_total`: with the loop motive `interpSeqT_body` at
  the program's derivation, the run halts with `(0, st'.out)`;
  `interpRun_total_boot` states it from `bootRes`.

The entry is one named-field structure of pure facts (`TopEntry`, from `Boot`
by `topEntry_of_boot`) and one resource (`topPre`, from `bootRes` by
`topPre_of_bootRes`). The partial run is `TopRunP.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

#ix_seg TopProl_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s) :
    IW live m [] (InExt (s.toNat - 176, 176)) Q 0x800043ec#64 R Mt
  by ix_run hlive using [h2, hsf] at 0x80004424


#ix_seg TopHead_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s arr cnt : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709551440#64) (h10 : R 10 = 0#64)
    (hcnt : ldv .ld Mt (s + 18446744073709551440#64 + 16#64).toNat = cnt)
    (harr : ldv .ld Mt (s + 18446744073709551440#64 + 24#64).toNat = arr) :
    IW live m [] (InExt (s.toNat - 176, 176)) Q 0x80004428#64 R Mt
  by ix_run hlive using [h2, h10, hcnt, harr, hsf] at 0x8000448c 0x80004514


#ix_seg TopEpi_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hRA : ldv .ld Mt (s + 18446744073709551440#64 + 168#64).toNat = 0x800045ec#64) :
    IW live m [] (interpS s) Q 0x80004514#64 R Mt
  by ix_run hlive using [h2, hRA, hsf, interpS]



section Setjmp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst VsaIris.Newlib
  VsaIris.Newlib.Setjmp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {live : Nat → Prop}

theorem sepL_args_split (f : Nat → BitVec 64) :
    sepL (GF := GF) argRegs (fun r => r ↦ᵣ f r) ⊣⊢
      iprop((10 : Nat) ↦ᵣ f 10 ∗ sepL [11, 12, 13, 14, 15, 16, 17] (fun r => r ↦ᵣ f r)) := by
  rw [show argRegs = 10 :: [11, 12, 13, 14, 15, 16, 17] from rfl, sepL_cons]
  exact .rfl

/-- **`interp_run`'s `jal setjmp` from a run** (`0x80004424`): `setjmp` fills
the first 112 bytes of the `jmp_buf` at `a0 = jbp` with the link, `s0`–`s11`
and `sp` (`SetjmpImg`), and returns `0`; the run continues at `0x80004428`
with every other register kept. -/
theorem ms_callSetjmp (hlive : ∀ p ∈ interpText, live p.1) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {jbp : BitVec 64} (hjb : JbAt jbp)
    (h10 : R 10 = jbp) (img0 : Nat → BitVec 8) :
    codeRes ∗ binImg ∗ ms 0x80004424#64 R S Mt ∗ ownImg (InExt (jbp.toNat, 112)) img0 ∗
      (∀ img : Nat → BitVec 8, ⌜SetjmpImg jbp 0x80004428#64 (R 2) R img⌝ -∗
        ownImg (InExt (jbp.toNat, 112)) img -∗
        ms 0x80004428#64 (upd (upd R 10 0#64) 1 0x80004428#64) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  unfold ms
  iintro ⟨#Hcode, #Himg, ⟨Hpc, Hra, Hregs, HS⟩, HJ, Hk⟩
  ihave #Hi := instrAt_of_codeRes interp_code_80004424 $$ Hcode
  ihave ⟨Hsp, Hcs, Htmp, Hargs⟩ := (regFile_newlib R).1 $$ Hregs
  ihave ⟨Ha0, Hargs⟩ := (sepL_args_split R).1 $$ Hargs
  ihave #Hspec := setjmp_spec live hcl Wp jbp (R 2) R img0 hjb
  iapply wp_callW Wp (jalx_80004424 live (fun p hp => hlive _ (interp_code_80004424 p hp)))
  iframe Hi Hspec Hpc Hra
  isplitl [Ha0 Hsp Hcs HJ]
  · rw [h10]
    iframe Ha0 Hsp Hcs HJ Himg
    ipureintro; decide
  iintro Hpc Hra ⟨Ha0, Hsp, Hcs, ⟨%img, HJ, %himg⟩⟩
  iapply Hk $$ %img %himg HJ
  rw [regFile_upd_ra]
  simp only [upd_same]
  iframe Hpc Hra HS
  iapply (regFile_newlib _).2
  rw [upd_other _ _ (by decide : (2 : Nat) ≠ 10),
    sepL_congr (l := Newlib.calleeSaved) (Φ := fun r => r ↦ᵣ upd R 10 0#64 r) (Ψ := fun r => r ↦ᵣ R r) (fun r hr => by
      rw [upd_other _ _ (fun e => by subst e; revert hr; decide)]),
    sepL_congr (l := tmpRegs) (Φ := fun r => r ↦ᵣ upd R 10 0#64 r) (Ψ := fun r => r ↦ᵣ R r) (fun r hr => by
      rw [upd_other _ _ (fun e => by subst e; revert hr; decide)])]
  iframe Hsp Hcs Htmp
  iapply (sepL_args_split _).2
  rw [upd_same, sepL_congr (l := [11, 12, 13, 14, 15, 16, 17]) (Φ := fun r => r ↦ᵣ upd R 10 0#64 r)
    (Ψ := fun r => r ↦ᵣ R r) (fun r hr => by
      rw [upd_other _ _ (fun e => by subst e; revert hr; decide)])]
  iframe Ha0 Hargs

end Setjmp

section Normal

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst VsaIris.Newlib
  Vsa.RuntimeRepr VsaIris.Newlib.MainErr VsaIris.Newlib.MainOk

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- `interp_run`'s entry `sp` (`main`'s frame, `spEntry`). -/
abbrev sTop : BitVec 64 := 0x87fffd00#64

/-- `interp_run`'s lowered `sp` (its 176-byte frame). -/
abbrev sFr : BitVec 64 := sTop + 18446744073709551440#64

/-- `struct Interp` in `main`'s frame (`interpObject`). -/
abbrev inpTop : Nat := 0x87fffe10

theorem mainSp_top : MainSp sTop := ⟨by decide, by decide, by decide⟩

theorem sFr_toNat : sFr.toNat = sTop.toNat - 176 := by decide

omit I in
theorem calleeSaved_split (f : Nat → BitVec 64) :
    sepL (GF := GF) Newlib.calleeSaved (fun r => r ↦ᵣ f r) ⊣⊢
      iprop((8 : Nat) ↦ᵣ f 8 ∗ sepL (Newlib.calleeSaved.drop 1) (fun r => r ↦ᵣ f r)) := by
  rw [show Newlib.calleeSaved = 8 :: Newlib.calleeSaved.drop 1 from rfl, sepL_cons]
  exact .rfl

/-- The world's `err_msg` and newlib/console pieces, for the last exit. -/
theorem world_exitParts (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (ρ : Regime) (st : St)
    (d : Nat) :
    world (GF := GF) N L Room inpTop ρ st d ⊢
      blockOwn (sTop.toNat + 496) 256 ∗ Stdio.stdioOwn ∗ consoleOwn st.out ∗ binImg := by
  unfold world worldE interpCtxE interpCoreE errAny
  iintro ⟨%H, %B, -, -, Hcon, Hstd, ⟨⟨%g, -, -, -, -, -, Herr⟩, -⟩, -, #Himg⟩
  iframe Hcon Hstd Himg
  iapply blockOwn_cast (by unfold interpErrOff; decide) (by unfold interpErrLen; rfl) $$ Herr

/-- `world_exitParts` with `errno` lent by the dropped heap. -/
theorem world_exitPartsE (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (hEL : ErrnoOwn.ErrnoLend (GF := GF) L Room) (ρ : Regime) (st : St) (d : Nat) :
    world (GF := GF) N L Room inpTop ρ st d ⊢
      blockOwn (sTop.toNat + 496) 256 ∗ Stdio.stdioOwn ∗ Stdio.errnoOwn ∗ consoleOwn st.out ∗
        binImg := by
  unfold world worldE interpCtxE interpCoreE errAny
  iintro ⟨%H, %B, Hh, -, Hcon, Hstd, ⟨⟨%g, -, -, -, -, -, Herr⟩, -⟩, -, #Himg⟩
  ihave ⟨Herrno, -⟩ := hEL _ _ $$ Hh
  iframe Hcon Hstd Herrno Himg
  iapply blockOwn_cast (by unfold interpErrOff; decide) (by unfold interpErrLen; rfl) $$ Herr

/-- **`interp_run` returns `0`, `main` returns `0`, `exit(0)`**, for either
WP: at `interp_run`'s epilogue (`0x80004514`) with `s5 = 0`, its frame's
spilled link `0x800045ec`, the world at `st`, and `main`'s saved pair: the run
halts with code 0 and output `st.out`. -/
theorem wp_topNormal (H : NewlibHoles) (hlive : ∀ p ∈ interpText, live p.1) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {ρ : Regime} {st : St} {d : Nat}
    (hEL : ErrnoOwn.ErrnoLend (GF := GF) L Room)
    {R : Nat → BitVec 64} {Mt : Mem} {imgT : Nat → BitVec 8}
    (h2 : R 2 = sFr) (h21 : R 21 = 0#64)
    (hra : ldv .ld Mt (sFr + 168#64).toNat = 0x800045ec#64)
    (hT : imgW imgT (sTop.toNat + 760) = 0x80000038#64) :
    codeRes ∗ ms 0x80004514#64 R (interpS sTop) Mt ∗ world N L Room inpTop ρ st d ∗
      ownImg (InExt (sTop.toNat + 752, 16)) imgT ∗ Φ (0, st.out)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hcode, Hms, Hw, HT, HΦ⟩
  ihave ⟨Herr, Hstd, Hno, Hcon, #Himg⟩ := world_exitPartsE N L Room hEL ρ st d $$ Hw
  ihave #Hgp := codeRes_gp $$ Hcode
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ [])
    (F := iprop(blockOwn (sTop.toNat + 496) 256 ∗ Stdio.stdioOwn ∗ Stdio.errnoOwn ∗
      consoleOwn st.out ∗
      ownImg (InExt (sTop.toNat + 752, 16)) imgT ∗ Φ (0, st.out) ∗ gp ↦ᵣ□ Newlib.gpV ∗ binImg))
  rotate_left
  · iframe Herr Hstd Hno Hcon HT HΦ Hms Hgp Himg
    iapply codeRes_text $$ Hcode
  intro F'
  refine TopEpi_run (m := ∅) hlive (by decide) (by decide) (by decide) (by decide) h2 hra ?_
  apply swp_closeRM
  intro R' Mt' hR' _
  have e10 : R' 10 = 0#64 := by subst hR'; ix_reg; exact h21
  have e1 : R' 1 = 0x800045ec#64 := by subst hR'; ix_reg
  have e2 : R' 2 = sTop := by subst hR'; ix_reg; decide
  unfold F'
  iintro ⟨⟨Herr, Hstd, Hno, Hcon, HT, HΦ, #Hgp, #Himg⟩, Hms⟩
  ihave ⟨Hpc, Hra, Hregs, -⟩ := ms_exit $$ Hms
  ihave ⟨Hsp, Hcs, Htmp, Hargs⟩ := (regFile_newlib R').1 $$ Hregs
  ihave ⟨Hs0, Hcs⟩ := (calleeSaved_split R').1 $$ Hcs
  ihave ⟨Ha0, Hargs⟩ := (sepL_args_split R').1 $$ Hargs
  ihave Htmp := clobbered_of_fn _ R' $$ Htmp
  ihave Hargs := clobbered_of_fn _ R' $$ Hargs
  rw [e10, e2]
  iapply wp_mainOkTail H live hcl Wp sTop (R' 1) (R' 8) R' st.out imgT mainSp_top hT
  iframe Hpc Ha0 Hra Hs0 Hsp Hcs Htmp Hgp Himg HT Herr Hstd Hno Hcon HΦ
  rw [show List.drop 1 argRegs = [11, 12, 13, 14, 15, 16, 17] from rfl]
  iexact Hargs

/-- The spills `interp_run`'s prologue leaves in its frame: `in`, the `repl`
flag, the count, the statement array, the link, `main`'s `s0`. -/
structure TopSpills (Mt : Mem) (R0 : Nat → BitVec 64) (ret : BitVec 64) : Prop where
  inp : ldv .ld Mt (sTop.toNat - 176) = R0 10
  flag : ldv .ld Mt (sFr + 8#64).toNat = R0 13
  cnt : ldv .ld Mt (sFr + 16#64).toNat = R0 12
  arr : ldv .ld Mt (sFr + 24#64).toNat = R0 11
  ra : ldv .ld Mt (sFr + 168#64).toNat = ret
  s0 : ldv .ld Mt (sFr + 160#64).toNat = R0 8

omit I in
/-- **`interp_run`'s spills** (`0x800043ec`..`0x80004420`), for either WP:
the 176-byte frame below `sTop` becomes the run's owned bytes; the run reaches
the `jal setjmp` with `a0 = in + 16`. -/
theorem wp_topSpill (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {R0 : Nat → BitVec 64} {ret : BitVec 64} {F : IProp GF}
    (h2 : R0 2 = sTop)
    (K : ∀ (R : Nat → BitVec 64) (Mt : Mem), R 2 = sFr → R 10 = R0 10 + 16#64 → R 1 = ret →
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 10 → R r = R0 r) → TopSpills Mt R0 ret →
      F ∗ codeRes ∗ ms 0x80004424#64 R (InExt (sTop.toNat - 176, 176)) Mt ⊢ Wp.W Φ) :
    F ∗ codeRes ∗ PC ↦ᵣ 0x800043ec#64 ∗ ra ↦ᵣ ret ∗ regFile R0 ∗
      blockOwn (sTop.toNat - 176) 176 ⊢ Wp.W Φ := by
  iintro ⟨HF, #Hcode, Hpc, Hra, Hregs, Hfr⟩
  ihave ⟨%Mt0, Hms⟩ := ms_intro $$ [Hpc Hra Hregs Hfr]
  · iframe Hpc Hra Hregs; unfold blockOwn; iexact Hfr
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ []) (F := iprop(F ∗ codeRes))
  rotate_left
  · iframe HF Hms Hcode
    iapply codeRes_text $$ Hcode
  intro F'
  refine TopProl_run (m := ∅) hlive (by decide) (by decide) (by decide) (by decide)
    (by ix_reg; exact h2) ?_
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  refine .trans ?_ (K R1 Mt1 ?_ ?_ ?_ ?_ ?_)
  · unfold F'
    iintro ⟨⟨HF, #Hcode⟩, Hms⟩
    iframe HF Hcode Hms
  · subst hR1; ix_reg
  · subst hR1; ix_reg
  · subst hR1; ix_reg
  · intro r h1 h2' h10; subst hR1; simp only [upd_apply, h1, h2', h10, ite_false]
  · subst hMt1
    have e : sTop.toNat - 176 = 0x87fffc50 := by decide
    constructor
    · rw [e]; ix_fwd; ix_reg
    · ix_fwd; ix_reg
    · ix_fwd; ix_reg
    · ix_fwd; ix_reg
    · ix_fwd; ix_reg
    · ix_fwd; ix_reg

/-- The `jmp_buf` words `setjmp` wrote: the landing `ra` and `sp`. -/
structure JbTop (jb : Nat → BitVec 8) (sI : BitVec 64) : Prop where
  ra : jbWord inpTop jb 0 = 0x80004428#64
  sp : jbWord inpTop jb 13 = sI

theorem jbTop_of {img img2 : Nat → BitVec 8} {R : Nat → BitVec 64}
    (h : Setjmp.SetjmpImg (BitVec.ofNat 64 (inpTop + 16)) 0x80004428#64 (R 2) R img) :
    JbTop (VsaIris.glue (InExt (inpTop + 16, 112)) img img2) (R 2) where
  ra := by
    have := h.words 0 (by decide)
    unfold jbWord
    rw [imgW_agree (g := img) (fun j hj => by
      unfold VsaIris.glue InExt interpJmpOff; simp only; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))])]
    have e : (BitVec.ofNat 64 (inpTop + 16)).toNat = inpTop + 16 := by decide
    rw [e] at this
    simpa [Setjmp.sjVal, interpJmpOff] using this
  sp := by
    have := h.words 13 (by decide)
    unfold jbWord
    rw [imgW_agree (g := img) (fun j hj => by
      unfold VsaIris.glue InExt interpJmpOff; simp only; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))])]
    have e : (BitVec.ofNat 64 (inpTop + 16)).toNat = inpTop + 16 := by decide
    rw [e] at this
    simpa [Setjmp.sjVal, interpJmpOff] using this

/-- **`setjmp`, then the world**, for either WP: at `interp_run`'s
`jal setjmp` with `a0 = in + 16`, `setjmp` fills the `jmp_buf` (taken out of
`worldPre`'s exclusive one and made read-only), returns `0`, and the world is
`world`, the `jmp_buf`'s landing words named (`JbTop`). -/
theorem wp_topSetjmp (hlive : ∀ p ∈ interpText, live p.1) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {ρ : Regime} {st : St} {d : Nat}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem}
    (h10 : R 10 = BitVec.ofNat 64 (inpTop + 16)) :
    codeRes ∗ binImg ∗ ms 0x80004424#64 R S Mt ∗ worldPre N L Room inpTop ρ st d ∗
      (∀ jb : Nat → BitVec 8, ⌜JbTop jb (R 2)⌝ -∗ jmpRO inpTop jb -∗
        world N L Room inpTop ρ st d -∗
        ms 0x80004428#64 (upd (upd R 10 0#64) 1 0x80004428#64) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  have hjb : Setjmp.JbAt (BitVec.ofNat 64 (inpTop + 16)) := ⟨by decide, by decide, by decide⟩
  unfold worldPre interpCtxPre jmpRO interpCore
  iintro ⟨#Hcode, #Himg, Hms, ⟨%H, %B, Hh, Hs, Hc, Hstd, ⟨Hcore, Hjb⟩, %hB⟩, HK⟩
  ihave ⟨Hj1, Hj2⟩ := blockOwn_split (inpTop + interpJmpOff) interpJmpLen 112 (inpTop + 128) 96
    (by decide) (by decide) (by decide) $$ Hjb
  unfold blockOwn
  ihave ⟨%img0, Hj1⟩ := ownSet_fn _ $$ Hj1
  iapply ms_callSetjmp hlive hcl Wp hjb h10 img0
  iframe Hcode Himg Hms
  isplitl [Hj1]
  · have e : (BitVec.ofNat 64 (inpTop + 16)).toNat = inpTop + 16 := by decide
    rw [e]
    iapply ownSet_iff _ (fun a => by simp only [InExt, interpJmpOff] <;> omega) $$ Hj1
  iintro %img %himg HJ Hms
  ihave ⟨%img2, Hj2⟩ := ownSet_fn _ $$ Hj2
  ihave HJ := ownSet_glue (InExt (inpTop + 16, 112)) (InExt (inpTop + 128, 96)) img img2
    (fun a h1 h2 => by unfold InExt at h1 h2; simp only at h1 h2; omega) $$ [HJ Hj2]
  · iframe Hj2
    have e : (BitVec.ofNat 64 (inpTop + 16)).toNat = inpTop + 16 := by decide
    rw [e] at *
    iexact HJ
  ihave HJ := ownSet_iff (T := InExt (inpTop + interpJmpOff, interpJmpLen)) _
    (fun a => by unfold InExt interpJmpOff interpJmpLen; simp only; omega) $$ HJ
  iapply Wp.fupd
  imod ownImg_persist _ _ $$ HJ with #HJ
  imodintro
  have hjt := jbTop_of (img2 := img2) himg
  iapply HK $$ %_ %hjt HJ [Hh Hs Hc Hstd Hcore] Hms
  unfold world worldE interpCtxE
  iexists H, B
  iframe Hh Hs Hc Hstd Hcore Himg
  isplitl []
  · iexists _
    unfold jmpRO interpJmpOff interpJmpLen
    iframe HJ
    ipureintro
    have := hjt.ra
    unfold jbWord at this
    simp only [Nat.mul_zero, Nat.add_zero, interpJmpOff] at this
    rw [this]; decide
  ipureintro; exact hB

theorem ofNat_toInt_small' {a : Nat} (h : a < 2 ^ 31) : (BitVec.ofNat 64 a).toInt = a := by
  rw [BitVec.toInt_eq_toNat_cond]; simp; omega

theorem shl3_ofNat {a : Nat} (h : a < 2 ^ 31) :
    BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := a) (by omega)]
  omega

omit I in
/-- **The count test** (`0x80004428`..`0x80004454`), for either WP: `setjmp`
returned `0` (`bnez` not taken), `s5 = 0`; an empty program goes to the
epilogue `0x80004514`, a nonempty one sets up the loop head `0x8000448c`
(`s0` the array, `s2` its end, `s3 = 3`, `s4 = 1`). -/
theorem wp_topHead (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {R : Nat → BitVec 64} {Mt : Mem} {F : IProp GF}
    {stmts count : Nat} (hc : count < 2 ^ 31)
    (h2 : R 2 = sFr) (h10 : R 10 = 0#64)
    (hcnt : ldv .ld Mt (sFr + 16#64).toNat = BitVec.ofNat 64 count)
    (harr : ldv .ld Mt (sFr + 24#64).toNat = BitVec.ofNat 64 stmts)
    (K0 : count = 0 → ∀ R' : Nat → BitVec 64, R' 2 = sFr → R' 21 = 0#64 →
      F ∗ codeRes ∗ ms 0x80004514#64 R' (InExt (sTop.toNat - 176, 176)) Mt ⊢ Wp.W Φ)
    (K1 : 0 < count → ∀ R' : Nat → BitVec 64, InterpHead R' sTop (BitVec.ofNat 64 stmts) 0 count →
      R' 21 = 0#64 →
      F ∗ codeRes ∗ ms 0x8000448c#64 R' (InExt (sTop.toNat - 176, 176)) Mt ⊢ Wp.W Φ) :
    F ∗ codeRes ∗ ms 0x80004428#64 R (InExt (sTop.toNat - 176, 176)) Mt ⊢ Wp.W Φ := by
  iintro ⟨HF, #Hcode, Hms⟩
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ []) (F := iprop(F ∗ codeRes))
  rotate_left
  · iframe HF Hms Hcode
    iapply codeRes_text $$ Hcode
  intro F'
  refine TopHead_run (m := ∅) hlive (by decide) (by decide) (by decide) (by decide) h2 h10 hcnt harr
    (fun h => absurd h10 h) (fun h => absurd h10 h) (fun h => absurd h10 h) ?_ ?_
  · intro _ hle
    have h0 : count = 0 := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hle
      rw [ofNat_toInt_small' hc] at hle
      simp at hle; omega
    apply swp_closeRM
    intro R1 Mt1 hR1 hMt1
    subst hMt1
    refine .trans ?_ (K0 h0 R1 (by subst hR1; ix_reg; exact h2) (by subst hR1; ix_reg))
    unfold F'
    iintro ⟨⟨HF, #Hcode⟩, Hms⟩
    iframe HF Hcode Hms
  · intro _ hlt
    have h0 : 0 < count := by
      rw [ofNat_toInt_small' hc] at hlt
      simp at hlt; omega
    apply swp_closeRM
    intro R1 Mt1 hR1 hMt1
    subst hMt1
    refine .trans ?_ (K1 h0 R1 ?_ (by subst hR1; ix_reg))
    · unfold F'
      iintro ⟨⟨HF, #Hcode⟩, Hms⟩
      iframe HF Hcode Hms
    · subst hR1
      refine ⟨by ix_reg; exact h2, by ix_reg; simp, by ix_reg; rw [shl3_ofNat hc], by ix_reg,
        by ix_reg⟩

end Normal

/-! ## The entry state and the loop head -/

section Entry

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst VsaIris.Newlib
  Vsa.RuntimeRepr Vsa.Sim.LayoutInstance VsaIris.Newlib.MainErr VsaIris.Newlib.MainOk VsaIris.VsaHeap

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- `interp_run`'s argument registers at its entry (`InterpRunPhysicalFacts`:
`sp`, `in`, `stmts`, `count`, `repl = 0`). -/
structure TopRegs (R0 : Nat → BitVec 64) (stmts count : Nat) : Prop where
  sp : R0 2 = sTop
  a0 : R0 10 = BitVec.ofNat 64 inpTop
  a1 : R0 11 = BitVec.ofNat 64 stmts
  a2 : R0 12 = BitVec.ofNat 64 count
  a3 : R0 13 = 0#64

/-- **`interp_run`'s entry, the pure facts** (`InterpRunPhysicalFacts` and
`Boot`, INTERP_DESIGN.md §5.1): the argument registers `in`, `stmts`,
`count`, `repl = 0` and `sp = spEntry` in `R0`; the program's statement array
over the read-only view `P` of the boundary memory `m`; its placement; the
stack admissibility; `in->globals = g`; `main`'s saved `ra` (`crt0`'s link). -/
structure TopEntry (m : Mem) (P : Nat → Prop) (stmts count : Nat) (p : Program) (g : Nat)
    (R0 : Nat → BitVec 64) : Prop where
  regs : TopRegs R0 stmts count
  repr : StmtArrayReprWithin m P stmts count p
  geo : ∀ k, P k → ReadOK k
  ram : 0x80000000 ≤ stmts ∧ stmts + 8 * count ≤ 0x100000000
  win : tohostAddr + 16 ≤ stmts
  fits : ProgramStackFits p
  globals : read64 m inpTop = some g
  mainRa : read64 m 0x87fffff8 = some 0x80000038

/-- **`interp_run`'s entry, the resources** (the registers at `R0`, `PC`
at `interp_run`, `ra` at `main`'s link, and `bootRes`'s pieces this proof
uses: `worldPre`, frame 0's address, the read-only view `P`, the stack below
`spEntry`, `main`'s frame outside `struct Interp`), with the code
(`codeRes`: the interpreter's text and `gp`) and the binary's image. -/
def topPre (N : NativeAddrs) (ρ : Regime) (m : Mem) (P : Nat → Prop) (g : Nat)
    (R0 : Nat → BitVec 64) : IProp GF :=
  iprop(PC ↦ᵣ 0x800043ec#64 ∗ ra ↦ᵣ 0x800045ec#64 ∗ regFile R0 ∗ codeRes ∗ binImg ∗
    worldPre N vsaLayoutP vsaRoomB inpTop ρ initSt 0 ∗ frameAt 0 g ∗ roOn P m ∗
    blockOwn stackSL.lo (spEntry - stackSL.lo) ∗ ownImg (CallerByte inpTop) (memImg m))

/-- The loop head's pure facts after the prologue: the loop's registers, the
frame words it reads, `s5 = 0`, the spilled link and `main`'s `s0`. -/
structure TopLoopFacts (R0 : Nat → BitVec 64) (stmts count : Nat) (R : Nat → BitVec 64)
    (Mt : Mem) : Prop where
  head : InterpHead R sTop (BitVec.ofNat 64 stmts) 0 count
  frame : InterpFrame Mt sTop inpTop
  s5 : R 21 = 0#64
  ra : ldv .ld Mt (sFr + 168#64).toNat = 0x800045ec#64
  s0 : ldv .ld Mt (sFr + 160#64).toNat = R0 8

/-- The loop head's resources: the run's frame without the result slot, the
slot, the code and data view the loop reads, the stack below the frame, the
world after `setjmp`, `main`'s saved pair, and the `jmp_buf`. -/
def topLoopRes (N : NativeAddrs) (ρ : Regime) (m : Mem) (P : Nat → Prop) (stmts count g : Nat)
    (R : Nat → BitVec 64) (Mt : Mem) : IProp GF :=
  iprop(ms 0x8000448c#64 R (interpS sTop) Mt ∗ slot24 (sFr + 88#64).toNat ∗ codeRes ∗ binImg ∗
    roOn P m ∗ roOwn roR (interpText ++ dataOf m (interpView stmts count inpTop)) ∗
    frameAt 0 g ∗ stackScratch sFr (sFr.toNat - stackSL.lo) ∗
    world N vsaLayoutP vsaRoomB inpTop ρ initSt 0 ∗
    ownImg (InExt (sTop.toNat + 752, 16)) (memImg m) ∗
    (∃ jb, ⌜JbTop jb sFr⌝ ∗ jmpRO inpTop jb))

/-- A represented statement array's bytes: in the view, present. -/
theorem stmtArray_view {m : Mem} {P : Nat → Prop} :
    ∀ {a n : Nat} {ss : List Stmt}, StmtArrayReprWithin m P a n ss →
      ∀ b, a ≤ b → b < a + 8 * n → P b ∧ (m[b]?).isSome
  | _, _, _, .nil, b, h1, h2 => absurd h2 (by omega)
  | a, _, _, .cons (n := n) hp hcov _ hrest, b, h1, h2 => by
    by_cases hb : b < a + 8
    · have hi : b = a + (b - a) := by omega
      refine ⟨hi ▸ hcov _ (by omega), ?_⟩
      rw [hi, readLE_mapped hp _ (by omega)]; rfl
    · exact stmtArray_view hrest b (by omega) (by omega)

omit I in
/-- `in->globals` read-only out of the world's word, as a read-only view of
the boundary memory. -/
theorem roOn_globals {m : Mem} {g : Nat} (hg : read64 m inpTop = some g) {img : Nat → BitVec 8}
    (hi : imgLE img inpTop 8 = g) :
    roImg (GF := GF) (InExt (inpTop, 8)) img ⊢ roOn (InExt (inpTop, 8)) m := by
  unfold roImg roOn
  iintro #H
  imodintro
  iintro %k %b %hk %hb
  have hag := imgLE_inj (hi.trans (readLE_memImg hg).symm)
  have e : img k = b := by
    have := hag (k - inpTop) (by unfold InExt at hk; simp only at hk; omega)
    rw [show inpTop + (k - inpTop) = k by unfold InExt at hk; simp only at hk; omega] at this
    rw [this, memImg_eq hb]
  rw [← e]
  iapply H $$ %k %hk

omit I in
theorem roOn_or {P Q : Nat → Prop} {m : Mem} :
    roOn (GF := GF) P m ∗ roOn Q m ⊢ roOn (fun k => P k ∨ Q k) m := by
  unfold roOn
  iintro ⟨#HP, #HQ⟩
  imodintro
  iintro %k %b %hk %hb
  rcases hk with hk | hk
  · iapply HP $$ %k %b %hk %hb
  · iapply HQ $$ %k %b %hk %hb

/-- `in->globals`, read-only, out of the world (which keeps it). -/
theorem world_globals (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (ρ : Regime)
    (st : St) (d : Nat) :
    world (GF := GF) N L Room inp ρ st d ⊢ world N L Room inp ρ st d ∗
      ∃ g img, ⌜imgLE img inp 8 = g⌝ ∗ roImg (InExt (inp, 8)) img ∗ frameAt 0 g := by
  unfold world worldE interpCtxE interpCoreE wordRO
  iintro ⟨%H, %B, Hh, Hs, Hc, Hstd, ⟨⟨%g, ⟨%img, #Hg, %hg⟩, #Hf, Hd, %hd, Hp, He⟩, Hjb⟩, %hB, #Hb⟩
  isplitl [Hh Hs Hc Hstd Hd Hp He Hjb]
  · iexists H, B
    iframe Hh Hs Hc Hstd Hjb Hb
    isplitl [Hd Hp He]
    · iexists g
      iframe Hf Hd Hp He
      isplitl []
      · iexists img; iframe Hg; ipureintro; exact hg
      ipureintro; exact hd
    ipureintro; exact hB
  iexists g, img
  iframe Hg Hf
  ipureintro; exact hg

/-- The loop's data view: the statement array and `in->globals`, in the view
`P ∨ in`, present. -/
theorem topView {m : Mem} {P : Nat → Prop} {stmts count : Nat} {p : Program} {g : Nat}
    {R0 : Nat → BitVec 64} (hE : TopEntry m P stmts count p g R0) :
    ∀ a ∈ interpView stmts count inpTop, (P a ∨ InExt (inpTop, 8) a) ∧ (m[a]?).isSome := by
  intro a ha
  rw [List.mem_append, mem_accAddrs_iff, mem_accAddrs_iff] at ha
  rcases ha with ha | ha
  · obtain ⟨h1, h2⟩ := stmtArray_view hE.repr a ha.1 ha.2
    exact ⟨.inl h1, h2⟩
  · refine ⟨.inr ⟨ha.1, ha.2⟩, ?_⟩
    rw [show a = inpTop + (a - inpTop) by omega, readLE_mapped hE.globals _ (by omega)]; rfl

theorem imgW_mainRa {m : Mem} (h : read64 m 0x87fffff8 = some 0x80000038) :
    imgW (memImg m) (sTop.toNat + 760) = 0x80000038#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [show sTop.toNat + 760 = 0x87fffff8 by decide, imgW_read64 h]; rfl

/-- **`interp_run`'s prologue**, for either WP: the spills, `setjmp`, the
count test. An empty program returns `0` to `main`, which exits `0` with the
boundary output (`hΦ0`); a nonempty one reaches the loop head with
`topLoopRes` and `TopLoopFacts` (`K1`). -/
theorem wp_topPrologue (H : NewlibHoles) (hlive : ∀ p ∈ interpText, live p.1) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {ρ : Regime} {m : Mem} {P : Nat → Prop} {stmts count : Nat} {p : Program}
    {g : Nat} {R0 : Nat → BitVec 64} (hE : TopEntry m P stmts count p g R0)
    (hΦ0 : count = 0 → ⊢ Φ (0, initSt.out))
    (K1 : 0 < count → ∀ (R : Nat → BitVec 64) (Mt : Mem), TopLoopFacts R0 stmts count R Mt →
      topLoopRes N ρ m P stmts count g R Mt ⊢ Wp.W Φ) :
    topPre N ρ m P g R0 ⊢ Wp.W Φ := by
  have hc : count < 2 ^ 31 := by have := hE.ram; omega
  unfold topPre
  iintro ⟨Hpc, Hra, Hregs, #Hcode, #Himg, Hwp, #Hfr, #Hro, Hstk, Hcal⟩
  ihave ⟨Hfree, Hframe⟩ := freeStack_carve $$ Hstk
  ihave ⟨HT, -⟩ := ownSet_split (CallerByte inpTop) (InExt (sTop.toNat + 752, 16)) _ $$ Hcal
  ihave HT := ownSet_iff (T := InExt (sTop.toNat + 752, 16)) _ (fun a => by
    unfold CallerByte InterpByte InExt
    simp only [spEntry, stackSL_hi, show sTop.toNat = 0x87fffd00 from rfl,
      show inpTop = 0x87fffe10 from rfl]; omega) $$ HT
  ihave Hframe := blockOwn_cast (p' := sTop.toNat - 176) (n' := 176) (by decide) (by decide) $$ Hframe
  -- the spills
  iapply wp_topSpill hlive Wp (ret := 0x800045ec#64) (F := iprop(binImg ∗
      worldPre N vsaLayoutP vsaRoomB inpTop ρ initSt 0 ∗ frameAt 0 g ∗ roOn P m ∗
      blockOwn stackSL.lo (spEntry - interpRunFrame - stackSL.lo) ∗
      ownImg (InExt (sTop.toNat + 752, 16)) (memImg m))) hE.regs.sp ?_
  rotate_left
  · iframe Himg Hwp Hfr Hro Hfree HT Hcode Hpc Hra Hregs Hframe
  intro R1 Mt1 h2 h10 h1 hkeep hsp
  iintro ⟨⟨#Himg, Hwp, #Hfr, #Hro, Hfree, HT⟩, #Hcode, Hms⟩
  -- `setjmp`
  have h10' : R1 10 = BitVec.ofNat 64 (inpTop + 16) := by rw [h10, hE.regs.a0]; rfl
  iapply wp_topSetjmp hlive hcl Wp h10'
  iframe Hcode Himg Hms Hwp
  iintro %jb %hjb #Hjb Hw Hms
  rw [h2] at hjb
  -- the count test
  iapply wp_topHead hlive Wp (stmts := stmts) (count := count)
    (R := upd (upd R1 10 0#64) 1 0x80004428#64) (Mt := Mt1) (F := iprop(binImg ∗
      world N vsaLayoutP vsaRoomB inpTop ρ initSt 0 ∗ frameAt 0 g ∗ roOn P m ∗
      blockOwn stackSL.lo (spEntry - interpRunFrame - stackSL.lo) ∗
      ownImg (InExt (sTop.toNat + 752, 16)) (memImg m) ∗ jmpRO inpTop jb)) hc
    (by ix_reg; exact h2) (by ix_reg) (hsp.cnt.trans hE.regs.a2) (hsp.arr.trans hE.regs.a1) ?_ ?_
  rotate_left 2
  · iframe Himg Hw Hfr Hro Hfree HT Hjb Hcode Hms
  · -- the empty program
    intro h0 R' h2' h21'
    iintro ⟨⟨#Himg, Hw, -, -, -, HT, -⟩, #Hcode, Hms⟩
    ihave ⟨Hms, -⟩ := ms_carveSlot (a := sTop.toNat - 176 + 88)
      (fun b hb => by simp only [InExt] at hb ⊢; omega) $$ Hms
    ihave HΦ := hΦ0 h0
    iapply wp_topNormal H hlive hcl Wp ErrnoOwn.errnoLend_vsa h2' h21' hsp.ra (imgW_mainRa hE.mainRa)
    iframe Hcode Hms Hw HT HΦ
  · -- the loop head
    intro hpos R' hh h21'
    iintro ⟨⟨#Himg, Hw, #Hfr, #Hro, Hfree, HT, #Hjb⟩, #Hcode, Hms⟩
    ihave ⟨Hms, Hslot⟩ := ms_carveSlot (a := sTop.toNat - 176 + 88)
      (fun b hb => by simp only [InExt] at hb ⊢; omega) $$ Hms
    ihave ⟨Hw, ⟨%g', %img, %hgi, #Hgw, #Hfr'⟩⟩ := world_globals _ _ _ _ _ _ _ $$ Hw
    ihave %hgg := frameAt_agree 0 g' g $$ [Hfr' Hfr]
    · iframe Hfr' Hfr
    subst hgg
    ihave #Hin := roOn_globals hE.globals hgi $$ Hgw
    ihave #Hro2 := roOn_or (P := P) (Q := InExt (inpTop, 8)) $$ [Hro Hin]
    · iframe Hro Hin
    have hK := K1 hpos R' Mt1 ⟨hh, ⟨?_, ?_⟩, h21', hsp.ra, hsp.s0⟩
    rotate_left
    · exact hsp.flag.trans hE.regs.a3
    · exact hsp.inp.trans hE.regs.a0
    iapply hK
    unfold topLoopRes
    iframe Hms Hcode Himg Hro Hfr Hw
    isplitl [Hslot]
    · rw [show (sFr + 88#64).toNat = sTop.toNat - 176 + 88 from by decide]
      iexact Hslot
    isplitl []
    · iapply roOwn_data (topView hE) $$ [Hcode Hro2]
      iframe Hcode Hro2
    isplitl [Hfree]
    · unfold stackScratch
      iapply blockOwn_cast (by decide) (by decide) $$ Hfree
    iframe HT
    iexists jb
    iframe Hjb
    ipureintro; exact hjb

end Entry

/-! ## The loop head's pure facts from the entry -/

section Facts

open Vsa.Sim.LayoutInstance

theorem stmts_toNat {m : Mem} {P : Nat → Prop} {stmts count : Nat} {p : Program} {g : Nat}
    {R0 : Nat → BitVec 64} (hE : TopEntry m P stmts count p g R0) :
    (BitVec.ofNat 64 stmts).toNat = stmts := by
  have := hE.ram; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem g_toNat {m : Mem} {P : Nat → Prop} {stmts count : Nat} {p : Program} {g : Nat}
    {R0 : Nat → BitVec 64} (hE : TopEntry m P stmts count p g R0) :
    (BitVec.ofNat 64 g).toNat = g := by
  have := readLE_lt hE.globals
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using this)]

/-- The loop's data view over the boundary memory. -/
theorem topData {m : Mem} {P : Nat → Prop} {stmts count : Nat} {p : Program} {g : Nat}
    {R0 : Nat → BitVec 64} (hE : TopEntry m P stmts count p g R0) :
    InterpData m m P (BitVec.ofNat 64 stmts) count inpTop (BitVec.ofNat 64 g) p := by
  have hs := stmts_toNat hE
  have hr := hE.ram; have hw := hE.win
  refine ⟨fun _ _ _ => rfl, ldv_ld_read64 hE.globals, ?_, ?_, ?_, by decide, by decide, by decide,
    by omega, by rw [hs]; exact hE.repr, hE.geo⟩ <;> rw [hs]
  · exact hr.1
  · exact hr.2
  · exact .inr hw

theorem topFrameGeom : ExecFrameGeom sTop := ⟨by decide, by decide, by decide, by decide⟩

theorem topStackGeom : StackGeom sFr (sFr.toNat - stackSL.lo) :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem topSlotGeom : SlotGeom (sFr + 88#64) := ⟨by decide, by decide, by decide⟩

theorem topNeeds {m : Mem} {P : Nat → Prop} {stmts count : Nat} {p : Program} {g : Nat}
    {R0 : Nat → BitVec 64} (hE : TopEntry m P stmts count p g R0) :
    ∀ x ∈ p, execNeed x 0 ≤ sFr.toNat - stackSL.lo ∧ x.bodiesBound perCallBudget = true := by
  intro x hx
  refine ⟨?_, bodiesBound_of_stackFits hE.fits hx⟩
  have := execNeed_of_stackFits hE.fits hx
  have e : sFr.toNat = spEntry - interpRunFrame := by decide
  omega

/-- The count is the program's length. -/
theorem topCount {m : Mem} {P : Nat → Prop} {stmts count : Nat} {p : Program} {g : Nat}
    {R0 : Nat → BitVec 64} (hE : TopEntry m P stmts count p g R0) : p.length = count :=
  stmtArray_length hE.repr

end Facts

/-! ## `interp_run`'s whole run -/

section Run

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst VsaIris.Newlib
  Vsa.RuntimeRepr Vsa.Sim.LayoutInstance VsaIris.VsaHeap

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- **`interp_run`'s whole run, total mode** (INTERP_DESIGN.md §4.4, §5.2):
from `interp_run`'s entry (`topPre` in the counted regime at the program's
cost `n`) and the loop motive at the program's derivation `D`, the machine
halts with code 0 and output `st'.out`. -/
theorem interpRun_total (H : NewlibHoles) (hlive : ∀ p ∈ interpText, live p.1) (hcl : CodeLive live)
    {N : NativeAddrs} {m : Mem} {P : Nat → Prop} {stmts count : Nat} {p : Program} {g : Nat}
    {R0 : Nat → BitVec 64} {st' : St} {n : Nat} (hE : TopEntry m P stmts count p g R0)
    (D : ExecSeqCost initSt 0 0 p st' .normal n)
    (hloop : interpSeqT_body (GF := GF) live N vsaLayoutP vsaRoomB inpTop initSt 0 0 p st' .normal n D) :
    topPre (GF := GF) N (.counted n) m P g R0 ⊢
      (twpW (GF := GF) (vsaModel live)).W (fun v => iprop(⌜v = (0, st'.out)⌝)) := by
  iapply wp_topPrologue H hlive hcl (twpW (GF := GF) (vsaModel live)) hE ?_ ?_
  · intro h0
    have hp : p = [] := List.eq_nil_of_length_eq_zero ((topCount hE).trans h0)
    subst hp
    cases D
    ipureintro; rfl
  · intro hpos R Mt hf
    have hp : p ≠ [] := by
      intro e; subst e; have := topCount hE; simp at this; omega
    have hK := hloop (fun v => iprop(⌜v = (0, st'.out)⌝)) 0 0 count sTop (BitVec.ofNat 64 stmts)
      (BitVec.ofNat 64 g) R Mt m m P p (sFr.toNat - stackSL.lo)
      (ownImg (InExt (sTop.toNat + 752, 16)) (memImg m)) hp (List.drop_zero (l := p)).symm (topData hE)
      hf.head topFrameGeom hf.frame topStackGeom (topNeeds hE) topSlotGeom
    rw [stmts_toNat hE, g_toNat hE, Nat.zero_add] at hK
    unfold topLoopRes
    iintro ⟨Hms, Hslot, #Hcode, #Himg, #Hro, #Hdv, #Hfr, Hst, Hw, HT, -⟩
    iapply hK
    iframe HT Hms Hcode Hro Hdv Hfr Hst Hw
    isplitl [Hslot]
    · iexact Hslot
    iintro %R' %hkeep HT Hms - - Hw
    rw [interpExit_normal]
    have h2 : R' 2 = sFr := (hkeep 2 (by decide)).trans hf.head.sp
    have h21 : R' 21 = 0#64 := (hkeep 21 (by decide)).trans hf.s5
    iapply wp_topNormal H hlive hcl (twpW (GF := GF) (vsaModel live)) ErrnoOwn.errnoLend_vsa h2 h21 hf.ra (imgW_mainRa hE.mainRa)
    iframe Hcode Hms Hw HT
    ipureintro; rfl

end Run

/-! ## From the boundary (`Boot`, `bootRes`) -/

section Boundary

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst VsaIris.Newlib
  Vsa.RuntimeRepr Vsa.Sim.LayoutInstance VsaIris.VsaHeap

theorem readOK_of_sharedGeom {P : Nat → Prop} (h : Vsa.Sim.SharedGeom P stackSL) :
    ∀ k, P k → ReadOK k := fun k hk => by
  have h1 := h.ram k hk; have h2 := h.htif k hk
  have e : Vsa.Sim.tohostAddr = 0x8001ad00 := rfl
  rw [e] at h2
  exact ⟨by omega, by omega, .inr (by rw [e]; omega), by omega, .inr (by rw [e]; omega)⟩

/-- **The entry's pure facts at the boundary**: `Boot`'s witnesses, the
read-only view being the boundary's shared bytes. -/
theorem topEntry_of_boot {c : Vsa.Machine.Config} {p : Program} (b : Boot c p)
    {R0 : Nat → BitVec 64} (hR : TopRegs R0 b.stmts b.count) :
    TopEntry c.σ.mem b.D.shared b.stmts b.count p (b.φf 0) R0 where
  regs := hR
  repr := (b.owned.program p b.repr).1
  geo := readOK_of_sharedGeom b.heapFacts.shared_geom
  ram := b.ready.stmts_ram
  win := b.ready.stmts_win
  fits := b.fits
  globals := by
    have h := b.ready.globals
    rwa [b.inp_toNat] at h
  mainRa := b.ready.main_ra

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The binary's image out of the boundary's read-only code view. -/
theorem binImg_of_roOn {m : Mem} (ht : Vsa.Sim.Code.FixedTextLoaded m)
    (hr : Vsa.Sim.Code.FixedRodataLoaded m) : roOn (GF := GF) CodeByte m ⊢ binImg := by
  unfold binImg roImg roOn
  iintro #H
  isplitl []
  · imodintro
    iintro %k %hk
    iapply H $$ %k %(textByte k) %(by unfold CodeByte; unfold textDom at hk; omega) %(by
      have := ht (k - 0x80000000) (by
        unfold textDom at hk; unfold Vsa.Sim.Code.fixedTextSize; omega)
      rw [show Vsa.Sim.Code.fixedTextBase + (k - 0x80000000) = k by
        unfold textDom at hk; unfold Vsa.Sim.Code.fixedTextBase; omega] at this
      exact this)
  · imodintro
    iintro %k %hk
    iapply H $$ %k %(rodataByte k) %(by unfold CodeByte; unfold rodataDom at hk; omega) %(by
      have := hr (k - 0x80018be0) (by
        unfold rodataDom at hk; unfold Vsa.Sim.Code.fixedRodataSize; omega)
      rw [show Vsa.Sim.Code.fixedRodataBase + (k - 0x80018be0) = k by
        unfold rodataDom at hk; unfold Vsa.Sim.Code.fixedRodataBase; omega] at this
      exact this)

variable [I : InterpGS GF] {live : Nat → Prop}

/-- **The entry's resources at the boundary**: `bootRes` (`world_of_boundary`)
with the entry registers and the interpreter's code (`codeRes`). -/
theorem topPre_of_bootRes {c : Vsa.Machine.Config} {p : Program} (b : Boot c p) (ρ : Regime)
    (R0 : Nat → BitVec 64) :
    bootRes b ρ ∗ PC ↦ᵣ 0x800043ec#64 ∗ ra ↦ᵣ 0x800045ec#64 ∗ regFile R0 ∗ codeRes ⊢
      topPre (GF := GF) b.N ρ c.σ.mem b.D.shared (b.φf 0) R0 := by
  have hi : b.inp.toNat = inpTop := b.inp_toNat
  unfold bootRes topPre
  rw [hi]
  iintro ⟨⟨Hw, #Hfr, -, #Hcode, #Hsh, Hstk, Hcal, -⟩, Hpc, Hra, Hregs, #Hc⟩
  ihave #Himg := binImg_of_roOn b.ready.text_image b.ready.rodata_image $$ Hcode
  iframe Hw Hfr Hsh Hstk Hcal Hpc Hra Hregs Hc Himg

/-- **`interp_run`'s whole run from the boundary, total mode**: `bootRes` in
the counted regime at the program's cost, the entry registers and the code. -/
theorem interpRun_total_boot (H : NewlibHoles) (hlive : ∀ p ∈ interpText, live p.1)
    (hcl : CodeLive live) {c : Vsa.Machine.Config} {p : Program} (b : Boot c p)
    {R0 : Nat → BitVec 64} (hR : TopRegs R0 b.stmts b.count) {st' : St} {n : Nat}
    (D : ExecSeqCost initSt 0 0 p st' .normal n)
    (hloop : interpSeqT_body (GF := GF) live b.N vsaLayoutP vsaRoomB inpTop initSt 0 0 p st' .normal
      n D) :
    bootRes b (.counted n) ∗ PC ↦ᵣ 0x800043ec#64 ∗ ra ↦ᵣ 0x800045ec#64 ∗ regFile R0 ∗ codeRes ⊢
      (twpW (GF := GF) (vsaModel live)).W (fun v => iprop(⌜v = (0, st'.out)⌝)) :=
  (topPre_of_bootRes b _ R0).trans (interpRun_total H hlive hcl (topEntry_of_boot b hR) D hloop)

end Boundary

end VsaIris.Interp
