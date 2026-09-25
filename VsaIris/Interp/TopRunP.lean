import VsaIris.Interp.TopRun
import VsaIris.Interp.ExecArm
import VsaIris.Interp.SpecErr
import VsaIris.Vsa.TopAbrupt
import VsaIris.Interp.ProofValueCons
import VsaIris.Interp.LeafErr

/-!
# `interp_run`'s whole run, partial mode (lane A, INTERP_DESIGN.md §4.4, §5.3)

The prologue and the normal exit are `TopRun`'s mode-generic lemmas. What the
partial run adds are the non-normal ends: a top-level `return`/`break`/
`continue` (`interp_run` formats an error and returns 1, `main` exits 70) and
an abort (the `longjmp` landing: exit 70; out of memory: exit 1).
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

/-! ## The top-level status blocks, with the `line` word read by havoc -/

#ix_seg TopAbrRet_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    (h2 : R 2 = sFr) (hin : ldv .ld Mt (sTop.toNat - 176) = BitVec.ofNat 64 inpTop)
    (hline : LdOK (R 9 + 4#64).toNat 4) :
    IW live m [] (interpS sTop) Q 0x80004540#64 R Mt
  by ix_run hlive using [h2, hin, hline, interpS, sFr_toNat] at 0x80004558

#ix_seg TopAbrBrk_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    (h2 : R 2 = sFr) (hin : ldv .ld Mt (sTop.toNat - 176) = BitVec.ofNat 64 inpTop)
    (hline : LdOK (R 9 + 4#64).toNat 4) :
    IW live m [] (interpS sTop) Q 0x80004564#64 R Mt
  by ix_run hlive using [h2, hin, hline, interpS, sFr_toNat] at 0x8000457c

#ix_seg TopTlRet_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    (h2 : R 2 = sFr) (hRA : ldv .ld Mt (sFr + 168#64).toNat = 0x800045ec#64) :
    IW live m [] (interpS sTop) Q 0x8000455c#64 R Mt
  by ix_run hlive using [h2, hRA, interpS]

#ix_seg TopTlBrk_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    (h2 : R 2 = sFr) (hRA : ldv .ld Mt (sFr + 168#64).toNat = 0x800045ec#64) :
    IW live m [] (interpS sTop) Q 0x80004580#64 R Mt
  by ix_run hlive using [h2, hRA, interpS]


section Abrupt

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst VsaIris.Newlib
  Vsa.RuntimeRepr Vsa.Sim.LayoutInstance VsaIris.Newlib.MainErr VsaIris.Newlib.TopAbrupt

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- The frame words the non-normal ends read: `in`, the link, `main`'s `s0`
(`&_impure_ptr`, which `main`'s error line loads `stderr` through). -/
structure TopFrameP (Mt : Mem) : Prop where
  inp : ldv .ld Mt (sTop.toNat - 176) = BitVec.ofNat 64 inpTop
  ra : ldv .ld Mt (sFr + 168#64).toNat = 0x800045ec#64
  s0 : ldv .ld Mt (sFr + 160#64).toNat = 0x8001b970#64

/-- A top-level status block's two runs (`TopSite`'s `head`, its `jal`):
the staging of `snprintf(in->err_msg, 256, fmt, s->line)` up to the `jal`
(`line` read by havoc: the statement node's representation does not cover
the word, `s1` is only known to be a node, `ReadOK`), and `li s5,1; j` into
the epilogue, up to `ret`. -/
structure TopRuns (live : Nat → Prop) (T : TopSite) : Prop where
  stage : ∀ {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem} {R : Nat → BitVec 64},
    R 2 = sFr → ldv .ld Mt (sTop.toNat - 176) = BitVec.ofNat 64 inpTop → LdOK (R 9 + 4#64).toNat 4 →
    (∀ R' : Nat → BitVec 64, R' 2 = sFr → R' 10 = BitVec.ofNat 64 inpTop + 224#64 →
      R' 11 = 256#64 → R' 12 = T.fmt → (∀ x ∈ Newlib.calleeSaved, R' x = R x) →
      IW live ∅ [] (interpS sTop) Q (BitVec.ofNat 64 T.jal.pc) R' Mt) →
    IW live ∅ [] (interpS sTop) Q (BitVec.ofNat 64 T.head) R Mt
  tail : ∀ {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem} {R : Nat → BitVec 64},
    R 2 = sFr → ldv .ld Mt (sFr + 168#64).toNat = 0x800045ec#64 →
    (∀ R' : Nat → BitVec 64, R' 10 = 1#64 → R' 1 = 0x800045ec#64 → R' 2 = sTop →
      R' 8 = ldv .ld Mt (sFr + 160#64).toNat →
      IW live ∅ [] (interpS sTop) Q 0x800045ec#64 R' Mt) →
    IW live ∅ [] (interpS sTop) Q (BitVec.ofNat 64 (T.jal.pc + 4)) R Mt
  code : ∀ p ∈ codeFoot T.jal.pc T.jal.code, (p.1, p.2.2) ∈ interpText

theorem calleeSaved_ne {x : Nat} (hx : x ∈ Newlib.calleeSaved) :
    x ≠ 10 ∧ x ≠ 11 ∧ x ≠ 12 ∧ x ≠ 13 ∧ x ≠ 15 := by
  revert x; decide

theorem topRet_runs (hlive : ∀ p ∈ interpText, live p.1) : TopRuns live topRet where
  stage h2 hin hl k := TopAbrRet_run hlive h2 hin hl (fun v => k _ (by ix_reg; exact h2) (by ix_reg)
    (by ix_reg) (by ix_reg) (fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := calleeSaved_ne hx
      simp only [upd_apply, h1, h2, h3, h4, h5, ite_false]))
  tail h2 hra k := TopTlRet_run hlive h2 hra (k _ (by ix_reg) (by ix_reg) (by ix_reg; decide)
    (by ix_reg))
  code := interp_code_80004558

theorem topBrk_runs (hlive : ∀ p ∈ interpText, live p.1) : TopRuns live topBrk where
  stage h2 hin hl k := TopAbrBrk_run hlive h2 hin hl (fun v => k _ (by ix_reg; exact h2) (by ix_reg)
    (by ix_reg) (by ix_reg) (fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := calleeSaved_ne hx
      simp only [upd_apply, h1, h2, h3, h4, h5, ite_false]))
  tail h2 hra k := TopTlBrk_run hlive h2 hra (k _ (by ix_reg) (by ix_reg) (by ix_reg; decide)
    (by ix_reg))
  code := interp_code_8000457c

theorem ldOK_of_readOK {q : BitVec 64} (h : ReadOK q.toNat) : LdOK (q + 4#64).toNat 4 := by
  have h1 := h.lo; have h2 := h.win.1; have h3 := h.win.2
  have e : (q + 4#64).toNat = q.toNat + 4 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  unfold LdOK; rw [e]; unfold tohostAddr at *; omega

theorem sFr_eq : sFr = sTop - 176#64 := by decide

theorem topErr_toNat : (BitVec.ofNat 64 inpTop + 224#64).toNat = sTop.toNat + 496 := by decide

/-- **A top-level `return`/`break`/`continue`, then `exit(70)`**, for either
WP, from `interp_run`'s loop exit `T.head` (`topRet`: `0x80004540`,
`topBrk`: `0x80004564`): the run stages `snprintf(in->err_msg, 256, fmt,
s->line)` (the `line` word read by havoc: `s1 = R 9` is a statement node,
`ReadOK`), formats (`T.OK`: the `jal` and the format), returns 1, and
`main`'s error line exits 70. -/
theorem wp_topAbrupt (H : NewlibHoles) (hcl : CodeLive live)
    {L : DlLayout} {Room : RoomPred} (hEL : ErrnoOwn.ErrnoLend (GF := GF) L Room)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {T : TopSite} (hok : T.OK) (hS : TopRuns live T) (hΦ : ∀ o, ⊢ Φ (70, o))
    {N : NativeAddrs} {ρ : Regime} {st : St} {d : Nat}
    {R : Nat → BitVec 64} {Mt : Mem} {imgT : Nat → BitVec 8}
    (h2 : R 2 = sFr) (hs1 : ReadOK (R 9).toNat) (hf : TopFrameP Mt)
    (hT : imgW imgT (sTop.toNat + 760) = 0x80000038#64) :
    codeRes ∗ ms (BitVec.ofNat 64 T.head) R (interpS sTop) Mt ∗ slot24 (sFr + 88#64).toNat ∗
      stackScratch sFr (sFr.toNat - stackSL.lo) ∗ world N L Room inpTop ρ st d ∗
      ownImg (InExt (sTop.toNat + 752, 16)) imgT
    ⊢ Wp.W Φ := by
  iintro ⟨#Hcode, Hms, Hslot, Hst, Hw, HT⟩
  ihave ⟨Herr, Hstd, Herrno, Hcon, #Himg⟩ := world_exitPartsE N L Room hEL ρ st d $$ Hw
  ihave #Hgp := codeRes_gp $$ Hcode
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ [])
    (F := iprop(slot24 (sFr + 88#64).toNat ∗ stackScratch sFr (sFr.toNat - stackSL.lo) ∗
      blockOwn (sTop.toNat + 496) 256 ∗ Stdio.stdioOwn ∗ Stdio.errnoOwn ∗ consoleOwn st.out ∗
      ownImg (InExt (sTop.toNat + 752, 16)) imgT ∗ codeRes ∗ gp ↦ᵣ□ Newlib.gpV ∗ binImg))
  rotate_left
  · iframe Hslot Hst Herr Hstd Herrno Hcon HT Hms Hcode Hgp Himg
    iapply codeRes_text $$ Hcode
  intro F'
  refine hS.stage h2 hf.inp (ldOK_of_readOK hs1) ?_
  intro R1 e2 e10 e11 e12 _
  apply swp_closeF
  unfold F'
  iintro ⟨⟨Hslot, Hst, Herr, Hstd, Herrno, Hcon, HT, #Hcode, #Hgp, #Himg⟩, Hms⟩
  -- `snprintf(in->err_msg, 256, fmt, line)`
  have hsp1 : SpIn sFr snprintfNeed := ⟨by decide, by decide, by decide⟩
  have hsn := H.at.snprintf live Wp sFr (BitVec.ofNat 64 inpTop + 224#64) 256#64 T.fmt [R1 13] R1
    rodataDom (fun _ => False)
    rodataByte hcl (by simp) (by decide) (by decide) (fmt_ok hok _) hsp1 (by decide)
    (by rw [topErr_toNat]; decide) (by rw [topErr_toNat]; decide)
  unfold snprintfSpec at hsn
  ihave #Hsn := hsn
  have hj : JalExec (vsaModel live) T.jal.pc T.jal.code snprintfEntry := by
    have := JalSite.exec hok.jalCert live (hok.jalText.live hcl)
    rwa [hok.jalTgt] at this
  iapply ms_callNewlibA Wp hj hS.code (vs := [BitVec.ofNat 64 inpTop + 224#64, 256#64, T.fmt, R1 13])
    (X := iprop(blockOwn (sTop.toNat + 496) 256 ∗ readable rodataDom (fun _ => False) rodataByte ∗
      Stdio.stdioOwn))
    (Y := iprop(cstrBuf (sTop.toNat + 496) 256 ∗ readable rodataDom (fun _ => False) rodataByte ∗
      Stdio.stdioOwn))
    (P := fun ra0 => iprop(⌜ra0.toNat % 4 = 0⌝ ∗ argsAt ([BitVec.ofNat 64 inpTop + 224#64, 256#64, T.fmt] ++ [R1 13]) ∗
      blockOwn (BitVec.ofNat 64 inpTop + 224#64).toNat (256#64 : BitVec 64).toNat ∗
      readable rodataDom (fun _ => False) rodataByte ∗ Stdio.stdioOwn ∗
      callFrame sFr snprintfNeed Newlib.calleeSaved R1))
    (Q := fun _ => iprop(clobbered argRegs ∗
      cstrBuf (BitVec.ofNat 64 inpTop + 224#64).toNat (256#64 : BitVec 64).toNat ∗
      readable rodataDom (fun _ => False) rodataByte ∗ Stdio.stdioOwn ∗
      callFrame sFr snprintfNeed Newlib.calleeSaved R1))
    (R := R1) (S := interpS sTop) (Mt := Mt)
    (s := sFr) (need := snprintfNeed) (n := sFr.toNat - stackSL.lo) (by simp)
    (fun i hi => by
      match i, hi with
      | 0, _ => exact e10
      | 1, _ => exact e11
      | 2, _ => exact e12
      | 3, _ => rfl) e2 (by decide) (by decide)
    (by
      have h1 := hok.jalCert.align; have h2 := hok.jalCert.hi
      unfold Vsa.Sim.tohostAddr at h2
      have h3 : T.jal.pc + 4 < 2 ^ 64 := by omega
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3]; omega)
    (fun _ hr => by
      iintro ⟨Ha, ⟨Hb, Hr, Hs⟩, Hc⟩
      isplitr
      · ipureintro; exact hr
      simp only [List.cons_append, List.nil_append]
      rw [topErr_toNat, show (256#64 : BitVec 64).toNat = 256 from rfl]
      iframe Ha Hb Hr Hs Hc)
    (fun _ => by
      iintro ⟨Ha, Hb, Hr, Hs, Hc⟩
      rw [topErr_toNat, show (256#64 : BitVec 64).toNat = 256 from rfl]
      iframe Ha Hb Hr Hs Hc)
  iframe Hsn Hcode Hms Hst Hgp Himg Herr Hstd
  isplitl []
  · unfold readable
    isplitr
    · iapply binImg_rodata $$ Himg
    · iapply Oom.ownSet_none
  iintro %R2 %hk2 ⟨Herr, -, Hstd⟩ Hms Hst
  -- `li s5,1; j`, the epilogue, `ret` to `main`
  have e2' : upd R2 1 (BitVec.ofNat 64 (T.jal.pc + 4)) 2 = sFr := by
    rw [upd_other _ _ (by decide), hk2 2 (by decide) (by decide), e2]
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ [])
    (F := iprop(slot24 (sFr + 88#64).toNat ∗ stackScratch sFr (sFr.toNat - stackSL.lo) ∗
      cstrBuf (sTop.toNat + 496) 256 ∗ Stdio.stdioOwn ∗ Stdio.errnoOwn ∗ consoleOwn st.out ∗
      ownImg (InExt (sTop.toNat + 752, 16)) imgT ∗ gp ↦ᵣ□ Newlib.gpV ∗ binImg))
  rotate_left
  · iframe Hslot Hst Herr Hstd Herrno Hcon HT Hms Hgp Himg
    iapply codeRes_text $$ Hcode
  intro F'
  refine hS.tail e2' hf.ra ?_
  intro R3 f10 f1 f2 f8
  apply swp_closeF
  unfold F'
  iintro ⟨⟨Hslot, Hst, Herr, Hstd, Herrno, Hcon, HT, #Hgp, #Himg⟩, Hms⟩
  ihave ⟨%Mt', Hms⟩ := ms_unslot (S := InExt (sTop.toNat - 176, 176)) (a := sTop.toNat - 176 + 88)
    (fun b hb => by simp only [InExt] at hb ⊢; omega) $$ [Hms Hslot]
  · iframe Hms
    rw [show (sFr + 88#64).toNat = sTop.toNat - 176 + 88 from by decide]
    iexact Hslot
  ihave ⟨Hpc, Hra, Hregs, Hfr⟩ := ms_exit $$ Hms
  -- `main`'s stack: the frame and the stack below
  ihave ⟨-, Hst⟩ := stackScratch_narrow (s := sFr) (n := sFr.toNat - stackSL.lo) (m := 4096 - 176)
    (by decide) (by decide) $$ Hst
  have hu := stackScratch_unframe (GF := GF) (s := sTop) (f := 176#64) (n := fprintfNeed)
    (by decide) (by decide)
  rw [← sFr_eq, show fprintfNeed - (176#64 : BitVec 64).toNat = 4096 - 176 from rfl,
    show sFr.toNat = sTop.toNat - 176 from by decide,
    show (176#64 : BitVec 64).toNat = 176 from rfl] at hu
  ihave Hst := hu $$ [Hst Hfr]
  · iframe Hst
    unfold blockOwn
    iexact Hfr
  -- the registers
  ihave ⟨Hsp, Hcs, Htmp, Hargs⟩ := (regFile_newlib R3).1 $$ Hregs
  ihave ⟨Hs0, Hcs⟩ := (calleeSaved_split R3).1 $$ Hcs
  ihave ⟨Ha0, Hargs⟩ := (sepL_args_split R3).1 $$ Hargs
  ihave Htmp := clobbered_of_fn _ R3 $$ Htmp
  ihave Hargs := clobbered_of_fn _ R3 $$ Hargs
  unfold cstrBuf
  icases Herr with ⟨%eimg, Herr, %henul⟩
  rw [f10, f2, f8, hf.s0]
  iapply wp_mainErrTail H live hcl Wp sTop 1#64 (R3 1) R3 st.out imgT eimg mainSp_top (by decide)
    hT henul
  unfold callFrame
  rw [show List.drop 1 argRegs = [11, 12, 13, 14, 15, 16, 17] from rfl]
  iframe Hpc Ha0 Hra Hs0 Hargs Hsp Hst Hcs Htmp Hgp Himg HT Herr Hstd Herrno Hcon
  iintro %o'
  iapply hΦ

end Abrupt

/-! ## The abort -/

section Abort

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst VsaIris.Newlib
  Vsa.RuntimeRepr Vsa.Sim.LayoutInstance VsaIris.Newlib.MainErr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

theorem imgW_glue_in {S : Nat → Prop} {f g : Nat → BitVec 8} {a : Nat} (h : ∀ j, j < 8 → S (a + j)) :
    imgW (glue S f g) a = imgW f a :=
  imgW_agree fun j hj => by unfold glue; rw [ite_eq_left_of_eq_true _ _ (eq_true (h j hj))]

/-- The frame's image around the landing: the loop's tracking memory off the
result slot, the slot at any bytes. -/
theorem topLanding_of {Mt : Mem} {jb imgT f : Nat → BitVec 8} (hf : TopFrameP Mt)
    (hjb : JbTop jb sFr) (hT : imgW imgT (sTop.toNat + 760) = 0x80000038#64) :
    TopLanding inpTop sTop jb (glue (interpS sTop) (imgM Mt) f) imgT where
  main := mainSp_top
  inp_eq := by decide
  ra := hjb.ra
  sp := hjb.sp.trans sFr_eq
  inI := by
    rw [imgW_glue_in (fun j hj => by
      simp only [interpS, InExt, show (sTop - 176#64).toNat = sTop.toNat - 176 from by decide]
      omega), imgW_eq_ldv, show (sTop - 176#64).toNat = sTop.toNat - 176 from by decide, hf.inp]
    decide
  raI := by
    rw [imgW_glue_in (fun j hj => by
      simp only [interpS, InExt, show (sTop - 176#64).toNat = sTop.toNat - 176 from by decide]
      omega), imgW_eq_ldv, show (sTop - 176#64).toNat + 168 = (sFr + 168#64).toNat from by decide,
      hf.ra]
  s0I := by
    rw [imgW_glue_in (fun j hj => by
      simp only [interpS, InExt, show (sTop - 176#64).toNat = sTop.toNat - 176 from by decide]
      omega), imgW_eq_ldv, show (sTop - 176#64).toNat + 160 = (sFr + 160#64).toNat from by decide,
      hf.s0]
  raT := hT

/-- **An abort at the top**, for either WP: the loop's abort resource (the
landing or the out-of-memory `exit(1)`, over the stack below `interp_run`'s
frame, `hcore`), the frame at the loop's tracking memory and the result slot,
the `jmp_buf` `setjmp` wrote and `main`'s saved pair end the run with a
nonzero exit code (`Abort.wp_abort`). -/
theorem wp_topAbort (H : NewlibHoles) (hcl : CodeLive live) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} (hΦe : ∀ e o, e ≠ 0 → ⊢ Φ (e, o)) {Core : IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} (hEL : ErrnoOwn.ErrnoLend (GF := GF) L Room)
    (hcore : Core ⊢ abortCore N L Room inpTop sFr (sFr.toNat - stackSL.lo))
    {Mt : Mem} {jb imgT : Nat → BitVec 8} (hf : TopFrameP Mt) (hjb : JbTop jb sFr)
    (hT : imgW imgT (sTop.toNat + 760) = 0x80000038#64) :
    abortAt Core sFr (sFr.toNat - stackSL.lo) ∗ slot24 (sFr + 88#64).toNat ∗
      ownSet (interpS sTop) (fun a => a ↦ₘ imgM Mt a) ∗ jmpRO inpTop jb ∗
      ownImg (InExt (sTop.toNat + 752, 16)) imgT ∗ gp ↦ᵣ□ Newlib.gpV ∗ binImg
    ⊢ Wp.W Φ := by
  iintro ⟨HA, Hslot, HS, #Hjb, HT, #Hgp, #Himg⟩
  ihave ⟨HC, Hst⟩ := abortAt_elim _ _ _ $$ HA
  ihave HC := hcore $$ HC
  ihave HA := abortAt_intro _ _ _ $$ [HC Hst]
  · iframe HC Hst
  unfold slot24 blockOwn
  ihave ⟨%f, Hslot⟩ := ownSet_fn _ $$ Hslot
  ihave HI := ownSet_glue (interpS sTop) (InExt ((sFr + 88#64).toNat, 24)) (imgM Mt) f
    (fun a h1 h2 => by
      simp only [interpS, InExt, show (sFr + 88#64).toNat = sTop.toNat - 176 + 88 from by decide]
        at h1 h2
      omega) $$ [HS Hslot]
  · iframe HS Hslot
  ihave HI := ownSet_iff (T := InExt ((sTop - 176#64).toNat, 176)) _ (fun a => by
    simp only [interpS, InExt, show (sFr + 88#64).toNat = sTop.toNat - 176 + 88 from by decide,
      show (sTop - 176#64).toNat = sTop.toNat - 176 from by decide]
    omega) $$ HI
  rw [sFr_eq] at *
  iapply wp_abort N L Room inpTop H hEL live hcl Wp hΦe sTop (sTop.toNat - 176 - stackSL.lo) (by decide)
    (by decide) jb (glue (interpS sTop) (imgM Mt) f) imgT (topLanding_of hf hjb hT)
  unfold abortRes
  rw [show (sTop - 176#64).toNat - stackSL.lo = sTop.toNat - 176 - stackSL.lo from by decide] at *
  isplitl [HA]
  · iexact HA
  isplitr
  · iexact Hjb
  isplitl [HI]
  · iexact HI
  isplitl [HT]
  · iexact HT
  isplitr
  · iexact Hgp
  · iexact Himg

end Abort

/-! ## `interp_run`'s whole run, partial mode -/

section Run

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst VsaIris.Newlib
  Vsa.RuntimeRepr Vsa.Sim.LayoutInstance VsaIris.VsaHeap VsaIris.Newlib.TopAbrupt

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

omit I in
/-- The error context of the partial specs, from the `jmp_buf` `setjmp` wrote. -/
theorem errCtx_of_jb {jb : Nat → BitVec 8} (hjb : JbTop jb sFr) :
    binImg (GF := GF) ∗ jmpRO inpTop jb ⊢ errCtx inpTop := by
  unfold errCtx
  iintro ⟨#Hb, #Hj⟩
  iframe Hb
  iexists jb
  iframe Hj
  ipureintro; rw [hjb.ra]; decide

/-- The landing core of the partial specs is the top's abort core: the stack
segment below `interp_run`'s frame. -/
theorem evalCore_top (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) :
    evalCore (GF := GF) N L Room inpTop ⊢ abortCore N L Room inpTop sFr (sFr.toNat - stackSL.lo) := by
  unfold evalCore
  rw [show runSp = sFr from by decide]
  exact .rfl

/-- **`interp_run`'s whole run, partial mode** (INTERP_DESIGN.md §4.4, §5.3):
from `interp_run`'s entry (`topPre` uncounted, `main`'s `s0` at
`&_impure_ptr`) and the partial statement specs under the error context
`setjmp` establishes, at the landing core `evalCore` (the stack below
`interp_run`'s frame): every halt is either code 0 after a normal completion
of the program (`hΦ0`, with its `ExecSeq`) or a nonzero code (`hΦe`:
`exit(70)` after a top-level `return`/`break`/`continue` or a runtime error,
`exit(1)` out of memory). The loop is `SeqLoopInterp.interpSeqP_all`. -/
theorem interpRun_partial (H : NewlibHoles) (hlive : ∀ p ∈ interpText, live p.1)
    (hcl : CodeLive live) {N : NativeAddrs} {m : Mem} {P : Nat → Prop}
    {stmts count : Nat} {p : Program} {g : Nat} {R0 : Nat → BitVec 64}
    {Φ : Nat × String → IProp GF} (hE : TopEntry m P stmts count p g R0)
    (hs0 : R0 8 = 0x8001b970#64)
    (hspecs : errCtx (GF := GF) inpTop ⊢
      execSpecsP (vsaModel live) N vsaLayoutP vsaRoomB inpTop (evalCore N vsaLayoutP vsaRoomB inpTop))
    (hΦ0 : ∀ st', ExecSeq initSt 0 0 p st' .normal → ⊢ Φ (0, st'.out))
    (hΦe : ∀ e o, e ≠ 0 → ⊢ Φ (e, o)) :
    topPre (GF := GF) N .uncounted m P g R0 ⊢ (wpW (GF := GF) (vsaModel live)).W Φ := by
  have hloop := interpSeqP_all (GF := GF) hlive (N := N)
    (by iintro %q; iapply valueNull_spec hlive (wpW (GF := GF) (vsaModel live)) N q)
    vsaLayoutP vsaRoomB inpTop (evalCore N vsaLayoutP vsaRoomB inpTop) 0 0 p
  iapply wp_topPrologue H hlive hcl (wpW (GF := GF) (vsaModel live)) hE ?_ ?_
  · intro h0
    have hp : p = [] := List.eq_nil_of_length_eq_zero ((topCount hE).trans h0)
    subst hp
    exact hΦ0 initSt (.nil initSt 0 0)
  · intro hpos R Mt hf
    have hp : p ≠ [] := by
      intro e; subst e; have := topCount hE; simp at this; omega
    have hfp : TopFrameP Mt := ⟨hf.frame.inp, hf.ra, hf.s0.trans hs0⟩
    have hT := imgW_mainRa hE.mainRa
    have hK := hloop Φ initSt 0 count sTop (BitVec.ofNat 64 stmts)
      (BitVec.ofNat 64 g) R Mt m m P p (sFr.toNat - stackSL.lo) emp hp (List.drop_zero (l := p)).symm
      (topData hE) hf.head topFrameGeom hf.frame topStackGeom (topNeeds hE) topSlotGeom
    rw [stmts_toNat hE, g_toNat hE] at hK
    unfold topLoopRes
    iintro ⟨Hms, Hslot, #Hcode, #Himg, #Hro, #Hdv, #Hfr, Hst, Hw, HT, ⟨%jb, %hjb, #Hjb⟩⟩
    ihave #Hctx := errCtx_of_jb hjb $$ [Himg Hjb]
    · iframe Himg Hjb
    ihave #Hspec := hspecs $$ Hctx
    ihave #Hgp := codeRes_gp $$ Hcode
    iapply hK
    iframe Hms Hcode Hro Hdv Hfr Hst Hw Hspec
    isplitl [Hslot]
    · iexact Hslot
    isplit
    · -- the loop's exits by status
      iintro %R' %st' %status %hE' %⟨hkeep, hs1⟩ - Hms Hst Hret Hw
      have h2 : R' 2 = sFr := (hkeep 2 (by decide)).trans hf.head.sp
      cases status with
      | normal =>
        have h21 : R' 21 = 0#64 := (hkeep 21 (by decide)).trans hf.s5
        rw [interpExit_normal]
        ihave HΦ := hΦ0 st' hE'
        iapply wp_topNormal H hlive hcl (wpW (GF := GF) (vsaModel live)) ErrnoOwn.errnoLend_vsa h2 h21 hf.ra hT
        iframe Hcode Hms Hw HT HΦ
      | ret v =>
        rw [interpExit_ret]
        simp only [statusRet]
        ihave Hret := valAt_slot $$ Hret
        iapply wp_topAbrupt H hcl ErrnoOwn.errnoLend_vsa (wpW (GF := GF) (vsaModel live)) topRet_ok (topRet_runs hlive)
          (fun o => hΦe 70 o (by decide)) h2 (hs1 (by simp)) hfp hT
        iframe Hcode Hms Hret Hst Hw HT
      | brk =>
        rw [interpExit_brk]
        simp only [statusRet]
        iapply wp_topAbrupt H hcl ErrnoOwn.errnoLend_vsa (wpW (GF := GF) (vsaModel live)) topBrk_ok (topBrk_runs hlive)
          (fun o => hΦe 70 o (by decide)) h2 (hs1 (by simp)) hfp hT
        iframe Hcode Hms Hret Hst Hw HT
      | cont =>
        rw [interpExit_cont]
        simp only [statusRet]
        iapply wp_topAbrupt H hcl ErrnoOwn.errnoLend_vsa (wpW (GF := GF) (vsaModel live)) topBrk_ok (topBrk_runs hlive)
          (fun o => hΦe 70 o (by decide)) h2 (hs1 (by simp)) hfp hT
        iframe Hcode Hms Hret Hst Hw HT
    · -- an abort
      iintro ⟨HA, Hslot, HS⟩
      iapply wp_topAbort H hcl (wpW (GF := GF) (vsaModel live)) hΦe ErrnoOwn.errnoLend_vsa (evalCore_top N vsaLayoutP vsaRoomB)
        hfp hjb hT
      iframe HA Hslot HS Hjb HT Hgp Himg

/-- **`interp_run`'s whole run from the boundary, partial mode**: `bootRes`
uncounted, the entry registers (`main`'s `s0` at `&_impure_ptr`) and the
code. -/
theorem interpRun_partial_boot (H : NewlibHoles) (hlive : ∀ p ∈ interpText, live p.1)
    (hcl : CodeLive live) {c : Vsa.Machine.Config} {p : Program} (b : Boot c p)
    {R0 : Nat → BitVec 64} (hR : TopRegs R0 b.stmts b.count) (hs0 : R0 8 = 0x8001b970#64)
    {Φ : Nat × String → IProp GF}
    (hspecs : errCtx (GF := GF) inpTop ⊢
      execSpecsP (vsaModel live) b.N vsaLayoutP vsaRoomB inpTop (evalCore b.N vsaLayoutP vsaRoomB inpTop))
    (hΦ0 : ∀ st', ExecSeq initSt 0 0 p st' .normal → ⊢ Φ (0, st'.out))
    (hΦe : ∀ e o, e ≠ 0 → ⊢ Φ (e, o)) :
    bootRes b .uncounted ∗ PC ↦ᵣ 0x800043ec#64 ∗ ra ↦ᵣ 0x800045ec#64 ∗ regFile R0 ∗ codeRes ⊢
      (wpW (GF := GF) (vsaModel live)).W Φ :=
  (topPre_of_bootRes b _ R0).trans
    (interpRun_partial H hlive hcl (topEntry_of_boot b hR) hs0 hspecs hΦ0 hΦe)

end Run

end VsaIris.Interp

#print axioms VsaIris.Interp.wp_topAbrupt
#print axioms VsaIris.Interp.topRet_runs
#print axioms VsaIris.Interp.topBrk_runs
#print axioms VsaIris.Interp.evalCore_top
#print axioms VsaIris.Interp.interpRun_partial
#print axioms VsaIris.Interp.interpRun_partial_boot
