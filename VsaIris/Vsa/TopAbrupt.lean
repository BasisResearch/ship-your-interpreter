import VsaIris.Vsa.Landing
import VsaIris.Vsa.Oom

/-!
# `interp_run`'s top-level `return` / `break` / `continue` (H5)

A top-level statement that finishes with status 3 (`return`) or 1/2
(`break`/`continue`) makes `interp_run` format an error into `err_msg` and
return 1; `main` then prints it and exits 70 (`Landing.wp_interpRet1`).

```
h+0:  ld a5,0(sp)          in
h+4:  lw a3,4(s1)          s->line
h+8:  auipc a2; addi a2    fmt
h+16: addi a0,a5,224       in->err_msg
h+20: li a1,256
h+24: jal snprintf         IrisHoles.newlib.snprintf
h+28: li s5,1
h+32: j 80004514           interp_run's epilogue
```

`h = 0x80004540` (`"… 'return' outside of a function"`) and
`h = 0x80004564` (`"… 'break'/'continue' outside of a loop"`). One
descriptor `TopSite` with its decided facts `TopSite.OK` gives
`wp_topAbrupt`; the two instances are `topRet_ok` and `topBrk_ok`.
-/

namespace VsaIris.Newlib.TopAbrupt

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Sim VsaIris.Inst VsaIris.Interp VsaIris.Stdio VsaIris.Newlib.Sites VsaIris.Newlib.Exit
  VsaIris.Newlib.MainErr VsaIris.Newlib.Landing

/-! ## The descriptor -/

/-- A top-level status block: its head, format, the staging before
`jal snprintf`, the `jal`, and `li s5,1; j` to the epilogue. -/
structure TopSite where
  head : Nat
  fmt : BitVec 64
  fmtBytes : List (BitVec 8)
  seg : List BBlock
  jal : JalSite
  tl : List BBlock

abbrev tL (a5v a3v a2v a0v a1v sI st : BitVec 64) : GRegs :=
  [(15, a5v), (13, a3v), (12, a2v), (10, a0v), (11, a1v), (2, sI), (9, st)]

abbrev tLds (sI st : BitVec 64) (imgI lineI : Nat → BitVec 8) : List (List (BitVec 8)) :=
  [imgWord imgI sI.toNat, imgWord4 lineI (st.toNat + 4)]

/-- The statement's `line` field, as `lw` loads it. -/
abbrev lineV (st : BitVec 64) (lineI : Nat → BitVec 8) : BitVec 64 :=
  bytesVal .lw (imgWord4 lineI (st.toNat + 4))

/-- The statement node's `line` word in RAM, off the HTIF words. -/
structure LineGeom (st : BitVec 64) : Prop where
  lo : 0x80000000 ≤ st.toNat
  hi : st.toNat + 8 ≤ 0x100000000
  win : st.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ st.toNat + 4

/-- The decided facts about a top-level status block. -/
structure TopSite.OK (T : TopSite) : Prop where
  len : evalBlocksFuel T.seg = 5 + 1
  wf : ChainOK (BitVec.ofNat 64 T.head) [15, 13, 12, 10, 11, 2, 9] T.seg
  keys : KeysOK [15, 13, 12, 10, 11, 2, 9]
  wr : ∀ k ∈ wrChain T.seg, k ∈ [15, 13, 12, 10, 11, 2, 9]
  log : ∀ (a5v a3v a2v a0v a1v sI st : BitVec 64) (imgI lineI : Nat → BitVec 8),
    (segOut T.seg (tL a5v a3v a2v a0v a1v sI st) (tLds sI st imgI lineI)).log = []
  facts : ∀ (m : Std.ExtHashMap Nat (BitVec 8)) (a5v a3v a2v a0v a1v sI st : BitVec 64)
    (imgI lineI : Nat → BitVec 8), topCodeLoaded m → FrameI sI → LineGeom st →
    (∀ k, sI.toNat ≤ k → k < sI.toNat + 176 → (m[k]?).getD 0 = imgI k) →
    (∀ k, k < 4 → (m[st.toNat + 4 + k]?).getD 0 = lineI (st.toNat + 4 + k)) →
    ChainFacts m m (tL a5v a3v a2v a0v a1v sI st) (tLds sI st imgI lineI) T.seg
  pc : ∀ (a5v a3v a2v a0v a1v sI st : BitVec 64) (imgI lineI : Nat → BitVec 8),
    evalBlocksPC (BitVec.ofNat 64 T.head)
      (SegEvalState.init (tL a5v a3v a2v a0v a1v sI st) (tLds sI st imgI lineI)) T.seg =
      BitVec.ofNat 64 T.jal.pc
  fin : ∀ (a5v a3v a2v a0v a1v sI st : BitVec 64) (imgI lineI : Nat → BitVec 8),
    finReg T.seg (tL a5v a3v a2v a0v a1v sI st) (tLds sI st imgI lineI) 15 = imgW imgI sI.toNat ∧
    finReg T.seg (tL a5v a3v a2v a0v a1v sI st) (tLds sI st imgI lineI) 13 = lineV st lineI ∧
    finReg T.seg (tL a5v a3v a2v a0v a1v sI st) (tLds sI st imgI lineI) 12 = T.fmt ∧
    finReg T.seg (tL a5v a3v a2v a0v a1v sI st) (tLds sI st imgI lineI) 10 =
      imgW imgI sI.toNat + 224#64 ∧
    finReg T.seg (tL a5v a3v a2v a0v a1v sI st) (tLds sI st imgI lineI) 11 = 256#64 ∧
    finReg T.seg (tL a5v a3v a2v a0v a1v sI st) (tLds sI st imgI lineI) 2 = sI ∧
    finReg T.seg (tL a5v a3v a2v a0v a1v sI st) (tLds sI st imgI lineI) 9 = st
  jalCert : T.jal.Cert
  jalTgt : T.jal.tgt = snprintfEntry
  jalText : TextAt T.jal.pc T.jal.code
  tlLen : evalBlocksFuel T.tl = 1 + 1
  tlWf : ChainOK (BitVec.ofNat 64 (T.jal.pc + 4)) [21] T.tl
  tlWr : ∀ k ∈ wrChain T.tl, k ∈ [21]
  tlLog : ∀ v : BitVec 64, (segOut T.tl [(21, v)] []).log = []
  tlFacts : ∀ (m : Std.ExtHashMap Nat (BitVec 8)) (v : BitVec 64), topCodeLoaded m →
    ChainFacts m m [(21, v)] [] T.tl
  tlPc : ∀ v : BitVec 64, evalBlocksPC (BitVec.ofNat 64 (T.jal.pc + 4))
    (SegEvalState.init [(21, v)] []) T.tl = 0x80004514#64
  tlFin : ∀ v : BitVec 64, finReg T.tl [(21, v)] [] 21 = 1#64
  fmtText : ∀ i (h : i < T.fmtBytes.length), rodataDom (T.fmt.toNat + i) ∧
    rodataByte (T.fmt.toNat + i) = T.fmtBytes[i] ∧ T.fmtBytes[i] ≠ 0
  fmtNul : rodataDom (T.fmt.toNat + T.fmtBytes.length) ∧
    rodataByte (T.fmt.toNat + T.fmtBytes.length) = 0
  fmtParse : parseFmt T.fmtBytes = some [.int]

/-! ## Memory facts shared by both instances -/

/-- `lw a3,4(s1)`: the statement's `line`. -/
theorem lineLw {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr}
    {lineI : Nat → BitVec 8} {st : BitVec 64} (hk : a.kind = .lw)
    (hea : eaddrM a L = st + sign_extend (m := 64) (0x004#12)) (hg : LineGeom st)
    (hpin : ∀ k, k < 4 → (m[st.toNat + 4 + k]?).getD 0 = lineI (st.toNat + 4 + k)) :
    MemFacts m L (imgWord4 lineI (st.toNat + 4)) a := by
  have h1 := hg.lo; have h2 := hg.hi; have h3 := hg.win
  exact lwFact hk (by rw [hea]; exact addr_off st _ 4 (by decide) (by omega)) (by omega)
    (by omega) (by omega) hpin

theorem fmt_ok {T : TopSite} (hT : T.OK) (lv : BitVec 64) :
    FmtArgsOK (fun a => rodataDom a ∨ False) rodataByte T.fmt [lv] := by
  refine ⟨T.fmtBytes, [.int], ⟨cstrCov_rodata (fun a ha => ⟨.inl ha, rfl⟩) hT.fmtText hT.fmtNul,
    hT.fmtParse, by simp, ?_⟩⟩
  intro i hi hs
  have : i = 0 := by simpa using hi
  subst this
  simp at hs

/-! ## The two blocks -/

#derive_case topRetSeg chain
  [(0x80004540#64, 0x00013783#32),
   (0x80004544#64, 0x0044a683#32),
   (0x80004548#64, 0x00015617#32),
   (0x8000454c#64, 0x00860613#32),
   (0x80004550#64, 0x0e078513#32),
   (0x80004554#64, 0x10000593#32)]

#derive_case topRetTl chain
  [(0x8000455c#64, 0x00100a93#32)] terminator ⟨0x80004560#64, 0xfb5ff06f#32, 0x6f#8, 0xf0#8,
      0x5f#8, 0xfb#8, .j, 0, 0, 0#13, 0x1fffb4#21, 0#12⟩

#derive_case topBrkSeg chain
  [(0x80004564#64, 0x00013783#32),
   (0x80004568#64, 0x0044a683#32),
   (0x8000456c#64, 0x00015617#32),
   (0x80004570#64, 0x01c60613#32),
   (0x80004574#64, 0x0e078513#32),
   (0x80004578#64, 0x10000593#32)]

#derive_case topBrkTl chain
  [(0x80004580#64, 0x00100a93#32)] terminator ⟨0x80004584#64, 0xf91ff06f#32, 0x6f#8, 0xf0#8,
      0x1f#8, 0xf9#8, .j, 0, 0, 0#13, 0x1fff90#21, 0#12⟩

/-- `"runtime error [line %d]: 'return' outside of a function"`. -/
def topRetFmtBytes : List (BitVec 8) := [0x72#8, 0x75#8, 0x6e#8, 0x74#8, 0x69#8, 0x6d#8, 0x65#8, 0x20#8, 0x65#8, 0x72#8, 0x72#8, 0x6f#8, 0x72#8, 0x20#8, 0x5b#8, 0x6c#8, 0x69#8, 0x6e#8, 0x65#8, 0x20#8, 0x25#8, 0x64#8, 0x5d#8, 0x3a#8, 0x20#8, 0x27#8, 0x72#8, 0x65#8, 0x74#8, 0x75#8, 0x72#8, 0x6e#8, 0x27#8, 0x20#8, 0x6f#8, 0x75#8, 0x74#8, 0x73#8, 0x69#8, 0x64#8, 0x65#8, 0x20#8, 0x6f#8, 0x66#8, 0x20#8, 0x61#8, 0x20#8, 0x66#8, 0x75#8, 0x6e#8, 0x63#8, 0x74#8, 0x69#8, 0x6f#8, 0x6e#8]

/-- `"runtime error [line %d]: 'break'/'continue' outside of a loop"`. -/
def topBrkFmtBytes : List (BitVec 8) := [0x72#8, 0x75#8, 0x6e#8, 0x74#8, 0x69#8, 0x6d#8, 0x65#8, 0x20#8, 0x65#8, 0x72#8, 0x72#8, 0x6f#8, 0x72#8, 0x20#8, 0x5b#8, 0x6c#8, 0x69#8, 0x6e#8, 0x65#8, 0x20#8, 0x25#8, 0x64#8, 0x5d#8, 0x3a#8, 0x20#8, 0x27#8, 0x62#8, 0x72#8, 0x65#8, 0x61#8, 0x6b#8, 0x27#8, 0x2f#8, 0x27#8, 0x63#8, 0x6f#8, 0x6e#8, 0x74#8, 0x69#8, 0x6e#8, 0x75#8, 0x65#8, 0x27#8, 0x20#8, 0x6f#8, 0x75#8, 0x74#8, 0x73#8, 0x69#8, 0x64#8, 0x65#8, 0x20#8, 0x6f#8, 0x66#8, 0x20#8, 0x61#8, 0x20#8, 0x6c#8, 0x6f#8, 0x6f#8, 0x70#8]

def topRet : TopSite where
  head := 0x80004540
  fmt := 0x80019550#64
  fmtBytes := topRetFmtBytes
  seg := topRetSeg
  jal := topJalRet
  tl := topRetTl

def topBrk : TopSite where
  head := 0x80004564
  fmt := 0x80019588#64
  fmtBytes := topBrkFmtBytes
  seg := topBrkSeg
  jal := topJalBrk
  tl := topBrkTl

theorem topRet_ok : topRet.OK where
  len := by decide
  wf := by decide
  keys := by decide
  wr := by decide
  log _ _ _ _ _ _ _ _ _ := rfl
  facts m a5v a3v a2v a0v a1v sI st imgI lineI hcode hg hst hpinI hpinL := by
    show ChainFacts m m _ _ topRetSeg
    unfold topRetSeg ChainFacts
    chain_facts hcode with "VsaIris.Newlib.Sites.topCode_at_"
    · exact frameLd (off := 0) rfl rfl (by decide) (by decide) hg hpinI
    · exact lineLw rfl rfl hst hpinL
  pc _ _ _ _ _ _ _ _ _ := rfl
  fin a5v a3v a2v a0v a1v sI st imgI lineI := by
    refine ⟨?_, rfl, rfl, ?_, rfl, rfl, rfl⟩
    · show bytesVal .ld (imgWord imgI sI.toNat) = _; rw [bytesVal_imgWord]
    · show bytesVal .ld (imgWord imgI sI.toNat) + sign_extend (m := 64) (0x0e0#12) = _
      rw [bytesVal_imgWord]; rfl
  jalCert := topJalRet_cert
  jalTgt := rfl
  jalText := by decide
  tlLen := by decide
  tlWf := by decide
  tlWr := by decide
  tlLog _ := rfl
  tlFacts m v hcode := by
    show ChainFacts m m _ _ topRetTl
    unfold topRetTl ChainFacts
    chain_facts hcode with "VsaIris.Newlib.Sites.topCode_at_"
  tlPc _ := rfl
  tlFin _ := rfl
  fmtText := by decide +kernel
  fmtNul := by decide +kernel
  fmtParse := by decide +kernel

theorem topBrk_ok : topBrk.OK where
  len := by decide
  wf := by decide
  keys := by decide
  wr := by decide
  log _ _ _ _ _ _ _ _ _ := rfl
  facts m a5v a3v a2v a0v a1v sI st imgI lineI hcode hg hst hpinI hpinL := by
    show ChainFacts m m _ _ topBrkSeg
    unfold topBrkSeg ChainFacts
    chain_facts hcode with "VsaIris.Newlib.Sites.topCode_at_"
    · exact frameLd (off := 0) rfl rfl (by decide) (by decide) hg hpinI
    · exact lineLw rfl rfl hst hpinL
  pc _ _ _ _ _ _ _ _ _ := rfl
  fin a5v a3v a2v a0v a1v sI st imgI lineI := by
    refine ⟨?_, rfl, rfl, ?_, rfl, rfl, rfl⟩
    · show bytesVal .ld (imgWord imgI sI.toNat) = _; rw [bytesVal_imgWord]
    · show bytesVal .ld (imgWord imgI sI.toNat) + sign_extend (m := 64) (0x0e0#12) = _
      rw [bytesVal_imgWord]; rfl
  jalCert := topJalBrk_cert
  jalTgt := rfl
  jalText := by decide
  tlLen := by decide
  tlWf := by decide
  tlWr := by decide
  tlLog _ := rfl
  tlFacts m v hcode := by
    show ChainFacts m m _ _ topBrkTl
    unfold topBrkTl ChainFacts
    chain_facts hcode with "VsaIris.Newlib.Sites.topCode_at_"
  tlPc _ := rfl
  tlFin _ := rfl
  fmtText := by decide +kernel
  fmtNul := by decide +kernel
  fmtParse := by decide +kernel

/-! ## The rule -/

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem calleeSaved_eq : calleeSaved = [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := rfl

/-- The staging's argument registers back into `snprintf`'s `argsAt` tail. -/
theorem put15 :
    (∃ v, (15 : Nat) ↦ᵣ v) ∗ clobbered (GF := GF)
      (((((argRegs.erase 15).erase 13).erase 12).erase 10).erase 11) ⊢
      clobbered (argRegs.drop 4) :=
  clobbered_put (r := 15) (rs := argRegs.drop 4) (by decide)

/-- **A top-level `return`/`break`/`continue`, then `exit(70)`**, for either
WP. At the block's head with `sp` at `interp_run`'s frame `sM - 176`
(holding `in = sM + 272`, `main`'s link and `main`'s `s0`), `s1` the
statement (its `line` word read-only), `err_msg`, the stack below, `main`'s
saved pair and newlib's data: `snprintf` formats the message into `err_msg`,
`interp_run` returns 1 and the run halts with code 70. -/
theorem wp_topAbrupt {Ierr : (Nat → BitVec 8) → Prop} (H : NewlibHolesAt Ierr) {T : TopSite}
    (hT : T.OK) (live : Nat → Prop) (hlive : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF} (sM rv : BitVec 64)
    (cs : Nat → BitVec 64) (o : String) (imgI imgT lineI : Nat → BitVec 8) (hsM : MainSp sM)
    (hst : LineGeom (cs 9)) (hinp : imgW imgI (sM - 176#64).toNat = sM + 272#64)
    (hraI : imgW imgI ((sM - 176#64).toNat + 168) = 0x800045ec#64)
    (hs0I : imgW imgI ((sM - 176#64).toNat + 160) = 0x8001b970#64)
    (hra : imgW imgT (sM.toNat + 760) = 0x80000038#64) :
    PC ↦ᵣ BitVec.ofNat 64 T.head ∗ ra ↦ᵣ rv ∗ sp ↦ᵣ (sM - 176#64) ∗
      sepL calleeSaved (fun r => r ↦ᵣ cs r) ∗ clobbered argRegs ∗ clobbered tmpRegs ∗
      gp ↦ᵣ□ gpV ∗ binImg ∗ ownImg (InExt ((sM - 176#64).toNat, 176)) imgI ∗
      roImg (InExt ((cs 9).toNat + 4, 4)) lineI ∗
      stackScratch (sM - 176#64) (fprintfNeed - 176) ∗
      ownImg (InExt (sM.toNat + 752, 16)) imgT ∗ blockOwn (sM.toNat + 496) 256 ∗
      stdioOwn ∗ consoleOwn o ∗ (∀ o', Φ (70, o ++ o'))
    ⊢ Wp.W Φ := by
  have h1 := hsM.lo; have h2 := hsM.hi; have h3 := hsM.align
  unfold fprintfNeed tohostAddr at h1
  have hsI : (sM - 176#64).toNat = sM.toNat - 176 := toNat_sub_frame (by simp; omega)
  have hg : FrameI (sM - 176#64) := ⟨by rw [hsI]; unfold tohostAddr; omega, by rw [hsI]; omega,
    by rw [hsI]; omega⟩
  have hdst : (imgW imgI (sM - 176#64).toNat + 224#64).toNat = sM.toNat + 496 := by
    rw [hinp, BitVec.add_assoc, show (272#64 + 224#64 : BitVec 64) = 496#64 from rfl,
      BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat]
    omega
  have hl1 := hst.lo; have hl2 := hst.hi
  have hcodeL := topCode_text.live hlive
  unfold VsaIris.sp VsaIris.ra
  rw [calleeSaved_eq]
  simp only [sepL_cons, sepL_nil]
  iintro ⟨Hpc, Hra, Hsp, ⟨H8, H9, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, -⟩, Hargs,
    Htmp, #Hgp, #Himg, HI, #Hline, Hscr, HT, Herr, Hstd, Hcon, HΦ⟩
  ihave #Hcode := instrAt_of_binImg topCode_text $$ Himg
  ihave ⟨⟨%a5v, Ha5⟩, Hargs⟩ := clobbered_take (r := 15) (by decide) $$ Hargs
  ihave ⟨⟨%a3v, Ha3⟩, Hargs⟩ := clobbered_take (r := 13) (by decide) $$ Hargs
  ihave ⟨⟨%a2v, Ha2⟩, Hargs⟩ := clobbered_take (r := 12) (by decide) $$ Hargs
  ihave ⟨⟨%a0v, Ha0⟩, Hargs⟩ := clobbered_take (r := 10) (by decide) $$ Hargs
  ihave ⟨⟨%a1v, Ha1⟩, Hargs⟩ := clobbered_take (r := 11) (by decide) $$ Hargs
  ihave HI := (ownImg_range _ _ _).1 $$ HI
  ihave #Hlf := roImg_foot (InExt ((cs 9).toNat + 4, 4)) lineI
    (List.range' ((cs 9).toNat + 4) 4) (fun a ha => by
      rw [List.mem_range'] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact ⟨by omega, by omega⟩) $$ Hline
  -- `ld a5,0(sp); lw a3,4(s1); la a2,fmt; addi a0,a5,224; li a1,256`
  iapply wp_segW live Wp T.seg (tL a5v a3v a2v a0v a1v (sM - 176#64) (cs 9))
    (tLds (sM - 176#64) (cs 9) imgI lineI) (BitVec.ofNat 64 T.head)
    (codeFoot topCodeBase topCode ++ imgFoot (sM - 176#64).toNat 176 imgI ++
      (List.range' ((cs 9).toNat + 4) 4).map (fun a => (a, Iris.DFrac.discard, lineI a)))
    [] 5 hT.len hT.wf hT.keys hT.wr (fun a _ => by rw [hT.log]; trivial)
    (fun c hok ⟨_, hMR, _, _⟩ => hT.facts _ _ _ _ _ _ _ _ _ _
      (topCodeLoaded_of (code_present hok _
        (fun q hq => hMR q (List.mem_append_left _ (List.mem_append_left _ hq))) hcodeL)) hg hst
      (imgFoot_pin hMR (fun q hq => List.mem_append_left _ (List.mem_append_right _ hq)))
      (fun k hk => hMR ((cs 9).toNat + 4 + k, Iris.DFrac.discard, lineI ((cs 9).toNat + 4 + k))
        (List.mem_append_right _ (List.mem_map.mpr ⟨(cs 9).toNat + 4 + k, by
          rw [List.mem_range']; exact ⟨k, hk, by omega⟩, rfl⟩))))
  have hpcA := hT.pc a5v a3v a2v a0v a1v (sM - 176#64) (cs 9) imgI lineI
  obtain ⟨f15, f13, f12, f10, f11, f2, f9⟩ := hT.fin a5v a3v a2v a0v a1v (sM - 176#64) (cs 9) imgI lineI
  simp only [tL] at hpcA f15 f13 f12 f10 f11 f2 f9
  simp only [tL, sepL_cons, sepL_nil, hpcA, f15, f13, f12, f10, f11, f2, f9]
  iframe Hpc Ha5 Ha3 Ha2 Ha0 Ha1 Hsp H9
  isplitr
  · iempintro
  isplitl [HI]
  · iapply (sepL_append _ _ _).2
    isplitl [HI]
    · iapply (sepL_append _ _ _).2
      isplitr
      · rw [← instrAt_eq]; iexact Hcode
      iexact HI
    iexact Hlf
  iintro Hpc ⟨Ha5, Ha3, Ha2, Ha0, Ha1, Hsp, H9, -⟩ - HMR
  ihave ⟨HAB, -⟩ := (sepL_append _ _ _).1 $$ HMR
  ihave ⟨-, HI⟩ := (sepL_append _ _ _).1 $$ HAB
  ihave HI := (ownImg_range _ _ _).2 $$ HI
  -- `snprintf(in->err_msg, 256, fmt, s->line)`
  have hsp1 : SpIn (sM - 176#64) snprintfNeed :=
    ⟨by rw [hsI]; unfold snprintfNeed tohostAddr; omega, by rw [hsI]; omega, by rw [hsI]; omega⟩
  have hf := H.snprintf live Wp (sM - 176#64) (imgW imgI (sM - 176#64).toNat + 224#64) 256#64
    T.fmt [lineV (cs 9) lineI] cs rodataDom (fun _ => False) rodataByte hlive (by simp)
    (by decide) (by decide) (fmt_ok hT _) hsp1
  unfold snprintfSpec at hf
  have hj : JalExec (vsaModel live) T.jal.pc T.jal.code snprintfEntry := by
    have := JalSite.exec hT.jalCert live (hT.jalText.live hlive)
    rwa [hT.jalTgt] at this
  ihave #Hjal := instrAt_of_binImg hT.jalText $$ Himg
  ihave #Hf := hf
  ihave ⟨Hslack, Hscr⟩ := stackScratch_narrow (s := sM - 176#64) (n := fprintfNeed - 176)
    (m := snprintfNeed) (by rw [hsI]; unfold fprintfNeed; omega)
    (by unfold fprintfNeed snprintfNeed; omega) $$ Hscr
  iapply wp_callW Wp (v := rv) hj
  iframe Hjal Hf
  unfold VsaIris.ra
  iframe Hpc Hra
  isplitl [Ha0 Ha1 Ha2 Ha3 Ha5 Hargs Herr Hstd Hsp Hscr H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26
    H27 Htmp]
  · unfold argsAt callFrame VsaIris.sp readable
    rw [calleeSaved_eq]
    simp only [List.cons_append, List.nil_append, List.zipIdx_cons, List.zipIdx_nil, sepL_cons,
      sepL_nil, List.length_cons, List.length_nil, Nat.add_zero, Nat.reduceAdd]
    rw [hdst, show (256#64 : BitVec 64).toNat = 256 from rfl]
    iframe Ha0 Ha1 Ha2 Ha3 Herr Hstd Hsp Hscr Htmp Hgp Himg
    iframe H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27
    isplitl [Ha5 Hargs]
    · iapply put15
      isplitl [Ha5]
      · iexists _; iexact Ha5
      iexact Hargs
    isplitr
    · iapply binImg_rodata $$ Himg
    · iapply Oom.ownSet_none
  unfold callFrame VsaIris.sp readable cstrBuf
  rw [calleeSaved_eq, hdst, show (256#64 : BitVec 64).toNat = 256 from rfl]
  simp only [sepL_cons, sepL_nil]
  iintro Hpc Hra ⟨Hargs, ⟨%eimg, Herr, %henul⟩, -, Hstd, ⟨Hsp, Hscr, ⟨H8, H9, H18, H19, H20, H21,
    H22, H23, H24, H25, H26, H27, -⟩, Htmp, -, -⟩⟩
  -- `li s5,1; j 80004514`
  iapply wp_segW live Wp T.tl [(21, cs 21)] [] (BitVec.ofNat 64 (T.jal.pc + 4))
    (codeFoot topCodeBase topCode) [] 1 hT.tlLen hT.tlWf (by change KeysOK [21]; decide)
    hT.tlWr (fun a _ => by rw [hT.tlLog]; trivial)
    (fun c hok ⟨_, hMR, _, _⟩ => hT.tlFacts _ _ (topCodeLoaded_of (code_present hok _ hMR hcodeL)))
  simp only [sepL_cons, sepL_nil, hT.tlPc, hT.tlFin]
  rw [← instrAt_eq]
  iframe Hpc H21
  isplitr
  · iempintro
  isplitr
  · iexact Hcode
  iintro Hpc ⟨H21, -⟩ - -
  -- `interp_run` returns 1, `main` exits 70
  ihave ⟨⟨%r0, Ha0⟩, Hargs⟩ := clobbered_take (r := 10) (by decide) $$ Hargs
  ihave Hscr := stackScratch_widen (s := sM - 176#64) (n := fprintfNeed - 176)
    (m := snprintfNeed) (by rw [hsI]; unfold fprintfNeed; omega)
    (by unfold fprintfNeed snprintfNeed; omega) $$ [Hslack Hscr]
  · isplitl [Hslack]
    · iexact Hslack
    · iexact Hscr
  iapply wp_interpRet1 H live hlive Wp sM (BitVec.ofNat 64 (T.jal.pc + 4)) r0 cs o imgI imgT eimg
    hsM hraI hs0I hra (by obtain ⟨k, hk, h0⟩ := henul; exact ⟨k, hk, h0⟩)
  unfold VsaIris.sp VsaIris.ra
  simp only [sepL_cons, sepL_nil]
  rw [show argRegs.drop 1 = argRegs.erase 10 from rfl]
  iframe Hpc Ha0 H21 Hra Hsp H23 H24 H25 H26 H27 Hargs Htmp Hgp Himg HI Hscr HT Herr Hstd Hcon HΦ
  isplitl [H8]
  · iexists _; iexact H8
  isplitl [H9]
  · iexists _; iexact H9
  isplitl [H18]
  · iexists _; iexact H18
  isplitl [H19]
  · iexists _; iexact H19
  isplitl [H20]
  · iexists _; iexact H20
  isplitl [H22]
  · iexists _; iexact H22
  iempintro

end Wp

end VsaIris.Newlib.TopAbrupt
