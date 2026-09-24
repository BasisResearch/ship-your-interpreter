import VsaIris.Interp.LeafCalls
import VsaIris.Interp.ProofNativeAssert
import VsaIris.Vsa.OomSites

/-!
# `runtime_error` from an `eval_expr` arm (lane E1)

The partial cases' error arms (`var` of an unbound name, `assign` to one)
call `runtime_error(in, e->line, fmt, name, 0)` from `eval_expr`'s frame
(`sp = s - 1088`). `ev_rtErr` is that call against H5's `rtErr_spec`: it
never returns, and its abort resource becomes the arm's own
(`abortAt evalCore s n ∗ slot24 sret`) by joining the frame back and widening
the landing core to the stack segment's (`evalCore`).

What the call needs beyond `evalPre`, named:

* `errCtx inp` (persistent): the binary image (`binImg`: `runtime_error` and
  `snprintf` run from it) and the `jmp_buf` read-only at an image whose `ra`
  word is aligned, with `in`'s placement (`ErrCtxOK`). `world` has the
  `jmp_buf` only existentially and no alignment; the supplier is A
  (`interp_run`'s `setjmp` wrote it, `TopLanding`), which holds all three at
  the top, so the partial cases take `errCtx` as a persistent premise beside
  the Löb hypothesis.
* `ErrRoom e d`: `runtime_error`'s stack below the arm's frame. It holds for
  `d < maxCallDepth` (`errRoom_of_lt`); at the deepest level it is
  INTERP_DESIGN.md Q7 (open: `rtErrNeed = 1248` exceeds the budget's 1088-byte
  leaf headroom).
* `evalCore`: the landing core over the whole stack segment, the one `Core`
  every nested abort widens to (`abortCore_mono`), so the partial cases with
  error arms are stated at `Core := evalCore`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.MemRepr Vsa.While Vsa.RuntimeRepr

/-- `in`'s placement and the `jmp_buf`'s return word, as `rtErr_spec` needs them. -/
structure ErrCtxOK (inp : Nat) (jb : Nat → BitVec 8) : Prop where
  ra : (jbWord inp jb 0).toNat % 4 = 0
  geom : RtErr.InpGeom (BitVec.ofNat 64 inp)
  lt : inp < 2 ^ 64

/-- `runtime_error`'s stack fits below an arm's frame (INTERP_DESIGN.md Q7). -/
structure ErrRoom (e : Expr) (d : Nat) : Prop where
  room : RtErr.rtErrNeed + evalFrame ≤ evalNeed e d

theorem errRoom_of_lt {e : Expr} {d : Nat} (h : d < maxCallDepth) : ErrRoom e d :=
  ⟨by
    have := Expr.stackNeed_ge e
    unfold evalNeed stackBudget RtErr.rtErrNeed snprintfNeed perCallBudget
    unfold maxCallDepth at h
    have : 1 ≤ 1000 - d := by omega
    have : 6144 ≤ (1000 - d) * 6144 := by
      calc 6144 = 1 * 6144 := by omega
        _ ≤ (1000 - d) * 6144 := Nat.mul_le_mul_right _ this
    unfold maxCallDepth; omega⟩

section Res

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- The error context the partial cases' error arms need (see the module doc). -/
def errCtx (inp : Nat) : IProp GF :=
  iprop(binImg ∗ ∃ jb, jmpRO inp jb ∗ ⌜ErrCtxOK inp jb⌝)

instance (inp : Nat) : Persistent (errCtx (GF := GF) inp) := by unfold errCtx; infer_instance

variable (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)

/-- The landing core over the whole stack segment `[0x87800000, 0x88000000)`. -/
def evalCore : IProp GF := abortCore N L Room inp 0x88000000#64 0x800000

/-- Every site inside the stack segment widens its core to `evalCore`. -/
theorem evalCore_of {s : BitVec 64} {n : Nat} (hn : n ≤ s.toNat) (hlo : 0x87800000 ≤ s.toNat - n)
    (hhi : s.toNat ≤ 0x88000000) :
    abortCore N L Room inp s n ⊢ evalCore (GF := GF) N L Room inp := by
  unfold evalCore
  exact abortCore_mono N L Room inp (by decide) (by unfold Vsa.Sim.tohostAddr; decide)
    (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
    (by decide)

end Res

/-! ## The error messages -/

/-- `"undefined variable '%s'"` (`.rodata` `0x80019388`). -/
def varFmtBytes : List (BitVec 8) :=
  [0x75#8, 0x6e#8, 0x64#8, 0x65#8, 0x66#8, 0x69#8, 0x6e#8, 0x65#8, 0x64#8, 0x20#8, 0x76#8, 0x61#8,
    0x72#8, 0x69#8, 0x61#8, 0x62#8, 0x6c#8, 0x65#8, 0x20#8, 0x27#8, 0x25#8, 0x73#8, 0x27#8]

/-- `"cannot assign to undefined variable '%s' (declare it with 'var')"`
(`.rodata` `0x800193a0`). -/
def assignFmtBytes : List (BitVec 8) :=
  [0x63#8, 0x61#8, 0x6e#8, 0x6e#8, 0x6f#8, 0x74#8, 0x20#8, 0x61#8, 0x73#8, 0x73#8, 0x69#8, 0x67#8,
    0x6e#8, 0x20#8, 0x74#8, 0x6f#8, 0x20#8, 0x75#8, 0x6e#8, 0x64#8, 0x65#8, 0x66#8, 0x69#8, 0x6e#8,
    0x65#8, 0x64#8, 0x20#8, 0x76#8, 0x61#8, 0x72#8, 0x69#8, 0x61#8, 0x62#8, 0x6c#8, 0x65#8, 0x20#8,
    0x27#8, 0x25#8, 0x73#8, 0x27#8, 0x20#8, 0x28#8, 0x64#8, 0x65#8, 0x63#8, 0x6c#8, 0x61#8, 0x72#8,
    0x65#8, 0x20#8, 0x69#8, 0x74#8, 0x20#8, 0x77#8, 0x69#8, 0x74#8, 0x68#8, 0x20#8, 0x27#8, 0x76#8,
    0x61#8, 0x72#8, 0x27#8, 0x29#8]

/-- A `.rodata` format with one `%s`, and a C string argument. -/
theorem fmt1s_ok {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) {fmt : BitVec 64} {bs : List (BitVec 8)}
    (hb : ∀ i (h : i < bs.length), rodataDom (fmt.toNat + i) ∧ rodataByte (fmt.toNat + i) = bs[i] ∧
      bs[i] ≠ 0)
    (hn : rodataDom (fmt.toNat + bs.length) ∧ rodataByte (fmt.toNat + bs.length) = 0)
    (hp : parseFmt bs = some [.str]) {x1 : BitVec 64} (hs : ∃ t, CStrCov R rd x1.toNat t)
    (x2 : BitVec 64) : FmtArgsOK R rd fmt [x1, x2] := by
  refine ⟨bs, [.str], ⟨cstrCov_rodata hro hb hn, hp, by simp, ?_⟩⟩
  intro i hi _
  have : i = 0 := by simpa using hi
  subst this
  exact hs

theorem varFmt_ok {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) {x1 : BitVec 64}
    (hs : ∃ t, CStrCov R rd x1.toNat t) (x2 : BitVec 64) :
    FmtArgsOK R rd 0x80019388#64 [x1, x2] :=
  fmt1s_ok hro (bs := varFmtBytes) (by decide) (by decide) (by decide) hs x2

theorem assignFmt_ok {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) {x1 : BitVec 64}
    (hs : ∃ t, CStrCov R rd x1.toNat t) (x2 : BitVec 64) :
    FmtArgsOK R rd 0x800193a0#64 [x1, x2] :=
  fmt1s_ok hro (bs := assignFmtBytes) (by decide) (by decide) (by decide) hs x2

/-! ## The call -/

section Call

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- **`runtime_error(in, line, fmt, name, 0)` from an `eval_expr` arm** (`jal`
at `i`, `sp = s - 1088`), `fmt` a `.rodata` message with one `%s` for the
name `x` at `p`: it never returns; on abort, the arm's frame and the result
slot rejoin, and the landing core widens to `evalCore`. -/
theorem ev_rtErr (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} (HN : NewlibHoles)
    (hcl : CodeLive live) {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code RtErr.rtErrEntry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    {sret s line fmt : BitVec 64} {n : Nat} {ρ : Regime} {st : St} {d : Nat} {p : Nat} {x : String}
    (hfmt : ∀ {R : Nat → Prop} {rd : Nat → BitVec 8},
      (∀ a, rodataDom a → R a ∧ rd a = rodataByte a) →
      (∃ t, CStrCov R rd (BitVec.ofNat 64 p).toNat t) → FmtArgsOK R rd fmt [BitVec.ofNat 64 p, 0#64])
    (hpt : p < 2 ^ 64) (hsg : StackGeom s n) (hroom : RtErr.rtErrNeed + 1088 ≤ n)
    (hdj : ∀ b, InExt (s.toNat - 1088, 1088) b → ¬ InExt (sret.toNat, 24) b)
    {R : Nat → BitVec 64} {M : Mem}
    (hR : R 10 = BitVec.ofNat 64 inp ∧ R 11 = line ∧ R 12 = fmt ∧ R 13 = BitVec.ofNat 64 p ∧
      R 14 = 0#64 ∧ R 2 = evalSP s) :
    errCtx inp ∗ codeRes ∗ strAt p x ∗ ms (BitVec.ofNat 64 i) R (frS (s.toNat - 1088) sret.toNat) M ∗
      stackScratch (evalSP s) (n - 1088) ∗ world N L Room inp ρ st d ∗
      (abortAt (evalCore N L Room inp) s n ∗ slot24 sret.toNat -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  obtain ⟨hR10, hR11, hR12, hR13, hR14, hR2⟩ := hR
  unfold errCtx
  iintro ⟨⟨#Himg, %jb, #Hjb, %hok⟩, #Hcode, #Hx, Hms, Hst, Hw, Hab⟩
  have hs1 := hsg.le; have hs2 := hsg.lo; have hs3 := hsg.hi; have hs4 := hsg.al
  unfold Vsa.Sim.LayoutInstance.stackSL at hs2 hs3
  simp only at hs2 hs3
  have hsf : (evalSP s).toNat = s.toNat - 1088 := by
    rw [← evalSP_eq]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have hrt := hroom
  unfold RtErr.rtErrNeed snprintfNeed at hrt
  have hsp : SpIn (evalSP s) RtErr.rtErrNeed :=
    ⟨by rw [hsf]; unfold RtErr.rtErrNeed snprintfNeed Vsa.Sim.tohostAddr; omega,
      by rw [hsf]; omega, by rw [hsf]; omega⟩
  have hinpt : (BitVec.ofNat 64 inp).toNat = inp := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hok.lt]
  ihave ⟨%rd, Hrd, %hrd⟩ := readable_str $$ [Himg Hx]
  · isplitl
    · iexact Himg
    · iexact Hx
  have hpt' : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpt]
  have hf : FmtArgsOK (fun a => (rodataDom a ∨ InExt (p, x.toList.length + 1) a) ∨ False) rd fmt
      [BitVec.ofNat 64 p, 0#64] :=
    hfmt (fun a ha => ⟨Or.inl (Or.inl ha), hrd.1 a ha⟩)
      ⟨_, by
        rw [hpt']
        exact cstrCov_of_img (fun i hi => Or.inl (Or.inr (by simp only [InExt]; omega))) hrd.2⟩
  rw [← hinpt]
  ihave #Hspec := RtErr.rtErr_spec HN live hcl Wp N L Room (BitVec.ofNat 64 inp) (evalSP s) line
    fmt (BitVec.ofNat 64 p) 0#64 R _ (fun _ => False) rd jb ρ st d hsp hok.geom hf
    (by rw [hinpt]; exact hok.ra)
  ihave #Hgp := codeRes_gp $$ Hcode
  have hn1088 : n - 1088 ≤ (evalSP s).toNat := by rw [hsf]; omega
  iapply ms_callNewlibAbort Wp hexec hcode (vs := [BitVec.ofNat 64 inp, line, fmt, BitVec.ofNat 64 p, 0#64])
    (P := fun _ => iprop(argsAt [BitVec.ofNat 64 inp, line, fmt, BitVec.ofNat 64 p, 0#64] ∗
      callFrame (evalSP s) RtErr.rtErrNeed Newlib.calleeSaved R ∗
      readable (fun a => rodataDom a ∨ InExt (p, x.toList.length + 1) a) (fun _ => False) rd ∗
      jmpRO (BitVec.ofNat 64 inp).toNat jb ∗ world N L Room (BitVec.ofNat 64 inp).toNat ρ st d))
    (Q := fun _ => iprop(False))
    (A := abortRes N L Room (BitVec.ofNat 64 inp).toNat (evalSP s) RtErr.rtErrNeed)
    (X := iprop(readable (fun a => rodataDom a ∨ InExt (p, x.toList.length + 1) a) (fun _ => False) rd ∗
      jmpRO (BitVec.ofNat 64 inp).toNat jb ∗ world N L Room (BitVec.ofNat 64 inp).toNat ρ st d))
    (Y := iprop(False))
    (need := RtErr.rtErrNeed) (n := n - 1088) (by simp)
    (fun j hj => by
      simp only [List.length_cons, List.length_nil] at hj
      rcases j with _ | _ | _ | _ | _ | j
      · exact hR10
      · exact hR11
      · exact hR12
      · exact hR13
      · exact hR14
      · omega)
    hR2 hn1088 (by unfold RtErr.rtErrNeed snprintfNeed; omega)
    (fun r => by iintro ⟨Ha, ⟨Hr, Hj, Hw⟩, Hf⟩; iframe Ha Hf Hr Hj Hw)
    (fun r => by iintro H; iexfalso; iexact H)
  rw [hinpt]
  iframe Hspec Hcode Hms Hst Hgp Himg Hrd Hjb Hw
  isplit
  · iintro %R' %_ Hf
    iexfalso; iexact Hf
  · iintro HA Hslack HS
    unfold abortRes abortAt
    icases HA with ⟨Hcore, Hst⟩
    ihave Hcore := evalCore_of N L Room inp (s := evalSP s) (n := RtErr.rtErrNeed)
      (by rw [hsf]; unfold RtErr.rtErrNeed snprintfNeed; omega)
      (by rw [hsf]; unfold RtErr.rtErrNeed snprintfNeed; omega) (by have := hsf; omega) $$ Hcore
    ihave Hst := stackScratch_widen (m := RtErr.rtErrNeed) hn1088
      (by unfold RtErr.rtErrNeed snprintfNeed; omega) $$ [Hslack Hst]
    · iframe Hslack Hst
    ihave ⟨HF, HA⟩ := ownSet_split_tracked _ _ M hdj $$ HS
    ihave HF := ownSet_forget _ _ $$ HF
    ihave HA := ownSet_forget _ _ $$ HA
    ihave Hst := evalFrame_join (s := s) (n := n) hs1 (by omega) $$ [Hst HF]
    · iframe Hst HF
    iapply Hab
    iframe Hcore Hst
    unfold slot24 blockOwn
    iexact HA

end Call

/-! ## Out of memory -/

section Oom

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- **An `eval_expr` arm's out-of-memory block** (H5's `wp_oomBlock` at site
`S`, from its head with `sp = s - 1088`): the arm's frame and the stack below
it become `exit(1)`'s region; the abort core widens to `evalCore` and the
result slot is handed back. -/
theorem ev_oom (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} (HN : NewlibHoles)
    (hcl : CodeLive live) {S : Oom.OomSite} (hS : S.OK) {s sret : BitVec 64} {n : Nat} {o : String}
    (hsg : StackGeom s n) (hsp : Oom.OomBlockSp S s n (evalSP s))
    (hdj : ∀ b, InExt (s.toNat - 1088, 1088) b → ¬ InExt (sret.toNat, 24) b)
    {R : Nat → BitVec 64} {M : Mem} (hR2 : R 2 = evalSP s) :
    errCtx inp ∗ codeRes ∗ ms (BitVec.ofNat 64 S.head) R (frS (s.toNat - 1088) sret.toNat) M ∗
      stackScratch (evalSP s) (n - 1088) ∗ Stdio.stdioOwn ∗ consoleOwn o ∗
      (abortAt (evalCore N L Room inp) s n ∗ slot24 sret.toNat -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  unfold errCtx
  iintro ⟨⟨#Himg, -⟩, #Hcode, Hms, Hst, Hstd, Hcon, Hk⟩
  have hs1 := hsg.le; have hs2 := hsg.lo; have hs3 := hsg.hi
  unfold Vsa.Sim.LayoutInstance.stackSL at hs2 hs3
  simp only at hs2 hs3
  have hf := hsp.frame; have hfit := hsp.fits
  have hsf : (evalSP s).toNat = s.toNat - 1088 := by
    rw [← evalSP_eq]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  unfold fwriteNeed at hfit
  ihave ⟨Hpc, Hra, Hregs, HS, Hsl⟩ := ms_exit_sretAny hdj $$ Hms
  ihave Hst := evalFrame_join (s := s) (n := n) hs1 (by omega) $$ [Hst HS]
  · iframe Hst HS
  ihave ⟨Hsp, Hcs, Htmp, Hargs⟩ := (regFile_newlib _).1 $$ Hregs
  ihave Htmp := clobbered_of_fn _ _ $$ Htmp
  ihave Hargs := clobbered_of_fn _ _ $$ Hargs
  ihave #Hgp := codeRes_gp $$ Hcode
  rw [hR2]
  iapply Oom.wp_oomBlock HN live hcl Wp N L Room inp S hS s (evalSP s) _ n hsp _ o
  iframe Hpc Hra Hsp Hargs Htmp Hcs Hgp Himg Hst Hstd Hcon
  iintro HA
  unfold abortRes abortAt
  icases HA with ⟨Hcore, Hst⟩
  ihave Hcore := evalCore_of N L Room inp (s := s) (n := n) hs1 (by omega) hs3 $$ Hcore
  iapply Hk
  iframe Hcore Hst Hsl

end Oom

end VsaIris.Interp
