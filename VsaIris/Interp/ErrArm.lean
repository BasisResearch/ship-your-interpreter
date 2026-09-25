import VsaIris.Interp.SpecErr
import VsaIris.Interp.ProofNativeAssert
import VsaIris.Interp.ProofValueKindName

/-!
# `runtime_error` from an `eval_expr` arm (lane E2)

INTERP_DESIGN.md §4.2. An error arm of `eval_expr` ends in `jal runtime_error`
at `sp = s - 1088` (the arm's frame is spilled). H5's `rtErr_spec` never
returns; its abort branch hands back `abortRes (s - 1088) rtErrNeed`. Joined
with the stack the call did not take and the arm's frame bytes, that is
`abortAt Core s n`, the abort of `evalSpecP_body` at the arm's `s` (the result
slot is the caller's to add). `ms_rtErrEval` is that step, for any eval arm
whose stack below its frame fits `runtime_error` (`1088 + rtErrNeed ≤ n`):
the binary and unary arms (`evalNeed` ≥ `3 * 1088`), and any arm with a child.
The model is H2's `na_rtErr` (`ProofNativeAssert.lean`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-! ## The messages -/

/-- A `.rodata` C string of `n` characters at `p`, read through any `rd` that
agrees with the image there: one `decide` each for the bytes and the NUL. -/
theorem rodata_cstr {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) (p n : Nat)
    (hb : ∀ i, i < n → rodataDom (p + i) ∧ rodataByte (p + i) ≠ 0)
    (hn : rodataDom (p + n) ∧ rodataByte (p + n) = 0) : ∃ t, CStrCov R rd p t :=
  ⟨(List.range n).map (fun i => rodataByte (p + i)), cstrCov_rodata hro
    (fun i h => by
      simp only [List.length_map, List.length_range] at h
      obtain ⟨h1, h2⟩ := hb i h
      exact ⟨h1, by simp, by simpa using h2⟩)
    (by simpa using hn)⟩

/-- `rodata_cstr` at a pointer word. -/
theorem rodata_cstrV {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) (p : BitVec 64) (n : Nat)
    (hb : ∀ i, i < n → rodataDom (p.toNat + i) ∧ rodataByte (p.toNat + i) ≠ 0)
    (hn : rodataDom (p.toNat + n) ∧ rodataByte (p.toNat + n) = 0) : ∃ t, CStrCov R rd p.toNat t :=
  rodata_cstr hro p.toNat n hb hn

/-- `value_kind_name`'s names are `.rodata` C strings. -/
theorem kindName_cstr {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) (v : Value) :
    ∃ t, CStrCov R rd (kindNamePtr v).toNat t := by
  cases v
  · exact rodata_cstr hro 0x80019018 4 (by decide) (by decide)
  · exact rodata_cstr hro 0x800192e8 4 (by decide) (by decide)
  · exact rodata_cstr hro 0x800192f0 3 (by decide) (by decide)
  · exact rodata_cstr hro 0x80018ea0 6 (by decide) (by decide)
  · exact rodata_cstr hro 0x800192f8 8 (by decide) (by decide)
  · exact rodata_cstr hro 0x80019308 15 (by decide) (by decide)

/-- `"operand of '%s' must be an int, got %s"` (`.rodata` `0x800193f0`), the
type error of `eval_binary`'s `int_operand`: two C string arguments. -/
theorem operand_fmt {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) {x1 x2 : BitVec 64}
    (h1 : ∃ t, CStrCov R rd x1.toNat t) (h2 : ∃ t, CStrCov R rd x2.toNat t) :
    FmtArgsOK R rd 0x800193f0#64 [x1, x2] := by
  refine ⟨(List.range 38).map (fun i => rodataByte (0x800193f0 + i)), [.str, .str],
    ⟨cstrCov_rodata hro (fun i h => ?_) (by decide), by decide, by simp, ?_⟩⟩
  · simp only [List.length_map, List.length_range] at h
    have := (show ∀ i, i < 38 → rodataDom (0x800193f0 + i) ∧ rodataByte (0x800193f0 + i) ≠ 0
      by decide) i h
    exact ⟨this.1, by simp, by simpa using this.2⟩
  · intro i hi _
    rcases i with _ | _ | i
    · exact h1
    · exact h2
    · simp only [List.length_cons, List.length_nil] at hi; omega

/-- A `.rodata` message with no conversion: any arguments. -/
theorem plain_fmt {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) (p : BitVec 64) (n : Nat)
    (hb : ∀ i, i < n → rodataDom (p.toNat + i) ∧ rodataByte (p.toNat + i) ≠ 0)
    (hn : rodataDom (p.toNat + n) ∧ rodataByte (p.toNat + n) = 0)
    (hp : parseFmt ((List.range n).map (fun i => rodataByte (p.toNat + i))) = some [])
    (args : List (BitVec 64)) : FmtArgsOK R rd p args :=
  ⟨(List.range n).map (fun i => rodataByte (p.toNat + i)), [],
    ⟨cstrCov_rodata hro (fun i h => by
      simp only [List.length_map, List.length_range] at h
      obtain ⟨h1, h2⟩ := hb i h
      exact ⟨h1, by simp, by simpa using h2⟩) (by simpa using hn), hp, by simp,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩

/-- A message whose format and arguments are all `.rodata`. -/
theorem readable_rodata_fmt {fmt : BitVec 64} {args : List (BitVec 64)}
    (h : ∀ {R : Nat → Prop} {rd : Nat → BitVec 8}, (∀ a, rodataDom a → R a ∧ rd a = rodataByte a) →
      FmtArgsOK R rd fmt args) :
    FmtArgsOK (fun a => rodataDom a ∨ False) rodataByte fmt args :=
  h (fun a ha => ⟨.inl ha, rfl⟩)

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The registers at an eval arm's `jal runtime_error`:
`runtime_error(in, line, fmt, x1, x2)` with `sp = s - 1088`. -/
structure RtErrEvalAt (R : Nat → BitVec 64) (inp : Nat) (line fmt x1 x2 s : BitVec 64) : Prop where
  h10 : R 10 = BitVec.ofNat 64 inp
  h11 : R 11 = line
  h12 : R 12 = fmt
  h13 : R 13 = x1
  h14 : R 14 = x2
  h2 : R 2 = evalSP s

/-- **A callee's abort below an `eval_expr` arm** (`sp = s - 1088`, the callee
entered with `need` bytes below `sp`): the arm's own `abortAt Core s n`. -/
theorem abortAt_of_evalCallee {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {Core : IProp GF} (hC : CoreOK N L Room inp Core) {s : BitVec 64} {n need : Nat}
    (hsg : StackGeom s n) (hn : 1088 + need ≤ n) :
    abortRes N L Room inp (evalSP s) need ∗ blockOwn (s.toNat - n) (n - 1088 - need) ∗
      ownSet (InExt (s.toNat - 1088, 1088)) byteAny ⊢ abortAt Core s n := by
  have hs1 := hsg.lo; have hs2 := hsg.hi; have hs4 := hsg.le; have hs5 := hsg.top
  unfold Vsa.Sim.LayoutInstance.stackSL at hs1 hs2
  simp only at hs1 hs2
  have hsf : (evalSP s).toNat = s.toNat - 1088 := by
    rw [← evalSP_eq]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  iintro ⟨HA, Hslack, HS⟩
  unfold abortRes abortAt
  icases HA with ⟨Hcore, Hst⟩
  ihave Hcore := hC (evalSP s) need (by rw [hsf]; omega) (by rw [hsf]; omega) (by rw [hsf]; omega)
    $$ Hcore
  ihave Hst := stackScratch_widen (s := evalSP s) (n := n - 1088) (m := need)
    (by rw [hsf]; omega) (by omega) $$ [Hslack Hst]
  · rw [hsf, show s.toNat - 1088 - (n - 1088) = s.toNat - n by omega]; iframe Hslack Hst
  ihave Hst := evalFrame_join hs4 (by omega) $$ [Hst HS]
  · iframe Hst HS
  iframe Hcore Hst

/-- **`runtime_error` from an eval arm, reading owned frame bytes** (`jal` at
`i`, `sp = s - 1088`): the format's `%s` arguments may also lie in bytes
`Sown` of the arm's frame (a message buffer), lent to the call as `readable`
and carved out of the run's bytes. It never returns; on abort, H5's resource
and the lent bytes (`rtErr_spec` returns them) rejoin the arm's
`abortAt Core s n`. -/
theorem ms_rtErrEvalOwn (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    (hE : ErrEnv N L Room inp live Core)
    {i : Nat} {code : List (BitVec 8)} (hexec : JalExec (vsaModel live) i code RtErr.rtErrEntry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    {s line fmt x1 x2 : BitVec 64} {n : Nat} {ρ : Regime} {st : St} {d : Nat}
    {Sro Sown : Nat → Prop} {rd : Nat → BitVec 8}
    (hown : ∀ a, Sown a → InExt (s.toNat - 1088, 1088) a)
    (hfmt : FmtArgsOK (fun a => Sro a ∨ Sown a) rd fmt [x1, x2])
    (hsg : StackGeom s n) (hn : 1088 + RtErr.rtErrNeed ≤ n)
    {R : Nat → BitVec 64} {Mt : Mem} :
    ⌜RtErrEvalAt R inp line fmt x1 x2 s⌝ ∗ codeRes ∗ errCtx inp ∗ readable Sro Sown rd ∗
      ms (BitVec.ofNat 64 i) R (fun a => InExt (s.toNat - 1088, 1088) a ∧ ¬ Sown a) Mt ∗
      stackScratch (evalSP s) (n - 1088) ∗ world N L Room inp ρ st d ∗
      (abortAt Core s n -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨%hR, #Hcode, #HE, Hrd, Hms, Hst, Hw, Hab⟩
  unfold errCtx
  icases HE with ⟨#Himg, %jb, #Hjb, %hjb⟩
  have hs1 := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs1 hs2
  simp only at hs1 hs2
  unfold RtErr.rtErrNeed snprintfNeed at hn
  have hsf : (evalSP s).toNat = s.toNat - 1088 := by
    rw [← evalSP_eq]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have hsp : SpIn (evalSP s) RtErr.rtErrNeed :=
    ⟨by rw [hsf]; unfold RtErr.rtErrNeed snprintfNeed Vsa.Sim.tohostAddr; omega,
      by rw [hsf]; omega, by rw [hsf]; omega⟩
  have hinp := hE.inpGeom
  have hinpN : (BitVec.ofNat 64 inp).toNat = inp := Nat.mod_eq_of_lt hE.inpLt
  have hjb' : (jbWord (BitVec.ofNat 64 inp).toNat jb 0).toNat % 4 = 0 := by rw [hinpN]; exact hjb
  have hspec := RtErr.rtErr_spec hE.newlib live hE.code Wp N L Room (BitVec.ofNat 64 inp)
    (evalSP s) line fmt x1 x2 R Sro Sown rd jb ρ st d hsp hinp hfmt hjb'
  rw [hinpN] at hspec
  ihave #Hspec := hspec
  ihave #Hgp := codeRes_gp $$ Hcode
  iapply ms_callNewlibAbort Wp hexec hcode (vs := [BitVec.ofNat 64 inp, line, fmt, x1, x2])
    (P := fun _ => iprop(argsAt [BitVec.ofNat 64 inp, line, fmt, x1, x2] ∗
      callFrame (evalSP s) RtErr.rtErrNeed Newlib.calleeSaved R ∗
      readable Sro Sown rd ∗ jmpRO inp jb ∗
      world N L Room inp ρ st d))
    (Q := fun _ => iprop(False))
    (A := iprop(abortRes N L Room inp (evalSP s) RtErr.rtErrNeed ∗ readable Sro Sown rd))
    (X := iprop(readable Sro Sown rd ∗ jmpRO inp jb ∗
      world N L Room inp ρ st d)) (Y := iprop(False))
    (need := RtErr.rtErrNeed) (n := n - 1088) (by simp)
    (fun j hj => by
      simp only [List.length_cons, List.length_nil] at hj
      rcases j with _ | _ | _ | _ | _ | j
      · exact hR.h10
      · exact hR.h11
      · exact hR.h12
      · exact hR.h13
      · exact hR.h14
      · omega)
    hR.h2 (by rw [hsf]; omega) (by unfold RtErr.rtErrNeed snprintfNeed; omega)
    (fun r => by iintro ⟨Ha, ⟨Hr, Hj, Hw⟩, Hf⟩; iframe Ha Hf Hr Hj Hw)
    (fun r => by iintro H; iexfalso; iexact H)
  iframe Hspec Hcode Hms Hst Hgp Himg Hrd Hjb Hw
  isplit
  · iintro %R' %_ Hf
    iexfalso; iexact Hf
  · iintro ⟨HA, Hrd⟩ Hslack HS
    ihave HS := ownSet_forget _ _ $$ HS
    unfold readable
    icases Hrd with ⟨-, Hown⟩
    ihave Hown := ownSet_forget _ _ $$ Hown
    ihave HS := ownSet_join (fun a => InExt (s.toNat - 1088, 1088) a ∧ ¬ Sown a) Sown byteAny
      (fun a h1 h2 => h1.2 h2) $$ [HS Hown]
    · iframe HS Hown
    ihave HS := ownSet_iff _ (T := InExt (s.toNat - 1088, 1088)) (fun a => ⟨fun h => h.elim (·.1)
      (hown a), fun h => by
        by_cases h' : Sown a
        · exact .inr h'
        · exact .inl ⟨h, h'⟩⟩) $$ HS
    iapply Hab
    iapply abortAt_of_evalCallee hE.core hsg (need := RtErr.rtErrNeed) (by unfold RtErr.rtErrNeed snprintfNeed; omega)
    rw [hsf, show s.toNat - 1088 - (n - 1088) = s.toNat - n by omega]
    iframe HA Hslack HS

/-- **`runtime_error` from an eval arm** (`jal` at `i`, `sp = s - 1088`): it
never returns; on abort, H5's resource becomes the arm's `abortAt Core s n`:
the call's stack, the slack below it and the frame bytes rejoin the stack
below `s`, and `CoreOK` turns H5's core into `Core`. -/
theorem ms_rtErrEval (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    (hE : ErrEnv N L Room inp live Core)
    {i : Nat} {code : List (BitVec 8)} (hexec : JalExec (vsaModel live) i code RtErr.rtErrEntry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    {s line fmt x1 x2 : BitVec 64} {n : Nat} {ρ : Regime} {st : St} {d : Nat}
    {Sro : Nat → Prop} {rd : Nat → BitVec 8}
    (hfmt : FmtArgsOK (fun a => Sro a ∨ False) rd fmt [x1, x2])
    (hsg : StackGeom s n) (hn : 1088 + RtErr.rtErrNeed ≤ n)
    {R : Nat → BitVec 64} {Mt : Mem} :
    ⌜RtErrEvalAt R inp line fmt x1 x2 s⌝ ∗ codeRes ∗ errCtx inp ∗ readable Sro (fun _ => False) rd ∗
      ms (BitVec.ofNat 64 i) R (InExt (s.toNat - 1088, 1088)) Mt ∗
      stackScratch (evalSP s) (n - 1088) ∗ world N L Room inp ρ st d ∗
      (abortAt Core s n -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨%hR, #Hcode, #HE, Hrd, Hms, Hst, Hw, Hab⟩
  ihave Hms := ms_iff (T := fun a => InExt (s.toNat - 1088, 1088) a ∧ ¬ False)
    (fun a => ⟨fun h => ⟨h, id⟩, fun h => h.1⟩) $$ Hms
  iapply ms_rtErrEvalOwn Wp hE hexec hcode (Sown := fun _ => False) (fun a h => h.elim) hfmt hsg hn
  iframe Hcode HE Hrd Hms Hst Hw Hab
  ipureintro; exact hR


/-- A binary node's budget leaves `runtime_error` room below the arm's frame:
each child needs at least two frames. -/
theorem evalNeed_binary_rtErr (op : BinOp) (l r : Expr) (d : Nat) :
    1088 + RtErr.rtErrNeed ≤ evalNeed (.binary op l r) d := by
  have := evalNeed_binary_left op l r d; have := Expr.stackNeed_ge l
  unfold evalNeed stackBudget at *; unfold RtErr.rtErrNeed snprintfNeed evalFrame at *; omega

/-- A 24-byte slot at frame offset `o` of an `eval_expr` arm (`sp + o`). -/
theorem evalSlotGeom {s : BitVec 64} {n : Nat} (hsg : StackGeom s n) (hn : 1088 ≤ n) {o : Nat}
    (ho : o + 24 ≤ 1088) (ho8 : o % 8 = 0) : SlotGeom (evalSP s + BitVec.ofNat 64 o) :=
  (evalCallGeom (nc := 0) hsg (by omega) ho ho8).slotGeom

/-- **`value_kind_name` from a run** (`jal` at `i`), on the value whose kind
word the run stored at the slot `p` of its owned bytes: the slot's bytes are
lent to the call at their tracked image and joined back unchanged. -/
theorem ms_callKindName (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hvk : ⊢ ∀ p Mt v, valueKindNameSpec (vsaModel live) Wp p Mt v)
    {i : Nat} {code : List (BitVec 8)} (hexec : JalExec (vsaModel live) i code valueKindNamePC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {p w0 : BitVec 64} {v : Value}
    (hS : ∀ k, InExt (p.toNat, 24) k → S k) (hg : SlotGeom p)
    (h0 : ldv .ld Mt p.toNat = w0) (htag : w0.toNat % 2 ^ 32 = valTag v) :
    ⌜R 10 = p⌝ ∗ codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗
      (∀ (R' : Nat → BitVec 64) (M' : Mem), ⌜∀ x ∈ fRegs, x ∉ [10, 14, 15] → R' x = R x⌝ -∗
        ⌜R' 10 = kindNamePtr v⌝ -∗ ⌜∀ k, S k → imgM M' k = imgM Mt k⌝ -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S M' -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨%h10, #Hcode, Hms, Hk⟩
  rw [ldv_ld_imgW] at h0
  have hsl : ∀ k, S k ↔ ((S k ∧ ¬ InExt (p.toNat, 24) k) ∨ InExt (p.toNat, 24) k) := fun k => by
    constructor
    · intro h; by_cases h' : InExt (p.toNat, 24) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hS k h
  ihave Hms := ms_iff hsl $$ Hms
  ihave ⟨Hms, Hslot⟩ := ms_split (fun k h1 h2 => h1.2 h2) $$ Hms
  ihave Hspec := hvk $$ %p %Mt %v
  unfold valueKindNameSpec
  iapply ms_callHelper Wp hexec hcode hal
  iframe Hspec Hcode Hms
  isplitl []
  · ipureintro; exact h10
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact ⟨hg, by rw [h0]; exact htag⟩
  iintro %R' %hkeep ⟨Hslot, %h10'⟩ Hms
  ihave ⟨%M', Hms, %⟨hag1, hag2, -⟩⟩ := ms_join $$ [Hms Hslot]
  · iframe Hms Hslot
  ihave Hms := ms_iff (fun k => (hsl k).symm) $$ Hms
  iapply Hk $$ %R' %M' %hkeep %h10' %(fun k hk => by
    by_cases h : InExt (p.toNat, 24) k
    · exact hag2 k h
    · exact hag1 k ⟨hk, h⟩) Hms
end

end VsaIris.Interp
