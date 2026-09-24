import VsaIris.Interp.ProofNativePrint
import VsaIris.Interp.ProofValueTruthy

/-!
# `native_assert` (lane H2)

`native_assert(sret, in, argc, args, line)`: with `argc ∉ {1, 2}` it calls
`runtime_error(in, line, "assert() takes 1 or 2 arguments", 0, 0)`; otherwise
it copies the first argument into its frame, asks `value_truthy`, and returns
`null` (`value_null`) when truthy, else calls `runtime_error(in, line, "%s",
msg, 0)` with `msg` the second argument's string or `"assertion failed"`.
`runtime_error` never returns (H5's `rtErr_spec`): its abort resource, with
the frame given back, is `native_assert`'s.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib VsaIris.Stdio
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-! ## The runs (`npF`: the 80-byte frame and the arguments) -/

/-- `addiw a6,a2,-1; bltu 1,a6`: one or two arguments pass the arity test. -/
theorem na_arity {n : Nat} (hn : n = 1 ∨ n = 2) :
    ¬ (1#64).toNat < (BitVec.signExtend 64
      (BitVec.extractLsb 31 0 (BitVec.ofNat 64 n + 18446744073709551615#64))).toNat := by
  rcases hn with rfl | rfl <;> decide

/- The prologue, one or two arguments: the saved registers, the arity test,
to the copy of the first argument. -/
#ix_seg na_pro {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {rv : Nat → BitVec 64}
    {s args r : BitVec 64} {n : Nat}
    (h12 : rv 12 = BitVec.ofNat 64 n) (h2 : rv 2 = s)
    (hs1 : 0x87800000 + 80 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hn : n = 1 ∨ n = 2) :
    IW live ∅ [] (npF s args n) Q nativeAssertPC (upd rv 1 r) M
  by
    have hsf : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
      rw [BitVec.toNat_add]; simp; omega
    unfold nativeAssertPC
    ix_run1 hlive using [h12, h2, hsf] at 0x80002e1c
    all_goals first
      | (intro hc; exfalso; revert hc; ix_reg; exact na_arity hn)
      | (intro _; ix_run1 hlive using [h12, h2, hsf] at 0x80002e1c)

/- The copy of the first argument into the frame, to `jal value_truthy`. -/
#ix_seg na_copy {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s args : BitVec 64} {n : Nat} {w0 w1 w2 : BitVec 64}
    (h13 : R 13 = args) (h2 : R 2 = s + 18446744073709551536#64)
    (hs1 : 0x87800000 + 80 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hn : 1 ≤ n) (ha1 : args.toNat % 8 = 0) (ha2 : 0x8001ad00 + 16 ≤ args.toNat)
    (ha3 : args.toNat + 24 * n ≤ 0x100000000)
    (hw0 : ldv .ld M args.toNat = w0) (hw1 : ldv .ld M (args + 8#64).toNat = w1)
    (hw2 : ldv .ld M (args + 16#64).toNat = w2) :
    IW live ∅ [] (npF s args n) Q 0x80002e1c#64 R M
  by
    have hsf : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
      rw [BitVec.toNat_add]; simp; omega
    ix_run1 hlive using [h13, h2, hsf, hw0, hw1, hw2] at 0x80002e44

/-- Any other count fails it (`argc - 1` as a 32-bit value is `-1` or at
least `2`). -/
theorem na_arity_bad {n : Nat} (hn : ¬ (n = 1 ∨ n = 2)) (hn2 : n < 2 ^ 31) :
    (1#64).toNat < (BitVec.signExtend 64
      (BitVec.extractLsb 31 0 (BitVec.ofNat 64 n + 18446744073709551615#64))).toNat := by
  by_cases h0 : n = 0
  · subst h0
    have hm : (BitVec.extractLsb 31 0 (BitVec.ofNat 64 0 + 18446744073709551615#64)).msb = true := by
      rw [BitVec.msb_eq_decide]; simp
    rw [BitVec.signExtend_eq_not_setWidth_not_of_msb_true hm]
    simp
  · have e : BitVec.ofNat 64 n + 18446744073709551615#64 = BitVec.ofNat 64 (n - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show n - 1 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show 18446744073709551615 < 2 ^ 64 by decide)]
      rw [show n + 18446744073709551615 = (n - 1) + 2 ^ 64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show n - 1 < 2 ^ 64 by omega)]
    have hm : (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (n - 1))).msb = false := by
      rw [BitVec.msb_eq_decide]; simp; omega
    rw [e, BitVec.signExtend_eq_setWidth_of_msb_false hm]
    simp; omega

/- The prologue, any other count: to `jal runtime_error` with the arity
message. -/
#ix_seg na_bad {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {rv : Nat → BitVec 64}
    {s args r : BitVec 64} {n : Nat}
    (h12 : rv 12 = BitVec.ofNat 64 n) (h2 : rv 2 = s)
    (hs1 : 0x87800000 + 80 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hn : ¬ (n = 1 ∨ n = 2)) (hn2 : n < 2 ^ 31) :
    IW live ∅ [] (npF s args n) Q nativeAssertPC (upd rv 1 r) M
  by
    have hsf : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
      rw [BitVec.toNat_add]; simp; omega
    unfold nativeAssertPC
    ix_run1 hlive using [h12, h2, hsf] at 0x80002e90
    all_goals first
      | (intro hc; exfalso; apply hc; ix_reg; exact na_arity_bad hn hn2)
      | (intro _; ix_run1 hlive using [h12, h2, hsf] at 0x80002e90)

/- After `value_truthy`, truthy: to `jal value_null`. -/
#ix_seg na_ok {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s args : BitVec 64} {n : Nat}
    (h2 : R 2 = s + 18446744073709551536#64) (h10 : R 10 ≠ 0#64)
    (hs1 : 0x87800000 + 80 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0) :
    IW live ∅ [] (npF s args n) Q 0x80002e48#64 R M
  by
    have hsf : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
      rw [BitVec.toNat_add]; simp; omega
    ix_run1 hlive using [h2, hsf] at 0x80002e58

/- The epilogue, after `value_null`. -/
#ix_seg na_epi {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s args r v8 v9 v18 : BitVec 64} {n : Nat}
    (h2 : R 2 = s + 18446744073709551536#64)
    (hs1 : 0x87800000 + 80 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : r.toNat % 4 = 0)
    (hra : ldv .ld M (s + 18446744073709551536#64 + 72#64).toNat = r)
    (hs0 : ldv .ld M (s + 18446744073709551536#64 + 64#64).toNat = v8)
    (hs1' : ldv .ld M (s + 18446744073709551536#64 + 56#64).toNat = v9)
    (hs2' : ldv .ld M (s + 18446744073709551536#64 + 48#64).toNat = v18) :
    IW live ∅ [] (npF s args n) Q 0x80002e5c#64 R M
  by
    ix_run1 hlive using [h2, hal, hra, hs0, hs1', hs2']

/- After `value_truthy`, falsy, one argument: to `jal runtime_error` with
`"assertion failed"`. -/
#ix_seg na_fail1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s args : BitVec 64} {n : Nat}
    (h2 : R 2 = s + 18446744073709551536#64) (h10 : R 10 = 0#64)
    (hs1 : 0x87800000 + 80 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (ha : ldv .ld M (s.toNat - 80) = args) (hc8 : ldv .ld M (s.toNat - 80 + 8) = 1#64) :
    IW live ∅ [] (npF s args n) Q 0x80002e48#64 R M
  by
    have hsf : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
      rw [BitVec.toNat_add]; simp; omega
    have hs8 : (s + 18446744073709551536#64 + 8#64).toNat = s.toNat - 80 + 8 := by
      rw [BitVec.toNat_add, hsf]; simp; omega
    ix_run1 hlive using [h2, h10, hsf, hs8, ha, hc8] at 0x80002ebc
    all_goals first
      | (intro hc; exfalso; apply hc; ix_reg; exact h10)
      | (intro _; ix_run1 hlive using [h2, h10, hsf, hs8, ha, hc8] at 0x80002ebc)

/- Falsy, two arguments, the second a string: its payload is the message. -/
#ix_seg na_fail2s {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s args pw : BitVec 64} {n : Nat}
    (h2 : R 2 = s + 18446744073709551536#64) (h10 : R 10 = 0#64)
    (hs1 : 0x87800000 + 80 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (ha2 : 0x8001ad00 + 16 ≤ args.toNat) (ha3 : args.toNat + 48 ≤ 0x100000000)
    (ha1 : args.toNat % 8 = 0) (hn : 2 ≤ n)
    (ha : ldv .ld M (s.toNat - 80) = args) (hc8 : ldv .ld M (s.toNat - 80 + 8) = 2#64)
    (hk : ldv .lw M (args + 24#64).toNat = 3#64) (hp : ldv .ld M (args + 32#64).toNat = pw) :
    IW live ∅ [] (npF s args n) Q 0x80002e48#64 R M
  by
    have hsf : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
      rw [BitVec.toNat_add]; simp; omega
    have hs8 : (s + 18446744073709551536#64 + 8#64).toNat = s.toNat - 80 + 8 := by
      rw [BitVec.toNat_add, hsf]; simp; omega
    ix_run1 hlive using [h2, h10, hsf, hs8, ha, hc8, hk, hp] at 0x80002ebc
    iterate 4 all_goals first
      | (intro hc; exfalso; apply hc; ix_reg; exact h10)
      | (intro hc; exfalso; revert hc; ix_reg; done)
      | (intro hc; exfalso; revert hc; ix_reg; exact hk3)
      | (intro _; ix_run1 hlive using [h2, h10, hsf, hs8, ha, hc8, hk, hp] at 0x80002ebc)
      | skip

/- Falsy, two arguments, the second not a string: `"assertion failed"`. -/
#ix_seg na_fail2o {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s args kw : BitVec 64} {n : Nat}
    (h2 : R 2 = s + 18446744073709551536#64) (h10 : R 10 = 0#64)
    (hs1 : 0x87800000 + 80 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (ha2 : 0x8001ad00 + 16 ≤ args.toNat) (ha3 : args.toNat + 48 ≤ 0x100000000)
    (ha1 : args.toNat % 8 = 0) (hn : 2 ≤ n)
    (ha : ldv .ld M (s.toNat - 80) = args) (hc8 : ldv .ld M (s.toNat - 80 + 8) = 2#64)
    (hk : ldv .lw M (args + 24#64).toNat = kw) (hk3 : kw ≠ 3#64) :
    IW live ∅ [] (npF s args n) Q 0x80002e48#64 R M
  by
    have hsf : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
      rw [BitVec.toNat_add]; simp; omega
    have hs8 : (s + 18446744073709551536#64 + 8#64).toNat = s.toNat - 80 + 8 := by
      rw [BitVec.toNat_add, hsf]; simp; omega
    ix_run1 hlive using [h2, h10, hsf, hs8, ha, hc8, hk] at 0x80002ebc
    iterate 4 all_goals first
      | (intro hc; exfalso; apply hc; ix_reg; exact h10)
      | (intro hc; exfalso; revert hc; ix_reg; done)
      | (intro hc; exfalso; revert hc; ix_reg; exact hk3)
      | (intro _; ix_run1 hlive using [h2, h10, hsf, hs8, ha, hc8, hk] at 0x80002ebc)
      | skip


/-! ## `runtime_error`'s messages -/

/-- `"assert() takes 1 or 2 arguments"` (`.rodata` `0x80019350`). -/
def naArityBytes : List (BitVec 8) := [0x61#8, 0x73#8, 0x73#8, 0x65#8, 0x72#8, 0x74#8, 0x28#8,
  0x29#8, 0x20#8, 0x74#8, 0x61#8, 0x6b#8, 0x65#8, 0x73#8, 0x20#8, 0x31#8, 0x20#8, 0x6f#8, 0x72#8,
  0x20#8, 0x32#8, 0x20#8, 0x61#8, 0x72#8, 0x67#8, 0x75#8, 0x6d#8, 0x65#8, 0x6e#8, 0x74#8, 0x73#8]

/-- `"assertion failed"` (`.rodata` `0x80019338`). -/
def naFailBytes : List (BitVec 8) := [0x61#8, 0x73#8, 0x73#8, 0x65#8, 0x72#8, 0x74#8, 0x69#8,
  0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8, 0x64#8]

theorem naArity_fmt {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) (x1 x2 : BitVec 64) :
    FmtArgsOK R rd 0x80019350#64 [x1, x2] :=
  ⟨naArityBytes, [], ⟨cstrCov_rodata hro (by decide) (by decide), by decide, by simp,
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩

/-- A C string's bytes, read through any `rd` that agrees with its image. -/
theorem cstrCov_of_img {R : Nat → Prop} {rd : Nat → BitVec 8} {p : Nat} {x : String}
    (hR : ∀ i, i ≤ x.toList.length → R (p + i)) (hc : CStrImg rd p x) :
    CStrCov R rd p (x.toList.map fun c => BitVec.ofNat 8 c.toNat) where
  bytes i h := by
    simp only [List.length_map] at h
    obtain ⟨e, h1, h2⟩ := hc.1 i h
    refine ⟨hR i (by omega), by simp [e], ?_⟩
    simp only [List.getElem_map]
    intro h0
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    simp at this; omega
  nul := by
    simp only [List.length_map]
    exact ⟨hR _ (Nat.le_refl _), hc.2⟩

/-- `"%s"` with a C string argument. -/
theorem naS_fmt {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) {x1 : BitVec 64}
    (hs : ∃ t, CStrCov R rd x1.toNat t) (x2 : BitVec 64) :
    FmtArgsOK R rd 0x80019038#64 [x1, x2] := by
  refine ⟨[0x25#8, 0x73#8], [.str], ⟨cstrCov_rodata hro (by decide) (by decide), by decide,
    by simp, ?_⟩⟩
  intro i hi _
  have : i = 0 := by simpa using hi
  subst this
  exact hs

/-- The default message is a `.rodata` C string. -/
theorem naFail_str {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) :
    ∃ t, CStrCov R rd (0x80019338#64 : BitVec 64).toNat t :=
  ⟨naFailBytes, cstrCov_rodata hro (by decide) (by decide)⟩

/-! ## The Iris glue -/

section Glue

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

omit I in
/-- `native_assert`'s frame out of the stack below `s`: `runtime_error`'s
stack below it. -/
theorem naFrame_split {s : BitVec 64} (hs : nativeAssertNeed ≤ s.toNat) :
    stackScratch (GF := GF) s nativeAssertNeed ⊢
      stackScratch (s + 18446744073709551536#64) RtErr.rtErrNeed ∗
        ownSet (InExt (s.toNat - 80, 80)) byteAny := by
  have h := stackScratch_frame (GF := GF) (s := s) (f := 80#64) (n := nativeAssertNeed) hs
    (by unfold nativeAssertNeed; simp)
  have hsm : s - 80#64 = s + 18446744073709551536#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have e : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
    unfold nativeAssertNeed at hs; rw [BitVec.toNat_add]; simp; omega
  rw [hsm, e, show (80#64 : BitVec 64).toNat = 80 from rfl,
    show nativeAssertNeed - 80 = RtErr.rtErrNeed by unfold nativeAssertNeed; omega] at h
  unfold blockOwn at h
  exact h

omit I in
/-- And back. -/
theorem naFrame_join {s : BitVec 64} (hs : nativeAssertNeed ≤ s.toNat) :
    stackScratch (GF := GF) (s + 18446744073709551536#64) RtErr.rtErrNeed ∗
        ownSet (InExt (s.toNat - 80, 80)) byteAny ⊢ stackScratch s nativeAssertNeed := by
  have h := stackScratch_unframe (GF := GF) (s := s) (f := 80#64) (n := nativeAssertNeed) hs
    (by unfold nativeAssertNeed; simp)
  have hsm : s - 80#64 = s + 18446744073709551536#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have e : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
    unfold nativeAssertNeed at hs; rw [BitVec.toNat_add]; simp; omega
  rw [hsm, e, show (80#64 : BitVec 64).toNat = 80 from rfl,
    show nativeAssertNeed - 80 = RtErr.rtErrNeed by unfold nativeAssertNeed; omega] at h
  unfold blockOwn at h
  exact h

omit I in
/-- A run's owned bytes without an empty set. -/
theorem ownImg_none (img : Nat → BitVec 8) : ⊢ ownImg (GF := GF) (fun _ => False) img := by
  unfold ownImg ownSet
  iexists []
  isplitr
  · ipureintro; exact ⟨List.nodup_nil, fun k => by simp⟩
  · simp only [sepL_nil]; iempintro

omit I in
/-- `.rodata` alone is readable. -/
theorem readable_rodata : binImg (GF := GF) ⊢ readable rodataDom (fun _ => False) rodataByte := by
  unfold binImg readable
  iintro ⟨-, #H⟩
  iframe H
  iapply ownImg_none

omit I in
theorem roImg_sub {S T : Nat → Prop} {f : Nat → BitVec 8} (h : ∀ k, T k → S k) :
    roImg (GF := GF) S f ⊢ roImg T f := by
  unfold roImg
  iintro #H
  imodintro
  iintro %k %hk
  iapply H $$ %k %(h k hk)

omit I in
/-- `.rodata` and a C string are readable at one image. -/
theorem readable_str {p : Nat} {x : String} :
    binImg (GF := GF) ∗ strAt p x ⊢ ∃ rd : Nat → BitVec 8,
      readable (fun a => rodataDom a ∨ InExt (p, x.toList.length + 1) a) (fun _ => False) rd ∗
      ⌜(∀ a, rodataDom a → rd a = rodataByte a) ∧ CStrImg rd p x⌝ := by
  classical
  unfold binImg strAt
  iintro ⟨⟨-, #Hr⟩, ⟨%img, %hc, #Hs⟩⟩
  ihave #Hr' := roImg_sub (T := fun a => rodataDom a ∧ InExt (p, x.toList.length + 1) a)
    (fun k h => h.1) $$ Hr
  ihave #Hs' := roImg_sub (T := fun a => rodataDom a ∧ InExt (p, x.toList.length + 1) a)
    (fun k h => h.2) $$ Hs
  ihave %hag := roImg_agree $$ [Hr' Hs']
  · isplitl
    · iexact Hr'
    · iexact Hs'
  iexists (fun a => if InExt (p, x.toList.length + 1) a then img a else rodataByte a)
  isplitl
  · unfold readable
    isplitl
    · unfold roImg
      imodintro
      iintro %k %hk
      by_cases hin : InExt (p, x.toList.length + 1) k
      · simp only [hin, ite_true]
        iapply Hs $$ %k %hin
      · simp only [hin, ite_false]
        iapply Hr $$ %k %(hk.resolve_right hin)
    · iapply ownImg_none
  · ipureintro
    refine ⟨fun a ha => ?_, ⟨fun i hi => ?_, ?_⟩⟩
    · by_cases hin : InExt (p, x.toList.length + 1) a
      · simp only [hin, ite_true]; exact (hag a ⟨ha, hin⟩).symm
      · simp only [hin, ite_false]
    · have hin : InExt (p, x.toList.length + 1) (p + i) := by simp only [InExt]; omega
      simp only [hin, ite_true]; exact hc.1 i hi
    · have hin : InExt (p, x.toList.length + 1) (p + x.toList.length) := by
        simp only [InExt]; omega
      simp only [hin, ite_true]; exact hc.2

/-- **A value slot out of a run's owned bytes**: the slot's three words are
those of a value's image, so the slot is the value. -/
theorem ms_carveVal (N : NativeAddrs) {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop}
    {M : Mem} {a b : Nat} {img : Nat → BitVec 8} {v : Value} (hS : ∀ k, InExt (a, 24) k → S k)
    (h0 : imgW (imgM M) a = imgW img b) (h8 : imgW (imgM M) (a + 8) = imgW img (b + 8))
    (h16 : imgW (imgM M) (a + 16) = imgW img (b + 16)) :
    ms (GF := GF) pc R S M ∗ valImg N img b v ⊢
      ms pc R (fun k => S k ∧ ¬ InExt (a, 24) k) M ∗ valAt N a v := by
  have hsl : ∀ k, S k ↔ ((S k ∧ ¬ InExt (a, 24) k) ∨ InExt (a, 24) k) := fun k => by
    constructor
    · intro h; by_cases h' : InExt (a, 24) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hS k h
  iintro ⟨Hms, #Hv⟩
  ihave Hms := ms_iff hsl $$ Hms
  ihave ⟨Hms, Hslot⟩ := ms_split (fun k h1 h2 => h1.2 h2) $$ Hms
  iframe Hms
  rw [← valImg_words (GF := GF) (N := N) (v := v) h0 h8 h16]
  iapply valAt_of_img N
  iframe Hv Hslot

/-- And back in: the run's other bytes unchanged. -/
theorem ms_uncarveVal (N : NativeAddrs) {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop}
    {M : Mem} {a : Nat} {v : Value} (hS : ∀ k, InExt (a, 24) k → S k) :
    ms (GF := GF) pc R (fun k => S k ∧ ¬ InExt (a, 24) k) M ∗ valAt N a v ⊢
      ∃ M', ms pc R S M' ∗ ⌜∀ k, S k → ¬ InExt (a, 24) k → imgM M' k = imgM M k⌝ := by
  have hsl : ∀ k, ((S k ∧ ¬ InExt (a, 24) k) ∨ InExt (a, 24) k) ↔ S k := fun k => by
    constructor
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hS k h
    · intro h; by_cases h' : InExt (a, 24) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
  iintro ⟨Hms, Hval⟩
  ihave ⟨%Ms, HsS, -⟩ := valAt_tracked N _ _ $$ Hval
  ihave ⟨%M', Hms, %⟨h1, -, -⟩⟩ := ms_join $$ [Hms HsS]
  · iframe Hms HsS
  iexists M'
  isplitl
  · iapply ms_iff hsl $$ Hms
  · ipureintro; exact fun k hk hn => h1 k ⟨hk, hn⟩

/-- The registers and memory at a `native_assert` `jal runtime_error`:
`runtime_error(in, line, fmt, x1, 0)` with `sp = s - 80`, the arguments'
bytes unchanged. -/
structure NaRtErrAt (R : Nat → BitVec 64) (M Margs : Mem) (inp line fmt x1 s args : BitVec 64)
    (n : Nat) : Prop where
  h10 : R 10 = inp
  h11 : R 11 = line
  h12 : R 12 = fmt
  h13 : R 13 = x1
  h14 : R 14 = 0#64
  h2 : R 2 = s + 18446744073709551536#64
  hargs : ∀ k, InExt (args.toNat, 24 * n) k → imgM M k = imgM Margs k

/-- **`runtime_error` from a `native_assert` run** (`jal` at `i`, `sp = s - 80`):
it never returns; on abort, H5's resource at `runtime_error`'s stack becomes
`native_assert`'s: the frame rejoins the stack below `s`, the arguments'
bytes rejoin their meanings, the result slot is handed back. -/
theorem na_rtErr (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} (HN : NewlibHoles) (hcl : CodeLive live)
    {i : Nat} {code : List (BitVec 8)} (hexec : JalExec (vsaModel live) i code RtErr.rtErrEntry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    {sret inp args s line fmt x1 : BitVec 64} {n : Nat} {vs : List Value} {ρ : Regime} {st : St}
    {d : Nat} {jb : Nat → BitVec 8} {Sro : Nat → Prop} {rd : Nat → BitVec 8}
    (hfmt : FmtArgsOK (fun a => Sro a ∨ False) rd fmt [x1, 0#64])
    (hinp : RtErr.InpGeom inp) (hjb : (jbWord inp.toNat jb 0).toNat % 4 = 0)
    (hs1 : 0x87800000 + nativeAssertNeed ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000)
    (hs3 : s.toNat % 16 = 0) (hlen : vs.length = n)
    (hdfa : ∀ k, InExt (s.toNat - 80, 80) k → ¬ InExt (args.toNat, 24 * n) k)
    {R : Nat → BitVec 64} {M Margs : Mem} :
    ⌜NaRtErrAt R M Margs inp line fmt x1 s args n⌝ ∗
      codeRes ∗ binImg ∗ ms (BitVec.ofNat 64 i) R (npF s args n) M ∗
      stackScratch (s + 18446744073709551536#64) RtErr.rtErrNeed ∗
      readable Sro (fun _ => False) rd ∗ jmpRO inp.toNat jb ∗ world N L Room inp.toNat ρ st d ∗
      slot24 sret.toNat ∗ valsImg N (imgM Margs) args.toNat vs ∗
      (abortRes N L Room inp.toNat s nativeAssertNeed ∗ slot24 sret.toNat ∗
        valsAt N args.toNat vs -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨%hR, #Hcode, #Himg, Hms, Hst, Hrd, #Hjb, Hw, Hsl, #Hv, Hab⟩
  obtain ⟨hR10, hR11, hR12, hR13, hR14, hR2, hargs⟩ := hR
  unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed at hs1
  have e80 : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
    rw [BitVec.toNat_add]; simp; omega
  have hsp : SpIn (s + 18446744073709551536#64) RtErr.rtErrNeed :=
    ⟨by rw [e80]; unfold RtErr.rtErrNeed snprintfNeed Vsa.Sim.tohostAddr; omega,
      by rw [e80]; omega, by rw [e80]; omega⟩
  ihave #Hspec := RtErr.rtErr_spec HN live hcl Wp N L Room inp (s + 18446744073709551536#64) line
    fmt x1 0#64 R Sro (fun _ => False) rd jb ρ st d hsp hinp hfmt hjb
  ihave #Hgp := codeRes_gp $$ Hcode
  iapply ms_callNewlibAbort Wp hexec hcode (vs := [inp, line, fmt, x1, 0#64])
    (P := fun _ => iprop(argsAt [inp, line, fmt, x1, 0#64] ∗
      callFrame (s + 18446744073709551536#64) RtErr.rtErrNeed Newlib.calleeSaved R ∗
      readable Sro (fun _ => False) rd ∗ jmpRO inp.toNat jb ∗ world N L Room inp.toNat ρ st d))
    (Q := fun _ => iprop(False))
    (A := abortRes N L Room inp.toNat (s + 18446744073709551536#64) RtErr.rtErrNeed)
    (X := iprop(readable Sro (fun _ => False) rd ∗ jmpRO inp.toNat jb ∗
      world N L Room inp.toNat ρ st d)) (Y := iprop(False))
    (need := RtErr.rtErrNeed) (n := RtErr.rtErrNeed) (by simp)
    (fun j hj => by
      simp only [List.length_cons, List.length_nil] at hj
      rcases j with _ | _ | _ | _ | _ | j
      · exact hR10
      · exact hR11
      · exact hR12
      · exact hR13
      · exact hR14
      · omega)
    hR2 (by rw [e80]; unfold RtErr.rtErrNeed snprintfNeed; omega) (Nat.le_refl _)
    (fun r => by iintro ⟨Ha, ⟨Hr, Hj, Hw⟩, Hf⟩; iframe Ha Hf Hr Hj Hw)
    (fun r => by iintro H; iexfalso; iexact H)
  iframe Hspec Hcode Hms Hst Hgp Himg Hrd Hjb Hw
  isplit
  · iintro %R' %_ Hf
    iexfalso; iexact Hf
  · iintro HA - HS
    unfold abortRes abortAt
    icases HA with ⟨Hcore, Hst⟩
    ihave Hcore := abortCore_mono N L Room inp.toNat (sc := s + 18446744073709551536#64)
      (sp := s) (nc := RtErr.rtErrNeed) (np := nativeAssertNeed)
      (by unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed; omega)
      (by unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed Vsa.Sim.tohostAddr; omega)
      (by rw [e80]; unfold nativeAssertNeed; omega) (by rw [e80]; omega) hs2 $$ Hcore
    ihave ⟨HF, HA⟩ := ownSet_split_tracked _ _ M hdfa $$ HS
    ihave HF := ownSet_forget _ _ $$ HF
    ihave Hst := naFrame_join (s := s) (by unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed; omega)
      $$ [Hst HF]
    · iframe Hst HF
    subst hlen
    ihave #Hv' := valsImg_agree N vs args.toNat (fun k hk => (hargs k hk).symm) $$ Hv
    ihave Hvs := valsAt_of_tracked N M vs args.toNat $$ [HA Hv']
    · iframe HA Hv'
    iapply Hab
    iframe Hsl Hvs Hcore Hst

/-- `native_assert`'s continuation pair (its `fnSpecAbort` post and abort). -/
abbrev NaK (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (sret inp args s r : BitVec 64)
    (vs : List Value) (ρ : Regime) (st : St) (d : Nat) (rv : Nat → BitVec 64) : IProp GF :=
  iprop((PC ↦ᵣ r -∗ ra ↦ᵣ r -∗
      (∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = rv x⌝ ∗
        ⌜∃ v m, (vs = [v] ∨ vs = [v, m]) ∧ v.truthy = true⌝ ∗ valAt N sret.toNat .null ∗
        valsAt N args.toNat vs ∗ world N L Room inp.toNat ρ st d ∗
        stackAt s nativeAssertNeed) -∗ Wp.W Φ) ∧
    (abortRes N L Room inp.toNat s nativeAssertNeed ∗ slot24 sret.toNat ∗
      valsAt N args.toNat vs -∗ Wp.W Φ))

/-- What a `native_assert` run carries. -/
def NaRest (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (sret inp args s r : BitVec 64)
    (vs : List Value) (ρ : Regime) (st : St) (d : Nat) (rv : Nat → BitVec 64)
    (jb : Nat → BitVec 8) (Margs : Mem) : IProp GF :=
  iprop(codeRes ∗ binImg ∗ slot24 sret.toNat ∗ valsImg N (imgM Margs) args.toNat vs ∗
    jmpRO inp.toNat jb ∗ world N L Room inp.toNat ρ st d ∗
    stackScratch (s + 18446744073709551536#64) RtErr.rtErrNeed ∗
    NaK Wp Φ N L Room sret inp args s r vs ρ st d rv)

/-- The shared pure facts of a `native_assert` run. -/
structure NaCtx (live : Nat → Prop) (sret inp args s line r : BitVec 64) (n : Nat)
    (rv : Nat → BitVec 64) (jb : Nat → BitVec 8) : Prop where
  hlive : ∀ p ∈ interpText, live p.1
  hal : r.toNat % 4 = 0
  h10 : rv 10 = sret
  h11 : rv 11 = inp
  h12 : rv 12 = BitVec.ofNat 64 n
  h13 : rv 13 = args
  h14 : rv 14 = line
  h2 : rv 2 = s
  hs1 : 0x87800000 + nativeAssertNeed ≤ s.toNat
  hs2 : s.toNat ≤ 0x88000000
  hs3 : s.toNat % 16 = 0
  hg : SlotGeom sret
  ha : ArgsGeom args n
  hn : n < 2 ^ 31
  hinp : RtErr.InpGeom inp
  hjb : (jbWord inp.toNat jb 0).toNat % 4 = 0
  hdfa : ∀ k, InExt (s.toNat - 80, 80) k → ¬ InExt (args.toNat, 24 * n) k

/-- **Wrong argument count**: the arity message through `runtime_error`. -/
theorem na_badPath (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} (HN : NewlibHoles) (hcl : CodeLive live)
    {sret inp args s line r : BitVec 64} {n : Nat} {vs : List Value} {ρ : Regime} {st : St}
    {d : Nat} {jb : Nat → BitVec 8} {rv : Nat → BitVec 64} {M Margs : Mem}
    (c : NaCtx live sret inp args s line r n rv jb) (hlen : vs.length = n)
    (hbad : ¬ (n = 1 ∨ n = 2))
    (hargs : ∀ k, InExt (args.toNat, 24 * n) k → imgM M k = imgM Margs k) :
    NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs ∗
      ms nativeAssertPC (upd rv 1 r) (npF s args n) M ⊢ Wp.W Φ := by
  have hs1 := c.hs1; have hs2 := c.hs2; have hs3 := c.hs3
  unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hoff : ∀ k, k < 80 → (s + 18446744073709551536#64 + BitVec.ofNat 64 k).toNat =
      s.toNat - 80 + k := by
    intro k hk; rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  iintro ⟨Hrest, Hms⟩
  iapply wp_swpF Wp (S := npF s args n) (R := upd rv 1 r) (Mt := M) (pc := nativeAssertPC)
    (F := NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs)
  rotate_left
  · unfold NaRest
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  refine na_bad c.hlive c.h12 c.h2 (by omega) hs2 hs3 hbad c.hn ?_
  intros; apply swp_closeF
  dsimp only [F']
  unfold NaRest
  iintro ⟨⟨#Hcode, #Himg, Hsl, #Hv, #Hjb, Hw, Hst, Hk⟩, Hms⟩
  ihave #Hrd := readable_rodata $$ Himg
  ihave Hk := and_elim_r $$ Hk
  iapply (na_rtErr Wp HN hcl (jalx_80002e90 live (fun p hp => c.hlive _ (interp_code_80002e90 p hp)))
    interp_code_80002e90 (naArity_fmt (fun a ha => ⟨.inl ha, rfl⟩) 0#64 0#64) c.hinp c.hjb c.hs1 hs2 hs3
    hlen c.hdfa)
  iframe Hcode Himg Hms Hst Hrd Hjb Hw Hsl Hv Hk
  ipureintro
  refine ⟨by ix_reg; exact c.h11, by ix_reg; exact c.h14, by ix_reg, by ix_reg, by ix_reg,
    by ix_reg, fun k hk => ?_⟩
  have hk' := c.hdfa k
  simp only [InExt] at hk hk'
  simp only [hoff 72 (by omega), hoff 64 (by omega), hoff 56 (by omega), hoff 48 (by omega)]
  simp (disch := omega) only [imgM_store_miss]
  exact hargs k hk

end Glue

end VsaIris.Interp
