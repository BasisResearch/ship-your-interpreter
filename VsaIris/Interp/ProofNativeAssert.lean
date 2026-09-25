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
  iintro ⟨⟨-, #Hr⟩, ⟨%img, %⟨hc, -⟩, #Hs⟩⟩
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
    (A := iprop(abortRes N L Room inp.toNat (s + 18446744073709551536#64) RtErr.rtErrNeed ∗
      readable Sro (fun _ => False) rd))
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
  · iintro ⟨HA, -⟩ - HS
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
    (⌜¬ AssertOk vs⌝ ∗ abortRes N L Room inp.toNat s nativeAssertNeed ∗ slot24 sret.toNat ∗
      valsAt N args.toNat vs -∗ Wp.W Φ))

/-- An abort continuation that wants the abort's reason, given it. -/
theorem wand_pure_apply {φ : Prop} {P Q : IProp GF} (h : φ) : iprop(⌜φ⌝ ∗ P -∗ Q) ⊢ iprop(P -∗ Q) := by
  iintro H HP
  iapply H
  iframe HP
  ipureintro; exact h

theorem not_assertOk_len {vs : List Value} (h : ¬ (vs.length = 1 ∨ vs.length = 2)) : ¬ AssertOk vs := by
  rintro ⟨v, m, (rfl | rfl), -⟩ <;> simp at h

theorem not_assertOk_falsy {vs : List Value} (h0 : 0 < vs.length) (ht : (vs[0]'h0).truthy = false) :
    ¬ AssertOk vs := by
  rintro ⟨v, m, (rfl | rfl), hv⟩ <;> simp_all

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
  hs4 : s.toNat ≤ Vsa.Sim.LayoutInstance.spEntry - Vsa.Sim.LayoutInstance.interpRunFrame
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
  ihave Hk := wand_pure_apply (not_assertOk_len (by rw [hlen]; exact hbad)) $$ Hk
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

/-- The state after `value_truthy` returns (`0x80002e48`): its answer in `a0`,
the saved registers, the frame's words, the arguments' bytes. -/
structure NaFacts (sret inp args s line r : BitVec 64) (n : Nat) (v : Value)
    (rv R : Nat → BitVec 64) (M Margs : Mem) : Prop where
  h10 : R 10 = if v.truthy then 1#64 else 0#64
  h2 : R 2 = s + 18446744073709551536#64
  h8 : R 8 = sret
  h9 : R 9 = inp
  h18 : R 18 = line
  hk : ∀ x ∈ fRegs, x ∉ callerSaved → x ∉ [2, 8, 9, 18] → R x = rv x
  sa : ldv .ld M (s.toNat - 80) = args
  sc : ldv .ld M (s.toNat - 80 + 8) = BitVec.ofNat 64 n
  sra : ldv .ld M (s + 18446744073709551536#64 + 72#64).toNat = r
  ss0 : ldv .ld M (s + 18446744073709551536#64 + 64#64).toNat = rv 8
  ss1 : ldv .ld M (s + 18446744073709551536#64 + 56#64).toNat = rv 9
  ss2 : ldv .ld M (s + 18446744073709551536#64 + 48#64).toNat = rv 18
  hargs : ∀ k, InExt (args.toNat, 24 * n) k → imgM M k = imgM Margs k

/-- **One or two arguments**: the prologue, the copy of the first argument,
`value_truthy` on it, the copy back into the frame. -/
theorem na_head (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred}
    {sret inp args s line r : BitVec 64} {n : Nat} {vs : List Value} {ρ : Regime} {st : St}
    {d : Nat} {jb : Nat → BitVec 8} {rv : Nat → BitVec 64} {M Margs : Mem}
    (c : NaCtx live sret inp args s line r n rv jb) (hlen : vs.length = n)
    (hok : n = 1 ∨ n = 2)
    (hargs : ∀ k, InExt (args.toNat, 24 * n) k → imgM M k = imgM Margs k)
    (hB : ∀ R' M', NaFacts sret inp args s line r n (vs[0]'(by omega)) rv R' M' Margs →
      NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs ∗
        ms 0x80002e48#64 R' (npF s args n) M' ⊢ Wp.W Φ) :
    NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs ∗
      ms nativeAssertPC (upd rv 1 r) (npF s args n) M ⊢ Wp.W Φ := by
  have hs1 := c.hs1; have hs2 := c.hs2; have hs3 := c.hs3
  unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed at hs1
  have ha1 := c.ha.al; have ha2 := c.ha.lo; have ha3 := c.ha.hi
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hoff : ∀ k, k < 80 → (s + 18446744073709551536#64 + BitVec.ofNat 64 k).toNat =
      s.toNat - 80 + k := by
    intro k hk; rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  have e80 : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
    rw [BitVec.toNat_add]; simp; omega
  have eA : ∀ k, k < 24 → (args + BitVec.ofNat 64 k).toNat = args.toNat + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show args.toNat + k < 2 ^ 64 by omega)]
  -- the prologue's stores leave the arguments' words
  have hA1 : ∀ k, InExt (args.toNat, 24 * n) k →
      imgM (writeLog (writeLog (writeLog (writeLog M
        [((s + 18446744073709551536#64 + 56#64).toNat, 8, rv 9)])
        [((s + 18446744073709551536#64 + 48#64).toNat, 8, rv 18)])
        [((s + 18446744073709551536#64 + 72#64).toNat, 8, r)])
        [((s + 18446744073709551536#64 + 64#64).toNat, 8, rv 8)]) k = imgM Margs k := by
    intro k hk
    have hk' := c.hdfa k
    simp only [InExt] at hk hk'
    simp only [hoff 72 (by omega), hoff 64 (by omega), hoff 56 (by omega), hoff 48 (by omega)]
    simp (disch := omega) only [imgM_store_miss]
    exact hargs k hk
  have hw : ∀ o, o ≤ 16 → ldv .ld (writeLog (writeLog (writeLog (writeLog M
        [((s + 18446744073709551536#64 + 56#64).toNat, 8, rv 9)])
        [((s + 18446744073709551536#64 + 48#64).toNat, 8, rv 18)])
        [((s + 18446744073709551536#64 + 72#64).toNat, 8, r)])
        [((s + 18446744073709551536#64 + 64#64).toNat, 8, rv 8)]) (args.toNat + o) =
      imgW (imgM Margs) (args.toNat + o) := fun o ho => by
    rw [ldv_ld_imgW]
    exact imgW_agree fun j hj => hA1 _ (by simp only [InExt]; omega)
  iintro ⟨Hrest, Hms⟩
  iapply wp_swpF Wp (S := npF s args n) (R := upd rv 1 r) (Mt := M) (pc := nativeAssertPC)
    (F := NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs)
  rotate_left
  · unfold NaRest
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  refine na_pro c.hlive c.h12 c.h2 (by omega) hs2 hs3 hok ?_
  intros
  refine na_copy c.hlive (w0 := imgW (imgM Margs) args.toNat)
    (w1 := imgW (imgM Margs) (args.toNat + 8)) (w2 := imgW (imgM Margs) (args.toNat + 16))
    (by ix_reg; exact c.h13) (by ix_reg) (by omega) hs2 hs3 (by omega) ha1
    (by unfold Vsa.Sim.tohostAddr at ha2; omega) ha3 (by have h := hw 0 (by omega); rw [Nat.add_zero] at h; exact h)
    (by rw [eA 8 (by omega)]; exact hw 8 (by omega)) (by rw [eA 16 (by omega)]; exact hw 16 (by omega)) ?_
  intros; apply swp_closeF
  dsimp only [F']
  unfold NaRest
  iintro ⟨⟨#Hcode, #Himg, Hsl, #Hv, #Hjb, Hw, Hst, Hk⟩, Hms⟩
  rw [hoff 16 (by omega), hoff 24 (by omega), hoff 32 (by omega)]
  -- the copy slot holds the first argument's words
  have hv0 : ∀ M0 : Mem, imgW (imgM (writeLog (writeLog (writeLog M0
      [(s.toNat - 80 + 16, 8, imgW (imgM Margs) args.toNat)])
      [(s.toNat - 80 + 24, 8, imgW (imgM Margs) (args.toNat + 8))])
      [(s.toNat - 80 + 32, 8, imgW (imgM Margs) (args.toNat + 16))])) (s.toNat - 80 + 16) =
      imgW (imgM Margs) args.toNat := fun M0 => by
    rw [imgW_store_miss _ _ (by omega), imgW_store_miss _ _ (by omega), imgW_store_hit]
  have hv8 : ∀ M0 : Mem, imgW (imgM (writeLog (writeLog (writeLog M0
      [(s.toNat - 80 + 16, 8, imgW (imgM Margs) args.toNat)])
      [(s.toNat - 80 + 24, 8, imgW (imgM Margs) (args.toNat + 8))])
      [(s.toNat - 80 + 32, 8, imgW (imgM Margs) (args.toNat + 16))])) (s.toNat - 80 + 16 + 8) =
      imgW (imgM Margs) (args.toNat + 8) := fun M0 => by
    rw [show s.toNat - 80 + 16 + 8 = s.toNat - 80 + 24 by omega, imgW_store_miss _ _ (by omega),
      imgW_store_hit]
  have hv16 : ∀ M0 : Mem, imgW (imgM (writeLog (writeLog (writeLog M0
      [(s.toNat - 80 + 16, 8, imgW (imgM Margs) args.toNat)])
      [(s.toNat - 80 + 24, 8, imgW (imgM Margs) (args.toNat + 8))])
      [(s.toNat - 80 + 32, 8, imgW (imgM Margs) (args.toNat + 16))])) (s.toNat - 80 + 16 + 16) =
      imgW (imgM Margs) (args.toNat + 16) := fun M0 => by
    rw [show s.toNat - 80 + 16 + 16 = s.toNat - 80 + 32 by omega, imgW_store_hit]
  have hsl : ∀ k, InExt (s.toNat - 80 + 16, 24) k → npF s args n k := fun k hk =>
    .inl (by simp only [InExt] at hk ⊢; omega)
  ihave #Hv0 := valsImg_get N (imgM Margs) vs args.toNat 0 (by omega) $$ Hv
  rw [show args.toNat + 24 * 0 = args.toNat by omega]
  ihave ⟨Hms, Hval⟩ := ms_carveVal N (a := s.toNat - 80 + 16) (b := args.toNat) (img := imgM Margs)
    (v := vs[0]'(by omega)) hsl (hv0 _) (hv8 _) (hv16 _) $$ [Hms Hv0]
  · iframe Hms Hv0
  -- `value_truthy(sp + 16)`
  have e16 : (s + 18446744073709551536#64 + 16#64).toNat = s.toNat - 80 + 16 := hoff 16 (by omega)
  have hslg : SlotGeom (s + 18446744073709551536#64 + 16#64) :=
    ⟨by rw [e16]; omega, by rw [e16]; unfold Vsa.Sim.tohostAddr; omega, by rw [e16]; omega⟩
  ihave #Hvt := valueTruthy_spec c.hlive Wp N (s + 18446744073709551536#64 + 16#64) (vs[0]'(by omega))
  unfold valueTruthySpec
  iapply ms_callHelper Wp (i := 0x80002e44)
    (jalx_80002e44 live (fun p hp => c.hlive _ (interp_code_80002e44 p hp))) interp_code_80002e44
    (by decide) (clob := [10, 14, 15]) (pins := fun rv => rv 10 = s + 18446744073709551536#64 + 16#64)
    (Pre := iprop(valAt N (s + 18446744073709551536#64 + 16#64).toNat (vs[0]'(by omega)) ∗
      ⌜SlotGeom (s + 18446744073709551536#64 + 16#64)⌝))
    (Post := fun rv' => iprop(valAt N (s + 18446744073709551536#64 + 16#64).toNat (vs[0]'(by omega)) ∗
      ⌜rv' 10 = if (vs[0]'(by omega)).truthy then 1#64 else 0#64⌝))
  iframe Hcode Hms
  isplitl []
  · ipureintro; ix_reg
  isplitl []
  · iexact Hvt
  isplitl [Hval]
  · rw [e16]; iframe Hval; ipureintro; exact hslg
  iintro %R3 %hk3 ⟨Hval, %h10⟩ Hms
  rw [e16]
  ihave ⟨%M3, Hms, %hM3⟩ := ms_uncarveVal N hsl $$ [Hms Hval]
  · iframe Hms Hval
  iapply (hB (upd R3 1 (BitVec.ofNat 64 (0x80002e44 + 4))) M3 ?f)
  rotate_left
  · unfold NaRest
    iframe Hcode Himg Hsl Hv Hjb Hw Hst Hk Hms
  case f =>
    have k3 := fun x (hx : x ∈ fRegs) (hc : x ∉ [10, 14, 15]) => hk3 x hx hc
    have hfr : ∀ o, (o + 8 ≤ 16 ∨ 40 ≤ o) → o + 8 ≤ 80 → ∀ j, j < 8 →
        npF s args n (s.toNat - 80 + o + j) ∧ ¬ InExt (s.toNat - 80 + 16, 24) (s.toNat - 80 + o + j) :=
      fun o ho1 ho2 j hj => ⟨.inl (by simp only [InExt]; omega), by simp only [InExt]; omega⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · ix_reg; exact h10
    · ix_reg; rw [k3 2 (by decide) (by decide)]; ix_reg
    · ix_reg; rw [k3 8 (by decide) (by decide)]; ix_reg; exact c.h10
    · ix_reg; rw [k3 9 (by decide) (by decide)]; ix_reg; exact c.h11
    · ix_reg; rw [k3 18 (by decide) (by decide)]; ix_reg; exact c.h14
    · intro x hx hc hn
      have hx1 : x ≠ 1 := fun e => by subst e; revert hx; decide
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      obtain ⟨hx2, hx8, hx9, hx18⟩ := hn
      have hcl : ∀ y ∈ callerSaved, x ≠ y := fun y hy e => hc (e ▸ hy)
      have hx10 := hcl 10 (by decide); have hx11 := hcl 11 (by decide)
      have hx14 := hcl 14 (by decide); have hx15 := hcl 15 (by decide)
      have hx16 := hcl 16 (by decide)
      simp only [upd, hx1, ite_false]
      rw [k3 x hx (by simp [hx10, hx14, hx15])]
      simp only [upd, hx1, hx2, hx8, hx9, hx10, hx11, hx14, hx15, hx16, hx18, ite_false]
    · rw [show s.toNat - 80 = s.toNat - 80 + 0 by omega,
        ldv_agree fun j hj => hM3 _ (hfr 0 (by omega) (by omega) j hj).1 (hfr 0 (by omega) (by omega) j hj).2]
      simp only [Nat.add_zero, hoff 8 (by omega)]
      simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss, ldv_store_hit]
    · rw [ldv_agree fun j hj => hM3 _ (hfr 8 (by omega) (by omega) j hj).1 (hfr 8 (by omega) (by omega) j hj).2]
      simp only [hoff 8 (by omega)]
      simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss, ldv_store_hit]
      ix_reg; exact c.h12
    all_goals first
      | (intro k hk
         have hk' := c.hdfa k
         have hn' : ¬ InExt (s.toNat - 80 + 16, 24) k := fun h => hk' (by simp only [InExt] at h ⊢; omega) hk
         rw [hM3 k (.inr hk) hn']
         simp only [InExt] at hk hk'
         simp only [hoff 8 (by omega)]
         simp (disch := omega) only [imgM_store_miss]
         exact hA1 k hk)
      | (simp only [hoff 72 (by omega), hoff 64 (by omega), hoff 56 (by omega), hoff 48 (by omega)]
         rw [ldv_agree fun j hj => hM3 _ (hfr _ (by omega) (by omega) j hj).1 (hfr _ (by omega) (by omega) j hj).2]
         simp only [hoff 8 (by omega), hoff 72 (by omega), hoff 64 (by omega), hoff 56 (by omega),
           hoff 48 (by omega)]
         simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss, ldv_store_hit])

/-- One or two values, the first truthy: `Call.assertOk`'s premise. -/
theorem na_shape {vs : List Value} (h : vs.length = 1 ∨ vs.length = 2)
    (ht : (vs[0]'(by omega)).truthy = true) :
    ∃ v m, (vs = [v] ∨ vs = [v, m]) ∧ v.truthy = true := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at h
  · exact ⟨a, a, .inl rfl, ht⟩
  · exact ⟨a, b, .inr rfl, ht⟩
  · simp at h

/-- **Truthy**: `value_null(sret)`, the epilogue, the return with
`Call.assertOk`'s premise. -/
theorem na_truthyPath (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred}
    {sret inp args s line r : BitVec 64} {n : Nat} {vs : List Value} {ρ : Regime} {st : St}
    {d : Nat} {jb : Nat → BitVec 8} {rv R : Nat → BitVec 64} {M Margs : Mem}
    (c : NaCtx live sret inp args s line r n rv jb) (hlen : vs.length = n)
    (hok : n = 1 ∨ n = 2)
    (f : NaFacts sret inp args s line r n (vs[0]'(by omega)) rv R M Margs)
    (ht : (vs[0]'(by omega)).truthy = true) :
    NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs ∗
      ms 0x80002e48#64 R (npF s args n) M ⊢ Wp.W Φ := by
  have hs1 := c.hs1; have hs2 := c.hs2; have hs3 := c.hs3
  unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have h10 : R 10 ≠ 0#64 := by rw [f.h10, ht]; decide
  iintro ⟨Hrest, Hms⟩
  iapply wp_swpF Wp (S := npF s args n) (R := R) (Mt := M) (pc := 0x80002e48#64)
    (F := NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs)
  rotate_left
  · unfold NaRest
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  refine na_ok c.hlive f.h2 h10 (by omega) hs2 hs3 ?_
  intros; apply swp_closeF
  dsimp only [F']
  unfold NaRest
  iintro ⟨⟨#Hcode, #Himg, Hsl, #Hv, #Hjb, Hw, Hst, Hk⟩, Hms⟩
  -- `value_null(sret)`
  ihave #Hvn := valueNull_spec c.hlive Wp N sret
  unfold valueNullSpec
  iapply ms_callHelper Wp (i := 0x80002e58)
    (jalx_80002e58 live (fun p hp => c.hlive _ (interp_code_80002e58 p hp))) interp_code_80002e58
    (by decide) (clob := []) (pins := fun rv => rv 10 = sret)
    (Pre := iprop(slot24 sret.toNat ∗ ⌜SlotGeom sret⌝)) (Post := fun _ => valAt N sret.toNat .null)
  iframe Hcode Hms
  isplitl []
  · ipureintro; ix_reg; exact f.h8
  isplitl []
  · iexact Hvn
  isplitl [Hsl]
  · iframe Hsl; ipureintro; exact c.hg
  iintro %R5 %hk5 Hnull Hms
  have k5 : ∀ x ∈ fRegs, R5 x = _ := fun x hx => hk5 x hx (by simp)
  -- the epilogue
  iapply wp_swpF Wp (S := npF s args n) (R := upd R5 1 (BitVec.ofNat 64 (0x80002e58 + 4)))
    (Mt := M) (pc := 0x80002e5c#64)
    (F := iprop(codeRes ∗ valAt N sret.toNat .null ∗ valsImg N (imgM Margs) args.toNat vs ∗
      world N L Room inp.toNat ρ st d ∗ stackScratch (s + 18446744073709551536#64) RtErr.rtErrNeed ∗
      NaK Wp Φ N L Room sret inp args s r vs ρ st d rv))
  rotate_left
  · rw [hro]; iframe Hcode Hnull Hv Hw Hst Hk Hms
  intro F'
  refine na_epi c.hlive (by ix_reg; rw [k5 2 (by decide)]; ix_reg; exact f.h2) (by omega) hs2 hs3
    c.hal f.sra f.ss0 f.ss1 f.ss2 ?_
  intros; apply swp_closeF
  dsimp only [F']
  iintro ⟨⟨#Hcode, Hnull, #Hv, Hw, Hst, Hk⟩, Hms⟩
  unfold ms
  icases Hms with ⟨Hpc, Hra, Hregs, HS⟩
  ihave ⟨HF, HA⟩ := ownSet_split_tracked _ _ M c.hdfa $$ HS
  ihave HF := ownSet_forget _ _ $$ HF
  ihave Hst := naFrame_join (s := s)
    (by unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed; omega) $$ [Hst HF]
  · iframe Hst HF
  have hsh := na_shape (hlen ▸ hok) ht
  subst hlen
  ihave #Hv' := valsImg_agree N vs args.toNat (fun k hk => (f.hargs k hk).symm) $$ Hv
  ihave Hvs := valsAt_of_tracked N M vs args.toNat $$ [HA Hv']
  · iframe HA Hv'
  ihave Hra := ptsto_eq (show _ = r by ix_reg) $$ Hra
  ihave Hk := and_elim_l $$ Hk
  iapply Hk $$ Hpc Hra
  iexists _
  iframe Hregs Hnull Hvs Hw
  isplitl []
  · ipureintro
    intro x hx hc
    have hx1 : x ≠ 1 := fun e => by subst e; revert hx; decide
    have hcl : ∀ y ∈ callerSaved, x ≠ y := fun y hy e => hc (e ▸ hy)
    have hx10 := hcl 10 (by decide); have hx12 := hcl 12 (by decide)
    have hx13 := hcl 13 (by decide)
    by_cases h2 : x = 2
    · subst h2; ix_reg
      rw [BitVec.add_assoc, show (18446744073709551536#64 : BitVec 64) + 80#64 = 0#64 by decide,
        BitVec.add_zero, c.h2]
    by_cases h8 : x = 8
    · subst h8; ix_reg
    by_cases h9 : x = 9
    · subst h9; ix_reg
    by_cases h18 : x = 18
    · subst h18; ix_reg
    simp only [upd, hx1, h2, h8, h9, h18, hx10, ite_false]
    rw [k5 x hx]
    simp only [upd, hx10, hx12, hx13, ite_false]
    exact f.hk x hx hc (by simp [h2, h8, h9, h18])
  isplitl []
  · ipureintro; exact hsh
  · unfold stackAt
    iframe Hst
    ipureintro
    exact ⟨by unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed; omega,
      by unfold Vsa.Sim.LayoutInstance.stackSL; simp; unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed; omega,
      by unfold Vsa.Sim.LayoutInstance.stackSL; simp; omega, hs3, c.hs4⟩

/-- **Falsy, one argument**: `runtime_error(in, line, "%s", "assertion failed", 0)`. -/
theorem na_falsy1 (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} (HN : NewlibHoles) (hcl : CodeLive live)
    {sret inp args s line r : BitVec 64} {n : Nat} {vs : List Value} {ρ : Regime} {st : St}
    {d : Nat} {jb : Nat → BitVec 8} {rv R : Nat → BitVec 64} {M Margs : Mem}
    (c : NaCtx live sret inp args s line r n rv jb) (hlen : vs.length = n)
    (hok : n = 1 ∨ n = 2)
    (f : NaFacts sret inp args s line r n (vs[0]'(by omega)) rv R M Margs)
    (ht : (vs[0]'(by omega)).truthy = false) (hn1 : n = 1) :
    NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs ∗
      ms 0x80002e48#64 R (npF s args n) M ⊢ Wp.W Φ := by
  have hs1 := c.hs1; have hs2 := c.hs2; have hs3 := c.hs3
  unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have h10 : R 10 = 0#64 := by rw [f.h10, ht]; rfl
  iintro ⟨Hrest, Hms⟩
  iapply wp_swpF Wp (S := npF s args n) (R := R) (Mt := M) (pc := 0x80002e48#64)
    (F := NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs)
  rotate_left
  · unfold NaRest
    icases Hrest with ⟨#Hcode, Hrest⟩
    rw [hro]
    iframe Hcode Hrest Hms
  intro F'
  refine na_fail1 c.hlive f.h2 h10 (by omega) hs2 hs3 f.sa (f.sc.trans (by rw [hn1])) ?_
  intros; apply swp_closeF
  dsimp only [F']
  unfold NaRest
  iintro ⟨⟨#Hcode, #Himg, Hsl, #Hv, #Hjb, Hw, Hst, Hk⟩, Hms⟩
  ihave #Hrd := readable_rodata $$ Himg
  ihave Hk := and_elim_r $$ Hk
  ihave Hk := wand_pure_apply (not_assertOk_falsy _ ht) $$ Hk
  iapply (na_rtErr Wp HN hcl (jalx_80002ebc live (fun p hp => c.hlive _ (interp_code_80002ebc p hp)))
    interp_code_80002ebc (naS_fmt (fun a ha => ⟨.inl ha, rfl⟩) (naFail_str (fun a ha => ⟨.inl ha, rfl⟩))
      0#64) c.hinp c.hjb c.hs1 hs2 hs3 hlen c.hdfa)
  iframe Hcode Himg Hms Hst Hrd Hjb Hw Hsl Hv Hk
  ipureintro
  exact ⟨by ix_reg; exact f.h9, by ix_reg; exact f.h18, by ix_reg, by ix_reg, by ix_reg,
    by ix_reg; exact f.h2, f.hargs⟩

/-- A kind other than the string's reads as another word. -/
theorem kind_ne3 {v : Value} (h : Vsa.RuntimeRepr.kindTag v ≠ 3) :
    BitVec.ofNat 64 (Vsa.RuntimeRepr.kindTag v) ≠ 3#64 := by
  cases v <;> simp only [Vsa.RuntimeRepr.kindTag] at h ⊢ <;> first | decide | exact absurd rfl h

theorem kindTag_small (v : Value) : Vsa.RuntimeRepr.kindTag v < 2 ^ 31 := by
  cases v <;> simp only [Vsa.RuntimeRepr.kindTag] <;> decide

/-- **Falsy, two arguments, the second not a string**: `"assertion failed"`. -/
theorem na_falsy2o (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} (HN : NewlibHoles) (hcl : CodeLive live)
    {sret inp args s line r : BitVec 64} {n : Nat} {vs : List Value} {ρ : Regime} {st : St}
    {d : Nat} {jb : Nat → BitVec 8} {rv R : Nat → BitVec 64} {M Margs : Mem}
    (c : NaCtx live sret inp args s line r n rv jb) (hlen : vs.length = n)
    (hok : n = 1 ∨ n = 2)
    (f : NaFacts sret inp args s line r n (vs[0]'(by omega)) rv R M Margs)
    (ht : (vs[0]'(by omega)).truthy = false) (hn2 : n = 2) (hk3 : Vsa.RuntimeRepr.kindTag (vs[1]'(by omega)) ≠ 3) :
    NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs ∗
      ms 0x80002e48#64 R (npF s args n) M ⊢ Wp.W Φ := by
  have hs1 := c.hs1; have hs2 := c.hs2; have hs3 := c.hs3
  unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have h10 : R 10 = 0#64 := by rw [f.h10, ht]; rfl
  have ha1 := c.ha.al; have ha2 := c.ha.lo; have ha3 := c.ha.hi
  unfold Vsa.Sim.tohostAddr at ha2
  have eA : ∀ k, k < 48 → (args + BitVec.ofNat 64 k).toNat = args.toNat + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show args.toNat + k < 2 ^ 64 by omega)]
  iintro ⟨Hrest, Hms⟩
  unfold NaRest
  icases Hrest with ⟨#Hcode, #Himg, Hsl, #Hv, #Hjb, Hw, Hst, Hk⟩
  ihave #Hv1 := valsImg_get N (imgM Margs) vs args.toNat 1 (by omega) $$ Hv
  ihave %hp := valOf_pure N _ _ _ _ $$ Hv1
  have hkw : ldv .lw M (args + 24#64).toNat =
      BitVec.ofNat 64 (Vsa.RuntimeRepr.kindTag (vs[1]'(by omega))) := by
    rw [eA 24 (by omega)]
    refine ldv_lw_kind ?_ (kindTag_small _)
    rw [imgW_agree (g := imgM Margs) (fun j hj => f.hargs _ (by simp only [InExt]; omega))]
    exact hp.kind
  iapply wp_swpF Wp (S := npF s args n) (R := R) (Mt := M) (pc := 0x80002e48#64)
    (F := NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs)
  rotate_left
  · rw [hro]; unfold NaRest
    iframe Hcode Himg Hsl Hv Hjb Hw Hst Hk Hms
  intro F'
  refine na_fail2o (n := n) c.hlive f.h2 h10 (by omega) hs2 hs3 (by omega) (by omega) ha1 (by omega) f.sa
    (f.sc.trans (by rw [hn2])) hkw (kind_ne3 hk3) ?_ ?_
  rotate_left
  · intros; rename_i hc; exact absurd (kind_ne3 hk3) hc
  intros; apply swp_closeF
  dsimp only [F']
  unfold NaRest
  iintro ⟨⟨#Hcode, #Himg, Hsl, #Hv, #Hjb, Hw, Hst, Hk⟩, Hms⟩
  ihave #Hrd := readable_rodata $$ Himg
  ihave Hk := and_elim_r $$ Hk
  ihave Hk := wand_pure_apply (not_assertOk_falsy _ ht) $$ Hk
  iapply (na_rtErr Wp HN hcl (jalx_80002ebc live (fun p hp => c.hlive _ (interp_code_80002ebc p hp)))
    interp_code_80002ebc (naS_fmt (fun a ha => ⟨.inl ha, rfl⟩) (naFail_str (fun a ha => ⟨.inl ha, rfl⟩))
      0#64) c.hinp c.hjb c.hs1 hs2 hs3 hlen c.hdfa)
  iframe Hcode Himg Hms Hst Hrd Hjb Hw Hsl Hv Hk
  ipureintro
  exact ⟨by ix_reg; exact f.h9, by ix_reg; exact f.h18, by ix_reg, by ix_reg, by ix_reg,
    by ix_reg; exact f.h2, f.hargs⟩

/-- **Falsy, two arguments, the second a string**: the string is the message. -/
theorem na_falsy2s (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} (HN : NewlibHoles) (hcl : CodeLive live)
    {sret inp args s line r : BitVec 64} {n : Nat} {vs : List Value} {ρ : Regime} {st : St}
    {d : Nat} {jb : Nat → BitVec 8} {rv R : Nat → BitVec 64} {M Margs : Mem}
    (c : NaCtx live sret inp args s line r n rv jb) (hlen : vs.length = n)
    (hok : n = 1 ∨ n = 2)
    (f : NaFacts sret inp args s line r n (vs[0]'(by omega)) rv R M Margs)
    (ht : (vs[0]'(by omega)).truthy = false) (hn2 : n = 2) {t : String} (hs : (vs[1]'(by omega)) = .str t) :
    NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs ∗
      ms 0x80002e48#64 R (npF s args n) M ⊢ Wp.W Φ := by
  have hs1 := c.hs1; have hs2 := c.hs2; have hs3 := c.hs3
  unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have h10 : R 10 = 0#64 := by rw [f.h10, ht]; rfl
  have ha1 := c.ha.al; have ha2 := c.ha.lo; have ha3 := c.ha.hi
  unfold Vsa.Sim.tohostAddr at ha2
  have eA : ∀ k, k < 48 → (args + BitVec.ofNat 64 k).toNat = args.toNat + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show args.toNat + k < 2 ^ 64 by omega)]
  iintro ⟨Hrest, Hms⟩
  unfold NaRest
  icases Hrest with ⟨#Hcode, #Himg, Hsl, #Hv, #Hjb, Hw, Hst, Hk⟩
  ihave #Hv1 := valsImg_get N (imgM Margs) vs args.toNat 1 (by omega) $$ Hv
  ihave %hp := valOf_pure N _ _ _ _ $$ Hv1
  have hkw : ldv .lw M (args + 24#64).toNat =
      BitVec.ofNat 64 (Vsa.RuntimeRepr.kindTag (vs[1]'(by omega))) := by
    rw [eA 24 (by omega)]
    refine ldv_lw_kind ?_ (kindTag_small _)
    rw [imgW_agree (g := imgM Margs) (fun j hj => f.hargs _ (by simp only [InExt]; omega))]
    exact hp.kind
  iapply wp_swpF Wp (S := npF s args n) (R := R) (Mt := M) (pc := 0x80002e48#64)
    (F := NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs)
  rotate_left
  · rw [hro]; unfold NaRest
    iframe Hcode Himg Hsl Hv Hjb Hw Hst Hk Hms
  intro F'
  have hpw : ldv .ld M (args + 32#64).toNat = imgW (imgM Margs) (args.toNat + 24 + 8) := by
    rw [eA 32 (by omega), ldv_ld_imgW]
    exact imgW_agree (fun j hj => f.hargs _ (by simp only [InExt]; omega))
  refine na_fail2s (n := n) c.hlive f.h2 h10 (by omega) hs2 hs3 (by omega) (by omega) ha1 (by omega) f.sa
    (f.sc.trans (by rw [hn2])) (hkw.trans (by rw [hs]; rfl)) hpw ?_
  intros; apply swp_closeF
  dsimp only [F']
  unfold NaRest
  iintro ⟨⟨#Hcode, #Himg, Hsl, #Hv, #Hjb, Hw, Hst, Hk⟩, Hms⟩
  ihave #Hv1 := valsImg_get N (imgM Margs) vs args.toNat 1 (by omega) $$ Hv
  rw [hs, show args.toNat + 24 * 1 = args.toNat + 24 by omega]
  simp only [valOf]
  icases Hv1 with ⟨-, #Hs⟩
  ihave ⟨%rd, Hrd, %hrd⟩ := readable_str $$ [Himg Hs]
  · isplitl
    · iexact Himg
    · iexact Hs
  have hfmt : FmtArgsOK (fun a => (rodataDom a ∨
      InExt ((imgW (imgM Margs) (args.toNat + 24 + 8)).toNat, t.toList.length + 1) a) ∨ False)
      rd 0x80019038#64 [imgW (imgM Margs) (args.toNat + 24 + 8), 0#64] :=
    naS_fmt (fun a ha => ⟨Or.inl (Or.inl ha), hrd.1 a ha⟩)
      ⟨_, cstrCov_of_img (fun i hi => Or.inl (Or.inr (by simp only [InExt]; omega))) hrd.2⟩ 0#64
  ihave Hk := and_elim_r $$ Hk
  ihave Hk := wand_pure_apply (not_assertOk_falsy _ ht) $$ Hk
  iapply (na_rtErr Wp HN hcl (jalx_80002ebc live (fun p hp => c.hlive _ (interp_code_80002ebc p hp)))
    interp_code_80002ebc hfmt c.hinp c.hjb c.hs1 hs2 hs3 hlen c.hdfa)
  iframe Hcode Himg Hms Hst Hrd Hjb Hw Hsl Hv Hk
  ipureintro
  exact ⟨by ix_reg; exact f.h9, by ix_reg; exact f.h18, by ix_reg, by ix_reg, by ix_reg,
    by ix_reg; exact f.h2, f.hargs⟩

theorem kindTag_str {v : Value} (h : Vsa.RuntimeRepr.kindTag v = 3) : ∃ t, v = .str t := by
  cases v <;> simp only [Vsa.RuntimeRepr.kindTag] at h <;> first | exact ⟨_, rfl⟩ | omega

/-- **`native_assert`**, for either WP, given H5's `NewlibHoles`: with one or
two arguments, the first truthy, it returns `null`; otherwise it aborts
through `runtime_error`. -/
theorem nativeAssert_spec (hlive : ∀ q ∈ interpText, live q.1) (hcl : CodeLive live)
    (HN : NewlibHoles) (Wp : MachWP (GF := GF) (vsaModel live)) (N : NativeAddrs) (L : DlLayout)
    (Room : RoomPred) (sret inp args s line : BitVec 64) (vs : List Value) (ρ : Regime) (st : St)
    (d : Nat) (jb : Nat → BitVec 8) :
    ⊢ nativeAssertSpec (vsaModel live) N Wp L Room sret inp args s line vs ρ st d jb := by
  unfold nativeAssertSpec fnSpecAbort
  iintro %rv !> %r %Φ Hpc Hra ⟨%hal, Hregs, %⟨h10, h11, h12, h13, h14, h2⟩, #Hcode, Hsl,
    %⟨hg, ha, hn, hinp, hjb⟩, Hvs, #Himg, #Hjb, Hw, ⟨Hst, %hsg⟩⟩ Hk
  have hs1 := hsg.le; have hs2 := hsg.lo; have hs3 := hsg.hi; have hs4 := hsg.al
  simp only [Vsa.Sim.LayoutInstance.stackSL] at hs2 hs3
  have hs0 : 0x87800000 + nativeAssertNeed ≤ s.toNat := by
    unfold nativeAssertNeed RtErr.rtErrNeed snprintfNeed at hs1 hs2 ⊢
    show 2273312768 + (80 + (224 + 1024)) ≤ s.toNat
    omega
  ihave ⟨%Margs, HA, #Hv⟩ := valsAt_tracked N vs args.toNat $$ Hvs
  ihave ⟨Hst, HF⟩ := naFrame_split (s := s) hs1 $$ Hst
  ihave ⟨%f, HF⟩ := ownSet_fn _ $$ HF
  ihave ⟨%Mf, HF⟩ := ownSet_mem _ f $$ HF
  ihave ⟨%M, HM, %⟨-, hMa, hdfa⟩⟩ := ownSet_join_tracked _ _ Mf Margs $$ [HF HA]
  · iframe HF HA
  have c : NaCtx live sret inp args s line r vs.length rv jb :=
    ⟨hlive, hal, h10, h11, h12, h13, h14, h2, hs0, hs3, hs4, hsg.top, hg, ha, hn, hinp, hjb,
      hdfa⟩
  have hms : ms (GF := GF) nativeAssertPC (upd rv 1 r) (npF s args vs.length) M =
      iprop(PC ↦ᵣ nativeAssertPC ∗ ra ↦ᵣ r ∗ regFile rv ∗
        ownSet (fun a => InExt (s.toNat - 80, 80) a ∨ InExt (args.toNat, 24 * vs.length) a)
          (fun a => a ↦ₘ imgM M a)) := by
    unfold ms; rw [regFile_upd_ra]; simp only [upd_same]
  by_cases hok : vs.length = 1 ∨ vs.length = 2
  · have hB : ∀ R' M', NaFacts sret inp args s line r vs.length (vs[0]'(by omega)) rv R' M' Margs →
        NaRest Wp Φ N L Room sret inp args s r vs ρ st d rv jb Margs ∗
          ms 0x80002e48#64 R' (npF s args vs.length) M' ⊢ Wp.W Φ := by
      intro R' M' f
      cases htr : (vs[0]'(by omega)).truthy
      · rcases hok with h1 | h2
        · exact na_falsy1 Wp HN hcl c rfl (.inl h1) f htr h1
        · by_cases hk3 : Vsa.RuntimeRepr.kindTag (vs[1]'(by omega)) = 3
          · obtain ⟨t, ht⟩ := kindTag_str hk3
            exact na_falsy2s Wp HN hcl c rfl (.inr h2) f htr h2 ht
          · exact na_falsy2o Wp HN hcl c rfl (.inr h2) f htr h2 hk3
      · exact na_truthyPath Wp c rfl hok f htr
    iapply na_head Wp c rfl hok hMa hB
    unfold NaRest
    rw [hms]
    iframe Hcode Himg Hsl Hv Hjb Hw Hst Hk Hpc Hra Hregs HM
  · iapply na_badPath Wp HN hcl c rfl hok hMa
    unfold NaRest
    rw [hms]
    iframe Hcode Himg Hsl Hv Hjb Hw Hst Hk Hpc Hra Hregs HM

end Glue

end VsaIris.Interp
