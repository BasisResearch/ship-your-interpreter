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


end VsaIris.Interp
