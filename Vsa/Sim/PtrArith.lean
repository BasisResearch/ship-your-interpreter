import Vsa.Sim.MemcpySpec

/-!
# `PtrArith` — canonical pointer / sign-extended-immediate arithmetic

The pointer lemmas used by every Layer-3 composition, in one place.  Existing
staples live elsewhere and stay put (`ptr_toNat`/`ptr_succ` in `MemcpySpec`,
`sub1_bv_sn5` in `SnprintfSpec5`); this file adds the *generic* forms new
compositions should reach for, plus the negative-immediate `toNat` constants.

**Kernel-recursion gotcha (recurring):** never prove a minus-K pointer identity
via `simp only [BitVec.toNat_add, BitVec.toNat_ofNat]` followed by rewriting a
`2^64 − K` literal and `omega` — the kernel dies with "deep recursion detected"
when more than one `toNat_ofNat` mod is in play.  The safe shape (used by
`ptr_sub` below, same as `sub1_bv_sn5`): `apply BitVec.eq_of_toNat_eq`, then a
single `rw [BitVec.toNat_add, <sext constant>, BitVec.toNat_ofNat]`, then
`omega` with `v.isLt` in context.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

namespace Vsa.Sim

/-! ## Negative 12-bit immediates as `toNat` constants

Proved by the staged route (`toNat_signExtend` → `msb` → `decide`); a bare
`decide` on the unfolded `sign_extend` can blow the kernel. -/

/-! ## Generic additive / subtractive pointer normal forms -/

/-! ## Stack-frame round trips (`addi sp,sp,-K` … `addi sp,sp,K`) -/

end Vsa.Sim
