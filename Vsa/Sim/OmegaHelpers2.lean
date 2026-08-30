import Vsa.Sim.EvalSimCommon

/-!
# `OmegaHelpers2` — minimal-context re-index lemmas (omega paid ONCE)

Companion to `Vsa/Sim/OmegaHelpers.lean`. `OmegaHelpers` collapsed the spill/expr/slot
memory-safety omega shapes. This file collapses the OTHER dominant omega shape found in
`Vsa/Sim/EvalCallNative2.lean` (measured: ~245 `omega`, 53s — the file's whole elaboration
cost, `experiments/straggler-migration.md`): **stack-offset re-indexing** of the form
`fsp.toNat - c + d = fsp.toNat - c' + d'`, emitted as term-mode `show … from by omega`
inside a single ~600-line theorem. Each such `omega` was slow NOT because the goal is hard
(it needs only `80 ≤ fsp.toNat`) but because term-mode `by omega` ingests the theorem's
entire ~100-hypothesis linear-arith context. Proving the equality via a lemma whose ONLY
hypotheses are the frame bound + a ground arithmetic side-condition pays omega once (compiled
into this olean) and reduces each callsite to a typecheck.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

/-- Saturating-subtraction re-index: `f - c + d = f - c' + d'` when the frame floor `lo ≤ f`
keeps both subtractions non-saturating (`c ≤ lo`, `c' ≤ lo`) and the offsets balance
(`d + c' = d' + c`). All hypotheses are either the single in-scope frame bound or GROUND
(`by decide`), so the callsite runs no omega — the omega is compiled into this lemma. -/
theorem reidxNat (f c d c' d' lo : Nat)
    (hf : lo ≤ f) (hc : c ≤ lo) (hc' : c' ≤ lo) (hbal : d + c' = d' + c) :
    f - c + d = f - c' + d' := by omega

/-- One-sided re-index `f - c + d = f - c'` (i.e. `d' = 0`): the RHS offset collapses. -/
theorem reidxNat0 (f c d c' lo : Nat)
    (hf : lo ≤ f) (hc : c ≤ lo) (hc' : c' ≤ lo) (hbal : d + c' = c) :
    f - c + d = f - c' := by omega

/-- Disjointness of an 8-byte store at `f - 80 + k` (`k ∈ [0, 40]`) from an address `a`
that lies OUTSIDE the whole frame+buffer window `[f - 80, f + 40)`. This is the
`getElem_writeMap8_disjoint` side-condition `a < (f-80+k) ∨ (f-80+k)+8 ≤ a` in
`EvalCallNative2`'s `hbufout`, derived once from the window membership `ha` and the frame
floor `hf`. The omega is compiled here; callers pass `ha`, `hf`, and the GROUND `k ≤ 40`. -/
theorem winStore_disjoint (f a k : Nat)
    (ha : a < f - 80 ∨ f + 40 ≤ a) (hf : 80 ≤ f) (hk : k + 40 ≤ 120) :
    a < (f - 80 + k) ∨ (f - 80 + k) + 8 ≤ a := by omega

/-- Disjointness of two distinct aligned 8-byte stack slots: the 8-byte read at
`f - 80 + b + o` (`o < 8`, slot base `b`) is disjoint from the 8-byte store at `f - 80 + k`
when `b` and `k` are distinct multiples of 8. This is the `getElem_writeMap8_disjoint`
side-condition inside `EvalCallNative2`'s `hread_spill`/`hmb5_*` slot-reload blocks. Omega
compiled here; callers pass `ho` and GROUND slot facts (`b%8=0`, `k%8=0`, `b≠k`, bounds). -/
theorem slotStore_disjoint (f b o k : Nat)
    (ho : o < 8) (hb8 : b % 8 = 0) (hk8 : k % 8 = 0) (hbk : b ≠ k)
    (hb : b ≤ 72) (hk : k ≤ 72) (hf : 80 ≤ f) :
    (f - 80 + b + o) < (f - 80 + k) ∨ (f - 80 + k) + 8 ≤ (f - 80 + b + o) := by omega

/-! ## `site_*_na` spill-store safety (the ~25s omega cluster in `EvalCallNative2`)

Each `site_<pc>_na` store takes FOUR safety preconditions over the store address
`addr = (v2 + sign_extend imm).toNat`: `0x80000000 ≤ addr`, `addr + 8 ≤ 2^64`,
`tohostAddr + 16 ≤ addr`, `addr % 8 = 0`. In `nativeAssertInternal` these were each a
term-mode `(by rw [haddrK]; …; omega)` running in the ~150-hypothesis theorem context —
measured ~25s of the file's 40s omega bill. `naStore_safe4` proves all four ONCE (omega in
this olean) from the address equation `haddr` (= `fsp.toNat - 80 + k`, `k ≤ 72` a multiple
of 8) + the four `RegionGuard fsp` frame bounds. Each site passes the four projections
`(h).1 (h).2.1 (h).2.2.1 (h).2.2.2`, running NO omega. -/
theorem naStore_safe4 (fsp addr k : Nat)
    (haddr : addr = fsp - 80 + k)
    (hk8 : k % 8 = 0) (hk : k ≤ 72)
    (halign : fsp % 8 = 0) (hlo : 0x80000000 + 80 ≤ fsp)
    (hhi : fsp + 40 ≤ 0x100000000) (hwin : tohostAddr + 16 + 80 ≤ fsp) :
    0x80000000 ≤ addr ∧ addr + 8 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ addr ∧ addr % 8 = 0 := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  subst haddr; rw [htoh] at hwin ⊢; refine ⟨by omega, by omega, by omega, by omega⟩

end Vsa.Sim
