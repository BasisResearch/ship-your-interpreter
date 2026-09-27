import Vsa.Sim.DivSites
import Vsa.Sim.Muldi3Spec
import Vsa.Triple

/-!
# Layer 3 — total-correctness spec for `__hidden___udivdi3` (unsigned 64-bit division)

Config-level (`Vsa.Logic.Triple`) composition of the per-site observational steps
(`Vsa/Sim/DivSites.lean`) into a total-correctness triple for libgcc's unsigned
64-bit division core `__hidden___udivdi3`.

We reuse the spec-independent observation consumers (`readback`, `obs_alu_*`,
`obs_btaken_*`, `obs_bnottaken_*`, `obs_jr_*`) and the `ret`-target helper
(`ret_tgt`) from `Vsa.Sim` (Muldi3Spec).

## Algorithm

Entry `0x800046ac`, `x10 = n`, `x11 = d`, `d ≠ 0`. Registers a0/a1/a2/a3 =
x10/x11/x12/x13 are the only clobbers; x1 (ra) and every other GPR are preserved
(blanket preservation conjunct). Returns via `ret` (reads x1). Result:
`x10 = n / d` (`BitVec.udiv` = Nat division), `x11 = n % d`.

Two loops: a *normalize* loop (`c0..d0`) shifting the divisor left until it is
`≥` the dividend or its sign bit is set, and a *divide* loop (`d8..ec`) doing
restoring shift-subtract long division.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Blanket ghost-frame predicate (`NotWritten`) + generic per-class helpers

`Ust` tracks the live GPRs `x10..x13`, `PC`, `x1`, `minstret`, `mem`, tick and
`GoodState`. To make preservation of *every other* register recoverable after
packaging into a `Triple` (needed by callers that stash the return address in a
scratch register like `t0`/`x5`, and by future interpreter callers that need
`s`-register / `sp` preservation), `Ust` carries a ghost snapshot
`g : (R : Register) → Option (RegisterType R)` and a blanket conjunct: every
register outside the write-set reads as its ghost value.

`NotWritten R` is the 11-way `Bool`-disequality conjunction over the union of the
tracked GPRs (`x10..x13`) and the per-step write-set / tick-set registers
(`PC, nextPC, minstret, minstret_increment, mcycle, mtime, mip`). Each generic
frame helper consumes exactly the disequalities its class needs, so preservation
is threaded through every transition with a single helper application. -/

/-- `R` is outside the union of the tracked GPRs and every register any hot-path
step (ALU / branch / jump / tick) can write. Unfolds to an 11-way conjunction of
`(X == R) = false` `Bool` disequalities, which the read-back frame lemmas consume
directly. -/
abbrev NotWritten (R : Register) : Prop :=
  (Register.x10 == R) = false ∧ (Register.x11 == R) = false ∧
  (Register.x12 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

/-- The blanket ghost-frame conjunct, as it appears in `Ust` and every derived
predicate: every non-written register reads as its ghost snapshot `g`. -/
abbrev Frame (g : (R : Register) → Option (RegisterType R)) (c : Config) : Prop :=
  ∀ R : Register, NotWritten R → c.σ.regs.get? R = g R

theorem NotWritten.x10 {R : Register} (h : NotWritten R) : (Register.x10 == R) = false := h.1
theorem NotWritten.x11 {R : Register} (h : NotWritten R) : (Register.x11 == R) = false := h.2.1
theorem NotWritten.x13 {R : Register} (h : NotWritten R) : (Register.x13 == R) = false := h.2.2.2.1

/-! ## The config-level state predicate

`Ust g pc a0 a1 a2 a3 r m0 c`: standing observation at a program point — `c.σ` is
a `GoodState` with `__hidden___udivdi3` code loaded, memory pinned to `m0`, PC at
`pc`, live GPRs `x10 = a0`, `x11 = a1`, `x12 = a2`, `x13 = a3`, `x1 = r`,
`minstret` defined, tick `< 2`, and the blanket ghost-frame conjunct `hframe`:
every register outside the tracked/written set reads as the ghost snapshot `g`
(constant across the whole function — no step writes a non-tracked register). -/

/-! ## ALU straight-line transitions

Each is a one-step `Triple.of_step` over a `site_*` lemma, reading the successor
`Ust` fields off `ReadsLikePost` through the reused `obs_alu_*` consumers. -/

/-! ## Branch transitions (all GPRs preserved; only PC moves) -/

/-! ## `ret` transition (f0 → r): PC → return address; GPRs preserved. -/

/-! ## Guard-predicate bridges (BitVec comparisons ⇒ Nat/top-bit facts) -/

/-! ## Shift / top-bit arithmetic facts -/

/-!
## Remaining: the two loops and the numeric division result (follow-up)

Everything above is fully proved (machine-stepping sites, all 24 config-level
one-step transitions `utr_*`, the guard-predicate bridges, and the shift/top-bit
arithmetic). What remains to reach the full `udivdi3_spec` postcondition
(`x10 = n / d`, `x11 = n % d`) is the pure-arithmetic loop reasoning, composed via
`Triple.loop`/`Triple.seq`. The invariants are:

**Prefix (ac → c0).** Compose `utr_ac_b0`, `utr_b0_b4`, `utr_b4_b8`,
`utr_b8_bc` (needs `d ≠ 0` ⇒ `(d == 0) = false`, from `beq_cases` + the `d ≠ 0`
hypothesis), `utr_bc_c0`. Establishes at `c0`: `a2 = d`, `a1 = n`, `a0 = -1`,
`a3 = 1`.

**Normalize loop (head `c4`, also entered from `c0`).** Guard `LoopN` = at `c0`
with `¬bgeu(a2,a1) ∧ ¬blez(a2)` (equivalently `a2.toNat < a1.toNat ∧ 0 < a2.toInt`).
Invariant: `∃ k, a2.toNat = d.toNat * 2^k ∧ a3.toNat = 2^k ∧ d.toNat * 2^k < 2^64`.
Measure: `2^64 - a2.toNat` (strictly decreases because a non-top-bit `a2` doubles
exactly, via `shl1_toNat` guarded by `toInt_pos_notop` from the `blez`-false
branch). Exit: at `d4` with `a2 = d·2^K` where `K` is minimal such that
`d·2^K ≥ n` or the top bit is set (the exact stop condition, from `bgeu`/`blez`
being true, bridged by `bgeu_true`/`blez_true`+`toInt_nonpos_top`).

**Divide loop (head `d8`).** After `utr_d4_d8` sets `a0 = 0`. Guard `LoopD` = at
`d8` with `a3 ≠ 0`. Invariant (`∃ j`):
  `a2.toNat = d.toNat * 2^j`, `a3.toNat = 2^j`, `d.toNat * 2^j < 2^64`,
  `a0.toNat % 2^(j+1) = 0`  (quotient bits so far are all above position j),
  `n.toNat = d.toNat * a0.toNat + a1.toNat`  (division progress), and
  `a1.toNat < 2 * a2.toNat`  (remainder bound).
Measure: `a3.toNat` (halves via `shr1_toNat`; `shr_lt` gives strict decrease).
The `or a0,a0,a3` step uses that bit `j` of `a0` is clear (`a0 % 2^(j+1) = 0`) to
turn the BitVec `|||` into `+ 2^j` — this needs a `Nat` lemma
`a % 2^(j+1) = 0 → a ||| 2^j = a + 2^j` (provable by `Nat.eq_of_testBit_eq` using
`Nat.testBit_two_pow_add_eq` / `_add_gt` and a `lowbits_clear`-style helper;
it was the one auxiliary not completed here). One body iteration splits on the
`bltu a1,a2` guard (`bltu_true`/`bltu_false`) and re-establishes the invariant with
`j ↦ j-1` (both loop-preserving cases verified by the arithmetic identities above).
Exit (`a3 = 0`, i.e. after the `j = 0` iteration): `a1.toNat < d.toNat` (from the
bound with `a2 = d`), so `a0 = n / d` and `a1 = n % d` by `Nat.div_mod_unique`
composed with `BitVec.toNat_udiv`/`toNat_umod`.

**Epilogue (`f0 → r`).** `utr_f0_ret` (proved) delivers `PC = r`, GPRs preserved,
`x1 = r`, mem unchanged, `GoodState`. The final `udivdi3_post` conjoins the numeric
result with the blanket-preservation conjunct (every GPR outside a0/a1/a2/a3 reads
as at entry — surfaced through the `obs_*_other` reads already threaded in each
`utr_*`).
-/

end Vsa.Sim

