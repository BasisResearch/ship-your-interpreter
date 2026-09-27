import Vsa.Sim.Muldi3Sites
import Vsa.Triple

/-!
# Layer 3 — the `__muldi3` total-correctness spec (`muldi3_spec`)

Config-level (`Vsa.Logic.Triple`) composition of the per-site observational steps
(`Vsa/Sim/Muldi3Sites.lean`) into a total-correctness triple for libgcc's
`__muldi3` (shift-add 64-bit multiply). This is the top of the M3 pilot.

## Invariant and measure

The loop (`0x48 … 0x5c`, back-edge `0x5c → 0x48`) maintains the shift-add
invariant `a0 + a2 * a1 = x * y` over `BitVec 64` (wrap-around: `+`/`*` are mod
2^64, the identity exact at that width). One iteration replaces
`(a0, a2, a1) ↦ (a0 + [a1 odd] a2, a2 <<< 1, a1 >>> 1)`; the invariant is
preserved because `(a2 <<< 1)*(a1 >>> 1) + (a1 &&& 1)*a2 = a2 * a1`
(`invmul_bv`). The measure `a1.toNat` strictly halves each iteration
(`shr_lt`), so the loop terminates.

## Parity / noise handling

Every step is taken through the parity-agnostic `stepObs_*` wrappers, so the
tick counter (`c.tick`) is unconstrained on entry (`< 2` invariant) and the
clock-noise registers (`mcycle`/`mtime`/`mip`) never appear in `P`/`Q`. The
observation relation `ReadsLikePost` (StepObs) lets a site read the next state's
GPRs/PC off the notick `sigmaPost_*` frame regardless of which variant fired.

## Spec shape

`P` fixes: `GoodState`, `__muldi3Loaded mem`, PC = entry, `x10 = x`, `x11 = y`,
`x1 = r` (return addr, 4-aligned & RAM & below tohost so `ret` refetches
cleanly), `tick < 2`, `minstret` defined, and `mem = m₀` (ghost). `Q`: PC = `r`,
`x10 = x * y`, `GoodState`, `mem = m₀` (no stores), and the non-clobbered GPRs
(everything but a0/a1/a2/a3 = x10..x13) unchanged. Tick/minstret noise is
existential.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Arithmetic core (BitVec 64, wrap-around) -/

/-- `A * (2 d + r) = A * 2 * d + r * A` (Nat, distribution). -/
private theorem key_nat (A d r : Nat) : A * (2 * d + r) = A * 2 * d + r * A := by
  rw [Nat.mul_add, Nat.mul_comm r A, ← Nat.mul_assoc]

private theorem mml (a b m : Nat) : (a % m) * b % m = a * b % m := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

private theorem amod (a b m : Nat) : (a % m + b % m) % m = (a + b) % m := by
  rw [← Nat.add_mod]

/-- Nat mod-2^64 form of the shift-add invariant identity. -/
private theorem invmul_nat (A a1n : Nat) :
    A * a1n % 2^64 = (A * 2 % 2^64 * (a1n / 2) % 2^64 + a1n % 2 * A % 2^64) % 2^64 := by
  have key : A * 2 * (a1n / 2) + a1n % 2 * A = A * a1n := by
    rw [← key_nat A (a1n / 2) (a1n % 2), Nat.div_add_mod a1n 2]
  rw [mml (A*2) (a1n/2) (2^64), amod, key]

/-- **Shift-add invariant identity** (`BitVec 64`, mod 2^64):
`a2 * a1 = (a2 <<< 1) * (a1 >>> 1) + (a1 &&& 1) * a2`. The `(a1 &&& 1) * a2`
term is `a2` when `a1` is odd and `0` when even — exactly the conditional
`add a0,a0,a2` guarded by `beqz (a1 & 1)`. -/
theorem invmul_bv (a2 a1 : BitVec 64) :
    a2 * a1 = (a2 <<< (1:Nat)) * (a1 >>> (1:Nat)) + (a1 &&& 1#64) * a2 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, BitVec.toNat_and]
  have hand : (a1.toNat &&& (1#64).toNat) = a1.toNat % 2 := by
    have : (1#64).toNat = 1 := by decide
    rw [this, Nat.and_one_is_mod]
  rw [hand, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hpow : (2:Nat)^1 = 2 := by decide
  rw [hpow]
  exact invmul_nat a2.toNat a1.toNat

/-- **Measure strictly decreases**: `a1 ≠ 0 ⇒ (a1 >>> 1).toNat < a1.toNat`. -/
theorem shr_lt (a1 : BitVec 64) (h : a1 ≠ 0#64) : (a1 >>> (1:Nat)).toNat < a1.toNat := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hpos : 0 < a1.toNat := by
    rcases Nat.eq_zero_or_pos a1.toNat with h0 | h0
    · exact absurd (by apply BitVec.eq_of_toNat_eq; simpa using h0) h
    · exact h0
  have hpow : (2:Nat)^1 = 2 := by decide
  rw [hpow]; omega

/-- `addi …,0` value adds `sign_extend 0x000#12 = 0`. -/
theorem sext_zero : (sign_extend (0x000#12) : BitVec 64) = (0#64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## Reading registers off an observed successor

`ReadsLikePost σ' spost` (StepObs) gives `σ'.regs.get? R = spost.regs.get? R` for
every non-tick register. Composed with a computed `spost.regs.get? R = w`, we get
`σ'.regs.get? R = w`. These `readback_*` lemmas do exactly that for the four
`sigmaPost_*` families used here, at a GPR / PC register `R`. -/

theorem readback (σ' spost : MState) (h : ReadsLikePost σ' spost) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (hw : spost.regs.get? R = some w) : σ'.regs.get? R = some w := by
  rw [h.1 R hmc hmt hmi]; exact hw

/-! ### `sigmaPost_alu` reads (PC := pc+4, rd_reg := v, others := σ) -/

theorem post_alu_pc (σ : MState) (pc vminstret : BitVec 64) (rd_reg : Register)
    (v : RegisterType rd_reg) :
    (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? Register.PC = some (BitVec.addInt pc 4) := by
  show ((((sigma3_alu σ pc rd_reg v).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_alu_rd (σ : MState) (pc vminstret : BitVec 64) (rd_reg : Register)
    (v : RegisterType rd_reg)
    (hrd_ms : (Register.minstret == rd_reg) = false) (hrd_pc : (Register.PC == rd_reg) = false) :
    (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? rd_reg = some v := by
  show ((((sigma3_alu σ pc rd_reg v).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hrd_ms, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hrd_pc, dif_neg, reduceCtorEq, not_false_eq_true]
  show ((afterNextPC (afterPrelude σ) pc).regs.insert rd_reg v).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `sigmaPost_alu` read of `R` outside `{minstret,PC,rd_reg,nextPC,minstret_increment}`
equals `σ`'s. (Thin wrapper over `get?_sigmaPost_alu`.) -/
theorem post_alu_other (σ : MState) (pc vminstret : BitVec 64) (rd_reg : Register)
    (v : RegisterType rd_reg) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? R = σ.regs.get? R :=
  get?_sigmaPost_alu σ pc vminstret rd_reg v R h1 h2 h3 h4 h5

/-! ### `sigmaPost_branch_*` reads (PC := target / pc+4, all GPRs := σ) -/

theorem post_branch_taken_pc (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13) :
    (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.PC
      = some (pc + sign_extend (m := 64) imm) := by
  show ((((sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_branch_nottaken_pc (σ : MState) (pc vminstret : BitVec 64) :
    (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.PC = some (BitVec.addInt pc 4) := by
  show ((((sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

/-! ### `sigmaPost_jump_x0` reads (`ret`: PC := tgt, all GPRs := σ) -/

theorem post_jump_x0_pc (σ : MState) (pc vminstret tgt : BitVec 64) :
    (sigmaPost_jump_x0 σ pc vminstret tgt).regs.get? Register.PC = some tgt := by
  show ((((sigma3_jump_x0 σ pc tgt).regs.insert Register.PC tgt).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_jump_x0_other (σ : MState) (pc vminstret tgt : BitVec 64) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_jump_x0 σ pc vminstret tgt).regs.get? R = σ.regs.get? R :=
  get?_sigmaPost_jump_x0 σ pc vminstret tgt R h1 h2 h4 h5

/-! ## Blanket ghost-frame predicate (`NotWrittenM`) + generic per-class helpers

`St` tracks the live GPRs `x10..x13`, `PC`, `x1`, `minstret`, `mem`, tick and
`GoodState`. To make preservation of *every other* register recoverable after
packaging into a `Triple` (needed by callers that stash the return address in a
scratch register, and by future interpreter callers that need `s`-register /
`sp` preservation), `St` carries a ghost snapshot
`g : (R : Register) → Option (RegisterType R)` and a blanket conjunct: every
register outside the write-set reads as its ghost value.

`NotWrittenM R` is the 11-way `Bool`-disequality conjunction over the union of the
tracked GPRs (`x10..x13`) and the per-step write-set / tick-set registers
(`PC, nextPC, minstret, minstret_increment, mcycle, mtime, mip`). The write-set is
identical to the division core's, but `NotWrittenM` is a separate abbrev (this file
is imported *by* `DivSpec`, so we cannot import `DivSpec.NotWritten`; the suffix `M`
avoids the name collision at the `Vsa` root). Each generic frame helper consumes
exactly the disequalities its class needs. -/

/-- `R` is outside the union of the tracked GPRs (`x10..x13`) and every register any
hot-path step (ALU / branch / jump / tick) can write. -/
abbrev NotWrittenM (R : Register) : Prop :=
  (Register.x10 == R) = false ∧ (Register.x11 == R) = false ∧
  (Register.x12 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

theorem NotWrittenM.x10 {R : Register} (h : NotWrittenM R) : (Register.x10 == R) = false := h.1
theorem NotWrittenM.x11 {R : Register} (h : NotWrittenM R) : (Register.x11 == R) = false := h.2.1
theorem NotWrittenM.x13 {R : Register} (h : NotWrittenM R) : (Register.x13 == R) = false := h.2.2.2.1

/-! ## The config-level state predicate

`St pc a0 a1 a2 x y r m0 c` is the standing observation at a program point:
`c.σ` is a `GoodState` with the `__muldi3` code loaded, memory pinned to the
ghost `m0`, PC at `pc`, the live GPRs `x10 = a0`, `x11 = a1`, `x12 = a2`,
`x1 = r`, `minstret` defined, and the tick counter `< 2`. The ghosts `x`, `y`
are the multiplier operands, `r` the return address (with its fetch-side
alignment/RAM/window facts so the eventual `ret`'s target is well-formed — here
`ret` just reads `r`, so we only need `r`'s value; the caller supplies target
alignment where a `ret` fires). -/

/-! ## ALU-observation consumer

From an ALU observation `ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)`, read the
framing fields off `σ'`. `obs_alu_pc` gives PC := pc+4; `obs_alu_rd` gives
rd := v; `obs_alu_other` gives any other-GPR read from `σ`; `obs_alu_minstret`
gives minstret defined. Each hides the `readback ∘ post_alu_*` composition. -/

theorem obs_alu_pc {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_alu_pc σ pc vm rd v)

theorem obs_alu_rd {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v))
    (hmc : (Register.mcycle == rd) = false) (hmt : (Register.mtime == rd) = false)
    (hmi : (Register.mip == rd) = false)
    (hrd_ms : (Register.minstret == rd) = false) (hrd_pc : (Register.PC == rd) = false) :
    σ'.regs.get? rd = some v :=
  readback σ' _ hobs rd hmc hmt hmi (post_alu_rd σ pc vm rd v hrd_ms hrd_pc)

theorem obs_alu_other {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((post_alu_other σ pc vm rd v R h1 h2 h3 h4 h5).trans hσ)

theorem obs_alu_minstret {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_alu σ pc rd v).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-! ## Prefix transitions (straight line, PC 0x40 → 0x44 → 0x48)

Each is a one-step `Triple` via `Triple.of_step` applied to a `site_*` lemma; the
successor's `St` fields are read off `ReadsLikePost` through the `post_alu_*`
frame lemmas. Register disequalities are `by decide`.

The `add_zero`/`sext` folds turn the model's raw ALU value (e.g. `v + sext 0`)
into the intended one (`v`). -/

/-! ## Branch-observation consumers (all GPRs preserved; only PC moves) -/

/-! ## Branch transitions -/

/-! ## `ret` and jump-observation consumers -/

theorem obs_jr_other {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((post_jump_x0_other σ pc vm tgt R h1 h2 h4 h5).trans hσ)

theorem obs_jr_pc {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) :
    σ'.regs.get? Register.PC = some tgt :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_jump_x0_pc σ pc vm tgt)

theorem obs_jr_minstret {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_jump_x0 σ pc tgt).regs.insert Register.PC tgt).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `x &&& (2^64 - 2) = x` for even `x < 2^64` (clearing an already-clear bit 0). -/
theorem and_clear_bit0 (x : Nat) (hlt : x < 2^64) (hev : x % 2 = 0) :
    x &&& (2^64 - 2) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have hmaskeq : (2^64 - 2) = 2 * (2^63 - 1) := by decide
  rw [hmaskeq]
  match i with
  | 0 =>
    have hx0 : x.testBit 0 = false := by rw [Nat.testBit_zero, hev]; rfl
    rw [hx0, Bool.false_and]
  | j + 1 =>
    rw [Nat.testBit_succ (2 * (2^63-1)) j]
    have hdiv : (2 * (2^63 - 1)) / 2 = 2^63 - 1 := by omega
    rw [hdiv]
    by_cases hj : j < 63
    · rw [Nat.testBit_two_pow_sub_one]; simp only [hj, decide_true, Bool.and_true]
    · have hxf : x.testBit (j+1) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [hxf, Bool.false_and]

/-- With a 4-aligned return address `r`, `ret`'s target `update (r + sext 0) 0 0#1 = r`. -/
theorem ret_tgt (r : BitVec 64) (halign : r.toNat % 4 = 0) :
    Sail.BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1 = r := by
  rw [sext_zero, BitVec.add_zero]
  show Sail.BitVec.updateSubrange' r 0 1 (0#1) = r
  have hmask : (~~~(((BitVec.allOnes 1).zeroExtend 64) <<< 0) : BitVec 64) = 0xFFFFFFFFFFFFFFFE#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have hy : (((0#1 : BitVec 1).zeroExtend 64) <<< 0 : BitVec 64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  simp only [Sail.BitVec.updateSubrange', hmask, hy, BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have hmv : (0xFFFFFFFFFFFFFFFE#64 : BitVec 64).toNat = 2^64 - 2 := by decide
  rw [hmv, Nat.and_comm]
  exact and_clear_bit0 r.toNat r.isLt (by omega)

/-! ## The loop invariant, guard, and measure

`LoopI x y r m0`: either at the loop head `0x48` with the shift-add invariant
`a0 + a2 * a1 = x * y`, or done at `0x60` with `a0 = x * y`. `LoopB` is the guard
"at `0x48` and `a1 ≠ 0`". `LoopMu = a1.toNat`. -/

/-! ## Invariant-preservation identities (odd / even iteration) -/

/-! ## One iteration of the loop (`0x48 → 0x5c`)

Chains `andi → beqz → [add] → srli → slli`. Internally splits on the low bit of
`a1` (`beqz a3`), landing at `0x5c` with `a1 ↦ a1>>>1`, `a2 ↦ a2<<<1`, and
`a0 ↦ a0 + [a1 odd] a2` — the invariant is re-established for the new triple via
`inv_even`/`inv_odd`. The `∃ a0'` in the postcondition hides the odd/even choice
of the new accumulator. -/

/-! ## The loop body (`Triple.loop` obligation)

From `LoopI ∧ LoopB ∧ LoopMu = n` (at `0x48`, `a1 ≠ 0`, `a1.toNat = n`), one full
iteration `iter_48_5c` reaches `0x5c`; the `bnez` then either loops back (`0x48`,
`AtHead`, measure `(a1>>>1).toNat < n` by `shr_lt`) or falls through (`0x60`,
`AtDone`, `a0' = x*y` since `a1>>>1 = 0`). Either way `LoopI ∧ LoopMu < n`. -/

/-! ## Loop → exit and the full multiply spec

`Triple.loop LoopMu loop_body` runs the loop to `LoopI ∧ ¬LoopB`. In that state
we are either already done at `0x60` (`AtDone`), or at `0x48` with `a1 = 0` (so
`a0 = x*y` by the invariant), in which case one last iteration (`iter_48_5c`
lands at `0x5c` with `a1>>>1 = 0`, then `bnez` falls through) reaches `0x60`.
Both feed the `ret`. -/

/-! ## The precondition of `__muldi3` and the spec

`muldi3_pre x y r m0 c`: entry `St` at `0x80004640` with `x10 = x`, `x11 = y`,
`x1 = r`, `mem = m0`, tick `< 2`, and `r` a 4-aligned return address. The `a2`/`a3`
entry values are irrelevant (existentially closed in the statement). -/

end Vsa.Sim
