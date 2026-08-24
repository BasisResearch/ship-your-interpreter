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
open Vsa.Sim.Code (__muldi3Loaded)

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

/-- `andi …,1` value equals `a1 &&& 1` (the `sign_extend 0x001#12 = 1#64`). -/
theorem sext_one : (sign_extend (0x001#12) : BitVec 64) = (1#64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- `addi …,0` value adds `sign_extend 0x000#12 = 0`. -/
theorem sext_zero : (sign_extend (0x000#12) : BitVec 64) = (0#64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The shift amount `extractLsb 0x01#6 5 0` is `1#6`, and shifting by it is `>>>1`/`<<<1`. -/
theorem shamt_one : Sail.BitVec.extractLsb (0x01#6) 5 0 = (1#6 : BitVec 6) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- Shifting a `BitVec 64` by `extractLsb 0x01#6 5 0` is shifting by `1`. -/
theorem shr_shamt (v : BitVec 64) : shift_bits_right v (Sail.BitVec.extractLsb (0x01#6) 5 0) = v >>> (1:Nat) := by
  show v >>> (Sail.BitVec.extractLsb (0x01#6) 5 0) = _
  rw [shamt_one]; rfl

theorem shl_shamt (v : BitVec 64) : shift_bits_left v (Sail.BitVec.extractLsb (0x01#6) 5 0) = v <<< (1:Nat) := by
  show v <<< (Sail.BitVec.extractLsb (0x01#6) 5 0) = _
  rw [shamt_one]; rfl

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

theorem post_branch_taken_other (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_branch_taken σ pc vminstret imm).regs.get? R = σ.regs.get? R :=
  get?_sigmaPost_branch_taken σ pc vminstret imm R h1 h2 h4 h5

theorem post_branch_nottaken_pc (σ : MState) (pc vminstret : BitVec 64) :
    (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.PC = some (BitVec.addInt pc 4) := by
  show ((((sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_branch_nottaken_other (σ : MState) (pc vminstret : BitVec 64) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_branch_nottaken σ pc vminstret).regs.get? R = σ.regs.get? R :=
  get?_sigmaPost_branch_nottaken σ pc vminstret R h1 h2 h4 h5

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
theorem NotWrittenM.x12 {R : Register} (h : NotWrittenM R) : (Register.x12 == R) = false := h.2.2.1
theorem NotWrittenM.x13 {R : Register} (h : NotWrittenM R) : (Register.x13 == R) = false := h.2.2.2.1

/-- Generic ALU frame step: a variable-`R` read-back through an ALU observation
(write-set `rd, PC, minstret, nextPC, minstret_increment`, tick-set
`mcycle, mtime, mip`). `rd` is one of the tracked GPRs; the caller picks the
matching disequality out of `NotWrittenM R`. -/
theorem frame_alu_m {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWrittenM R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

/-- Generic taken-branch frame step (write-set `PC, minstret, nextPC,
minstret_increment`; no `rd`). -/
theorem frame_btaken_m {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    (hR : NotWrittenM R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_taken σ pc vm imm R hmi hpc hnpc hmii

/-- Generic not-taken-branch frame step. -/
theorem frame_bnottaken_m {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWrittenM R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hmi hpc hnpc hmii

/-- Generic `jr`/`ret` frame step (`jump_x0`: write-set `PC, minstret, nextPC,
minstret_increment`). -/
theorem frame_jr_m {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenM R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

/-! ## The config-level state predicate

`St pc a0 a1 a2 x y r m0 c` is the standing observation at a program point:
`c.σ` is a `GoodState` with the `__muldi3` code loaded, memory pinned to the
ghost `m0`, PC at `pc`, the live GPRs `x10 = a0`, `x11 = a1`, `x12 = a2`,
`x1 = r`, `minstret` defined, and the tick counter `< 2`. The ghosts `x`, `y`
are the multiplier operands, `r` the return address (with its fetch-side
alignment/RAM/window facts so the eventual `ret`'s target is well-formed — here
`ret` just reads `r`, so we only need `r`'s value; the caller supplies target
alignment where a `ret` fires). -/
structure St (g : (R : Register) → Option (RegisterType R))
    (pc a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : __muldi3Loaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some pc
  a0 : c.σ.regs.get? Register.x10 = some a0
  a1 : c.σ.regs.get? Register.x11 = some a1
  a2 : c.σ.regs.get? Register.x12 = some a2
  a3 : c.σ.regs.get? Register.x13 = some a3
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  hframe : ∀ R : Register, NotWrittenM R → c.σ.regs.get? R = g R

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

private theorem addi0 (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [sext_zero]; exact BitVec.add_zero v

private theorem andi1 (v : BitVec 64) : v &&& sign_extend (m := 64) (0x001#12) = v &&& 1#64 := by
  rw [sext_one]

/-- `mv a2,a0` (0x40 → 0x44): `x12 := x` (= entry `x10`). `a0 = x`, `a1 = y`
preserved; `a2` overwritten by `x`; `x13` (a3) passes through unchanged. -/
theorem tr_40_44 (g : (R : Register) → Option (RegisterType R))
    (x y r a2old a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (St g (0x80004640#64) x y a2old a3old r m0) (St g (0x80004644#64) x y x a3old r m0) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004640 c.σ c.tick c.steps (0x80004640#64) vmi x hSt.good hSt.pc hmi hSt.a0 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    ?_,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x12 hR).trans (hSt.hframe R hR)⟩
  -- x12 := (x + sext 0) = x
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [addi0 x] at hrd

/-- `li a0,0` (0x44 → 0x48): `x10 := 0`. -/
theorem tr_44_48 (g : (R : Register) → Option (RegisterType R))
    (x y r a2 a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (St g (0x80004644#64) x y a2 a3old r m0) (St g (0x80004648#64) (0#64) y a2 a3old r m0) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004644 c.σ c.tick c.steps (0x80004644#64) vmi hSt.good hSt.pc hmi hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    obs_alu_pc hobs, ?_,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x10 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [addi0 (0#64)] at hrd

/-- `andi a3,a1,1` (0x48 → 0x4c): `x13 := a1 &&& 1`. -/
theorem tr_48_4c (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (St g (0x80004648#64) a0 y a2 a3old r m0) (St g (0x8000464c#64) a0 y a2 (y &&& 1#64) r m0) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004648 c.σ c.tick c.steps (0x80004648#64) vmi y hSt.good hSt.pc hmi hSt.a1 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    ?_,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x13 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [andi1 y] at hrd

/-- `add a0,a0,a2` (0x50 → 0x54, odd path): `x10 := a0 + a2`. -/
theorem tr_50_54 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (St g (0x80004650#64) a0 y a2 a3 r m0) (St g (0x80004654#64) (a0 + a2) y a2 a3 r m0) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004650 c.σ c.tick c.steps (0x80004650#64) vmi a0 a2 hSt.good hSt.pc hmi hSt.a0 hSt.a2 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    obs_alu_pc hobs,
    obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide),
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x10 hR).trans (hSt.hframe R hR)⟩

/-- `srli a1,a1,1` (0x54 → 0x58): `x11 := a1 >>> 1`. -/
theorem tr_54_58 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (St g (0x80004654#64) a0 a1 a2 a3 r m0) (St g (0x80004658#64) a0 (a1 >>> (1:Nat)) a2 a3 r m0) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004654 c.σ c.tick c.steps (0x80004654#64) vmi a1 hSt.good hSt.pc hmi hSt.a1 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    ?_,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x11 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [shr_shamt a1] at hrd

/-- `slli a2,a2,1` (0x58 → 0x5c): `x12 := a2 <<< 1`. -/
theorem tr_58_5c (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (St g (0x80004658#64) a0 a1 a2 a3 r m0) (St g (0x8000465c#64) a0 a1 (a2 <<< (1:Nat)) a3 r m0) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004658 c.σ c.tick c.steps (0x80004658#64) vmi a2 hSt.good hSt.pc hmi hSt.a2 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    ?_,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x12 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [shl_shamt a2] at hrd

/-! ## Branch-observation consumers (all GPRs preserved; only PC moves) -/

theorem obs_btaken_other {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((post_branch_taken_other σ pc vm imm R h1 h2 h4 h5).trans hσ)

theorem obs_btaken_pc {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) :
    σ'.regs.get? Register.PC = some (pc + sign_extend (m := 64) imm) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_branch_taken_pc σ pc vm imm)

theorem obs_btaken_minstret {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_bnottaken_other {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((post_branch_nottaken_other σ pc vm R h1 h2 h4 h5).trans hσ)

theorem obs_bnottaken_pc {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_branch_nottaken_pc σ pc vm)

theorem obs_bnottaken_minstret {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-! ## Branch transitions -/

/-- `beqz a3` taken (0x4c → 0x54, a3 = 0 i.e. a1 even): skip the `add`. -/
theorem tr_4c_54 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hodd : ((y &&& 1#64) == (0#64)) = true) :
    Triple (St g (0x8000464c#64) a0 y a2 (y &&& 1#64) r m0) (St g (0x80004654#64) a0 y a2 (y &&& 1#64) r m0) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_8000464c_taken c.σ c.tick c.steps (0x8000464c#64) vmi (y &&& 1#64)
      hSt.good hSt.pc hmi hSt.a3 hSt.loaded rfl hodd hSt.tick
  have hpceq : (0x8000464c#64 : BitVec 64) + sign_extend (m := 64) (0x0008#13) = (0x80004654#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem, ?_,
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_btaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_btaken_minstret hobs, hi',
    fun R hR => (frame_btaken_m hobs R hR).trans (hSt.hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

/-- `beqz a3` not taken (0x4c → 0x50, a3 ≠ 0 i.e. a1 odd): do the `add`. -/
theorem tr_4c_50 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hodd : ((y &&& 1#64) == (0#64)) = false) :
    Triple (St g (0x8000464c#64) a0 y a2 (y &&& 1#64) r m0) (St g (0x80004650#64) a0 y a2 (y &&& 1#64) r m0) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_8000464c_nottaken c.σ c.tick c.steps (0x8000464c#64) vmi (y &&& 1#64)
      hSt.good hSt.pc hmi hSt.a3 hSt.loaded rfl hodd hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    obs_bnottaken_pc hobs,
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_bnottaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_bnottaken_minstret hobs, hi',
    fun R hR => (frame_bnottaken_m hobs R hR).trans (hSt.hframe R hR)⟩

/-- `bnez a1` taken (0x5c → 0x48, a1 ≠ 0): loop back-edge. -/
theorem tr_5c_48 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3 a1 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hne : (a1 != (0#64)) = true) :
    Triple (St g (0x8000465c#64) a0 a1 a2 a3 r m0) (St g (0x80004648#64) a0 a1 a2 a3 r m0) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_8000465c_taken c.σ c.tick c.steps (0x8000465c#64) vmi a1
      hSt.good hSt.pc hmi hSt.a1 hSt.loaded rfl hne hSt.tick
  have hpceq : (0x8000465c#64 : BitVec 64) + sign_extend (m := 64) (0x1fec#13) = (0x80004648#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem, ?_,
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_btaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_btaken_minstret hobs, hi',
    fun R hR => (frame_btaken_m hobs R hR).trans (hSt.hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

/-- `bnez a1` not taken (0x5c → 0x60, a1 = 0): fall through to `ret`. -/
theorem tr_5c_60 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3 a1 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hne : (a1 != (0#64)) = false) :
    Triple (St g (0x8000465c#64) a0 a1 a2 a3 r m0) (St g (0x80004660#64) a0 a1 a2 a3 r m0) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_8000465c_nottaken c.σ c.tick c.steps (0x8000465c#64) vmi a1
      hSt.good hSt.pc hmi hSt.a1 hSt.loaded rfl hne hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    obs_bnottaken_pc hobs,
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_bnottaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_bnottaken_minstret hobs, hi',
    fun R hR => (frame_bnottaken_m hobs R hR).trans (hSt.hframe R hR)⟩

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

/-- `ret` (0x60 → `r`): PC → return address `r`; all GPRs preserved. Requires `r`
4-aligned (so bit-0-clearing is a no-op) and its fetch-side window facts (`htgt`). -/
theorem tr_60_ret (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (halign : r.toNat % 4 = 0) :
    Triple (St g (0x80004660#64) a0 a1 a2 a3 r m0)
           (fun c => GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.regs.get? Register.PC = some r ∧
             c.σ.regs.get? Register.x10 = some a0 ∧ c.σ.regs.get? Register.x11 = some a1 ∧
             c.σ.regs.get? Register.x12 = some a2 ∧ c.σ.regs.get? Register.x1 = some r ∧
             c.tick < 2 ∧ (∀ R : Register, NotWrittenM R → c.σ.regs.get? R = g R)) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halign]; exact halign
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004660 c.σ c.tick c.steps (0x80004660#64) vmi r
      hSt.good hSt.pc hmi hSt.ra hSt.loaded rfl htgt hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.mem, ?_,
    obs_jr_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_jr_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_jr_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_jr_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    hi',
    fun R hR => (frame_jr_m hobs R hR).trans (hSt.hframe R hR)⟩
  rw [obs_jr_pc hobs, ret_tgt r halign]

/-! ## The loop invariant, guard, and measure

`LoopI x y r m0`: either at the loop head `0x48` with the shift-add invariant
`a0 + a2 * a1 = x * y`, or done at `0x60` with `a0 = x * y`. `LoopB` is the guard
"at `0x48` and `a1 ≠ 0`". `LoopMu = a1.toNat`. -/

/-- At loop head 0x48 with the shift-add invariant. -/
def AtHead (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  ∃ a0 a1 a2 a3, St g (0x80004648#64) a0 a1 a2 a3 r m0 c ∧ a0 + a2 * a1 = x * y

/-- Done at 0x60 with `a0 = x * y`. -/
def AtDone (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  ∃ a1 a2 a3, St g (0x80004660#64) (x * y) a1 a2 a3 r m0 c

def LoopI (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  AtHead g x y r m0 c ∨ AtDone g x y r m0 c

/-- Loop guard: at `0x48` (`AtHead`) with a nonzero `a1`. -/
def LoopB (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  ∃ a0 a1 a2 a3, St g (0x80004648#64) a0 a1 a2 a3 r m0 c ∧ a0 + a2 * a1 = x * y ∧ a1 ≠ 0#64

/-- Loop measure: `x11.toNat` (`0` if `x11` undefined — total on `Config`).
`x11 : Register` has `RegisterType = BitVec 64`, whose default is `0#64`. -/
def LoopMu (c : Config) : Nat :=
  ((c.σ.regs.get? Register.x11).getD (0#64)).toNat

/-! ## Invariant-preservation identities (odd / even iteration) -/

/-- `a1 &&& 1` is `0` or `1` (the low bit). -/
theorem and1_cases (a1 : BitVec 64) : a1 &&& 1#64 = 0#64 ∨ a1 &&& 1#64 = 1#64 := by
  have hval : (a1 &&& 1#64).toNat = a1.toNat % 2 := by
    rw [BitVec.toNat_and]; have h1 : (1#64).toNat = 1 := by decide
    rw [h1, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one a1.toNat with h0 | h1
  · left; apply BitVec.eq_of_toNat_eq; rw [hval, h0]; rfl
  · right; apply BitVec.eq_of_toNat_eq; rw [hval, h1]; rfl

/-- **Even iteration**: `a1 &&& 1 = 0` ⇒ `a0 + (a2<<<1)*(a1>>>1) = a0 + a2*a1`
(no `add`, invariant preserved). -/
theorem inv_even (a0 a1 a2 : BitVec 64) (hev : a1 &&& 1#64 = 0#64) :
    a0 + (a2 <<< (1:Nat)) * (a1 >>> (1:Nat)) = a0 + a2 * a1 := by
  rw [invmul_bv a2 a1, hev, BitVec.zero_mul, BitVec.add_zero]

/-- **Odd iteration**: `a1 &&& 1 = 1` ⇒ `(a0+a2) + (a2<<<1)*(a1>>>1) = a0 + a2*a1`
(the `add a0,a0,a2` folds in, invariant preserved). -/
theorem inv_odd (a0 a1 a2 : BitVec 64) (hod : a1 &&& 1#64 = 1#64) :
    (a0 + a2) + (a2 <<< (1:Nat)) * (a1 >>> (1:Nat)) = a0 + a2 * a1 := by
  rw [invmul_bv a2 a1, hod, BitVec.one_mul, BitVec.add_assoc, BitVec.add_comm a2 _,
    ← BitVec.add_assoc]

/-! ## One iteration of the loop (`0x48 → 0x5c`)

Chains `andi → beqz → [add] → srli → slli`. Internally splits on the low bit of
`a1` (`beqz a3`), landing at `0x5c` with `a1 ↦ a1>>>1`, `a2 ↦ a2<<<1`, and
`a0 ↦ a0 + [a1 odd] a2` — the invariant is re-established for the new triple via
`inv_even`/`inv_odd`. The `∃ a0'` in the postcondition hides the odd/even choice
of the new accumulator. -/
theorem iter_48_5c (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hinv : a0 + a2 * a1 = x * y) :
    Triple (St g (0x80004648#64) a0 a1 a2 a3old r m0)
           (fun c => ∃ a0', St g (0x8000465c#64) a0' (a1 >>> (1:Nat)) (a2 <<< (1:Nat)) (a1 &&& 1#64) r m0 c
             ∧ a0' + (a2 <<< (1:Nat)) * (a1 >>> (1:Nat)) = x * y) := by
  -- andi: 0x48 → 0x4c, x13 := a1 &&& 1  (tr_48_4c branches on register value `y := a1`)
  have h1 : Triple (St g (0x80004648#64) a0 a1 a2 a3old r m0)
      (St g (0x8000464c#64) a0 a1 a2 (a1 &&& 1#64) r m0) := tr_48_4c g x a1 r a0 a2 a3old m0
  rcases and1_cases a1 with hev | hod
  · -- even: beqz taken, skip add
    have hbeq : ((a1 &&& 1#64) == (0#64)) = true := by rw [hev]; rfl
    have h2 := tr_4c_54 g x a1 r a0 a2 m0 hbeq
    have h3 := tr_54_58 g x y r a0 a1 a2 (a1 &&& 1#64) m0
    have h4 := tr_58_5c g x y r a0 (a1 >>> (1:Nat)) a2 (a1 &&& 1#64) m0
    have hchain : Triple (St g (0x80004648#64) a0 a1 a2 a3old r m0)
        (St g (0x8000465c#64) a0 (a1 >>> (1:Nat)) (a2 <<< (1:Nat)) (a1 &&& 1#64) r m0) :=
      (h1.seq h2).seq (h3.seq h4)
    exact hchain.conseq (fun _ h => h) (fun c hc =>
      ⟨a0, hc, by rw [inv_even a0 a1 a2 hev]; exact hinv⟩)
  · -- odd: beqz not taken, do add
    have hbne : ((a1 &&& 1#64) == (0#64)) = false := by rw [hod]; rfl
    have h2 := tr_4c_50 g x a1 r a0 a2 m0 hbne
    have h2' := tr_50_54 g x a1 r a0 a2 (a1 &&& 1#64) m0
    have h3 := tr_54_58 g x a1 r (a0 + a2) a1 a2 (a1 &&& 1#64) m0
    have h4 := tr_58_5c g x a1 r (a0 + a2) (a1 >>> (1:Nat)) a2 (a1 &&& 1#64) m0
    have hchain : Triple (St g (0x80004648#64) a0 a1 a2 a3old r m0)
        (St g (0x8000465c#64) (a0 + a2) (a1 >>> (1:Nat)) (a2 <<< (1:Nat)) (a1 &&& 1#64) r m0) :=
      ((h1.seq h2).seq h2').seq (h3.seq h4)
    exact hchain.conseq (fun _ h => h) (fun c hc =>
      ⟨a0 + a2, hc, by rw [inv_odd a0 a1 a2 hod]; exact hinv⟩)

/-! ## The loop body (`Triple.loop` obligation)

From `LoopI ∧ LoopB ∧ LoopMu = n` (at `0x48`, `a1 ≠ 0`, `a1.toNat = n`), one full
iteration `iter_48_5c` reaches `0x5c`; the `bnez` then either loops back (`0x48`,
`AtHead`, measure `(a1>>>1).toNat < n` by `shr_lt`) or falls through (`0x60`,
`AtDone`, `a0' = x*y` since `a1>>>1 = 0`). Either way `LoopI ∧ LoopMu < n`. -/
theorem loop_body (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (n : Nat) :
    Triple (fun c => LoopI g x y r m0 c ∧ LoopB g x y r m0 c ∧ LoopMu c = n)
           (fun c => LoopI g x y r m0 c ∧ LoopMu c < n) := by
  intro c hc
  obtain ⟨_, ⟨a0, a1, a2, a3, hSt, hinv, hne⟩, hmu⟩ := hc
  -- LoopMu c = a1.toNat (x11 = a1)
  have hmu_eq : LoopMu c = a1.toNat := by
    simp only [LoopMu, hSt.a1, Option.getD_some]
  rw [hmu_eq] at hmu
  -- one iteration to 0x5c
  obtain ⟨c1, hs1, a0', h5c, hinv'⟩ := iter_48_5c g x y r a0 a1 a2 a3 m0 hinv c hSt
  by_cases hnew : (a1 >>> (1:Nat)) = 0#64
  · -- exit to 0x60: AtDone, a0' = x*y
    have hbne : ((a1 >>> (1:Nat)) != (0#64)) = false := by rw [hnew]; rfl
    obtain ⟨c2, hs2, hSt2⟩ := tr_5c_60 g x y r a0' (a2 <<< (1:Nat)) (a1 &&& 1#64) (a1 >>> (1:Nat)) m0 hbne c1 h5c
    have ha0' : a0' = x * y := by
      have := hinv'
      rw [hnew, BitVec.mul_zero, BitVec.add_zero] at this
      exact this
    refine ⟨c2, hs1.trans hs2, Or.inr ⟨_, _, _, ha0' ▸ hSt2⟩, ?_⟩
    -- LoopMu c2 = (a1>>>1).toNat = 0 < n
    have hmc2 : LoopMu c2 = (a1 >>> (1:Nat)).toNat := by simp only [LoopMu, hSt2.a1, Option.getD_some]
    have hnpos : 0 < n := by
      rw [← hmu]
      have : 0 < a1.toNat := by
        rcases Nat.eq_zero_or_pos a1.toNat with h0 | h0
        · exact absurd (by apply BitVec.eq_of_toNat_eq; simpa using h0) hne
        · exact h0
      exact this
    rw [hmc2, hnew]
    show (0#64).toNat < n
    have h0 : (0#64 : BitVec 64).toNat = 0 := by decide
    rw [h0]; exact hnpos
  · -- loop back to 0x48: AtHead, measure decreases
    have hbne : ((a1 >>> (1:Nat)) != (0#64)) = true := by
      rw [bne_iff_ne]; exact hnew
    obtain ⟨c2, hs2, hSt2⟩ := tr_5c_48 g x y r a0' (a2 <<< (1:Nat)) (a1 &&& 1#64) (a1 >>> (1:Nat)) m0 hbne c1 h5c
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨a0', a1 >>> (1:Nat), a2 <<< (1:Nat), a1 &&& 1#64, hSt2, hinv'⟩, ?_⟩
    have hmu2 : LoopMu c2 = (a1 >>> (1:Nat)).toNat := by simp only [LoopMu, hSt2.a1, Option.getD_some]
    rw [hmu2, ← hmu]
    exact shr_lt a1 hne

/-! ## Loop → exit and the full multiply spec

`Triple.loop LoopMu loop_body` runs the loop to `LoopI ∧ ¬LoopB`. In that state
we are either already done at `0x60` (`AtDone`), or at `0x48` with `a1 = 0` (so
`a0 = x*y` by the invariant), in which case one last iteration (`iter_48_5c`
lands at `0x5c` with `a1>>>1 = 0`, then `bnez` falls through) reaches `0x60`.
Both feed the `ret`. -/

/-- The loop runs to a `0x60`-`AtDone` configuration (`a0 = x*y`). -/
theorem loop_to_done (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (LoopI g x y r m0) (AtDone g x y r m0) := by
  have hloop := Triple.loop (I := LoopI g x y r m0) (B := LoopB g x y r m0) LoopMu (loop_body g x y r m0)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hDone
  · -- AtHead with ¬LoopB ⇒ a1 = 0 ⇒ a0 = x*y; run last iteration to 0x60
    obtain ⟨a0, a1, a2, a3, hSt, hinv⟩ := hHead
    have ha1 : a1 = 0#64 := by
      by_cases hne : a1 = 0#64
      · exact hne
      · exact absurd ⟨a0, a1, a2, a3, hSt, hinv, hne⟩ hnB
    -- iterate 0x48 → 0x5c (a1 = 0: even, no add; a1>>>1 = 0)
    obtain ⟨c1, hs1, a0', h5c, hinv'⟩ := iter_48_5c g x y r a0 a1 a2 a3 m0 hinv c hSt
    have hnew : (a1 >>> (1:Nat)) = 0#64 := by rw [ha1]; rfl
    have hbne : ((a1 >>> (1:Nat)) != (0#64)) = false := by rw [hnew]; rfl
    obtain ⟨c2, hs2, hSt2⟩ := tr_5c_60 g x y r a0' (a2 <<< (1:Nat)) (a1 &&& 1#64) (a1 >>> (1:Nat)) m0 hbne c1 h5c
    have ha0' : a0' = x * y := by
      have := hinv'; rw [hnew, BitVec.mul_zero, BitVec.add_zero] at this; exact this
    exact ⟨c2, hs1.trans hs2, _, _, _, ha0' ▸ hSt2⟩
  · exact ⟨c, .refl c, hDone⟩

/-! ## The precondition of `__muldi3` and the spec

`muldi3_pre x y r m0 c`: entry `St` at `0x80004640` with `x10 = x`, `x11 = y`,
`x1 = r`, `mem = m0`, tick `< 2`, and `r` a 4-aligned return address. The `a2`/`a3`
entry values are irrelevant (existentially closed in the statement). -/
def muldi3_pre (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  (∃ a2old a3old, St g (0x80004640#64) x y a2old a3old r m0 c) ∧ r.toNat % 4 = 0

/-- `muldi3_post`: PC back at `r`, `x10 = x * y`, `GoodState`, memory unchanged
(`= m0`), the callee-saved return register `x1 = r` intact, `tick < 2`, and the
blanket ghost-frame conjunct (every non-clobbered register reads as its entry
ghost `g` — recovers callee-saved GPRs for downstream callers). -/
def muldi3_post (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some (x * y) ∧ c.σ.regs.get? Register.x1 = some r ∧
  c.tick < 2 ∧ (∀ R : Register, NotWrittenM R → c.σ.regs.get? R = g R)

/-- **`muldi3_spec`** — total-correctness triple for libgcc `__muldi3`
(shift-add 64-bit multiply). From the entry precondition the machine runs (in
finitely many architectural steps, tick parity unconstrained) to the return
address `r` with `x10 = x * y` (`BitVec 64`, wrap-around), `GoodState` preserved,
and memory unchanged (`__muldi3` performs no stores). -/
theorem muldi3_spec (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (muldi3_pre g x y r m0) (muldi3_post g x y r m0) := by
  -- prefix: 0x40 → 0x44 → 0x48 establishing AtHead with a0=0, a2=x, invariant 0 + x*y = x*y
  have hpre : Triple (muldi3_pre g x y r m0) (fun c => LoopI g x y r m0 c ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨⟨a2old, a3old, hEntry⟩, halign⟩ := hc
    -- 0x40 → 0x44 (mv a2,a0: x12 := x)
    obtain ⟨c1, hs1, hSt1⟩ := tr_40_44 g x y r a2old a3old m0 c hEntry
    -- 0x44 → 0x48 (li a0,0: x10 := 0)
    obtain ⟨c2, hs2, hSt2⟩ := tr_44_48 g x y r x a3old m0 c1 hSt1
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨0#64, y, x, a3old, hSt2, ?_⟩, halign⟩
    -- 0 + x * y = x * y
    rw [BitVec.zero_add]
  -- loop to AtDone (a0 = x*y at 0x60), carrying alignment
  have hbody : Triple (fun c => LoopI g x y r m0 c ∧ r.toNat % 4 = 0)
      (fun c => AtDone g x y r m0 c ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨hI, halign⟩ := hc
    obtain ⟨c', hs, hDone⟩ := loop_to_done g x y r m0 c hI
    exact ⟨c', hs, hDone, halign⟩
  -- ret: 0x60 → r
  have hret : Triple (fun c => AtDone g x y r m0 c ∧ r.toNat % 4 = 0) (muldi3_post g x y r m0) := by
    intro c hc
    obtain ⟨⟨a1, a2, a3, hSt⟩, halign⟩ := hc
    obtain ⟨c', hs, hG, hmem, hpc, ha0, ha1, ha2, hra, htick, hframe⟩ := tr_60_ret g x y r (x*y) a1 a2 a3 m0 halign c hSt
    exact ⟨c', hs, hG, hmem, hpc, ha0, hra, htick, hframe⟩
  exact (hpre.seq hbody).seq hret

end Vsa.Sim
