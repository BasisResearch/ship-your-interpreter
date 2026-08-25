import Vsa.Sim.RegPins
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.Execute
import Vsa.Sim.RegAccess

/-!
# `BlockPilot` — proof-by-reflection block lemma for straight-line ALU runs (PILOT)

**Goal.** Replace the per-instruction site+ceremony composition (one `site_*`
lemma + ~8 `obs_*` transport lines per instruction) for *straight-line
ALU-register segments* by a single lemma, `block_alu_sound`, that consumes a
concrete `List AInstr` program description and produces the whole `Steps` chain
with a *computed* register outcome (`runG`) in one application.

**Scope (deliberately minimal).** ADDI-class register-immediate (`addi`/`mv`/
`li`, incl. `rs1 = x0`) and RTYPE `add` — the `stepObs_alu` shape with
`sigmaPost_alu` posts.  No loads/stores/branches/jumps, no width variants.

## Design

* `AInstr` — fully concrete per-instruction data: pc, the 4 LE code bytes, the
  assembled word, kind, GPR *indices* (`Nat`, not `Register`) and the ITYPE
  immediate.  Keeping indices as `Nat` sidesteps `RegisterType` heterogeneity:
  the four 33-branch dispatch batteries below (`rX_src`/`wX_gpr`/`obs_gpr_rd`/
  `obs_gpr_other`) case on the concrete index, so every branch sees a concrete
  register whose `RegisterType` reduces to `BitVec 64`.
* `GRegs = List (Nat × BitVec 64)` — symbolic register pins keyed by concrete
  GPR index (the `PinsHold` pattern of `RegPins.lean`, made *computable* on the
  key side so the block semantics `runG` can look sources up and thread
  updates).
* `ProgFacts` — the per-element non-computable obligations: 4 byte pins from a
  `Code.*Loaded` accessor, and a σ-generic decode fact (`DecodeFact`), which the
  DecodeTable lemmas `decode_<word>` inhabit *directly*.
* `BlockOK` — the computable VC: PC contiguity/range/alignment, byte/word
  coherence, non-RVC check, register-index bounds, and source-availability
  (domain threading), all `Decidable` and discharged by a single `by decide` at
  the application site (everything it inspects is concrete structure; the
  symbolic pin *values* are never consulted — the `pinsAvoid` discipline).
* `block_alu_sound` — proved once by list induction, each step through
  `stepObs_alu`; register-disequality side conditions at *symbolic* index are
  closed by two bounded-∀ `decide` lemmas (`gpr_rd_ok`, `gprReg_beq_false`)
  rather than per-site `by decide`s.

## Measured verdict (acceptance test: the 3-mv chain `0x800143b4–0x800143bc`
of `__ssputs_r`, real byte pins + DecodeTable lemmas, vs the same 3 steps via
`site_143b4_sp`/`site_143b8_sp`/`site_143bc_sp` + `tr_setup_mv`-style ceremony;
both derive the identical statement: `Steps (u+3)`, tick, `GoodState`, mem,
`PC = 0x800143c0`, the three written registers, minstret, and an `x10` frame)

* wall-clock `lake env lean` on the *use* site (5 runs each): reflection
  **0.97–1.02 s** vs ceremony **1.01–1.03 s** — a wash; both are dominated by
  the ≈ 0.55 s olean import of the `SsputsSites` closure.
* `lean --profile` proof-work (elaboration + tactics + kernel): reflection
  **≈ 57 ms** (15.3 + 31.7 + 10.2) vs ceremony **≈ 95 ms** (13.2 + 72.6 + 8.7)
  — ≈ 1.7× less tactic work at 3 instructions.  Reflection's tactic cost is
  two `decide`s (near-constant per block, tiny per-instruction VC evaluation);
  ceremony's is per-instruction × per-tracked-register (`obs_*` transports and
  their `by decide` batteries), so the gap grows with block length and pin
  count (ceremony O(instrs × regs), reflection O(instrs) with small constants).
* line count (identical theorem statement): ceremony **67** lines (≈ 50-line
  body; ≈ 13–16 lines per instruction, and each additional *tracked register*
  adds a transport line per instruction) vs reflection **36** lines (≈ 19-line
  body of which 5 are the `mvBlock` data list; marginal cost = 1 data line +
  2 `ProgFacts` entries per instruction, independent of tracked registers).
* one-time cost: this file (≈ 840 lines, of which ≈ 300 are the scripted
  dispatch batteries) compiles in **≈ 2.0 s**.

**Verdict: modest win now, structural win at scale.**  Wall-clock is a wash at
3 instructions (import-bound), but the reflection body is ≈ 2.6× smaller,
per-instruction cost is 1 data line instead of a dozen ceremony lines, and the
per-register transport dimension disappears entirely.

**Obstructions hit** (none fatal): (1) `RegisterType` heterogeneity forces the
`Nat`-indexed `gprGet`/`gprRT` dispatch layer — mechanical but 33 branches × 4
lemmas of one-time boilerplate; (2) `decide` cannot touch symbolic indices, so
all symbolic-index disequalities must be pre-packaged as bounded-∀ `decide`
lemmas (`gpr_rd_ok`, `gprReg_beq_false`); at the *use* site the same gotcha
transposes: `KeysOK (keysG L)`/`BlockOK … (keysG L) …` mention the symbolic pin
values through `L`, so the caller must close them as
`show KeysOK [14, 15] by decide` (the concrete-keys form) — the `pinsAvoid`
`rfl`-not-`decide` lesson in `Prop` clothing; (3) the DecodeTable is per-word
(no computable decoder on this side of the Sail model), so decode facts stay
*inputs* (`ProgFacts`) rather than being computed — reflection covers the
VC/frame/threading, not decode; (4) `omega`/`decide` do not see through
unreduced structure projections of a destructured `AInstr` — side conditions
must be restated (`have hrd31' : ard ≤ 31 := hrd31`) before automation.

## Generalizing beyond ALU

* **loads/stores**: `AInstr` grows an address expression over `GRegs` (base
  pin + concrete offset); `BlockOK` can no longer be fully decidable — address
  range/alignment/HTIF-window side conditions on *symbolic* addresses must move
  to `ProgFacts`-style per-element hypotheses (computed VCs); the state
  threading gains a memory component (`σ'.mem = m'` chains, `PinW`-style width
  handling for the loaded value).
* **branches**: a taken branch ends the block, so blocks become basic blocks
  and the lemma family needs a terminator case (`stepObs_branch_*` at the end,
  with the branch condition as a per-element hypothesis) — the list-induction
  skeleton is unchanged.
* **`x0` as `rd`** (nops): excluded (`1 ≤ rd`); would need a `wX_bits_zero`
  no-op branch in `wX_gpr` and a no-op `stepG`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Concrete `regidx` from a GPR index. -/
abbrev gprIdx (n : Nat) : regidx := regidx.Regidx (BitVec.ofNat 5 n)

/-! ## Symbolic GPR pin lists with computable keys -/

/-- Register pins keyed by GPR index: concrete keys, symbolic values. -/
abbrev GRegs := List (Nat × BitVec 64)

/-- Keys of a pin list. -/
def keysG : GRegs → List Nat
  | [] => []
  | (n, _) :: L => n :: keysG L

/-- Association lookup (first hit). -/
def lookupG (n : Nat) : GRegs → Option (BitVec 64)
  | [] => none
  | (m, v) :: L => if m = n then some v else lookupG n L

/-- Remove *all* entries with key `n`. -/
def eraseG (n : Nat) : GRegs → GRegs
  | [] => []
  | (m, v) :: L => if m = n then eraseG n L else (m, v) :: eraseG n L

/-- All keys are real GPR indices (`1..31`). -/
abbrev KeysOK (d : List Nat) : Prop := ∀ n ∈ d, 1 ≤ n ∧ n ≤ 31
/-- GPR index → `Register` (`1..31 ↦ x1..x31`).  `0` and `≥ 32` map to the junk
default `x1`; every lemma about `gprReg` carries `1 ≤ n`/`n ≤ 31` bounds (or, for
sources, handles `0` separately via `rX_bits_zero`), so the junk values are never
consulted. -/
def gprReg : Nat → Register
  | 1 => Register.x1
  | 2 => Register.x2
  | 3 => Register.x3
  | 4 => Register.x4
  | 5 => Register.x5
  | 6 => Register.x6
  | 7 => Register.x7
  | 8 => Register.x8
  | 9 => Register.x9
  | 10 => Register.x10
  | 11 => Register.x11
  | 12 => Register.x12
  | 13 => Register.x13
  | 14 => Register.x14
  | 15 => Register.x15
  | 16 => Register.x16
  | 17 => Register.x17
  | 18 => Register.x18
  | 19 => Register.x19
  | 20 => Register.x20
  | 21 => Register.x21
  | 22 => Register.x22
  | 23 => Register.x23
  | 24 => Register.x24
  | 25 => Register.x25
  | 26 => Register.x26
  | 27 => Register.x27
  | 28 => Register.x28
  | 29 => Register.x29
  | 30 => Register.x30
  | 31 => Register.x31
  | 0 => Register.x1
  | _+32 => Register.x1

/-- Homogeneous (`BitVec 64`-valued) GPR read, dispatching the heterogeneous
`RegisterType` register file by concrete index.  This is the type-level trick that
confines the pilot to GPRs: each branch has a *concrete* register, so
`RegisterType Register.x<k>` reduces to `BitVec 64` and no cast is needed. -/
def gprGet (σ : MState) : Nat → Option (BitVec 64)
  | 1 => σ.regs.get? Register.x1
  | 2 => σ.regs.get? Register.x2
  | 3 => σ.regs.get? Register.x3
  | 4 => σ.regs.get? Register.x4
  | 5 => σ.regs.get? Register.x5
  | 6 => σ.regs.get? Register.x6
  | 7 => σ.regs.get? Register.x7
  | 8 => σ.regs.get? Register.x8
  | 9 => σ.regs.get? Register.x9
  | 10 => σ.regs.get? Register.x10
  | 11 => σ.regs.get? Register.x11
  | 12 => σ.regs.get? Register.x12
  | 13 => σ.regs.get? Register.x13
  | 14 => σ.regs.get? Register.x14
  | 15 => σ.regs.get? Register.x15
  | 16 => σ.regs.get? Register.x16
  | 17 => σ.regs.get? Register.x17
  | 18 => σ.regs.get? Register.x18
  | 19 => σ.regs.get? Register.x19
  | 20 => σ.regs.get? Register.x20
  | 21 => σ.regs.get? Register.x21
  | 22 => σ.regs.get? Register.x22
  | 23 => σ.regs.get? Register.x23
  | 24 => σ.regs.get? Register.x24
  | 25 => σ.regs.get? Register.x25
  | 26 => σ.regs.get? Register.x26
  | 27 => σ.regs.get? Register.x27
  | 28 => σ.regs.get? Register.x28
  | 29 => σ.regs.get? Register.x29
  | 30 => σ.regs.get? Register.x30
  | 31 => σ.regs.get? Register.x31
  | 0 => none
  | _+32 => none

/-- Inject a `BitVec 64` into `RegisterType (gprReg n)` (definitionally the
identity in every branch — all GPRs and the junk default are `BitVec 64`). -/
def gprRT : (n : Nat) → BitVec 64 → RegisterType (gprReg n)
  | 1, v => v
  | 2, v => v
  | 3, v => v
  | 4, v => v
  | 5, v => v
  | 6, v => v
  | 7, v => v
  | 8, v => v
  | 9, v => v
  | 10, v => v
  | 11, v => v
  | 12, v => v
  | 13, v => v
  | 14, v => v
  | 15, v => v
  | 16, v => v
  | 17, v => v
  | 18, v => v
  | 19, v => v
  | 20, v => v
  | 21, v => v
  | 22, v => v
  | 23, v => v
  | 24, v => v
  | 25, v => v
  | 26, v => v
  | 27, v => v
  | 28, v => v
  | 29, v => v
  | 30, v => v
  | 31, v => v
  | 0, v => v
  | _+32, v => v
/-! ## Pin satisfaction and the bounded-∀ `decide` battery

`decide` rejects open terms, so every side condition the induction needs at a
*symbolic* GPR index is pre-packaged here as a bounded-∀ statement over `n < 32`
(decidable via `Nat.decidableBallLT`) and closed by one kernel `decide` each. -/

/-- All pins hold (`gprGet`-phrased `PinsHold`). -/
def GHolds (σ : MState) : GRegs → Prop
  | [] => True
  | (n, v) :: L => gprGet σ n = some v ∧ GHolds σ L

/-- What a *source* read of index `n` requires of `σ`: nothing for `x0` (the
value is `0`), the `gprGet` pin otherwise. -/
def srcPin (σ : MState) : Nat → BitVec 64 → Prop
  | 0, v => v = 0#64
  | m+1, v => gprGet σ (m+1) = some v

/-- Symbolic source value from the pin list (`x0 ↦ 0`). -/
def srcVal (n : Nat) (L : GRegs) : BitVec 64 :=
  match n with
  | 0 => 0#64
  | m+1 => (lookupG (m+1) L).getD 0#64

/-- The written GPR avoids the non-noise pinned/step registers, and is
`NonPinned` — everything `stepObs_alu` needs of a symbolic `rd` index. -/
theorem gpr_rd_ok : ∀ n, n < 32 → 1 ≤ n →
    ((gprReg n == Register.nextPC) = false ∧
     (gprReg n == Register.minstret_increment) = false ∧
     (gprReg n == Register.minstret) = false ∧
     (gprReg n == Register.hart_state) = false ∧
     NonPinned (gprReg n)) := by decide

/-- `gprReg` is injective on `1..31`, `==`-phrased for the `obs_*` consumers. -/
theorem gprReg_beq_false : ∀ n, n < 32 → ∀ m, m < 32 → 1 ≤ n → 1 ≤ m → n ≠ m →
    (gprReg n == gprReg m) = false := by decide
/-- Generic GPR *source* read at the execute-time state
`afterNextPC (afterPrelude σ) pc`, dispatching to the `rX_bits_x<k>` battery
(`RegAccess.lean`) — `x0` reads `0` via `rX_bits_zero`. -/
theorem rX_src (σ : MState) (pc : BitVec 64) :
    ∀ (n : Nat), n ≤ 31 → ∀ (v : BitVec 64), srcPin σ n v →
    (rX_bits (gprIdx n)).run (afterNextPC (afterPrelude σ) pc)
      = .ok v (afterNextPC (afterPrelude σ) pc)
  | 0, _, v, h => by rw [show v = 0#64 from h]; exact rX_bits_zero _
  | 1, _, v, h => rX_bits_x1 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 2, _, v, h => rX_bits_x2 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 3, _, v, h => rX_bits_x3 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 4, _, v, h => rX_bits_x4 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 5, _, v, h => rX_bits_x5 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 6, _, v, h => rX_bits_x6 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 7, _, v, h => rX_bits_x7 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 8, _, v, h => rX_bits_x8 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 9, _, v, h => rX_bits_x9 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 10, _, v, h => rX_bits_x10 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 11, _, v, h => rX_bits_x11 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 12, _, v, h => rX_bits_x12 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 13, _, v, h => rX_bits_x13 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 14, _, v, h => rX_bits_x14 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 15, _, v, h => rX_bits_x15 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 16, _, v, h => rX_bits_x16 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 17, _, v, h => rX_bits_x17 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 18, _, v, h => rX_bits_x18 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 19, _, v, h => rX_bits_x19 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 20, _, v, h => rX_bits_x20 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 21, _, v, h => rX_bits_x21 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 22, _, v, h => rX_bits_x22 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 23, _, v, h => rX_bits_x23 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 24, _, v, h => rX_bits_x24 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 25, _, v, h => rX_bits_x25 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 26, _, v, h => rX_bits_x26 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 27, _, v, h => rX_bits_x27 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 28, _, v, h => rX_bits_x28 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 29, _, v, h => rX_bits_x29 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 30, _, v, h => rX_bits_x30 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 31, _, v, h => rX_bits_x31 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | _+32, hn, _, _ => absurd hn (by omega)

/-- Generic GPR write, dispatching to the `wX_bits_x<k>` battery: the write is
the single insert `regs.insert (gprReg n) (gprRT n d)`. -/
theorem wX_gpr (s : MState) (d : BitVec 64) :
    ∀ (n : Nat), 1 ≤ n → n ≤ 31 →
    (wX_bits (gprIdx n) d).run s
      = .ok () {s with regs := s.regs.insert (gprReg n) (gprRT n d)}
  | 0, h, _ => absurd h (by omega)
  | 1, _, _ => wX_bits_x1 s d
  | 2, _, _ => wX_bits_x2 s d
  | 3, _, _ => wX_bits_x3 s d
  | 4, _, _ => wX_bits_x4 s d
  | 5, _, _ => wX_bits_x5 s d
  | 6, _, _ => wX_bits_x6 s d
  | 7, _, _ => wX_bits_x7 s d
  | 8, _, _ => wX_bits_x8 s d
  | 9, _, _ => wX_bits_x9 s d
  | 10, _, _ => wX_bits_x10 s d
  | 11, _, _ => wX_bits_x11 s d
  | 12, _, _ => wX_bits_x12 s d
  | 13, _, _ => wX_bits_x13 s d
  | 14, _, _ => wX_bits_x14 s d
  | 15, _, _ => wX_bits_x15 s d
  | 16, _, _ => wX_bits_x16 s d
  | 17, _, _ => wX_bits_x17 s d
  | 18, _, _ => wX_bits_x18 s d
  | 19, _, _ => wX_bits_x19 s d
  | 20, _, _ => wX_bits_x20 s d
  | 21, _, _ => wX_bits_x21 s d
  | 22, _, _ => wX_bits_x22 s d
  | 23, _, _ => wX_bits_x23 s d
  | 24, _, _ => wX_bits_x24 s d
  | 25, _, _ => wX_bits_x25 s d
  | 26, _, _ => wX_bits_x26 s d
  | 27, _, _ => wX_bits_x27 s d
  | 28, _, _ => wX_bits_x28 s d
  | 29, _, _ => wX_bits_x29 s d
  | 30, _, _ => wX_bits_x30 s d
  | 31, _, _ => wX_bits_x31 s d
  | _+32, _, h => absurd h (by omega)

/-- Read the written GPR back out of an ALU observation, `gprGet`-phrased. -/
theorem obs_gpr_rd {σ' σ : MState} {pc vm : BitVec 64} :
    ∀ (n : Nat), 1 ≤ n → n ≤ 31 → ∀ (v : BitVec 64),
    ReadsLikePost σ' (sigmaPost_alu σ pc vm (gprReg n) (gprRT n v)) →
    gprGet σ' n = some v
  | 0, h, _, _, _ => absurd h (by omega)
  | 1, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 2, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 3, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 4, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 5, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 6, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 7, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 8, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 9, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 10, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 11, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 12, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 13, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 14, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 15, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 16, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 17, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 18, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 19, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 20, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 21, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 22, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 23, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 24, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 25, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 26, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 27, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 28, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 29, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 30, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 31, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | _+32, _, h, _, _ => absurd h (by omega)

/-- Transport a `gprGet` pin on `m` (with `gprReg n ≠ gprReg m`) through an ALU
step writing `gprReg n`. -/
theorem obs_gpr_other {σ' σ : MState} {pc vm : BitVec 64} {n : Nat} {v : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm (gprReg n) (gprRT n v))) :
    ∀ (m : Nat), 1 ≤ m → m ≤ 31 → (gprReg n == gprReg m) = false →
    ∀ (w : BitVec 64), gprGet σ m = some w → gprGet σ' m = some w
  | 0, h, _, _, _, _ => absurd h (by omega)
  | 1, _, _, hne, w, h => obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 2, _, _, hne, w, h => obs_alu_other hobs Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 3, _, _, hne, w, h => obs_alu_other hobs Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 4, _, _, hne, w, h => obs_alu_other hobs Register.x4 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 5, _, _, hne, w, h => obs_alu_other hobs Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 6, _, _, hne, w, h => obs_alu_other hobs Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 7, _, _, hne, w, h => obs_alu_other hobs Register.x7 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 8, _, _, hne, w, h => obs_alu_other hobs Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 9, _, _, hne, w, h => obs_alu_other hobs Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 10, _, _, hne, w, h => obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 11, _, _, hne, w, h => obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 12, _, _, hne, w, h => obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 13, _, _, hne, w, h => obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 14, _, _, hne, w, h => obs_alu_other hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 15, _, _, hne, w, h => obs_alu_other hobs Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 16, _, _, hne, w, h => obs_alu_other hobs Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 17, _, _, hne, w, h => obs_alu_other hobs Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 18, _, _, hne, w, h => obs_alu_other hobs Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 19, _, _, hne, w, h => obs_alu_other hobs Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 20, _, _, hne, w, h => obs_alu_other hobs Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 21, _, _, hne, w, h => obs_alu_other hobs Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 22, _, _, hne, w, h => obs_alu_other hobs Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 23, _, _, hne, w, h => obs_alu_other hobs Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 24, _, _, hne, w, h => obs_alu_other hobs Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 25, _, _, hne, w, h => obs_alu_other hobs Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 26, _, _, hne, w, h => obs_alu_other hobs Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 27, _, _, hne, w, h => obs_alu_other hobs Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 28, _, _, hne, w, h => obs_alu_other hobs Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 29, _, _, hne, w, h => obs_alu_other hobs Register.x29 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 30, _, _, hne, w, h => obs_alu_other hobs Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 31, _, _, hne, w, h => obs_alu_other hobs Register.x31 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | _+32, _, h, _, _, _ => absurd h (by omega)
/-! ## Support lemmas: lookup/erase/pin-transport -/

theorem gholds_lookup {σ : MState} {n : Nat} {v : BitVec 64} :
    ∀ (L : GRegs), GHolds σ L → lookupG n L = some v → gprGet σ n = some v := by
  intro L
  induction L with
  | nil => intro _ hlk; exact nomatch hlk
  | cons p L ih =>
    obtain ⟨m, w⟩ := p
    intro hL hlk
    simp only [lookupG] at hlk
    split at hlk
    · next heq => cases hlk; exact heq ▸ hL.1
    · exact ih hL.2 hlk

theorem lookup_of_mem {n : Nat} :
    ∀ (L : GRegs), n ∈ keysG L → ∃ v, lookupG n L = some v := by
  intro L
  induction L with
  | nil => intro h; exact nomatch h
  | cons p L ih =>
    obtain ⟨m, w⟩ := p
    intro h
    simp only [lookupG]
    split
    · exact ⟨w, rfl⟩
    · next hne =>
      have h' : n ∈ m :: keysG L := h
      cases h' with
      | head => exact absurd rfl hne
      | tail _ htl => exact ih htl

theorem mem_of_mem_keysG_eraseG {n k : Nat} :
    ∀ (L : GRegs), k ∈ keysG (eraseG n L) → k ∈ keysG L := by
  intro L
  induction L with
  | nil => intro h; exact nomatch h
  | cons p L ih =>
    obtain ⟨m, w⟩ := p
    intro h
    simp only [eraseG] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · have h' : k ∈ m :: keysG (eraseG n L) := h
      cases h' with
      | head => exact List.mem_cons_self ..
      | tail _ htl => exact List.mem_cons_of_mem _ (ih htl)

theorem mem_keysG_eraseG {n k : Nat} (hne : k ≠ n) :
    ∀ (L : GRegs), k ∈ keysG L → k ∈ keysG (eraseG n L) := by
  intro L
  induction L with
  | nil => intro h; exact nomatch h
  | cons p L ih =>
    obtain ⟨m, w⟩ := p
    intro h
    have h' : k ∈ m :: keysG L := h
    simp only [eraseG]
    split
    · next heq =>
      cases h' with
      | head => exact absurd heq hne
      | tail _ htl => exact ih htl
    · cases h' with
      | head => exact List.mem_cons_self ..
      | tail _ htl => exact List.mem_cons_of_mem _ (ih htl)

/-- Pins with keys ≠ the written index survive an ALU step (all stale entries
for the written key having been erased). -/
theorem gholds_eraseG {σ' σ : MState} {pc vm : BitVec 64} {n : Nat} {v : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm (gprReg n) (gprRT n v)))
    (hn1 : 1 ≤ n) (hn31 : n ≤ 31) :
    ∀ (L : GRegs), KeysOK (keysG L) → GHolds σ L → GHolds σ' (eraseG n L) := by
  intro L
  induction L with
  | nil => intro _ _; exact trivial
  | cons p L ih =>
    obtain ⟨m, w⟩ := p
    intro hK hL
    simp only [eraseG]
    split
    · exact ih (fun k hk => hK k (List.mem_cons_of_mem _ hk)) hL.2
    · next hne =>
      have hm := hK m (List.mem_cons_self ..)
      exact ⟨obs_gpr_other hobs m hm.1 hm.2
        (gprReg_beq_false n (by omega) m (by omega) hn1 hm.1 (fun e => hne e.symm)) w hL.1,
        ih (fun k hk => hK k (List.mem_cons_of_mem _ hk)) hL.2⟩

/-- The source-read obligation is met by the pin list (`x0` trivially). -/
theorem srcPin_srcVal (σ : MState) (L : GRegs) :
    ∀ (n : Nat), (n = 0 ∨ n ∈ keysG L) → GHolds σ L → srcPin σ n (srcVal n L)
  | 0, _, _ => rfl
  | m+1, hok, hL => by
    obtain ⟨v, hv⟩ := lookup_of_mem L (hok.resolve_left (Nat.succ_ne_zero m))
    show gprGet σ (m+1) = some ((lookupG (m+1) L).getD 0#64)
    rw [hv]
    exact gholds_lookup L hL hv

/-! ## The program description -/

/-- Instruction kind: register-immediate `ADDI` (covers `addi`/`mv`/`li`) or
register-register `ADD`. -/
inductive AKind where
  | addi : AKind
  | add  : AKind
deriving DecidableEq

/-- One straight-line ALU instruction, fully concrete: address, the four LE code
bytes, the assembled word, and the operands as GPR *indices*.  `rs2` is unused
for `addi`, `imm` unused for `add`. -/
structure AInstr where
  pc   : BitVec 64
  word : BitVec 32
  b0   : BitVec 8
  b1   : BitVec 8
  b2   : BitVec 8
  b3   : BitVec 8
  kind : AKind
  rd   : Nat
  rs1  : Nat
  rs2  : Nat
  imm  : BitVec 12

/-- The decoded AST the DecodeTable lemma for `a.word` must produce. -/
def astOf (a : AInstr) : instruction :=
  match a.kind with
  | .addi => instruction.ITYPE (a.imm, gprIdx a.rs1, gprIdx a.rd, iop.ADDI)
  | .add  => instruction.RTYPE (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, rop.ADD)

/-- The written value, computed over the symbolic pin list. -/
def aluVal (a : AInstr) (L : GRegs) : BitVec 64 :=
  match a.kind with
  | .addi => srcVal a.rs1 L + sign_extend (m := 64) a.imm
  | .add  => srcVal a.rs1 L + srcVal a.rs2 L

/-- Pin-list effect of one instruction. -/
def stepG (a : AInstr) (L : GRegs) : GRegs :=
  (a.rd, aluVal a L) :: eraseG a.rd L

/-- Pin-list effect of the whole block: the computed register outcome. -/
def runG : List AInstr → GRegs → GRegs
  | [], L => L
  | a :: r, L => runG r (stepG a L)

/-- Fall-through end PC of the block. -/
def endPC (pc0 : BitVec 64) : List AInstr → BitVec 64
  | [] => pc0
  | a :: r => endPC (BitVec.addInt a.pc 4) r

/-! ## Per-element obligations (`ProgFacts`) and the computable VC (`BlockOK`) -/

/-- The four little-endian code-byte pins, stated on the block-invariant memory
`m0` (ALU steps never touch memory, so pins on the entry memory serve every
step). -/
def BytePins (m : Std.ExtHashMap Nat (BitVec 8)) (a : AInstr) : Prop :=
  m[a.pc.toNat]? = some a.b0 ∧ m[a.pc.toNat + 1]? = some a.b1 ∧
  m[a.pc.toNat + 2]? = some a.b2 ∧ m[a.pc.toNat + 3]? = some a.b3

/-- σ-generic decode fact for one element — the shape of the DecodeTable lemmas
`Vsa.Sim.DecodeTable.decode_<word>`, which inhabit this directly. -/
def DecodeFact (a : AInstr) : Prop :=
  ∀ s : SequentialState RegisterType trivialChoiceSource,
    s.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) →
    s.regs.get? Register.cur_privilege =
      some ((Privilege.Machine) : RegisterType Register.cur_privilege) →
    s.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) →
    (ext_decode a.word).run s = .ok (astOf a) s

/-- The non-computable per-element obligations: byte pins + decode facts. -/
def ProgFacts (m : Std.ExtHashMap Nat (BitVec 8)) : List AInstr → Prop
  | [] => True
  | a :: r => BytePins m a ∧ DecodeFact a ∧ ProgFacts m r

/-- Source-index obligation: a GPR index, and either `x0` or available in the
domain of pinned/previously-written registers. -/
abbrev SrcOK (n : Nat) (dom : List Nat) : Prop :=
  n ≤ 31 ∧ (n = 0 ∨ n ∈ dom)

/-- The computable per-instruction VC (all atoms decidable on the concrete
structure; symbolic pin *values* are never inspected). -/
abbrev InstrOK (pc0 : BitVec 64) (dom : List Nat) (a : AInstr) : Prop :=
  a.pc.toNat = pc0.toNat ∧
  (((a.b3.append a.b2).append a.b1).append a.b0).toNat = a.word.toNat ∧
  (Sail.BitVec.extractLsb (((a.b3.append a.b2).append a.b1).append a.b0) 1 0).toNat
    = (0b11#2 : BitVec 2).toNat ∧
  0x80000000 ≤ a.pc.toNat ∧
  a.pc.toNat + 4 ≤ tohostAddr ∧
  a.pc.toNat % 4 = 0 ∧
  1 ≤ a.rd ∧ a.rd ≤ 31 ∧
  SrcOK a.rs1 dom ∧
  (¬ a.kind = AKind.add ∨ SrcOK a.rs2 dom)

/-- The block VC: per-instruction VCs with PC contiguity and source-domain
threading (`dom` accumulates written registers). -/
def BlockOK (pc0 : BitVec 64) (dom : List Nat) : List AInstr → Prop
  | [] => True
  | a :: r => InstrOK pc0 dom a ∧ BlockOK (BitVec.addInt a.pc 4) (a.rd :: dom) r

instance instDecBlockOK (pc0 : BitVec 64) (dom : List Nat) :
    (is : List AInstr) → Decidable (BlockOK pc0 dom is)
  | [] => isTrue trivial
  | a :: r =>
    have : Decidable (BlockOK (BitVec.addInt a.pc 4) (a.rd :: dom) r) :=
      instDecBlockOK _ _ r
    inferInstanceAs (Decidable (_ ∧ _))

/-! ## The block lemma -/

/-- Generalized form: `dom` is any under-approximation of the pinned keys.
Proved by one list induction; each step goes through `stepObs_alu`. -/
theorem block_alu_run (is : List AInstr) :
    ∀ (σ : MState) (i u : Nat) (pc0 vm : BitVec 64) (L : GRegs)
      (m0 : Std.ExtHashMap Nat (BitVec 8)) (dom : List Nat),
    GoodState σ →
    σ.regs.get? Register.PC = some pc0 →
    σ.regs.get? Register.minstret = some vm →
    σ.mem = m0 →
    GHolds σ L →
    KeysOK (keysG L) →
    (∀ n ∈ dom, n ∈ keysG L) →
    ProgFacts m0 is →
    BlockOK pc0 dom is →
    i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + is.length⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = m0 ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (endPC pc0 is) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runG is L) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ a ∈ is, (gprReg a.rd == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  induction is with
  | nil =>
    intro σ i u pc0 vm L m0 dom hG hpc hmi hmem hL _ _ _ _ hi
    exact ⟨σ, i, Steps.refl _, hi, hG, hmem, rfl, hpc, ⟨vm, hmi⟩, hL, fun R _ _ => rfl⟩
  | cons a r ih =>
    intro σ i u pc0 vm L m0 dom hG hpc hmi hmem hL hkeys hdom hfacts hwf hi
    obtain ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ := a
    have hfacts' : BytePins m0 ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        DecodeFact ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        ProgFacts m0 r := hfacts
    obtain ⟨hbp, hdec, hfr⟩ := hfacts'
    have hwf' : InstrOK pc0 dom ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        BlockOK (BitVec.addInt apc 4) (ard :: dom) r := hwf
    obtain ⟨hwfa, hwfr⟩ := hwf'
    obtain ⟨hpcn, hwn, hrvcn, hlo, hhi, halign, hrd1, hrd31, hs1ok, hs2ok⟩ := hwfa
    have hpceq : apc = pc0 := BitVec.eq_of_toNat_eq hpcn
    subst hpceq
    have hword : (((ab3.append ab2).append ab1).append ab0) = aword :=
      BitVec.eq_of_toNat_eq hwn
    have hnotrvc : Sail.BitVec.extractLsb (((ab3.append ab2).append ab1).append ab0) 1 0
        = (0b11#2 : BitVec 2) := BitVec.eq_of_toNat_eq hrvcn
    have hb0 : σ.mem[apc.toNat]? = some ab0 := by rw [hmem]; exact hbp.1
    have hb1 : σ.mem[apc.toNat + 1]? = some ab1 := by rw [hmem]; exact hbp.2.1
    have hb2 : σ.mem[apc.toNat + 2]? = some ab2 := by rw [hmem]; exact hbp.2.2.1
    have hb3 : σ.mem[apc.toNat + 3]? = some ab3 := by rw [hmem]; exact hbp.2.2.2
    have hdec' := hdec (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg)
    have hrd31' : ard ≤ 31 := hrd31
    have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
    have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
      srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
    have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
    cases akind with
    | addi =>
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L + sign_extend (m := 64) aimm) ard hrd1 hrd31
      have hexec := execute_itype_addi_char aimm (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (srcVal ars1 L + sign_extend (m := 64) aimm)))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.ITYPE (aimm, gprIdx ars1, gprIdx ard, iop.ADDI))
          (gprReg ard) (gprRT ard (srcVal ars1 L + sign_extend (m := 64) aimm))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepG ⟨apc, aword, ab0, ab1, ab2, ab3, .addi, ard, ars1, ars2, aimm⟩ L) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (srcVal ars1 L + sign_extend (m := 64) aimm) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepG ⟨apc, aword, ab0, ab1, ab2, ab3, .addi, ard, ars1, ars2, aimm⟩ L)) := by
        intro k hk
        have hk' : k ∈ ard :: keysG (eraseG ard L) := hk
        cases hk' with
        | head => exact ⟨hrd1, hrd31⟩
        | tail _ h => exact hkeys k (mem_of_mem_keysG_eraseG L h)
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepG ⟨apc, aword, ab0, ab1, ab2, ab3, .addi, ard, ars1, ars2, aimm⟩ L) := by
        intro n hn
        show n ∈ ard :: keysG (eraseG ard L)
        cases hn with
        | head => exact List.mem_cons_self ..
        | tail _ h =>
          cases Nat.decEq n ard with
          | isTrue e => rw [e]; exact List.mem_cons_self ..
          | isFalse ne => exact List.mem_cons_of_mem _ (mem_keysG_eraseG ne L (hdom n h))
      have hmem1' : σ1.mem = m0 := hmem1.trans hmem
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepG ⟨apc, aword, ab0, ab1, ab2, ab3, .addi, ard, ars1, ars2, aimm⟩ L)
          m0 (ard :: dom) hG1 hpc1 hmi1 hmem1' hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        have h1 : σ1.regs.get? R = σ.regs.get? R :=
          (hobs1.1 R (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
            (hn Register.mip (by decide))).trans
            (get?_sigmaPost_alu σ apc vm (gprReg ard) _ R
              (hn Register.minstret (by decide)) (hn Register.PC (by decide))
              (hrds _ (List.mem_cons_self ..)) (hn Register.nextPC (by decide))
              (hn Register.minstret_increment (by decide)))
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans h1
    | add =>
      have hsp2ok : SrcOK ars2 dom := hs2ok.resolve_left (fun h => h rfl)
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hsp2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hsp2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L + srcVal ars2 L) ard hrd1 hrd31
      have hexec := execute_rtype_add_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (srcVal ars1 L + srcVal ars2 L)))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPE (gprIdx ars2, gprIdx ars1, gprIdx ard, rop.ADD))
          (gprReg ard) (gprRT ard (srcVal ars1 L + srcVal ars2 L))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepG ⟨apc, aword, ab0, ab1, ab2, ab3, .add, ard, ars1, ars2, aimm⟩ L) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (srcVal ars1 L + srcVal ars2 L) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepG ⟨apc, aword, ab0, ab1, ab2, ab3, .add, ard, ars1, ars2, aimm⟩ L)) := by
        intro k hk
        have hk' : k ∈ ard :: keysG (eraseG ard L) := hk
        cases hk' with
        | head => exact ⟨hrd1, hrd31⟩
        | tail _ h => exact hkeys k (mem_of_mem_keysG_eraseG L h)
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepG ⟨apc, aword, ab0, ab1, ab2, ab3, .add, ard, ars1, ars2, aimm⟩ L) := by
        intro n hn
        show n ∈ ard :: keysG (eraseG ard L)
        cases hn with
        | head => exact List.mem_cons_self ..
        | tail _ h =>
          cases Nat.decEq n ard with
          | isTrue e => rw [e]; exact List.mem_cons_self ..
          | isFalse ne => exact List.mem_cons_of_mem _ (mem_keysG_eraseG ne L (hdom n h))
      have hmem1' : σ1.mem = m0 := hmem1.trans hmem
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepG ⟨apc, aword, ab0, ab1, ab2, ab3, .add, ard, ars1, ars2, aimm⟩ L)
          m0 (ard :: dom) hG1 hpc1 hmi1 hmem1' hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        have h1 : σ1.regs.get? R = σ.regs.get? R :=
          (hobs1.1 R (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
            (hn Register.mip (by decide))).trans
            (get?_sigmaPost_alu σ apc vm (gprReg ard) _ R
              (hn Register.minstret (by decide)) (hn Register.PC (by decide))
              (hrds _ (List.mem_cons_self ..)) (hn Register.nextPC (by decide))
              (hn Register.minstret_increment (by decide)))
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans h1

/-- **The block lemma.** A concrete list of straight-line ALU instructions,
whose byte pins + decode facts are supplied (`ProgFacts`) and whose computable
VC holds (`BlockOK …`, one `by decide`), turns an entry state with pinned PC /
minstret / source registers (`GHolds`) into the full `Steps` chain with:
tick invariant, `GoodState`, memory and HTIF output unchanged, the fall-through
PC, and the *computed* register outcome `runG is L` — plus the register frame
for everything outside `noiseRegs ∪ {rd}`s (consumable by `pins_of_frame`). -/
theorem block_alu_sound (is : List AInstr) (σ : MState) (i u : Nat)
    (pc0 vm : BitVec 64) (L : GRegs)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hL : GHolds σ L)
    (hkeys : KeysOK (keysG L))
    (hfacts : ProgFacts σ.mem is)
    (hwf : BlockOK pc0 (keysG L) is)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + is.length⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (endPC pc0 is) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runG is L) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ a ∈ is, (gprReg a.rd == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) :=
  block_alu_run is σ i u pc0 vm L σ.mem (keysG L)
    hG hpc hmi rfl hL hkeys (fun _ h => h) hfacts hwf hi

end Vsa.Sim
