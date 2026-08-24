import Vsa.Sim.StepAlu
import Vsa.Sim.StepBranch
import Vsa.Sim.StepJump
import Vsa.Sim.StepStore

/-!
# Layer 3 — parity-agnostic **observational** step wrappers (`StepObs`)

The M3 method pilot's central design move. The Layer-0/2 step lemmas
(`step_alu_notick`/`step_alu_tick`, `step_branch_*_notick`/`_tick`,
`step_jr_notick`/`_tick`, …) come in **two** variants because `stepOnce` ticks
the platform clock every `plat_insns_per_tick = 2` retired instructions: on the
`i+1 = 2` boundary the post-state additionally carries `tick_clock`'s
`mcycle`/`mtime`/`mip` writes (`sigmaTick_*`), off the boundary it does not
(`sigmaPost_*`). A Layer-3 function spec must be **parity-agnostic**: the caller
does not know the tick counter's parity at the entry PC, and must not care.

This file provides, for each instruction class used by `__muldi3`, **one**
observational step wrapper that folds both variants into a single statement:

> for any `i < 2`, there is a successor state `σ'` and counter `i' < 2` with
> `Step ⟨σ,i,u⟩ ⟨σ',i',u+1⟩`, `GoodState σ'`, `σ'.mem = σ.mem`, and the
> **observable** reads — `PC`, the written GPR, and every *other* GPR — all
> given by `get?` equalities that hold **whichever** variant fired.

The tick/notick difference lives entirely in the *unmentioned* noise registers
(`mcycle`/`mtime`/`mip`); reading any GPR or the PC through the tick chain
reduces to reading it through `sigmaPost` (the three tick inserts are on pinned,
non-GPR registers). So the observational conjunction is *identical* for the two
variants, and the parity split disappears.

`i < 2` is the tick invariant: `stepOnce` keeps `i ∈ {0,1}` (it resets to `0` on
the tick boundary and otherwise increments `0 ↦ 1`). Carrying `i < 2` in the
Layer-3 invariant lets the loop re-enter with the counter unconstrained.

## The read-back lemmas

`get?_gpr_tickchain` reduces a `get? R` through the three tick inserts to a
`get? R` on the base state, given `R ∉ {mcycle, mtime, mip}` (all `by decide`
for a concrete GPR/PC). Composed with the existing `get?_sigmaPost_*` read-backs
(from `StepAlu`/`StepBranch`/`StepJump`), it gives one uniform read-back that
serves both variants.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Tick-chain read-back: the three tick inserts are transparent to GPR/PC

For each family the `sigmaTick_*` state is `sigmaPost_* + {mcycle, mtime, mip}`
inserts. Reading `R ∉ {mcycle, mtime, mip}` (every GPR and the PC) through those
three inserts sees straight through to `sigmaPost_*`. These are the read-backs
that render the observational conjunction parity-agnostic. -/

/-- ALU: GPR/PC read-back through the tick chain drops to `sigmaPost_alu`. -/
theorem get?_sigmaTick_alu (σ : MState) (pc vminstret : BitVec 64) (rd_reg : Register)
    (v : RegisterType rd_reg) (vmip vmtime vmtimecmp vmcycle : BitVec 64) (R : Register)
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false) :
    (sigmaTick_alu σ pc vminstret rd_reg v vmip vmtime vmtimecmp vmcycle).regs.get? R
      = (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? R := by
  show (((((sigmaPost_alu σ pc vminstret rd_reg v).regs.insert Register.mcycle _).insert
      Register.mtime _).insert Register.mip _)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmi, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmt, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmc, dif_neg, reduceCtorEq, not_false_eq_true]

/-- Taken branch: GPR/PC read-back through the tick chain drops to `sigmaPost`. -/
theorem get?_sigmaTick_branch_taken (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) (R : Register)
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false) :
    (sigmaTick_branch_taken σ pc vminstret imm vmip vmtime vmtimecmp vmcycle).regs.get? R
      = (sigmaPost_branch_taken σ pc vminstret imm).regs.get? R := by
  show (((((sigmaPost_branch_taken σ pc vminstret imm).regs.insert Register.mcycle _).insert
      Register.mtime _).insert Register.mip _)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmi, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmt, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmc, dif_neg, reduceCtorEq, not_false_eq_true]

/-- Not-taken branch: GPR/PC read-back through the tick chain drops to `sigmaPost`. -/
theorem get?_sigmaTick_branch_nottaken (σ : MState) (pc vminstret : BitVec 64)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) (R : Register)
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false) :
    (sigmaTick_branch_nottaken σ pc vminstret vmip vmtime vmtimecmp vmcycle).regs.get? R
      = (sigmaPost_branch_nottaken σ pc vminstret).regs.get? R := by
  show (((((sigmaPost_branch_nottaken σ pc vminstret).regs.insert Register.mcycle _).insert
      Register.mtime _).insert Register.mip _)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmi, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmt, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmc, dif_neg, reduceCtorEq, not_false_eq_true]

/-- Jump `x0` (`ret`): GPR/PC read-back through the tick chain drops to `sigmaPost`. -/
theorem get?_sigmaTick_jump_x0 (σ : MState) (pc vminstret tgt : BitVec 64)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) (R : Register)
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false) :
    (sigmaTick_jump_x0 σ pc vminstret tgt vmip vmtime vmtimecmp vmcycle).regs.get? R
      = (sigmaPost_jump_x0 σ pc vminstret tgt).regs.get? R := by
  show (((((sigmaPost_jump_x0 σ pc vminstret tgt).regs.insert Register.mcycle _).insert
      Register.mtime _).insert Register.mip _)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmi, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmt, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmc, dif_neg, reduceCtorEq, not_false_eq_true]

/-! ## The parity-agnostic observation relation

`ReadsLikePost σ' spost` says `σ'` reads identically to the notick post-state
`spost` on **every register outside the tick write-set** `{mcycle, mtime, mip}`.
This is the observational payload the step wrappers deliver: it holds for `spost`
itself (trivially) and for the tick state `spost + tick_clock` (by the
`get?_sigmaTick_*` read-backs), so a single wrapper covers both parities. The
caller reads the PC and GPRs off `spost` via the existing `get?_sigmaPost_*` /
`get?_sigma3_*` frame lemmas, wrapped through `ReadsLikePost`. -/

/-- `σ'` reads like the notick post-state `spost` on all non-tick registers,
**and** carries the same `sailOutput` (HTIF console). The register conjunct is
the historical payload (unchanged arity for the `∀ R …` reader — direct
applications become `hobs.1 R …`); the second conjunct threads output invariance
step-by-step, mirroring the `mem`/`tick<2` observables. Every step used here is a
regs+mem update over `afterNextPC (afterPrelude σ) pc` — `sailOutput` is untouched
(`rfl`), including the STORE class (the HTIF console append only fires inside the
model when the tohost window is hit, which the store lemmas exclude via `hhiwin`;
the post-state simply doesn't touch `sailOutput`). -/
def ReadsLikePost (σ' spost : MState) : Prop :=
  (∀ R : Register, (Register.mcycle == R) = false → (Register.mtime == R) = false →
    (Register.mip == R) = false → σ'.regs.get? R = spost.regs.get? R)
  ∧ σ'.sailOutput = spost.sailOutput

theorem ReadsLikePost.rfl (s : MState) : ReadsLikePost s s :=
  ⟨fun _ _ _ _ => Eq.refl _, Eq.refl _⟩

/-- Output-invariance consumer: `ReadsLikePost` gives `sailOutput` equality. -/
theorem ReadsLikePost.out {σ' spost : MState} (h : ReadsLikePost σ' spost) :
    σ'.sailOutput = spost.sailOutput := h.2

/-! ## Per-class `sailOutput` = `σ.sailOutput` (rfl)

Every `sigmaPost_*` state is a regs(+mem for STORE) update over
`afterNextPC (afterPrelude σ) pc`, none of which touches `sailOutput`. So each
class's post-state carries `σ`'s output verbatim. Callers chain these with
`ReadsLikePost.out` to thread output invariance step-by-step (exactly like the
`get?_sigmaPost_*` register frame + `mem`-unchanged threads). -/

theorem sailOutput_sigmaPost_alu (σ : MState) (pc vminstret : BitVec 64)
    (rd_reg : Register) (v : RegisterType rd_reg) :
    (sigmaPost_alu σ pc vminstret rd_reg v).sailOutput = σ.sailOutput := rfl

theorem sailOutput_sigmaPost_branch_taken (σ : MState) (pc vminstret : BitVec 64)
    (imm : BitVec 13) :
    (sigmaPost_branch_taken σ pc vminstret imm).sailOutput = σ.sailOutput := rfl

theorem sailOutput_sigmaPost_branch_nottaken (σ : MState) (pc vminstret : BitVec 64) :
    (sigmaPost_branch_nottaken σ pc vminstret).sailOutput = σ.sailOutput := rfl

theorem sailOutput_sigmaPost_jump_x0 (σ : MState) (pc vminstret tgt : BitVec 64) :
    (sigmaPost_jump_x0 σ pc vminstret tgt).sailOutput = σ.sailOutput := rfl

theorem sailOutput_sigmaPost_jal (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).sailOutput = σ.sailOutput := rfl

theorem sailOutput_sigmaPost_store (σ : MState) (pc vminstret : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8)) :
    (sigmaPost_store σ pc vminstret m').sailOutput = σ.sailOutput := rfl

/-! ## `mem` is unchanged by every step used here (regs-only updates)

`sigmaPost_*` and `sigmaTick_*` are pure `regs` updates over `afterNextPC
(afterPrelude σ) pc`, whose `.mem = σ.mem` by `rfl`. So `.mem` of every reached
state is `σ.mem` definitionally — the wrappers below discharge the mem-unchanged
conjunct by `rfl`. -/

/-! ## Generic ALU observational step (absorbs tick parity)

Given the same abstract data as `step_alu_notick`/`step_alu_tick` (an abstract
`hexec` producing `sigma3_alu`, the `rd_reg` framing side conditions, the fetch
bytes), and `i < 2`, produce a single successor: `Step`, `i' < 2`, `GoodState`,
`mem = σ.mem`, and `ReadsLikePost σ' (sigmaPost_alu …)`. The tick/notick case
split is internal; the observation is identical either way. -/
theorem stepObs_alu
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (rd_reg : Register) (v : RegisterType rd_reg)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc rd_reg v))
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ' (sigmaPost_alu σ pc vminstret rd_reg v) := by
  by_cases htick : i + 1 = 2
  · -- tick boundary: obtain the tick-noise witnesses from GoodState of sigmaPost
    have hGp := goodstate_sigmaPost_alu σ pc vminstret rd_reg hrd v hG
    obtain ⟨vmip, hmip⟩ := hGp.mip
    obtain ⟨vmtime, hmtime⟩ := hGp.mtime
    obtain ⟨vmtimecmp, hmtimecmp⟩ := hGp.mtimecmp
    obtain ⟨vmcycle, hmcycle⟩ := hGp.mcycle
    obtain ⟨hstep, hGt⟩ := step_alu_tick σ i u pc vminstret w ast rd_reg v b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hword hnotrvc hdec hexec hrd_npc hrd_mi hrd_ms hrd_hart hrd
      hb0 hb1 hb2 hb3 hlo hhi halign htick
    refine ⟨_, 0, hstep, by decide, hGt, rfl, ?_, rfl⟩
    intro R hmc hmt hmi
    exact get?_sigmaTick_alu σ pc vminstret rd_reg v vmip vmtime vmtimecmp vmcycle R hmc hmt hmi
  · obtain ⟨hstep, hGt⟩ := step_alu_notick σ i u pc vminstret w ast rd_reg v b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hrd_npc hrd_mi hrd_ms hrd_hart hrd
      hb0 hb1 hb2 hb3 hlo hhi halign htick
    exact ⟨_, i + 1, hstep, by omega, hGt, rfl, ReadsLikePost.rfl _⟩

/-! ## Generic branch observational steps (taken / not-taken, absorb tick parity) -/

/-- Taken-branch observational step: `ReadsLikePost σ' (sigmaPost_branch_taken …)`. -/
theorem stepObs_branch_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret imm) := by
  by_cases htick : i + 1 = 2
  · have hGp := goodstate_sigmaPost_branch_taken σ pc vminstret imm hG
    obtain ⟨vmip, hmip⟩ := hGp.mip
    obtain ⟨vmtime, hmtime⟩ := hGp.mtime
    obtain ⟨vmtimecmp, hmtimecmp⟩ := hGp.mtimecmp
    obtain ⟨vmcycle, hmcycle⟩ := hGp.mcycle
    obtain ⟨hstep, hGt⟩ := step_branch_taken_tick σ i u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign htick
    refine ⟨_, 0, hstep, by decide, hGt, rfl, ?_, rfl⟩
    intro R hmc hmt hmi
    exact get?_sigmaTick_branch_taken σ pc vminstret imm vmip vmtime vmtimecmp vmcycle R hmc hmt hmi
  · obtain ⟨hstep, hGt⟩ := step_branch_taken_notick σ i u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign htick
    exact ⟨_, i + 1, hstep, by omega, hGt, rfl, ReadsLikePost.rfl _⟩

/-- Not-taken-branch observational step: `ReadsLikePost σ' (sigmaPost_branch_nottaken …)`. -/
theorem stepObs_branch_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  by_cases htick : i + 1 = 2
  · have hGp := goodstate_sigmaPost_branch_nottaken σ pc vminstret hG
    obtain ⟨vmip, hmip⟩ := hGp.mip
    obtain ⟨vmtime, hmtime⟩ := hGp.mtime
    obtain ⟨vmtimecmp, hmtimecmp⟩ := hGp.mtimecmp
    obtain ⟨vmcycle, hmcycle⟩ := hGp.mcycle
    obtain ⟨hstep, hGt⟩ := step_branch_nottaken_tick σ i u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign htick
    refine ⟨_, 0, hstep, by decide, hGt, rfl, ?_, rfl⟩
    intro R hmc hmt hmi
    exact get?_sigmaTick_branch_nottaken σ pc vminstret vmip vmtime vmtimecmp vmcycle R hmc hmt hmi
  · obtain ⟨hstep, hGt⟩ := step_branch_nottaken_notick σ i u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign htick
    exact ⟨_, i + 1, hstep, by omega, hGt, rfl, ReadsLikePost.rfl _⟩

/-! ## Generic `ret` (`jr x0`) observational step (absorbs tick parity) -/

/-- `ret`/`jr x0` observational step: `ReadsLikePost σ' (sigmaPost_jump_x0 … tgt)`
with `tgt = bit-0-cleared (rs1 + sext imm)`. -/
theorem stepObs_jr
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 : regidx) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)) := by
  by_cases htick : i + 1 = 2
  · have hGp := goodstate_sigmaPost_jump_x0 σ pc vminstret
      (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) hG
    obtain ⟨vmip, hmip⟩ := hGp.mip
    obtain ⟨vmtime, hmtime⟩ := hGp.mtime
    obtain ⟨vmtimecmp, hmtimecmp⟩ := hGp.mtimecmp
    obtain ⟨vmcycle, hmcycle⟩ := hGp.mcycle
    obtain ⟨hstep, hGt⟩ := step_jr_tick σ i u pc vminstret vrs1 w imm rs1 b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt htick
    refine ⟨_, 0, hstep, by decide, hGt, rfl, ?_, rfl⟩
    intro R hmc hmt hmi
    exact get?_sigmaTick_jump_x0 σ pc vminstret _ vmip vmtime vmtimecmp vmcycle R hmc hmt hmi
  · obtain ⟨hstep, hGt⟩ := step_jr_notick σ i u pc vminstret vrs1 w imm rs1 b0 b1 b2 b3
      hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt htick
    exact ⟨_, i + 1, hstep, by omega, hGt, rfl, ReadsLikePost.rfl _⟩

/-! ## Unconditional jump `j` (jal x0) observational step (absorbs tick parity) -/

/-- `j` (`jal x0`) observational step:
`ReadsLikePost σ' (sigmaPost_jump_x0 … (pc + sext imm))`. -/
theorem stepObs_j
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm)) := by
  by_cases htick : i + 1 = 2
  · have hGp := goodstate_sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm) hG
    obtain ⟨vmip, hmip⟩ := hGp.mip
    obtain ⟨vmtime, hmtime⟩ := hGp.mtime
    obtain ⟨vmtimecmp, hmtimecmp⟩ := hGp.mtimecmp
    obtain ⟨vmcycle, hmcycle⟩ := hGp.mcycle
    obtain ⟨hstep, hGt⟩ := step_j_tick σ i u pc vminstret w imm b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt htick
    refine ⟨_, 0, hstep, by decide, hGt, rfl, ?_, rfl⟩
    intro R hmc hmt hmi
    exact get?_sigmaTick_jump_x0 σ pc vminstret _ vmip vmtime vmtimecmp vmcycle R hmc hmt hmi
  · obtain ⟨hstep, hGt⟩ := step_j_notick σ i u pc vminstret w imm b0 b1 b2 b3
      hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt htick
    exact ⟨_, i + 1, hstep, by omega, hGt, rfl, ReadsLikePost.rfl _⟩

/-! ## `jal` (call, writes the link register) observational step -/

/-- JAL: GPR/PC read-back through the tick chain drops to `sigmaPost_jal`. -/
theorem get?_sigmaTick_jal (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) (R : Register)
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false) :
    (sigmaTick_jal σ pc vminstret imm rd_reg link vmip vmtime vmtimecmp vmcycle).regs.get? R
      = (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? R := by
  show (((((sigmaPost_jal σ pc vminstret imm rd_reg link).regs.insert Register.mcycle _).insert
      Register.mtime _).insert Register.mip _)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmi, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmt, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmc, dif_neg, reduceCtorEq, not_false_eq_true]

/-- `jal` (call) observational step: writes `link = pc+4` to `rd_reg`, jumps to
`pc + sext imm`. `ReadsLikePost σ' (sigmaPost_jal …)`. -/
theorem stepObs_jal
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, rd)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (pc + sign_extend (m := 64) imm)}
        = .ok () (sigma3_jal σ pc imm rd_reg link))
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ pc vminstret imm rd_reg link) := by
  by_cases htick : i + 1 = 2
  · have hGp := goodstate_sigmaPost_jal σ pc vminstret imm rd_reg hrd link hG
    obtain ⟨vmip, hmip⟩ := hGp.mip
    obtain ⟨vmtime, hmtime⟩ := hGp.mtime
    obtain ⟨vmtimecmp, hmtimecmp⟩ := hGp.mtimecmp
    obtain ⟨vmcycle, hmcycle⟩ := hGp.mcycle
    obtain ⟨hstep, hGt⟩ := step_jal_tick σ i u pc vminstret w imm rd rd_reg link b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt
      hrd_npc hrd_mi hrd_ms hrd_hart hrd hwr htick
    refine ⟨_, 0, hstep, by decide, hGt, rfl, ?_, rfl⟩
    intro R hmc hmt hmi
    exact get?_sigmaTick_jal σ pc vminstret imm rd_reg link vmip vmtime vmtimecmp vmcycle R hmc hmt hmi
  · obtain ⟨hstep, hGt⟩ := step_jal_notick σ i u pc vminstret w imm rd rd_reg link b0 b1 b2 b3
      hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt
      hrd_npc hrd_mi hrd_ms hrd_hart hrd hwr htick
    exact ⟨_, i + 1, hstep, by omega, hGt, rfl, ReadsLikePost.rfl _⟩

/-! ## Generic STORE observational step (absorbs tick parity)

Same shape as `stepObs_alu`, over `step_store_notick`/`step_store_tick`
(`Vsa/Sim/StepStore.lean`): the execute step is supplied abstractly with the
memory-only post-state `sigma3_store σ pc m'`, and the wrapper's memory
conjunct is `σ'.mem = m'` (the described update) instead of mem-unchanged. -/

/-- STORE: GPR/PC read-back through the tick chain drops to `sigmaPost_store`. -/
theorem get?_sigmaTick_store (σ : MState) (pc vminstret : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8))
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) (R : Register)
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false) :
    (sigmaTick_store σ pc vminstret m' vmip vmtime vmtimecmp vmcycle).regs.get? R
      = (sigmaPost_store σ pc vminstret m').regs.get? R := by
  show (((((sigmaPost_store σ pc vminstret m').regs.insert Register.mcycle _).insert
      Register.mtime _).insert Register.mip _)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmi, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmt, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmc, dif_neg, reduceCtorEq, not_false_eq_true]

/-- Generic STORE observational step: `Step`, `i' < 2`, `GoodState`,
`σ'.mem = m'` (the byte-insert chain supplied through `hexec`), and
`ReadsLikePost σ' (sigmaPost_store …)`. Tick parity absorbed. -/
theorem stepObs_store
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (m' : Std.ExtHashMap Nat (BitVec 8))
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_store σ pc m'))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = m' ∧ ReadsLikePost σ' (sigmaPost_store σ pc vminstret m') := by
  by_cases htick : i + 1 = 2
  · have hGp := goodstate_sigmaPost_store σ pc vminstret m' hG
    obtain ⟨vmip, hmip⟩ := hGp.mip
    obtain ⟨vmtime, hmtime⟩ := hGp.mtime
    obtain ⟨vmtimecmp, hmtimecmp⟩ := hGp.mtimecmp
    obtain ⟨vmcycle, hmcycle⟩ := hGp.mcycle
    obtain ⟨hstep, hGt⟩ := step_store_tick σ i u pc vminstret w ast m' b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign htick
    refine ⟨_, 0, hstep, by decide, hGt, rfl, ?_, rfl⟩
    intro R hmc hmt hmi
    exact get?_sigmaTick_store σ pc vminstret m' vmip vmtime vmtimecmp vmcycle R hmc hmt hmi
  · obtain ⟨hstep, hGt⟩ := step_store_notick σ i u pc vminstret w ast m' b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign htick
    exact ⟨_, i + 1, hstep, by omega, hGt, rfl, ReadsLikePost.rfl _⟩

end Vsa.Sim
