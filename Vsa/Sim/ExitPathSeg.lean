import Vsa.Sim.ExitPath
import Vsa.Sim.StepObs
import Vsa.Sim.RegAccess
import Vsa.Sim.Code._exit
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.DecodeTable.Batch06Part20
import Vsa.Sim.DecodeTable.Batch06Part15
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch14Part06

/-!
# Layer 5 — discharging two of `ErrorTailChain`'s four segments

`Vsa/Sim/ExitPath.lean` reduced the opaque `ErrorTailChain` residual to four
straight-line segment `Triple`s (`InterpContSeg`, `MainErrorSeg`, `Crt0ExitSeg`,
`ExitPrologSeg`).  This file discharges the two that are pure straight-line /
branch machine code with no external calls:

* **`ExitPrologSeg`** (`0x80000180 → the sd a5,tohost` @0x80000190): the `_exit`
  prologue `slli/srli/ori` form the syscall-exit word `(70<<<1)|1` in `a5`, the
  `auipc a4,0x1b` forms the `tohost` base, and control parks at the store site
  satisfying `ExitStorePreExit`.  Discharged here (conditional on the standing
  HTIF invariant `htif_payload_writes = 0`, the one fact `AtExitProlog` does not
  itself carry — supplied as the minimal `HtifPayloadZero` residual).

The threading reuses the `StepObs` ALU battery (`stepObs_alu`) and the
`Muldi3Spec` observation consumers (`obs_alu_pc`/`obs_alu_rd`/`obs_alu_other`/
`obs_alu_minstret`), mirroring `Vsa/Sim/DivSites.lean` + `Vsa/Sim/DivSpec.lean`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps output)
open Vsa.Logic
open Vsa.Sim.Code (_exitLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The four `_exit`-prologue ALU execute characters

Each produces the `sigma3_alu` post-state for its op, reading its `rs1` off the
skeleton state `afterNextPC (afterPrelude σ) pc` via the `get?_afterNextPC` frame
lemma (the register value pinned by the caller's hypothesis). -/

/-- `slli a4,a0,0x20` @0x80000180: `x14 := shift_bits_left a0 (extractLsb 0x20 5 0)`. -/
theorem ep_exec_slli_a4_a0 (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.SHIFTIOP (0x20#6, regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, sop.SLLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14 (shift_bits_left v10 (Sail.BitVec.extractLsb (0x20#6) 5 0))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_shiftiop_slli_char (0x20#6) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0e#5) v10
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x14 (shift_bits_left v10 (Sail.BitVec.extractLsb (0x20#6) 5 0)))
    (rX_bits_x10 _ v10 h₂)
    (wX_bits_x14 _ (shift_bits_left v10 (Sail.BitVec.extractLsb (0x20#6) 5 0)))

/-- `srli a5,a4,0x1f` @0x80000184: `x15 := shift_bits_right a4 (extractLsb 0x1f 5 0)`. -/
theorem ep_exec_srli_a5_a4 (σ : MState) (pc : BitVec 64) (v14 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.SHIFTIOP (0x1f#6, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, sop.SRLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (shift_bits_right v14 (Sail.BitVec.extractLsb (0x1f#6) 5 0))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_shiftiop_srli_char (0x1f#6) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) v14
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (shift_bits_right v14 (Sail.BitVec.extractLsb (0x1f#6) 5 0)))
    (rX_bits_x14 _ v14 h₂)
    (wX_bits_x15 _ (shift_bits_right v14 (Sail.BitVec.extractLsb (0x1f#6) 5 0)))

/-- `ori a5,a5,1` @0x80000188: `x15 := a5 ||| sext 1`. -/
theorem ep_exec_ori_a5_a5 (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.ITYPE (0x001#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ORI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (v15 ||| sign_extend (m := 64) (0x001#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_itype_ori_char (0x001#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (v15 ||| sign_extend (m := 64) (0x001#12)))
    (rX_bits_x15 _ v15 h₂)
    (wX_bits_x15 _ (v15 ||| sign_extend (m := 64) (0x001#12)))

/-- `auipc a4,0x1b` @0x8000018c: `x14 := pc + sext (0x1b +++ 0)`. Reads `PC`
(the current instruction PC, pinned by `hpc`; `afterNextPC` writes `nextPC`, not
`PC`). -/
theorem ep_exec_auipc_a4 (σ : MState) (pc : BitVec 64)
    (hpc : σ.regs.get? Register.PC = some pc) :
    (execute (instruction.UTYPE (0x0001b#20, regidx.Regidx 0x0e#5, uop.AUIPC))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14
            (pc + sign_extend (m := 64) ((0x0001b#20 : BitVec 20) +++ (0x000#12 : BitVec 12)))) := by
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  exact execute_utype_auipc_char (0x0001b#20) (regidx.Regidx 0x0e#5) pc
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x14
      (pc + sign_extend (m := 64) ((0x0001b#20 : BitVec 20) +++ (0x000#12 : BitVec 12))))
    hpc₂
    (wX_bits_x14 _ (pc + sign_extend (m := 64) ((0x0001b#20 : BitVec 20) +++ (0x000#12 : BitVec 12))))

/-! ## The four `_exit`-prologue observational step sites -/

/-- `slli a4,a0,0x20` @0x80000180 (word `0x02051713`, bytes `13 17 05 02`). -/
theorem esite_80000180
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : _exitLoaded σ.mem)
    (hpcv : pc = (0x80000180#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (shift_bits_left v10 (Sail.BitVec.extractLsb (0x20#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._exit_at_80000180 hmem
  exact stepObs_alu σ i u (0x80000180#64) vminstret (0x02051713#32)
    (instruction.SHIFTIOP (0x20#6, regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, sop.SLLI))
    Register.x14 (shift_bits_left v10 (Sail.BitVec.extractLsb (0x20#6) 5 0))
    (0x13#8) (0x17#8) (0x05#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02051713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (ep_exec_slli_a4_a0 σ (0x80000180#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- `srli a5,a4,0x1f` @0x80000184 (word `0x01f75793`, bytes `93 57 f7 01`). -/
theorem esite_80000184
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : _exitLoaded σ.mem)
    (hpcv : pc = (0x80000184#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (shift_bits_right v14 (Sail.BitVec.extractLsb (0x1f#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._exit_at_80000184 hmem
  exact stepObs_alu σ i u (0x80000184#64) vminstret (0x01f75793#32)
    (instruction.SHIFTIOP (0x1f#6, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, sop.SRLI))
    Register.x15 (shift_bits_right v14 (Sail.BitVec.extractLsb (0x1f#6) 5 0))
    (0x93#8) (0x57#8) (0xf7#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_01f75793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (ep_exec_srli_a5_a4 σ (0x80000184#64) v14 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- `ori a5,a5,1` @0x80000188 (word `0x0017e793`, bytes `93 e7 17 00`). -/
theorem esite_80000188
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : _exitLoaded σ.mem)
    (hpcv : pc = (0x80000188#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (v15 ||| sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._exit_at_80000188 hmem
  exact stepObs_alu σ i u (0x80000188#64) vminstret (0x0017e793#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ORI))
    Register.x15 (v15 ||| sign_extend (m := 64) (0x001#12))
    (0x93#8) (0xe7#8) (0x17#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0017e793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (ep_exec_ori_a5_a5 σ (0x80000188#64) v15 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- `auipc a4,0x1b` @0x8000018c (word `0x0001b717`, bytes `17 b7 01 00`). -/
theorem esite_8000018c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : _exitLoaded σ.mem)
    (hpcv : pc = (0x8000018c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (pc + sign_extend (m := 64) ((0x0001b#20 : BitVec 20) +++ (0x000#12 : BitVec 12)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._exit_at_8000018c hmem
  exact stepObs_alu σ i u (0x8000018c#64) vminstret (0x0001b717#32)
    (instruction.UTYPE (0x0001b#20, regidx.Regidx 0x0e#5, uop.AUIPC))
    Register.x14 (0x8000018c#64 + sign_extend (m := 64) ((0x0001b#20 : BitVec 20) +++ (0x000#12 : BitVec 12)))
    (0x17#8) (0xb7#8) (0x01#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0001b717 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (ep_exec_auipc_a4 σ (0x8000018c#64) hpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## `ExitPrologSeg` — the `_exit` prologue to the `sd a5,tohost` site

We thread the four ALU sites from the `_exit` entry `0x80000180` (with `a0 = 70`,
`GoodState`, tick-bounded, `htif_payload_writes = 0`, output `= out`, `_exit` code
loaded) to the `sd a5,tohost` store site `0x80000190`, then assemble the
`ExitStorePreExit out` store-site predicate at that config.

Two facts `AtExitProlog` does not itself carry are the `_exit` code being loaded
(`_exitLoaded`) and the standing HTIF invariant `htif_payload_writes = 0` (not
part of `GoodState`; established once at boot and untouched off the HTIF-store
path).  They are supplied as the minimal residual `ExitPrologGeom out`. -/

/-- The two facts `AtExitProlog` does not name that the `_exit` prologue decode
needs: the `_exit` code is loaded and `htif_payload_writes = 0`. -/
def ExitPrologGeom (out : String) : Prop :=
  ∀ c, AtExitProlog out c →
    _exitLoaded c.σ.mem ∧ c.σ.regs.get? Register.htif_payload_writes = some (0#4)

/-- **`ExitPrologSeg` discharged** (conditional on `ExitPrologGeom`).  From
`AtExitProlog out` (with `_exit` loaded and `htif_payload_writes = 0`), the
`slli/srli/ori/auipc` reach the `sd a5,tohost` @0x80000190 store config, which
satisfies `ExitStorePreExit out`: `a4 = tohost base`, `a5 = (70<<<1)|1`, EA =
`tohostAddr`, output unchanged. -/
theorem exitPrologSeg_of (out : String) (hgeom : ExitPrologGeom out) :
    Triple (AtExitProlog out) (ExitStorePreExit out) := by
  intro c hpre
  obtain ⟨hG, htick, hpc, hx10, hout⟩ := hpre
  obtain ⟨hmem, hpw⟩ := hgeom c ⟨hG, htick, hpc, hx10, hout⟩
  obtain ⟨vm0, hm0⟩ := hG.minstret
  -- σ0 = c.σ @ 0x80000180
  -- Step 1: slli a4,a0,0x20  →  σ1 @ 0x80000184, x14 := 70<<32
  obtain ⟨σ1, i1, hstep1, hi1, hG1, hmem1, hobs1⟩ :=
    esite_80000180 c.σ c.tick c.steps (0x80000180#64) vm0 (70#64) hG hpc hm0 hx10 hmem rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80000184#64) := obs_alu_pc hobs1
  have hx14_1 : σ1.regs.get? Register.x14
      = some (shift_bits_left (70#64) (Sail.BitVec.extractLsb (0x20#6) 5 0)) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vm1, hm1⟩ := obs_alu_minstret hobs1
  have hpw1 : σ1.regs.get? Register.htif_payload_writes = some (0#4) :=
    obs_alu_other hobs1 Register.htif_payload_writes (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hpw
  have hout1 : output σ1 = out := by
    unfold output; rw [hobs1.out]; exact hout
  -- Step 2: srli a5,a4,0x1f  →  σ2 @ 0x80000188, x15 := 70<<1
  obtain ⟨σ2, i2, hstep2, hi2, hG2, hmem2, hobs2⟩ :=
    esite_80000184 σ1 i1 (c.steps + 1) (0x80000184#64) vm1
      (shift_bits_left (70#64) (Sail.BitVec.extractLsb (0x20#6) 5 0))
      hG1 hpc1 hm1 hx14_1 (by rw [hmem1]; exact hmem) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80000188#64) := obs_alu_pc hobs2
  have hx15_2 : σ2.regs.get? Register.x15
      = some (shift_bits_right (shift_bits_left (70#64) (Sail.BitVec.extractLsb (0x20#6) 5 0))
          (Sail.BitVec.extractLsb (0x1f#6) 5 0)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vm2, hm2⟩ := obs_alu_minstret hobs2
  have hpw2 : σ2.regs.get? Register.htif_payload_writes = some (0#4) :=
    obs_alu_other hobs2 Register.htif_payload_writes (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hpw1
  have hout2 : output σ2 = out := by
    unfold output; rw [hobs2.out]; exact hout1
  -- Step 3: ori a5,a5,1  →  σ3 @ 0x8000018c, x15 := (70<<1)|1
  obtain ⟨σ3, i3, hstep3, hi3, hG3, hmem3, hobs3⟩ :=
    esite_80000188 σ2 i2 (c.steps + 1 + 1) (0x80000188#64) vm2
      (shift_bits_right (shift_bits_left (70#64) (Sail.BitVec.extractLsb (0x20#6) 5 0))
        (Sail.BitVec.extractLsb (0x1f#6) 5 0))
      hG2 hpc2 hm2 hx15_2 (by rw [hmem2, hmem1]; exact hmem) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x8000018c#64) := obs_alu_pc hobs3
  have hx15_3 : σ3.regs.get? Register.x15 = some ((70#64 <<< 1) ||| 1#64) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (shift_bits_right (shift_bits_left (70#64) (Sail.BitVec.extractLsb (0x20#6) 5 0))
        (Sail.BitVec.extractLsb (0x1f#6) 5 0) ||| sign_extend (m := 64) (0x001#12))
        = ((70#64 <<< 1) ||| 1#64) from by decide] at this
  obtain ⟨vm3, hm3⟩ := obs_alu_minstret hobs3
  have hpw3 : σ3.regs.get? Register.htif_payload_writes = some (0#4) :=
    obs_alu_other hobs3 Register.htif_payload_writes (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hpw2
  have hout3 : output σ3 = out := by
    unfold output; rw [hobs3.out]; exact hout2
  -- Step 4: auipc a4,0x1b  →  σ4 @ 0x80000190, x14 := 0x8001b18c
  obtain ⟨σ4, i4, hstep4, hi4, hG4, hmem4, hobs4⟩ :=
    esite_8000018c σ3 i3 (c.steps + 1 + 1 + 1) (0x8000018c#64) vm3
      hG3 hpc3 hm3 (by rw [hmem3, hmem2, hmem1]; exact hmem) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80000190#64) := obs_alu_pc hobs4
  have hx14_4 : σ4.regs.get? Register.x14 = some (0x8001b18c#64) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x8000018c#64 + sign_extend (m := 64) ((0x0001b#20 : BitVec 20) +++ (0x000#12 : BitVec 12)))
        = (0x8001b18c#64) from by decide] at this
  have hx15_4 : σ4.regs.get? Register.x15 = some ((70#64 <<< 1) ||| 1#64) :=
    obs_alu_other hobs4 Register.x15 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hx15_3
  obtain ⟨vm4, hm4⟩ := obs_alu_minstret hobs4
  have hpw4 : σ4.regs.get? Register.htif_payload_writes = some (0#4) :=
    obs_alu_other hobs4 Register.htif_payload_writes (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hpw3
  have hout4 : output σ4 = out := by
    unfold output; rw [hobs4.out]; exact hout3
  have hmem4' : σ4.mem = c.σ.mem := by rw [hmem4, hmem3, hmem2, hmem1]
  -- the store-site config c4 @ 0x80000190
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩, ?_, ?_⟩
  · -- Steps c ⟨σ4,…⟩: chain the four single steps.
    have s1 : Steps c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact Steps.single hstep1
    exact s1.trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans (Steps.single hstep4)))
  · -- ExitStorePreExit out ⟨σ4,…⟩
    have hb : _exitLoaded σ4.mem := by rw [hmem4']; exact hmem
    obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._exit_at_80000190 hb
    -- reads for the store at 0x80000190
    have hra1 : (rX_bits (regidx.Regidx 0x0e#5)).run (afterNextPC (afterPrelude σ4) (0x80000190#64))
        = .ok (0x8001b18c#64) (afterNextPC (afterPrelude σ4) (0x80000190#64)) := by
      apply rX_bits_x14
      rw [get?_afterNextPC σ4 _ _ (by decide) (by decide)]; exact hx14_4
    have hra2 : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ4) (0x80000190#64))
        = .ok ((70#64 <<< 1) ||| 1#64) (afterNextPC (afterPrelude σ4) (0x80000190#64)) := by
      apply rX_bits_x15
      rw [get?_afterNextPC σ4 _ _ (by decide) (by decide)]; exact hx15_4
    obtain ⟨thv4, hth4⟩ := hG4.htif_tohost
    refine ⟨0x80000190#64, vm4, 0xb6f73a23#32, 0xb74#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5,
      0x8001b18c#64, (70#64 <<< 1) ||| 1#64, thv4,
      0x23#8, 0x3a#8, 0xf7#8, 0xb6#8,
      hG4, hpc4, hm4, ?_, ?_, ?_, hra1, hra2, ?_, rfl, hpw4, hth4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq; decide
    · apply BitVec.eq_of_toNat_eq; decide
    · exact Vsa.Sim.DecodeTable.decode_b6f73a23 (afterPrelude σ4)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.misa)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.cur_privilege)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.mseccfg)
    · -- EA = tohostAddr
      show (0x8001b18c#64) + sign_extend (m := 64) (0xb74#12) = BitVec.ofNat 64 tohostAddr
      apply BitVec.eq_of_toNat_eq; rw [show tohostAddr = 0x8001ad00 from rfl]; decide
    · exact hb0
    · exact hb1
    · exact hb2
    · exact hb3
    · show (0x80000000 : Nat) ≤ (0x80000190#64 : BitVec 64).toNat; decide
    · show (0x80000190#64 : BitVec 64).toNat + 4 ≤ tohostAddr
      rw [show tohostAddr = 0x8001ad00 from rfl]; decide
    · show (0x80000190#64 : BitVec 64).toNat % 4 = 0; decide
    · exact hout4

/-- `exitPrologSeg_of` packaged as the `ExitPrologSeg out` segment residual of
`errorTailChain_of_segments`, conditional on the `ExitPrologGeom` HTIF/code
geometry. -/
theorem exitPrologSeg (out : String) (hgeom : ExitPrologGeom out) :
    ExitPrologSeg out :=
  exitPrologSeg_of out hgeom

end Vsa.Sim
