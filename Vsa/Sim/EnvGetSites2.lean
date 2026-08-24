import Vsa.Sim.EnvGetSites

/-!
# Layer 3 — remaining per-site observational step lemmas for `env_get`

Continuation of `Vsa/Sim/EnvGetSites.lean` (which holds the shared byte-word /
non-RVC facts `*_eg`, the control-flow map, and the validated site templates for
`0x80002c10` and `0x80002c14`).  This file adds the remaining ~35 `env_get`
sites, all `_eg2`-suffixed, following the same `stepObs_*` idioms.

Instruction inventory (decoded from `Code/Env_get.lean`):

* ALU-class (`stepObs_alu`): `mv`/`li`/`addi`/`slli`/`add`, and the SIGNED loads
  `lw`/`ld` (they write a GPR with `sign_extend`, observed as `sigmaPost_alu`).
* STORE-class (`stepObs_store`): the seven prologue `sd` spills and the three HIT
  `sd`s into `*out`.
* BRANCH-class: `blez`(=`bge x0,·`)/`beq`/`bne`, taken and not-taken.
* JUMP-class: `j`(`jal x0`), `jal strcmp`, `ret`(`jr x0`).

Reuses `ValueSites` builders (`exec_ld`, `exec_lw`, `exec_sd_val`) and the
`ExecuteAlu`/`ExecuteBranch`/`ExecuteJump` `_char` characterizations, plus the
`*_eg` byte-word facts and `decode_*` table entries.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## ALU-class straight-line sites (`mv`/`li`/`addi`/`slli`/`add`) -/

/-! ### 0x80002c34 (`mv s4,a0`): `x20 := x10 + sext 0`. -/
theorem site_80002c34_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c34#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x20 (v10 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c34 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002c34#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80002c34#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80002c34#64) vminstret (0x00050a13#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x14#5, iop.ADDI))
    Register.x20 (v10 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x0a#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_00050a13_eg nr_00050a13_eg
    (Vsa.Sim.DecodeTable.decode_00050a13 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x14#5) v10
      (afterNextPC (afterPrelude σ) (0x80002c34#64))
      (sigma3_alu σ (0x80002c34#64) Register.x20 (v10 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x10 _ v10 hx10₂) (wX_bits_x20 _ (v10 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c38 (`mv s3,a1`): `x19 := x11 + sext 0`. -/
theorem site_80002c38_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c38#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x19 (v11 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c38 hmem
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x80002c38#64)).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ (0x80002c38#64) _ (by decide) (by decide)]; exact hx11
  exact stepObs_alu σ i u (0x80002c38#64) vminstret (0x00058993#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x13#5, iop.ADDI))
    Register.x19 (v11 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x89#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_00058993_eg nr_00058993_eg
    (Vsa.Sim.DecodeTable.decode_00058993 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x13#5) v11
      (afterNextPC (afterPrelude σ) (0x80002c38#64))
      (sigma3_alu σ (0x80002c38#64) Register.x19 (v11 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x11 _ v11 hx11₂) (wX_bits_x19 _ (v11 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c3c (`mv s5,a2`): `x21 := x12 + sext 0`. -/
theorem site_80002c3c_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c3c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x21 (v12 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c3c hmem
  have hx12₂ : (afterNextPC (afterPrelude σ) (0x80002c3c#64)).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ (0x80002c3c#64) _ (by decide) (by decide)]; exact hx12
  exact stepObs_alu σ i u (0x80002c3c#64) vminstret (0x00060a93#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x15#5, iop.ADDI))
    Register.x21 (v12 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x0a#8) (0x06#8) (0x00#8)
    hG hpc hminstret w_00060a93_eg nr_00060a93_eg
    (Vsa.Sim.DecodeTable.decode_00060a93 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x15#5) v12
      (afterNextPC (afterPrelude σ) (0x80002c3c#64))
      (sigma3_alu σ (0x80002c3c#64) Register.x21 (v12 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x12 _ v12 hx12₂) (wX_bits_x21 _ (v12 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c4c (`li s0,0`): `x8 := 0 + sext 0`. -/
theorem site_80002c4c_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c4c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x8 ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c4c hmem
  exact stepObs_alu σ i u (0x80002c4c#64) vminstret (0x00000413#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x08#5, iop.ADDI))
    Register.x8 ((0#64) + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x04#8) (0x00#8) (0x00#8)
    hG hpc hminstret w_00000413_eg nr_00000413_eg
    (Vsa.Sim.DecodeTable.decode_00000413 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x08#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x80002c4c#64))
      (sigma3_alu σ (0x80002c4c#64) Register.x8 ((0#64) + sign_extend (m := 64) (0x000#12)))
      (rX_bits_zero _) (wX_bits_x8 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c54 (`addi s0,s0,1`): `x8 := s0 + sext 1` (scan back-edge `i++`). -/
theorem site_80002c54_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c54#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x8 (v8 + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c54 hmem
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80002c54#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80002c54#64) _ (by decide) (by decide)]; exact hx8
  exact stepObs_alu σ i u (0x80002c54#64) vminstret (0x00140413#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x08#5, regidx.Regidx 0x08#5, iop.ADDI))
    Register.x8 (v8 + sign_extend (m := 64) (0x001#12)) (0x13#8) (0x04#8) (0x14#8) (0x00#8)
    hG hpc hminstret w_00140413_eg nr_00140413_eg
    (Vsa.Sim.DecodeTable.decode_00140413 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x08#5) v8
      (afterNextPC (afterPrelude σ) (0x80002c54#64))
      (sigma3_alu σ (0x80002c54#64) Register.x8 (v8 + sign_extend (m := 64) (0x001#12)))
      (rX_bits_x8 _ v8 hx8₂) (wX_bits_x8 _ (v8 + sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c58 (`addi s1,s1,8`): `x9 := s1 + sext 8` (names++). -/
theorem site_80002c58_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c58#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x9 (v9 + sign_extend (m := 64) (0x008#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c58 hmem
  have hx9₂ : (afterNextPC (afterPrelude σ) (0x80002c58#64)).regs.get? Register.x9 = some v9 := by
    rw [get?_afterNextPC σ (0x80002c58#64) _ (by decide) (by decide)]; exact hx9
  exact stepObs_alu σ i u (0x80002c58#64) vminstret (0x00848493#32)
    (instruction.ITYPE (0x008#12, regidx.Regidx 0x09#5, regidx.Regidx 0x09#5, iop.ADDI))
    Register.x9 (v9 + sign_extend (m := 64) (0x008#12)) (0x93#8) (0x84#8) (0x84#8) (0x00#8)
    hG hpc hminstret w_00848493_eg nr_00848493_eg
    (Vsa.Sim.DecodeTable.decode_00848493 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x008#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x09#5) v9
      (afterNextPC (afterPrelude σ) (0x80002c58#64))
      (sigma3_alu σ (0x80002c58#64) Register.x9 (v9 + sign_extend (m := 64) (0x008#12)))
      (rX_bits_x9 _ v9 hx9₂) (wX_bits_x9 _ (v9 + sign_extend (m := 64) (0x008#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c64 (`mv a1,s3`): `x11 := x19 + sext 0`. -/
theorem site_80002c64_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v19 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx19 : σ.regs.get? Register.x19 = some v19)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c64#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11 (v19 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c64 hmem
  have hx19₂ : (afterNextPC (afterPrelude σ) (0x80002c64#64)).regs.get? Register.x19 = some v19 := by
    rw [get?_afterNextPC σ (0x80002c64#64) _ (by decide) (by decide)]; exact hx19
  exact stepObs_alu σ i u (0x80002c64#64) vminstret (0x00098593#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x13#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v19 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x85#8) (0x09#8) (0x00#8)
    hG hpc hminstret w_00098593_eg nr_00098593_eg
    (Vsa.Sim.DecodeTable.decode_00098593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x13#5) (regidx.Regidx 0x0b#5) v19
      (afterNextPC (afterPrelude σ) (0x80002c64#64))
      (sigma3_alu σ (0x80002c64#64) Register.x11 (v19 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x19 _ v19 hx19₂) (wX_bits_x11 _ (v19 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Load-class sites (`lw`/`ld` — ALU-class, write a GPR with `sign_extend`) -/

/-! ### 0x80002c40 (`lw s2,0(s4)`): `x18 := sext32 [s4+0]` (env->count, CHAIN HEAD). -/
theorem site_80002c40_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c40#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v20 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v20 + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (v20 + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v20 + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (v20 + sign_extend (m := 64) (0x000#12)).toNat % 4 = 0)
    (h0 : σ.mem[(v20 + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (h1 : σ.mem[(v20 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v20 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v20 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x18
          (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c40 hmem
  have hx20₂ : (afterNextPC (afterPrelude σ) (0x80002c40#64)).regs.get? Register.x20 = some v20 := by
    rw [get?_afterNextPC σ (0x80002c40#64) _ (by decide) (by decide)]; exact hx20
  exact stepObs_alu σ i u (0x80002c40#64) vminstret (0x000a2903#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x14#5, regidx.Regidx 0x12#5, false, 4))
    Register.x18 (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))
    (0x03#8) (0x29#8) (0x0a#8) (0x00#8)
    hG hpc hminstret w_000a2903_eg nr_000a2903_eg
    (Vsa.Sim.DecodeTable.decode_000a2903 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x80002c40#64) (0x000#12) (regidx.Regidx 0x14#5) (regidx.Regidx 0x12#5)
      (sigma3_alu σ (0x80002c40#64) Register.x18
        (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      v20 b0 b1 b2 b3 hG (rX_bits_x20 _ v20 hx20₂)
      (wX_bits_x18 _ (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c48 (`ld s1,8(s4)`): `x9 := sext64 [s4+8]` (env->names). -/
theorem site_80002c48_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c48#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v20 + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (v20 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v20 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v20 + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (v20 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (d0 : σ.mem[(v20 + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (d1 : σ.mem[(v20 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(v20 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(v20 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(v20 + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(v20 + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(v20 + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(v20 + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x9
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c48 hmem
  have hx20₂ : (afterNextPC (afterPrelude σ) (0x80002c48#64)).regs.get? Register.x20 = some v20 := by
    rw [get?_afterNextPC σ (0x80002c48#64) _ (by decide) (by decide)]; exact hx20
  exact stepObs_alu σ i u (0x80002c48#64) vminstret (0x008a3483#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x14#5, regidx.Regidx 0x09#5, false, 8))
    Register.x9 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x34#8) (0x8a#8) (0x00#8)
    hG hpc hminstret w_008a3483_eg nr_008a3483_eg
    (Vsa.Sim.DecodeTable.decode_008a3483 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002c48#64) (0x008#12) (regidx.Regidx 0x14#5) (regidx.Regidx 0x09#5)
      (sigma3_alu σ (0x80002c48#64) Register.x9
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      v20 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x20 _ v20 hx20₂)
      (wX_bits_x9 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c60 (`ld` off=0x000(rs1=Register.x9) → Register.x10). -/
theorem site_80002c60_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x9 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c60#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c60 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c60#64)).regs.get? Register.x9 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c60#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002c60#64) vminstret (0x0004b503#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x09#5, regidx.Regidx 0x0a#5, false, 8))
    Register.x10 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0xb5#8) (0x04#8) (0x00#8)
    hG hpc hminstret w_0004b503_eg nr_0004b503_eg
    (Vsa.Sim.DecodeTable.decode_0004b503 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002c60#64) (0x000#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x80002c60#64) Register.x10
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x9 _ vbase hbase₂)
      (wX_bits_x10 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c70 (`ld` off=0x010(rs1=Register.x20) → Register.x15). -/
theorem site_80002c70_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x20 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c70#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c70 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c70#64)).regs.get? Register.x20 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c70#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002c70#64) vminstret (0x010a3783#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x14#5, regidx.Regidx 0x0f#5, false, 8))
    Register.x15 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x37#8) (0x0a#8) (0x01#8)
    hG hpc hminstret w_010a3783_eg nr_010a3783_eg
    (Vsa.Sim.DecodeTable.decode_010a3783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002c70#64) (0x010#12) (regidx.Regidx 0x14#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x80002c70#64) Register.x15
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x20 _ vbase hbase₂)
      (wX_bits_x15 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c84 (`ld` off=0x000(rs1=Register.x15) → Register.x14). -/
theorem site_80002c84_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x15 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c84#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c84 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c84#64)).regs.get? Register.x15 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c84#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002c84#64) vminstret (0x0007b703#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, false, 8))
    Register.x14 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0xb7#8) (0x07#8) (0x00#8)
    hG hpc hminstret w_0007b703_eg nr_0007b703_eg
    (Vsa.Sim.DecodeTable.decode_0007b703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002c84#64) (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5)
      (sigma3_alu σ (0x80002c84#64) Register.x14
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x15 _ vbase hbase₂)
      (wX_bits_x14 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c90 (`ld` off=0x008(rs1=Register.x15) → Register.x14). -/
theorem site_80002c90_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x15 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c90#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c90 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c90#64)).regs.get? Register.x15 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c90#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002c90#64) vminstret (0x0087b703#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, false, 8))
    Register.x14 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0xb7#8) (0x87#8) (0x00#8)
    hG hpc hminstret w_0087b703_eg nr_0087b703_eg
    (Vsa.Sim.DecodeTable.decode_0087b703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002c90#64) (0x008#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5)
      (sigma3_alu σ (0x80002c90#64) Register.x14
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x15 _ vbase hbase₂)
      (wX_bits_x14 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c98 (`ld` off=0x010(rs1=Register.x15) → Register.x15). -/
theorem site_80002c98_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x15 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c98#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c98 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c98#64)).regs.get? Register.x15 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c98#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002c98#64) vminstret (0x0107b783#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, false, 8))
    Register.x15 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0xb7#8) (0x07#8) (0x01#8)
    hG hpc hminstret w_0107b783_eg nr_0107b783_eg
    (Vsa.Sim.DecodeTable.decode_0107b783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002c98#64) (0x010#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x80002c98#64) Register.x15
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x15 _ vbase hbase₂)
      (wX_bits_x15 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002ca0 (`ld` off=0x038(rs1=Register.x2) → Register.x1). -/
theorem site_80002ca0_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002ca0#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x038#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x038#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x038#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x038#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x038#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x038#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x038#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x038#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x038#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x038#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x1
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002ca0 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002ca0#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002ca0#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002ca0#64) vminstret (0x03813083#32)
    (instruction.LOAD (0x038#12, regidx.Regidx 0x02#5, regidx.Regidx 0x01#5, false, 8))
    Register.x1 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x30#8) (0x81#8) (0x03#8)
    hG hpc hminstret w_03813083_eg nr_03813083_eg
    (Vsa.Sim.DecodeTable.decode_03813083 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002ca0#64) (0x038#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x01#5)
      (sigma3_alu σ (0x80002ca0#64) Register.x1
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vbase hbase₂)
      (wX_bits_x1 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002ca4 (`ld` off=0x030(rs1=Register.x2) → Register.x8). -/
theorem site_80002ca4_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002ca4#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x030#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x030#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x030#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x030#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x030#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x030#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x030#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x030#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x030#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x030#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x8
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002ca4 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002ca4#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002ca4#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002ca4#64) vminstret (0x03013403#32)
    (instruction.LOAD (0x030#12, regidx.Regidx 0x02#5, regidx.Regidx 0x08#5, false, 8))
    Register.x8 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x34#8) (0x01#8) (0x03#8)
    hG hpc hminstret w_03013403_eg nr_03013403_eg
    (Vsa.Sim.DecodeTable.decode_03013403 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002ca4#64) (0x030#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x08#5)
      (sigma3_alu σ (0x80002ca4#64) Register.x8
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vbase hbase₂)
      (wX_bits_x8 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002ca8 (`ld` off=0x028(rs1=Register.x2) → Register.x9). -/
theorem site_80002ca8_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002ca8#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x028#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x028#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x028#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x028#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x028#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x028#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x028#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x028#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x028#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x028#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x9
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002ca8 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002ca8#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002ca8#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002ca8#64) vminstret (0x02813483#32)
    (instruction.LOAD (0x028#12, regidx.Regidx 0x02#5, regidx.Regidx 0x09#5, false, 8))
    Register.x9 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x34#8) (0x81#8) (0x02#8)
    hG hpc hminstret w_02813483_eg nr_02813483_eg
    (Vsa.Sim.DecodeTable.decode_02813483 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002ca8#64) (0x028#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x09#5)
      (sigma3_alu σ (0x80002ca8#64) Register.x9
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vbase hbase₂)
      (wX_bits_x9 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002cac (`ld` off=0x020(rs1=Register.x2) → Register.x18). -/
theorem site_80002cac_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002cac#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x020#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x020#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x020#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x020#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x020#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x020#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x020#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x020#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x020#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x020#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x18
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002cac hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002cac#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002cac#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002cac#64) vminstret (0x02013903#32)
    (instruction.LOAD (0x020#12, regidx.Regidx 0x02#5, regidx.Regidx 0x12#5, false, 8))
    Register.x18 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x39#8) (0x01#8) (0x02#8)
    hG hpc hminstret w_02013903_eg nr_02013903_eg
    (Vsa.Sim.DecodeTable.decode_02013903 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002cac#64) (0x020#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x12#5)
      (sigma3_alu σ (0x80002cac#64) Register.x18
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vbase hbase₂)
      (wX_bits_x18 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002cb0 (`ld` off=0x018(rs1=Register.x2) → Register.x19). -/
theorem site_80002cb0_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002cb0#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x018#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x018#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x19
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002cb0 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002cb0#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002cb0#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002cb0#64) vminstret (0x01813983#32)
    (instruction.LOAD (0x018#12, regidx.Regidx 0x02#5, regidx.Regidx 0x13#5, false, 8))
    Register.x19 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x39#8) (0x81#8) (0x01#8)
    hG hpc hminstret w_01813983_eg nr_01813983_eg
    (Vsa.Sim.DecodeTable.decode_01813983 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002cb0#64) (0x018#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x13#5)
      (sigma3_alu σ (0x80002cb0#64) Register.x19
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vbase hbase₂)
      (wX_bits_x19 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002cb4 (`ld` off=0x010(rs1=Register.x2) → Register.x20). -/
theorem site_80002cb4_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002cb4#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x010#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x20
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002cb4 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002cb4#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002cb4#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002cb4#64) vminstret (0x01013a03#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x02#5, regidx.Regidx 0x14#5, false, 8))
    Register.x20 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x3a#8) (0x01#8) (0x01#8)
    hG hpc hminstret w_01013a03_eg nr_01013a03_eg
    (Vsa.Sim.DecodeTable.decode_01013a03 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002cb4#64) (0x010#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x14#5)
      (sigma3_alu σ (0x80002cb4#64) Register.x20
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vbase hbase₂)
      (wX_bits_x20 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002cb8 (`ld` off=0x008(rs1=Register.x2) → Register.x21). -/
theorem site_80002cb8_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002cb8#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x21
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002cb8 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002cb8#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002cb8#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002cb8#64) vminstret (0x00813a83#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x02#5, regidx.Regidx 0x15#5, false, 8))
    Register.x21 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x3a#8) (0x81#8) (0x00#8)
    hG hpc hminstret w_00813a83_eg nr_00813a83_eg
    (Vsa.Sim.DecodeTable.decode_00813a83 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002cb8#64) (0x008#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x15#5)
      (sigma3_alu σ (0x80002cb8#64) Register.x21
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vbase hbase₂)
      (wX_bits_x21 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002cc4 (`ld` off=0x018(rs1=Register.x20) → Register.x20). -/
theorem site_80002cc4_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x20 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002cc4#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x018#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x018#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x018#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x20
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002cc4 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002cc4#64)).regs.get? Register.x20 = some vbase := by
    rw [get?_afterNextPC σ (0x80002cc4#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002cc4#64) vminstret (0x018a3a03#32)
    (instruction.LOAD (0x018#12, regidx.Regidx 0x14#5, regidx.Regidx 0x14#5, false, 8))
    Register.x20 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x3a#8) (0x8a#8) (0x01#8)
    hG hpc hminstret w_018a3a03_eg nr_018a3a03_eg
    (Vsa.Sim.DecodeTable.decode_018a3a03 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002cc4#64) (0x018#12) (regidx.Regidx 0x14#5) (regidx.Regidx 0x14#5)
      (sigma3_alu σ (0x80002cc4#64) Register.x20
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x20 _ vbase hbase₂)
      (wX_bits_x20 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c18 (`sd` Register.x19 → off=0x018(base=Register.x2)). -/
theorem site_80002c18_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hdata : σ.regs.get? Register.x19 = some vdata)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c18#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x018#12)).toNat)
    (hahiram : (vbase + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) (0x018#12)).toNat)
    (haalign : (vbase + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002c18#64)).mem
        (vbase + sign_extend (m := 64) (0x018#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c18#64)).mem
            (vbase + sign_extend (m := 64) (0x018#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c18 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c18#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c18#64) _ (by decide) (by decide)]; exact hbase
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x80002c18#64)).regs.get? Register.x19 = some vdata := by
    rw [get?_afterNextPC σ (0x80002c18#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x80002c18#64) vminstret (0x01313c23#32)
    (instruction.STORE (0x018#12, regidx.Regidx 0x13#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c18#64)).mem
      (vbase + sign_extend (m := 64) (0x018#12)).toNat (sdData_val vdata))
    (0x23#8) (0x3c#8) (0x31#8) (0x01#8)
    hG hpc hminstret w_01313c23_eg nr_01313c23_eg
    (Vsa.Sim.DecodeTable.decode_01313c23 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002c18#64) (0x018#12) (regidx.Regidx 0x13#5) (regidx.Regidx 0x02#5)
      vbase vdata hG (rX_bits_x2 _ vbase hbase₂) (rX_bits_x19 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c1c (`sd` Register.x20 → off=0x010(base=Register.x2)). -/
theorem site_80002c1c_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hdata : σ.regs.get? Register.x20 = some vdata)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c1c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x010#12)).toNat)
    (hahiram : (vbase + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) (0x010#12)).toNat)
    (haalign : (vbase + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002c1c#64)).mem
        (vbase + sign_extend (m := 64) (0x010#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c1c#64)).mem
            (vbase + sign_extend (m := 64) (0x010#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c1c hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c1c#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c1c#64) _ (by decide) (by decide)]; exact hbase
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x80002c1c#64)).regs.get? Register.x20 = some vdata := by
    rw [get?_afterNextPC σ (0x80002c1c#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x80002c1c#64) vminstret (0x01413823#32)
    (instruction.STORE (0x010#12, regidx.Regidx 0x14#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c1c#64)).mem
      (vbase + sign_extend (m := 64) (0x010#12)).toNat (sdData_val vdata))
    (0x23#8) (0x38#8) (0x41#8) (0x01#8)
    hG hpc hminstret w_01413823_eg nr_01413823_eg
    (Vsa.Sim.DecodeTable.decode_01413823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002c1c#64) (0x010#12) (regidx.Regidx 0x14#5) (regidx.Regidx 0x02#5)
      vbase vdata hG (rX_bits_x2 _ vbase hbase₂) (rX_bits_x20 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c20 (`sd` Register.x21 → off=0x008(base=Register.x2)). -/
theorem site_80002c20_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hdata : σ.regs.get? Register.x21 = some vdata)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c20#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (vbase + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (vbase + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002c20#64)).mem
        (vbase + sign_extend (m := 64) (0x008#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c20#64)).mem
            (vbase + sign_extend (m := 64) (0x008#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c20 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c20#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c20#64) _ (by decide) (by decide)]; exact hbase
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x80002c20#64)).regs.get? Register.x21 = some vdata := by
    rw [get?_afterNextPC σ (0x80002c20#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x80002c20#64) vminstret (0x01513423#32)
    (instruction.STORE (0x008#12, regidx.Regidx 0x15#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c20#64)).mem
      (vbase + sign_extend (m := 64) (0x008#12)).toNat (sdData_val vdata))
    (0x23#8) (0x34#8) (0x51#8) (0x01#8)
    hG hpc hminstret w_01513423_eg nr_01513423_eg
    (Vsa.Sim.DecodeTable.decode_01513423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002c20#64) (0x008#12) (regidx.Regidx 0x15#5) (regidx.Regidx 0x02#5)
      vbase vdata hG (rX_bits_x2 _ vbase hbase₂) (rX_bits_x21 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c24 (`sd` Register.x1 → off=0x038(base=Register.x2)). -/
theorem site_80002c24_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hdata : σ.regs.get? Register.x1 = some vdata)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c24#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x038#12)).toNat)
    (hahiram : (vbase + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) (0x038#12)).toNat)
    (haalign : (vbase + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002c24#64)).mem
        (vbase + sign_extend (m := 64) (0x038#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c24#64)).mem
            (vbase + sign_extend (m := 64) (0x038#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c24 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c24#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c24#64) _ (by decide) (by decide)]; exact hbase
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x80002c24#64)).regs.get? Register.x1 = some vdata := by
    rw [get?_afterNextPC σ (0x80002c24#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x80002c24#64) vminstret (0x02113c23#32)
    (instruction.STORE (0x038#12, regidx.Regidx 0x01#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c24#64)).mem
      (vbase + sign_extend (m := 64) (0x038#12)).toNat (sdData_val vdata))
    (0x23#8) (0x3c#8) (0x11#8) (0x02#8)
    hG hpc hminstret w_02113c23_eg nr_02113c23_eg
    (Vsa.Sim.DecodeTable.decode_02113c23 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002c24#64) (0x038#12) (regidx.Regidx 0x01#5) (regidx.Regidx 0x02#5)
      vbase vdata hG (rX_bits_x2 _ vbase hbase₂) (rX_bits_x1 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c28 (`sd` Register.x8 → off=0x030(base=Register.x2)). -/
theorem site_80002c28_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hdata : σ.regs.get? Register.x8 = some vdata)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c28#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x030#12)).toNat)
    (hahiram : (vbase + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) (0x030#12)).toNat)
    (haalign : (vbase + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002c28#64)).mem
        (vbase + sign_extend (m := 64) (0x030#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c28#64)).mem
            (vbase + sign_extend (m := 64) (0x030#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c28 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c28#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c28#64) _ (by decide) (by decide)]; exact hbase
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x80002c28#64)).regs.get? Register.x8 = some vdata := by
    rw [get?_afterNextPC σ (0x80002c28#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x80002c28#64) vminstret (0x02813823#32)
    (instruction.STORE (0x030#12, regidx.Regidx 0x08#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c28#64)).mem
      (vbase + sign_extend (m := 64) (0x030#12)).toNat (sdData_val vdata))
    (0x23#8) (0x38#8) (0x81#8) (0x02#8)
    hG hpc hminstret w_02813823_eg nr_02813823_eg
    (Vsa.Sim.DecodeTable.decode_02813823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002c28#64) (0x030#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x02#5)
      vbase vdata hG (rX_bits_x2 _ vbase hbase₂) (rX_bits_x8 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c2c (`sd` Register.x9 → off=0x028(base=Register.x2)). -/
theorem site_80002c2c_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hdata : σ.regs.get? Register.x9 = some vdata)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c2c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x028#12)).toNat)
    (hahiram : (vbase + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) (0x028#12)).toNat)
    (haalign : (vbase + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002c2c#64)).mem
        (vbase + sign_extend (m := 64) (0x028#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c2c#64)).mem
            (vbase + sign_extend (m := 64) (0x028#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c2c hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c2c#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c2c#64) _ (by decide) (by decide)]; exact hbase
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x80002c2c#64)).regs.get? Register.x9 = some vdata := by
    rw [get?_afterNextPC σ (0x80002c2c#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x80002c2c#64) vminstret (0x02913423#32)
    (instruction.STORE (0x028#12, regidx.Regidx 0x09#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c2c#64)).mem
      (vbase + sign_extend (m := 64) (0x028#12)).toNat (sdData_val vdata))
    (0x23#8) (0x34#8) (0x91#8) (0x02#8)
    hG hpc hminstret w_02913423_eg nr_02913423_eg
    (Vsa.Sim.DecodeTable.decode_02913423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002c2c#64) (0x028#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x02#5)
      vbase vdata hG (rX_bits_x2 _ vbase hbase₂) (rX_bits_x9 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c30 (`sd` Register.x18 → off=0x020(base=Register.x2)). -/
theorem site_80002c30_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x2 = some vbase)
    (hdata : σ.regs.get? Register.x18 = some vdata)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c30#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x020#12)).toNat)
    (hahiram : (vbase + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) (0x020#12)).toNat)
    (haalign : (vbase + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002c30#64)).mem
        (vbase + sign_extend (m := 64) (0x020#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c30#64)).mem
            (vbase + sign_extend (m := 64) (0x020#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c30 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c30#64)).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c30#64) _ (by decide) (by decide)]; exact hbase
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x80002c30#64)).regs.get? Register.x18 = some vdata := by
    rw [get?_afterNextPC σ (0x80002c30#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x80002c30#64) vminstret (0x03213023#32)
    (instruction.STORE (0x020#12, regidx.Regidx 0x12#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c30#64)).mem
      (vbase + sign_extend (m := 64) (0x020#12)).toNat (sdData_val vdata))
    (0x23#8) (0x30#8) (0x21#8) (0x03#8)
    hG hpc hminstret w_03213023_eg nr_03213023_eg
    (Vsa.Sim.DecodeTable.decode_03213023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002c30#64) (0x020#12) (regidx.Regidx 0x12#5) (regidx.Regidx 0x02#5)
      vbase vdata hG (rX_bits_x2 _ vbase hbase₂) (rX_bits_x18 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c8c (`sd` Register.x14 → off=0x000(base=Register.x21)). -/
theorem site_80002c8c_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x21 = some vbase)
    (hdata : σ.regs.get? Register.x14 = some vdata)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c8c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (vbase + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (vbase + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002c8c#64)).mem
        (vbase + sign_extend (m := 64) (0x000#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c8c#64)).mem
            (vbase + sign_extend (m := 64) (0x000#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c8c hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c8c#64)).regs.get? Register.x21 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c8c#64) _ (by decide) (by decide)]; exact hbase
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x80002c8c#64)).regs.get? Register.x14 = some vdata := by
    rw [get?_afterNextPC σ (0x80002c8c#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x80002c8c#64) vminstret (0x00eab023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x15#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c8c#64)).mem
      (vbase + sign_extend (m := 64) (0x000#12)).toNat (sdData_val vdata))
    (0x23#8) (0xb0#8) (0xea#8) (0x00#8)
    hG hpc hminstret w_00eab023_eg nr_00eab023_eg
    (Vsa.Sim.DecodeTable.decode_00eab023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002c8c#64) (0x000#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x15#5)
      vbase vdata hG (rX_bits_x21 _ vbase hbase₂) (rX_bits_x14 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c94 (`sd` Register.x14 → off=0x008(base=Register.x21)). -/
theorem site_80002c94_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x21 = some vbase)
    (hdata : σ.regs.get? Register.x14 = some vdata)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c94#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (vbase + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (vbase + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002c94#64)).mem
        (vbase + sign_extend (m := 64) (0x008#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c94#64)).mem
            (vbase + sign_extend (m := 64) (0x008#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c94 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c94#64)).regs.get? Register.x21 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c94#64) _ (by decide) (by decide)]; exact hbase
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x80002c94#64)).regs.get? Register.x14 = some vdata := by
    rw [get?_afterNextPC σ (0x80002c94#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x80002c94#64) vminstret (0x00eab423#32)
    (instruction.STORE (0x008#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x15#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c94#64)).mem
      (vbase + sign_extend (m := 64) (0x008#12)).toNat (sdData_val vdata))
    (0x23#8) (0xb4#8) (0xea#8) (0x00#8)
    hG hpc hminstret w_00eab423_eg nr_00eab423_eg
    (Vsa.Sim.DecodeTable.decode_00eab423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002c94#64) (0x008#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x15#5)
      vbase vdata hG (rX_bits_x21 _ vbase hbase₂) (rX_bits_x14 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c9c (`sd` Register.x15 → off=0x010(base=Register.x21)). -/
theorem site_80002c9c_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x21 = some vbase)
    (hdata : σ.regs.get? Register.x15 = some vdata)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c9c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x010#12)).toNat)
    (hahiram : (vbase + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) (0x010#12)).toNat)
    (haalign : (vbase + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002c9c#64)).mem
        (vbase + sign_extend (m := 64) (0x010#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c9c#64)).mem
            (vbase + sign_extend (m := 64) (0x010#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c9c hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c9c#64)).regs.get? Register.x21 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c9c#64) _ (by decide) (by decide)]; exact hbase
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x80002c9c#64)).regs.get? Register.x15 = some vdata := by
    rw [get?_afterNextPC σ (0x80002c9c#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x80002c9c#64) vminstret (0x00fab823#32)
    (instruction.STORE (0x010#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x15#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002c9c#64)).mem
      (vbase + sign_extend (m := 64) (0x010#12)).toNat (sdData_val vdata))
    (0x23#8) (0xb8#8) (0xfa#8) (0x00#8)
    hG hpc hminstret w_00fab823_eg nr_00fab823_eg
    (Vsa.Sim.DecodeTable.decode_00fab823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002c9c#64) (0x010#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x15#5)
      vbase vdata hG (rX_bits_x21 _ vbase hbase₂) (rX_bits_x15 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## HIT-block index arithmetic (`slli`/`add`: 24*i stride) -/

/-! ### 0x80002c74 (`slli a4,s0,1`): `x14 := s0 <<< 1`. -/
theorem site_80002c74_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c74#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (shift_bits_left v8 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c74 hmem
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80002c74#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80002c74#64) _ (by decide) (by decide)]; exact hx8
  exact stepObs_alu σ i u (0x80002c74#64) vminstret (0x00141713#32)
    (instruction.SHIFTIOP (0x01#6, (regidx.Regidx 0x08#5), (regidx.Regidx 0x0e#5), sop.SLLI))
    Register.x14 (shift_bits_left v8 (Sail.BitVec.extractLsb (0x01#6) 5 0)) (0x13#8) (0x17#8) (0x14#8) (0x00#8)
    hG hpc hminstret w_00141713_eg nr_00141713_eg
    (Vsa.Sim.DecodeTable.decode_00141713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_shiftiop_slli_char (0x01#6) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0e#5) v8
      (afterNextPC (afterPrelude σ) (0x80002c74#64))
      (sigma3_alu σ (0x80002c74#64) Register.x14 (shift_bits_left v8 (Sail.BitVec.extractLsb (0x01#6) 5 0)))
      (rX_bits_x8 _ v8 hx8₂) (wX_bits_x14 _ (shift_bits_left v8 (Sail.BitVec.extractLsb (0x01#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c78 (`add a4,a4,s0`): `x14 := a4 + s0`. -/
theorem site_80002c78_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8) (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c78#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (v14 + v8)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c78 hmem
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80002c78#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80002c78#64) _ (by decide) (by decide)]; exact hx8
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x80002c78#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x80002c78#64) _ (by decide) (by decide)]; exact hx14
  exact stepObs_alu σ i u (0x80002c78#64) vminstret (0x00870733#32)
    (instruction.RTYPE ((regidx.Regidx 0x08#5), (regidx.Regidx 0x0e#5), (regidx.Regidx 0x0e#5), rop.ADD))
    Register.x14 (v14 + v8) (0x33#8) (0x07#8) (0x87#8) (0x00#8)
    hG hpc hminstret w_00870733_eg nr_00870733_eg
    (Vsa.Sim.DecodeTable.decode_00870733 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_add_char (regidx.Regidx 0x08#5) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14 v8
      (afterNextPC (afterPrelude σ) (0x80002c78#64))
      (sigma3_alu σ (0x80002c78#64) Register.x14 (v14 + v8))
      (rX_bits_x14 _ v14 hx14₂) (rX_bits_x8 _ v8 hx8₂) (wX_bits_x14 _ (v14 + v8)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c7c (`slli a4,a4,3`): `x14 := a4 <<< 3`. -/
theorem site_80002c7c_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c7c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (shift_bits_left v14 (Sail.BitVec.extractLsb (0x03#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c7c hmem
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x80002c7c#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x80002c7c#64) _ (by decide) (by decide)]; exact hx14
  exact stepObs_alu σ i u (0x80002c7c#64) vminstret (0x00371713#32)
    (instruction.SHIFTIOP (0x03#6, (regidx.Regidx 0x0e#5), (regidx.Regidx 0x0e#5), sop.SLLI))
    Register.x14 (shift_bits_left v14 (Sail.BitVec.extractLsb (0x03#6) 5 0)) (0x13#8) (0x17#8) (0x37#8) (0x00#8)
    hG hpc hminstret w_00371713_eg nr_00371713_eg
    (Vsa.Sim.DecodeTable.decode_00371713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_shiftiop_slli_char (0x03#6) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14
      (afterNextPC (afterPrelude σ) (0x80002c7c#64))
      (sigma3_alu σ (0x80002c7c#64) Register.x14 (shift_bits_left v14 (Sail.BitVec.extractLsb (0x03#6) 5 0)))
      (rX_bits_x14 _ v14 hx14₂) (wX_bits_x14 _ (shift_bits_left v14 (Sail.BitVec.extractLsb (0x03#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c80 (`add a5,a5,a4`): `x15 := a5 + a4` (&vals[i]). -/
theorem site_80002c80_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14) (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c80#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 + v14)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c80 hmem
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x80002c80#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x80002c80#64) _ (by decide) (by decide)]; exact hx14
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002c80#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002c80#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_alu σ i u (0x80002c80#64) vminstret (0x00e787b3#32)
    (instruction.RTYPE ((regidx.Regidx 0x0e#5), (regidx.Regidx 0x0f#5), (regidx.Regidx 0x0f#5), rop.ADD))
    Register.x15 (v15 + v14) (0xb3#8) (0x87#8) (0xe7#8) (0x00#8)
    hG hpc hminstret w_00e787b3_eg nr_00e787b3_eg
    (Vsa.Sim.DecodeTable.decode_00e787b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_add_char (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15 v14
      (afterNextPC (afterPrelude σ) (0x80002c80#64))
      (sigma3_alu σ (0x80002c80#64) Register.x15 (v15 + v14))
      (rX_bits_x15 _ v15 hx15₂) (rX_bits_x14 _ v14 hx14₂) (wX_bits_x15 _ (v15 + v14)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c88 (`li a0,1`): `x10 := 0 + sext 1` (HIT return value). -/
theorem site_80002c88_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c88#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c88 hmem
  exact stepObs_alu σ i u (0x80002c88#64) vminstret (0x00100513#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0x001#12)) (0x13#8) (0x05#8) (0x10#8) (0x00#8)
    hG hpc hminstret w_00100513_eg nr_00100513_eg
    (Vsa.Sim.DecodeTable.decode_00100513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x80002c88#64))
      (sigma3_alu σ (0x80002c88#64) Register.x10 ((0#64) + sign_extend (m := 64) (0x001#12)))
      (rX_bits_zero _) (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002cbc (`addi sp,sp,64`): `x2 := sp + sext 0x040` (epilogue restore). -/
theorem site_80002cbc_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002cbc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x2 (vsp + sign_extend (m := 64) (0x040#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002cbc hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002cbc#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80002cbc#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002cbc#64) vminstret (0x04010113#32)
    (instruction.ITYPE (0x040#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))
    Register.x2 (vsp + sign_extend (m := 64) (0x040#12)) (0x13#8) (0x01#8) (0x01#8) (0x04#8)
    hG hpc hminstret w_04010113_eg nr_04010113_eg
    (Vsa.Sim.DecodeTable.decode_04010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x040#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) vsp
      (afterNextPC (afterPrelude σ) (0x80002cbc#64))
      (sigma3_alu σ (0x80002cbc#64) Register.x2 (vsp + sign_extend (m := 64) (0x040#12)))
      (rX_bits_x2 _ vsp hx2₂) (wX_bits_x2 _ (vsp + sign_extend (m := 64) (0x040#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002ccc (`li a0,0`): `x10 := 0 + sext 0` (MISS return value). -/
theorem site_80002ccc_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002ccc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002ccc hmem
  exact stepObs_alu σ i u (0x80002ccc#64) vminstret (0x00000513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x05#8) (0x00#8) (0x00#8)
    hG hpc hminstret w_00000513_eg nr_00000513_eg
    (Vsa.Sim.DecodeTable.decode_00000513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x80002ccc#64))
      (sigma3_alu σ (0x80002ccc#64) Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)))
      (rX_bits_zero _) (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Branch-class sites (`blez`/`beq`/`bnez`) -/

/-! ### 0x80002c44 (`blez s2,cc4` = `bge x0,s2`), NOT taken: `count > 0`, fall to c48. -/
theorem site_80002c44_nottaken_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v18 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx18 : σ.regs.get? Register.x18 = some v18)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c44#64 : BitVec 64)) (hv : zopz0zKzJ_s (0#64) v18 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c44 hmem
  have hx18₂ : (afterNextPC (afterPrelude σ) (0x80002c44#64)).regs.get? Register.x18 = some v18 := by
    rw [get?_afterNextPC σ (0x80002c44#64) _ (by decide) (by decide)]; exact hx18
  exact stepObs_branch_nottaken σ i u (0x80002c44#64) vminstret (0x0080#13)
    (regidx.Regidx 0x00#5) (regidx.Regidx 0x12#5) bop.BGE (0x09205063#32)
    (0x63#8) (0x50#8) (0x20#8) (0x09#8)
    hG hpc hminstret w_09205063_eg nr_09205063_eg
    (Vsa.Sim.DecodeTable.decode_09205063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bge_nottaken (0x0080#13) (regidx.Regidx 0x00#5) (regidx.Regidx 0x12#5)
      (0#64) v18 (afterNextPC (afterPrelude σ) (0x80002c44#64))
      (rX_bits_zero _) (rX_bits_x18 _ v18 hx18₂) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c44 (`blez s2,cc4`), TAKEN: `count <= 0`, branch to cc4 (descend). -/
theorem site_80002c44_taken_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v18 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx18 : σ.regs.get? Register.x18 = some v18)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c44#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x0080#13)).toNat % 4 = 0)
    (hv : zopz0zKzJ_s (0#64) v18 = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0080#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c44 hmem
  have hx18₂ : (afterNextPC (afterPrelude σ) (0x80002c44#64)).regs.get? Register.x18 = some v18 := by
    rw [get?_afterNextPC σ (0x80002c44#64) _ (by decide) (by decide)]; exact hx18
  have hpc₂ : (afterNextPC (afterPrelude σ) (0x80002c44#64)).regs.get? Register.PC
      = some (0x80002c44#64 : BitVec 64) := by
    rw [get?_afterNextPC σ (0x80002c44#64) _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) (0x80002c44#64)).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ (0x80002c44#64) _ (by decide) (by decide)]; exact hG.misa
  exact stepObs_branch_taken σ i u (0x80002c44#64) vminstret (0x0080#13)
    (regidx.Regidx 0x00#5) (regidx.Regidx 0x12#5) bop.BGE (0x09205063#32)
    (0x63#8) (0x50#8) (0x20#8) (0x09#8)
    hG hpc hminstret w_09205063_eg nr_09205063_eg
    (Vsa.Sim.DecodeTable.decode_09205063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bge_taken (0x0080#13) (regidx.Regidx 0x00#5) (regidx.Regidx 0x12#5)
      (0#64) v18 (0x80002c44#64) initMisa (afterNextPC (afterPrelude σ) (0x80002c44#64))
      (rX_bits_zero _) (rX_bits_x18 _ v18 hx18₂) hpc₂ hmisa₂ htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c5c (`beq s0,s2,cc4` = SCAN TEST), NOT taken: `i != count`, fall to c60. -/
theorem site_80002c5c_nottaken_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 v18 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8) (hx18 : σ.regs.get? Register.x18 = some v18)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c5c#64 : BitVec 64)) (hv : (v8 == v18) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c5c hmem
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80002c5c#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80002c5c#64) _ (by decide) (by decide)]; exact hx8
  have hx18₂ : (afterNextPC (afterPrelude σ) (0x80002c5c#64)).regs.get? Register.x18 = some v18 := by
    rw [get?_afterNextPC σ (0x80002c5c#64) _ (by decide) (by decide)]; exact hx18
  exact stepObs_branch_nottaken σ i u (0x80002c5c#64) vminstret (0x0068#13)
    (regidx.Regidx 0x08#5) (regidx.Regidx 0x12#5) bop.BEQ (0x07240463#32)
    (0x63#8) (0x04#8) (0x24#8) (0x07#8)
    hG hpc hminstret w_07240463_eg nr_07240463_eg
    (Vsa.Sim.DecodeTable.decode_07240463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_nottaken (0x0068#13) (regidx.Regidx 0x08#5) (regidx.Regidx 0x12#5)
      v8 v18 (afterNextPC (afterPrelude σ) (0x80002c5c#64))
      (rX_bits_x8 _ v8 hx8₂) (rX_bits_x18 _ v18 hx18₂) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c5c (`beq s0,s2,cc4`), TAKEN: `i == count` (scan exhausted), branch to cc4. -/
theorem site_80002c5c_taken_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 v18 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8) (hx18 : σ.regs.get? Register.x18 = some v18)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c5c#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x0068#13)).toNat % 4 = 0)
    (hv : (v8 == v18) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0068#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c5c hmem
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80002c5c#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80002c5c#64) _ (by decide) (by decide)]; exact hx8
  have hx18₂ : (afterNextPC (afterPrelude σ) (0x80002c5c#64)).regs.get? Register.x18 = some v18 := by
    rw [get?_afterNextPC σ (0x80002c5c#64) _ (by decide) (by decide)]; exact hx18
  have hpc₂ : (afterNextPC (afterPrelude σ) (0x80002c5c#64)).regs.get? Register.PC
      = some (0x80002c5c#64 : BitVec 64) := by
    rw [get?_afterNextPC σ (0x80002c5c#64) _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) (0x80002c5c#64)).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ (0x80002c5c#64) _ (by decide) (by decide)]; exact hG.misa
  exact stepObs_branch_taken σ i u (0x80002c5c#64) vminstret (0x0068#13)
    (regidx.Regidx 0x08#5) (regidx.Regidx 0x12#5) bop.BEQ (0x07240463#32)
    (0x63#8) (0x04#8) (0x24#8) (0x07#8)
    hG hpc hminstret w_07240463_eg nr_07240463_eg
    (Vsa.Sim.DecodeTable.decode_07240463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_taken (0x0068#13) (regidx.Regidx 0x08#5) (regidx.Regidx 0x12#5)
      v8 v18 (0x80002c5c#64) initMisa (afterNextPC (afterPrelude σ) (0x80002c5c#64))
      (rX_bits_x8 _ v8 hx8₂) (rX_bits_x18 _ v18 hx18₂) hpc₂ hmisa₂ htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c6c (`bnez a0,c54` = `bne a0,x0`), NOT taken: `strcmp == 0` (HIT), fall to c70. -/
theorem site_80002c6c_nottaken_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c6c#64 : BitVec 64)) (hv : (v10 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c6c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002c6c#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80002c6c#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_branch_nottaken σ i u (0x80002c6c#64) vminstret (0x1fe8#13)
    (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5) bop.BNE (0xfe0514e3#32)
    (0xe3#8) (0x14#8) (0x05#8) (0xfe#8)
    hG hpc hminstret w_fe0514e3_eg nr_fe0514e3_eg
    (Vsa.Sim.DecodeTable.decode_fe0514e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bne_nottaken (0x1fe8#13) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
      v10 (0#64) (afterNextPC (afterPrelude σ) (0x80002c6c#64))
      (rX_bits_x10 _ v10 hx10₂) (rX_bits_zero _) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c6c (`bnez a0,c54`), TAKEN: `strcmp != 0`, branch back to c54 (next iter). -/
theorem site_80002c6c_taken_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c6c#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1fe8#13)).toNat % 4 = 0)
    (hv : (v10 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1fe8#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c6c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002c6c#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80002c6c#64) _ (by decide) (by decide)]; exact hx10
  have hpc₂ : (afterNextPC (afterPrelude σ) (0x80002c6c#64)).regs.get? Register.PC
      = some (0x80002c6c#64 : BitVec 64) := by
    rw [get?_afterNextPC σ (0x80002c6c#64) _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) (0x80002c6c#64)).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ (0x80002c6c#64) _ (by decide) (by decide)]; exact hG.misa
  exact stepObs_branch_taken σ i u (0x80002c6c#64) vminstret (0x1fe8#13)
    (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5) bop.BNE (0xfe0514e3#32)
    (0xe3#8) (0x14#8) (0x05#8) (0xfe#8)
    hG hpc hminstret w_fe0514e3_eg nr_fe0514e3_eg
    (Vsa.Sim.DecodeTable.decode_fe0514e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bne_taken (0x1fe8#13) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
      v10 (0#64) (0x80002c6c#64) initMisa (afterNextPC (afterPrelude σ) (0x80002c6c#64))
      (rX_bits_x10 _ v10 hx10₂) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002cc8 (`bnez s4,c40` = CHAIN TEST), NOT taken: `parent == 0`, fall to ccc (MISS). -/
theorem site_80002cc8_nottaken_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002cc8#64 : BitVec 64)) (hv : (v20 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002cc8 hmem
  have hx20₂ : (afterNextPC (afterPrelude σ) (0x80002cc8#64)).regs.get? Register.x20 = some v20 := by
    rw [get?_afterNextPC σ (0x80002cc8#64) _ (by decide) (by decide)]; exact hx20
  exact stepObs_branch_nottaken σ i u (0x80002cc8#64) vminstret (0x1f78#13)
    (regidx.Regidx 0x14#5) (regidx.Regidx 0x00#5) bop.BNE (0xf60a1ce3#32)
    (0xe3#8) (0x1c#8) (0x0a#8) (0xf6#8)
    hG hpc hminstret w_f60a1ce3_eg nr_f60a1ce3_eg
    (Vsa.Sim.DecodeTable.decode_f60a1ce3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bne_nottaken (0x1f78#13) (regidx.Regidx 0x14#5) (regidx.Regidx 0x00#5)
      v20 (0#64) (afterNextPC (afterPrelude σ) (0x80002cc8#64))
      (rX_bits_x20 _ v20 hx20₂) (rX_bits_zero _) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002cc8 (`bnez s4,c40`), TAKEN: `parent != 0`, branch to c40 (next chain head). -/
theorem site_80002cc8_taken_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002cc8#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1f78#13)).toNat % 4 = 0)
    (hv : (v20 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1f78#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002cc8 hmem
  have hx20₂ : (afterNextPC (afterPrelude σ) (0x80002cc8#64)).regs.get? Register.x20 = some v20 := by
    rw [get?_afterNextPC σ (0x80002cc8#64) _ (by decide) (by decide)]; exact hx20
  have hpc₂ : (afterNextPC (afterPrelude σ) (0x80002cc8#64)).regs.get? Register.PC
      = some (0x80002cc8#64 : BitVec 64) := by
    rw [get?_afterNextPC σ (0x80002cc8#64) _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) (0x80002cc8#64)).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ (0x80002cc8#64) _ (by decide) (by decide)]; exact hG.misa
  exact stepObs_branch_taken σ i u (0x80002cc8#64) vminstret (0x1f78#13)
    (regidx.Regidx 0x14#5) (regidx.Regidx 0x00#5) bop.BNE (0xf60a1ce3#32)
    (0xe3#8) (0x1c#8) (0x0a#8) (0xf6#8)
    hG hpc hminstret w_f60a1ce3_eg nr_f60a1ce3_eg
    (Vsa.Sim.DecodeTable.decode_f60a1ce3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bne_taken (0x1f78#13) (regidx.Regidx 0x14#5) (regidx.Regidx 0x00#5)
      v20 (0#64) (0x80002cc8#64) initMisa (afterNextPC (afterPrelude σ) (0x80002cc8#64))
      (rX_bits_x20 _ v20 hx20₂) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Jump-class sites (`j`/`jal`/`ret`) -/

/-! ### 0x80002c50 (`j 0x80002c60` = `jal x0`): enter scan loop at the test. -/
theorem site_80002c50_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c50#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x000010#21)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x000010#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c50 hmem
  exact stepObs_j σ i u (0x80002c50#64) vminstret (0x0100006f#32) (0x000010#21)
    (0x6f#8) (0x00#8) (0x00#8) (0x01#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) (by decide) w_0100006f_eg
    (Vsa.Sim.DecodeTable.decode_0100006f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt hi

/-! ### 0x80002c68 (`jal strcmp` = `jal x1`, imm 0x004238 → 0x80006ea0). -/
theorem site_80002c68_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c68#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x004238#21)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x004238#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c68 hmem
  refine stepObs_jal σ i u (0x80002c68#64) vminstret (0x238040ef#32) (0x004238#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80002c68#64) 4) (0xef#8) (0x40#8) (0x80#8) (0x23#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) nr_238040ef_eg w_238040ef_eg
    (Vsa.Sim.DecodeTable.decode_238040ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi
  exact wX_bits_x1 _ (BitVec.addInt (0x80002c68#64) 4)

/-! ### 0x80002cc0 (`ret` = `jr x1`): epilogue return. -/
theorem site_80002cc0_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002cc0#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002cc0 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80002cc0#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80002cc0#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80002cc0#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80002cc0#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00008067_eg w_00008067_eg
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

/-! ### 0x80002cd0 (`j 0x80002ca0` = `jal x0`, imm 0x1fffd0 → epilogue with a0=0). -/
theorem site_80002cd0_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002cd0#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1fffd0#21)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x1fffd0#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002cd0 hmem
  exact stepObs_j σ i u (0x80002cd0#64) vminstret (0xfd1ff06f#32) (0x1fffd0#21)
    (0x6f#8) (0xf0#8) (0x1f#8) (0xfd#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) (by decide) w_fd1ff06f_eg
    (Vsa.Sim.DecodeTable.decode_fd1ff06f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt hi

/-! ### 0x80002cd4 (`li a0,0`): NULL-env entry return value. -/
theorem site_80002cd4_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002cd4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002cd4 hmem
  exact stepObs_alu σ i u (0x80002cd4#64) vminstret (0x00000513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x05#8) (0x00#8) (0x00#8)
    hG hpc hminstret w_00000513_eg nr_00000513_eg
    (Vsa.Sim.DecodeTable.decode_00000513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x80002cd4#64))
      (sigma3_alu σ (0x80002cd4#64) Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)))
      (rX_bits_zero _) (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002cd8 (`ret` = `jr x1`): NULL-env entry return. -/
theorem site_80002cd8_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002cd8#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002cd8 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80002cd8#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80002cd8#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80002cd8#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80002cd8#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00008067_eg w_00008067_eg
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

end Vsa.Sim

