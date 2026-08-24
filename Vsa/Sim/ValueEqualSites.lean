import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch02Part20
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch03Part03
import Vsa.Sim.DecodeTable.Batch03Part11
import Vsa.Sim.DecodeTable.Batch03Part20
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch07Part04
import Vsa.Sim.DecodeTable.Batch07Part06
import Vsa.Sim.DecodeTable.Batch11Part24
import Vsa.Sim.DecodeTable.Batch12Part27
import Vsa.Sim.ValueSites
import Vsa.Sim.Code.Value_equal

/-!
# Layer 3 — per-site observational step lemmas for `value_equal` (@0x8000285c)

`value_equal(Value a, Value b)` takes both 24-byte `Value`s **by reference**
(`a0`/`a1` = pointers). It:

* loads both kind tags (`lw a4,0(a0); lw a5,0(a1)`),
* `bne a5,a4 → 0x8000288c` (`li a0,0; ret`) if the kinds differ,
* `li a4,5; bltu a4,a5 → 0x8000288c` (out-of-range kind guard),
* dispatches through a `.rodata` jump table at `0x80019ef8` (`auipc/addi` build the
  base, `slli a5,a5,2; add a5,a5,a4; lw a5,0(a5); add a5,a5,a4; jr a5`).

Per-kind handlers:

* kind 0 (null)    → 0x800028a8: `li a0,1; ret`
* kind 1 (bool)    → 0x800028b0: `lw a0,8(a0); lw a5,8(a1); sub a0,a0,a5; seqz a0,a0; ret`
* kind 2 (int)     → 0x80002894: `ld a0,8(a0); ld a5,8(a1); sub; seqz; ret`
* kind 3 (str)     → 0x800028c4: `ld a1,8(a1); ld a0,8(a0); <strcmp call>; seqz; ret`
* kind 4 (closure) → 0x80002894 (SAME as int: compares the 8-byte `Closure*` at +8)
* kind 5 (native)  → 0x800028e8: `ld a0,16(a0); ld a5,16(a1); sub; seqz; ret`

The jump-table read at `0x80002880` (`lw a5,0(a5)`) reads `.rodata` *outside* the
code region, so its site takes the four table-entry bytes as explicit hypotheses.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## 0x8000285c — `lw a4,0(a0)` (kind of `a`). Writes `x14`. -/
theorem site_8000285c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbufa : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbufa)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x8000285c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbufa + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (vbufa + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbufa + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbufa + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (vbufa + sign_extend (m := 64) (0x000#12)).toNat % 4 = 0)
    (h0 : σ.mem[(vbufa + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (h1 : σ.mem[(vbufa + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbufa + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbufa + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_8000285c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x8000285c#64)).regs.get? Register.x10 = some vbufa := by
    rw [get?_afterNextPC σ (0x8000285c#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x8000285c#64) vminstret (0x00052703#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, false, 4))
    Register.x14 (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))
    (0x03#8) (0x27#8) (0x05#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00052703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x8000285c#64) (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0e#5)
      (sigma3_alu σ (0x8000285c#64) Register.x14
        (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      vbufa b0 b1 b2 b3 hG (rX_bits_x10 _ vbufa hx10₂)
      (wX_bits_x14 _ (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## 0x80002860 — `lw a5,0(a1)` (kind of `b`). Writes `x15`. -/
theorem site_80002860
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbufb : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some vbufb)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x80002860#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbufb + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (vbufb + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbufb + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbufb + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (vbufb + sign_extend (m := 64) (0x000#12)).toNat % 4 = 0)
    (h0 : σ.mem[(vbufb + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (h1 : σ.mem[(vbufb + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbufb + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbufb + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_80002860 hmem
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x80002860#64)).regs.get? Register.x11 = some vbufb := by
    rw [get?_afterNextPC σ (0x80002860#64) _ (by decide) (by decide)]; exact hx11
  exact stepObs_alu σ i u (0x80002860#64) vminstret (0x0005a783#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, false, 4))
    Register.x15 (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))
    (0x83#8) (0xa7#8) (0x05#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0005a783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x80002860#64) (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x80002860#64) Register.x15
        (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      vbufb b0 b1 b2 b3 hG (rX_bits_x11 _ vbufb hx11₂)
      (wX_bits_x15 _ (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## 0x80002864 — `bne a5,a4` (rs1=x15, rs2=x14), imm 0x028 → 0x8000288c -/

theorem exec_bne_a5_a4_taken (σ : MState) (pc : BitVec 64) (v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx14 : σ.regs.get? Register.x14 = some v14)
    (htgt : (pc + sign_extend (m := 64) (0x028#13)).toNat % 4 = 0)
    (hv : (v15 != v14) = true) :
    (execute (instruction.BTYPE (0x028#13, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x028#13)) := by
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bne_taken (0x028#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5)
    v15 v14 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 h15) (rX_bits_x14 _ v14 h14) hpc₂ hmisa₂ htgt hv

theorem exec_bne_a5_a4_nottaken (σ : MState) (pc : BitVec 64) (v15 v14 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx14 : σ.regs.get? Register.x14 = some v14)
    (hv : (v15 != v14) = false) :
    (execute (instruction.BTYPE (0x028#13, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_btype_bne_nottaken (0x028#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5)
    v15 v14 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 h15) (rX_bits_x14 _ v14 h14) hv

theorem site_80002864_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x80002864#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x028#13)).toNat % 4 = 0)
    (hv : (v15 != v14) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x028#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_80002864 hmem
  exact stepObs_branch_taken σ i u (0x80002864#64) vminstret (0x028#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) bop.BNE (0x02e79463#32)
    (0x63#8) (0x94#8) (0xe7#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02e79463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_a5_a4_taken σ (0x80002864#64) v15 v14 hG hpc hx15 hx14 htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80002864_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x80002864#64 : BitVec 64))
    (hv : (v15 != v14) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_80002864 hmem
  exact stepObs_branch_nottaken σ i u (0x80002864#64) vminstret (0x028#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) bop.BNE (0x02e79463#32)
    (0x63#8) (0x94#8) (0xe7#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02e79463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_a5_a4_nottaken σ (0x80002864#64) v15 v14 hx15 hx14 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## 0x80002868 — `li a4,5` (addi a4,zero,5). Writes `x14 := 5`. -/
theorem site_80002868
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x80002868#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 ((0#64) + sign_extend (m := 64) (0x005#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_80002868 hmem
  exact stepObs_alu σ i u (0x80002868#64) vminstret (0x00500713#32)
    (instruction.ITYPE (0x005#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0e#5, iop.ADDI))
    Register.x14 ((0#64) + sign_extend (m := 64) (0x005#12)) (0x13#8) (0x07#8) (0x50#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00500713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x005#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0e#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x80002868#64))
      (sigma3_alu σ (0x80002868#64) Register.x14 ((0#64) + sign_extend (m := 64) (0x005#12)))
      (rX_bits_zero _) (wX_bits_x14 _ ((0#64) + sign_extend (m := 64) (0x005#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## 0x8000286c — `bltu a4,a5` (rs1=x14, rs2=x15), imm 0x020 → 0x8000288c -/

theorem exec_bltu_a4_a5_taken (σ : MState) (pc : BitVec 64) (v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx14 : σ.regs.get? Register.x14 = some v14) (hx15 : σ.regs.get? Register.x15 = some v15)
    (htgt : (pc + sign_extend (m := 64) (0x020#13)).toNat % 4 = 0)
    (hv : zopz0zI_u v14 v15 = true) :
    (execute (instruction.BTYPE (0x020#13, regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, bop.BLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x020#13)) := by
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bltu_taken (0x020#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5)
    v14 v15 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x14 _ v14 h14) (rX_bits_x15 _ v15 h15) hpc₂ hmisa₂ htgt hv

theorem exec_bltu_a4_a5_nottaken (σ : MState) (pc : BitVec 64) (v14 v15 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) (hx15 : σ.regs.get? Register.x15 = some v15)
    (hv : zopz0zI_u v14 v15 = false) :
    (execute (instruction.BTYPE (0x020#13, regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, bop.BLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_btype_bltu_nottaken (0x020#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5)
    v14 v15 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x14 _ v14 h14) (rX_bits_x15 _ v15 h15) hv

theorem site_8000286c_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14) (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x8000286c#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x020#13)).toNat % 4 = 0)
    (hv : zopz0zI_u v14 v15 = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x020#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_8000286c hmem
  exact stepObs_branch_taken σ i u (0x8000286c#64) vminstret (0x020#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) bop.BLTU (0x02f76063#32)
    (0x63#8) (0x60#8) (0xf7#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02f76063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bltu_a4_a5_taken σ (0x8000286c#64) v14 v15 hG hpc hx14 hx15 htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_8000286c_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14) (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x8000286c#64 : BitVec 64))
    (hv : zopz0zI_u v14 v15 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_8000286c hmem
  exact stepObs_branch_nottaken σ i u (0x8000286c#64) vminstret (0x020#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) bop.BLTU (0x02f76063#32)
    (0x63#8) (0x60#8) (0xf7#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02f76063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bltu_a4_a5_nottaken σ (0x8000286c#64) v14 v15 hx14 hx15 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## 0x80002870 — `auipc a4,0x17`. Writes `x14 := pc + sext(0x17 <<< 12) = 0x80019870`. -/
theorem exec_auipc_a4 (σ : MState) (pc : BitVec 64)
    (hpc : σ.regs.get? Register.PC = some pc) :
    (execute (instruction.UTYPE (0x00017#20, regidx.Regidx 0x0e#5, uop.AUIPC))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14 (pc + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))) := by
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  exact execute_utype_auipc_char (0x00017#20) (regidx.Regidx 0x0e#5) pc
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x14 (pc + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))) hpc₂
    (wX_bits_x14 _ (pc + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12)))

theorem site_80002870
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x80002870#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (pc + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_80002870 hmem
  exact stepObs_alu σ i u (0x80002870#64) vminstret (0x00017717#32)
    (instruction.UTYPE (0x00017#20, regidx.Regidx 0x0e#5, uop.AUIPC))
    Register.x14 ((0x80002870#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
    (0x17#8) (0x77#8) (0x01#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00017717 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_auipc_a4 σ (0x80002870#64) hpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## 0x80002874 — `addi a4,a4,1672` (0x688). Writes `x14 := v14 + sext 0x688`. -/
theorem exec_addi_a4_a4 (σ : MState) (pc : BitVec 64) (v14 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.ITYPE (0x688#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14 (v14 + sign_extend (m := 64) (0x688#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_itype_addi_char (0x688#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x14 (v14 + sign_extend (m := 64) (0x688#12)))
    (rX_bits_x14 _ v14 h₂) (wX_bits_x14 _ (v14 + sign_extend (m := 64) (0x688#12)))

theorem site_80002874
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x80002874#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 (v14 + sign_extend (m := 64) (0x688#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_80002874 hmem
  exact stepObs_alu σ i u (0x80002874#64) vminstret (0x68870713#32)
    (instruction.ITYPE (0x688#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ADDI))
    Register.x14 (v14 + sign_extend (m := 64) (0x688#12)) (0x13#8) (0x07#8) (0x87#8) (0x68#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_68870713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a4_a4 σ (0x80002874#64) v14 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## 0x80002878 — `slli a5,a5,2` (rd=x15, rs1=x15, shamt=2). -/
theorem exec_slli_a5 (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.SHIFTIOP (0x02#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, sop.SLLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_shiftiop_slli_char (0x02#6) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0)))
    (rX_bits_x15 _ v15 h₂)
    (wX_bits_x15 _ (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0)))

theorem site_80002878
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x80002878#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_80002878 hmem
  exact stepObs_alu σ i u (0x80002878#64) vminstret (0x00279793#32)
    (instruction.SHIFTIOP (0x02#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, sop.SLLI))
    Register.x15 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0))
    (0x93#8) (0x97#8) (0x27#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00279793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_a5 σ (0x80002878#64) v15 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## 0x8000287c / 0x80002884 — `add a5,a5,a4` (rd=x15, rs1=x15, rs2=x14). -/
theorem exec_add_a5_a5_a4 (σ : MState) (pc : BitVec 64) (v15 v14 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v15 + v14)) := by
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_rtype_add_char (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
    v15 v14 (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (v15 + v14))
    (rX_bits_x15 _ v15 h15) (rX_bits_x14 _ v14 h14) (wX_bits_x15 _ (v15 + v14))

theorem site_8000287c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x8000287c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 + v14)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_8000287c hmem
  exact stepObs_alu σ i u (0x8000287c#64) vminstret (0x00e787b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))
    Register.x15 (v15 + v14) (0xb3#8) (0x87#8) (0xe7#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00e787b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_a5_a5_a4 σ (0x8000287c#64) v15 v14 hx15 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80002884
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x80002884#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 + v14)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_80002884 hmem
  exact stepObs_alu σ i u (0x80002884#64) vminstret (0x00e787b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))
    Register.x15 (v15 + v14) (0xb3#8) (0x87#8) (0xe7#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00e787b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_a5_a5_a4 σ (0x80002884#64) v15 v14 hx15 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## 0x80002880 — `lw a5,0(a5)` : the JUMP-TABLE read.

`a5 = 0x80019ef8 + 4*kind` (in `.rodata`, outside the code region), so the four
table-entry bytes `t0..t3` are passed as explicit hypotheses (not from
`Value_equalLoaded`). Writes `x15 := sign_extend (t3 ++ t2 ++ t1 ++ t0)`. -/
theorem site_80002880
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vtab : BitVec 64) (t0 t1 t2 t3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some vtab)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x80002880#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vtab + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (vtab + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (vtab + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vtab + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (vtab + sign_extend (m := 64) (0x000#12)).toNat % 4 = 0)
    (h0 : σ.mem[(vtab + sign_extend (m := 64) (0x000#12)).toNat]? = some t0)
    (h1 : σ.mem[(vtab + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some t1)
    (h2 : σ.mem[(vtab + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some t2)
    (h3 : σ.mem[(vtab + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some t3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_80002880 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002880#64)).regs.get? Register.x15 = some vtab := by
    rw [get?_afterNextPC σ (0x80002880#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_alu σ i u (0x80002880#64) vminstret (0x0007a783#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, false, 4))
    Register.x15 (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4)))
    (0x83#8) (0xa7#8) (0x07#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0007a783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x80002880#64) (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x80002880#64) Register.x15
        (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))))
      vtab t0 t1 t2 t3 hG (rX_bits_x15 _ vtab hx15₂)
      (wX_bits_x15 _ (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## 0x80002888 — `jr a5` : the computed dispatch jump (`jalr x0, 0(a5)`).

`a5 = jumptable-target` = one of the six handler addresses. `stepObs_jr` with
rs1=x15; the target-alignment side condition `htgt` selects a 4-aligned code addr. -/
theorem site_80002888
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vtgt : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some vtgt)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x80002888#64 : BitVec 64))
    (htgt : (BitVec.update (vtgt + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret
          (BitVec.update (vtgt + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_80002888 hmem
  have hx15₂ : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ) (0x80002888#64))
      = .ok vtgt (afterNextPC (afterPrelude σ) (0x80002888#64)) := by
    apply rX_bits_x15
    rw [get?_afterNextPC σ (0x80002888#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_jr σ i u (0x80002888#64) vminstret vtgt (0x00078067#32) (0x000#12)
    (regidx.Regidx 0x0f#5) (0x67#8) (0x80#8) (0x07#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00078067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx15₂ htgt hi

/-! ## Shared handler-tail instructions -----------------------------------------

`sub a0,a0,a5` (rd=x10, rs1=x10, rs2=x15) and `seqz a0,a0` (sltiu a0,a0,1) appear
in the int/closure, bool, and native tails; `li a0,0/1` and `ret` close the
mismatch/null/tail paths. -/

theorem exec_sub_a0_a0_a5 (σ : MState) (pc : BitVec 64) (v10 v15 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, rop.SUB))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x10 (v10 - v15)) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_rtype_sub_char (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5)
    v10 v15 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 (v10 - v15))
    (rX_bits_x10 _ v10 h10) (rX_bits_x15 _ v15 h15) (wX_bits_x10 _ (v10 - v15))

theorem exec_seqz_a0 (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.ITYPE (0x001#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, iop.SLTIU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10
            (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v10 (sign_extend (m := 64) (0x001#12)))))) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_itype_sltiu_char (0x001#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5) v10
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x10
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v10 (sign_extend (m := 64) (0x001#12))))))
    (rX_bits_x10 _ v10 h10)
    (wX_bits_x10 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v10 (sign_extend (m := 64) (0x001#12))))))

/-! ### `sub a0,a0,a5` at 0x8000289c (int/closure), 0x800028b8 (bool), 0x800028f0 (native) -/

theorem site_8000289c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10) (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x8000289c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v10 - v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_8000289c hmem
  exact stepObs_alu σ i u (0x8000289c#64) vminstret (0x40f50533#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, rop.SUB))
    Register.x10 (v10 - v15) (0x33#8) (0x05#8) (0xf5#8) (0x40#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_40f50533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sub_a0_a0_a5 σ (0x8000289c#64) v10 v15 hx10 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_800028b8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10) (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028b8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v10 - v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028b8 hmem
  exact stepObs_alu σ i u (0x800028b8#64) vminstret (0x40f50533#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, rop.SUB))
    Register.x10 (v10 - v15) (0x33#8) (0x05#8) (0xf5#8) (0x40#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_40f50533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sub_a0_a0_a5 σ (0x800028b8#64) v10 v15 hx10 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_800028f0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10) (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028f0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v10 - v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028f0 hmem
  exact stepObs_alu σ i u (0x800028f0#64) vminstret (0x40f50533#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, rop.SUB))
    Register.x10 (v10 - v15) (0x33#8) (0x05#8) (0xf5#8) (0x40#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_40f50533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sub_a0_a0_a5 σ (0x800028f0#64) v10 v15 hx10 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### `seqz a0,a0` at 0x800028a0 (int/closure), 0x800028bc (bool), 0x800028f4 (native)

`seqz a0,a0` = `sltiu a0,a0,1`: writes `x10 := cond (v10 = 0) 1 0`. -/

theorem site_800028a0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028a0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v10 (sign_extend (m := 64) (0x001#12)))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028a0 hmem
  exact stepObs_alu σ i u (0x800028a0#64) vminstret (0x00153513#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, iop.SLTIU))
    Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v10 (sign_extend (m := 64) (0x001#12)))))
    (0x13#8) (0x35#8) (0x15#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00153513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_seqz_a0 σ (0x800028a0#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_800028bc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028bc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v10 (sign_extend (m := 64) (0x001#12)))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028bc hmem
  exact stepObs_alu σ i u (0x800028bc#64) vminstret (0x00153513#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, iop.SLTIU))
    Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v10 (sign_extend (m := 64) (0x001#12)))))
    (0x13#8) (0x35#8) (0x15#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00153513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_seqz_a0 σ (0x800028bc#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_800028f4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028f4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v10 (sign_extend (m := 64) (0x001#12)))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028f4 hmem
  exact stepObs_alu σ i u (0x800028f4#64) vminstret (0x00153513#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, iop.SLTIU))
    Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v10 (sign_extend (m := 64) (0x001#12)))))
    (0x13#8) (0x35#8) (0x15#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00153513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_seqz_a0 σ (0x800028f4#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### `li a0,0` @0x8000288c (mismatch/oob), `li a0,1` @0x800028a8 (null) -/

theorem site_8000288c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x8000288c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_8000288c hmem
  exact stepObs_alu σ i u (0x8000288c#64) vminstret (0x00000513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x05#8) (0x00#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00000513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x8000288c#64))
      (sigma3_alu σ (0x8000288c#64) Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)))
      (rX_bits_zero _) (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_800028a8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028a8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028a8 hmem
  exact stepObs_alu σ i u (0x800028a8#64) vminstret (0x00100513#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0x001#12)) (0x13#8) (0x05#8) (0x10#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00100513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x800028a8#64))
      (sigma3_alu σ (0x800028a8#64) Register.x10 ((0#64) + sign_extend (m := 64) (0x001#12)))
      (rX_bits_zero _) (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### `ret` sites @0x80002890, 0x800028a4, 0x800028ac, 0x800028c0, 0x800028f8 -/

theorem site_ret_gen
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hword : (((b3.append b2).append b1).append b0) = (0x00008067#32 : BitVec 32))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret
          (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) pc)
      = .ok vra (afterNextPC (afterPrelude σ) pc) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u pc vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) b0 b1 b2 b3
    hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign
    (by rw [hword]; apply BitVec.eq_of_toNat_eq; decide) hword
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

/-! ### Payload loads (int/closure @+8, bool @+8 word, native @+16) -/

/-- `ld a0,8(a0)` @0x80002894 (int/closure) — loads `a`'s 8-byte payload into `x10`. -/
theorem site_80002894
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbufa : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbufa)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x80002894#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbufa + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vbufa + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbufa + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbufa + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vbufa + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_80002894 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002894#64)).regs.get? Register.x10 = some vbufa := by
    rw [get?_afterNextPC σ (0x80002894#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80002894#64) vminstret (0x00853503#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, false, 8))
    Register.x10 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x35#8) (0x85#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00853503 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002894#64) (0x008#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x80002894#64) Register.x10 (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      vbufa b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ vbufa hx10₂)
      (wX_bits_x10 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- `ld a5,8(a1)` @0x80002898 (int/closure) — loads `b`'s 8-byte payload into `x15`. -/
theorem site_80002898
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbufb : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some vbufb)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x80002898#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbufb + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vbufb + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbufb + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbufb + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vbufb + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_80002898 hmem
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x80002898#64)).regs.get? Register.x11 = some vbufb := by
    rw [get?_afterNextPC σ (0x80002898#64) _ (by decide) (by decide)]; exact hx11
  exact stepObs_alu σ i u (0x80002898#64) vminstret (0x0085b783#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, false, 8))
    Register.x15 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0xb7#8) (0x85#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0085b783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002898#64) (0x008#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x80002898#64) Register.x15 (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      vbufb b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x11 _ vbufb hx11₂)
      (wX_bits_x15 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- `lw a0,8(a0)` @0x800028b0 (bool) — loads `a`'s 4-byte bool payload into `x10`. -/
theorem site_800028b0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbufa : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbufa)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028b0#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbufa + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vbufa + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbufa + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbufa + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vbufa + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (h0 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028b0 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x800028b0#64)).regs.get? Register.x10 = some vbufa := by
    rw [get?_afterNextPC σ (0x800028b0#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x800028b0#64) vminstret (0x00852503#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, false, 4))
    Register.x10 (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))
    (0x03#8) (0x25#8) (0x85#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00852503 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x800028b0#64) (0x008#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x800028b0#64) Register.x10
        (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      vbufa b0 b1 b2 b3 hG (rX_bits_x10 _ vbufa hx10₂)
      (wX_bits_x10 _ (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- `lw a5,8(a1)` @0x800028b4 (bool) — loads `b`'s 4-byte bool payload into `x15`. -/
theorem site_800028b4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbufb : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some vbufb)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028b4#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbufb + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vbufb + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbufb + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbufb + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vbufb + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (h0 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028b4 hmem
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x800028b4#64)).regs.get? Register.x11 = some vbufb := by
    rw [get?_afterNextPC σ (0x800028b4#64) _ (by decide) (by decide)]; exact hx11
  exact stepObs_alu σ i u (0x800028b4#64) vminstret (0x0085a783#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, false, 4))
    Register.x15 (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))
    (0x83#8) (0xa7#8) (0x85#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0085a783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x800028b4#64) (0x008#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x800028b4#64) Register.x15
        (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      vbufb b0 b1 b2 b3 hG (rX_bits_x11 _ vbufb hx11₂)
      (wX_bits_x15 _ (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- `ld a0,16(a0)` @0x800028e8 (native) — loads `a`'s fn pointer at +16 into `x10`. -/
theorem site_800028e8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbufa : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbufa)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028e8#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbufa + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (vbufa + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbufa + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbufa + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (vbufa + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vbufa + sign_extend (m := 64) (0x010#12)).toNat]? = some b0)
    (h1 : σ.mem[(vbufa + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbufa + sign_extend (m := 64) (0x010#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbufa + sign_extend (m := 64) (0x010#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vbufa + sign_extend (m := 64) (0x010#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vbufa + sign_extend (m := 64) (0x010#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vbufa + sign_extend (m := 64) (0x010#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vbufa + sign_extend (m := 64) (0x010#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028e8 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x800028e8#64)).regs.get? Register.x10 = some vbufa := by
    rw [get?_afterNextPC σ (0x800028e8#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x800028e8#64) vminstret (0x01053503#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, false, 8))
    Register.x10 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x35#8) (0x05#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_01053503 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800028e8#64) (0x010#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x800028e8#64) Register.x10 (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      vbufa b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ vbufa hx10₂)
      (wX_bits_x10 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- `ld a5,16(a1)` @0x800028ec (native) — loads `b`'s fn pointer at +16 into `x15`. -/
theorem site_800028ec
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbufb : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some vbufb)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028ec#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbufb + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (vbufb + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbufb + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbufb + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (vbufb + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vbufb + sign_extend (m := 64) (0x010#12)).toNat]? = some b0)
    (h1 : σ.mem[(vbufb + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbufb + sign_extend (m := 64) (0x010#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbufb + sign_extend (m := 64) (0x010#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vbufb + sign_extend (m := 64) (0x010#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vbufb + sign_extend (m := 64) (0x010#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vbufb + sign_extend (m := 64) (0x010#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vbufb + sign_extend (m := 64) (0x010#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028ec hmem
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x800028ec#64)).regs.get? Register.x11 = some vbufb := by
    rw [get?_afterNextPC σ (0x800028ec#64) _ (by decide) (by decide)]; exact hx11
  exact stepObs_alu σ i u (0x800028ec#64) vminstret (0x0105b783#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, false, 8))
    Register.x15 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0xb7#8) (0x05#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0105b783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800028ec#64) (0x010#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x800028ec#64) Register.x15 (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      vbufb b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x11 _ vbufb hx11₂)
      (wX_bits_x15 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
