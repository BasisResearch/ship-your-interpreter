import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.MemLoadTotal
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part09
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch02Part22
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch03Part13
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part20
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch05Part03
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch05Part17
import Vsa.Sim.DecodeTable.Batch06Part04
import Vsa.Sim.DecodeTable.Batch06Part21
import Vsa.Sim.DecodeTable.Batch06Part22
import Vsa.Sim.DecodeTable.Batch06Part23
import Vsa.Sim.DecodeTable.Batch07Part03
import Vsa.Sim.DecodeTable.Batch07Part06
import Vsa.Sim.DecodeTable.Batch07Part10
import Vsa.Sim.DecodeTable.Batch07Part11
import Vsa.Sim.DecodeTable.Batch08Part02
import Vsa.Sim.DecodeTable.Batch09Part10
import Vsa.Sim.DecodeTable.Batch09Part17
import Vsa.Sim.DecodeTable.Batch09Part18
import Vsa.Sim.DecodeTable.Batch09Part28
import Vsa.Sim.DecodeTable.Batch09Part29
import Vsa.Sim.DecodeTable.Batch11Part22
import Vsa.Sim.DecodeTable.Batch11Part25
import Vsa.Sim.DecodeTable.Batch15Part02
import Vsa.Sim.DecodeTable.Batch15Part27
import Vsa.Sim.DecodeTable.Batch16Part05
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch16Part25
import Vsa.Sim.StrlenMagic
import Vsa.Sim.Code.Strcmp

/-!
# Layer 3 — per-site observational step lemmas for `strcmp`

One `StepObs` lemma per instruction of newlib `strcmp`
(75 instructions at `[0x80006ea0, 0x80006fcc)`), following `StrlenSites.lean`
verbatim: each site = the fully-qualified `DecodeTable` decode lemma + the
`rX`/`wX` read-backs + the matching `ExecuteAlu`/`ExecuteBranch`/`ExecuteLoad`
character, assembled into the abstract `hexec` the generic `stepObs_*` wrapper
wants, and closed by one `stepObs_*` application. Branch sites are split
taken/nottaken.

Register aliases: t0=x5, t1=x6, t2=x7, a0=x10, a1=x11, a2=x12, a3=x13,
a4=x14, a5=x15.

Loads: every `ld` here is the word-wise NUL-scanning load whose trailing bytes
may be unmapped, so all `ld` sites use the TOTAL 8-byte chain
(`vmem_read_data_eight_total`), value `sign_extend (ldBytesT σ₂ addr)`. The two
`lbu` byte-loop sites read mapped bytes, so they use the width-1 `some`-hyp chain
(`vmem_read_data_one`).

Segment map (control flow):
* entry / alignment test (`0xea0…eac`): `or a4,a0,a1`; `li t2,-1`;
  `andi a4,a4,7`; `bnez a4,0xf84` (misaligned → byte loop)
* mask setup (`0xeb0…eb4`): `auipc a5,0x14`; `ld a5,-560(a5)` (load `mask`
  = 0x7f7f7f7f7f7f7f7f)
* word loop, 3 unrolled iterations each `ld a2,k(a0); ld a3,k(a1)`, magic
  `t0 = ((a2&a5)+a5) | a2 | a5`, `bne t0,t2` (zero byte? → tail), `bne a2,a3`
  (differ? → lane compare):
  * iter0 (`0xeb8…ed4`), iter1 (`0xed8…ef4`), iter2 (`0xef8…f10`)
  * `0xf14…f1c`: `addi a0,a0,24`; `addi a1,a1,24`; `beq a2,a3,0xeb8` (loop back)
* lane compare (`0xf20…f80`): shift-left probes to find differing byte, then
  `srli …,0x30`; `sub a0,a4,a5`; `zext.b a1,a0`; `bnez a1`; `ret` (twice), and
  the `zext.b a4;zext.b a5;sub;ret` finisher
* byte loop (`0xf84…fa0`): `lbu a2,0(a0); lbu a3,0(a1)`; `addi a0,a0,1;
  addi a1,a1,1`; `bne a2,a3` (differ→exit); `bnez a2,0xf84` (loop); `sub a0,a2,a3; ret`
* word-loop exit blocks (`0xfa4…fc8`): three `addi …,8/16; bne a2,a3,0xf84`
  fall-throughs and `li a0,0; ret` equal-return tails
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (StrcmpLoaded)
open Vsa.Sim.DecodeTable

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Shared execute helpers

Concrete per-mnemonic execute helpers (mirroring `StrlenSites.lean`): each takes
the register `some`-hypotheses on `σ`, lifts them through `afterNextPC ∘
afterPrelude` via `get?_afterNextPC`, and feeds the matching `execute_*_char`.
Register combinations that recur across the three unrolled word-loop iterations
share a single helper. -/

/-- `execute (RTYPE and t0,a2,a5)` = `and x5,x12,x15`. Writes `x5 := a2 & a5`. -/
theorem exec_and_t0_a2_a5 (σ : MState) (pc : BitVec 64) (v12 v15 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x05#5, rop.AND))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x5 (v12 &&& v15)) := by
  have hx12₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_rtype_and_char (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x05#5)
    v12 v15 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x5 (v12 &&& v15))
    (rX_bits_x12 _ v12 hx12₂) (rX_bits_x15 _ v15 hx15₂) (wX_bits_x5 _ (v12 &&& v15))

/-- `execute (RTYPE or t1,a2,a5)` = `or x6,x12,x15`. Writes `x6 := a2 | a5`. -/
theorem exec_or_t1_a2_a5 (σ : MState) (pc : BitVec 64) (v12 v15 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x06#5, rop.OR))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x6 (v12 ||| v15)) := by
  have hx12₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_rtype_or_char (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x06#5)
    v12 v15 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x6 (v12 ||| v15))
    (rX_bits_x12 _ v12 hx12₂) (rX_bits_x15 _ v15 hx15₂) (wX_bits_x6 _ (v12 ||| v15))

/-- `execute (RTYPE add t0,t0,a5)` = `add x5,x5,x15`. Writes `x5 := t0 + a5`. -/
theorem exec_add_t0_t0_a5 (σ : MState) (pc : BitVec 64) (v5 v15 : BitVec 64)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x05#5, regidx.Regidx 0x05#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x5 (v5 + v15)) := by
  have hx5₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x5 = some v5 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx5
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_rtype_add_char (regidx.Regidx 0x0f#5) (regidx.Regidx 0x05#5) (regidx.Regidx 0x05#5)
    v5 v15 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x5 (v5 + v15))
    (rX_bits_x5 _ v5 hx5₂) (rX_bits_x15 _ v15 hx15₂) (wX_bits_x5 _ (v5 + v15))

/-- `execute (RTYPE or t0,t0,t1)` = `or x5,x5,x6`. Writes `x5 := t0 | t1`. -/
theorem exec_or_t0_t0_t1 (σ : MState) (pc : BitVec 64) (v5 v6 : BitVec 64)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx6 : σ.regs.get? Register.x6 = some v6) :
    (execute (instruction.RTYPE (regidx.Regidx 0x06#5, regidx.Regidx 0x05#5, regidx.Regidx 0x05#5, rop.OR))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x5 (v5 ||| v6)) := by
  have hx5₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x5 = some v5 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx5
  have hx6₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x6 = some v6 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx6
  exact execute_rtype_or_char (regidx.Regidx 0x06#5) (regidx.Regidx 0x05#5) (regidx.Regidx 0x05#5)
    v5 v6 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x5 (v5 ||| v6))
    (rX_bits_x5 _ v5 hx5₂) (rX_bits_x6 _ v6 hx6₂) (wX_bits_x5 _ (v5 ||| v6))

/-- `execute (RTYPE or a4,a0,a1)` = `or x14,x10,x11`. Writes `x14 := a0 | a1`. -/
theorem exec_or_a4_a0_a1 (σ : MState) (pc : BitVec 64) (v10 v11 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, rop.OR))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x14 (v10 ||| v11)) := by
  have hx10₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_rtype_or_char (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0e#5)
    v10 v11 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x14 (v10 ||| v11))
    (rX_bits_x10 _ v10 hx10₂) (rX_bits_x11 _ v11 hx11₂) (wX_bits_x14 _ (v10 ||| v11))

/-- `execute (ITYPE addi t2,x0,0xfff)` = `li t2,-1`. Writes `x7 := -1`. -/
theorem exec_li_t2_m1 (σ : MState) (pc : BitVec 64) :
    (execute (instruction.ITYPE (0xfff#12, regidx.Regidx 0x00#5, regidx.Regidx 0x07#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x7 ((0#64) + sign_extend (m := 64) (0xfff#12))) :=
  execute_itype_addi_char (0xfff#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x07#5) (0#64)
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x7 ((0#64) + sign_extend (m := 64) (0xfff#12)))
    (rX_bits_zero _) (wX_bits_x7 _ ((0#64) + sign_extend (m := 64) (0xfff#12)))

/-- `execute (ITYPE andi a4,a4,7)` = `andi x14,x14,7`. Writes `x14 := a4 & 7`. -/
theorem exec_andi_a4_7 (σ : MState) (pc : BitVec 64) (v14 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.ITYPE (0x007#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ANDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x14 (v14 &&& sign_extend (m := 64) (0x007#12))) := by
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_itype_andi_char (0x007#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x14 (v14 &&& sign_extend (m := 64) (0x007#12)))
    (rX_bits_x14 _ v14 hx14₂) (wX_bits_x14 _ (v14 &&& sign_extend (m := 64) (0x007#12)))

/-- `execute (UTYPE auipc a5,0x14)` = `auipc x15,0x14`. Writes `x15 := pc + sext(0x14000)`. -/
theorem exec_auipc_a5 (σ : MState) (pc : BitVec 64)
    (hpc : σ.regs.get? Register.PC = some pc) :
    (execute (instruction.UTYPE (0x00014#20, regidx.Regidx 0x0f#5, uop.AUIPC))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (pc + sign_extend (m := 64) ((0x00014#20) +++ 0x000#12))) := by
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  exact execute_utype_auipc_char (0x00014#20) (regidx.Regidx 0x0f#5) pc
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (pc + sign_extend (m := 64) ((0x00014#20) +++ 0x000#12))) hpc₂
    (wX_bits_x15 _ (pc + sign_extend (m := 64) ((0x00014#20) +++ 0x000#12)))

/-- Generic `execute (LOAD ld rd, imm(rs1))` via the TOTAL 8-byte chain. Takes the
`rs1`-read and `rd`-write run facts abstractly (write target `σ'`), so one helper
serves every `ld` site (`ld a2,k(a0)`, `ld a3,k(a1)`, `ld a5,off(a5)`). The value
written is `sign_extend (ldBytesT σ₂ (v1 + sext imm))`. -/
theorem exec_ld_total (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs1 rd : regidx)
    (v1 : BitVec 64) (σ' : SequentialState RegisterType trivialChoiceSource)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (sign_extend (m := 64)
        (ldBytesT (afterNextPC (afterPrelude σ) pc) (v1 + sign_extend (m := 64) imm)))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok () σ')
    (hlo : 0x80000000 ≤ (v1 + sign_extend (m := 64) imm).toNat)
    (hhiram : (v1 + sign_extend (m := 64) imm).toNat + 8 ≤ 0x100000000)
    (hhtif : (v1 + sign_extend (m := 64) imm).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v1 + sign_extend (m := 64) imm).toNat)
    (halign : (v1 + sign_extend (m := 64) imm).toNat % 8 = 0) :
    (execute (instruction.LOAD (imm, rs1, rd, false, 8))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  have hpriv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  have hmstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  have hseccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  have hpma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  have hcfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  have haddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  have hmprv : _get_Mstatus_MPRV initMstatus = 0#1 := by decide
  have hread := vmem_read_data_eight_total (afterNextPC (afterPrelude σ) pc)
    rs1 (sign_extend (m := 64) imm) v1 initMstatus initPmpaddr
    hpriv hmstatus hmprv hseccfg hpma hcfg haddr hbase' hrs1 hlo hhiram hhtif halign
  exact execute_load_signed_char imm rs1 rd
    8 (ldBytesT (afterNextPC (afterPrelude σ) pc) (v1 + sign_extend (m := 64) imm))
    (afterNextPC (afterPrelude σ) pc) σ'
    (by decide) hread hwr

/-- Generic `execute (SHIFTIOP slli rd, shamt(rs1))`. Value `shift_bits_left v (shamt[5:0])`,
write target `σ'` abstract. Serves the `slli a4,a2,k` / `slli a5,a3,k` lane probes. -/
theorem exec_slli_gen (σ : MState) (pc : BitVec 64) (shamt : BitVec 6) (rs1 rd : regidx)
    (v : BitVec 64) (σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (shift_bits_left v (Sail.BitVec.extractLsb shamt 5 0))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ') :
    (execute (instruction.SHIFTIOP (shamt, rs1, rd, sop.SLLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' :=
  execute_shiftiop_slli_char shamt rs1 rd v (afterNextPC (afterPrelude σ) pc) σ' hrs hwr

/-- Generic `execute (SHIFTIOP srli rd, shamt(rs1))`. Value `shift_bits_right v (shamt[5:0])`. -/
theorem exec_srli_gen (σ : MState) (pc : BitVec 64) (shamt : BitVec 6) (rs1 rd : regidx)
    (v : BitVec 64) (σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (shift_bits_right v (Sail.BitVec.extractLsb shamt 5 0))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ') :
    (execute (instruction.SHIFTIOP (shamt, rs1, rd, sop.SRLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' :=
  execute_shiftiop_srli_char shamt rs1 rd v (afterNextPC (afterPrelude σ) pc) σ' hrs hwr

/-- Generic `execute (ITYPE addi rd, imm(rs1))`. Value `v + sext imm`, target `σ'` abstract.
Serves `addi a0,a0,k` / `addi a1,a1,k`, `mv`, `li a0,0`. -/
theorem exec_addi_gen (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs1 rd : regidx)
    (v : BitVec 64) (σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (v + sign_extend (m := 64) imm)).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ') :
    (execute (instruction.ITYPE (imm, rs1, rd, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' :=
  execute_itype_addi_char imm rs1 rd v (afterNextPC (afterPrelude σ) pc) σ' hrs hwr

/-- Generic `execute (ITYPE andi rd, imm(rs1))`. Value `v &&& sext imm`, target `σ'` abstract.
Serves `zext.b …` (imm 0xff) lane extractions. -/
theorem exec_andi_gen (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs1 rd : regidx)
    (v : BitVec 64) (σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (v &&& sign_extend (m := 64) imm)).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ') :
    (execute (instruction.ITYPE (imm, rs1, rd, iop.ANDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' :=
  execute_itype_andi_char imm rs1 rd v (afterNextPC (afterPrelude σ) pc) σ' hrs hwr

/-- Generic `execute (RTYPE sub rd, rs1, rs2)`. Value `v1 - v2`, target `σ'` abstract.
Serves `sub a0,a4,a5` / `sub a0,a2,a3`. -/
theorem exec_sub_gen (σ : MState) (pc : BitVec 64) (rs2 rs1 rd : regidx)
    (v1 v2 : BitVec 64) (σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc) = .ok v2 (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (v1 - v2)).run (afterNextPC (afterPrelude σ) pc) = .ok () σ') :
    (execute (instruction.RTYPE (rs2, rs1, rd, rop.SUB))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' :=
  execute_rtype_sub_char rs2 rs1 rd v1 v2 (afterNextPC (afterPrelude σ) pc) σ' hrs1 hrs2 hwr

/-- Generic taken `bne rs1,rs2,imm`. Serves every `bne`/`bnez` site (`bnez` has
`rs2 = x0`). PC → pc + sext imm. -/
theorem exec_bne_taken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (rs1 rs2 : regidx)
    (v1 v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc) = .ok v2 (afterNextPC (afterPrelude σ) pc))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : (v1 != v2) = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BNE))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) := by
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bne_taken imm rs1 rs2 v1 v2 pc initMisa (afterNextPC (afterPrelude σ) pc)
    hrs1 hrs2 hpc₂ hmisa₂ htgt hv

/-- Generic not-taken `bne rs1,rs2,imm`. PC → pc+4. -/
theorem exec_bne_nottaken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (rs1 rs2 : regidx)
    (v1 v2 : BitVec 64)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc) = .ok v2 (afterNextPC (afterPrelude σ) pc))
    (hv : (v1 != v2) = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BNE))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) :=
  execute_btype_bne_nottaken imm rs1 rs2 v1 v2 (afterNextPC (afterPrelude σ) pc) hrs1 hrs2 hv

/-- Generic taken `beq rs1,rs2,imm`. PC → pc + sext imm. -/
theorem exec_beq_taken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (rs1 rs2 : regidx)
    (v1 v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc) = .ok v2 (afterNextPC (afterPrelude σ) pc))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : (v1 == v2) = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BEQ))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) := by
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_beq_taken imm rs1 rs2 v1 v2 pc initMisa (afterNextPC (afterPrelude σ) pc)
    hrs1 hrs2 hpc₂ hmisa₂ htgt hv

/-- Generic not-taken `beq rs1,rs2,imm`. PC → pc+4. -/
theorem exec_beq_nottaken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (rs1 rs2 : regidx)
    (v1 v2 : BitVec 64)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc) = .ok v2 (afterNextPC (afterPrelude σ) pc))
    (hv : (v1 == v2) = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BEQ))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) :=
  execute_btype_beq_nottaken imm rs1 rs2 v1 v2 (afterNextPC (afterPrelude σ) pc) hrs1 hrs2 hv

/-- Generic `execute (LOAD lbu rd, imm(rs1))` via the width-1 `some`-hyp chain.
Writes `rd := zero_extend b0v`. Serves `lbu a2,0(a0)` / `lbu a3,0(a1)`. -/
theorem exec_lbu_gen (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs1 rd : regidx)
    (v1 : BitVec 64) (b0v : BitVec 8) (σ' : SequentialState RegisterType trivialChoiceSource)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (zero_extend (m := 64) b0v)).run (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (v1 + sign_extend (m := 64) imm).toNat)
    (hhiram : (v1 + sign_extend (m := 64) imm).toNat + 1 ≤ 0x100000000)
    (hhtif : (v1 + sign_extend (m := 64) imm).toNat + 1 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v1 + sign_extend (m := 64) imm).toNat)
    (hb0 : σ.mem[(v1 + sign_extend (m := 64) imm).toNat]? = some b0v) :
    (execute (instruction.LOAD (imm, rs1, rd, true, 1))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  have hpriv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  have hmstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  have hseccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  have hpma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  have hcfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  have haddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  have hmprv : _get_Mstatus_MPRV initMstatus = 0#1 := by decide
  have hread := vmem_read_data_one (afterNextPC (afterPrelude σ) pc)
    rs1 (sign_extend (m := 64) imm) v1 b0v initMstatus initPmpaddr
    hpriv hmstatus hmprv hseccfg hpma hcfg haddr hbase' hrs1 hlo hhiram hhtif
    (by rw [mem_afterNextPC]; exact hb0)
  exact execute_load_unsigned_char imm rs1 rd 1 b0v (afterNextPC (afterPrelude σ) pc) σ'
    (by decide) hread hwr

/-- `execute (JALR ret)` = `jr x1,0` (rs1 = x1 = ra). PC → bit-0-cleared `ra`. -/
theorem exec_ret (σ : MState) (pc : BitVec 64) (vra : BitVec 64)
    (hx1 : σ.regs.get? Register.x1 = some vra) :
    (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) pc)
      = .ok vra (afterNextPC (afterPrelude σ) pc) := by
  apply rX_bits_x1
  rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx1

/-! ## Entry / alignment test (`0x80006ea0 … 0x80006eac`) -/

/-! ### Site 0x80006ea0 — `or a4,a0,a1` -/
theorem or_a4_word :
    (((0x00#8).append (0xb5#8)).append (0x67#8)).append (0x33#8) = (0x00b56733#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem or_a4_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xb5#8)).append (0x67#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006ea0** (`or a4,a0,a1`). Writes `x14 := a0 | a1`. -/
theorem site_80006ea0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ea0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (v10 ||| v11)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ea0 hmem
  exact stepObs_alu σ i u (0x80006ea0#64) vminstret (0x00b56733#32)
    (instruction.RTYPE (regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, rop.OR))
    Register.x14 (v10 ||| v11) (0x33#8) (0x67#8) (0xb5#8) (0x00#8)
    hG hpc hminstret or_a4_word or_a4_notrvc
    (decode_00b56733 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_a4_a0_a1 σ (0x80006ea0#64) v10 v11 hx10 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi
/-! ### Site 0x80006ea4 — `li t2,-1` -/
theorem li_t2_word :
    (((0xff#8).append (0xf0#8)).append (0x03#8)).append (0x93#8) = (0xfff00393#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem li_t2_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xf0#8)).append (0x03#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ea4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ea4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x7 ((0#64) + sign_extend (m := 64) (0xfff#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ea4 hmem
  exact stepObs_alu σ i u (0x80006ea4#64) vminstret (0xfff00393#32)
    (instruction.ITYPE (0xfff#12, regidx.Regidx 0x00#5, regidx.Regidx 0x07#5, iop.ADDI))
    Register.x7 ((0#64) + sign_extend (m := 64) (0xfff#12)) (0x93#8) (0x03#8) (0xf0#8) (0xff#8)
    hG hpc hminstret li_t2_word li_t2_notrvc
    (Vsa.Sim.DecodeTable.decode_fff00393 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_li_t2_m1 σ (0x80006ea4#64))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ea8 — `andi a4,a4,7` -/
theorem andi_a4_word :
    (((0x00#8).append (0x77#8)).append (0x77#8)).append (0x13#8) = (0x00777713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem andi_a4_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x77#8)).append (0x77#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ea8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ea8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (v14 &&& sign_extend (m := 64) (0x007#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ea8 hmem
  exact stepObs_alu σ i u (0x80006ea8#64) vminstret (0x00777713#32)
    (instruction.ITYPE (0x007#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ANDI))
    Register.x14 (v14 &&& sign_extend (m := 64) (0x007#12)) (0x13#8) (0x77#8) (0x77#8) (0x00#8)
    hG hpc hminstret andi_a4_word andi_a4_notrvc
    (Vsa.Sim.DecodeTable.decode_00777713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_andi_gen σ (0x80006ea8#64) (0x007#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14 _ (rX_bits_x14 _ v14
      (by rw [get?_afterNextPC σ (0x80006ea8#64) _ (by decide) (by decide)]; exact hx14)) (wX_bits_x14 _ (v14 &&& sign_extend (m := 64) (0x007#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006eac — `bnez a4,0x80006f84` (misaligned → byte loop) -/
theorem bnez_a4_word :
    (((0x0c#8).append (0x07#8)).append (0x1c#8)).append (0x63#8) = (0x0c071c63#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bnez_a4_notrvc :
    Sail.BitVec.extractLsb ((((0x0c#8).append (0x07#8)).append (0x1c#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006eac_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006eac#64 : BitVec 64))
    (hv : (v14 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x00d8#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006eac hmem
  exact stepObs_branch_taken σ i u (0x80006eac#64) vminstret (0x00d8#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BNE (0x0c071c63#32)
    (0x63#8) (0x1c#8) (0x07#8) (0x0c#8)
    hG hpc hminstret bnez_a4_word bnez_a4_notrvc
    (Vsa.Sim.DecodeTable.decode_0c071c63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006eac#64) (0x00d8#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) v14 (0#64) hG hpc
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006eac#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_zero _)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006eac_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006eac#64 : BitVec 64))
    (hv : (v14 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006eac hmem
  exact stepObs_branch_nottaken σ i u (0x80006eac#64) vminstret (0x00d8#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BNE (0x0c071c63#32)
    (0x63#8) (0x1c#8) (0x07#8) (0x0c#8)
    hG hpc hminstret bnez_a4_word bnez_a4_notrvc
    (Vsa.Sim.DecodeTable.decode_0c071c63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006eac#64) (0x00d8#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) v14 (0#64)
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006eac#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006eb0 — `auipc a5,0x14` -/
theorem auipc_a5_word :
    (((0x00#8).append (0x01#8)).append (0x47#8)).append (0x97#8) = (0x00014797#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem auipc_a5_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x01#8)).append (0x47#8)).append (0x97#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006eb0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006eb0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 ((0x80006eb0#64) + sign_extend (m := 64) ((0x00014#20) +++ 0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006eb0 hmem
  exact stepObs_alu σ i u (0x80006eb0#64) vminstret (0x00014797#32)
    (instruction.UTYPE (0x00014#20, regidx.Regidx 0x0f#5, uop.AUIPC))
    Register.x15 ((0x80006eb0#64) + sign_extend (m := 64) ((0x00014#20) +++ 0x000#12)) (0x97#8) (0x47#8) (0x01#8) (0x00#8)
    hG hpc hminstret auipc_a5_word auipc_a5_notrvc
    (Vsa.Sim.DecodeTable.decode_00014797 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_auipc_a5 σ (0x80006eb0#64) hpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006eb4 — `ld a5,-560(a5)` (load mask) (TOTAL 8-byte load) -/
theorem ld_mask_word :
    (((0xdd#8).append (0x07#8)).append (0xb7#8)).append (0x83#8) = (0xdd07b783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ld_mask_notrvc :
    Sail.BitVec.extractLsb ((((0xdd#8).append (0x07#8)).append (0xb7#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006eb4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006eb4#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v15 + sign_extend (m := 64) (0xdd0#12)).toNat)
    (hhiram : (v15 + sign_extend (m := 64) (0xdd0#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v15 + sign_extend (m := 64) (0xdd0#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v15 + sign_extend (m := 64) (0xdd0#12)).toNat)
    (halign : (v15 + sign_extend (m := 64) (0xdd0#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006eb4#64)) (v15 + sign_extend (m := 64) (0xdd0#12))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006eb4 hmem
  exact stepObs_alu σ i u (0x80006eb4#64) vminstret (0xdd07b783#32)
    (instruction.LOAD (0xdd0#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, false, 8))
    Register.x15
    (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006eb4#64)) (v15 + sign_extend (m := 64) (0xdd0#12))))
    (0x83#8) (0xb7#8) (0x07#8) (0xdd#8)
    hG hpc hminstret ld_mask_word ld_mask_notrvc
    (Vsa.Sim.DecodeTable.decode_dd07b783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_total σ (0x80006eb4#64) (0xdd0#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15 _ hG
      (rX_bits_x15 _ v15
      (by rw [get?_afterNextPC σ (0x80006eb4#64) _ (by decide) (by decide)]; exact hx15))
      (wX_bits_x15 _ (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006eb4#64)) (v15 + sign_extend (m := 64) (0xdd0#12))))) hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006eb8 — `ld a2,0(a0)` (TOTAL 8-byte load) -/
theorem ld_a2_i0_word :
    (((0x00#8).append (0x05#8)).append (0x36#8)).append (0x03#8) = (0x00053603#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ld_a2_i0_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x36#8)).append (0x03#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006eb8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006eb8#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12
          (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006eb8#64)) (v10 + sign_extend (m := 64) (0x000#12))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006eb8 hmem
  exact stepObs_alu σ i u (0x80006eb8#64) vminstret (0x00053603#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0c#5, false, 8))
    Register.x12
    (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006eb8#64)) (v10 + sign_extend (m := 64) (0x000#12))))
    (0x03#8) (0x36#8) (0x05#8) (0x00#8)
    hG hpc hminstret ld_a2_i0_word ld_a2_i0_notrvc
    (Vsa.Sim.DecodeTable.decode_00053603 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_total σ (0x80006eb8#64) (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0c#5) v10 _ hG
      (rX_bits_x10 _ v10
      (by rw [get?_afterNextPC σ (0x80006eb8#64) _ (by decide) (by decide)]; exact hx10))
      (wX_bits_x12 _ (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006eb8#64)) (v10 + sign_extend (m := 64) (0x000#12))))) hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ebc — `ld a3,0(a1)` (TOTAL 8-byte load) -/
theorem ld_a3_i0_word :
    (((0x00#8).append (0x05#8)).append (0xb6#8)).append (0x83#8) = (0x0005b683#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ld_a3_i0_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0xb6#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ebc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ebc#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (v11 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13
          (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006ebc#64)) (v11 + sign_extend (m := 64) (0x000#12))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ebc hmem
  exact stepObs_alu σ i u (0x80006ebc#64) vminstret (0x0005b683#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0d#5, false, 8))
    Register.x13
    (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006ebc#64)) (v11 + sign_extend (m := 64) (0x000#12))))
    (0x83#8) (0xb6#8) (0x05#8) (0x00#8)
    hG hpc hminstret ld_a3_i0_word ld_a3_i0_notrvc
    (Vsa.Sim.DecodeTable.decode_0005b683 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_total σ (0x80006ebc#64) (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0d#5) v11 _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006ebc#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x13 _ (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006ebc#64)) (v11 + sign_extend (m := 64) (0x000#12))))) hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ec0 — `and t0,a2,a5` = `and x5,x12,x15` -/
theorem and_t0_80006ec0_word :
    (((0x00#8).append (0xf6#8)).append (0x72#8)).append (0xb3#8) = (0x00f672b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem and_t0_80006ec0_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf6#8)).append (0x72#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ec0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ec0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x5 (v12 &&& v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ec0 hmem
  exact stepObs_alu σ i u (0x80006ec0#64) vminstret (0x00f672b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x05#5, rop.AND))
    Register.x5 (v12 &&& v15) (0xb3#8) (0x72#8) (0xf6#8) (0x00#8)
    hG hpc hminstret and_t0_80006ec0_word and_t0_80006ec0_notrvc
    (Vsa.Sim.DecodeTable.decode_00f672b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_and_t0_a2_a5 σ (0x80006ec0#64) v12 v15 hx12 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ec4 — `or t1,a2,a5` = `or x6,x12,x15` -/
theorem or_t1_80006ec4_word :
    (((0x00#8).append (0xf6#8)).append (0x63#8)).append (0x33#8) = (0x00f66333#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem or_t1_80006ec4_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf6#8)).append (0x63#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ec4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ec4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x6 (v12 ||| v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ec4 hmem
  exact stepObs_alu σ i u (0x80006ec4#64) vminstret (0x00f66333#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x06#5, rop.OR))
    Register.x6 (v12 ||| v15) (0x33#8) (0x63#8) (0xf6#8) (0x00#8)
    hG hpc hminstret or_t1_80006ec4_word or_t1_80006ec4_notrvc
    (Vsa.Sim.DecodeTable.decode_00f66333 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_t1_a2_a5 σ (0x80006ec4#64) v12 v15 hx12 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ec8 — `add t0,t0,a5` = `add x5,x5,x15` -/
theorem add_t0_80006ec8_word :
    (((0x00#8).append (0xf2#8)).append (0x82#8)).append (0xb3#8) = (0x00f282b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem add_t0_80006ec8_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf2#8)).append (0x82#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ec8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v5 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ec8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x5 (v5 + v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ec8 hmem
  exact stepObs_alu σ i u (0x80006ec8#64) vminstret (0x00f282b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x05#5, regidx.Regidx 0x05#5, rop.ADD))
    Register.x5 (v5 + v15) (0xb3#8) (0x82#8) (0xf2#8) (0x00#8)
    hG hpc hminstret add_t0_80006ec8_word add_t0_80006ec8_notrvc
    (Vsa.Sim.DecodeTable.decode_00f282b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_t0_t0_a5 σ (0x80006ec8#64) v5 v15 hx5 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ecc — `or t0,t0,t1` = `or x5,x5,x6` -/
theorem or_t0_80006ecc_word :
    (((0x00#8).append (0x62#8)).append (0xe2#8)).append (0xb3#8) = (0x0062e2b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem or_t0_80006ecc_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x62#8)).append (0xe2#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ecc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v5 v6 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx6 : σ.regs.get? Register.x6 = some v6)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ecc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x5 (v5 ||| v6)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ecc hmem
  exact stepObs_alu σ i u (0x80006ecc#64) vminstret (0x0062e2b3#32)
    (instruction.RTYPE (regidx.Regidx 0x06#5, regidx.Regidx 0x05#5, regidx.Regidx 0x05#5, rop.OR))
    Register.x5 (v5 ||| v6) (0xb3#8) (0xe2#8) (0x62#8) (0x00#8)
    hG hpc hminstret or_t0_80006ecc_word or_t0_80006ecc_notrvc
    (Vsa.Sim.DecodeTable.decode_0062e2b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_t0_t0_t1 σ (0x80006ecc#64) v5 v6 hx5 hx6)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ed0 — `bne t0,t2,0x80006fac` (zero byte → exit0) -/
theorem bne_t0t2_i0_word :
    (((0x0c#8).append (0x72#8)).append (0x9e#8)).append (0x63#8) = (0x0c729e63#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bne_t0t2_i0_notrvc :
    Sail.BitVec.extractLsb ((((0x0c#8).append (0x72#8)).append (0x9e#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ed0_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v5 v7 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx7 : σ.regs.get? Register.x7 = some v7)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ed0#64 : BitVec 64))
    (hv : (v5 != v7) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x00dc#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ed0 hmem
  exact stepObs_branch_taken σ i u (0x80006ed0#64) vminstret (0x00dc#13)
    (regidx.Regidx 0x05#5) (regidx.Regidx 0x07#5) bop.BNE (0x0c729e63#32)
    (0x63#8) (0x9e#8) (0x72#8) (0x0c#8)
    hG hpc hminstret bne_t0t2_i0_word bne_t0t2_i0_notrvc
    (Vsa.Sim.DecodeTable.decode_0c729e63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006ed0#64) (0x00dc#13) (regidx.Regidx 0x05#5) (regidx.Regidx 0x07#5) v5 v7 hG hpc
      (rX_bits_x5 _ v5
        (by rw [get?_afterNextPC σ (0x80006ed0#64) _ (by decide) (by decide)]; exact hx5))
      (rX_bits_x7 _ v7
        (by rw [get?_afterNextPC σ (0x80006ed0#64) _ (by decide) (by decide)]; exact hx7))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006ed0_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v5 v7 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx7 : σ.regs.get? Register.x7 = some v7)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ed0#64 : BitVec 64))
    (hv : (v5 != v7) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ed0 hmem
  exact stepObs_branch_nottaken σ i u (0x80006ed0#64) vminstret (0x00dc#13)
    (regidx.Regidx 0x05#5) (regidx.Regidx 0x07#5) bop.BNE (0x0c729e63#32)
    (0x63#8) (0x9e#8) (0x72#8) (0x0c#8)
    hG hpc hminstret bne_t0t2_i0_word bne_t0t2_i0_notrvc
    (Vsa.Sim.DecodeTable.decode_0c729e63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006ed0#64) (0x00dc#13) (regidx.Regidx 0x05#5) (regidx.Regidx 0x07#5) v5 v7
      (rX_bits_x5 _ v5
        (by rw [get?_afterNextPC σ (0x80006ed0#64) _ (by decide) (by decide)]; exact hx5))
      (rX_bits_x7 _ v7
        (by rw [get?_afterNextPC σ (0x80006ed0#64) _ (by decide) (by decide)]; exact hx7))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ed4 — `bne a2,a3,0x80006f20` (differ → lane compare) -/
theorem bne_a2a3_i0_word :
    (((0x04#8).append (0xd6#8)).append (0x16#8)).append (0x63#8) = (0x04d61663#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bne_a2a3_i0_notrvc :
    Sail.BitVec.extractLsb ((((0x04#8).append (0xd6#8)).append (0x16#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ed4_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ed4#64 : BitVec 64))
    (hv : (v12 != v13) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x004c#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ed4 hmem
  exact stepObs_branch_taken σ i u (0x80006ed4#64) vminstret (0x004c#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) bop.BNE (0x04d61663#32)
    (0x63#8) (0x16#8) (0xd6#8) (0x04#8)
    hG hpc hminstret bne_a2a3_i0_word bne_a2a3_i0_notrvc
    (Vsa.Sim.DecodeTable.decode_04d61663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006ed4#64) (0x004c#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) v12 v13 hG hpc
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006ed4#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006ed4#64) _ (by decide) (by decide)]; exact hx13))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006ed4_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ed4#64 : BitVec 64))
    (hv : (v12 != v13) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ed4 hmem
  exact stepObs_branch_nottaken σ i u (0x80006ed4#64) vminstret (0x004c#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) bop.BNE (0x04d61663#32)
    (0x63#8) (0x16#8) (0xd6#8) (0x04#8)
    hG hpc hminstret bne_a2a3_i0_word bne_a2a3_i0_notrvc
    (Vsa.Sim.DecodeTable.decode_04d61663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006ed4#64) (0x004c#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) v12 v13
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006ed4#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006ed4#64) _ (by decide) (by decide)]; exact hx13))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ed8 — `ld a2,8(a0)` (TOTAL 8-byte load) -/
theorem ld_a2_i1_word :
    (((0x00#8).append (0x85#8)).append (0x36#8)).append (0x03#8) = (0x00853603#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ld_a2_i1_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x85#8)).append (0x36#8)).append (0x03#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ed8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ed8#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12
          (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006ed8#64)) (v10 + sign_extend (m := 64) (0x008#12))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ed8 hmem
  exact stepObs_alu σ i u (0x80006ed8#64) vminstret (0x00853603#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0c#5, false, 8))
    Register.x12
    (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006ed8#64)) (v10 + sign_extend (m := 64) (0x008#12))))
    (0x03#8) (0x36#8) (0x85#8) (0x00#8)
    hG hpc hminstret ld_a2_i1_word ld_a2_i1_notrvc
    (Vsa.Sim.DecodeTable.decode_00853603 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_total σ (0x80006ed8#64) (0x008#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0c#5) v10 _ hG
      (rX_bits_x10 _ v10
      (by rw [get?_afterNextPC σ (0x80006ed8#64) _ (by decide) (by decide)]; exact hx10))
      (wX_bits_x12 _ (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006ed8#64)) (v10 + sign_extend (m := 64) (0x008#12))))) hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006edc — `ld a3,8(a1)` (TOTAL 8-byte load) -/
theorem ld_a3_i1_word :
    (((0x00#8).append (0x85#8)).append (0xb6#8)).append (0x83#8) = (0x0085b683#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ld_a3_i1_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x85#8)).append (0xb6#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006edc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006edc#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (v11 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13
          (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006edc#64)) (v11 + sign_extend (m := 64) (0x008#12))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006edc hmem
  exact stepObs_alu σ i u (0x80006edc#64) vminstret (0x0085b683#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0d#5, false, 8))
    Register.x13
    (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006edc#64)) (v11 + sign_extend (m := 64) (0x008#12))))
    (0x83#8) (0xb6#8) (0x85#8) (0x00#8)
    hG hpc hminstret ld_a3_i1_word ld_a3_i1_notrvc
    (Vsa.Sim.DecodeTable.decode_0085b683 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_total σ (0x80006edc#64) (0x008#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0d#5) v11 _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006edc#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x13 _ (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006edc#64)) (v11 + sign_extend (m := 64) (0x008#12))))) hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ee0 — `and t0,a2,a5` = `and x5,x12,x15` -/
theorem and_t0_80006ee0_word :
    (((0x00#8).append (0xf6#8)).append (0x72#8)).append (0xb3#8) = (0x00f672b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem and_t0_80006ee0_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf6#8)).append (0x72#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ee0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ee0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x5 (v12 &&& v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ee0 hmem
  exact stepObs_alu σ i u (0x80006ee0#64) vminstret (0x00f672b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x05#5, rop.AND))
    Register.x5 (v12 &&& v15) (0xb3#8) (0x72#8) (0xf6#8) (0x00#8)
    hG hpc hminstret and_t0_80006ee0_word and_t0_80006ee0_notrvc
    (Vsa.Sim.DecodeTable.decode_00f672b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_and_t0_a2_a5 σ (0x80006ee0#64) v12 v15 hx12 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ee4 — `or t1,a2,a5` = `or x6,x12,x15` -/
theorem or_t1_80006ee4_word :
    (((0x00#8).append (0xf6#8)).append (0x63#8)).append (0x33#8) = (0x00f66333#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem or_t1_80006ee4_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf6#8)).append (0x63#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ee4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ee4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x6 (v12 ||| v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ee4 hmem
  exact stepObs_alu σ i u (0x80006ee4#64) vminstret (0x00f66333#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x06#5, rop.OR))
    Register.x6 (v12 ||| v15) (0x33#8) (0x63#8) (0xf6#8) (0x00#8)
    hG hpc hminstret or_t1_80006ee4_word or_t1_80006ee4_notrvc
    (Vsa.Sim.DecodeTable.decode_00f66333 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_t1_a2_a5 σ (0x80006ee4#64) v12 v15 hx12 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ee8 — `add t0,t0,a5` = `add x5,x5,x15` -/
theorem add_t0_80006ee8_word :
    (((0x00#8).append (0xf2#8)).append (0x82#8)).append (0xb3#8) = (0x00f282b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem add_t0_80006ee8_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf2#8)).append (0x82#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ee8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v5 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ee8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x5 (v5 + v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ee8 hmem
  exact stepObs_alu σ i u (0x80006ee8#64) vminstret (0x00f282b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x05#5, regidx.Regidx 0x05#5, rop.ADD))
    Register.x5 (v5 + v15) (0xb3#8) (0x82#8) (0xf2#8) (0x00#8)
    hG hpc hminstret add_t0_80006ee8_word add_t0_80006ee8_notrvc
    (Vsa.Sim.DecodeTable.decode_00f282b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_t0_t0_a5 σ (0x80006ee8#64) v5 v15 hx5 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006eec — `or t0,t0,t1` = `or x5,x5,x6` -/
theorem or_t0_80006eec_word :
    (((0x00#8).append (0x62#8)).append (0xe2#8)).append (0xb3#8) = (0x0062e2b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem or_t0_80006eec_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x62#8)).append (0xe2#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006eec
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v5 v6 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx6 : σ.regs.get? Register.x6 = some v6)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006eec#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x5 (v5 ||| v6)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006eec hmem
  exact stepObs_alu σ i u (0x80006eec#64) vminstret (0x0062e2b3#32)
    (instruction.RTYPE (regidx.Regidx 0x06#5, regidx.Regidx 0x05#5, regidx.Regidx 0x05#5, rop.OR))
    Register.x5 (v5 ||| v6) (0xb3#8) (0xe2#8) (0x62#8) (0x00#8)
    hG hpc hminstret or_t0_80006eec_word or_t0_80006eec_notrvc
    (Vsa.Sim.DecodeTable.decode_0062e2b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_t0_t0_t1 σ (0x80006eec#64) v5 v6 hx5 hx6)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ef0 — `bne t0,t2,0x80006fa4` (zero byte → exit1) -/
theorem bne_t0t2_i1_word :
    (((0x0a#8).append (0x72#8)).append (0x9a#8)).append (0x63#8) = (0x0a729a63#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bne_t0t2_i1_notrvc :
    Sail.BitVec.extractLsb ((((0x0a#8).append (0x72#8)).append (0x9a#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ef0_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v5 v7 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx7 : σ.regs.get? Register.x7 = some v7)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ef0#64 : BitVec 64))
    (hv : (v5 != v7) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x00b4#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ef0 hmem
  exact stepObs_branch_taken σ i u (0x80006ef0#64) vminstret (0x00b4#13)
    (regidx.Regidx 0x05#5) (regidx.Regidx 0x07#5) bop.BNE (0x0a729a63#32)
    (0x63#8) (0x9a#8) (0x72#8) (0x0a#8)
    hG hpc hminstret bne_t0t2_i1_word bne_t0t2_i1_notrvc
    (Vsa.Sim.DecodeTable.decode_0a729a63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006ef0#64) (0x00b4#13) (regidx.Regidx 0x05#5) (regidx.Regidx 0x07#5) v5 v7 hG hpc
      (rX_bits_x5 _ v5
        (by rw [get?_afterNextPC σ (0x80006ef0#64) _ (by decide) (by decide)]; exact hx5))
      (rX_bits_x7 _ v7
        (by rw [get?_afterNextPC σ (0x80006ef0#64) _ (by decide) (by decide)]; exact hx7))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006ef0_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v5 v7 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx7 : σ.regs.get? Register.x7 = some v7)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ef0#64 : BitVec 64))
    (hv : (v5 != v7) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ef0 hmem
  exact stepObs_branch_nottaken σ i u (0x80006ef0#64) vminstret (0x00b4#13)
    (regidx.Regidx 0x05#5) (regidx.Regidx 0x07#5) bop.BNE (0x0a729a63#32)
    (0x63#8) (0x9a#8) (0x72#8) (0x0a#8)
    hG hpc hminstret bne_t0t2_i1_word bne_t0t2_i1_notrvc
    (Vsa.Sim.DecodeTable.decode_0a729a63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006ef0#64) (0x00b4#13) (regidx.Regidx 0x05#5) (regidx.Regidx 0x07#5) v5 v7
      (rX_bits_x5 _ v5
        (by rw [get?_afterNextPC σ (0x80006ef0#64) _ (by decide) (by decide)]; exact hx5))
      (rX_bits_x7 _ v7
        (by rw [get?_afterNextPC σ (0x80006ef0#64) _ (by decide) (by decide)]; exact hx7))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ef4 — `bne a2,a3,0x80006f20` (differ → lane compare) -/
theorem bne_a2a3_i1_word :
    (((0x02#8).append (0xd6#8)).append (0x16#8)).append (0x63#8) = (0x02d61663#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bne_a2a3_i1_notrvc :
    Sail.BitVec.extractLsb ((((0x02#8).append (0xd6#8)).append (0x16#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ef4_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ef4#64 : BitVec 64))
    (hv : (v12 != v13) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x002c#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ef4 hmem
  exact stepObs_branch_taken σ i u (0x80006ef4#64) vminstret (0x002c#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) bop.BNE (0x02d61663#32)
    (0x63#8) (0x16#8) (0xd6#8) (0x02#8)
    hG hpc hminstret bne_a2a3_i1_word bne_a2a3_i1_notrvc
    (Vsa.Sim.DecodeTable.decode_02d61663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006ef4#64) (0x002c#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) v12 v13 hG hpc
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006ef4#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006ef4#64) _ (by decide) (by decide)]; exact hx13))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006ef4_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ef4#64 : BitVec 64))
    (hv : (v12 != v13) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ef4 hmem
  exact stepObs_branch_nottaken σ i u (0x80006ef4#64) vminstret (0x002c#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) bop.BNE (0x02d61663#32)
    (0x63#8) (0x16#8) (0xd6#8) (0x02#8)
    hG hpc hminstret bne_a2a3_i1_word bne_a2a3_i1_notrvc
    (Vsa.Sim.DecodeTable.decode_02d61663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006ef4#64) (0x002c#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) v12 v13
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006ef4#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006ef4#64) _ (by decide) (by decide)]; exact hx13))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ef8 — `ld a2,16(a0)` (TOTAL 8-byte load) -/
theorem ld_a2_i2_word :
    (((0x01#8).append (0x05#8)).append (0x36#8)).append (0x03#8) = (0x01053603#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ld_a2_i2_notrvc :
    Sail.BitVec.extractLsb ((((0x01#8).append (0x05#8)).append (0x36#8)).append (0x03#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ef8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006ef8#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12
          (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006ef8#64)) (v10 + sign_extend (m := 64) (0x010#12))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006ef8 hmem
  exact stepObs_alu σ i u (0x80006ef8#64) vminstret (0x01053603#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0c#5, false, 8))
    Register.x12
    (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006ef8#64)) (v10 + sign_extend (m := 64) (0x010#12))))
    (0x03#8) (0x36#8) (0x05#8) (0x01#8)
    hG hpc hminstret ld_a2_i2_word ld_a2_i2_notrvc
    (Vsa.Sim.DecodeTable.decode_01053603 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_total σ (0x80006ef8#64) (0x010#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0c#5) v10 _ hG
      (rX_bits_x10 _ v10
      (by rw [get?_afterNextPC σ (0x80006ef8#64) _ (by decide) (by decide)]; exact hx10))
      (wX_bits_x12 _ (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006ef8#64)) (v10 + sign_extend (m := 64) (0x010#12))))) hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006efc — `ld a3,16(a1)` (TOTAL 8-byte load) -/
theorem ld_a3_i2_word :
    (((0x01#8).append (0x05#8)).append (0xb6#8)).append (0x83#8) = (0x0105b683#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ld_a3_i2_notrvc :
    Sail.BitVec.extractLsb ((((0x01#8).append (0x05#8)).append (0xb6#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006efc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006efc#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (v11 + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13
          (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006efc#64)) (v11 + sign_extend (m := 64) (0x010#12))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006efc hmem
  exact stepObs_alu σ i u (0x80006efc#64) vminstret (0x0105b683#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0d#5, false, 8))
    Register.x13
    (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006efc#64)) (v11 + sign_extend (m := 64) (0x010#12))))
    (0x83#8) (0xb6#8) (0x05#8) (0x01#8)
    hG hpc hminstret ld_a3_i2_word ld_a3_i2_notrvc
    (Vsa.Sim.DecodeTable.decode_0105b683 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_total σ (0x80006efc#64) (0x010#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0d#5) v11 _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006efc#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x13 _ (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006efc#64)) (v11 + sign_extend (m := 64) (0x010#12))))) hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f00 — `and t0,a2,a5` = `and x5,x12,x15` -/
theorem and_t0_80006f00_word :
    (((0x00#8).append (0xf6#8)).append (0x72#8)).append (0xb3#8) = (0x00f672b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem and_t0_80006f00_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf6#8)).append (0x72#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f00
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f00#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x5 (v12 &&& v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f00 hmem
  exact stepObs_alu σ i u (0x80006f00#64) vminstret (0x00f672b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x05#5, rop.AND))
    Register.x5 (v12 &&& v15) (0xb3#8) (0x72#8) (0xf6#8) (0x00#8)
    hG hpc hminstret and_t0_80006f00_word and_t0_80006f00_notrvc
    (Vsa.Sim.DecodeTable.decode_00f672b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_and_t0_a2_a5 σ (0x80006f00#64) v12 v15 hx12 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f04 — `or t1,a2,a5` = `or x6,x12,x15` -/
theorem or_t1_80006f04_word :
    (((0x00#8).append (0xf6#8)).append (0x63#8)).append (0x33#8) = (0x00f66333#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem or_t1_80006f04_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf6#8)).append (0x63#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f04
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f04#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x6 (v12 ||| v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f04 hmem
  exact stepObs_alu σ i u (0x80006f04#64) vminstret (0x00f66333#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x06#5, rop.OR))
    Register.x6 (v12 ||| v15) (0x33#8) (0x63#8) (0xf6#8) (0x00#8)
    hG hpc hminstret or_t1_80006f04_word or_t1_80006f04_notrvc
    (Vsa.Sim.DecodeTable.decode_00f66333 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_t1_a2_a5 σ (0x80006f04#64) v12 v15 hx12 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f08 — `add t0,t0,a5` = `add x5,x5,x15` -/
theorem add_t0_80006f08_word :
    (((0x00#8).append (0xf2#8)).append (0x82#8)).append (0xb3#8) = (0x00f282b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem add_t0_80006f08_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf2#8)).append (0x82#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f08
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v5 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f08#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x5 (v5 + v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f08 hmem
  exact stepObs_alu σ i u (0x80006f08#64) vminstret (0x00f282b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x05#5, regidx.Regidx 0x05#5, rop.ADD))
    Register.x5 (v5 + v15) (0xb3#8) (0x82#8) (0xf2#8) (0x00#8)
    hG hpc hminstret add_t0_80006f08_word add_t0_80006f08_notrvc
    (Vsa.Sim.DecodeTable.decode_00f282b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_t0_t0_a5 σ (0x80006f08#64) v5 v15 hx5 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f0c — `or t0,t0,t1` = `or x5,x5,x6` -/
theorem or_t0_80006f0c_word :
    (((0x00#8).append (0x62#8)).append (0xe2#8)).append (0xb3#8) = (0x0062e2b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem or_t0_80006f0c_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x62#8)).append (0xe2#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f0c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v5 v6 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx6 : σ.regs.get? Register.x6 = some v6)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f0c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x5 (v5 ||| v6)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f0c hmem
  exact stepObs_alu σ i u (0x80006f0c#64) vminstret (0x0062e2b3#32)
    (instruction.RTYPE (regidx.Regidx 0x06#5, regidx.Regidx 0x05#5, regidx.Regidx 0x05#5, rop.OR))
    Register.x5 (v5 ||| v6) (0xb3#8) (0xe2#8) (0x62#8) (0x00#8)
    hG hpc hminstret or_t0_80006f0c_word or_t0_80006f0c_notrvc
    (Vsa.Sim.DecodeTable.decode_0062e2b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_t0_t0_t1 σ (0x80006f0c#64) v5 v6 hx5 hx6)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f10 — `bne t0,t2,0x80006fb8` (zero byte → exit2) -/
theorem bne_t0t2_i2_word :
    (((0x0a#8).append (0x72#8)).append (0x94#8)).append (0x63#8) = (0x0a729463#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bne_t0t2_i2_notrvc :
    Sail.BitVec.extractLsb ((((0x0a#8).append (0x72#8)).append (0x94#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f10_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v5 v7 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx7 : σ.regs.get? Register.x7 = some v7)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f10#64 : BitVec 64))
    (hv : (v5 != v7) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x00a8#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f10 hmem
  exact stepObs_branch_taken σ i u (0x80006f10#64) vminstret (0x00a8#13)
    (regidx.Regidx 0x05#5) (regidx.Regidx 0x07#5) bop.BNE (0x0a729463#32)
    (0x63#8) (0x94#8) (0x72#8) (0x0a#8)
    hG hpc hminstret bne_t0t2_i2_word bne_t0t2_i2_notrvc
    (Vsa.Sim.DecodeTable.decode_0a729463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006f10#64) (0x00a8#13) (regidx.Regidx 0x05#5) (regidx.Regidx 0x07#5) v5 v7 hG hpc
      (rX_bits_x5 _ v5
        (by rw [get?_afterNextPC σ (0x80006f10#64) _ (by decide) (by decide)]; exact hx5))
      (rX_bits_x7 _ v7
        (by rw [get?_afterNextPC σ (0x80006f10#64) _ (by decide) (by decide)]; exact hx7))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006f10_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v5 v7 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v5)
    (hx7 : σ.regs.get? Register.x7 = some v7)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f10#64 : BitVec 64))
    (hv : (v5 != v7) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f10 hmem
  exact stepObs_branch_nottaken σ i u (0x80006f10#64) vminstret (0x00a8#13)
    (regidx.Regidx 0x05#5) (regidx.Regidx 0x07#5) bop.BNE (0x0a729463#32)
    (0x63#8) (0x94#8) (0x72#8) (0x0a#8)
    hG hpc hminstret bne_t0t2_i2_word bne_t0t2_i2_notrvc
    (Vsa.Sim.DecodeTable.decode_0a729463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006f10#64) (0x00a8#13) (regidx.Regidx 0x05#5) (regidx.Regidx 0x07#5) v5 v7
      (rX_bits_x5 _ v5
        (by rw [get?_afterNextPC σ (0x80006f10#64) _ (by decide) (by decide)]; exact hx5))
      (rX_bits_x7 _ v7
        (by rw [get?_afterNextPC σ (0x80006f10#64) _ (by decide) (by decide)]; exact hx7))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f14 — `addi a0,a0,24` -/
theorem addi_a0_24_word :
    (((0x01#8).append (0x85#8)).append (0x05#8)).append (0x13#8) = (0x01850513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem addi_a0_24_notrvc :
    Sail.BitVec.extractLsb ((((0x01#8).append (0x85#8)).append (0x05#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f14
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f14#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v10 + sign_extend (m := 64) (0x018#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f14 hmem
  exact stepObs_alu σ i u (0x80006f14#64) vminstret (0x01850513#32)
    (instruction.ITYPE (0x018#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v10 + sign_extend (m := 64) (0x018#12)) (0x13#8) (0x05#8) (0x85#8) (0x01#8)
    hG hpc hminstret addi_a0_24_word addi_a0_24_notrvc
    (Vsa.Sim.DecodeTable.decode_01850513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006f14#64) (0x018#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5) v10 _ (rX_bits_x10 _ v10
      (by rw [get?_afterNextPC σ (0x80006f14#64) _ (by decide) (by decide)]; exact hx10)) (wX_bits_x10 _ (v10 + sign_extend (m := 64) (0x018#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f18 — `addi a1,a1,24` -/
theorem addi_a1_24_word :
    (((0x01#8).append (0x85#8)).append (0x85#8)).append (0x93#8) = (0x01858593#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem addi_a1_24_notrvc :
    Sail.BitVec.extractLsb ((((0x01#8).append (0x85#8)).append (0x85#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f18
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f18#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11 (v11 + sign_extend (m := 64) (0x018#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f18 hmem
  exact stepObs_alu σ i u (0x80006f18#64) vminstret (0x01858593#32)
    (instruction.ITYPE (0x018#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v11 + sign_extend (m := 64) (0x018#12)) (0x93#8) (0x85#8) (0x85#8) (0x01#8)
    hG hpc hminstret addi_a1_24_word addi_a1_24_notrvc
    (Vsa.Sim.DecodeTable.decode_01858593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006f18#64) (0x018#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) v11 _ (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006f18#64) _ (by decide) (by decide)]; exact hx11)) (wX_bits_x11 _ (v11 + sign_extend (m := 64) (0x018#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f1c — `beq a2,a3,0x80006eb8` (loop back) -/
theorem beq_a2a3_loop_word :
    (((0xf8#8).append (0xd6#8)).append (0x0e#8)).append (0xe3#8) = (0xf8d60ee3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem beq_a2a3_loop_notrvc :
    Sail.BitVec.extractLsb ((((0xf8#8).append (0xd6#8)).append (0x0e#8)).append (0xe3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f1c_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f1c#64 : BitVec 64))
    (hv : (v12 == v13) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1f9c#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f1c hmem
  exact stepObs_branch_taken σ i u (0x80006f1c#64) vminstret (0x1f9c#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) bop.BEQ (0xf8d60ee3#32)
    (0xe3#8) (0x0e#8) (0xd6#8) (0xf8#8)
    hG hpc hminstret beq_a2a3_loop_word beq_a2a3_loop_notrvc
    (Vsa.Sim.DecodeTable.decode_f8d60ee3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_taken σ (0x80006f1c#64) (0x1f9c#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) v12 v13 hG hpc
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006f1c#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006f1c#64) _ (by decide) (by decide)]; exact hx13))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006f1c_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f1c#64 : BitVec 64))
    (hv : (v12 == v13) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f1c hmem
  exact stepObs_branch_nottaken σ i u (0x80006f1c#64) vminstret (0x1f9c#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) bop.BEQ (0xf8d60ee3#32)
    (0xe3#8) (0x0e#8) (0xd6#8) (0xf8#8)
    hG hpc hminstret beq_a2a3_loop_word beq_a2a3_loop_notrvc
    (Vsa.Sim.DecodeTable.decode_f8d60ee3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_nottaken σ (0x80006f1c#64) (0x1f9c#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) v12 v13
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006f1c#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006f1c#64) _ (by decide) (by decide)]; exact hx13))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f20 — `slli a4,a2,0x30` -/
theorem slli_a4_30_0_word :
    (((0x03#8).append (0x06#8)).append (0x17#8)).append (0x13#8) = (0x03061713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem slli_a4_30_0_notrvc :
    Sail.BitVec.extractLsb ((((0x03#8).append (0x06#8)).append (0x17#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f20
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f20#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x30#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f20 hmem
  exact stepObs_alu σ i u (0x80006f20#64) vminstret (0x03061713#32)
    (instruction.SHIFTIOP (0x30#6, regidx.Regidx 0x0c#5, regidx.Regidx 0x0e#5, sop.SLLI))
    Register.x14 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x30#6) 5 0)) (0x13#8) (0x17#8) (0x06#8) (0x03#8)
    hG hpc hminstret slli_a4_30_0_word slli_a4_30_0_notrvc
    (Vsa.Sim.DecodeTable.decode_03061713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_gen σ (0x80006f20#64) (0x30#6) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0e#5) v12 _ (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006f20#64) _ (by decide) (by decide)]; exact hx12)) (wX_bits_x14 _ (shift_bits_left v12 (Sail.BitVec.extractLsb (0x30#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f24 — `slli a5,a3,0x30` -/
theorem slli_a5_30_0_word :
    (((0x03#8).append (0x06#8)).append (0x97#8)).append (0x93#8) = (0x03069793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem slli_a5_30_0_notrvc :
    Sail.BitVec.extractLsb ((((0x03#8).append (0x06#8)).append (0x97#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f24
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f24#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (shift_bits_left v13 (Sail.BitVec.extractLsb (0x30#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f24 hmem
  exact stepObs_alu σ i u (0x80006f24#64) vminstret (0x03069793#32)
    (instruction.SHIFTIOP (0x30#6, regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, sop.SLLI))
    Register.x15 (shift_bits_left v13 (Sail.BitVec.extractLsb (0x30#6) 5 0)) (0x93#8) (0x97#8) (0x06#8) (0x03#8)
    hG hpc hminstret slli_a5_30_0_word slli_a5_30_0_notrvc
    (Vsa.Sim.DecodeTable.decode_03069793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_gen σ (0x80006f24#64) (0x30#6) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0f#5) v13 _ (rX_bits_x13 _ v13
      (by rw [get?_afterNextPC σ (0x80006f24#64) _ (by decide) (by decide)]; exact hx13)) (wX_bits_x15 _ (shift_bits_left v13 (Sail.BitVec.extractLsb (0x30#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f28 — `bne a4,a5,0x80006f5c` -/
theorem bne_a4a5_30_word :
    (((0x02#8).append (0xf7#8)).append (0x1a#8)).append (0x63#8) = (0x02f71a63#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bne_a4a5_30_notrvc :
    Sail.BitVec.extractLsb ((((0x02#8).append (0xf7#8)).append (0x1a#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f28_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f28#64 : BitVec 64))
    (hv : (v14 != v15) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0034#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f28 hmem
  exact stepObs_branch_taken σ i u (0x80006f28#64) vminstret (0x0034#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) bop.BNE (0x02f71a63#32)
    (0x63#8) (0x1a#8) (0xf7#8) (0x02#8)
    hG hpc hminstret bne_a4a5_30_word bne_a4a5_30_notrvc
    (Vsa.Sim.DecodeTable.decode_02f71a63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006f28#64) (0x0034#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) v14 v15 hG hpc
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006f28#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006f28#64) _ (by decide) (by decide)]; exact hx15))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006f28_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f28#64 : BitVec 64))
    (hv : (v14 != v15) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f28 hmem
  exact stepObs_branch_nottaken σ i u (0x80006f28#64) vminstret (0x0034#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) bop.BNE (0x02f71a63#32)
    (0x63#8) (0x1a#8) (0xf7#8) (0x02#8)
    hG hpc hminstret bne_a4a5_30_word bne_a4a5_30_notrvc
    (Vsa.Sim.DecodeTable.decode_02f71a63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006f28#64) (0x0034#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) v14 v15
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006f28#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006f28#64) _ (by decide) (by decide)]; exact hx15))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f2c — `slli a4,a2,0x20` -/
theorem slli_a4_20_word :
    (((0x02#8).append (0x06#8)).append (0x17#8)).append (0x13#8) = (0x02061713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem slli_a4_20_notrvc :
    Sail.BitVec.extractLsb ((((0x02#8).append (0x06#8)).append (0x17#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f2c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f2c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x20#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f2c hmem
  exact stepObs_alu σ i u (0x80006f2c#64) vminstret (0x02061713#32)
    (instruction.SHIFTIOP (0x20#6, regidx.Regidx 0x0c#5, regidx.Regidx 0x0e#5, sop.SLLI))
    Register.x14 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x20#6) 5 0)) (0x13#8) (0x17#8) (0x06#8) (0x02#8)
    hG hpc hminstret slli_a4_20_word slli_a4_20_notrvc
    (Vsa.Sim.DecodeTable.decode_02061713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_gen σ (0x80006f2c#64) (0x20#6) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0e#5) v12 _ (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006f2c#64) _ (by decide) (by decide)]; exact hx12)) (wX_bits_x14 _ (shift_bits_left v12 (Sail.BitVec.extractLsb (0x20#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f30 — `slli a5,a3,0x20` -/
theorem slli_a5_20_word :
    (((0x02#8).append (0x06#8)).append (0x97#8)).append (0x93#8) = (0x02069793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem slli_a5_20_notrvc :
    Sail.BitVec.extractLsb ((((0x02#8).append (0x06#8)).append (0x97#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f30
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f30#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (shift_bits_left v13 (Sail.BitVec.extractLsb (0x20#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f30 hmem
  exact stepObs_alu σ i u (0x80006f30#64) vminstret (0x02069793#32)
    (instruction.SHIFTIOP (0x20#6, regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, sop.SLLI))
    Register.x15 (shift_bits_left v13 (Sail.BitVec.extractLsb (0x20#6) 5 0)) (0x93#8) (0x97#8) (0x06#8) (0x02#8)
    hG hpc hminstret slli_a5_20_word slli_a5_20_notrvc
    (Vsa.Sim.DecodeTable.decode_02069793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_gen σ (0x80006f30#64) (0x20#6) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0f#5) v13 _ (rX_bits_x13 _ v13
      (by rw [get?_afterNextPC σ (0x80006f30#64) _ (by decide) (by decide)]; exact hx13)) (wX_bits_x15 _ (shift_bits_left v13 (Sail.BitVec.extractLsb (0x20#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f34 — `bne a4,a5,0x80006f5c` -/
theorem bne_a4a5_20_word :
    (((0x02#8).append (0xf7#8)).append (0x14#8)).append (0x63#8) = (0x02f71463#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bne_a4a5_20_notrvc :
    Sail.BitVec.extractLsb ((((0x02#8).append (0xf7#8)).append (0x14#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f34_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f34#64 : BitVec 64))
    (hv : (v14 != v15) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0028#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f34 hmem
  exact stepObs_branch_taken σ i u (0x80006f34#64) vminstret (0x0028#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) bop.BNE (0x02f71463#32)
    (0x63#8) (0x14#8) (0xf7#8) (0x02#8)
    hG hpc hminstret bne_a4a5_20_word bne_a4a5_20_notrvc
    (Vsa.Sim.DecodeTable.decode_02f71463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006f34#64) (0x0028#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) v14 v15 hG hpc
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006f34#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006f34#64) _ (by decide) (by decide)]; exact hx15))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006f34_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f34#64 : BitVec 64))
    (hv : (v14 != v15) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f34 hmem
  exact stepObs_branch_nottaken σ i u (0x80006f34#64) vminstret (0x0028#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) bop.BNE (0x02f71463#32)
    (0x63#8) (0x14#8) (0xf7#8) (0x02#8)
    hG hpc hminstret bne_a4a5_20_word bne_a4a5_20_notrvc
    (Vsa.Sim.DecodeTable.decode_02f71463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006f34#64) (0x0028#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) v14 v15
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006f34#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006f34#64) _ (by decide) (by decide)]; exact hx15))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f38 — `slli a4,a2,0x10` -/
theorem slli_a4_10_word :
    (((0x01#8).append (0x06#8)).append (0x17#8)).append (0x13#8) = (0x01061713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem slli_a4_10_notrvc :
    Sail.BitVec.extractLsb ((((0x01#8).append (0x06#8)).append (0x17#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f38
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f38#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x10#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f38 hmem
  exact stepObs_alu σ i u (0x80006f38#64) vminstret (0x01061713#32)
    (instruction.SHIFTIOP (0x10#6, regidx.Regidx 0x0c#5, regidx.Regidx 0x0e#5, sop.SLLI))
    Register.x14 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x10#6) 5 0)) (0x13#8) (0x17#8) (0x06#8) (0x01#8)
    hG hpc hminstret slli_a4_10_word slli_a4_10_notrvc
    (Vsa.Sim.DecodeTable.decode_01061713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_gen σ (0x80006f38#64) (0x10#6) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0e#5) v12 _ (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006f38#64) _ (by decide) (by decide)]; exact hx12)) (wX_bits_x14 _ (shift_bits_left v12 (Sail.BitVec.extractLsb (0x10#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f3c — `slli a5,a3,0x10` -/
theorem slli_a5_10_word :
    (((0x01#8).append (0x06#8)).append (0x97#8)).append (0x93#8) = (0x01069793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem slli_a5_10_notrvc :
    Sail.BitVec.extractLsb ((((0x01#8).append (0x06#8)).append (0x97#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f3c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f3c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (shift_bits_left v13 (Sail.BitVec.extractLsb (0x10#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f3c hmem
  exact stepObs_alu σ i u (0x80006f3c#64) vminstret (0x01069793#32)
    (instruction.SHIFTIOP (0x10#6, regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, sop.SLLI))
    Register.x15 (shift_bits_left v13 (Sail.BitVec.extractLsb (0x10#6) 5 0)) (0x93#8) (0x97#8) (0x06#8) (0x01#8)
    hG hpc hminstret slli_a5_10_word slli_a5_10_notrvc
    (Vsa.Sim.DecodeTable.decode_01069793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_gen σ (0x80006f3c#64) (0x10#6) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0f#5) v13 _ (rX_bits_x13 _ v13
      (by rw [get?_afterNextPC σ (0x80006f3c#64) _ (by decide) (by decide)]; exact hx13)) (wX_bits_x15 _ (shift_bits_left v13 (Sail.BitVec.extractLsb (0x10#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f40 — `bne a4,a5,0x80006f5c` -/
theorem bne_a4a5_10_word :
    (((0x00#8).append (0xf7#8)).append (0x1e#8)).append (0x63#8) = (0x00f71e63#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bne_a4a5_10_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf7#8)).append (0x1e#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f40_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f40#64 : BitVec 64))
    (hv : (v14 != v15) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x001c#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f40 hmem
  exact stepObs_branch_taken σ i u (0x80006f40#64) vminstret (0x001c#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) bop.BNE (0x00f71e63#32)
    (0x63#8) (0x1e#8) (0xf7#8) (0x00#8)
    hG hpc hminstret bne_a4a5_10_word bne_a4a5_10_notrvc
    (Vsa.Sim.DecodeTable.decode_00f71e63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006f40#64) (0x001c#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) v14 v15 hG hpc
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006f40#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006f40#64) _ (by decide) (by decide)]; exact hx15))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006f40_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f40#64 : BitVec 64))
    (hv : (v14 != v15) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f40 hmem
  exact stepObs_branch_nottaken σ i u (0x80006f40#64) vminstret (0x001c#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) bop.BNE (0x00f71e63#32)
    (0x63#8) (0x1e#8) (0xf7#8) (0x00#8)
    hG hpc hminstret bne_a4a5_10_word bne_a4a5_10_notrvc
    (Vsa.Sim.DecodeTable.decode_00f71e63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006f40#64) (0x001c#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) v14 v15
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006f40#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006f40#64) _ (by decide) (by decide)]; exact hx15))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f44 — `srli a4,a2,0x30` -/
theorem srli_a4_30_word :
    (((0x03#8).append (0x06#8)).append (0x57#8)).append (0x13#8) = (0x03065713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem srli_a4_30_notrvc :
    Sail.BitVec.extractLsb ((((0x03#8).append (0x06#8)).append (0x57#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f44
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f44#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (shift_bits_right v12 (Sail.BitVec.extractLsb (0x30#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f44 hmem
  exact stepObs_alu σ i u (0x80006f44#64) vminstret (0x03065713#32)
    (instruction.SHIFTIOP (0x30#6, regidx.Regidx 0x0c#5, regidx.Regidx 0x0e#5, sop.SRLI))
    Register.x14 (shift_bits_right v12 (Sail.BitVec.extractLsb (0x30#6) 5 0)) (0x13#8) (0x57#8) (0x06#8) (0x03#8)
    hG hpc hminstret srli_a4_30_word srli_a4_30_notrvc
    (Vsa.Sim.DecodeTable.decode_03065713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_srli_gen σ (0x80006f44#64) (0x30#6) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0e#5) v12 _ (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006f44#64) _ (by decide) (by decide)]; exact hx12)) (wX_bits_x14 _ (shift_bits_right v12 (Sail.BitVec.extractLsb (0x30#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f48 — `srli a5,a3,0x30` -/
theorem srli_a5_30_word :
    (((0x03#8).append (0x06#8)).append (0xd7#8)).append (0x93#8) = (0x0306d793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem srli_a5_30_notrvc :
    Sail.BitVec.extractLsb ((((0x03#8).append (0x06#8)).append (0xd7#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f48
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f48#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (shift_bits_right v13 (Sail.BitVec.extractLsb (0x30#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f48 hmem
  exact stepObs_alu σ i u (0x80006f48#64) vminstret (0x0306d793#32)
    (instruction.SHIFTIOP (0x30#6, regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, sop.SRLI))
    Register.x15 (shift_bits_right v13 (Sail.BitVec.extractLsb (0x30#6) 5 0)) (0x93#8) (0xd7#8) (0x06#8) (0x03#8)
    hG hpc hminstret srli_a5_30_word srli_a5_30_notrvc
    (Vsa.Sim.DecodeTable.decode_0306d793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_srli_gen σ (0x80006f48#64) (0x30#6) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0f#5) v13 _ (rX_bits_x13 _ v13
      (by rw [get?_afterNextPC σ (0x80006f48#64) _ (by decide) (by decide)]; exact hx13)) (wX_bits_x15 _ (shift_bits_right v13 (Sail.BitVec.extractLsb (0x30#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f4c — `sub a0,a4,a5` -/
theorem sub_a0_1_word :
    (((0x40#8).append (0xf7#8)).append (0x05#8)).append (0x33#8) = (0x40f70533#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sub_a0_1_notrvc :
    Sail.BitVec.extractLsb ((((0x40#8).append (0xf7#8)).append (0x05#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f4c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f4c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v14 - v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f4c hmem
  exact stepObs_alu σ i u (0x80006f4c#64) vminstret (0x40f70533#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x0a#5, rop.SUB))
    Register.x10 (v14 - v15) (0x33#8) (0x05#8) (0xf7#8) (0x40#8)
    hG hpc hminstret sub_a0_1_word sub_a0_1_notrvc
    (Vsa.Sim.DecodeTable.decode_40f70533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sub_gen σ (0x80006f4c#64) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0a#5) v14 v15 _ (rX_bits_x14 _ v14
      (by rw [get?_afterNextPC σ (0x80006f4c#64) _ (by decide) (by decide)]; exact hx14)) (rX_bits_x15 _ v15
      (by rw [get?_afterNextPC σ (0x80006f4c#64) _ (by decide) (by decide)]; exact hx15)) (wX_bits_x10 _ (v14 - v15)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f50 — `zext.b a1,a0` -/
theorem zextb_a1_1_word :
    (((0x0f#8).append (0xf5#8)).append (0x75#8)).append (0x93#8) = (0x0ff57593#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem zextb_a1_1_notrvc :
    Sail.BitVec.extractLsb ((((0x0f#8).append (0xf5#8)).append (0x75#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f50
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f50#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11 (v10 &&& sign_extend (m := 64) (0x0ff#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f50 hmem
  exact stepObs_alu σ i u (0x80006f50#64) vminstret (0x0ff57593#32)
    (instruction.ITYPE (0x0ff#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0b#5, iop.ANDI))
    Register.x11 (v10 &&& sign_extend (m := 64) (0x0ff#12)) (0x93#8) (0x75#8) (0xf5#8) (0x0f#8)
    hG hpc hminstret zextb_a1_1_word zextb_a1_1_notrvc
    (Vsa.Sim.DecodeTable.decode_0ff57593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_andi_gen σ (0x80006f50#64) (0x0ff#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0b#5) v10 _ (rX_bits_x10 _ v10
      (by rw [get?_afterNextPC σ (0x80006f50#64) _ (by decide) (by decide)]; exact hx10)) (wX_bits_x11 _ (v10 &&& sign_extend (m := 64) (0x0ff#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f54 — `bnez a1,0x80006f74` -/
theorem bnez_a1_1_word :
    (((0x02#8).append (0x05#8)).append (0x90#8)).append (0x63#8) = (0x02059063#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bnez_a1_1_notrvc :
    Sail.BitVec.extractLsb ((((0x02#8).append (0x05#8)).append (0x90#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f54_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f54#64 : BitVec 64))
    (hv : (v11 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0020#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f54 hmem
  exact stepObs_branch_taken σ i u (0x80006f54#64) vminstret (0x0020#13)
    (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) bop.BNE (0x02059063#32)
    (0x63#8) (0x90#8) (0x05#8) (0x02#8)
    hG hpc hminstret bnez_a1_1_word bnez_a1_1_notrvc
    (Vsa.Sim.DecodeTable.decode_02059063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006f54#64) (0x0020#13) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) v11 (0#64) hG hpc
      (rX_bits_x11 _ v11
        (by rw [get?_afterNextPC σ (0x80006f54#64) _ (by decide) (by decide)]; exact hx11))
      (rX_bits_zero _)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006f54_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f54#64 : BitVec 64))
    (hv : (v11 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f54 hmem
  exact stepObs_branch_nottaken σ i u (0x80006f54#64) vminstret (0x0020#13)
    (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) bop.BNE (0x02059063#32)
    (0x63#8) (0x90#8) (0x05#8) (0x02#8)
    hG hpc hminstret bnez_a1_1_word bnez_a1_1_notrvc
    (Vsa.Sim.DecodeTable.decode_02059063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006f54#64) (0x0020#13) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) v11 (0#64)
      (rX_bits_x11 _ v11
        (by rw [get?_afterNextPC σ (0x80006f54#64) _ (by decide) (by decide)]; exact hx11))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f58 — `ret` = `jr x1,0` -/
theorem ret_f58_word :
    (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ret_f58_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f58
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f58#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f58 hmem
  exact stepObs_jr σ i u (0x80006f58#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    ret_f58_notrvc ret_f58_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ret σ (0x80006f58#64) vra hx1) htgt hi

/-! ### Site 0x80006f5c — `srli a4,a4,0x30` -/
theorem srli_a4_30b_word :
    (((0x03#8).append (0x07#8)).append (0x57#8)).append (0x13#8) = (0x03075713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem srli_a4_30b_notrvc :
    Sail.BitVec.extractLsb ((((0x03#8).append (0x07#8)).append (0x57#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f5c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f5c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (shift_bits_right v14 (Sail.BitVec.extractLsb (0x30#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f5c hmem
  exact stepObs_alu σ i u (0x80006f5c#64) vminstret (0x03075713#32)
    (instruction.SHIFTIOP (0x30#6, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, sop.SRLI))
    Register.x14 (shift_bits_right v14 (Sail.BitVec.extractLsb (0x30#6) 5 0)) (0x13#8) (0x57#8) (0x07#8) (0x03#8)
    hG hpc hminstret srli_a4_30b_word srli_a4_30b_notrvc
    (Vsa.Sim.DecodeTable.decode_03075713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_srli_gen σ (0x80006f5c#64) (0x30#6) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14 _ (rX_bits_x14 _ v14
      (by rw [get?_afterNextPC σ (0x80006f5c#64) _ (by decide) (by decide)]; exact hx14)) (wX_bits_x14 _ (shift_bits_right v14 (Sail.BitVec.extractLsb (0x30#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f60 — `srli a5,a5,0x30` -/
theorem srli_a5_30b_word :
    (((0x03#8).append (0x07#8)).append (0xd7#8)).append (0x93#8) = (0x0307d793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem srli_a5_30b_notrvc :
    Sail.BitVec.extractLsb ((((0x03#8).append (0x07#8)).append (0xd7#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f60
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f60#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (shift_bits_right v15 (Sail.BitVec.extractLsb (0x30#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f60 hmem
  exact stepObs_alu σ i u (0x80006f60#64) vminstret (0x0307d793#32)
    (instruction.SHIFTIOP (0x30#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, sop.SRLI))
    Register.x15 (shift_bits_right v15 (Sail.BitVec.extractLsb (0x30#6) 5 0)) (0x93#8) (0xd7#8) (0x07#8) (0x03#8)
    hG hpc hminstret srli_a5_30b_word srli_a5_30b_notrvc
    (Vsa.Sim.DecodeTable.decode_0307d793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_srli_gen σ (0x80006f60#64) (0x30#6) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15 _ (rX_bits_x15 _ v15
      (by rw [get?_afterNextPC σ (0x80006f60#64) _ (by decide) (by decide)]; exact hx15)) (wX_bits_x15 _ (shift_bits_right v15 (Sail.BitVec.extractLsb (0x30#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f64 — `sub a0,a4,a5` -/
theorem sub_a0_2_word :
    (((0x40#8).append (0xf7#8)).append (0x05#8)).append (0x33#8) = (0x40f70533#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sub_a0_2_notrvc :
    Sail.BitVec.extractLsb ((((0x40#8).append (0xf7#8)).append (0x05#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f64
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f64#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v14 - v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f64 hmem
  exact stepObs_alu σ i u (0x80006f64#64) vminstret (0x40f70533#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x0a#5, rop.SUB))
    Register.x10 (v14 - v15) (0x33#8) (0x05#8) (0xf7#8) (0x40#8)
    hG hpc hminstret sub_a0_2_word sub_a0_2_notrvc
    (Vsa.Sim.DecodeTable.decode_40f70533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sub_gen σ (0x80006f64#64) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0a#5) v14 v15 _ (rX_bits_x14 _ v14
      (by rw [get?_afterNextPC σ (0x80006f64#64) _ (by decide) (by decide)]; exact hx14)) (rX_bits_x15 _ v15
      (by rw [get?_afterNextPC σ (0x80006f64#64) _ (by decide) (by decide)]; exact hx15)) (wX_bits_x10 _ (v14 - v15)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f68 — `zext.b a1,a0` -/
theorem zextb_a1_2_word :
    (((0x0f#8).append (0xf5#8)).append (0x75#8)).append (0x93#8) = (0x0ff57593#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem zextb_a1_2_notrvc :
    Sail.BitVec.extractLsb ((((0x0f#8).append (0xf5#8)).append (0x75#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f68
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f68#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11 (v10 &&& sign_extend (m := 64) (0x0ff#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f68 hmem
  exact stepObs_alu σ i u (0x80006f68#64) vminstret (0x0ff57593#32)
    (instruction.ITYPE (0x0ff#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0b#5, iop.ANDI))
    Register.x11 (v10 &&& sign_extend (m := 64) (0x0ff#12)) (0x93#8) (0x75#8) (0xf5#8) (0x0f#8)
    hG hpc hminstret zextb_a1_2_word zextb_a1_2_notrvc
    (Vsa.Sim.DecodeTable.decode_0ff57593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_andi_gen σ (0x80006f68#64) (0x0ff#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0b#5) v10 _ (rX_bits_x10 _ v10
      (by rw [get?_afterNextPC σ (0x80006f68#64) _ (by decide) (by decide)]; exact hx10)) (wX_bits_x11 _ (v10 &&& sign_extend (m := 64) (0x0ff#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f6c — `bnez a1,0x80006f74` -/
theorem bnez_a1_2_word :
    (((0x00#8).append (0x05#8)).append (0x94#8)).append (0x63#8) = (0x00059463#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bnez_a1_2_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x94#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f6c_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f6c#64 : BitVec 64))
    (hv : (v11 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0008#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f6c hmem
  exact stepObs_branch_taken σ i u (0x80006f6c#64) vminstret (0x0008#13)
    (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) bop.BNE (0x00059463#32)
    (0x63#8) (0x94#8) (0x05#8) (0x00#8)
    hG hpc hminstret bnez_a1_2_word bnez_a1_2_notrvc
    (Vsa.Sim.DecodeTable.decode_00059463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006f6c#64) (0x0008#13) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) v11 (0#64) hG hpc
      (rX_bits_x11 _ v11
        (by rw [get?_afterNextPC σ (0x80006f6c#64) _ (by decide) (by decide)]; exact hx11))
      (rX_bits_zero _)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006f6c_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f6c#64 : BitVec 64))
    (hv : (v11 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f6c hmem
  exact stepObs_branch_nottaken σ i u (0x80006f6c#64) vminstret (0x0008#13)
    (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) bop.BNE (0x00059463#32)
    (0x63#8) (0x94#8) (0x05#8) (0x00#8)
    hG hpc hminstret bnez_a1_2_word bnez_a1_2_notrvc
    (Vsa.Sim.DecodeTable.decode_00059463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006f6c#64) (0x0008#13) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) v11 (0#64)
      (rX_bits_x11 _ v11
        (by rw [get?_afterNextPC σ (0x80006f6c#64) _ (by decide) (by decide)]; exact hx11))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f70 — `ret` = `jr x1,0` -/
theorem ret_f70_word :
    (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ret_f70_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f70
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f70#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f70 hmem
  exact stepObs_jr σ i u (0x80006f70#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    ret_f70_notrvc ret_f70_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ret σ (0x80006f70#64) vra hx1) htgt hi

/-! ### Site 0x80006f74 — `zext.b a4,a4` -/
theorem zextb_a4_word :
    (((0x0f#8).append (0xf7#8)).append (0x77#8)).append (0x13#8) = (0x0ff77713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem zextb_a4_notrvc :
    Sail.BitVec.extractLsb ((((0x0f#8).append (0xf7#8)).append (0x77#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f74
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f74#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (v14 &&& sign_extend (m := 64) (0x0ff#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f74 hmem
  exact stepObs_alu σ i u (0x80006f74#64) vminstret (0x0ff77713#32)
    (instruction.ITYPE (0x0ff#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ANDI))
    Register.x14 (v14 &&& sign_extend (m := 64) (0x0ff#12)) (0x13#8) (0x77#8) (0xf7#8) (0x0f#8)
    hG hpc hminstret zextb_a4_word zextb_a4_notrvc
    (Vsa.Sim.DecodeTable.decode_0ff77713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_andi_gen σ (0x80006f74#64) (0x0ff#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14 _ (rX_bits_x14 _ v14
      (by rw [get?_afterNextPC σ (0x80006f74#64) _ (by decide) (by decide)]; exact hx14)) (wX_bits_x14 _ (v14 &&& sign_extend (m := 64) (0x0ff#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f78 — `zext.b a5,a5` -/
theorem zextb_a5_word :
    (((0x0f#8).append (0xf7#8)).append (0xf7#8)).append (0x93#8) = (0x0ff7f793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem zextb_a5_notrvc :
    Sail.BitVec.extractLsb ((((0x0f#8).append (0xf7#8)).append (0xf7#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f78
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f78#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 &&& sign_extend (m := 64) (0x0ff#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f78 hmem
  exact stepObs_alu σ i u (0x80006f78#64) vminstret (0x0ff7f793#32)
    (instruction.ITYPE (0x0ff#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ANDI))
    Register.x15 (v15 &&& sign_extend (m := 64) (0x0ff#12)) (0x93#8) (0xf7#8) (0xf7#8) (0x0f#8)
    hG hpc hminstret zextb_a5_word zextb_a5_notrvc
    (Vsa.Sim.DecodeTable.decode_0ff7f793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_andi_gen σ (0x80006f78#64) (0x0ff#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15 _ (rX_bits_x15 _ v15
      (by rw [get?_afterNextPC σ (0x80006f78#64) _ (by decide) (by decide)]; exact hx15)) (wX_bits_x15 _ (v15 &&& sign_extend (m := 64) (0x0ff#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f7c — `sub a0,a4,a5` -/
theorem sub_a0_3_word :
    (((0x40#8).append (0xf7#8)).append (0x05#8)).append (0x33#8) = (0x40f70533#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sub_a0_3_notrvc :
    Sail.BitVec.extractLsb ((((0x40#8).append (0xf7#8)).append (0x05#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f7c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f7c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v14 - v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f7c hmem
  exact stepObs_alu σ i u (0x80006f7c#64) vminstret (0x40f70533#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x0a#5, rop.SUB))
    Register.x10 (v14 - v15) (0x33#8) (0x05#8) (0xf7#8) (0x40#8)
    hG hpc hminstret sub_a0_3_word sub_a0_3_notrvc
    (Vsa.Sim.DecodeTable.decode_40f70533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sub_gen σ (0x80006f7c#64) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0a#5) v14 v15 _ (rX_bits_x14 _ v14
      (by rw [get?_afterNextPC σ (0x80006f7c#64) _ (by decide) (by decide)]; exact hx14)) (rX_bits_x15 _ v15
      (by rw [get?_afterNextPC σ (0x80006f7c#64) _ (by decide) (by decide)]; exact hx15)) (wX_bits_x10 _ (v14 - v15)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f80 — `ret` = `jr x1,0` -/
theorem ret_f80_word :
    (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ret_f80_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f80
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f80#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f80 hmem
  exact stepObs_jr σ i u (0x80006f80#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    ret_f80_notrvc ret_f80_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ret σ (0x80006f80#64) vra hx1) htgt hi

/-! ### Site 0x80006f84 — `lbu a2,0(a0)` (width-1 lbu) -/
theorem lbu_a2_word :
    (((0x00#8).append (0x05#8)).append (0x46#8)).append (0x03#8) = (0x00054603#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem lbu_a2_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x46#8)).append (0x03#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f84
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f84#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x000#12)).toNat)
    (hb0 : σ.mem[(v10 + sign_extend (m := 64) (0x000#12)).toNat]? = some b0v) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x12 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strcmp_at_80006f84 hmem
  exact stepObs_alu σ i u (0x80006f84#64) vminstret (0x00054603#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0c#5, true, 1))
    Register.x12 (zero_extend (m := 64) b0v) (0x03#8) (0x46#8) (0x05#8) (0x00#8)
    hG hpc hminstret lbu_a2_word lbu_a2_notrvc
    (Vsa.Sim.DecodeTable.decode_00054603 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_gen σ (0x80006f84#64) (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0c#5) v10 b0v _ hG
      (rX_bits_x10 _ v10
      (by rw [get?_afterNextPC σ (0x80006f84#64) _ (by decide) (by decide)]; exact hx10))
      (wX_bits_x12 _ (zero_extend (m := 64) b0v)) hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f88 — `lbu a3,0(a1)` (width-1 lbu) -/
theorem lbu_a3_word :
    (((0x00#8).append (0x05#8)).append (0xc6#8)).append (0x83#8) = (0x0005c683#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem lbu_a3_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0xc6#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f88
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f88#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x000#12)).toNat)
    (hb0 : σ.mem[(v11 + sign_extend (m := 64) (0x000#12)).toNat]? = some b0v) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strcmp_at_80006f88 hmem
  exact stepObs_alu σ i u (0x80006f88#64) vminstret (0x0005c683#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0d#5, true, 1))
    Register.x13 (zero_extend (m := 64) b0v) (0x83#8) (0xc6#8) (0x05#8) (0x00#8)
    hG hpc hminstret lbu_a3_word lbu_a3_notrvc
    (Vsa.Sim.DecodeTable.decode_0005c683 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_gen σ (0x80006f88#64) (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0d#5) v11 b0v _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006f88#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x13 _ (zero_extend (m := 64) b0v)) hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f8c — `addi a0,a0,1` -/
theorem addi_a0_1b_word :
    (((0x00#8).append (0x15#8)).append (0x05#8)).append (0x13#8) = (0x00150513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem addi_a0_1b_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x15#8)).append (0x05#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f8c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f8c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v10 + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f8c hmem
  exact stepObs_alu σ i u (0x80006f8c#64) vminstret (0x00150513#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v10 + sign_extend (m := 64) (0x001#12)) (0x13#8) (0x05#8) (0x15#8) (0x00#8)
    hG hpc hminstret addi_a0_1b_word addi_a0_1b_notrvc
    (Vsa.Sim.DecodeTable.decode_00150513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006f8c#64) (0x001#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5) v10 _ (rX_bits_x10 _ v10
      (by rw [get?_afterNextPC σ (0x80006f8c#64) _ (by decide) (by decide)]; exact hx10)) (wX_bits_x10 _ (v10 + sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f90 — `addi a1,a1,1` -/
theorem addi_a1_1b_word :
    (((0x00#8).append (0x15#8)).append (0x85#8)).append (0x93#8) = (0x00158593#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem addi_a1_1b_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x15#8)).append (0x85#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f90
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f90#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11 (v11 + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f90 hmem
  exact stepObs_alu σ i u (0x80006f90#64) vminstret (0x00158593#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v11 + sign_extend (m := 64) (0x001#12)) (0x93#8) (0x85#8) (0x15#8) (0x00#8)
    hG hpc hminstret addi_a1_1b_word addi_a1_1b_notrvc
    (Vsa.Sim.DecodeTable.decode_00158593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006f90#64) (0x001#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) v11 _ (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006f90#64) _ (by decide) (by decide)]; exact hx11)) (wX_bits_x11 _ (v11 + sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f94 — `bne a2,a3,0x80006f9c` (differ → exit) -/
theorem bne_a2a3_b_word :
    (((0x00#8).append (0xd6#8)).append (0x14#8)).append (0x63#8) = (0x00d61463#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bne_a2a3_b_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xd6#8)).append (0x14#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f94_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f94#64 : BitVec 64))
    (hv : (v12 != v13) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0008#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f94 hmem
  exact stepObs_branch_taken σ i u (0x80006f94#64) vminstret (0x0008#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) bop.BNE (0x00d61463#32)
    (0x63#8) (0x14#8) (0xd6#8) (0x00#8)
    hG hpc hminstret bne_a2a3_b_word bne_a2a3_b_notrvc
    (Vsa.Sim.DecodeTable.decode_00d61463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006f94#64) (0x0008#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) v12 v13 hG hpc
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006f94#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006f94#64) _ (by decide) (by decide)]; exact hx13))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006f94_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f94#64 : BitVec 64))
    (hv : (v12 != v13) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f94 hmem
  exact stepObs_branch_nottaken σ i u (0x80006f94#64) vminstret (0x0008#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) bop.BNE (0x00d61463#32)
    (0x63#8) (0x14#8) (0xd6#8) (0x00#8)
    hG hpc hminstret bne_a2a3_b_word bne_a2a3_b_notrvc
    (Vsa.Sim.DecodeTable.decode_00d61463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006f94#64) (0x0008#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) v12 v13
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006f94#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006f94#64) _ (by decide) (by decide)]; exact hx13))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f98 — `bnez a2,0x80006f84` (loop) -/
theorem bnez_a2_b_word :
    (((0xfe#8).append (0x06#8)).append (0x16#8)).append (0xe3#8) = (0xfe0616e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bnez_a2_b_notrvc :
    Sail.BitVec.extractLsb ((((0xfe#8).append (0x06#8)).append (0x16#8)).append (0xe3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f98_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f98#64 : BitVec 64))
    (hv : (v12 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1fec#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f98 hmem
  exact stepObs_branch_taken σ i u (0x80006f98#64) vminstret (0x1fec#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5) bop.BNE (0xfe0616e3#32)
    (0xe3#8) (0x16#8) (0x06#8) (0xfe#8)
    hG hpc hminstret bnez_a2_b_word bnez_a2_b_notrvc
    (Vsa.Sim.DecodeTable.decode_fe0616e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006f98#64) (0x1fec#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5) v12 (0#64) hG hpc
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006f98#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_zero _)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006f98_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f98#64 : BitVec 64))
    (hv : (v12 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f98 hmem
  exact stepObs_branch_nottaken σ i u (0x80006f98#64) vminstret (0x1fec#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5) bop.BNE (0xfe0616e3#32)
    (0xe3#8) (0x16#8) (0x06#8) (0xfe#8)
    hG hpc hminstret bnez_a2_b_word bnez_a2_b_notrvc
    (Vsa.Sim.DecodeTable.decode_fe0616e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006f98#64) (0x1fec#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5) v12 (0#64)
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006f98#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006f9c — `sub a0,a2,a3` -/
theorem sub_a0_b_word :
    (((0x40#8).append (0xd6#8)).append (0x05#8)).append (0x33#8) = (0x40d60533#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sub_a0_b_notrvc :
    Sail.BitVec.extractLsb ((((0x40#8).append (0xd6#8)).append (0x05#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006f9c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006f9c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v12 - v13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006f9c hmem
  exact stepObs_alu σ i u (0x80006f9c#64) vminstret (0x40d60533#32)
    (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x0a#5, rop.SUB))
    Register.x10 (v12 - v13) (0x33#8) (0x05#8) (0xd6#8) (0x40#8)
    hG hpc hminstret sub_a0_b_word sub_a0_b_notrvc
    (Vsa.Sim.DecodeTable.decode_40d60533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sub_gen σ (0x80006f9c#64) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0a#5) v12 v13 _ (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006f9c#64) _ (by decide) (by decide)]; exact hx12)) (rX_bits_x13 _ v13
      (by rw [get?_afterNextPC σ (0x80006f9c#64) _ (by decide) (by decide)]; exact hx13)) (wX_bits_x10 _ (v12 - v13)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006fa0 — `ret` = `jr x1,0` -/
theorem ret_fa0_word :
    (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ret_fa0_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006fa0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006fa0#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006fa0 hmem
  exact stepObs_jr σ i u (0x80006fa0#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    ret_fa0_notrvc ret_fa0_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ret σ (0x80006fa0#64) vra hx1) htgt hi

/-! ### Site 0x80006fa4 — `addi a0,a0,8` -/
theorem addi_a0_8x_word :
    (((0x00#8).append (0x85#8)).append (0x05#8)).append (0x13#8) = (0x00850513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem addi_a0_8x_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x85#8)).append (0x05#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006fa4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006fa4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v10 + sign_extend (m := 64) (0x008#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006fa4 hmem
  exact stepObs_alu σ i u (0x80006fa4#64) vminstret (0x00850513#32)
    (instruction.ITYPE (0x008#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v10 + sign_extend (m := 64) (0x008#12)) (0x13#8) (0x05#8) (0x85#8) (0x00#8)
    hG hpc hminstret addi_a0_8x_word addi_a0_8x_notrvc
    (Vsa.Sim.DecodeTable.decode_00850513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006fa4#64) (0x008#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5) v10 _ (rX_bits_x10 _ v10
      (by rw [get?_afterNextPC σ (0x80006fa4#64) _ (by decide) (by decide)]; exact hx10)) (wX_bits_x10 _ (v10 + sign_extend (m := 64) (0x008#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006fa8 — `addi a1,a1,8` -/
theorem addi_a1_8x_word :
    (((0x00#8).append (0x85#8)).append (0x85#8)).append (0x93#8) = (0x00858593#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem addi_a1_8x_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x85#8)).append (0x85#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006fa8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006fa8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11 (v11 + sign_extend (m := 64) (0x008#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006fa8 hmem
  exact stepObs_alu σ i u (0x80006fa8#64) vminstret (0x00858593#32)
    (instruction.ITYPE (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v11 + sign_extend (m := 64) (0x008#12)) (0x93#8) (0x85#8) (0x85#8) (0x00#8)
    hG hpc hminstret addi_a1_8x_word addi_a1_8x_notrvc
    (Vsa.Sim.DecodeTable.decode_00858593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006fa8#64) (0x008#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) v11 _ (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006fa8#64) _ (by decide) (by decide)]; exact hx11)) (wX_bits_x11 _ (v11 + sign_extend (m := 64) (0x008#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006fac — `bne a2,a3,0x80006f84` -/
theorem bne_a2a3_x0_word :
    (((0xfc#8).append (0xd6#8)).append (0x1c#8)).append (0xe3#8) = (0xfcd61ce3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bne_a2a3_x0_notrvc :
    Sail.BitVec.extractLsb ((((0xfc#8).append (0xd6#8)).append (0x1c#8)).append (0xe3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006fac_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006fac#64 : BitVec 64))
    (hv : (v12 != v13) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1fd8#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006fac hmem
  exact stepObs_branch_taken σ i u (0x80006fac#64) vminstret (0x1fd8#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) bop.BNE (0xfcd61ce3#32)
    (0xe3#8) (0x1c#8) (0xd6#8) (0xfc#8)
    hG hpc hminstret bne_a2a3_x0_word bne_a2a3_x0_notrvc
    (Vsa.Sim.DecodeTable.decode_fcd61ce3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006fac#64) (0x1fd8#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) v12 v13 hG hpc
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006fac#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006fac#64) _ (by decide) (by decide)]; exact hx13))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006fac_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006fac#64 : BitVec 64))
    (hv : (v12 != v13) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006fac hmem
  exact stepObs_branch_nottaken σ i u (0x80006fac#64) vminstret (0x1fd8#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) bop.BNE (0xfcd61ce3#32)
    (0xe3#8) (0x1c#8) (0xd6#8) (0xfc#8)
    hG hpc hminstret bne_a2a3_x0_word bne_a2a3_x0_notrvc
    (Vsa.Sim.DecodeTable.decode_fcd61ce3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006fac#64) (0x1fd8#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) v12 v13
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006fac#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006fac#64) _ (by decide) (by decide)]; exact hx13))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006fb0 — `li a0,0` -/
theorem li_a0_0a_word :
    (((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8) = (0x00000513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem li_a0_0a_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006fb0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006fb0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006fb0 hmem
  exact stepObs_alu σ i u (0x80006fb0#64) vminstret (0x00000513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x05#8) (0x00#8) (0x00#8)
    hG hpc hminstret li_a0_0a_word li_a0_0a_notrvc
    (Vsa.Sim.DecodeTable.decode_00000513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006fb0#64) (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64) _ (rX_bits_zero _) (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006fb4 — `ret` = `jr x1,0` -/
theorem ret_fb4_word :
    (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ret_fb4_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006fb4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006fb4#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006fb4 hmem
  exact stepObs_jr σ i u (0x80006fb4#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    ret_fb4_notrvc ret_fb4_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ret σ (0x80006fb4#64) vra hx1) htgt hi

/-! ### Site 0x80006fb8 — `addi a0,a0,16` -/
theorem addi_a0_16x_word :
    (((0x01#8).append (0x05#8)).append (0x05#8)).append (0x13#8) = (0x01050513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem addi_a0_16x_notrvc :
    Sail.BitVec.extractLsb ((((0x01#8).append (0x05#8)).append (0x05#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006fb8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006fb8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v10 + sign_extend (m := 64) (0x010#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006fb8 hmem
  exact stepObs_alu σ i u (0x80006fb8#64) vminstret (0x01050513#32)
    (instruction.ITYPE (0x010#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v10 + sign_extend (m := 64) (0x010#12)) (0x13#8) (0x05#8) (0x05#8) (0x01#8)
    hG hpc hminstret addi_a0_16x_word addi_a0_16x_notrvc
    (Vsa.Sim.DecodeTable.decode_01050513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006fb8#64) (0x010#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5) v10 _ (rX_bits_x10 _ v10
      (by rw [get?_afterNextPC σ (0x80006fb8#64) _ (by decide) (by decide)]; exact hx10)) (wX_bits_x10 _ (v10 + sign_extend (m := 64) (0x010#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006fbc — `addi a1,a1,16` -/
theorem addi_a1_16x_word :
    (((0x01#8).append (0x05#8)).append (0x85#8)).append (0x93#8) = (0x01058593#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem addi_a1_16x_notrvc :
    Sail.BitVec.extractLsb ((((0x01#8).append (0x05#8)).append (0x85#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006fbc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006fbc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11 (v11 + sign_extend (m := 64) (0x010#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006fbc hmem
  exact stepObs_alu σ i u (0x80006fbc#64) vminstret (0x01058593#32)
    (instruction.ITYPE (0x010#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v11 + sign_extend (m := 64) (0x010#12)) (0x93#8) (0x85#8) (0x05#8) (0x01#8)
    hG hpc hminstret addi_a1_16x_word addi_a1_16x_notrvc
    (Vsa.Sim.DecodeTable.decode_01058593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006fbc#64) (0x010#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) v11 _ (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006fbc#64) _ (by decide) (by decide)]; exact hx11)) (wX_bits_x11 _ (v11 + sign_extend (m := 64) (0x010#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006fc0 — `bne a2,a3,0x80006f84` -/
theorem bne_a2a3_x1_word :
    (((0xfc#8).append (0xd6#8)).append (0x12#8)).append (0xe3#8) = (0xfcd612e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bne_a2a3_x1_notrvc :
    Sail.BitVec.extractLsb ((((0xfc#8).append (0xd6#8)).append (0x12#8)).append (0xe3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006fc0_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006fc0#64 : BitVec 64))
    (hv : (v12 != v13) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1fc4#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006fc0 hmem
  exact stepObs_branch_taken σ i u (0x80006fc0#64) vminstret (0x1fc4#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) bop.BNE (0xfcd612e3#32)
    (0xe3#8) (0x12#8) (0xd6#8) (0xfc#8)
    hG hpc hminstret bne_a2a3_x1_word bne_a2a3_x1_notrvc
    (Vsa.Sim.DecodeTable.decode_fcd612e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006fc0#64) (0x1fc4#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) v12 v13 hG hpc
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006fc0#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006fc0#64) _ (by decide) (by decide)]; exact hx13))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006fc0_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006fc0#64 : BitVec 64))
    (hv : (v12 != v13) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006fc0 hmem
  exact stepObs_branch_nottaken σ i u (0x80006fc0#64) vminstret (0x1fc4#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) bop.BNE (0xfcd612e3#32)
    (0xe3#8) (0x12#8) (0xd6#8) (0xfc#8)
    hG hpc hminstret bne_a2a3_x1_word bne_a2a3_x1_notrvc
    (Vsa.Sim.DecodeTable.decode_fcd612e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006fc0#64) (0x1fc4#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5) v12 v13
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80006fc0#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006fc0#64) _ (by decide) (by decide)]; exact hx13))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006fc4 — `li a0,0` -/
theorem li_a0_0b_word :
    (((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8) = (0x00000513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem li_a0_0b_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006fc4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006fc4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006fc4 hmem
  exact stepObs_alu σ i u (0x80006fc4#64) vminstret (0x00000513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x05#8) (0x00#8) (0x00#8)
    hG hpc hminstret li_a0_0b_word li_a0_0b_notrvc
    (Vsa.Sim.DecodeTable.decode_00000513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006fc4#64) (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64) _ (rX_bits_zero _) (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006fc8 — `ret` = `jr x1,0` -/
theorem ret_fc8_word :
    (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ret_fc8_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006fc8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrcmpLoaded σ.mem)
    (hpcv : pc = (0x80006fc8#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcmp_at_80006fc8 hmem
  exact stepObs_jr σ i u (0x80006fc8#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    ret_fc8_notrvc ret_fc8_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ret σ (0x80006fc8#64) vra hx1) htgt hi


end Vsa.Sim
