import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.MemLoadTotal
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part27
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch02Part27
import Vsa.Sim.DecodeTable.Batch03Part02
import Vsa.Sim.DecodeTable.Batch03Part06
import Vsa.Sim.DecodeTable.Batch03Part09
import Vsa.Sim.DecodeTable.Batch03Part12
import Vsa.Sim.DecodeTable.Batch03Part13
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part17
import Vsa.Sim.DecodeTable.Batch04Part18
import Vsa.Sim.DecodeTable.Batch04Part19
import Vsa.Sim.DecodeTable.Batch04Part22
import Vsa.Sim.DecodeTable.Batch04Part23
import Vsa.Sim.DecodeTable.Batch04Part25
import Vsa.Sim.DecodeTable.Batch04Part26
import Vsa.Sim.DecodeTable.Batch04Part32
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch06Part23
import Vsa.Sim.DecodeTable.Batch06Part24
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch07Part06
import Vsa.Sim.DecodeTable.Batch07Part27
import Vsa.Sim.DecodeTable.Batch09Part09
import Vsa.Sim.DecodeTable.Batch13Part06
import Vsa.Sim.DecodeTable.Batch15Part25
import Vsa.Sim.DecodeTable.Batch16Part10
import Vsa.Sim.DecodeTable.Batch16Part15
import Vsa.Sim.DecodeTable.Batch16Part18
import Vsa.Sim.DecodeTable.Batch16Part26
import Vsa.Sim.StrlenMagic
import Vsa.Sim.Code.Strcpy

/-!
# Layer 3 — per-site observational step lemmas for `strcpy`

One `StepObs` lemma per instruction of newlib `strcpy`
(55 instructions at `[0x80006dc4, 0x80006ea0)`), following `StrlenSites.lean` /
`StrcmpSites.lean` verbatim. Branch sites are split taken/nottaken.

Register aliases: a0=x10, a1=x11, a2=x12, a3=x13, a4=x14, a5=x15, a6=x16.

Loads: the two `ld a4,0(…)` word loads use the TOTAL 8-byte chain
(`vmem_read_data_eight_total`); the byte-tail/head `lbu` loads use the width-1
`some`-hyp chain (`vmem_read_data_one`).

Stores: the aligned `sd a4,0(a2)` word store uses the width-8 `vmem_write_addr_8`
chain; the byte `sb` stores use the width-1 `vmem_write_addr_1` chain (the
`DemoStore`/`MemcpySites` recipe). Store sites plug into `stepObs_store` and carry
`σ'.mem = m'` (the described insert chain).

Segment map (control flow):
* entry / alignment test (`0xdc4…dcc`): `or a5,a0,a1`; `andi a5,a5,7`;
  `bnez a5,0xe7c` (misaligned → byte head)
* magic setup (`0xdd0…df8`): `lui a5,0x7f7f8`; `addi a5,a5,-129` (a5 = 0x7f7f7f7f);
  `ld a4,0(a1)`; `slli a3,a5,0x20`; `add a3,a3,a5` (a3 = magic64);
  magic `a6 = ((a4&a3)+a3) | a4 | a3`; `li a5,-1`; `mv a2,a0`
* word loop (`0xdfc…e20`): `bne a6,a5,0xe24` (zero byte → byte tail); else
  `addi a1,a1,8`; `sd a4,0(a2)`; `ld a4,0(a1)`; `addi a2,a2,8`; magic on new a4;
  `beq a5,a6,0xe00` (loop back)
* byte tail (`0xe24…e78`): unrolled `lbu`/`sb`/`beqz` chain copying up to 7 bytes,
  with `bnez a4,0xe98` at the end; `ret`
* byte head (`0xe7c…e94`): `mv a5,a0`; `lbu a4,0(a1)`; `addi a5,a5,1;
  addi a1,a1,1`; `sb a4,-1(a5)`; `bnez a4,0xe80` (loop); `ret`
* NUL finisher (`0xe98…e9c`): `sb zero,7(a2)`; `ret`
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (StrcpyLoaded)
open Vsa.Sim.DecodeTable

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Shared execute helpers (mirrors `StrcmpSites.lean`; re-declared here since
that file is not imported). Each lifts the register `some`-hypotheses through
`afterNextPC ∘ afterPrelude` and feeds the matching `execute_*_char`. Generic
helpers abstract the write target `σ'` to dodge the `RegisterType rd` coupling. -/

theorem exec_slli_gen (σ : MState) (pc : BitVec 64) (shamt : BitVec 6) (rs1 rd : regidx)
    (v : BitVec 64) (σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (shift_bits_left v (Sail.BitVec.extractLsb shamt 5 0))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ') :
    (execute (instruction.SHIFTIOP (shamt, rs1, rd, sop.SLLI))).run
        (afterNextPC (afterPrelude σ) pc) = .ok RETIRE_SUCCESS σ' :=
  execute_shiftiop_slli_char shamt rs1 rd v (afterNextPC (afterPrelude σ) pc) σ' hrs hwr

theorem exec_addi_gen (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs1 rd : regidx)
    (v : BitVec 64) (σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (v + sign_extend (m := 64) imm)).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ') :
    (execute (instruction.ITYPE (imm, rs1, rd, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc) = .ok RETIRE_SUCCESS σ' :=
  execute_itype_addi_char imm rs1 rd v (afterNextPC (afterPrelude σ) pc) σ' hrs hwr

theorem exec_andi_gen (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs1 rd : regidx)
    (v : BitVec 64) (σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (v &&& sign_extend (m := 64) imm)).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ') :
    (execute (instruction.ITYPE (imm, rs1, rd, iop.ANDI))).run
        (afterNextPC (afterPrelude σ) pc) = .ok RETIRE_SUCCESS σ' :=
  execute_itype_andi_char imm rs1 rd v (afterNextPC (afterPrelude σ) pc) σ' hrs hwr

/-- `execute (UTYPE lui a5,0x7f7f8)` = `lui x15,…`. Writes `x15 := sext(0x7f7f8000)`. -/
theorem exec_lui_a5 (σ : MState) (pc : BitVec 64) :
    (execute (instruction.UTYPE (0x7f7f8#20, regidx.Regidx 0x0f#5, uop.LUI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12))) :=
  execute_utype_lui_char (0x7f7f8#20) (regidx.Regidx 0x0f#5)
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12)))
    (wX_bits_x15 _ (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12)))

/-- Generic taken `bne rs1,rs2,imm`. -/
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

theorem exec_bne_nottaken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (rs1 rs2 : regidx)
    (v1 v2 : BitVec 64)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc) = .ok v2 (afterNextPC (afterPrelude σ) pc))
    (hv : (v1 != v2) = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BNE))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) :=
  execute_btype_bne_nottaken imm rs1 rs2 v1 v2 (afterNextPC (afterPrelude σ) pc) hrs1 hrs2 hv

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

theorem exec_beq_nottaken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (rs1 rs2 : regidx)
    (v1 v2 : BitVec 64)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc) = .ok v2 (afterNextPC (afterPrelude σ) pc))
    (hv : (v1 == v2) = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BEQ))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) :=
  execute_btype_beq_nottaken imm rs1 rs2 v1 v2 (afterNextPC (afterPrelude σ) pc) hrs1 hrs2 hv

theorem exec_ret (σ : MState) (pc : BitVec 64) (vra : BitVec 64)
    (hx1 : σ.regs.get? Register.x1 = some vra) :
    (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) pc)
      = .ok vra (afterNextPC (afterPrelude σ) pc) := by
  apply rX_bits_x1
  rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx1

/-- Generic total 8-byte `ld` (abstract write target `σ'`). -/
theorem exec_ld_total (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs1 rd : regidx)
    (v1 : BitVec 64) (σ' : SequentialState RegisterType trivialChoiceSource)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (sign_extend (m := 64)
        (ldBytesT (afterNextPC (afterPrelude σ) pc) (v1 + sign_extend (m := 64) imm)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (v1 + sign_extend (m := 64) imm).toNat)
    (hhiram : (v1 + sign_extend (m := 64) imm).toNat + 8 ≤ 0x100000000)
    (hhtif : (v1 + sign_extend (m := 64) imm).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v1 + sign_extend (m := 64) imm).toNat)
    (halign : (v1 + sign_extend (m := 64) imm).toNat % 8 = 0) :
    (execute (instruction.LOAD (imm, rs1, rd, false, 8))).run
        (afterNextPC (afterPrelude σ) pc) = .ok RETIRE_SUCCESS σ' := by
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
    (afterNextPC (afterPrelude σ) pc) σ' (by decide) hread hwr

/-- Generic width-1 `lbu` (abstract write target `σ'`). -/
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

/-! ### Store helpers (`DemoStore`/`MemcpySites` recipe)

`sb` = width-1 `vmem_write_addr_1`; `sd` = width-8 `vmem_write_addr_8`. Both
produce `sigma3_store σ pc m'` with `m'` the described insert chain; the site
carries `σ'.mem = m'` through `stepObs_store`. -/

/-- Store byte slice for width `w`. -/
abbrev stData (w : Nat) (vdata : BitVec 64) : BitVec (8 * w) :=
  Sail.BitVec.extractLsb vdata ((w *i 8) -i 1) 0

/-- Generic `execute (STORE sb rs2, imm(rs1))` (width 1) via `vmem_write_addr_1`.
Post memory `mem.insert (v1 + sext imm).toNat (low byte of vdata)`. -/
theorem exec_sb (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata : BitVec 64)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc) = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (hlo : 0x80000000 ≤ (v1 + sign_extend (m := 64) imm).toNat)
    (hhiram : (v1 + sign_extend (m := 64) imm).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v1 + sign_extend (m := 64) imm).toNat) :
    (execute (instruction.STORE (imm, rs2, rs1, 1))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_store σ pc
            ((afterNextPC (afterPrelude σ) pc).mem.insert
              (v1 + sign_extend (m := 64) imm).toNat (stData 1 vdata))) := by
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
  have hwrite := vmem_write_addr_1 (afterNextPC (afterPrelude σ) pc)
    (v1 + sign_extend (m := 64) imm) (stData 1 vdata) initMstatus initPmpaddr
    hpriv hmstatus (by decide) hpma hcfg haddr hbase' hlo hhiram hhiwin
  have hchar := execute_STORE_char imm rs2 rs1 1 v1 vdata (afterNextPC (afterPrelude σ) pc)
    initMstatus (0#64)
    (sigma3_store σ pc ((afterNextPC (afterPrelude σ) pc).mem.insert
      (v1 + sign_extend (m := 64) imm).toNat (stData 1 vdata)))
    (by decide) hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      show (vmem_write_addr (virtaddr.Virtaddr (v1 + sign_extend (m := 64) imm)) 1
          (stData 1 vdata) (MemoryAccessType.Store mem_payload.Data) false false false).run
          (afterNextPC (afterPrelude σ) pc)
        = .ok (.Ok true) (sigma3_store σ pc ((afterNextPC (afterPrelude σ) pc).mem.insert
            (v1 + sign_extend (m := 64) imm).toNat (stData 1 vdata)))
      exact hwrite)
  show (execute (instruction.STORE (imm, rs2, rs1, 1))).run (afterNextPC (afterPrelude σ) pc) = _
  simp only [execute]
  exact hchar

/-- The width-8 store post-memory: the eight little-endian byte inserts at
`a .. a+7` from the slice `stData 8 vdata`. -/
abbrev sdMemCpy (m : Std.ExtHashMap Nat (BitVec 8)) (a : BitVec 64) (vdata : BitVec 64) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((((((m.insert a.toNat ((stData 8 vdata).extractLsb' 0 8)).insert
      (a.toNat + 1) ((stData 8 vdata).extractLsb' 8 8)).insert
      (a.toNat + 2) ((stData 8 vdata).extractLsb' 16 8)).insert
      (a.toNat + 3) ((stData 8 vdata).extractLsb' 24 8)).insert
      (a.toNat + 4) ((stData 8 vdata).extractLsb' 32 8)).insert
      (a.toNat + 5) ((stData 8 vdata).extractLsb' 40 8)).insert
      (a.toNat + 6) ((stData 8 vdata).extractLsb' 48 8)).insert
      (a.toNat + 7) ((stData 8 vdata).extractLsb' 56 8))

/-- Generic `execute (STORE sd rs2, imm(rs1))` (width 8) via `vmem_write_addr_8`. -/
theorem exec_sd (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata : BitVec 64)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc) = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (hlo : 0x80000000 ≤ (v1 + sign_extend (m := 64) imm).toNat)
    (hhiram : (v1 + sign_extend (m := 64) imm).toNat + 8 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v1 + sign_extend (m := 64) imm).toNat)
    (halign : (v1 + sign_extend (m := 64) imm).toNat % 8 = 0) :
    (execute (instruction.STORE (imm, rs2, rs1, 8))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_store σ pc
            (sdMemCpy (afterNextPC (afterPrelude σ) pc).mem (v1 + sign_extend (m := 64) imm) vdata)) := by
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
  have hwrite := vmem_write_addr_8 (afterNextPC (afterPrelude σ) pc)
    (v1 + sign_extend (m := 64) imm) (stData 8 vdata) initMstatus initPmpaddr
    hpriv hmstatus (by decide) hpma hcfg haddr hbase' hlo hhiram hhiwin halign
  have hchar := execute_STORE_char imm rs2 rs1 8 v1 vdata (afterNextPC (afterPrelude σ) pc)
    initMstatus (0#64)
    (sigma3_store σ pc (sdMemCpy (afterNextPC (afterPrelude σ) pc).mem (v1 + sign_extend (m := 64) imm) vdata))
    (by decide) hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      show (vmem_write_addr (virtaddr.Virtaddr (v1 + sign_extend (m := 64) imm)) 8
          (stData 8 vdata) (MemoryAccessType.Store mem_payload.Data) false false false).run
          (afterNextPC (afterPrelude σ) pc)
        = .ok (.Ok true)
            (sigma3_store σ pc (sdMemCpy (afterNextPC (afterPrelude σ) pc).mem (v1 + sign_extend (m := 64) imm) vdata))
      exact hwrite)
  show (execute (instruction.STORE (imm, rs2, rs1, 8))).run (afterNextPC (afterPrelude σ) pc) = _
  simp only [execute]
  exact hchar

/-! ### Concrete RTYPE helpers for the two magic blocks (a6=x16 / a5=x15) -/

/-- Emit an `RTYPE` helper: `execute (RTYPE rs2,rs1,rd,op)` reading x{r1},x{r2}. -/
theorem exec_add_a3_a3_a5 (σ : MState) (pc : BitVec 64) (v13 v15 : BitVec 64)
    (hx13 : σ.regs.get? Register.x13 = some v13) (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0d#5, regidx.Regidx 0x0d#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x13 (v13 + v15)) := by
  have h13 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_rtype_add_char (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0d#5)
    v13 v15 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x13 (v13 + v15))
    (rX_bits_x13 _ v13 h13) (rX_bits_x15 _ v15 h15) (wX_bits_x13 _ (v13 + v15))

/-- `and a6,a4,a3` = `and x16,x14,x13`. -/
theorem exec_and_a6_a4_a3 (σ : MState) (pc : BitVec 64) (v14 v13 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x10#5, rop.AND))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x16 (v14 &&& v13)) := by
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have h13 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_rtype_and_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x10#5)
    v14 v13 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x16 (v14 &&& v13))
    (rX_bits_x14 _ v14 h14) (rX_bits_x13 _ v13 h13) (wX_bits_x16 _ (v14 &&& v13))

/-- `add a6,a6,a3` = `add x16,x16,x13`. -/
theorem exec_add_a6_a6_a3 (σ : MState) (pc : BitVec 64) (v16 v13 : BitVec 64)
    (hx16 : σ.regs.get? Register.x16 = some v16) (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x10#5, regidx.Regidx 0x10#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x16 (v16 + v13)) := by
  have h16 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x16 = some v16 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx16
  have h13 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_rtype_add_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x10#5) (regidx.Regidx 0x10#5)
    v16 v13 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x16 (v16 + v13))
    (rX_bits_x16 _ v16 h16) (rX_bits_x13 _ v13 h13) (wX_bits_x16 _ (v16 + v13))

/-- `or a6,a6,a4` = `or x16,x16,x14`. -/
theorem exec_or_a6_a6_a4 (σ : MState) (pc : BitVec 64) (v16 v14 : BitVec 64)
    (hx16 : σ.regs.get? Register.x16 = some v16) (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x10#5, regidx.Regidx 0x10#5, rop.OR))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x16 (v16 ||| v14)) := by
  have h16 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x16 = some v16 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx16
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_rtype_or_char (regidx.Regidx 0x0e#5) (regidx.Regidx 0x10#5) (regidx.Regidx 0x10#5)
    v16 v14 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x16 (v16 ||| v14))
    (rX_bits_x16 _ v16 h16) (rX_bits_x14 _ v14 h14) (wX_bits_x16 _ (v16 ||| v14))

/-- `or a6,a6,a3` = `or x16,x16,x13`. -/
theorem exec_or_a6_a6_a3 (σ : MState) (pc : BitVec 64) (v16 v13 : BitVec 64)
    (hx16 : σ.regs.get? Register.x16 = some v16) (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x10#5, regidx.Regidx 0x10#5, rop.OR))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x16 (v16 ||| v13)) := by
  have h16 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x16 = some v16 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx16
  have h13 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_rtype_or_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x10#5) (regidx.Regidx 0x10#5)
    v16 v13 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x16 (v16 ||| v13))
    (rX_bits_x16 _ v16 h16) (rX_bits_x13 _ v13 h13) (wX_bits_x16 _ (v16 ||| v13))

/-- `and a5,a4,a3` = `and x15,x14,x13`. -/
theorem exec_and_a5_a4_a3 (σ : MState) (pc : BitVec 64) (v14 v13 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, rop.AND))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v14 &&& v13)) := by
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have h13 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_rtype_and_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5)
    v14 v13 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v14 &&& v13))
    (rX_bits_x14 _ v14 h14) (rX_bits_x13 _ v13 h13) (wX_bits_x15 _ (v14 &&& v13))

/-- `add a5,a5,a3` = `add x15,x15,x13`. -/
theorem exec_add_a5_a5_a3 (σ : MState) (pc : BitVec 64) (v15 v13 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v15 + v13)) := by
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have h13 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_rtype_add_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
    v15 v13 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 + v13))
    (rX_bits_x15 _ v15 h15) (rX_bits_x13 _ v13 h13) (wX_bits_x15 _ (v15 + v13))

/-- `or a5,a5,a4` = `or x15,x15,x14`. -/
theorem exec_or_a5_a5_a4 (σ : MState) (pc : BitVec 64) (v15 v14 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.OR))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v15 ||| v14)) := by
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_rtype_or_char (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
    v15 v14 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 ||| v14))
    (rX_bits_x15 _ v15 h15) (rX_bits_x14 _ v14 h14) (wX_bits_x15 _ (v15 ||| v14))

/-- `or a5,a5,a3` = `or x15,x15,x13`. -/
theorem exec_or_a5_a5_a3 (σ : MState) (pc : BitVec 64) (v15 v13 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.OR))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v15 ||| v13)) := by
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have h13 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_rtype_or_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
    v15 v13 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 ||| v13))
    (rX_bits_x15 _ v15 h15) (rX_bits_x13 _ v13 h13) (wX_bits_x15 _ (v15 ||| v13))

/-- `or a5,a0,a1` = `or x15,x10,x11` (entry). -/
theorem exec_or_a5_a0_a1 (σ : MState) (pc : BitVec 64) (v10 v11 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0f#5, rop.OR))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v10 ||| v11)) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_rtype_or_char (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0f#5)
    v10 v11 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v10 ||| v11))
    (rX_bits_x10 _ v10 h10) (rX_bits_x11 _ v11 h11) (wX_bits_x15 _ (v10 ||| v11))

/-- `li a5,-1` = `addi x15,x0,0xfff`. -/
theorem exec_li_a5_m1 (σ : MState) (pc : BitVec 64) :
    (execute (instruction.ITYPE (0xfff#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 ((0#64) + sign_extend (m := 64) (0xfff#12))) :=
  execute_itype_addi_char (0xfff#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0f#5) (0#64)
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 ((0#64) + sign_extend (m := 64) (0xfff#12)))
    (rX_bits_zero _) (wX_bits_x15 _ ((0#64) + sign_extend (m := 64) (0xfff#12)))

/-- `addi a5,a5,-129` = `addi x15,x15,0xf7f`. -/
theorem exec_addi_a5_m129 (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.ITYPE (0xf7f#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v15 + sign_extend (m := 64) (0xf7f#12))) := by
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_itype_addi_char (0xf7f#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 + sign_extend (m := 64) (0xf7f#12)))
    (rX_bits_x15 _ v15 h15) (wX_bits_x15 _ (v15 + sign_extend (m := 64) (0xf7f#12)))

/-- `andi a5,a5,7` = `andi x15,x15,7`. -/
theorem exec_andi_a5_7 (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.ITYPE (0x007#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ANDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v15 &&& sign_extend (m := 64) (0x007#12))) := by
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_itype_andi_char (0x007#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 &&& sign_extend (m := 64) (0x007#12)))
    (rX_bits_x15 _ v15 h15) (wX_bits_x15 _ (v15 &&& sign_extend (m := 64) (0x007#12)))
/-! ### Site 0x80006dc4 — `or a5,a0,a1` -/
theorem or_a5_ent_word :
    (((0x00#8).append (0xb5#8)).append (0x67#8)).append (0xb3#8) = (0x00b567b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem or_a5_ent_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xb5#8)).append (0x67#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006dc4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006dc4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v10 ||| v11)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006dc4 hmem
  exact stepObs_alu σ i u (0x80006dc4#64) vminstret (0x00b567b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0f#5, rop.OR))
    Register.x15 (v10 ||| v11) (0xb3#8) (0x67#8) (0xb5#8) (0x00#8)
    hG hpc hminstret or_a5_ent_word or_a5_ent_notrvc
    (Vsa.Sim.DecodeTable.decode_00b567b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_a5_a0_a1 σ (0x80006dc4#64) v10 v11 hx10 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006dc8 — `andi a5,a5,7` -/
theorem andi_a5_ent_word :
    (((0x00#8).append (0x77#8)).append (0xf7#8)).append (0x93#8) = (0x0077f793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem andi_a5_ent_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x77#8)).append (0xf7#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006dc8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006dc8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 &&& sign_extend (m := 64) (0x007#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006dc8 hmem
  exact stepObs_alu σ i u (0x80006dc8#64) vminstret (0x0077f793#32)
    (instruction.ITYPE (0x007#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ANDI))
    Register.x15 (v15 &&& sign_extend (m := 64) (0x007#12)) (0x93#8) (0xf7#8) (0x77#8) (0x00#8)
    hG hpc hminstret andi_a5_ent_word andi_a5_ent_notrvc
    (Vsa.Sim.DecodeTable.decode_0077f793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_andi_a5_7 σ (0x80006dc8#64) v15 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006dcc — `bnez a5,0x80006e7c` (misaligned → byte head) -/
theorem bnez_a5_ent_word :
    (((0x0a#8).append (0x07#8)).append (0x98#8)).append (0x63#8) = (0x0a079863#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bnez_a5_ent_notrvc :
    Sail.BitVec.extractLsb ((((0x0a#8).append (0x07#8)).append (0x98#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006dcc_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006dcc#64 : BitVec 64))
    (hv : (v15 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x00b0#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006dcc hmem
  exact stepObs_branch_taken σ i u (0x80006dcc#64) vminstret (0x00b0#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BNE (0x0a079863#32)
    (0x63#8) (0x98#8) (0x07#8) (0x0a#8)
    hG hpc hminstret bnez_a5_ent_word bnez_a5_ent_notrvc
    (Vsa.Sim.DecodeTable.decode_0a079863 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006dcc#64) (0x00b0#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) v15 (0#64) hG hpc
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006dcc#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_zero _)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006dcc_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006dcc#64 : BitVec 64))
    (hv : (v15 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006dcc hmem
  exact stepObs_branch_nottaken σ i u (0x80006dcc#64) vminstret (0x00b0#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BNE (0x0a079863#32)
    (0x63#8) (0x98#8) (0x07#8) (0x0a#8)
    hG hpc hminstret bnez_a5_ent_word bnez_a5_ent_notrvc
    (Vsa.Sim.DecodeTable.decode_0a079863 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006dcc#64) (0x00b0#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) v15 (0#64)
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006dcc#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006dd0 — `lui a5,0x7f7f8` -/
theorem lui_a5_word :
    (((0x7f#8).append (0x7f#8)).append (0x87#8)).append (0xb7#8) = (0x7f7f87b7#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem lui_a5_notrvc :
    Sail.BitVec.extractLsb ((((0x7f#8).append (0x7f#8)).append (0x87#8)).append (0xb7#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006dd0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006dd0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006dd0 hmem
  exact stepObs_alu σ i u (0x80006dd0#64) vminstret (0x7f7f87b7#32)
    (instruction.UTYPE (0x7f7f8#20, regidx.Regidx 0x0f#5, uop.LUI))
    Register.x15 (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12)) (0xb7#8) (0x87#8) (0x7f#8) (0x7f#8)
    hG hpc hminstret lui_a5_word lui_a5_notrvc
    (Vsa.Sim.DecodeTable.decode_7f7f87b7 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lui_a5 σ (0x80006dd0#64))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006dd4 — `addi a5,a5,-129` -/
theorem addi_a5_m129_word :
    (((0xf7#8).append (0xf7#8)).append (0x87#8)).append (0x93#8) = (0xf7f78793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem addi_a5_m129_notrvc :
    Sail.BitVec.extractLsb ((((0xf7#8).append (0xf7#8)).append (0x87#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006dd4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006dd4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 + sign_extend (m := 64) (0xf7f#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006dd4 hmem
  exact stepObs_alu σ i u (0x80006dd4#64) vminstret (0xf7f78793#32)
    (instruction.ITYPE (0xf7f#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 (v15 + sign_extend (m := 64) (0xf7f#12)) (0x93#8) (0x87#8) (0xf7#8) (0xf7#8)
    hG hpc hminstret addi_a5_m129_word addi_a5_m129_notrvc
    (Vsa.Sim.DecodeTable.decode_f7f78793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a5_m129 σ (0x80006dd4#64) v15 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006dd8 — `ld a4,0(a1)` (TOTAL 8-byte load) -/
theorem ld_a4_0_word :
    (((0x00#8).append (0x05#8)).append (0xb7#8)).append (0x03#8) = (0x0005b703#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ld_a4_0_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0xb7#8)).append (0x03#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006dd8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006dd8#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (v11 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006dd8#64)) (v11 + sign_extend (m := 64) (0x000#12))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006dd8 hmem
  exact stepObs_alu σ i u (0x80006dd8#64) vminstret (0x0005b703#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0e#5, false, 8))
    Register.x14
    (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006dd8#64)) (v11 + sign_extend (m := 64) (0x000#12))))
    (0x03#8) (0xb7#8) (0x05#8) (0x00#8)
    hG hpc hminstret ld_a4_0_word ld_a4_0_notrvc
    (Vsa.Sim.DecodeTable.decode_0005b703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_total σ (0x80006dd8#64) (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0e#5) v11 _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006dd8#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x14 _ (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006dd8#64)) (v11 + sign_extend (m := 64) (0x000#12))))) hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006ddc — `slli a3,a5,0x20` -/
theorem slli_a3_word :
    (((0x02#8).append (0x07#8)).append (0x96#8)).append (0x93#8) = (0x02079693#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem slli_a3_notrvc :
    Sail.BitVec.extractLsb ((((0x02#8).append (0x07#8)).append (0x96#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006ddc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006ddc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006ddc hmem
  exact stepObs_alu σ i u (0x80006ddc#64) vminstret (0x02079693#32)
    (instruction.SHIFTIOP (0x20#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0d#5, sop.SLLI))
    Register.x13 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0)) (0x93#8) (0x96#8) (0x07#8) (0x02#8)
    hG hpc hminstret slli_a3_word slli_a3_notrvc
    (Vsa.Sim.DecodeTable.decode_02079693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_gen σ (0x80006ddc#64) (0x20#6) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0d#5) v15 _ (rX_bits_x15 _ v15
      (by rw [get?_afterNextPC σ (0x80006ddc#64) _ (by decide) (by decide)]; exact hx15)) (wX_bits_x13 _ (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006de0 — `add a3,a3,a5` -/
theorem add_a3_word :
    (((0x00#8).append (0xf6#8)).append (0x86#8)).append (0xb3#8) = (0x00f686b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem add_a3_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf6#8)).append (0x86#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006de0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006de0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13 (v13 + v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006de0 hmem
  exact stepObs_alu σ i u (0x80006de0#64) vminstret (0x00f686b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0d#5, regidx.Regidx 0x0d#5, rop.ADD))
    Register.x13 (v13 + v15) (0xb3#8) (0x86#8) (0xf6#8) (0x00#8)
    hG hpc hminstret add_a3_word add_a3_notrvc
    (Vsa.Sim.DecodeTable.decode_00f686b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_a3_a3_a5 σ (0x80006de0#64) v13 v15 hx13 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006de4 — `and a6,a4,a3` -/
theorem and_a6_word :
    (((0x00#8).append (0xd7#8)).append (0x78#8)).append (0x33#8) = (0x00d77833#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem and_a6_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xd7#8)).append (0x78#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006de4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006de4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x16 (v14 &&& v13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006de4 hmem
  exact stepObs_alu σ i u (0x80006de4#64) vminstret (0x00d77833#32)
    (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x10#5, rop.AND))
    Register.x16 (v14 &&& v13) (0x33#8) (0x78#8) (0xd7#8) (0x00#8)
    hG hpc hminstret and_a6_word and_a6_notrvc
    (Vsa.Sim.DecodeTable.decode_00d77833 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_and_a6_a4_a3 σ (0x80006de4#64) v14 v13 hx14 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006de8 — `add a6,a6,a3` -/
theorem add_a6_word :
    (((0x00#8).append (0xd8#8)).append (0x08#8)).append (0x33#8) = (0x00d80833#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem add_a6_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xd8#8)).append (0x08#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006de8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v16 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx16 : σ.regs.get? Register.x16 = some v16)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006de8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x16 (v16 + v13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006de8 hmem
  exact stepObs_alu σ i u (0x80006de8#64) vminstret (0x00d80833#32)
    (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x10#5, regidx.Regidx 0x10#5, rop.ADD))
    Register.x16 (v16 + v13) (0x33#8) (0x08#8) (0xd8#8) (0x00#8)
    hG hpc hminstret add_a6_word add_a6_notrvc
    (Vsa.Sim.DecodeTable.decode_00d80833 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_a6_a6_a3 σ (0x80006de8#64) v16 v13 hx16 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006dec — `or a6,a6,a4` -/
theorem or_a6_a4_word :
    (((0x00#8).append (0xe8#8)).append (0x68#8)).append (0x33#8) = (0x00e86833#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem or_a6_a4_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xe8#8)).append (0x68#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006dec
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v16 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx16 : σ.regs.get? Register.x16 = some v16)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006dec#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x16 (v16 ||| v14)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006dec hmem
  exact stepObs_alu σ i u (0x80006dec#64) vminstret (0x00e86833#32)
    (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x10#5, regidx.Regidx 0x10#5, rop.OR))
    Register.x16 (v16 ||| v14) (0x33#8) (0x68#8) (0xe8#8) (0x00#8)
    hG hpc hminstret or_a6_a4_word or_a6_a4_notrvc
    (Vsa.Sim.DecodeTable.decode_00e86833 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_a6_a6_a4 σ (0x80006dec#64) v16 v14 hx16 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006df0 — `or a6,a6,a3` -/
theorem or_a6_a3_word :
    (((0x00#8).append (0xd8#8)).append (0x68#8)).append (0x33#8) = (0x00d86833#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem or_a6_a3_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xd8#8)).append (0x68#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006df0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v16 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx16 : σ.regs.get? Register.x16 = some v16)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006df0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x16 (v16 ||| v13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006df0 hmem
  exact stepObs_alu σ i u (0x80006df0#64) vminstret (0x00d86833#32)
    (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x10#5, regidx.Regidx 0x10#5, rop.OR))
    Register.x16 (v16 ||| v13) (0x33#8) (0x68#8) (0xd8#8) (0x00#8)
    hG hpc hminstret or_a6_a3_word or_a6_a3_notrvc
    (Vsa.Sim.DecodeTable.decode_00d86833 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_a6_a6_a3 σ (0x80006df0#64) v16 v13 hx16 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006df4 — `li a5,-1` -/
theorem li_a5_m1_word :
    (((0xff#8).append (0xf0#8)).append (0x07#8)).append (0x93#8) = (0xfff00793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem li_a5_m1_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xf0#8)).append (0x07#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006df4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006df4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 ((0#64) + sign_extend (m := 64) (0xfff#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006df4 hmem
  exact stepObs_alu σ i u (0x80006df4#64) vminstret (0xfff00793#32)
    (instruction.ITYPE (0xfff#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 ((0#64) + sign_extend (m := 64) (0xfff#12)) (0x93#8) (0x07#8) (0xf0#8) (0xff#8)
    hG hpc hminstret li_a5_m1_word li_a5_m1_notrvc
    (Vsa.Sim.DecodeTable.decode_fff00793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_li_a5_m1 σ (0x80006df4#64))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006df8 — `mv a2,a0` -/
theorem mv_a2_word :
    (((0x00#8).append (0x05#8)).append (0x06#8)).append (0x13#8) = (0x00050613#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem mv_a2_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x06#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006df8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006df8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x12 (v10 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006df8 hmem
  exact stepObs_alu σ i u (0x80006df8#64) vminstret (0x00050613#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0c#5, iop.ADDI))
    Register.x12 (v10 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x06#8) (0x05#8) (0x00#8)
    hG hpc hminstret mv_a2_word mv_a2_notrvc
    (Vsa.Sim.DecodeTable.decode_00050613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006df8#64) (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0c#5) v10 _ (rX_bits_x10 _ v10
      (by rw [get?_afterNextPC σ (0x80006df8#64) _ (by decide) (by decide)]; exact hx10)) (wX_bits_x12 _ (v10 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006dfc — `bne a6,a5,0x80006e24` (zero byte → byte tail) -/
theorem bne_a6a5_word :
    (((0x02#8).append (0xf8#8)).append (0x14#8)).append (0x63#8) = (0x02f81463#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bne_a6a5_notrvc :
    Sail.BitVec.extractLsb ((((0x02#8).append (0xf8#8)).append (0x14#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006dfc_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v16 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx16 : σ.regs.get? Register.x16 = some v16)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006dfc#64 : BitVec 64))
    (hv : (v16 != v15) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0028#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006dfc hmem
  exact stepObs_branch_taken σ i u (0x80006dfc#64) vminstret (0x0028#13)
    (regidx.Regidx 0x10#5) (regidx.Regidx 0x0f#5) bop.BNE (0x02f81463#32)
    (0x63#8) (0x14#8) (0xf8#8) (0x02#8)
    hG hpc hminstret bne_a6a5_word bne_a6a5_notrvc
    (Vsa.Sim.DecodeTable.decode_02f81463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006dfc#64) (0x0028#13) (regidx.Regidx 0x10#5) (regidx.Regidx 0x0f#5) v16 v15 hG hpc
      (rX_bits_x16 _ v16
        (by rw [get?_afterNextPC σ (0x80006dfc#64) _ (by decide) (by decide)]; exact hx16))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006dfc#64) _ (by decide) (by decide)]; exact hx15))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006dfc_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v16 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx16 : σ.regs.get? Register.x16 = some v16)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006dfc#64 : BitVec 64))
    (hv : (v16 != v15) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006dfc hmem
  exact stepObs_branch_nottaken σ i u (0x80006dfc#64) vminstret (0x0028#13)
    (regidx.Regidx 0x10#5) (regidx.Regidx 0x0f#5) bop.BNE (0x02f81463#32)
    (0x63#8) (0x14#8) (0xf8#8) (0x02#8)
    hG hpc hminstret bne_a6a5_word bne_a6a5_notrvc
    (Vsa.Sim.DecodeTable.decode_02f81463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006dfc#64) (0x0028#13) (regidx.Regidx 0x10#5) (regidx.Regidx 0x0f#5) v16 v15
      (rX_bits_x16 _ v16
        (by rw [get?_afterNextPC σ (0x80006dfc#64) _ (by decide) (by decide)]; exact hx16))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006dfc#64) _ (by decide) (by decide)]; exact hx15))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e00 — `addi a1,a1,8` -/
theorem addi_a1_8_word :
    (((0x00#8).append (0x85#8)).append (0x85#8)).append (0x93#8) = (0x00858593#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem addi_a1_8_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x85#8)).append (0x85#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e00
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e00#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11 (v11 + sign_extend (m := 64) (0x008#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e00 hmem
  exact stepObs_alu σ i u (0x80006e00#64) vminstret (0x00858593#32)
    (instruction.ITYPE (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v11 + sign_extend (m := 64) (0x008#12)) (0x93#8) (0x85#8) (0x85#8) (0x00#8)
    hG hpc hminstret addi_a1_8_word addi_a1_8_notrvc
    (Vsa.Sim.DecodeTable.decode_00858593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006e00#64) (0x008#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) v11 _ (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006e00#64) _ (by decide) (by decide)]; exact hx11)) (wX_bits_x11 _ (v11 + sign_extend (m := 64) (0x008#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e04 — `sd a4,0(a2)` (width-8 sd) -/
theorem sd_a4_word :
    (((0x00#8).append (0xe6#8)).append (0x30#8)).append (0x23#8) = (0x00e63023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sd_a4_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xe6#8)).append (0x30#8)).append (0x23#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e04
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e04#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v12 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v12 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v12 + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (v12 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = (sdMemCpy (afterNextPC (afterPrelude σ) (0x80006e04#64)).mem (v12 + sign_extend (m := 64) (0x000#12)) v14) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret (sdMemCpy (afterNextPC (afterPrelude σ) (0x80006e04#64)).mem (v12 + sign_extend (m := 64) (0x000#12)) v14)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e04 hmem
  exact stepObs_store σ i u (0x80006e04#64) vminstret (0x00e63023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0c#5, 8))
    (sdMemCpy (afterNextPC (afterPrelude σ) (0x80006e04#64)).mem (v12 + sign_extend (m := 64) (0x000#12)) v14)
    (0x23#8) (0x30#8) (0xe6#8) (0x00#8)
    hG hpc hminstret sd_a4_word sd_a4_notrvc
    (Vsa.Sim.DecodeTable.decode_00e63023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd σ (0x80006e04#64) (0x000#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0c#5) v12 v14 hG
      (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006e04#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x14 _ v14
      (by rw [get?_afterNextPC σ (0x80006e04#64) _ (by decide) (by decide)]; exact hx14))
      hlo hhiram hhiwin halign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e08 — `ld a4,0(a1)` (TOTAL 8-byte load) -/
theorem ld_a4_1_word :
    (((0x00#8).append (0x05#8)).append (0xb7#8)).append (0x03#8) = (0x0005b703#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ld_a4_1_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0xb7#8)).append (0x03#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e08
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e08#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (v11 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006e08#64)) (v11 + sign_extend (m := 64) (0x000#12))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e08 hmem
  exact stepObs_alu σ i u (0x80006e08#64) vminstret (0x0005b703#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0e#5, false, 8))
    Register.x14
    (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006e08#64)) (v11 + sign_extend (m := 64) (0x000#12))))
    (0x03#8) (0xb7#8) (0x05#8) (0x00#8)
    hG hpc hminstret ld_a4_1_word ld_a4_1_notrvc
    (Vsa.Sim.DecodeTable.decode_0005b703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_total σ (0x80006e08#64) (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0e#5) v11 _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006e08#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x14 _ (sign_extend (m := 64)
          (ldBytesT (afterNextPC (afterPrelude σ) (0x80006e08#64)) (v11 + sign_extend (m := 64) (0x000#12))))) hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e0c — `addi a2,a2,8` -/
theorem addi_a2_8_word :
    (((0x00#8).append (0x86#8)).append (0x06#8)).append (0x13#8) = (0x00860613#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem addi_a2_8_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x86#8)).append (0x06#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e0c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e0c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x12 (v12 + sign_extend (m := 64) (0x008#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e0c hmem
  exact stepObs_alu σ i u (0x80006e0c#64) vminstret (0x00860613#32)
    (instruction.ITYPE (0x008#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, iop.ADDI))
    Register.x12 (v12 + sign_extend (m := 64) (0x008#12)) (0x13#8) (0x06#8) (0x86#8) (0x00#8)
    hG hpc hminstret addi_a2_8_word addi_a2_8_notrvc
    (Vsa.Sim.DecodeTable.decode_00860613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006e0c#64) (0x008#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5) v12 _ (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006e0c#64) _ (by decide) (by decide)]; exact hx12)) (wX_bits_x12 _ (v12 + sign_extend (m := 64) (0x008#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e10 — `and a5,a4,a3` -/
theorem and_a5_w_word :
    (((0x00#8).append (0xd7#8)).append (0x77#8)).append (0xb3#8) = (0x00d777b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem and_a5_w_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xd7#8)).append (0x77#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e10
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e10#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v14 &&& v13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e10 hmem
  exact stepObs_alu σ i u (0x80006e10#64) vminstret (0x00d777b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, rop.AND))
    Register.x15 (v14 &&& v13) (0xb3#8) (0x77#8) (0xd7#8) (0x00#8)
    hG hpc hminstret and_a5_w_word and_a5_w_notrvc
    (Vsa.Sim.DecodeTable.decode_00d777b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_and_a5_a4_a3 σ (0x80006e10#64) v14 v13 hx14 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e14 — `add a5,a5,a3` -/
theorem add_a5_w_word :
    (((0x00#8).append (0xd7#8)).append (0x87#8)).append (0xb3#8) = (0x00d787b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem add_a5_w_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xd7#8)).append (0x87#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e14
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e14#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 + v13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e14 hmem
  exact stepObs_alu σ i u (0x80006e14#64) vminstret (0x00d787b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))
    Register.x15 (v15 + v13) (0xb3#8) (0x87#8) (0xd7#8) (0x00#8)
    hG hpc hminstret add_a5_w_word add_a5_w_notrvc
    (Vsa.Sim.DecodeTable.decode_00d787b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_a5_a5_a3 σ (0x80006e14#64) v15 v13 hx15 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e18 — `or a5,a5,a4` -/
theorem or_a5_a4_w_word :
    (((0x00#8).append (0xe7#8)).append (0xe7#8)).append (0xb3#8) = (0x00e7e7b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem or_a5_a4_w_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xe7#8)).append (0xe7#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e18
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e18#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 ||| v14)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e18 hmem
  exact stepObs_alu σ i u (0x80006e18#64) vminstret (0x00e7e7b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.OR))
    Register.x15 (v15 ||| v14) (0xb3#8) (0xe7#8) (0xe7#8) (0x00#8)
    hG hpc hminstret or_a5_a4_w_word or_a5_a4_w_notrvc
    (Vsa.Sim.DecodeTable.decode_00e7e7b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_a5_a5_a4 σ (0x80006e18#64) v15 v14 hx15 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e1c — `or a5,a5,a3` -/
theorem or_a5_a3_w_word :
    (((0x00#8).append (0xd7#8)).append (0xe7#8)).append (0xb3#8) = (0x00d7e7b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem or_a5_a3_w_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xd7#8)).append (0xe7#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e1c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e1c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 ||| v13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e1c hmem
  exact stepObs_alu σ i u (0x80006e1c#64) vminstret (0x00d7e7b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.OR))
    Register.x15 (v15 ||| v13) (0xb3#8) (0xe7#8) (0xd7#8) (0x00#8)
    hG hpc hminstret or_a5_a3_w_word or_a5_a3_w_notrvc
    (Vsa.Sim.DecodeTable.decode_00d7e7b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_a5_a5_a3 σ (0x80006e1c#64) v15 v13 hx15 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e20 — `beq a5,a6,0x80006e00` (loop back) -/
theorem beq_a5a6_word :
    (((0xff#8).append (0x07#8)).append (0x80#8)).append (0xe3#8) = (0xff0780e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem beq_a5a6_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0x07#8)).append (0x80#8)).append (0xe3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e20_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v16 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx16 : σ.regs.get? Register.x16 = some v16)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e20#64 : BitVec 64))
    (hv : (v15 == v16) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1fe0#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e20 hmem
  exact stepObs_branch_taken σ i u (0x80006e20#64) vminstret (0x1fe0#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x10#5) bop.BEQ (0xff0780e3#32)
    (0xe3#8) (0x80#8) (0x07#8) (0xff#8)
    hG hpc hminstret beq_a5a6_word beq_a5a6_notrvc
    (Vsa.Sim.DecodeTable.decode_ff0780e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_taken σ (0x80006e20#64) (0x1fe0#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x10#5) v15 v16 hG hpc
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006e20#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_x16 _ v16
        (by rw [get?_afterNextPC σ (0x80006e20#64) _ (by decide) (by decide)]; exact hx16))
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006e20_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v16 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx16 : σ.regs.get? Register.x16 = some v16)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e20#64 : BitVec 64))
    (hv : (v15 == v16) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e20 hmem
  exact stepObs_branch_nottaken σ i u (0x80006e20#64) vminstret (0x1fe0#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x10#5) bop.BEQ (0xff0780e3#32)
    (0xe3#8) (0x80#8) (0x07#8) (0xff#8)
    hG hpc hminstret beq_a5a6_word beq_a5a6_notrvc
    (Vsa.Sim.DecodeTable.decode_ff0780e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_nottaken σ (0x80006e20#64) (0x1fe0#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x10#5) v15 v16
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006e20#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_x16 _ v16
        (by rw [get?_afterNextPC σ (0x80006e20#64) _ (by decide) (by decide)]; exact hx16))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e24 — `lbu a5,0(a1)` (width-1 lbu) -/
theorem lbu_a5_t0_word :
    (((0x00#8).append (0x05#8)).append (0xc7#8)).append (0x83#8) = (0x0005c783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem lbu_a5_t0_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0xc7#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e24
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e24#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x000#12)).toNat)
    (hb0 : σ.mem[(v11 + sign_extend (m := 64) (0x000#12)).toNat]? = some b0v) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strcpy_at_80006e24 hmem
  exact stepObs_alu σ i u (0x80006e24#64) vminstret (0x0005c783#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, true, 1))
    Register.x15 (zero_extend (m := 64) b0v) (0x83#8) (0xc7#8) (0x05#8) (0x00#8)
    hG hpc hminstret lbu_a5_t0_word lbu_a5_t0_notrvc
    (Vsa.Sim.DecodeTable.decode_0005c783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_gen σ (0x80006e24#64) (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0f#5) v11 b0v _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006e24#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x15 _ (zero_extend (m := 64) b0v)) hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e28 — `lbu a4,1(a1)` (width-1 lbu) -/
theorem lbu_a4_t1_word :
    (((0x00#8).append (0x15#8)).append (0xc7#8)).append (0x03#8) = (0x0015c703#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem lbu_a4_t1_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x15#8)).append (0xc7#8)).append (0x03#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e28
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e28#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x001#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x001#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x001#12)).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x001#12)).toNat)
    (hb0 : σ.mem[(v11 + sign_extend (m := 64) (0x001#12)).toNat]? = some b0v) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strcpy_at_80006e28 hmem
  exact stepObs_alu σ i u (0x80006e28#64) vminstret (0x0015c703#32)
    (instruction.LOAD (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0e#5, true, 1))
    Register.x14 (zero_extend (m := 64) b0v) (0x03#8) (0xc7#8) (0x15#8) (0x00#8)
    hG hpc hminstret lbu_a4_t1_word lbu_a4_t1_notrvc
    (Vsa.Sim.DecodeTable.decode_0015c703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_gen σ (0x80006e28#64) (0x001#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0e#5) v11 b0v _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006e28#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x14 _ (zero_extend (m := 64) b0v)) hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e2c — `lbu a3,2(a1)` (width-1 lbu) -/
theorem lbu_a3_t2_word :
    (((0x00#8).append (0x25#8)).append (0xc6#8)).append (0x83#8) = (0x0025c683#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem lbu_a3_t2_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x25#8)).append (0xc6#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e2c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e2c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x002#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x002#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x002#12)).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x002#12)).toNat)
    (hb0 : σ.mem[(v11 + sign_extend (m := 64) (0x002#12)).toNat]? = some b0v) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strcpy_at_80006e2c hmem
  exact stepObs_alu σ i u (0x80006e2c#64) vminstret (0x0025c683#32)
    (instruction.LOAD (0x002#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0d#5, true, 1))
    Register.x13 (zero_extend (m := 64) b0v) (0x83#8) (0xc6#8) (0x25#8) (0x00#8)
    hG hpc hminstret lbu_a3_t2_word lbu_a3_t2_notrvc
    (Vsa.Sim.DecodeTable.decode_0025c683 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_gen σ (0x80006e2c#64) (0x002#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0d#5) v11 b0v _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006e2c#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x13 _ (zero_extend (m := 64) b0v)) hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e30 — `sb a5,0(a2)` (width-1 sb) -/
theorem sb_a5_t0_word :
    (((0x00#8).append (0xf6#8)).append (0x00#8)).append (0x23#8) = (0x00f60023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sb_a5_t0_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf6#8)).append (0x00#8)).append (0x23#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e30
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e30#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v12 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v12 + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v12 + sign_extend (m := 64) (0x000#12)).toNat) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = ((afterNextPC (afterPrelude σ) (0x80006e30#64)).mem.insert (v12 + sign_extend (m := 64) (0x000#12)).toNat (stData 1 v15)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret ((afterNextPC (afterPrelude σ) (0x80006e30#64)).mem.insert (v12 + sign_extend (m := 64) (0x000#12)).toNat (stData 1 v15))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e30 hmem
  exact stepObs_store σ i u (0x80006e30#64) vminstret (0x00f60023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0c#5, 1))
    ((afterNextPC (afterPrelude σ) (0x80006e30#64)).mem.insert (v12 + sign_extend (m := 64) (0x000#12)).toNat (stData 1 v15))
    (0x23#8) (0x00#8) (0xf6#8) (0x00#8)
    hG hpc hminstret sb_a5_t0_word sb_a5_t0_notrvc
    (Vsa.Sim.DecodeTable.decode_00f60023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sb σ (0x80006e30#64) (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0c#5) v12 v15 hG
      (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006e30#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x15 _ v15
      (by rw [get?_afterNextPC σ (0x80006e30#64) _ (by decide) (by decide)]; exact hx15))
      hlo hhiram hhiwin)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e34 — `beqz a5,0x80006e78` -/
theorem beqz_a5_t0_word :
    (((0x04#8).append (0x07#8)).append (0x82#8)).append (0x63#8) = (0x04078263#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem beqz_a5_t0_notrvc :
    Sail.BitVec.extractLsb ((((0x04#8).append (0x07#8)).append (0x82#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e34_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e34#64 : BitVec 64))
    (hv : (v15 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0044#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e34 hmem
  exact stepObs_branch_taken σ i u (0x80006e34#64) vminstret (0x0044#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x04078263#32)
    (0x63#8) (0x82#8) (0x07#8) (0x04#8)
    hG hpc hminstret beqz_a5_t0_word beqz_a5_t0_notrvc
    (Vsa.Sim.DecodeTable.decode_04078263 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_taken σ (0x80006e34#64) (0x0044#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) v15 (0#64) hG hpc
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006e34#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_zero _)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006e34_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e34#64 : BitVec 64))
    (hv : (v15 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e34 hmem
  exact stepObs_branch_nottaken σ i u (0x80006e34#64) vminstret (0x0044#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x04078263#32)
    (0x63#8) (0x82#8) (0x07#8) (0x04#8)
    hG hpc hminstret beqz_a5_t0_word beqz_a5_t0_notrvc
    (Vsa.Sim.DecodeTable.decode_04078263 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_nottaken σ (0x80006e34#64) (0x0044#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) v15 (0#64)
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006e34#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e38 — `sb a4,1(a2)` (width-1 sb) -/
theorem sb_a4_t1_word :
    (((0x00#8).append (0xe6#8)).append (0x00#8)).append (0xa3#8) = (0x00e600a3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sb_a4_t1_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xe6#8)).append (0x00#8)).append (0xa3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e38
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e38#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v12 + sign_extend (m := 64) (0x001#12)).toNat)
    (hhiram : (v12 + sign_extend (m := 64) (0x001#12)).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v12 + sign_extend (m := 64) (0x001#12)).toNat) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = ((afterNextPC (afterPrelude σ) (0x80006e38#64)).mem.insert (v12 + sign_extend (m := 64) (0x001#12)).toNat (stData 1 v14)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret ((afterNextPC (afterPrelude σ) (0x80006e38#64)).mem.insert (v12 + sign_extend (m := 64) (0x001#12)).toNat (stData 1 v14))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e38 hmem
  exact stepObs_store σ i u (0x80006e38#64) vminstret (0x00e600a3#32)
    (instruction.STORE (0x001#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0c#5, 1))
    ((afterNextPC (afterPrelude σ) (0x80006e38#64)).mem.insert (v12 + sign_extend (m := 64) (0x001#12)).toNat (stData 1 v14))
    (0xa3#8) (0x00#8) (0xe6#8) (0x00#8)
    hG hpc hminstret sb_a4_t1_word sb_a4_t1_notrvc
    (Vsa.Sim.DecodeTable.decode_00e600a3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sb σ (0x80006e38#64) (0x001#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0c#5) v12 v14 hG
      (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006e38#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x14 _ v14
      (by rw [get?_afterNextPC σ (0x80006e38#64) _ (by decide) (by decide)]; exact hx14))
      hlo hhiram hhiwin)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e3c — `beqz a4,0x80006e78` -/
theorem beqz_a4_t1_word :
    (((0x02#8).append (0x07#8)).append (0x0e#8)).append (0x63#8) = (0x02070e63#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem beqz_a4_t1_notrvc :
    Sail.BitVec.extractLsb ((((0x02#8).append (0x07#8)).append (0x0e#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e3c_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e3c#64 : BitVec 64))
    (hv : (v14 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x003c#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e3c hmem
  exact stepObs_branch_taken σ i u (0x80006e3c#64) vminstret (0x003c#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BEQ (0x02070e63#32)
    (0x63#8) (0x0e#8) (0x07#8) (0x02#8)
    hG hpc hminstret beqz_a4_t1_word beqz_a4_t1_notrvc
    (Vsa.Sim.DecodeTable.decode_02070e63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_taken σ (0x80006e3c#64) (0x003c#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) v14 (0#64) hG hpc
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006e3c#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_zero _)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006e3c_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e3c#64 : BitVec 64))
    (hv : (v14 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e3c hmem
  exact stepObs_branch_nottaken σ i u (0x80006e3c#64) vminstret (0x003c#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BEQ (0x02070e63#32)
    (0x63#8) (0x0e#8) (0x07#8) (0x02#8)
    hG hpc hminstret beqz_a4_t1_word beqz_a4_t1_notrvc
    (Vsa.Sim.DecodeTable.decode_02070e63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_nottaken σ (0x80006e3c#64) (0x003c#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) v14 (0#64)
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006e3c#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e40 — `lbu a5,3(a1)` (width-1 lbu) -/
theorem lbu_a5_t3_word :
    (((0x00#8).append (0x35#8)).append (0xc7#8)).append (0x83#8) = (0x0035c783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem lbu_a5_t3_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x35#8)).append (0xc7#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e40
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e40#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x003#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x003#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x003#12)).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x003#12)).toNat)
    (hb0 : σ.mem[(v11 + sign_extend (m := 64) (0x003#12)).toNat]? = some b0v) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strcpy_at_80006e40 hmem
  exact stepObs_alu σ i u (0x80006e40#64) vminstret (0x0035c783#32)
    (instruction.LOAD (0x003#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, true, 1))
    Register.x15 (zero_extend (m := 64) b0v) (0x83#8) (0xc7#8) (0x35#8) (0x00#8)
    hG hpc hminstret lbu_a5_t3_word lbu_a5_t3_notrvc
    (Vsa.Sim.DecodeTable.decode_0035c783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_gen σ (0x80006e40#64) (0x003#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0f#5) v11 b0v _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006e40#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x15 _ (zero_extend (m := 64) b0v)) hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e44 — `sb a3,2(a2)` (width-1 sb) -/
theorem sb_a3_t2_word :
    (((0x00#8).append (0xd6#8)).append (0x01#8)).append (0x23#8) = (0x00d60123#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sb_a3_t2_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xd6#8)).append (0x01#8)).append (0x23#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e44
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e44#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v12 + sign_extend (m := 64) (0x002#12)).toNat)
    (hhiram : (v12 + sign_extend (m := 64) (0x002#12)).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v12 + sign_extend (m := 64) (0x002#12)).toNat) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = ((afterNextPC (afterPrelude σ) (0x80006e44#64)).mem.insert (v12 + sign_extend (m := 64) (0x002#12)).toNat (stData 1 v13)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret ((afterNextPC (afterPrelude σ) (0x80006e44#64)).mem.insert (v12 + sign_extend (m := 64) (0x002#12)).toNat (stData 1 v13))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e44 hmem
  exact stepObs_store σ i u (0x80006e44#64) vminstret (0x00d60123#32)
    (instruction.STORE (0x002#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x0c#5, 1))
    ((afterNextPC (afterPrelude σ) (0x80006e44#64)).mem.insert (v12 + sign_extend (m := 64) (0x002#12)).toNat (stData 1 v13))
    (0x23#8) (0x01#8) (0xd6#8) (0x00#8)
    hG hpc hminstret sb_a3_t2_word sb_a3_t2_notrvc
    (Vsa.Sim.DecodeTable.decode_00d60123 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sb σ (0x80006e44#64) (0x002#12) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0c#5) v12 v13 hG
      (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006e44#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x13 _ v13
      (by rw [get?_afterNextPC σ (0x80006e44#64) _ (by decide) (by decide)]; exact hx13))
      hlo hhiram hhiwin)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e48 — `beqz a3,0x80006e78` -/
theorem beqz_a3_t2_word :
    (((0x02#8).append (0x06#8)).append (0x88#8)).append (0x63#8) = (0x02068863#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem beqz_a3_t2_notrvc :
    Sail.BitVec.extractLsb ((((0x02#8).append (0x06#8)).append (0x88#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e48_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e48#64 : BitVec 64))
    (hv : (v13 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0030#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e48 hmem
  exact stepObs_branch_taken σ i u (0x80006e48#64) vminstret (0x0030#13)
    (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) bop.BEQ (0x02068863#32)
    (0x63#8) (0x88#8) (0x06#8) (0x02#8)
    hG hpc hminstret beqz_a3_t2_word beqz_a3_t2_notrvc
    (Vsa.Sim.DecodeTable.decode_02068863 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_taken σ (0x80006e48#64) (0x0030#13) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) v13 (0#64) hG hpc
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006e48#64) _ (by decide) (by decide)]; exact hx13))
      (rX_bits_zero _)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006e48_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e48#64 : BitVec 64))
    (hv : (v13 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e48 hmem
  exact stepObs_branch_nottaken σ i u (0x80006e48#64) vminstret (0x0030#13)
    (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) bop.BEQ (0x02068863#32)
    (0x63#8) (0x88#8) (0x06#8) (0x02#8)
    hG hpc hminstret beqz_a3_t2_word beqz_a3_t2_notrvc
    (Vsa.Sim.DecodeTable.decode_02068863 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_nottaken σ (0x80006e48#64) (0x0030#13) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) v13 (0#64)
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006e48#64) _ (by decide) (by decide)]; exact hx13))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e4c — `lbu a4,4(a1)` (width-1 lbu) -/
theorem lbu_a4_t4_word :
    (((0x00#8).append (0x45#8)).append (0xc7#8)).append (0x03#8) = (0x0045c703#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem lbu_a4_t4_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x45#8)).append (0xc7#8)).append (0x03#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e4c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e4c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x004#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x004#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x004#12)).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x004#12)).toNat)
    (hb0 : σ.mem[(v11 + sign_extend (m := 64) (0x004#12)).toNat]? = some b0v) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strcpy_at_80006e4c hmem
  exact stepObs_alu σ i u (0x80006e4c#64) vminstret (0x0045c703#32)
    (instruction.LOAD (0x004#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0e#5, true, 1))
    Register.x14 (zero_extend (m := 64) b0v) (0x03#8) (0xc7#8) (0x45#8) (0x00#8)
    hG hpc hminstret lbu_a4_t4_word lbu_a4_t4_notrvc
    (Vsa.Sim.DecodeTable.decode_0045c703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_gen σ (0x80006e4c#64) (0x004#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0e#5) v11 b0v _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006e4c#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x14 _ (zero_extend (m := 64) b0v)) hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e50 — `sb a5,3(a2)` (width-1 sb) -/
theorem sb_a5_t3_word :
    (((0x00#8).append (0xf6#8)).append (0x01#8)).append (0xa3#8) = (0x00f601a3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sb_a5_t3_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf6#8)).append (0x01#8)).append (0xa3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e50
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e50#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v12 + sign_extend (m := 64) (0x003#12)).toNat)
    (hhiram : (v12 + sign_extend (m := 64) (0x003#12)).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v12 + sign_extend (m := 64) (0x003#12)).toNat) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = ((afterNextPC (afterPrelude σ) (0x80006e50#64)).mem.insert (v12 + sign_extend (m := 64) (0x003#12)).toNat (stData 1 v15)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret ((afterNextPC (afterPrelude σ) (0x80006e50#64)).mem.insert (v12 + sign_extend (m := 64) (0x003#12)).toNat (stData 1 v15))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e50 hmem
  exact stepObs_store σ i u (0x80006e50#64) vminstret (0x00f601a3#32)
    (instruction.STORE (0x003#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0c#5, 1))
    ((afterNextPC (afterPrelude σ) (0x80006e50#64)).mem.insert (v12 + sign_extend (m := 64) (0x003#12)).toNat (stData 1 v15))
    (0xa3#8) (0x01#8) (0xf6#8) (0x00#8)
    hG hpc hminstret sb_a5_t3_word sb_a5_t3_notrvc
    (Vsa.Sim.DecodeTable.decode_00f601a3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sb σ (0x80006e50#64) (0x003#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0c#5) v12 v15 hG
      (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006e50#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x15 _ v15
      (by rw [get?_afterNextPC σ (0x80006e50#64) _ (by decide) (by decide)]; exact hx15))
      hlo hhiram hhiwin)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e54 — `beqz a5,0x80006e78` -/
theorem beqz_a5_t3_word :
    (((0x02#8).append (0x07#8)).append (0x82#8)).append (0x63#8) = (0x02078263#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem beqz_a5_t3_notrvc :
    Sail.BitVec.extractLsb ((((0x02#8).append (0x07#8)).append (0x82#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e54_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e54#64 : BitVec 64))
    (hv : (v15 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0024#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e54 hmem
  exact stepObs_branch_taken σ i u (0x80006e54#64) vminstret (0x0024#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x02078263#32)
    (0x63#8) (0x82#8) (0x07#8) (0x02#8)
    hG hpc hminstret beqz_a5_t3_word beqz_a5_t3_notrvc
    (Vsa.Sim.DecodeTable.decode_02078263 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_taken σ (0x80006e54#64) (0x0024#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) v15 (0#64) hG hpc
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006e54#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_zero _)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006e54_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e54#64 : BitVec 64))
    (hv : (v15 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e54 hmem
  exact stepObs_branch_nottaken σ i u (0x80006e54#64) vminstret (0x0024#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x02078263#32)
    (0x63#8) (0x82#8) (0x07#8) (0x02#8)
    hG hpc hminstret beqz_a5_t3_word beqz_a5_t3_notrvc
    (Vsa.Sim.DecodeTable.decode_02078263 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_nottaken σ (0x80006e54#64) (0x0024#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) v15 (0#64)
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006e54#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e58 — `lbu a5,5(a1)` (width-1 lbu) -/
theorem lbu_a5_t5_word :
    (((0x00#8).append (0x55#8)).append (0xc7#8)).append (0x83#8) = (0x0055c783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem lbu_a5_t5_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x55#8)).append (0xc7#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e58
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e58#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x005#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x005#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x005#12)).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x005#12)).toNat)
    (hb0 : σ.mem[(v11 + sign_extend (m := 64) (0x005#12)).toNat]? = some b0v) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strcpy_at_80006e58 hmem
  exact stepObs_alu σ i u (0x80006e58#64) vminstret (0x0055c783#32)
    (instruction.LOAD (0x005#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, true, 1))
    Register.x15 (zero_extend (m := 64) b0v) (0x83#8) (0xc7#8) (0x55#8) (0x00#8)
    hG hpc hminstret lbu_a5_t5_word lbu_a5_t5_notrvc
    (Vsa.Sim.DecodeTable.decode_0055c783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_gen σ (0x80006e58#64) (0x005#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0f#5) v11 b0v _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006e58#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x15 _ (zero_extend (m := 64) b0v)) hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e5c — `sb a4,4(a2)` (width-1 sb) -/
theorem sb_a4_t4_word :
    (((0x00#8).append (0xe6#8)).append (0x02#8)).append (0x23#8) = (0x00e60223#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sb_a4_t4_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xe6#8)).append (0x02#8)).append (0x23#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e5c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e5c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v12 + sign_extend (m := 64) (0x004#12)).toNat)
    (hhiram : (v12 + sign_extend (m := 64) (0x004#12)).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v12 + sign_extend (m := 64) (0x004#12)).toNat) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = ((afterNextPC (afterPrelude σ) (0x80006e5c#64)).mem.insert (v12 + sign_extend (m := 64) (0x004#12)).toNat (stData 1 v14)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret ((afterNextPC (afterPrelude σ) (0x80006e5c#64)).mem.insert (v12 + sign_extend (m := 64) (0x004#12)).toNat (stData 1 v14))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e5c hmem
  exact stepObs_store σ i u (0x80006e5c#64) vminstret (0x00e60223#32)
    (instruction.STORE (0x004#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0c#5, 1))
    ((afterNextPC (afterPrelude σ) (0x80006e5c#64)).mem.insert (v12 + sign_extend (m := 64) (0x004#12)).toNat (stData 1 v14))
    (0x23#8) (0x02#8) (0xe6#8) (0x00#8)
    hG hpc hminstret sb_a4_t4_word sb_a4_t4_notrvc
    (Vsa.Sim.DecodeTable.decode_00e60223 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sb σ (0x80006e5c#64) (0x004#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0c#5) v12 v14 hG
      (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006e5c#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x14 _ v14
      (by rw [get?_afterNextPC σ (0x80006e5c#64) _ (by decide) (by decide)]; exact hx14))
      hlo hhiram hhiwin)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e60 — `beqz a4,0x80006e78` -/
theorem beqz_a4_t4_word :
    (((0x00#8).append (0x07#8)).append (0x0c#8)).append (0x63#8) = (0x00070c63#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem beqz_a4_t4_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x07#8)).append (0x0c#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e60_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e60#64 : BitVec 64))
    (hv : (v14 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0018#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e60 hmem
  exact stepObs_branch_taken σ i u (0x80006e60#64) vminstret (0x0018#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BEQ (0x00070c63#32)
    (0x63#8) (0x0c#8) (0x07#8) (0x00#8)
    hG hpc hminstret beqz_a4_t4_word beqz_a4_t4_notrvc
    (Vsa.Sim.DecodeTable.decode_00070c63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_taken σ (0x80006e60#64) (0x0018#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) v14 (0#64) hG hpc
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006e60#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_zero _)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006e60_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e60#64 : BitVec 64))
    (hv : (v14 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e60 hmem
  exact stepObs_branch_nottaken σ i u (0x80006e60#64) vminstret (0x0018#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BEQ (0x00070c63#32)
    (0x63#8) (0x0c#8) (0x07#8) (0x00#8)
    hG hpc hminstret beqz_a4_t4_word beqz_a4_t4_notrvc
    (Vsa.Sim.DecodeTable.decode_00070c63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_nottaken σ (0x80006e60#64) (0x0018#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) v14 (0#64)
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006e60#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e64 — `lbu a4,6(a1)` (width-1 lbu) -/
theorem lbu_a4_t6_word :
    (((0x00#8).append (0x65#8)).append (0xc7#8)).append (0x03#8) = (0x0065c703#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem lbu_a4_t6_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x65#8)).append (0xc7#8)).append (0x03#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e64
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e64#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x006#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x006#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x006#12)).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x006#12)).toNat)
    (hb0 : σ.mem[(v11 + sign_extend (m := 64) (0x006#12)).toNat]? = some b0v) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strcpy_at_80006e64 hmem
  exact stepObs_alu σ i u (0x80006e64#64) vminstret (0x0065c703#32)
    (instruction.LOAD (0x006#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0e#5, true, 1))
    Register.x14 (zero_extend (m := 64) b0v) (0x03#8) (0xc7#8) (0x65#8) (0x00#8)
    hG hpc hminstret lbu_a4_t6_word lbu_a4_t6_notrvc
    (Vsa.Sim.DecodeTable.decode_0065c703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_gen σ (0x80006e64#64) (0x006#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0e#5) v11 b0v _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006e64#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x14 _ (zero_extend (m := 64) b0v)) hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e68 — `sb a5,5(a2)` (width-1 sb) -/
theorem sb_a5_t5_word :
    (((0x00#8).append (0xf6#8)).append (0x02#8)).append (0xa3#8) = (0x00f602a3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sb_a5_t5_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf6#8)).append (0x02#8)).append (0xa3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e68
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e68#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v12 + sign_extend (m := 64) (0x005#12)).toNat)
    (hhiram : (v12 + sign_extend (m := 64) (0x005#12)).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v12 + sign_extend (m := 64) (0x005#12)).toNat) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = ((afterNextPC (afterPrelude σ) (0x80006e68#64)).mem.insert (v12 + sign_extend (m := 64) (0x005#12)).toNat (stData 1 v15)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret ((afterNextPC (afterPrelude σ) (0x80006e68#64)).mem.insert (v12 + sign_extend (m := 64) (0x005#12)).toNat (stData 1 v15))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e68 hmem
  exact stepObs_store σ i u (0x80006e68#64) vminstret (0x00f602a3#32)
    (instruction.STORE (0x005#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0c#5, 1))
    ((afterNextPC (afterPrelude σ) (0x80006e68#64)).mem.insert (v12 + sign_extend (m := 64) (0x005#12)).toNat (stData 1 v15))
    (0xa3#8) (0x02#8) (0xf6#8) (0x00#8)
    hG hpc hminstret sb_a5_t5_word sb_a5_t5_notrvc
    (Vsa.Sim.DecodeTable.decode_00f602a3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sb σ (0x80006e68#64) (0x005#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0c#5) v12 v15 hG
      (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006e68#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x15 _ v15
      (by rw [get?_afterNextPC σ (0x80006e68#64) _ (by decide) (by decide)]; exact hx15))
      hlo hhiram hhiwin)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e6c — `beqz a5,0x80006e78` -/
theorem beqz_a5_t5_word :
    (((0x00#8).append (0x07#8)).append (0x86#8)).append (0x63#8) = (0x00078663#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem beqz_a5_t5_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x07#8)).append (0x86#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e6c_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e6c#64 : BitVec 64))
    (hv : (v15 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x000c#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e6c hmem
  exact stepObs_branch_taken σ i u (0x80006e6c#64) vminstret (0x000c#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x00078663#32)
    (0x63#8) (0x86#8) (0x07#8) (0x00#8)
    hG hpc hminstret beqz_a5_t5_word beqz_a5_t5_notrvc
    (Vsa.Sim.DecodeTable.decode_00078663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_taken σ (0x80006e6c#64) (0x000c#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) v15 (0#64) hG hpc
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006e6c#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_zero _)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006e6c_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e6c#64 : BitVec 64))
    (hv : (v15 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e6c hmem
  exact stepObs_branch_nottaken σ i u (0x80006e6c#64) vminstret (0x000c#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x00078663#32)
    (0x63#8) (0x86#8) (0x07#8) (0x00#8)
    hG hpc hminstret beqz_a5_t5_word beqz_a5_t5_notrvc
    (Vsa.Sim.DecodeTable.decode_00078663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_nottaken σ (0x80006e6c#64) (0x000c#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) v15 (0#64)
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x80006e6c#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e70 — `sb a4,6(a2)` (width-1 sb) -/
theorem sb_a4_t6_word :
    (((0x00#8).append (0xe6#8)).append (0x03#8)).append (0x23#8) = (0x00e60323#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sb_a4_t6_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xe6#8)).append (0x03#8)).append (0x23#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e70
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e70#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v12 + sign_extend (m := 64) (0x006#12)).toNat)
    (hhiram : (v12 + sign_extend (m := 64) (0x006#12)).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v12 + sign_extend (m := 64) (0x006#12)).toNat) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = ((afterNextPC (afterPrelude σ) (0x80006e70#64)).mem.insert (v12 + sign_extend (m := 64) (0x006#12)).toNat (stData 1 v14)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret ((afterNextPC (afterPrelude σ) (0x80006e70#64)).mem.insert (v12 + sign_extend (m := 64) (0x006#12)).toNat (stData 1 v14))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e70 hmem
  exact stepObs_store σ i u (0x80006e70#64) vminstret (0x00e60323#32)
    (instruction.STORE (0x006#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0c#5, 1))
    ((afterNextPC (afterPrelude σ) (0x80006e70#64)).mem.insert (v12 + sign_extend (m := 64) (0x006#12)).toNat (stData 1 v14))
    (0x23#8) (0x03#8) (0xe6#8) (0x00#8)
    hG hpc hminstret sb_a4_t6_word sb_a4_t6_notrvc
    (Vsa.Sim.DecodeTable.decode_00e60323 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sb σ (0x80006e70#64) (0x006#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0c#5) v12 v14 hG
      (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006e70#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_x14 _ v14
      (by rw [get?_afterNextPC σ (0x80006e70#64) _ (by decide) (by decide)]; exact hx14))
      hlo hhiram hhiwin)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e74 — `bnez a4,0x80006e98` (→ NUL finisher) -/
theorem bnez_a4_t6_word :
    (((0x02#8).append (0x07#8)).append (0x12#8)).append (0x63#8) = (0x02071263#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bnez_a4_t6_notrvc :
    Sail.BitVec.extractLsb ((((0x02#8).append (0x07#8)).append (0x12#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e74_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e74#64 : BitVec 64))
    (hv : (v14 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0024#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e74 hmem
  exact stepObs_branch_taken σ i u (0x80006e74#64) vminstret (0x0024#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BNE (0x02071263#32)
    (0x63#8) (0x12#8) (0x07#8) (0x02#8)
    hG hpc hminstret bnez_a4_t6_word bnez_a4_t6_notrvc
    (Vsa.Sim.DecodeTable.decode_02071263 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006e74#64) (0x0024#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) v14 (0#64) hG hpc
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006e74#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_zero _)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006e74_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e74#64 : BitVec 64))
    (hv : (v14 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e74 hmem
  exact stepObs_branch_nottaken σ i u (0x80006e74#64) vminstret (0x0024#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BNE (0x02071263#32)
    (0x63#8) (0x12#8) (0x07#8) (0x02#8)
    hG hpc hminstret bnez_a4_t6_word bnez_a4_t6_notrvc
    (Vsa.Sim.DecodeTable.decode_02071263 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006e74#64) (0x0024#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) v14 (0#64)
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006e74#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e78 — `ret` = `jr x1,0` -/
theorem ret_e78_word :
    (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ret_e78_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e78
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e78#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e78 hmem
  exact stepObs_jr σ i u (0x80006e78#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    ret_e78_notrvc ret_e78_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ret σ (0x80006e78#64) vra hx1) htgt hi

/-! ### Site 0x80006e7c — `mv a5,a0` -/
theorem mv_a5_h_word :
    (((0x00#8).append (0x05#8)).append (0x07#8)).append (0x93#8) = (0x00050793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem mv_a5_h_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x07#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e7c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e7c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v10 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e7c hmem
  exact stepObs_alu σ i u (0x80006e7c#64) vminstret (0x00050793#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 (v10 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x07#8) (0x05#8) (0x00#8)
    hG hpc hminstret mv_a5_h_word mv_a5_h_notrvc
    (Vsa.Sim.DecodeTable.decode_00050793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006e7c#64) (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0f#5) v10 _ (rX_bits_x10 _ v10
      (by rw [get?_afterNextPC σ (0x80006e7c#64) _ (by decide) (by decide)]; exact hx10)) (wX_bits_x15 _ (v10 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e80 — `lbu a4,0(a1)` (width-1 lbu) -/
theorem lbu_a4_h_word :
    (((0x00#8).append (0x05#8)).append (0xc7#8)).append (0x03#8) = (0x0005c703#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem lbu_a4_h_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0xc7#8)).append (0x03#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e80
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e80#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x000#12)).toNat)
    (hb0 : σ.mem[(v11 + sign_extend (m := 64) (0x000#12)).toNat]? = some b0v) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strcpy_at_80006e80 hmem
  exact stepObs_alu σ i u (0x80006e80#64) vminstret (0x0005c703#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0e#5, true, 1))
    Register.x14 (zero_extend (m := 64) b0v) (0x03#8) (0xc7#8) (0x05#8) (0x00#8)
    hG hpc hminstret lbu_a4_h_word lbu_a4_h_notrvc
    (Vsa.Sim.DecodeTable.decode_0005c703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_gen σ (0x80006e80#64) (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0e#5) v11 b0v _ hG
      (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006e80#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x14 _ (zero_extend (m := 64) b0v)) hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e84 — `addi a5,a5,1` -/
theorem addi_a5_1h_word :
    (((0x00#8).append (0x17#8)).append (0x87#8)).append (0x93#8) = (0x00178793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem addi_a5_1h_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x17#8)).append (0x87#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e84
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e84#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e84 hmem
  exact stepObs_alu σ i u (0x80006e84#64) vminstret (0x00178793#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 (v15 + sign_extend (m := 64) (0x001#12)) (0x93#8) (0x87#8) (0x17#8) (0x00#8)
    hG hpc hminstret addi_a5_1h_word addi_a5_1h_notrvc
    (Vsa.Sim.DecodeTable.decode_00178793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006e84#64) (0x001#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15 _ (rX_bits_x15 _ v15
      (by rw [get?_afterNextPC σ (0x80006e84#64) _ (by decide) (by decide)]; exact hx15)) (wX_bits_x15 _ (v15 + sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e88 — `addi a1,a1,1` -/
theorem addi_a1_1h_word :
    (((0x00#8).append (0x15#8)).append (0x85#8)).append (0x93#8) = (0x00158593#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem addi_a1_1h_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x15#8)).append (0x85#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e88
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e88#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11 (v11 + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e88 hmem
  exact stepObs_alu σ i u (0x80006e88#64) vminstret (0x00158593#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v11 + sign_extend (m := 64) (0x001#12)) (0x93#8) (0x85#8) (0x15#8) (0x00#8)
    hG hpc hminstret addi_a1_1h_word addi_a1_1h_notrvc
    (Vsa.Sim.DecodeTable.decode_00158593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_gen σ (0x80006e88#64) (0x001#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) v11 _ (rX_bits_x11 _ v11
      (by rw [get?_afterNextPC σ (0x80006e88#64) _ (by decide) (by decide)]; exact hx11)) (wX_bits_x11 _ (v11 + sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e8c — `sb a4,-1(a5)` (width-1 sb) -/
theorem sb_a4_h_word :
    (((0xfe#8).append (0xe7#8)).append (0x8f#8)).append (0xa3#8) = (0xfee78fa3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sb_a4_h_notrvc :
    Sail.BitVec.extractLsb ((((0xfe#8).append (0xe7#8)).append (0x8f#8)).append (0xa3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e8c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e8c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v15 + sign_extend (m := 64) (0xfff#12)).toNat)
    (hhiram : (v15 + sign_extend (m := 64) (0xfff#12)).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v15 + sign_extend (m := 64) (0xfff#12)).toNat) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = ((afterNextPC (afterPrelude σ) (0x80006e8c#64)).mem.insert (v15 + sign_extend (m := 64) (0xfff#12)).toNat (stData 1 v14)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret ((afterNextPC (afterPrelude σ) (0x80006e8c#64)).mem.insert (v15 + sign_extend (m := 64) (0xfff#12)).toNat (stData 1 v14))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e8c hmem
  exact stepObs_store σ i u (0x80006e8c#64) vminstret (0xfee78fa3#32)
    (instruction.STORE (0xfff#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, 1))
    ((afterNextPC (afterPrelude σ) (0x80006e8c#64)).mem.insert (v15 + sign_extend (m := 64) (0xfff#12)).toNat (stData 1 v14))
    (0xa3#8) (0x8f#8) (0xe7#8) (0xfe#8)
    hG hpc hminstret sb_a4_h_word sb_a4_h_notrvc
    (Vsa.Sim.DecodeTable.decode_fee78fa3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sb σ (0x80006e8c#64) (0xfff#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) v15 v14 hG
      (rX_bits_x15 _ v15
      (by rw [get?_afterNextPC σ (0x80006e8c#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_x14 _ v14
      (by rw [get?_afterNextPC σ (0x80006e8c#64) _ (by decide) (by decide)]; exact hx14))
      hlo hhiram hhiwin)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e90 — `bnez a4,0x80006e80` (loop) -/
theorem bnez_a4_h_word :
    (((0xfe#8).append (0x07#8)).append (0x18#8)).append (0xe3#8) = (0xfe0718e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem bnez_a4_h_notrvc :
    Sail.BitVec.extractLsb ((((0xfe#8).append (0x07#8)).append (0x18#8)).append (0xe3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e90_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e90#64 : BitVec 64))
    (hv : (v14 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1ff0#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e90 hmem
  exact stepObs_branch_taken σ i u (0x80006e90#64) vminstret (0x1ff0#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BNE (0xfe0718e3#32)
    (0xe3#8) (0x18#8) (0x07#8) (0xfe#8)
    hG hpc hminstret bnez_a4_h_word bnez_a4_h_notrvc
    (Vsa.Sim.DecodeTable.decode_fe0718e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_taken σ (0x80006e90#64) (0x1ff0#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) v14 (0#64) hG hpc
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006e90#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_zero _)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_80006e90_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e90#64 : BitVec 64))
    (hv : (v14 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e90 hmem
  exact stepObs_branch_nottaken σ i u (0x80006e90#64) vminstret (0x1ff0#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BNE (0xfe0718e3#32)
    (0xe3#8) (0x18#8) (0x07#8) (0xfe#8)
    hG hpc hminstret bnez_a4_h_word bnez_a4_h_notrvc
    (Vsa.Sim.DecodeTable.decode_fe0718e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bne_nottaken σ (0x80006e90#64) (0x1ff0#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) v14 (0#64)
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80006e90#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e94 — `ret` = `jr x1,0` -/
theorem ret_e94_word :
    (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ret_e94_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e94
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e94#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e94 hmem
  exact stepObs_jr σ i u (0x80006e94#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    ret_e94_notrvc ret_e94_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ret σ (0x80006e94#64) vra hx1) htgt hi

/-! ### Site 0x80006e98 — `sb zero,7(a2)` (width-1 sb) -/
theorem sb_zero_word :
    (((0x00#8).append (0x06#8)).append (0x03#8)).append (0xa3#8) = (0x000603a3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem sb_zero_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x06#8)).append (0x03#8)).append (0xa3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e98
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e98#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v12 + sign_extend (m := 64) (0x007#12)).toNat)
    (hhiram : (v12 + sign_extend (m := 64) (0x007#12)).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v12 + sign_extend (m := 64) (0x007#12)).toNat) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = ((afterNextPC (afterPrelude σ) (0x80006e98#64)).mem.insert (v12 + sign_extend (m := 64) (0x007#12)).toNat (stData 1 (0#64))) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret ((afterNextPC (afterPrelude σ) (0x80006e98#64)).mem.insert (v12 + sign_extend (m := 64) (0x007#12)).toNat (stData 1 (0#64)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e98 hmem
  exact stepObs_store σ i u (0x80006e98#64) vminstret (0x000603a3#32)
    (instruction.STORE (0x007#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0c#5, 1))
    ((afterNextPC (afterPrelude σ) (0x80006e98#64)).mem.insert (v12 + sign_extend (m := 64) (0x007#12)).toNat (stData 1 (0#64)))
    (0xa3#8) (0x03#8) (0x06#8) (0x00#8)
    hG hpc hminstret sb_zero_word sb_zero_notrvc
    (Vsa.Sim.DecodeTable.decode_000603a3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sb σ (0x80006e98#64) (0x007#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0c#5) v12 (0#64) hG
      (rX_bits_x12 _ v12
      (by rw [get?_afterNextPC σ (0x80006e98#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_zero _)
      hlo hhiram hhiwin)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006e9c — `ret` = `jr x1,0` -/
theorem ret_e9c_word :
    (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem ret_e9c_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem site_80006e9c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrcpyLoaded σ.mem)
    (hpcv : pc = (0x80006e9c#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strcpy_at_80006e9c hmem
  exact stepObs_jr σ i u (0x80006e9c#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    ret_e9c_notrvc ret_e9c_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ret σ (0x80006e9c#64) vra hx1) htgt hi


end Vsa.Sim
