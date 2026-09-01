import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch02Part20
import Vsa.Sim.DecodeTable.Batch03Part01
import Vsa.Sim.DecodeTable.Batch03Part05
import Vsa.Sim.DecodeTable.Batch03Part20
import Vsa.Sim.DecodeTable.Batch03Part30
import Vsa.Sim.DecodeTable.Batch04Part02
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch04Part29
import Vsa.Sim.DecodeTable.Batch04Part31
import Vsa.Sim.DecodeTable.Batch07Part04
import Vsa.Sim.Code.Value_null
import Vsa.Sim.Code.Value_bool
import Vsa.Sim.Code.Value_int
import Vsa.Sim.Code.Value_str
import Vsa.Sim.Code.Value_truthy

/-!
# Layer 3 — per-site observational step lemmas for the `value_*` leaf constructors

One observational-step (`StepObs`) lemma per instruction of the five runtime-value
leaf functions (`c/src/value.c`):

* `value_null`  (3 insts @0x800027ec): `sw zero,0(a0); sd zero,8(a0); ret`
* `value_bool`  (5 insts @0x800027f8): `snez a1,a1; li a5,1; sw a1,8(a0); sw a5,0(a0); ret`
* `value_int`   (4 insts @0x8000280c): `li a5,2; sd a1,8(a0); sw a5,0(a0); ret`
* `value_str`   (4 insts @0x8000281c): `li a5,3; sd a1,8(a0); sw a5,0(a0); ret`
* `value_truthy`(12 insts @0x8000282c): kind dispatch (`lw`/`beq`/`snez`/`ld`).

**ABI (LP64, verified against the disasm + `value.c`):** a 24-byte `Value` is
returned via an **sret** pointer — the caller passes the buffer address in `a0`
(`x10`). `value_bool/int/str` take their payload in `a1` (`x11`). `value_truthy`
takes its `Value` argument **by reference** (24 > 16 bytes ⇒ not in registers):
`a0` holds a pointer to the `Value`, read back with `lw a5,0(a0)` (kind) and
`ld/lw …,8(a0)` (payload). None of these functions touch `sp`.

This file introduces **width-4 (`sw`) store sites** — a first (memcpy used `sb`/`sd`)
— following the `sb` recipe at width 4 over `vmem_write_addr_4`, plus **width-8
(`sd`)** over `vmem_write_addr_8` and **signed loads** (`lw`/`ld`) over
`execute_load_signed_char`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Width-4 / width-8 store data slices and effective addresses

A `sw rs2,off(rs1)` stores the low 4 bytes of `rs2` (`swData`); a `sd` the low
8 bytes (`sdData_val`). The effective address is `rs1 + sext off`. -/

/-- The store data slice for width 4: `extractLsb vdata 31 0` (auto-`setWidth (8*4)`). -/
abbrev swData (vdata : BitVec 64) : BitVec (8 * 4) :=
  Sail.BitVec.extractLsb vdata ((4 *i 8) -i 1) 0

/-- The store data slice for width 8: `extractLsb vdata 63 0` (auto-`setWidth (8*8)`). -/
abbrev sdData_val (vdata : BitVec 64) : BitVec (8 * 8) :=
  Sail.BitVec.extractLsb vdata ((8 *i 8) -i 1) 0

/-- The width-4 write-map: `mem` updated with 4 little-endian bytes at `a`. -/
abbrev writeMap4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((mem.insert a (d.extractLsb' 0 8)).insert (a + 1) (d.extractLsb' 8 8)).insert
    (a + 2) (d.extractLsb' 16 8)).insert (a + 3) (d.extractLsb' 24 8))

/-- The width-8 write-map: `mem` updated with 8 little-endian bytes at `a`. -/
abbrev writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((((((mem.insert a (d.extractLsb' 0 8)).insert (a + 1) (d.extractLsb' 8 8)).insert
    (a + 2) (d.extractLsb' 16 8)).insert (a + 3) (d.extractLsb' 24 8)).insert
    (a + 4) (d.extractLsb' 32 8)).insert (a + 5) (d.extractLsb' 40 8)).insert
    (a + 6) (d.extractLsb' 48 8)).insert (a + 7) (d.extractLsb' 56 8))

/-! ## Generic width-4 `sw` execute characterization

A `sw rs2,off(rs1)` at `afterNextPC (afterPrelude σ) pc`, given the base `rs1 = vbase`
and data `rs2 = vdata`, with the effective address `vbase + sext off` in RAM, above
the HTIF window, and 4-aligned, produces `sigma3_store σ pc (writeMap4 …)`. -/
theorem exec_sw (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (vbase vdata : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) imm).toNat)
    (hhiram : (vbase + sign_extend (m := 64) imm).toNat + 4 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) imm).toNat)
    (halign : (vbase + sign_extend (m := 64) imm).toNat % 4 = 0) :
    (execute (instruction.STORE (imm, rs2, rs1, 4))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_store σ pc
            (writeMap4 (afterNextPC (afterPrelude σ) pc).mem
              (vbase + sign_extend (m := 64) imm).toNat (swData vdata))) := by
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
  have hwrite := vmem_write_addr_4 (afterNextPC (afterPrelude σ) pc)
    (vbase + sign_extend (m := 64) imm) (swData vdata) initMstatus initPmpaddr
    hpriv hmstatus (by decide) hpma hcfg haddr hbase' hlo hhiram hhiwin halign
  have hchar := execute_STORE_char imm rs2 rs1 4
    vbase vdata (afterNextPC (afterPrelude σ) pc) initMstatus (0#64)
    (sigma3_store σ pc
      (writeMap4 (afterNextPC (afterPrelude σ) pc).mem
        (vbase + sign_extend (m := 64) imm).toNat (swData vdata)))
    (by decide) hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      show (vmem_write_addr (virtaddr.Virtaddr (vbase + sign_extend (m := 64) imm)) 4
          (swData vdata) (MemoryAccessType.Store mem_payload.Data) false false false).run
          (afterNextPC (afterPrelude σ) pc)
        = .ok (.Ok true) (sigma3_store σ pc
            (writeMap4 (afterNextPC (afterPrelude σ) pc).mem
              (vbase + sign_extend (m := 64) imm).toNat (swData vdata)))
      exact hwrite)
  show (execute (instruction.STORE (imm, rs2, rs1, 4))).run (afterNextPC (afterPrelude σ) pc) = _
  simp only [execute]
  exact hchar

/-! ## Generic width-8 `sd` execute characterization -/
theorem exec_sd_val (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (vbase vdata : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) imm).toNat)
    (hhiram : (vbase + sign_extend (m := 64) imm).toNat + 8 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) imm).toNat)
    (halign : (vbase + sign_extend (m := 64) imm).toNat % 8 = 0) :
    (execute (instruction.STORE (imm, rs2, rs1, 8))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_store σ pc
            (writeMap8 (afterNextPC (afterPrelude σ) pc).mem
              (vbase + sign_extend (m := 64) imm).toNat (sdData_val vdata))) := by
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
    (vbase + sign_extend (m := 64) imm) (sdData_val vdata) initMstatus initPmpaddr
    hpriv hmstatus (by decide) hpma hcfg haddr hbase' hlo hhiram hhiwin halign
  have hchar := execute_STORE_char imm rs2 rs1 8
    vbase vdata (afterNextPC (afterPrelude σ) pc) initMstatus (0#64)
    (sigma3_store σ pc
      (writeMap8 (afterNextPC (afterPrelude σ) pc).mem
        (vbase + sign_extend (m := 64) imm).toNat (sdData_val vdata)))
    (by decide) hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      show (vmem_write_addr (virtaddr.Virtaddr (vbase + sign_extend (m := 64) imm)) 8
          (sdData_val vdata) (MemoryAccessType.Store mem_payload.Data) false false false).run
          (afterNextPC (afterPrelude σ) pc)
        = .ok (.Ok true) (sigma3_store σ pc
            (writeMap8 (afterNextPC (afterPrelude σ) pc).mem
              (vbase + sign_extend (m := 64) imm).toNat (sdData_val vdata)))
      exact hwrite)
  show (execute (instruction.STORE (imm, rs2, rs1, 8))).run (afterNextPC (afterPrelude σ) pc) = _
  simp only [execute]
  exact hchar

/-! ## Byte-word / non-RVC facts for every value_* instruction word -/

theorem w_00052023 : (((0x00#8).append (0x05#8)).append (0x20#8)).append (0x23#8) = (0x00052023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00052023 : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x20#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00053423 : (((0x00#8).append (0x05#8)).append (0x34#8)).append (0x23#8) = (0x00053423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00053423 : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x34#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00008067 : (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00008067 : Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00b035b3 : (((0x00#8).append (0xb0#8)).append (0x35#8)).append (0xb3#8) = (0x00b035b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00b035b3 : Sail.BitVec.extractLsb ((((0x00#8).append (0xb0#8)).append (0x35#8)).append (0xb3#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00100793 : (((0x00#8).append (0x10#8)).append (0x07#8)).append (0x93#8) = (0x00100793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00100793 : Sail.BitVec.extractLsb ((((0x00#8).append (0x10#8)).append (0x07#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00b52423 : (((0x00#8).append (0xb5#8)).append (0x24#8)).append (0x23#8) = (0x00b52423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00b52423 : Sail.BitVec.extractLsb ((((0x00#8).append (0xb5#8)).append (0x24#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00f52023 : (((0x00#8).append (0xf5#8)).append (0x20#8)).append (0x23#8) = (0x00f52023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00f52023 : Sail.BitVec.extractLsb ((((0x00#8).append (0xf5#8)).append (0x20#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00200793 : (((0x00#8).append (0x20#8)).append (0x07#8)).append (0x93#8) = (0x00200793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00200793 : Sail.BitVec.extractLsb ((((0x00#8).append (0x20#8)).append (0x07#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00b53423 : (((0x00#8).append (0xb5#8)).append (0x34#8)).append (0x23#8) = (0x00b53423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00b53423 : Sail.BitVec.extractLsb ((((0x00#8).append (0xb5#8)).append (0x34#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00300793 : (((0x00#8).append (0x30#8)).append (0x07#8)).append (0x93#8) = (0x00300793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00300793 : Sail.BitVec.extractLsb ((((0x00#8).append (0x30#8)).append (0x07#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00052783 : (((0x00#8).append (0x05#8)).append (0x27#8)).append (0x83#8) = (0x00052783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00052783 : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x27#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00100713 : (((0x00#8).append (0x10#8)).append (0x07#8)).append (0x13#8) = (0x00100713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00100713 : Sail.BitVec.extractLsb ((((0x00#8).append (0x10#8)).append (0x07#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_02e78063 : (((0x02#8).append (0xe7#8)).append (0x80#8)).append (0x63#8) = (0x02e78063#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_02e78063 : Sail.BitVec.extractLsb ((((0x02#8).append (0xe7#8)).append (0x80#8)).append (0x63#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00200713 : (((0x00#8).append (0x20#8)).append (0x07#8)).append (0x13#8) = (0x00200713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00200713 : Sail.BitVec.extractLsb ((((0x00#8).append (0x20#8)).append (0x07#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00e78663 : (((0x00#8).append (0xe7#8)).append (0x86#8)).append (0x63#8) = (0x00e78663#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00e78663 : Sail.BitVec.extractLsb ((((0x00#8).append (0xe7#8)).append (0x86#8)).append (0x63#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00f03533 : (((0x00#8).append (0xf0#8)).append (0x35#8)).append (0x33#8) = (0x00f03533#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00f03533 : Sail.BitVec.extractLsb ((((0x00#8).append (0xf0#8)).append (0x35#8)).append (0x33#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00853503 : (((0x00#8).append (0x85#8)).append (0x35#8)).append (0x03#8) = (0x00853503#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00853503 : Sail.BitVec.extractLsb ((((0x00#8).append (0x85#8)).append (0x35#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00a03533 : (((0x00#8).append (0xa0#8)).append (0x35#8)).append (0x33#8) = (0x00a03533#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00a03533 : Sail.BitVec.extractLsb ((((0x00#8).append (0xa0#8)).append (0x35#8)).append (0x33#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00852503 : (((0x00#8).append (0x85#8)).append (0x25#8)).append (0x03#8) = (0x00852503#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00852503 : Sail.BitVec.extractLsb ((((0x00#8).append (0x85#8)).append (0x25#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## `value_null` (@0x800027ec): `sw zero,0(a0); sd zero,8(a0); ret` -/

/-- **Step 0x800027ec** (`sw zero,0(a0)`): store word 0 at `a0` (the kind tag = VAL_NULL). -/
theorem site_800027ec
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbuf : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbuf)
    (hmem : Value_nullLoaded σ.mem)
    (hpcv : pc = (0x800027ec#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbuf + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (vbuf + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbuf + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (vbuf + sign_extend (m := 64) (0x000#12)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap4 (afterNextPC (afterPrelude σ) (0x800027ec#64)).mem
        (vbuf + sign_extend (m := 64) (0x000#12)).toNat (swData (0#64)) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap4 (afterNextPC (afterPrelude σ) (0x800027ec#64)).mem
            (vbuf + sign_extend (m := 64) (0x000#12)).toNat (swData (0#64)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_null_at_800027ec hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x800027ec#64)).regs.get? Register.x10 = some vbuf := by
    rw [get?_afterNextPC σ (0x800027ec#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_store σ i u (0x800027ec#64) vminstret (0x00052023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, 4))
    (writeMap4 (afterNextPC (afterPrelude σ) (0x800027ec#64)).mem
      (vbuf + sign_extend (m := 64) (0x000#12)).toNat (swData (0#64)))
    (0x23#8) (0x20#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_00052023 nr_00052023
    (Vsa.Sim.DecodeTable.decode_00052023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sw σ (0x800027ec#64) (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
      vbuf (0#64) hG (rX_bits_x10 _ vbuf hx10₂) (rX_bits_zero _) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x800027f0** (`sd zero,8(a0)`): store dword 0 at `a0+8` (payload). -/
theorem site_800027f0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbuf : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbuf)
    (hmem : Value_nullLoaded σ.mem)
    (hpcv : pc = (0x800027f0#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbuf + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (vbuf + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbuf + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (vbuf + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x800027f0#64)).mem
        (vbuf + sign_extend (m := 64) (0x008#12)).toNat (sdData_val (0#64)) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x800027f0#64)).mem
            (vbuf + sign_extend (m := 64) (0x008#12)).toNat (sdData_val (0#64)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_null_at_800027f0 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x800027f0#64)).regs.get? Register.x10 = some vbuf := by
    rw [get?_afterNextPC σ (0x800027f0#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_store σ i u (0x800027f0#64) vminstret (0x00053423#32)
    (instruction.STORE (0x008#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x800027f0#64)).mem
      (vbuf + sign_extend (m := 64) (0x008#12)).toNat (sdData_val (0#64)))
    (0x23#8) (0x34#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_00053423 nr_00053423
    (Vsa.Sim.DecodeTable.decode_00053423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x800027f0#64) (0x008#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
      vbuf (0#64) hG (rX_bits_x10 _ vbuf hx10₂) (rX_bits_zero _) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x800027f4** (`ret`): PC → bit-0-cleared `ra`. -/
theorem site_800027f4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : Value_nullLoaded σ.mem)
    (hpcv : pc = (0x800027f4#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_null_at_800027f4 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x800027f4#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x800027f4#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x800027f4#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x800027f4#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00008067 w_00008067
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

/-! ## `value_bool` (@0x800027f8): `snez a1,a1; li a5,1; sw a1,8(a0); sw a5,0(a0); ret` -/

/-- `execute (RTYPE sltu x11,x0,x11)` (`snez a1,a1`): `rs1 = x0` reads 0, so the
value is `zero_extend (bool_to_bit (0 <u a1)) = (a1 ≠ 0 ? 1 : 0)`; writes `x11`. -/
theorem exec_snez_a1 (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0b#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, rop.SLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x11 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v11)))) := by
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_rtype_sltu_char (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0b#5)
    (0#64) v11 (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x11 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v11))))
    (rX_bits_zero _) (rX_bits_x11 _ v11 hx11₂)
    (wX_bits_x11 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v11))))

/-- **Step 0x800027f8** (`snez a1,a1`). Writes `x11 := (a1 ≠ 0 ? 1 : 0)`. -/
theorem site_800027f8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Value_boolLoaded σ.mem)
    (hpcv : pc = (0x800027f8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v11)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_bool_at_800027f8 hmem
  exact stepObs_alu σ i u (0x800027f8#64) vminstret (0x00b035b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0b#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, rop.SLTU))
    Register.x11 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v11)))
    (0xb3#8) (0x35#8) (0xb0#8) (0x00#8)
    hG hpc hminstret w_00b035b3 nr_00b035b3
    (Vsa.Sim.DecodeTable.decode_00b035b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_snez_a1 σ (0x800027f8#64) v11 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- `execute (ITYPE addi x15,x0,k)` (`li a5,k`): `rs1 = x0` reads 0; writes `x15 := sext k`. -/
theorem exec_li_a5 (σ : MState) (pc : BitVec 64) (k : BitVec 12) :
    (execute (instruction.ITYPE (k, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 ((0#64) + sign_extend (m := 64) k)) :=
  execute_itype_addi_char k (regidx.Regidx 0x00#5) (regidx.Regidx 0x0f#5) (0#64)
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 ((0#64) + sign_extend (m := 64) k))
    (rX_bits_zero _) (wX_bits_x15 _ ((0#64) + sign_extend (m := 64) k))

/-- **Step 0x800027fc** (`li a5,1`). Writes `x15 := 1`. -/
theorem site_800027fc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Value_boolLoaded σ.mem)
    (hpcv : pc = (0x800027fc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 ((0#64) + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_bool_at_800027fc hmem
  exact stepObs_alu σ i u (0x800027fc#64) vminstret (0x00100793#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 ((0#64) + sign_extend (m := 64) (0x001#12)) (0x93#8) (0x07#8) (0x10#8) (0x00#8)
    hG hpc hminstret w_00100793 nr_00100793
    (Vsa.Sim.DecodeTable.decode_00100793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_li_a5 σ (0x800027fc#64) (0x001#12))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002800** (`sw a1,8(a0)`): store low 4 bytes of `a1` at `a0+8` (bool payload). -/
theorem site_80002800
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbuf v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbuf)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Value_boolLoaded σ.mem)
    (hpcv : pc = (0x80002800#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbuf + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (vbuf + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbuf + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (vbuf + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap4 (afterNextPC (afterPrelude σ) (0x80002800#64)).mem
        (vbuf + sign_extend (m := 64) (0x008#12)).toNat (swData v11) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap4 (afterNextPC (afterPrelude σ) (0x80002800#64)).mem
            (vbuf + sign_extend (m := 64) (0x008#12)).toNat (swData v11))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_bool_at_80002800 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002800#64)).regs.get? Register.x10 = some vbuf := by
    rw [get?_afterNextPC σ (0x80002800#64) _ (by decide) (by decide)]; exact hx10
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x80002800#64)).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ (0x80002800#64) _ (by decide) (by decide)]; exact hx11
  exact stepObs_store σ i u (0x80002800#64) vminstret (0x00b52423#32)
    (instruction.STORE (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, 4))
    (writeMap4 (afterNextPC (afterPrelude σ) (0x80002800#64)).mem
      (vbuf + sign_extend (m := 64) (0x008#12)).toNat (swData v11))
    (0x23#8) (0x24#8) (0xb5#8) (0x00#8)
    hG hpc hminstret w_00b52423 nr_00b52423
    (Vsa.Sim.DecodeTable.decode_00b52423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sw σ (0x80002800#64) (0x008#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5)
      vbuf v11 hG (rX_bits_x10 _ vbuf hx10₂) (rX_bits_x11 _ v11 hx11₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002804** (`sw a5,0(a0)`): store low 4 bytes of `a5` at `a0` (kind tag). -/
theorem site_80002804
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbuf v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbuf)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Value_boolLoaded σ.mem)
    (hpcv : pc = (0x80002804#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbuf + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (vbuf + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbuf + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (vbuf + sign_extend (m := 64) (0x000#12)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap4 (afterNextPC (afterPrelude σ) (0x80002804#64)).mem
        (vbuf + sign_extend (m := 64) (0x000#12)).toNat (swData v15) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap4 (afterNextPC (afterPrelude σ) (0x80002804#64)).mem
            (vbuf + sign_extend (m := 64) (0x000#12)).toNat (swData v15))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_bool_at_80002804 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002804#64)).regs.get? Register.x10 = some vbuf := by
    rw [get?_afterNextPC σ (0x80002804#64) _ (by decide) (by decide)]; exact hx10
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002804#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002804#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_store σ i u (0x80002804#64) vminstret (0x00f52023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0a#5, 4))
    (writeMap4 (afterNextPC (afterPrelude σ) (0x80002804#64)).mem
      (vbuf + sign_extend (m := 64) (0x000#12)).toNat (swData v15))
    (0x23#8) (0x20#8) (0xf5#8) (0x00#8)
    hG hpc hminstret w_00f52023 nr_00f52023
    (Vsa.Sim.DecodeTable.decode_00f52023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sw σ (0x80002804#64) (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0a#5)
      vbuf v15 hG (rX_bits_x10 _ vbuf hx10₂) (rX_bits_x15 _ v15 hx15₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002808** (`ret`). -/
theorem site_80002808
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : Value_boolLoaded σ.mem)
    (hpcv : pc = (0x80002808#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_bool_at_80002808 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80002808#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80002808#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80002808#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80002808#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00008067 w_00008067
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

/-! ## `value_int` (@0x8000280c): `li a5,2; sd a1,8(a0); sw a5,0(a0); ret` -/

/-- **Step 0x8000280c** (`li a5,2`). Writes `x15 := 2`. -/
theorem site_8000280c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Value_intLoaded σ.mem)
    (hpcv : pc = (0x8000280c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 ((0#64) + sign_extend (m := 64) (0x002#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_int_at_8000280c hmem
  exact stepObs_alu σ i u (0x8000280c#64) vminstret (0x00200793#32)
    (instruction.ITYPE (0x002#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 ((0#64) + sign_extend (m := 64) (0x002#12)) (0x93#8) (0x07#8) (0x20#8) (0x00#8)
    hG hpc hminstret w_00200793 nr_00200793
    (Vsa.Sim.DecodeTable.decode_00200793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_li_a5 σ (0x8000280c#64) (0x002#12))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002810** (`sd a1,8(a0)`): store the 8-byte int payload `a1` at `a0+8`. -/
theorem site_80002810
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbuf v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbuf)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Value_intLoaded σ.mem)
    (hpcv : pc = (0x80002810#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbuf + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (vbuf + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbuf + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (vbuf + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002810#64)).mem
        (vbuf + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v11) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002810#64)).mem
            (vbuf + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v11))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_int_at_80002810 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002810#64)).regs.get? Register.x10 = some vbuf := by
    rw [get?_afterNextPC σ (0x80002810#64) _ (by decide) (by decide)]; exact hx10
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x80002810#64)).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ (0x80002810#64) _ (by decide) (by decide)]; exact hx11
  exact stepObs_store σ i u (0x80002810#64) vminstret (0x00b53423#32)
    (instruction.STORE (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002810#64)).mem
      (vbuf + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v11))
    (0x23#8) (0x34#8) (0xb5#8) (0x00#8)
    hG hpc hminstret w_00b53423 nr_00b53423
    (Vsa.Sim.DecodeTable.decode_00b53423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002810#64) (0x008#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5)
      vbuf v11 hG (rX_bits_x10 _ vbuf hx10₂) (rX_bits_x11 _ v11 hx11₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002814** (`sw a5,0(a0)`): store kind tag (=2) at `a0`. -/
theorem site_80002814
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbuf v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbuf)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Value_intLoaded σ.mem)
    (hpcv : pc = (0x80002814#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbuf + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (vbuf + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbuf + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (vbuf + sign_extend (m := 64) (0x000#12)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap4 (afterNextPC (afterPrelude σ) (0x80002814#64)).mem
        (vbuf + sign_extend (m := 64) (0x000#12)).toNat (swData v15) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap4 (afterNextPC (afterPrelude σ) (0x80002814#64)).mem
            (vbuf + sign_extend (m := 64) (0x000#12)).toNat (swData v15))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_int_at_80002814 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002814#64)).regs.get? Register.x10 = some vbuf := by
    rw [get?_afterNextPC σ (0x80002814#64) _ (by decide) (by decide)]; exact hx10
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002814#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002814#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_store σ i u (0x80002814#64) vminstret (0x00f52023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0a#5, 4))
    (writeMap4 (afterNextPC (afterPrelude σ) (0x80002814#64)).mem
      (vbuf + sign_extend (m := 64) (0x000#12)).toNat (swData v15))
    (0x23#8) (0x20#8) (0xf5#8) (0x00#8)
    hG hpc hminstret w_00f52023 nr_00f52023
    (Vsa.Sim.DecodeTable.decode_00f52023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sw σ (0x80002814#64) (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0a#5)
      vbuf v15 hG (rX_bits_x10 _ vbuf hx10₂) (rX_bits_x15 _ v15 hx15₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002818** (`ret`). -/
theorem site_80002818
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : Value_intLoaded σ.mem)
    (hpcv : pc = (0x80002818#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_int_at_80002818 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80002818#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80002818#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80002818#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80002818#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00008067 w_00008067
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

/-! ## `value_str` (@0x8000281c): `li a5,3; sd a1,8(a0); sw a5,0(a0); ret` -/

/-- **Step 0x8000281c** (`li a5,3`). Writes `x15 := 3`. -/
theorem site_8000281c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Value_strLoaded σ.mem)
    (hpcv : pc = (0x8000281c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 ((0#64) + sign_extend (m := 64) (0x003#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_str_at_8000281c hmem
  exact stepObs_alu σ i u (0x8000281c#64) vminstret (0x00300793#32)
    (instruction.ITYPE (0x003#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 ((0#64) + sign_extend (m := 64) (0x003#12)) (0x93#8) (0x07#8) (0x30#8) (0x00#8)
    hG hpc hminstret w_00300793 nr_00300793
    (Vsa.Sim.DecodeTable.decode_00300793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_li_a5 σ (0x8000281c#64) (0x003#12))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002820** (`sd a1,8(a0)`): store the 8-byte string pointer `a1` at `a0+8`. -/
theorem site_80002820
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbuf v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbuf)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Value_strLoaded σ.mem)
    (hpcv : pc = (0x80002820#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbuf + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (vbuf + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbuf + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (vbuf + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002820#64)).mem
        (vbuf + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v11) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002820#64)).mem
            (vbuf + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v11))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_str_at_80002820 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002820#64)).regs.get? Register.x10 = some vbuf := by
    rw [get?_afterNextPC σ (0x80002820#64) _ (by decide) (by decide)]; exact hx10
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x80002820#64)).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ (0x80002820#64) _ (by decide) (by decide)]; exact hx11
  exact stepObs_store σ i u (0x80002820#64) vminstret (0x00b53423#32)
    (instruction.STORE (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002820#64)).mem
      (vbuf + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v11))
    (0x23#8) (0x34#8) (0xb5#8) (0x00#8)
    hG hpc hminstret w_00b53423 nr_00b53423
    (Vsa.Sim.DecodeTable.decode_00b53423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002820#64) (0x008#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5)
      vbuf v11 hG (rX_bits_x10 _ vbuf hx10₂) (rX_bits_x11 _ v11 hx11₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002824** (`sw a5,0(a0)`): store kind tag (=3) at `a0`. -/
theorem site_80002824
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbuf v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbuf)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Value_strLoaded σ.mem)
    (hpcv : pc = (0x80002824#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vbuf + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (vbuf + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vbuf + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (vbuf + sign_extend (m := 64) (0x000#12)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap4 (afterNextPC (afterPrelude σ) (0x80002824#64)).mem
        (vbuf + sign_extend (m := 64) (0x000#12)).toNat (swData v15) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap4 (afterNextPC (afterPrelude σ) (0x80002824#64)).mem
            (vbuf + sign_extend (m := 64) (0x000#12)).toNat (swData v15))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_str_at_80002824 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002824#64)).regs.get? Register.x10 = some vbuf := by
    rw [get?_afterNextPC σ (0x80002824#64) _ (by decide) (by decide)]; exact hx10
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002824#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002824#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_store σ i u (0x80002824#64) vminstret (0x00f52023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0a#5, 4))
    (writeMap4 (afterNextPC (afterPrelude σ) (0x80002824#64)).mem
      (vbuf + sign_extend (m := 64) (0x000#12)).toNat (swData v15))
    (0x23#8) (0x20#8) (0xf5#8) (0x00#8)
    hG hpc hminstret w_00f52023 nr_00f52023
    (Vsa.Sim.DecodeTable.decode_00f52023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sw σ (0x80002824#64) (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0a#5)
      vbuf v15 hG (rX_bits_x10 _ vbuf hx10₂) (rX_bits_x15 _ v15 hx15₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002828** (`ret`). -/
theorem site_80002828
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : Value_strLoaded σ.mem)
    (hpcv : pc = (0x80002828#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_str_at_80002828 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80002828#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80002828#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80002828#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80002828#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00008067 w_00008067
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

/-! ## `value_truthy` (@0x8000282c): kind dispatch (`lw`/`beq`/`snez`/`ld`)

**ABI:** the 24-byte `Value` argument is passed **by reference** (24 > 16 ⇒ not in
registers): `a0` holds a pointer to the caller's `Value`. `lw a5,0(a0)` reads the
kind tag (4 bytes); `beq a5,{1,2}` dispatches; `ld a0,8(a0)` / `lw a0,8(a0)` reads
the payload. The result in `a0`:
* kind = 1 (bool): `lw a0,8(a0)` — the (4-byte) bool payload;
* kind = 2 (int):  `ld a0,8(a0); snez a0,a0` — `(i ≠ 0 ? 1 : 0)`;
* else (0/3/4/5):  `snez a0,a5` where `a5 = kind` — `0` for null, `1` for str/fn/native.

This matches `Value.truthy` exactly (`c/src/value.c` vs `Vsa/While/Semantics.lean`).
-/

/-- Generic signed 4-byte load `lw rd,off(rs1)` at `afterNextPC …`: reads the LE
word `(((b3.append b2).append b1).append b0)` at `vbase + sext off` and writes
`sign_extend word` to `rd`. -/
theorem exec_lw (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (sign_extend (m := 64)
        ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))).run (afterNextPC (afterPrelude σ) pc)
      = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 4 = 0)
    (h0 : σ.mem[(vbase + sign_extend (m := 64) off).toNat]? = some b0)
    (h1 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 3]? = some b3) :
    (execute (instruction.LOAD (off, rs1, rd, false, 4))).run (afterNextPC (afterPrelude σ) pc)
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
  have hread := vmem_read_data_four (afterNextPC (afterPrelude σ) pc) rs1
    (sign_extend (m := 64) off) vbase b0 b1 b2 b3 initMstatus initPmpaddr
    hpriv hmstatus (by decide) hseccfg hpma hcfg haddr hbase' hrs1 hlo hhiram hhtif halign
    (by rw [mem_afterNextPC]; exact h0) (by rw [mem_afterNextPC]; exact h1)
    (by rw [mem_afterNextPC]; exact h2) (by rw [mem_afterNextPC]; exact h3)
  exact execute_load_signed_char off rs1 rd 4
    ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)) (afterNextPC (afterPrelude σ) pc)
    σ' (by decide) hread hwr

/-- Generic **unsigned** 4-byte load `lwu rd,off(rs1)` at `afterNextPC …`: reads
the LE word `(((b3.append b2).append b1).append b0)` at `vbase + sext off` and
writes `zero_extend word` to `rd`.  Identical to `exec_lw` except `is_unsigned =
true` and the write value is `zero_extend` (via `execute_load_unsigned_char`);
the underlying `vmem_read` at width 4 is the same, so the read side is shared. -/
theorem exec_lwu (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (zero_extend (m := 64)
        ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))).run (afterNextPC (afterPrelude σ) pc)
      = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 4 = 0)
    (h0 : σ.mem[(vbase + sign_extend (m := 64) off).toNat]? = some b0)
    (h1 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 3]? = some b3) :
    (execute (instruction.LOAD (off, rs1, rd, true, 4))).run (afterNextPC (afterPrelude σ) pc)
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
  have hread := vmem_read_data_four (afterNextPC (afterPrelude σ) pc) rs1
    (sign_extend (m := 64) off) vbase b0 b1 b2 b3 initMstatus initPmpaddr
    hpriv hmstatus (by decide) hseccfg hpma hcfg haddr hbase' hrs1 hlo hhiram hhtif halign
    (by rw [mem_afterNextPC]; exact h0) (by rw [mem_afterNextPC]; exact h1)
    (by rw [mem_afterNextPC]; exact h2) (by rw [mem_afterNextPC]; exact h3)
  exact execute_load_unsigned_char off rs1 rd 4
    ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)) (afterNextPC (afterPrelude σ) pc)
    σ' (by decide) hread hwr

/-- Generic signed 8-byte load `ld rd,off(rs1)` at `afterNextPC …`: reads the LE
dword at `vbase + sext off` and writes it (sign_extend of a full 64-bit value is
itself) to `rd`. -/
theorem exec_ld (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8)))).run (afterNextPC (afterPrelude σ) pc)
      = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 8 = 0)
    (h0 : σ.mem[(vbase + sign_extend (m := 64) off).toNat]? = some b0)
    (h1 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 3]? = some b3)
    (h4 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 4]? = some b4)
    (h5 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 5]? = some b5)
    (h6 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 6]? = some b6)
    (h7 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 7]? = some b7) :
    (execute (instruction.LOAD (off, rs1, rd, false, 8))).run (afterNextPC (afterPrelude σ) pc)
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
  have hread := vmem_read_data_eight (afterNextPC (afterPrelude σ) pc) rs1
    (sign_extend (m := 64) off) vbase b0 b1 b2 b3 b4 b5 b6 b7 initMstatus initPmpaddr
    hpriv hmstatus (by decide) hseccfg hpma hcfg haddr hbase' hrs1 hlo hhiram hhtif halign
    (by rw [mem_afterNextPC]; exact h0) (by rw [mem_afterNextPC]; exact h1)
    (by rw [mem_afterNextPC]; exact h2) (by rw [mem_afterNextPC]; exact h3)
    (by rw [mem_afterNextPC]; exact h4) (by rw [mem_afterNextPC]; exact h5)
    (by rw [mem_afterNextPC]; exact h6) (by rw [mem_afterNextPC]; exact h7)
  exact execute_load_signed_char off rs1 rd 8
    ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
      : BitVec (8 * 8)) (afterNextPC (afterPrelude σ) pc)
    σ' (by decide) hread hwr

/-- **Step 0x8000282c** (`lw a5,0(a0)`): read the kind tag (4 bytes) at `a0`. Writes
`x15 := sign_extend (kind word)`. -/
theorem site_8000282c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbuf : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbuf)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x8000282c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbuf + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (vbuf + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbuf + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbuf + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (vbuf + sign_extend (m := 64) (0x000#12)).toNat % 4 = 0)
    (h0 : σ.mem[(vbuf + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (h1 : σ.mem[(vbuf + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbuf + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbuf + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_8000282c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x8000282c#64)).regs.get? Register.x10 = some vbuf := by
    rw [get?_afterNextPC σ (0x8000282c#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x8000282c#64) vminstret (0x00052783#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0f#5, false, 4))
    Register.x15 (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))
    (0x83#8) (0x27#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_00052783 nr_00052783
    (Vsa.Sim.DecodeTable.decode_00052783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x8000282c#64) (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x8000282c#64) Register.x15
        (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      vbuf b0 b1 b2 b3 hG (rX_bits_x10 _ vbuf hx10₂)
      (wX_bits_x15 _ (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002830** (`li a4,1`). Writes `x14 := 1`. -/
theorem site_80002830
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x80002830#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 ((0#64) + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_80002830 hmem
  exact stepObs_alu σ i u (0x80002830#64) vminstret (0x00100713#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0e#5, iop.ADDI))
    Register.x14 ((0#64) + sign_extend (m := 64) (0x001#12)) (0x13#8) (0x07#8) (0x10#8) (0x00#8)
    hG hpc hminstret w_00100713 nr_00100713
    (Vsa.Sim.DecodeTable.decode_00100713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0e#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x80002830#64))
      (sigma3_alu σ (0x80002830#64) Register.x14 ((0#64) + sign_extend (m := 64) (0x001#12)))
      (rX_bits_zero _) (wX_bits_x14 _ ((0#64) + sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002834, not taken** (`beq a5,a4`, kind ≠ 1): fall to 0x80002838. -/
theorem site_80002834_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x80002834#64 : BitVec 64)) (hv : (v15 == v14) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_80002834 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002834#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002834#64) _ (by decide) (by decide)]; exact hx15
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x80002834#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x80002834#64) _ (by decide) (by decide)]; exact hx14
  exact stepObs_branch_nottaken σ i u (0x80002834#64) vminstret (0x0020#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) bop.BEQ (0x02e78063#32)
    (0x63#8) (0x80#8) (0xe7#8) (0x02#8)
    hG hpc hminstret w_02e78063 nr_02e78063
    (Vsa.Sim.DecodeTable.decode_02e78063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_nottaken (0x0020#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5)
      v15 v14 (afterNextPC (afterPrelude σ) (0x80002834#64))
      (rX_bits_x15 _ v15 hx15₂) (rX_bits_x14 _ v14 hx14₂) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002834, taken** (`beq a5,a4`, kind = 1 / bool): branch to 0x80002854. -/
theorem site_80002834_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x80002834#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x0020#13)).toNat % 4 = 0)
    (hv : (v15 == v14) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0020#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_80002834 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002834#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002834#64) _ (by decide) (by decide)]; exact hx15
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x80002834#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x80002834#64) _ (by decide) (by decide)]; exact hx14
  have hpc₂ : (afterNextPC (afterPrelude σ) (0x80002834#64)).regs.get? Register.PC
      = some (0x80002834#64 : BitVec 64) := by
    rw [get?_afterNextPC σ (0x80002834#64) _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) (0x80002834#64)).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ (0x80002834#64) _ (by decide) (by decide)]; exact hG.misa
  exact stepObs_branch_taken σ i u (0x80002834#64) vminstret (0x0020#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) bop.BEQ (0x02e78063#32)
    (0x63#8) (0x80#8) (0xe7#8) (0x02#8)
    hG hpc hminstret w_02e78063 nr_02e78063
    (Vsa.Sim.DecodeTable.decode_02e78063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_taken (0x0020#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5)
      v15 v14 (0x80002834#64) initMisa (afterNextPC (afterPrelude σ) (0x80002834#64))
      (rX_bits_x15 _ v15 hx15₂) (rX_bits_x14 _ v14 hx14₂) hpc₂ hmisa₂ htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002838** (`li a4,2`). Writes `x14 := 2`. -/
theorem site_80002838
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x80002838#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 ((0#64) + sign_extend (m := 64) (0x002#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_80002838 hmem
  exact stepObs_alu σ i u (0x80002838#64) vminstret (0x00200713#32)
    (instruction.ITYPE (0x002#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0e#5, iop.ADDI))
    Register.x14 ((0#64) + sign_extend (m := 64) (0x002#12)) (0x13#8) (0x07#8) (0x20#8) (0x00#8)
    hG hpc hminstret w_00200713 nr_00200713
    (Vsa.Sim.DecodeTable.decode_00200713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x002#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0e#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x80002838#64))
      (sigma3_alu σ (0x80002838#64) Register.x14 ((0#64) + sign_extend (m := 64) (0x002#12)))
      (rX_bits_zero _) (wX_bits_x14 _ ((0#64) + sign_extend (m := 64) (0x002#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x8000283c, not taken** (`beq a5,a4`, kind ≠ 2): fall to 0x80002840. -/
theorem site_8000283c_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x8000283c#64 : BitVec 64)) (hv : (v15 == v14) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_8000283c hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x8000283c#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x8000283c#64) _ (by decide) (by decide)]; exact hx15
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x8000283c#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x8000283c#64) _ (by decide) (by decide)]; exact hx14
  exact stepObs_branch_nottaken σ i u (0x8000283c#64) vminstret (0x000c#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) bop.BEQ (0x00e78663#32)
    (0x63#8) (0x86#8) (0xe7#8) (0x00#8)
    hG hpc hminstret w_00e78663 nr_00e78663
    (Vsa.Sim.DecodeTable.decode_00e78663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_nottaken (0x000c#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5)
      v15 v14 (afterNextPC (afterPrelude σ) (0x8000283c#64))
      (rX_bits_x15 _ v15 hx15₂) (rX_bits_x14 _ v14 hx14₂) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x8000283c, taken** (`beq a5,a4`, kind = 2 / int): branch to 0x80002848. -/
theorem site_8000283c_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x8000283c#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x000c#13)).toNat % 4 = 0)
    (hv : (v15 == v14) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x000c#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_8000283c hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x8000283c#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x8000283c#64) _ (by decide) (by decide)]; exact hx15
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x8000283c#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x8000283c#64) _ (by decide) (by decide)]; exact hx14
  have hpc₂ : (afterNextPC (afterPrelude σ) (0x8000283c#64)).regs.get? Register.PC
      = some (0x8000283c#64 : BitVec 64) := by
    rw [get?_afterNextPC σ (0x8000283c#64) _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) (0x8000283c#64)).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ (0x8000283c#64) _ (by decide) (by decide)]; exact hG.misa
  exact stepObs_branch_taken σ i u (0x8000283c#64) vminstret (0x000c#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) bop.BEQ (0x00e78663#32)
    (0x63#8) (0x86#8) (0xe7#8) (0x00#8)
    hG hpc hminstret w_00e78663 nr_00e78663
    (Vsa.Sim.DecodeTable.decode_00e78663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_taken (0x000c#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5)
      v15 v14 (0x8000283c#64) initMisa (afterNextPC (afterPrelude σ) (0x8000283c#64))
      (rX_bits_x15 _ v15 hx15₂) (rX_bits_x14 _ v14 hx14₂) hpc₂ hmisa₂ htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002840** (`snez a0,a5`): default branch. Writes `x10 := (a5 ≠ 0 ? 1 : 0)`;
since `a5 = kind`, this is `0` for null (kind 0) and `1` for str/fn/native (kind ≥ 3). -/
theorem site_80002840
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x80002840#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_80002840 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002840#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002840#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_alu σ i u (0x80002840#64) vminstret (0x00f03533#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, rop.SLTU))
    Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15)))
    (0x33#8) (0x35#8) (0xf0#8) (0x00#8)
    hG hpc hminstret w_00f03533 nr_00f03533
    (Vsa.Sim.DecodeTable.decode_00f03533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_sltu_char (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
      (0#64) v15 (afterNextPC (afterPrelude σ) (0x80002840#64))
      (sigma3_alu σ (0x80002840#64) Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15))))
      (rX_bits_zero _) (rX_bits_x15 _ v15 hx15₂)
      (wX_bits_x10 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15)))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002844** (`ret`). -/
theorem site_80002844
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x80002844#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_80002844 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80002844#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80002844#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80002844#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80002844#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00008067 w_00008067
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

/-- **Step 0x80002848** (`ld a0,8(a0)`): read the 8-byte int payload at `a0+8`. Writes
`x10 := payload` (sign_extend of a full 64-bit value is itself). -/
theorem site_80002848
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbuf : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbuf)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x80002848#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbuf + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vbuf + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbuf + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbuf + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vbuf + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vbuf + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(vbuf + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbuf + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbuf + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vbuf + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vbuf + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vbuf + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vbuf + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_80002848 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002848#64)).regs.get? Register.x10 = some vbuf := by
    rw [get?_afterNextPC σ (0x80002848#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80002848#64) vminstret (0x00853503#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, false, 8))
    Register.x10 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x35#8) (0x85#8) (0x00#8)
    hG hpc hminstret w_00853503 nr_00853503
    (Vsa.Sim.DecodeTable.decode_00853503 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002848#64) (0x008#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x80002848#64) Register.x10 (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      vbuf b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ vbuf hx10₂)
      (wX_bits_x10 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x8000284c** (`snez a0,a0`): int case final. Writes `x10 := (a0 ≠ 0 ? 1 : 0)`. -/
theorem site_8000284c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x8000284c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v10)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_8000284c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x8000284c#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x8000284c#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x8000284c#64) vminstret (0x00a03533#32)
    (instruction.RTYPE (regidx.Regidx 0x0a#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, rop.SLTU))
    Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v10)))
    (0x33#8) (0x35#8) (0xa0#8) (0x00#8)
    hG hpc hminstret w_00a03533 nr_00a03533
    (Vsa.Sim.DecodeTable.decode_00a03533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_sltu_char (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
      (0#64) v10 (afterNextPC (afterPrelude σ) (0x8000284c#64))
      (sigma3_alu σ (0x8000284c#64) Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v10))))
      (rX_bits_zero _) (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x10 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v10)))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002850** (`ret`). -/
theorem site_80002850
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x80002850#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_80002850 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80002850#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80002850#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80002850#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80002850#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00008067 w_00008067
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

/-- **Step 0x80002854** (`lw a0,8(a0)`): bool case. Reads the 4-byte bool payload at
`a0+8`; writes `x10 := sign_extend (payload word)`. -/
theorem site_80002854
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbuf : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbuf)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x80002854#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbuf + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vbuf + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbuf + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbuf + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vbuf + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (h0 : σ.mem[(vbuf + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(vbuf + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbuf + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbuf + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_80002854 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002854#64)).regs.get? Register.x10 = some vbuf := by
    rw [get?_afterNextPC σ (0x80002854#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80002854#64) vminstret (0x00852503#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, false, 4))
    Register.x10 (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))
    (0x03#8) (0x25#8) (0x85#8) (0x00#8)
    hG hpc hminstret w_00852503 nr_00852503
    (Vsa.Sim.DecodeTable.decode_00852503 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x80002854#64) (0x008#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x80002854#64) Register.x10
        (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      vbuf b0 b1 b2 b3 hG (rX_bits_x10 _ vbuf hx10₂)
      (wX_bits_x10 _ (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Step 0x80002858** (`ret`). -/
theorem site_80002858
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : Value_truthyLoaded σ.mem)
    (hpcv : pc = (0x80002858#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_truthy_at_80002858 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80002858#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80002858#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80002858#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80002858#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00008067 w_00008067
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

end Vsa.Sim
