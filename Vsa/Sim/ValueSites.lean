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

/-! ## `value_null` (@0x800027ec): `sw zero,0(a0); sd zero,8(a0); ret` -/

/-! ## `value_bool` (@0x800027f8): `snez a1,a1; li a5,1; sw a1,8(a0); sw a5,0(a0); ret` -/

/-! ## `value_int` (@0x8000280c): `li a5,2; sd a1,8(a0); sw a5,0(a0); ret` -/

/-! ## `value_str` (@0x8000281c): `li a5,3; sd a1,8(a0); sw a5,0(a0); ret` -/

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

end Vsa.Sim
