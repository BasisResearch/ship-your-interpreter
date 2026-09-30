import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeNF
import Vsa.Sim.Code.Value_null
import Vsa.Sim.Code.Value_bool
import Vsa.Sim.Code.Value_int
import Vsa.Sim.Code.Value_str
import Vsa.Sim.Code.Value_truthy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev swData (vdata : BitVec 64) : BitVec (8 * 4) :=
  Sail.BitVec.extractLsb vdata ((4 *i 8) -i 1) 0

abbrev sdData_val (vdata : BitVec 64) : BitVec (8 * 8) :=
  Sail.BitVec.extractLsb vdata ((8 *i 8) -i 1) 0

abbrev writeMap4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((mem.insert a (d.extractLsb' 0 8)).insert (a + 1) (d.extractLsb' 8 8)).insert
    (a + 2) (d.extractLsb' 16 8)).insert (a + 3) (d.extractLsb' 24 8))

abbrev writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((((((mem.insert a (d.extractLsb' 0 8)).insert (a + 1) (d.extractLsb' 8 8)).insert
    (a + 2) (d.extractLsb' 16 8)).insert (a + 3) (d.extractLsb' 24 8)).insert
    (a + 4) (d.extractLsb' 32 8)).insert (a + 5) (d.extractLsb' 40 8)).insert
    (a + 6) (d.extractLsb' 48 8)).insert (a + 7) (d.extractLsb' 56 8))

structure SiteGood (σ : MState) (pc : BitVec 64) : Prop where
  priv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
    = some (Privilege.Machine : RegisterType Register.cur_privilege)
  mstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus
  seccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64)
  pma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
    = some (initPmaRegions : RegisterType Register.pma_regions)
  cfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
    = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n)
  pmpaddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr
  tohost : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
    = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base)

theorem siteGood_of_good (σ : MState) (pc : BitVec 64) (hG : GoodState σ) : SiteGood σ pc where
  priv := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  mstatus := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  seccfg := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  pma := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  cfg := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  pmpaddr := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  tohost := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base

theorem exec_store_w (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (w : Nat) (vbase vdata : BitVec 64) (σ3 : MState) (hw : w ≤ 8) (hS : SiteGood σ pc)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (hwrite : (vmem_write_addr (virtaddr.Virtaddr (vbase + sign_extend (m := 64) imm)) w
        (Sail.BitVec.extractLsb vdata ((w *i 8) -i 1) 0)
        (MemoryAccessType.Store mem_payload.Data) false false false).run
        (afterNextPC (afterPrelude σ) pc) = .ok (.Ok true) σ3) :
    (execute (instruction.STORE (imm, rs2, rs1, w))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ3 := by
  simp only [execute]
  exact execute_STORE_char imm rs2 rs1 w vbase vdata _ initMstatus (0#64) σ3 hw
    hS.priv hS.mstatus (by decide) hS.seccfg (by decide) hrs2 hrs1 hwrite

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
              (vbase + sign_extend (m := 64) imm).toNat (swData vdata))) :=
  have hS := siteGood_of_good σ pc hG
  exec_store_w σ pc imm rs2 rs1 4 vbase vdata _ (by decide) hS hrs1 hrs2
    (vmem_write_addr_4 (afterNextPC (afterPrelude σ) pc)
      (vbase + sign_extend (m := 64) imm) (swData vdata) initMstatus initPmpaddr
      hS.priv hS.mstatus (by decide) hS.pma hS.cfg hS.pmpaddr hS.tohost hlo hhiram hhiwin halign)

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
              (vbase + sign_extend (m := 64) imm).toNat (sdData_val vdata))) :=
  have hS := siteGood_of_good σ pc hG
  exec_store_w σ pc imm rs2 rs1 8 vbase vdata _ (by decide) hS hrs1 hrs2
    (vmem_write_addr_8 (afterNextPC (afterPrelude σ) pc)
      (vbase + sign_extend (m := 64) imm) (sdData_val vdata) initMstatus initPmpaddr
      hS.priv hS.mstatus (by decide) hS.pma hS.cfg hS.pmpaddr hS.tohost hlo hhiram hhiwin halign)

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
      = .ok RETIRE_SUCCESS σ' :=
  have hS := siteGood_of_good σ pc hG
  execute_load_signed_char off rs1 rd 8 _ (afterNextPC (afterPrelude σ) pc) σ' (by decide)
    (vmem_read_data_eight (afterNextPC (afterPrelude σ) pc) rs1
      (sign_extend (m := 64) off) vbase b0 b1 b2 b3 b4 b5 b6 b7 initMstatus initPmpaddr
      hS.priv hS.mstatus (by decide) hS.seccfg hS.pma hS.cfg hS.pmpaddr hS.tohost
      hrs1 hlo hhiram hhtif halign
      (by rw [mem_afterNextPC]; exact h0) (by rw [mem_afterNextPC]; exact h1)
      (by rw [mem_afterNextPC]; exact h2) (by rw [mem_afterNextPC]; exact h3)
      (by rw [mem_afterNextPC]; exact h4) (by rw [mem_afterNextPC]; exact h5)
      (by rw [mem_afterNextPC]; exact h6) (by rw [mem_afterNextPC]; exact h7)) hwr

end Vsa.Sim
