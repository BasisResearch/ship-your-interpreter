import Vsa.Sim.BlockMem
import Vsa.Sim.ValueSites
import Vsa.Sim.PinW
/-! Probe: width-2 store characterization `exec_sh` — clone of `exec_sw`
(ValueSites.lean:95) via the EXISTING `vmem_write_addr_2` + width-generic
`execute_STORE_char`; store image = the EXISTING `writeMap2` (PinW.lean). -/
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim
open Sail.ConcurrencyInterfaceV1.PreSail
open Register
open Vsa.Machine (MState)

abbrev shDataP (vdata : BitVec 64) : BitVec (8 * 2) :=
  Sail.BitVec.extractLsb vdata 15 0

theorem exec_sh_probe (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (vbase vdata : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) imm).toNat)
    (hhiram : (vbase + sign_extend (m := 64) imm).toNat + 2 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) imm).toNat)
    (halign : (vbase + sign_extend (m := 64) imm).toNat % 2 = 0) :
    (execute (instruction.STORE (imm, rs2, rs1, 2))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_store σ pc
            (writeMap2 (afterNextPC (afterPrelude σ) pc).mem
              (vbase + sign_extend (m := 64) imm).toNat (shDataP vdata))) := by
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
  have hwrite := vmem_write_addr_2 (afterNextPC (afterPrelude σ) pc)
    (vbase + sign_extend (m := 64) imm) (shDataP vdata) initMstatus initPmpaddr
    hpriv hmstatus (by decide) hpma hcfg haddr hbase' hlo hhiram hhiwin halign
  have hchar := execute_STORE_char imm rs2 rs1 2
    vbase vdata (afterNextPC (afterPrelude σ) pc) initMstatus (0#64)
    (sigma3_store σ pc
      (writeMap2 (afterNextPC (afterPrelude σ) pc).mem
        (vbase + sign_extend (m := 64) imm).toNat (shDataP vdata)))
    (by decide) hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      show (vmem_write_addr (virtaddr.Virtaddr (vbase + sign_extend (m := 64) imm)) 2
          (shDataP vdata) (MemoryAccessType.Store mem_payload.Data) false false false).run
          (afterNextPC (afterPrelude σ) pc)
        = .ok (.Ok true) (sigma3_store σ pc
            (writeMap2 (afterNextPC (afterPrelude σ) pc).mem
              (vbase + sign_extend (m := 64) imm).toNat (shDataP vdata)))
      exact hwrite)
  show (execute (instruction.STORE (imm, rs2, rs1, 2))).run (afterNextPC (afterPrelude σ) pc) = _
  simp only [execute]
  exact hchar

#print axioms exec_sh_probe
