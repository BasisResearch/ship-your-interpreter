import Vsa.Sim.BlockMem
/-! Probe: width-2 load characterizations `exec_lhu_bm`/`exec_lh_bm` — clones of
`exec_lbu_bm` (BlockMem.lean:137) via the EXISTING `vmem_read_data_two` +
width-generic `execute_load_{unsigned,signed}_char`. -/
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim
open Sail.ConcurrencyInterfaceV1.PreSail
open Register
open Vsa.Machine (MState)

theorem exec_lhu_bm_probe (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (b0 b1 : BitVec 8)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (zero_extend (m := 64) (b1.append b0 : BitVec (8 * 2)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 2 = 0)
    (h0 : σ.mem[(vbase + sign_extend (m := 64) off).toNat]? = some b0)
    (h1 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 1]? = some b1) :
    (execute (instruction.LOAD (off, rs1, rd, true, 2))).run (afterNextPC (afterPrelude σ) pc)
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
  have hread := vmem_read_data_two (afterNextPC (afterPrelude σ) pc) rs1
    (sign_extend (m := 64) off) vbase b0 b1 initMstatus initPmpaddr
    hpriv hmstatus (by decide) hseccfg hpma hcfg haddr hbase' hrs1 hlo hhiram hhtif halign
    (by rw [mem_afterNextPC]; exact h0) (by rw [mem_afterNextPC]; exact h1)
  exact execute_load_unsigned_char off rs1 rd 2 (b1.append b0 : BitVec (8 * 2))
    (afterNextPC (afterPrelude σ) pc) σ' (by decide) hread hwr

theorem exec_lh_bm_probe (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (b0 b1 : BitVec 8)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (sign_extend (m := 64) (b1.append b0 : BitVec (8 * 2)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 2 = 0)
    (h0 : σ.mem[(vbase + sign_extend (m := 64) off).toNat]? = some b0)
    (h1 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 1]? = some b1) :
    (execute (instruction.LOAD (off, rs1, rd, false, 2))).run (afterNextPC (afterPrelude σ) pc)
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
  have hread := vmem_read_data_two (afterNextPC (afterPrelude σ) pc) rs1
    (sign_extend (m := 64) off) vbase b0 b1 initMstatus initPmpaddr
    hpriv hmstatus (by decide) hseccfg hpma hcfg haddr hbase' hrs1 hlo hhiram hhtif halign
    (by rw [mem_afterNextPC]; exact h0) (by rw [mem_afterNextPC]; exact h1)
  exact execute_load_signed_char off rs1 rd 2 (b1.append b0 : BitVec (8 * 2))
    (afterNextPC (afterPrelude σ) pc) σ' (by decide) hread hwr

#print axioms exec_lhu_bm_probe
#print axioms exec_lh_bm_probe
