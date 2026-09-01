import Vsa.Sim.ErrorTail
import Vsa.Sim.HtifLift
/-! Probe: `exec_sd_tohost_putchar` — the P1 seam step: the `_write` loop's
`sd a5,-856(a6)` console store as an instruction-level execute characterization.
Clone of `exec_sd_tohost_exit` (ErrorTail.lean:75) with
`mem_write_value_tohost_putchar` (HtifLift.lean) as the abstract post. -/
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim
open Sail.ConcurrencyInterfaceV1.PreSail
open Register
open Vsa.Machine (MState)

/-- Post-state of the putchar `sd`: HTIF handshake register tower + the byte
pushed to `sailOutput`; memory UNCHANGED. -/
abbrev sigmaPutchar (σ : MState) (pc : BitVec 64) (data : BitVec 64) (c : BitVec 8) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (((((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
                Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
              Register.htif_tohost data).insert
            Register.htif_cmd_write 0#1).insert
          Register.htif_payload_writes 0#4).insert
        Register.htif_tohost (zeros (n := 64))),
    sailOutput := (afterNextPC (afterPrelude σ) pc).sailOutput.push
      (toString (Char.ofNat c.toNat)) }

theorem exec_sd_tohost_putchar
    (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c) :
    (execute (instruction.STORE (imm, rs2, rs1, 8))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigmaPutchar σ pc data c) := by
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
  have hpaddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  have hpw₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_payload_writes = some (0#4) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpw
  have hth₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost = some th := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hth
  have hmwv := mem_write_value_tohost_putchar (afterNextPC (afterPrelude σ) pc) c data
    initMstatus initPmpaddr th hpriv hmstatus (by decide) hpma hcfg hpaddr hbase hpw₂ hth₂ hputc
  have hatohost : (BitVec.ofNat 64 tohostAddr).toNat = tohostAddr := by
    simp only [tohostAddr]; decide
  have htr := translateAddr_machine_store (afterNextPC (afterPrelude σ) pc)
    (BitVec.ofNat 64 tohostAddr) initMstatus hpriv hmstatus (by decide)
  have hea := mem_write_ea_8 (afterNextPC (afterPrelude σ) pc) (BitVec.ofNat 64 tohostAddr)
    initMstatus initPmpaddr hpriv hmstatus (by decide) hpma hcfg hpaddr
    (by rw [hatohost]; exact (by decide : (0x80000000 : Nat) ≤ tohostAddr))
    (by rw [hatohost]; exact (by decide : tohostAddr + 8 ≤ 0x100000000))
    (by rw [hatohost]; exact (by decide : tohostAddr % 8 = 0))
  have hwval : (BitVec.setWidth (8 * 8)
      (Sail.BitVec.extractLsb data (((8 : Nat) *i 8) -i 1).toNat 0)) = data := by
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      BitVec.toNat_setWidth]
    have key : ∀ W : Nat, W = 64 →
        (BitVec.ofNat W (data.toNat >>> 0)).toNat % 2 ^ (8 * 8) = data.toNat := by
      intro W hW; subst hW
      simp only [Nat.shiftRight_zero, BitVec.toNat_ofNat]
      have : data.toNat < 2 ^ 64 := data.isLt
      have h1 : data.toNat % 2 ^ 64 = data.toNat := by omega
      rw [h1]; omega
    exact key ((((8 : Nat) *i 8) -i 1).toNat - 0 + 1) (by decide)
  have hwrite := vmem_write_addr_w (afterNextPC (afterPrelude σ) pc) (sigmaPutchar σ pc data c)
    (BitVec.ofNat 64 tohostAddr) 8 data initMstatus (by decide) (by decide)
    (by rw [hatohost]; exact (by decide : tohostAddr % 8 = 0))
    (by rw [hatohost]; exact (by decide : (tohostAddr + (8 - 1)) / 4096 = tohostAddr / 4096))
    hmstatus hpriv (by decide) htr hea hmwv hwval
  have hchar := execute_STORE_char imm rs2 rs1 8 v1 vdata (afterNextPC (afterPrelude σ) pc)
    initMstatus (0#64) (sigmaPutchar σ pc data c) (by decide)
    hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      rw [haddr, hdataeq, hwval]
      exact hwrite)
  simp only [execute]
  exact hchar

#print axioms exec_sd_tohost_putchar
