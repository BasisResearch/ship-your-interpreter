import Vsa.Sim.HtifLift
import Vsa.Sim.JmpSpec
import Vsa.Refinement

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev sigmaPutcharP (σ : MState) (pc : BitVec 64) (data : BitVec 64) (c : BitVec 8) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (((((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
                Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
              Register.htif_tohost data).insert
            Register.htif_cmd_write 0#1).insert
          Register.htif_payload_writes 0#4).insert
        Register.htif_tohost (zeros (n := 64))),
    sailOutput := (afterNextPC (afterPrelude σ) pc).sailOutput.push
      (toString (Char.ofNat c.toNat)) }

/-- `htif_tohost` is pinned only up to existence: any write to it keeps `GoodState`. -/
theorem GoodState.insert_htif_tohost {σ : MState} (hG : GoodState σ)
    (v : RegisterType Register.htif_tohost) :
    GoodState {σ with regs := σ.regs.insert Register.htif_tohost v} := by
  have Q : ∀ {A : Register} {x : Option (RegisterType A)}, (Register.htif_tohost == A) = false →
      σ.regs.get? A = x → (σ.regs.insert Register.htif_tohost v).get? A = x :=
    fun hA hx => (get?_insert_pinned σ.regs _ v _ hA).trans hx
  have E : ∀ {A : Register}, (Register.htif_tohost == A) = false →
      (∃ w, σ.regs.get? A = some w) → ∃ w, (σ.regs.insert Register.htif_tohost v).get? A = some w :=
    fun hA ⟨w, hw⟩ => ⟨w, Q hA hw⟩
  exact ⟨Q (by decide) hG.cur_privilege, Q (by decide) hG.misa, Q (by decide) hG.mstatus,
    Q (by decide) hG.mie, Q (by decide) hG.mseccfg, Q (by decide) hG.satp, Q (by decide) hG.mtvec,
    Q (by decide) hG.mideleg, Q (by decide) hG.medeleg, Q (by decide) hG.hart_state,
    Q (by decide) hG.htif_done, ⟨v, Std.ExtDHashMap.get?_insert_self⟩,
    Q (by decide) hG.htif_tohost_base, Q (by decide) hG.elp, Q (by decide) hG.pmpcfg_n,
    Q (by decide) hG.pmpaddr_n, Q (by decide) hG.pma_regions, Q (by decide) hG.menvcfg,
    Q (by decide) hG.mcountinhibit, Q (by decide) hG.mcyclecfg, Q (by decide) hG.minstretcfg,
    E (by decide) hG.mip, E (by decide) hG.sig_meip, E (by decide) hG.sig_seip,
    E (by decide) hG.mtime, E (by decide) hG.mtimecmp, E (by decide) hG.minstret,
    E (by decide) hG.minstret_increment, E (by decide) hG.mcycle, E (by decide) hG.nextPC,
    E (by decide) hG.PC⟩

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
      = .ok RETIRE_SUCCESS (sigmaPutcharP σ pc data c) := by
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
  have hwrite := vmem_write_addr_w (afterNextPC (afterPrelude σ) pc) (sigmaPutcharP σ pc data c)
    (BitVec.ofNat 64 tohostAddr) 8 data initMstatus (by decide) (by decide)
    (by rw [hatohost]; exact (by decide : tohostAddr % 8 = 0))
    (by rw [hatohost]; exact (by decide : (tohostAddr + (8 - 1)) / 4096 = tohostAddr / 4096))
    hmstatus hpriv (by decide) htr hea hmwv hwval
  have hchar := execute_STORE_char imm rs2 rs1 8 v1 vdata (afterNextPC (afterPrelude σ) pc)
    initMstatus (0#64) (sigmaPutcharP σ pc data c) (by decide)
    hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      rw [haddr, hdataeq, hwval]
      exact hwrite)
  simp only [execute]
  exact hchar

abbrev sigmaPutcharFinal (σ : MState) (pc npc vminstret data : BitVec 64) (c : BitVec 8) : MState :=
  {(({(sigmaPutcharP σ pc data c) with
        regs := (sigmaPutcharP σ pc data c).regs.insert Register.PC npc}) : MState) with
    regs := ((({(sigmaPutcharP σ pc data c) with
        regs := (sigmaPutcharP σ pc data c).regs.insert Register.PC npc}) : MState).regs.insert
          Register.minstret (BitVec.addInt vminstret 1))}

theorem get?_sigmaPutcharFinal (σ : MState) (pc npc vminstret data : BitVec 64) (c : BitVec 8)
    (R : Register)
    (hms : (Register.minstret == R) = false) (hpc : (Register.PC == R) = false)
    (hth : (Register.htif_tohost == R) = false)
    (hpw : (Register.htif_payload_writes == R) = false)
    (hcw : (Register.htif_cmd_write == R) = false)
    (hnpc : (Register.nextPC == R) = false)
    (hmi : (Register.minstret_increment == R) = false) :
    (sigmaPutcharFinal σ pc npc vminstret data c).regs.get? R = σ.regs.get? R := by
  reg_reads [hms, hpc, hth, hpw, hcw, hnpc, hmi]

theorem get?_PC_sigmaPutcharFinal (σ : MState) (pc npc vminstret data : BitVec 64) (c : BitVec 8) :
    (sigmaPutcharFinal σ pc npc vminstret data c).regs.get? Register.PC = some npc := by
  reg_reads []

theorem get?_minstret_sigmaPutcharFinal (σ : MState) (pc npc vminstret data : BitVec 64)
    (c : BitVec 8) :
    (sigmaPutcharFinal σ pc npc vminstret data c).regs.get? Register.minstret
      = some (BitVec.addInt vminstret 1) := by
  reg_reads []

theorem get?_payload_writes_sigmaPutcharFinal (σ : MState)
    (pc npc vminstret data : BitVec 64) (c : BitVec 8) :
    (sigmaPutcharFinal σ pc npc vminstret data c).regs.get? Register.htif_payload_writes
      = some (0#4) := by
  reg_reads []

theorem get?_htif_tohost_sigmaPutcharFinal (σ : MState)
    (pc npc vminstret data : BitVec 64) (c : BitVec 8) :
    (sigmaPutcharFinal σ pc npc vminstret data c).regs.get? Register.htif_tohost
      = some (zeros (n := 64)) := by
  reg_reads []

theorem goodstate_sigmaPutcharFinal (σ : MState) (pc npc vminstret data : BitVec 64)
    (c : BitVec 8) (hG : GoodState σ) :
    GoodState (sigmaPutcharFinal σ pc npc vminstret data c) :=
  (((((((((hG.insert_nonpinned (r := Register.minstret_increment) (by decide) true).insert_nonpinned
      (r := Register.nextPC) (by decide) (BitVec.addInt pc 4)).insert_nonpinned
      (r := Register.htif_cmd_write) (by decide) 1#1).insert_nonpinned
      (r := Register.htif_payload_writes) (by decide) (0#4 + BitVec.ofInt 4 1)).insert_htif_tohost
      data).insert_nonpinned (r := Register.htif_cmd_write) (by decide) 0#1).insert_nonpinned
      (r := Register.htif_payload_writes) (by decide) 0#4).insert_htif_tohost
      (zeros (n := 64))).of_regs_eq (σ' := sigmaPutcharP σ pc data c) (by rfl)).retirePost _ _

theorem try_step_tohost_putchar
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (try_step u true).run σ = .ok false (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c) :=
  try_step_retire (Fetched.of_bytes hG hpc hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec)
    (exec_sd_tohost_putchar σ pc imm rs2 rs1 v1 vdata data c th hG hrs1 hrs2 haddr hdataeq hpw hth hputc)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩

theorem stepOnce_tohost_putchar_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ
      = .ok (.inr (i + 1, u + 1)) (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c) :=
  stepOnce_retire_notick (try_step_tohost_putchar σ u pc vminstret w imm rs2 rs1 v1 vdata data c th
      b0 b1 b2 b3 hG hpc hminstret hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hputc
      hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c hG) htick

noncomputable abbrev sigmaTick_putchar
    (σ : MState) (pc npc vminstret data : BitVec 64) (c : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) : MState :=
  {(sigmaPutcharFinal σ pc npc vminstret data c) with
    regs := (((sigmaPutcharFinal σ pc npc vminstret data c).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1))))}

theorem stepOnce_tohost_putchar_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ
      = .ok (.inr (0, u + 1))
          (sigmaTick_putchar σ pc (BitVec.addInt pc 4) vminstret data c vmip vmtime vmtimecmp vmcycle) :=
  stepOnce_retire_tick (try_step_tohost_putchar σ u pc vminstret w imm rs2 rs1 v1 vdata data c th
      b0 b1 b2 b3 hG hpc hminstret hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hputc
      hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c hG) hmip hmtime hmtimecmp hmcycle htick

theorem step_tohost_putchar_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c, i + 1, u + 1⟩
    ∧ GoodState (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c) :=
  step_retire_notick (try_step_tohost_putchar σ u pc vminstret w imm rs2 rs1 v1 vdata data c th
      b0 b1 b2 b3 hG hpc hminstret hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hputc
      hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c hG) htick

theorem step_tohost_putchar_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaTick_putchar σ pc (BitVec.addInt pc 4) vminstret data c vmip vmtime vmtimecmp vmcycle,
        0, u + 1⟩
    ∧ GoodState (sigmaTick_putchar σ pc (BitVec.addInt pc 4) vminstret data c
        vmip vmtime vmtimecmp vmcycle) :=
  step_retire_tick (try_step_tohost_putchar σ u pc vminstret w imm rs2 rs1 v1 vdata data c th
      b0 b1 b2 b3 hG hpc hminstret hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hputc
      hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c hG) hmip hmtime hmtimecmp hmcycle htick

theorem stepObs_tohost_putchar
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧
      GoodState σ' ∧
      σ'.mem = σ.mem ∧
      σ'.sailOutput = σ.sailOutput.push (toString (Char.ofNat c.toNat)) ∧
      σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) ∧
      (∃ vm', σ'.regs.get? Register.minstret = some vm') ∧
      σ'.regs.get? Register.htif_payload_writes = some (0#4) ∧
      (∃ th', σ'.regs.get? Register.htif_tohost = some th') ∧
      (∀ R : Register,
        (Register.PC == R) = false → (Register.minstret == R) = false →
        (Register.minstret_increment == R) = false → (Register.nextPC == R) = false →
        (Register.htif_cmd_write == R) = false → (Register.htif_payload_writes == R) = false →
        (Register.htif_tohost == R) = false →
        (Register.mip == R) = false → (Register.mtime == R) = false →
        (Register.mcycle == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  obtain ⟨σ', i', hstep, hi', hG', hmem, hR, hout⟩ := stepObs_retire (try_step_tohost_putchar σ u pc vminstret w imm rs2 rs1 v1 vdata data c th
      b0 b1 b2 b3 hG hpc hminstret hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hputc
      hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c hG) hi
  refine ⟨σ', i', hstep, hi', hG', hmem, hout, ?_, ⟨BitVec.addInt vminstret 1, ?_⟩, ?_,
    ⟨zeros (n := 64), ?_⟩, ?_⟩
  · exact (hR _ (by decide) (by decide) (by decide)).trans
      (get?_PC_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c)
  · exact (hR _ (by decide) (by decide) (by decide)).trans
      (get?_minstret_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c)
  · exact (hR _ (by decide) (by decide) (by decide)).trans
      (get?_payload_writes_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c)
  · exact (hR _ (by decide) (by decide) (by decide)).trans
      (get?_htif_tohost_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c)
  · intro R h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact (hR R h10 h9 h8).trans
      (get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c R h2 h1 h7 h6 h5 h4 h3)

end Vsa.Sim
