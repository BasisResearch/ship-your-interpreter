import Vsa.Sim.TermSimClose
import Vsa.Sim.ErrorSim
import Vsa.Sim.HtifLift

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps Halted Halts output)
open Vsa.Logic
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

abbrev sigmaExitG (σ : MState) (pc : BitVec 64) (data e : BitVec 64) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
                Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
              Register.htif_tohost data).insert
            Register.htif_done true).insert
          Register.htif_exit_code e}

theorem exec_sd_tohost_G
    (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data e : BitVec 64) (th : BitVec 64)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hsmall : e.toNat < 2 ^ 47)
    (hexit : data = (e <<< 1) ||| 1#64) :
    (execute (instruction.STORE (imm, rs2, rs1, 8))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigmaExitG σ pc data e) := by
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

  have hmwv := mem_write_value_tohost_exit (afterNextPC (afterPrelude σ) pc) e data
    initMstatus initPmpaddr th hpriv hmstatus (by decide) hpma hcfg hpaddr hbase hpw₂ hth₂ hsmall hexit
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
  have hwrite := vmem_write_addr_w (afterNextPC (afterPrelude σ) pc) (sigmaExitG σ pc data e)
    (BitVec.ofNat 64 tohostAddr) 8 data initMstatus (by decide) (by decide)
    (by rw [hatohost]; exact (by decide : tohostAddr % 8 = 0))
    (by rw [hatohost]; exact (by decide : (tohostAddr + (8 - 1)) / 4096 = tohostAddr / 4096))
    hmstatus hpriv (by decide) htr hea hmwv hwval
  have hchar := execute_STORE_char imm rs2 rs1 8 v1 vdata (afterNextPC (afterPrelude σ) pc)
    initMstatus (0#64) (sigmaExitG σ pc data e) (by decide)
    hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      rw [haddr, hdataeq, hwval]
      exact hwrite)
  simp only [execute]
  exact hchar

abbrev sigmaExitFinalG (σ : MState) (pc npc vminstret data e : BitVec 64) : MState :=
  {(({(sigmaExitG σ pc data e) with
        regs := (sigmaExitG σ pc data e).regs.insert Register.PC npc}) : MState) with
    regs := ((({(sigmaExitG σ pc data e) with
        regs := (sigmaExitG σ pc data e).regs.insert Register.PC npc}) : MState).regs.insert
          Register.minstret (BitVec.addInt vminstret 1))}

theorem try_step_tohost_G
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data e : BitVec 64) (th : BitVec 64)
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
    (hsmall : e.toNat < 2 ^ 47)
    (hexit : data = (e <<< 1) ||| 1#64)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (try_step u true).run σ = .ok false (sigmaExitFinalG σ pc (BitVec.addInt pc 4) vminstret data e) := by
  obtain ⟨vmip, hmip⟩ := hG.mip
  obtain ⟨vmeip, hmeip⟩ := hG.sig_meip
  obtain ⟨vseip, hseip⟩ := hG.sig_seip
  have hdisp : (dispatchInterrupt Privilege.Machine).run (afterPrelude σ)
      = .ok none (afterPrelude σ) :=
    dispatch_none (afterPrelude σ) vmip vmeip vseip _ _
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mie)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hmip)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hmeip)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hseip)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mideleg)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mstatus)
  have hfetch : (fetch ()).run (afterPrelude σ)
      = .ok (FetchResult.F_Base (((b3.append b2).append b1).append b0)) (afterPrelude σ) :=
    fetch_F_Base (afterPrelude σ) pc b0 b1 b2 b3 _ _ _
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hpc)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mstatus)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.pma_regions)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.pmpcfg_n)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.pmpaddr_n)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.htif_tohost_base)
      hlo hhi halign
      (by rw [mem_afterPrelude]; exact hb0) (by rw [mem_afterPrelude]; exact hb1)
      (by rw [mem_afterPrelude]; exact hb2) (by rw [mem_afterPrelude]; exact hb3)
      hnotrvc
  have hdec' : (ext_decode (((b3.append b2).append b1).append b0)).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ) := by
    rw [hword]; exact hdec
  have hlpad : (is_landing_pad_expected ()).run (afterPrelude σ) = .ok false (afterPrelude σ) :=
    is_landing_pad_expected_false (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.elp)
  have hexec := exec_sd_tohost_G σ pc imm rs2 rs1 v1 vdata data e th
    hG hrs1 hrs2 haddr hdataeq hpw hth hsmall hexit
  have hframe : ∀ R : Register,
      (Register.htif_exit_code == R) = false → (Register.htif_done == R) = false →
      (Register.htif_tohost == R) = false → (Register.htif_payload_writes == R) = false →
      (Register.htif_cmd_write == R) = false →
      (sigmaExitG σ pc data e).regs.get? R = (afterNextPC (afterPrelude σ) pc).regs.get? R := by
    intro R h1 h2 h3 h4 h5
    show (((((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
                Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
              Register.htif_tohost data).insert
            Register.htif_done true).insert
          Register.htif_exit_code e).get? R) = _
    rw [Std.ExtDHashMap.get?_insert]; simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]; simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]; simp only [h3, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]; simp only [h4, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]; simp only [h5, dif_neg, reduceCtorEq, not_false_eq_true]
  have hhart₃ : (sigmaExitG σ pc data e).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide),
      get?_afterNextPC σ pc _ (by decide) (by decide)]
    exact hG.hart_state
  have hnextPC₃ : (sigmaExitG σ pc data e).regs.get? Register.nextPC = some (BitVec.addInt pc 4) := by
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigmaExitG σ pc data e).regs.get? Register.minstret_increment = some true := by
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide,
      dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigmaExitG σ pc data e).regs.get? Register.minstret = some vminstret := by
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide),
      get?_afterNextPC σ pc _ (by decide) (by decide)]
    exact hminstret
  exact try_step_execute_char σ u pc (BitVec.addInt pc 4)
    (((b3.append b2).append b1).append b0) (instruction.STORE (imm, rs2, rs1, 8))
    (sigmaExitG σ pc data e) vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec' hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

theorem htif_done_sigmaExitG_final (σ : MState) (pc npc vminstret data e : BitVec 64) :
    (sigmaExitFinalG σ pc npc vminstret data e).regs.get? Register.htif_done = some true := by
  show (((((sigmaExitG σ pc data e).regs.insert Register.PC npc).insert
      Register.minstret (BitVec.addInt vminstret 1)))).get? Register.htif_done = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.htif_done) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.PC == Register.htif_done) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  show ((((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
          Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
        Register.htif_tohost data).insert
      Register.htif_done true).insert
    Register.htif_exit_code e).get? Register.htif_done = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.htif_exit_code == Register.htif_done) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem htif_exit_code_sigmaExitG_final (σ : MState) (pc npc vminstret data e : BitVec 64) :
    (sigmaExitFinalG σ pc npc vminstret data e).regs.get? Register.htif_exit_code = some e := by
  show (((((sigmaExitG σ pc data e).regs.insert Register.PC npc).insert
      Register.minstret (BitVec.addInt vminstret 1)))).get? Register.htif_exit_code = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.htif_exit_code) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.PC == Register.htif_exit_code) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  show ((((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
          Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
        Register.htif_tohost data).insert
      Register.htif_done true).insert
    Register.htif_exit_code e).get? Register.htif_exit_code = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem stepOnce_tohost_G
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data e : BitVec 64) (th : BitVec 64)
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
    (hsmall : e.toNat < 2 ^ 47)
    (hexit : data = (e <<< 1) ||| 1#64)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (stepOnce i u).run σ
      = .ok (.inl (some e.toNat, u + 1)) (sigmaExitFinalG σ pc (BitVec.addInt pc 4) vminstret data e) := by
  have hts := try_step_tohost_G σ u pc vminstret w imm rs2 rs1 v1 vdata data e th b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hsmall hexit
    hb0 hb1 hb2 hb3 hlo hhi halign
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hdone' := htif_done_sigmaExitG_final σ pc (BitVec.addInt pc 4) vminstret data e
  have hcode' := htif_exit_code_sigmaExitG_final σ pc (BitVec.addInt pc 4) vminstret data e
  unfold stepOnce
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, hhtif,
    Bool.false_eq_true, if_false]
  rw [hts]
  simp only [Bool.false_eq_true, if_false, EStateM.pure, EStateM.bind, EStateM.get,
    hdone', if_true, hcode']

end Vsa.Sim
