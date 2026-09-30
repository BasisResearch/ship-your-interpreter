import Vsa.Sim.Skeleton
import Vsa.Sim.Retire
import Vsa.Sim.StepAddi
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.Frame

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev sigma3_store (σ : MState) (pc : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8)) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with mem := m'}

theorem get?_sigma3_store_regs (σ : MState) (pc : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8)) (R : Register) :
    (sigma3_store σ pc m').regs.get? R = (afterNextPC (afterPrelude σ) pc).regs.get? R := rfl

theorem get?_sigma3_store_pinned (σ : MState) (pc : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8)) (R : Register)
    (hnpc : (Register.nextPC == R) = false)
    (hmi : (Register.minstret_increment == R) = false) :
    (sigma3_store σ pc m').regs.get? R = σ.regs.get? R := by
  rw [get?_sigma3_store_regs]
  exact get?_afterNextPC σ pc R hnpc hmi

theorem try_step_store
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (m' : Std.ExtHashMap Nat (BitVec 8))
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_store σ pc m'))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3_store σ pc m') with regs := (sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)}) : MState) with
            regs := (({(sigma3_store σ pc m') with regs := (sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
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
    fetch_F_Base (afterPrelude σ) pc b0 b1 b2 b3
      _ _ _
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
      = .ok ast (afterPrelude σ) := by
    rw [hword]; exact hdec
  have hlpad : (is_landing_pad_expected ()).run (afterPrelude σ) = .ok false (afterPrelude σ) :=
    is_landing_pad_expected_false (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.elp)

  have hhart₃ : (sigma3_store σ pc m').regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [get?_sigma3_store_pinned σ pc m' _ (by decide) (by decide)]
    exact hG.hart_state
  have hnextPC₃ : (sigma3_store σ pc m').regs.get? Register.nextPC = some (BitVec.addInt pc 4) := by
    rw [get?_sigma3_store_regs]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigma3_store σ pc m').regs.get? Register.minstret_increment = some true := by
    rw [get?_sigma3_store_regs]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigma3_store σ pc m').regs.get? Register.minstret = some vminstret := by
    rw [get?_sigma3_store_pinned σ pc m' _ (by decide) (by decide)]
    exact hminstret
  exact try_step_execute_char σ u pc (BitVec.addInt pc 4)
    (((b3.append b2).append b1).append b0) ast
    (sigma3_store σ pc m') vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec' hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

abbrev sigmaPost_store (σ : MState) (pc vminstret : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8)) : MState :=
  {(({(sigma3_store σ pc m') with regs := (sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)}) : MState) with
    regs := (({(sigma3_store σ pc m') with regs := (sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

theorem get?_sigmaPost_store (σ : MState) (pc vminstret : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8)) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_store σ pc vminstret m').regs.get? R = σ.regs.get? R := by
  reg_reads [h1, h2, h4, h5]

theorem goodstate_sigmaPost_store (σ : MState) (pc vminstret : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ) : GoodState (sigmaPost_store σ pc vminstret m') := by

  have hbase : GoodState (afterNextPC (afterPrelude σ) pc) :=
    ((hG.insert_nonpinned (r := Register.minstret_increment) (by decide) _).insert_nonpinned
      (r := Register.nextPC) (by decide) _)

  have hstore : GoodState (sigma3_store σ pc m') :=
    GoodState.of_regs_eq (σ := afterNextPC (afterPrelude σ) pc) (σ' := sigma3_store σ pc m') rfl hbase
  exact ((hstore.insert_nonpinned (r := Register.PC) (by decide) _).insert_nonpinned
    (r := Register.minstret) (by decide) _)

theorem htif_done_sigmaPost_store (σ : MState) (pc vminstret : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ) : (sigmaPost_store σ pc vminstret m').regs.get? Register.htif_done = some false := by
  rw [get?_sigmaPost_store σ pc vminstret m' _ (by decide) (by decide) (by decide) (by decide)]
  exact hG.htif_done

theorem stepOnce_store_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (m' : Std.ExtHashMap Nat (BitVec 8))
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_store σ pc m'))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1)) (sigmaPost_store σ pc vminstret m') := by
  have hts := try_step_store σ u pc vminstret w ast m' b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_store σ pc vminstret m' hG
  unfold stepOnce
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, hhtif,
    Bool.false_eq_true, if_false]
  rw [hts]
  simp only [Bool.false_eq_true, if_false, EStateM.pure, EStateM.bind, EStateM.get, hhtif']
  have htick' : (i + 1 == Int.toNat plat_insns_per_tick) = false := by
    simp only [plat_insns_per_tick, show Int.toNat 2 = 2 from rfl, beq_eq_false_iff_ne]
    exact htick
  simp only [htick', Bool.false_eq_true, if_false, EStateM.pure]

noncomputable abbrev sigmaTick_store
    (σ : MState) (pc vminstret : BitVec 64) (m' : Std.ExtHashMap Nat (BitVec 8))
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) : MState :=
  {(sigmaPost_store σ pc vminstret m') with
    regs := (((((sigmaPost_store σ pc vminstret m').regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1))))))}

theorem stepOnce_store_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (m' : Std.ExtHashMap Nat (BitVec 8))
    (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_store σ pc vminstret m').regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_store σ pc vminstret m').regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_store σ pc vminstret m').regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_store σ pc vminstret m').regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_store σ pc m'))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ
      = .ok (.inr (0, u + 1)) (sigmaTick_store σ pc vminstret m' vmip vmtime vmtimecmp vmcycle) := by
  have hts := try_step_store σ u pc vminstret w ast m' b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign
  simp only [EStateM.run] at hts
  have hGp := goodstate_sigmaPost_store σ pc vminstret m' hG
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_store σ pc vminstret m' hG
  have htc := tick_clock_char (sigmaPost_store σ pc vminstret m') vmip vmtime vmtimecmp vmcycle
    hGp.cur_privilege hGp.mcountinhibit hGp.mcyclecfg hGp.menvcfg hGp.misa
    hmip hmtime hmtimecmp hmcycle hGp.sig_meip hGp.sig_seip
  simp only [EStateM.run] at htc
  unfold stepOnce
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, hhtif,
    Bool.false_eq_true, if_false]
  rw [hts]
  simp only [Bool.false_eq_true, if_false, EStateM.pure, EStateM.bind, EStateM.get, hhtif']
  have htick' : (i + 1 == Int.toNat plat_insns_per_tick) = true := by
    simp only [plat_insns_per_tick, show Int.toNat 2 = 2 from rfl, beq_iff_eq]
    exact htick
  simp only [htick', if_true, EStateM.bind]
  rw [htc]
  rfl

theorem step_store_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (m' : Std.ExtHashMap Nat (BitVec 8))
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_store σ pc m'))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩ ⟨sigmaPost_store σ pc vminstret m', i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_store σ pc vminstret m') :=
  ⟨Vsa.Machine.Step.mk
    (stepOnce_store_notick σ i u pc vminstret w ast m' b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec
      hb0 hb1 hb2 hb3 hlo hhi halign htick),
   goodstate_sigmaPost_store σ pc vminstret m' hG⟩

theorem step_store_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (m' : Std.ExtHashMap Nat (BitVec 8))
    (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_store σ pc vminstret m').regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_store σ pc vminstret m').regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_store σ pc vminstret m').regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_store σ pc vminstret m').regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_store σ pc m'))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaTick_store σ pc vminstret m' vmip vmtime vmtimecmp vmcycle, 0, u + 1⟩
    ∧ GoodState (sigmaTick_store σ pc vminstret m' vmip vmtime vmtimecmp vmcycle) := by
  refine ⟨Vsa.Machine.Step.mk
    (stepOnce_store_tick σ i u pc vminstret w ast m' b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hword hnotrvc hdec hexec
      hb0 hb1 hb2 hb3 hlo hhi halign htick), ?_⟩
  have hGp := goodstate_sigmaPost_store σ pc vminstret m' hG
  exact ((hGp.insert_nonpinned (r := Register.mcycle) (by decide) _).insert_nonpinned
    (r := Register.mtime) (by decide) _).insert_nonpinned (r := Register.mip) (by decide) _

end Vsa.Sim
