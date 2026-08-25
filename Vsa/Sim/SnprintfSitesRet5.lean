import Vsa.Sim.RegPins
import Vsa.Sim.SnprintfSitesRet
import Vsa.Sim.SnprintfSitesRet4
import Vsa.Sim.DecodeTable.Batch02Part05
import Vsa.Sim.DecodeTable.Batch03Part30
import Vsa.Sim.DecodeTable.Batch05Part19
import Vsa.Sim.DecodeTable.Batch07Part28

/-!
# `SnprintfSitesRet5` — hand-written sites for the flush return path

Two site classes `scripts/gen_sites.py` does not cover (generator gaps, noted
in the session report):

* **linking `jalr`** (`jalr ra,0(rs1)` — the indirect *call* through the
  locale's `mbtowc` function pointer at `0x80007740`).  The whole
  `stepObs_jalr` tick-absorbing wrapper did not exist either (only
  `stepObs_jr` for `rd = x0` and `stepObs_jal` for direct calls); it is built
  here from `step_jalr_notick` / `step_jalr_tick` (`StepJump.lean`), together
  with its `obs_jalr_*` read-back consumers and the `pins_jalr` RegPins
  transport.
* **`sltu` / `snez`** (`snez a0,a0` at `0x80012280` in `__ascii_mbtowc`);
* **`lhu`** (`lhu a5,16(a5)` — the FILE-flags halfword read at `0x800079c0`;
  the generic `exec_lhu_gen` execute helper is also new) and **`andi`**
  (`andi a5,a5,64` at `0x800079c4`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `stepObs_jalr` — tick-absorbing observational step for a linking `jalr` -/

/-- GPR/PC read-back through the JALR tick chain drops to `sigmaPost_jalr`
(mirror of `get?_sigmaTick_jal`). -/
theorem get?_sigmaTick_jalr (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) (R : Register)
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false) :
    (sigmaTick_jalr σ pc vminstret tgt rd_reg link vmip vmtime vmtimecmp vmcycle).regs.get? R
      = (sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.get? R := by
  show (((((sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.insert Register.mcycle _).insert
      Register.mtime _).insert Register.mip _)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmi, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmt, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmc, dif_neg, reduceCtorEq, not_false_eq_true]

/-- `jalr` (indirect call, writes `link = pc+4` to `rd_reg`, jumps to the
bit-0-cleared `rs1 + sext imm`).  Mirror of `stepObs_jal` over
`step_jalr_notick`/`step_jalr_tick`. -/
theorem stepObs_jalr
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, rd)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}
        = .ok () (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link))
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)
          rd_reg link) := by
  by_cases htick : i + 1 = 2
  · have hGp := goodstate_sigmaPost_jalr σ pc vminstret
      (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg hrd link hG
    obtain ⟨vmip, hmip⟩ := hGp.mip
    obtain ⟨vmtime, hmtime⟩ := hGp.mtime
    obtain ⟨vmtimecmp, hmtimecmp⟩ := hGp.mtimecmp
    obtain ⟨vmcycle, hmcycle⟩ := hGp.mcycle
    obtain ⟨hstep, hGt⟩ := step_jalr_tick σ i u pc vminstret vrs1 w imm rs1 rd rd_reg link
      b0 b1 b2 b3 vmip vmtime vmtimecmp vmcycle
      hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt
      hrd_npc hrd_mi hrd_ms hrd_hart hrd hwr htick
    refine ⟨_, 0, hstep, by decide, hGt, rfl, ?_, rfl⟩
    intro R hmc hmt hmi
    exact get?_sigmaTick_jalr σ pc vminstret _ rd_reg link vmip vmtime vmtimecmp vmcycle
      R hmc hmt hmi
  · obtain ⟨hstep, hGt⟩ := step_jalr_notick σ i u pc vminstret vrs1 w imm rs1 rd rd_reg link
      b0 b1 b2 b3 hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt
      hrd_npc hrd_mi hrd_ms hrd_hart hrd hwr htick
    exact ⟨_, i + 1, hstep, by omega, hGt, rfl, ReadsLikePost.rfl _⟩

/-! ## `obs_jalr_*` read-back consumers (mirror of `DivSites2`'s `obs_jal_*`) -/

theorem post_jalr_pc (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg) :
    (sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.get? Register.PC = some tgt := by
  show ((((sigma3_jalr σ pc tgt rd_reg link).regs.insert Register.PC tgt).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg,
    reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_jalr_rd (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    (sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.get? rd_reg = some link := by
  show ((((sigma3_jalr σ pc tgt rd_reg link).regs.insert Register.PC tgt).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  show (((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC tgt).insert
    rd_reg link).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_jalr_other (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.get? R = σ.regs.get? R :=
  get?_sigmaPost_jalr σ pc vminstret tgt rd_reg link R h1 h2 h3 h4 h5

theorem obs_jalr_pc {σ' σ : MState} {pc vm tgt : BitVec 64}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jalr σ pc vm tgt rd_reg link)) :
    σ'.regs.get? Register.PC = some tgt :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide)
    (post_jalr_pc σ pc vm tgt rd_reg link)

theorem obs_jalr_rd {σ' σ : MState} {pc vm tgt : BitVec 64}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jalr σ pc vm tgt rd_reg link))
    (hmc : (Register.mcycle == rd_reg) = false) (hmt : (Register.mtime == rd_reg) = false)
    (hmi : (Register.mip == rd_reg) = false)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    σ'.regs.get? rd_reg = some link :=
  readback σ' _ hobs rd_reg hmc hmt hmi (post_jalr_rd σ pc vm tgt rd_reg link h1 h2)

theorem obs_jalr_other {σ' σ : MState} {pc vm tgt : BitVec 64}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jalr σ pc vm tgt rd_reg link)) (R : Register)
    {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi
    ((post_jalr_other σ pc vm tgt rd_reg link R h1 h2 h3 h4 h5).trans hσ)

theorem obs_jalr_minstret {σ' σ : MState} {pc vm tgt : BitVec 64}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jalr σ pc vm tgt rd_reg link)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_jalr σ pc tgt rd_reg link).regs.insert Register.PC tgt).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `RegPins` transport across a linking `jalr` (mirror of `pins_jal`). -/
theorem pins_jalr {σ' σ : MState} {pc vm tgt : BitVec 64}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jalr σ pc vm tgt rd_reg link)) {L : List Pin}
    (hav : pinsAvoid (rd_reg :: noiseRegs) L = true)
    (h : PinsHold σ L) : PinsHold σ' L := by
  induction L with
  | nil => trivial
  | cons p rest ih =>
    obtain ⟨hn, hrest⟩ := pinsAvoid_cons hav
    exact ⟨obs_jalr_other hobs p.1
      (hn Register.mcycle (List.mem_cons_of_mem rd_reg (by decide)))
      (hn Register.mtime (List.mem_cons_of_mem rd_reg (by decide)))
      (hn Register.mip (List.mem_cons_of_mem rd_reg (by decide)))
      (hn Register.minstret (List.mem_cons_of_mem rd_reg (by decide)))
      (hn Register.PC (List.mem_cons_of_mem rd_reg (by decide)))
      (hn rd_reg (List.mem_cons_self ..))
      (hn Register.nextPC (List.mem_cons_of_mem rd_reg (by decide)))
      (hn Register.minstret_increment (List.mem_cons_of_mem rd_reg (by decide)))
      h.1, ih hrest h.2⟩

/-! ## The two hand sites -/

/-- 0x80007740: `jalr ra,0(x20)` — the indirect call through the locale `mbtowc`
function pointer (`s4`).  Link `x1 := 0x80007744`; target = bit-0-cleared `s4`. -/
theorem site_80007740_rt5 (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hmem : Vsa.Sim.Code.SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80007740#64 : BitVec 64))
    (htgt : (BitVec.update (v20 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jalr σ pc vminstret
        (BitVec.update (v20 + sign_extend (m := 64) (0x000#12)) 0 0#1)
        Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007740 hmem
  refine stepObs_jalr σ i u (0x80007740#64) vminstret v20 (0x000a00e7#32) (0x000#12)
    (regidx.Regidx 0x14#5) (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80007740#64) 4)
    (0xe7#8) (0x00#8) (0x0a#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_000a00e7 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (rX_bits_x20 _ v20
      (by rw [get?_afterNextPC σ (0x80007740#64) _ (by decide) (by decide)]; exact hx20))
    htgt
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi
  exact wX_bits_x1 _ (BitVec.addInt (0x80007740#64) 4)

/-- 0x80012280: `snez a0,a0` (`sltu x10,x0,x10`). -/
theorem site_80012280_rt5 (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code.__ascii_mbtowcLoaded σ.mem)
    (hpcv : pc = (0x80012280#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10
        (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v10)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ascii_mbtowc_at_80012280 hmem
  exact stepObs_alu σ i u (0x80012280#64) vminstret (0x00a03533#32)
    (instruction.RTYPE (regidx.Regidx 0x0a#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5,
      rop.SLTU))
    Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v10)))
    (0x33#8) (0x35#8) (0xa0#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00a03533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_sltu_char (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
      (0#64) v10 (afterNextPC (afterPrelude σ) (0x80012280#64))
      (sigma3_alu σ (0x80012280#64) Register.x10
        (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v10))))
      (rX_bits_zero _)
      (rX_bits_x10 _ v10
        (by rw [get?_afterNextPC σ (0x80012280#64) _ (by decide) (by decide)]; exact hx10))
      (wX_bits_x10 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v10)))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## `lhu` (2-byte unsigned load) -/

/-- Generic `lhu rd,off(rs1)`: reads the LE halfword `b1.append b0` at
`v1 + sext imm` and writes `zero_extend` of it (mirror of
`StrcpySites.exec_lbu_gen` at width 2, over `vmem_read_data_two`). -/
theorem exec_lhu_gen (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs1 rd : regidx)
    (v1 : BitVec 64) (b0v b1v : BitVec 8)
    (σ' : SequentialState RegisterType trivialChoiceSource)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (zero_extend (m := 64) ((b1v.append b0v) : BitVec (8 * 2)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (v1 + sign_extend (m := 64) imm).toNat)
    (hhiram : (v1 + sign_extend (m := 64) imm).toNat + 2 ≤ 0x100000000)
    (hhtif : (v1 + sign_extend (m := 64) imm).toNat + 2 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v1 + sign_extend (m := 64) imm).toNat)
    (halign : (v1 + sign_extend (m := 64) imm).toNat % 2 = 0)
    (hb0 : σ.mem[(v1 + sign_extend (m := 64) imm).toNat]? = some b0v)
    (hb1 : σ.mem[(v1 + sign_extend (m := 64) imm).toNat + 1]? = some b1v) :
    (execute (instruction.LOAD (imm, rs1, rd, true, 2))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  have hpriv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  have hmstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus
      = some initMstatus := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  have hseccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  have hpma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  have hcfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  have haddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n
      = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  have hread := vmem_read_data_two (afterNextPC (afterPrelude σ) pc)
    rs1 (sign_extend (m := 64) imm) v1 b0v b1v initMstatus initPmpaddr
    hpriv hmstatus (by decide) hseccfg hpma hcfg haddr hbase' hrs1 hlo hhiram hhtif halign
    (by rw [mem_afterNextPC]; exact hb0) (by rw [mem_afterNextPC]; exact hb1)
  exact execute_load_unsigned_char imm rs1 rd 2 ((b1v.append b0v) : BitVec (8 * 2))
    (afterNextPC (afterPrelude σ) pc) σ' (by decide) hread hwr

/-- 0x800079c0: `lhu x15,0x10(x15)` — the FILE `_flags` halfword. -/
theorem site_800079c0_rt5 (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (b0v b1v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Vsa.Sim.Code.SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800079c0#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v15 + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (v15 + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤ 0x100000000)
    (hhtif : (v15 + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v15 + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (v15 + sign_extend (m := 64) (0x010#12)).toNat % 2 = 0)
    (hb0 : σ.mem[(v15 + sign_extend (m := 64) (0x010#12)).toNat]? = some b0v)
    (hb1 : σ.mem[(v15 + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1v)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15
        (zero_extend (m := 64) ((b1v.append b0v) : BitVec (8 * 2)))) := by
  subst hpcv
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800079c0 hmem
  exact stepObs_alu σ i u (0x800079c0#64) vminstret (0x0107d783#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, true, 2))
    Register.x15 (zero_extend (m := 64) ((b1v.append b0v) : BitVec (8 * 2)))
    (0x83#8) (0xd7#8) (0x07#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0107d783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lhu_gen σ (0x800079c0#64) (0x010#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
      v15 b0v b1v
      (sigma3_alu σ (0x800079c0#64) Register.x15
        (zero_extend (m := 64) ((b1v.append b0v) : BitVec (8 * 2)))) hG
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x800079c0#64) _ (by decide) (by decide)]; exact hx15))
      (wX_bits_x15 _ (zero_extend (m := 64) ((b1v.append b0v) : BitVec (8 * 2))))
      hlo hhiram hhtif halign hb0 hb1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi

/-- 0x800079c4: `andi x15,x15,0x40` — the `__SMBF` flag test. -/
theorem site_800079c4_rt5 (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Vsa.Sim.Code.SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800079c4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15
        (v15 &&& sign_extend (m := 64) (0x040#12))) := by
  subst hpcv
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800079c4 hmem
  exact stepObs_alu σ i u (0x800079c4#64) vminstret (0x0407f793#32)
    (instruction.ITYPE (0x040#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ANDI))
    Register.x15 (v15 &&& sign_extend (m := 64) (0x040#12))
    (0x93#8) (0xf7#8) (0x07#8) (0x04#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0407f793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_andi_char (0x040#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
      (afterNextPC (afterPrelude σ) (0x800079c4#64))
      (sigma3_alu σ (0x800079c4#64) Register.x15 (v15 &&& sign_extend (m := 64) (0x040#12)))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x800079c4#64) _ (by decide) (by decide)]; exact hx15))
      (wX_bits_x15 _ (v15 &&& sign_extend (m := 64) (0x040#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
