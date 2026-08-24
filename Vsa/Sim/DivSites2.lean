import Vsa.Sim.DivLoops
import Vsa.Sim.Code.«__umoddi3»
import Vsa.Sim.Code.«__divdi3»
import Vsa.Sim.Code.«__moddi3»

/-!
# Layer 3 — site step lemmas OUTSIDE the shared `__hidden___udivdi3` core

Per-instruction observational-step `Triple`s for every instruction reachable
from the three wrapper entries `__divdi3` (0x800046a4), `__umoddi3` (0x800046f4)
and `__moddi3` (0x80004728) that lies OUTSIDE the shared unsigned core
`[0x800046ac, 0x800046f4)` (which `Vsa/Sim/DivSites.lean` + `DivSpec.lean` +
`DivLoops.lean` already handle).

Each wrapper block negates operands (`neg = sub rd,x0,rs`), saves the return
address to `t0` (`mv t0,ra`), calls the core (`jal`), fixes up the sign of the
result (`neg`), and returns via `t0` (`jr t0`). These sites use the `stepObs_jal`
/ `stepObs_j` / `stepObs_jr` wrappers (first use of `jal`/`j` in this project),
so we also build the `jal` observation consumers `obs_jal_*` here (analogues of
`obs_alu_*` in `Muldi3Spec`).

These lemmas are stated over the udivdi3 `Ust` predicate (`DivSpec.lean`) where
the PC lies in the core, and over local wrapper predicates elsewhere; but since
the wrapper code is loaded by a DIFFERENT `Loaded` predicate than the core, each
site lemma is stated as a bare machine-stepping `site_*`-style existential and the
config-level `Triple` glue lives in `DivSpec2.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `jal` observation consumers (analogue of `obs_alu_*`)

From a `jal` observation `ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)`
read framing fields off `σ'`: `obs_jal_pc` gives PC := pc + sext imm; `obs_jal_rd`
gives rd_reg := link; `obs_jal_other` reads any register outside the write-set
from `σ`; `obs_jal_minstret` gives minstret defined. -/

theorem post_jal_pc (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.PC
      = some (pc + sign_extend (m := 64) imm) := by
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_jal_rd (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? rd_reg = some link := by
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  show (((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
    (pc + sign_extend (m := 64) imm)).insert rd_reg link).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_jal_other (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? R = σ.regs.get? R :=
  get?_sigmaPost_jal σ pc vminstret imm rd_reg link R h1 h2 h3 h4 h5

theorem obs_jal_pc {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    σ'.regs.get? Register.PC = some (pc + sign_extend (m := 64) imm) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_jal_pc σ pc vm imm rd_reg link)

theorem obs_jal_rd {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link))
    (hmc : (Register.mcycle == rd_reg) = false) (hmt : (Register.mtime == rd_reg) = false)
    (hmi : (Register.mip == rd_reg) = false)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    σ'.regs.get? rd_reg = some link :=
  readback σ' _ hobs rd_reg hmc hmt hmi (post_jal_rd σ pc vm imm rd_reg link h1 h2)

theorem obs_jal_other {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((post_jal_other σ pc vm imm rd_reg link R h1 h2 h3 h4 h5).trans hσ)

theorem obs_jal_minstret {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-! ## `__umoddi3` entry sites (0x800046f4 – 0x80004700)

```
f4 mv t0,ra      ; t0 := ra           (ITYPE addi t0,ra,0; rd x5, rs1 x1)
f8 jal 46ac      ; ra := f8+4; → 46ac (JAL rd x1, imm 0x1fffb4)
fc mv a0,a1      ; a0 := a1           (ITYPE addi a0,a1,0; rd x10, rs1 x11)
00 jr t0         ; PC := t0           (JALR rd x0, rs1 x5)
```
-/

/-! ### 0x800046f4 — `mv t0,ra` = `addi t0,ra,0` (rd = x5, rs1 = x1) -/

theorem exec_mv_t0_ra (σ : MState) (pc : BitVec 64) (v1 : BitVec 64)
    (hx1 : σ.regs.get? Register.x1 = some v1) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x01#5, regidx.Regidx 0x05#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x5 (v1 + sign_extend (m := 64) (0x000#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x1 = some v1 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx1
  exact execute_itype_addi_char (0x000#12) (regidx.Regidx 0x01#5) (regidx.Regidx 0x05#5) v1
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x5 (v1 + sign_extend (m := 64) (0x000#12)))
    (rX_bits_x1 _ v1 h₂) (wX_bits_x5 _ (v1 + sign_extend (m := 64) (0x000#12)))

theorem site2_800046f4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v1 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some v1)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x800046f4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x5 (v1 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_800046f4 hmem
  exact stepObs_alu σ i u (0x800046f4#64) vminstret (0x00008293#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x01#5, regidx.Regidx 0x05#5, iop.ADDI))
    Register.x5 (v1 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x82#8) (0x00#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00008293 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_mv_t0_ra σ (0x800046f4#64) v1 hx1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046f8 — `jal 0x800046ac` (rd = x1, imm 0x1fffb4 → 0x800046ac) -/

theorem site2_800046f8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x800046f8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1fffb4#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_800046f8 hmem
  refine stepObs_jal σ i u (0x800046f8#64) vminstret (0xfb5ff0ef#32) (0x1fffb4#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800046f8#64) 4) (0xef#8) (0xf0#8) (0x5f#8) (0xfb#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fb5ff0ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi
  exact wX_bits_x1 _ (BitVec.addInt (0x800046f8#64) 4)

/-! ### 0x800046fc — `mv a0,a1` = `addi a0,a1,0` (rd = x10, rs1 = x11) -/

theorem exec_mv_a0_a1 (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 (v11 + sign_extend (m := 64) (0x000#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5) v11
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 (v11 + sign_extend (m := 64) (0x000#12)))
    (rX_bits_x11 _ v11 h₂) (wX_bits_x10 _ (v11 + sign_extend (m := 64) (0x000#12)))

theorem site2_800046fc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x800046fc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v11 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_800046fc hmem
  exact stepObs_alu σ i u (0x800046fc#64) vminstret (0x00058513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v11 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x85#8) (0x05#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00058513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_mv_a0_a1 σ (0x800046fc#64) v11 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80004700 — `jr t0` = `jalr x0,t0,0` (rs1 = x5) -/

theorem site2_80004700
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vt0 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some vt0)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x80004700#64 : BitVec 64))
    (htgt : (BitVec.update (vt0 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vt0 + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_80004700 hmem
  have hx5₂ : (rX_bits (regidx.Regidx 0x05#5)).run (afterNextPC (afterPrelude σ) (0x80004700#64))
      = .ok vt0 (afterNextPC (afterPrelude σ) (0x80004700#64)) := by
    apply rX_bits_x5
    rw [get?_afterNextPC σ (0x80004700#64) _ (by decide) (by decide)]; exact hx5
  exact stepObs_jr σ i u (0x80004700#64) vminstret vt0 (0x00028067#32) (0x000#12)
    (regidx.Regidx 0x05#5) (0x67#8) (0x80#8) (0x02#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00028067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx5₂ htgt hi

/-! ## `neg` helper (`neg rd,rs = sub rd,x0,rs`, RTYPE with rs1 = x0)

`neg a0,a0` = `RTYPE(rs2 = x10, rs1 = x0, rd = x10, SUB)`: `x10 := 0 - a0`.
`neg a1,a1` similarly on x11. The `rs1 = x0` read uses `rX_bits_zero`. -/

theorem exec_neg_a0 (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0a#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, rop.SUB))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x10 ((0#64) - v10)) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_rtype_sub_char (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
    (0#64) v10 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 ((0#64) - v10))
    (rX_bits_zero _) (rX_bits_x10 _ v10 h10) (wX_bits_x10 _ ((0#64) - v10))

theorem exec_neg_a1 (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0b#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, rop.SUB))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x11 ((0#64) - v11)) := by
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_rtype_sub_char (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0b#5)
    (0#64) v11 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x11 ((0#64) - v11))
    (rX_bits_zero _) (rX_bits_x11 _ v11 h11) (wX_bits_x11 _ ((0#64) - v11))

/-- `neg a0,a1` = `sub a0,x0,a1` = `RTYPE(rs2 = x11, rs1 = x0, rd = x10, SUB)`:
`x10 := 0 - a1` (used at moddi3 0x80004750). -/
theorem exec_neg_a0_a1 (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0b#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, rop.SUB))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x10 ((0#64) - v11)) := by
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_rtype_sub_char (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
    (0#64) v11 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 ((0#64) - v11))
    (rX_bits_zero _) (rX_bits_x11 _ v11 h11) (wX_bits_x10 _ ((0#64) - v11))

/-! ## `__divdi3` entry sites (0x800046a4 / 0x800046a8) — the two sign tests

```
a4 bltz a0,4704   ; BLT a0,x0 : if a0 < 0 (signed) → 0x80004704
a8 bltz a1,4714   ; BLT a1,x0 : if a1 < 0 (signed) → 0x80004714
```
Both fall through into the shared core at 0x800046ac. -/

/-! ### 0x800046a4 — `bltz a0` = `blt a0,x0` (rs1 = x10, rs2 = x0), imm 0x0060 → 0x80004704 -/

theorem exec_bltz_a0_taken (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (htgt : (pc + sign_extend (m := 64) (0x0060#13)).toNat % 4 = 0)
    (hv : zopz0zI_s v10 (0#64) = true) :
    (execute (instruction.BTYPE (0x0060#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, bop.BLT))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x0060#13)) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_blt_taken (0x0060#13) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
    v10 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x10 _ v10 h10) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

theorem exec_bltz_a0_nottaken (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hv : zopz0zI_s v10 (0#64) = false) :
    (execute (instruction.BTYPE (0x0060#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, bop.BLT))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_btype_blt_nottaken (0x0060#13) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
    v10 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x10 _ v10 h10) (rX_bits_zero _) hv

theorem site2_800046a4_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code.__divdi3Loaded σ.mem)
    (hpcv : pc = (0x800046a4#64 : BitVec 64)) (hv : zopz0zI_s v10 (0#64) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0060#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__divdi3_at_800046a4 hmem
  exact stepObs_branch_taken σ i u (0x800046a4#64) vminstret (0x0060#13)
    (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5) bop.BLT (0x06054063#32)
    (0x63#8) (0x40#8) (0x05#8) (0x06#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_06054063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bltz_a0_taken σ (0x800046a4#64) v10 hG hpc hx10 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site2_800046a4_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code.__divdi3Loaded σ.mem)
    (hpcv : pc = (0x800046a4#64 : BitVec 64)) (hv : zopz0zI_s v10 (0#64) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__divdi3_at_800046a4 hmem
  exact stepObs_branch_nottaken σ i u (0x800046a4#64) vminstret (0x0060#13)
    (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5) bop.BLT (0x06054063#32)
    (0x63#8) (0x40#8) (0x05#8) (0x06#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_06054063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bltz_a0_nottaken σ (0x800046a4#64) v10 hx10 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80004710 — `j 0x800046ac` = `jal x0, imm 0x1fff9c` (unconditional) -/

theorem site2_80004710
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x80004710#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x1fff9c#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_80004710 hmem
  exact stepObs_j σ i u (0x80004710#64) vminstret (0xf9dff06f#32) (0x1fff9c#21)
    (0x6f#8) (0xf0#8) (0xdf#8) (0xf9#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_f9dff06f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide) hi

end Vsa.Sim
