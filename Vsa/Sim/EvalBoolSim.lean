import Vsa.Sim.EvalNullSim
import Vsa.Sim.EvalRecCommon
import Vsa.Sim.DecodeTable.Batch16Part04
import Vsa.Sim.DecodeTable.Batch14Part10
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4: the `EvalE.bool` simulation Triple (`evalBoolSim`)

The third M4 leaf case (after `EvalE.int` and `EvalE.null`). Mirrors `evalNullSim`
(`EvalNullSim.lean`) but for the `EX_BOOL` arm (`ExprKind` tag `k = 2`, arm PC
`0x80003420`). The arm is three instructions — `lw a1,8(a2)` (the 32-bit bool
word → `x11`), `jal value_bool` and `j 0x800033ec` — so block C is the payload
`lw` site followed by the shared `armTail_v` (`EvalSimCommon.lean`) instantiated
at the `value_bool` callee (from PC `0x80003424`) and produced value `.bool b`.

Structure (mirrors `EvalNullSim.lean` + the int payload-load site from
`EvalIntSim4.lean`):

* **`site_80003420_ee`** — the payload-load site (`lw a1,8(a2)`, 32-bit signed →
  `x11`), mirroring the int arm's `site_80003408_ee` (`ld a1,8(a2)`) but 4-byte.
* **`value_bool_spec_full`** — the strengthened `value_bool` spec: from the bool
  callee precondition it runs to a post carrying (besides `ValueRepr … (.bool _)`)
  the console-output and memory-frame facts `armTail_v` needs (`bool_post` omits
  them). Re-runs the five `value_bool` instructions, mirroring `value_bool_spec`.
* **`blockC_bool`** — the arm `ArmEntryK … 0x80003420 Value_boolLoaded (.bool b) →
  PreEpilogueV … (.bool b)`: runs the payload `lw`, then `armTail_v` at the `jal`
  PC `0x80003424` with `value_bool_spec_full` and the two tail sites
  `site_80003424_ee` / `site_80003428_ee`.
* **`EvalBoolSimGoal`/`evalBoolSim`** — the `EvalE.bool` Triple, composed
  `blockA_k (→ArmEntryK) ≫ blockC_bool (→PreEpilogueV .bool b) ≫ blockD_v
  (→EvalExit .bool b)`. Bool entry predicate `EvalBoolEntry` mirrors `EvalNullEntry`
  but carries `BoolSlotPinned 2 0x80003420` + `Value_boolLoaded` and `ExprRepr …
  (.bool b)` in place of the null-specific slot/callee/expr.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The payload-load site `site_80003420_ee` (@0x80003420, `lw a1,8(a2)`)

Mirrors the int arm's `site_80003408_ee` (`ld a1,8(a2)`), but the bool payload is
a 32-bit signed word (`lw`, funct3=010), so it uses `exec_lw` (as in the kind-load
`site_80003164_ee`) writing `x11` from `x12 + 8`. The result is
`sign_extend (b3 ++ b2 ++ b1 ++ b0 : BitVec 32)`. -/
theorem site_80003420_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vexpr : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some vexpr)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003420#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vexpr + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vexpr + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (vexpr + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vexpr + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vexpr + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (h0 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003420 hmem
  have hx12₂ : (afterNextPC (afterPrelude σ) (0x80003420#64)).regs.get? Register.x12 = some vexpr := by
    rw [get?_afterNextPC σ (0x80003420#64) _ (by decide) (by decide)]; exact hx12
  exact stepObs_alu σ i u (0x80003420#64) vminstret (0x00862583#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0b#5, false, 4))
    Register.x11 (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))
    (0x83#8) (0x25#8) (0x86#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00862583 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x80003420#64) (0x008#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5)
      (sigma3_alu σ (0x80003420#64) Register.x11
        (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      vexpr b0 b1 b2 b3 hG (rX_bits_x12 _ vexpr hx12₂)
      (wX_bits_x11 _ (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## The two `EX_BOOL` tail sites (@0x80003424, @0x80003428)

Mirror the null arm's `site_8000342c_ee` (jal) and `site_80003430_ee` (j), with the
bool arm's PCs/words: `jal value_bool` (`bd4ff0ef`, imm `0x1ff3d4`, target
`0x800027f8`, link `0x80003428`) and `j 0x800033ec` (`fc5ff06f`, imm `0x1fffc4`). -/

/-- 0x80003424: `jal value_bool` (imm 0x1ff3d4 → 0x800027f8, rd=x1=ra). -/
theorem site_80003424_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003424#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1ff3d4#21)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1ff3d4#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003424 hmem
  exact stepObs_jal σ i u (0x80003424#64) vminstret (0xbd4ff0ef#32) (0x1ff3d4#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80003424#64) 4)
    (0xef#8) (0xf0#8) (0x4f#8) (0xbd#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_bd4ff0ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt (0x80003424#64) 4)) hi

/-- 0x80003428: `j 0x800033ec` (jal x0, imm 0x1fffc4 → epilogue). -/
theorem site_80003428_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003428#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1fffc4#21)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x1fffc4#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003428 hmem
  exact stepObs_j σ i u (0x80003428#64) vminstret (0xfc5ff06f#32) (0x1fffc4#21)
    (0x6f#8) (0xf0#8) (0x5f#8) (0xfc#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fc5ff06f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt hi

/-! ## `Value_boolLoaded` survives an 8-byte spill write

Mirror `loaded_null_writeMap8`, for `value_bool`'s code `[0x800027f8, 0x8000280c)`.
Needed by `blockA_k`'s `hcalleeSurv` (the prologue `sd` spills). -/
theorem loaded_bool_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ 0x800027f8 ∨ 0x8000280c ≤ a8) (h : Value_boolLoaded mem) :
    Value_boolLoaded (writeMap8 mem a8 d) := by
  simp only [Value_boolLoaded, value_boolChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])

/-! ## `value_bool_spec_full` — strengthened `value_bool` (output + memFrame)

`bool_post` (`ValueSpec.lean`) carries `ValueRepr … (.bool _)` + the `NotWrittenV`
register frame, but NOT the console-output invariance or the sret-buffer memory
frame that `armTail_v` needs. This re-runs the five `value_bool` instructions
(`snez a1,a1; li a5,1; sw a1,8(a0); sw a5,0(a0); ret`), mirroring
`value_null_spec_full`'s output/memFrame threading, and adds those two facts to the
post. -/
theorem value_bool_spec_full (g : (R : Register) → Option (RegisterType R)) (buf vb r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (out0 : Array String) :
    Triple
      (fun c => GoodState c.σ ∧ Value_boolLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
        c.σ.regs.get? Register.PC = some (0x800027f8#64 : BitVec 64) ∧
        c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x11 = some vb ∧
        c.σ.regs.get? Register.x1 = some r ∧
        (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
        BoolRegion buf ∧ (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
        c.σ.sailOutput = out0 ∧
        (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R))
      (fun c => GoodState c.σ ∧
        c.σ.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
        c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x1 = some r ∧
        (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
        ValueRepr c.σ.mem N φc buf.toNat (.bool (vb != 0#64)) ∧
        c.σ.sailOutput = out0 ∧
        (∀ k : Nat, ¬ (buf.toNat ≤ k ∧ k < buf.toNat + 24) → m0[k]? = c.σ.mem[k]?) ∧
        MemExtends m0 c.σ.mem ∧
        (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)) := by
  intro c hpre
  obtain ⟨hG, hloaded, hmem, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick, hreg, hrettgt, hout, hframe⟩ := hpre
  have hpay := bool_pay_addr buf hreg
  have htag : (buf + sign_extend (m := 64) (0x000#12)).toNat = buf.toNat := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]
    rw [BitVec.add_zero]
  have htoh : tohostAddr = 0x8001ad00 := rfl
  let snezV : BitVec 64 := zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) vb))
  -- === 0x800027f8: snez a1,a1 (x11 := snez result) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800027f8 c.σ c.tick c.steps (0x800027f8#64) vmi vb hG hpc hmi ha1 hloaded rfl htick
  have hmem1eq : σ1.mem = c.σ.mem := by rw [hmem1]
  have hpc1 : σ1.regs.get? Register.PC = some (0x800027fc#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800027f8#64) 4 = (0x800027fc#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha1_1 : σ1.regs.get? Register.x11 = some snezV :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hloaded1 : Value_boolLoaded σ1.mem := by rw [hmem1eq]; exact hloaded
  -- === 0x800027fc: li a5,1 (x15 := 1) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800027fc σ1 i1 (c.steps + 1) (0x800027fc#64) vmi1 hG1 hpc1 hmi1 hloaded1 rfl hi1
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002800#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800027fc#64) 4 = (0x80002800#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha5_2 : σ2.regs.get? Register.x15 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hloaded2 : Value_boolLoaded σ2.mem := by rw [hmem2eq]; exact hloaded
  -- === 0x80002800: sw a1,8(a0) (writeMap4 at buf+8 with snez) ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002800 σ2 i2 (c.steps + 1 + 1) (0x80002800#64) vmi2 buf snezV hG2 hpc2 hmi2 ha0_2 ha1_2
      hloaded2 rfl
      (by rw [hpay]; have := hreg.lo; omega) (by rw [hpay]; have := hreg.hi; omega)
      (by rw [hpay]; have := hreg.win; omega) (by rw [hpay]; have := hreg.align; omega) hi2
  have hmem3' : σ3.mem = writeMap4 c.σ.mem (buf.toNat + 8) (swData snezV) := by
    rw [hmem3, mem_afterNextPC, hpay, hmem2eq]
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002804#64 : BitVec 64) := by
    have := obs_store_pc_val hobs3
    rwa [show BitVec.addInt (0x80002800#64) 4 = (0x80002804#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_store_other_val' hobs3 Register.x10 (by decide) ha0_2
  have hra_3 := obs_store_other_val' hobs3 Register.x1 (by decide) hra_2
  have ha5_3 := obs_store_other_val' hobs3 Register.x15 (by decide) ha5_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_val hobs3
  have hloaded3 : Value_boolLoaded σ3.mem := by
    rw [hmem3']
    exact loaded_bool_writeMap4 c.σ.mem (buf.toNat + 8) (swData snezV)
      (by have := hreg.code_disjoint; have := hreg.hi; omega) hloaded
  -- === 0x80002804: sw a5,0(a0) (writeMap4 at buf with tag 1) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002804 σ3 i3 (c.steps + 1 + 1 + 1) (0x80002804#64) vmi3 buf
      ((0#64) + sign_extend (m := 64) (0x001#12)) hG3 hpc3 hmi3 ha0_3 ha5_3 hloaded3 rfl
      (by rw [htag]; exact hreg.lo) (by rw [htag]; have := hreg.hi; omega)
      (by rw [htag]; have := hreg.win; omega) (by rw [htag]; have := hreg.align; omega) hi3
  have hmem4' : σ4.mem
      = writeMap4 (writeMap4 c.σ.mem (buf.toNat + 8) (swData snezV)) buf.toNat
          (swData ((0#64) + sign_extend (m := 64) (0x001#12))) := by
    rw [hmem4, mem_afterNextPC, htag, hmem3']
  have hpc4 : σ4.regs.get? Register.PC = some (0x80002808#64 : BitVec 64) := by
    have := obs_store_pc_val hobs4
    rwa [show BitVec.addInt (0x80002804#64) 4 = (0x80002808#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_store_other_val' hobs4 Register.x10 (by decide) ha0_3
  have hra_4 := obs_store_other_val' hobs4 Register.x1 (by decide) hra_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret_val hobs4
  have hloaded4 : Value_boolLoaded σ4.mem := by
    rw [hmem4']
    exact loaded_bool_writeMap4 (writeMap4 c.σ.mem (buf.toNat + 8) (swData snezV)) buf.toNat
      (swData ((0#64) + sign_extend (m := 64) (0x001#12)))
      (by have := hreg.code_disjoint; have := hreg.hi; omega)
      (loaded_bool_writeMap4 c.σ.mem (buf.toNat + 8) (swData snezV)
        (by have := hreg.code_disjoint; have := hreg.hi; omega) hloaded)
  -- === 0x80002808: ret ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80002808 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80002808#64) vmi4 r hG4 hpc4 hmi4 hra_4 hloaded4 rfl
      hrettgt hi4
  have hsteps : Steps c ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ :=
    ((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)
  have hout5 : σ5.sailOutput = c.σ.sailOutput := by
    rw [hobs5.out, sailOutput_sigmaPost_jump_x0, hobs4.out, sailOutput_sigmaPost_store,
      hobs3.out, sailOutput_sigmaPost_store, hobs2.out, sailOutput_sigmaPost_alu,
      hobs1.out, sailOutput_sigmaPost_alu]
  have hmem5eq : σ5.mem = writeMap4 (writeMap4 c.σ.mem (buf.toNat + 8) (swData snezV)) buf.toNat
      (swData ((0#64) + sign_extend (m := 64) (0x001#12))) := by rw [hmem5, hmem4']
  refine ⟨⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩, hsteps, hG5, obs_jr_pc hobs5,
    obs_jr_other' hobs5 Register.x10 (by decide) ha0_4,
    obs_jr_other' hobs5 Register.x1 (by decide) hra_4,
    obs_jr_minstret hobs5, hi5, ?_, hout5.trans hout, ?_, ?_,
    fun R hR => (frame_jr_v hobs5 R hR).trans
      ((frame_store_v hobs4 R hR).trans ((frame_store_v hobs3 R hR).trans
        ((frame_alu_v hobs2 R hR).trans ((frame_alu_snez hobs1 R hR).trans (hframe R hR)))))⟩
  · -- ValueRepr (.bool (vb≠0)): read32 buf = 1, read32 (buf+8) = cond (vb≠0) 1 0
    show ValueRepr σ5.mem N φc buf.toNat (.bool (vb != 0#64))
    refine ⟨?_, ?_⟩
    · show read32 σ5.mem buf.toNat = some 1
      rw [hmem5eq, read32_writeMap4, swData_toNat]; rfl
    · show read32 σ5.mem (buf.toNat + 8) = some (cond (vb != 0#64) 1 0)
      rw [hmem5eq, read32_writeMap4_disjoint _ _ _ _ (by omega), read32_writeMap4, snez_readback]
  · -- memFrame: outside [buf, buf+24) both writeMap4 writes pass through to m0 = c.σ.mem
    intro k hk
    rw [hmem5eq, getElem_writeMap4_disjoint _ _ _ _ (by omega),
        getElem_writeMap4_disjoint _ _ _ _ (by omega), hmem]
  · -- MemExtends m0 σ5.mem: the two writeMap4 writes only ADD presence.
    rw [hmem5eq, ← hmem]
    exact ((MemExtends.refl c.σ.mem).trans
      (memExtends_writeMap4 c.σ.mem (buf.toNat + 8) (swData snezV))).trans
      (memExtends_writeMap4 (writeMap4 c.σ.mem (buf.toNat + 8) (swData snezV)) buf.toNat
        (swData ((0#64) + sign_extend (m := 64) (0x001#12))))

/-! ## The `.bool` payload value bridge

The `lw a1,8(a2)` loads `payV = sign_extend (word32)` where `word32.toNat =
read32 ment (aExpr+8)`. `value_bool` produces `.bool (payV != 0#64)`. From
`ExprRepr ment aExpr (.bool b)`: for `b = true` the payload word is nonzero, for
`b = false` it is `0`. Since `sign_extend` preserves zero-ness of the 32-bit word,
`(payV != 0#64) = b`. -/

/-- Sign-extending a 32-bit word to 64 bits preserves whether it is zero. -/
theorem sext32_ne_zero (w : BitVec (8 * 4)) :
    ((sign_extend (m := 64) w : BitVec 64) != 0#64) = (w.toNat != 0) := by
  have hlt : w.toNat < 2 ^ 32 := w.isLt
  by_cases hz : w.toNat = 0
  · have hw0 : w = 0#32 := by apply BitVec.eq_of_toNat_eq; rw [hz]; rfl
    subst hw0
    rw [show (sign_extend (m := 64) (0#32) : BitVec 64) = 0#64 from by
      apply BitVec.eq_of_toNat_eq; simp only [sign_extend, Sail.BitVec.signExtend,
        BitVec.toNat_signExtend]; rfl]
    simp
  · have hne : (sign_extend (m := 64) w : BitVec 64).toNat ≠ 0 := by
      by_cases hmsb : w.msb = true
      · -- msb set: toNat ≥ 2^63 in the extension, certainly nonzero
        simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, hmsb,
          if_true, BitVec.toNat_setWidth]
        have : (2 ^ 64 - 2 ^ 32) ≠ 0 := by decide
        omega
      · -- msb clear: toNat = w.toNat ≠ 0
        simp only [Bool.not_eq_true] at hmsb
        simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, hmsb,
          Bool.false_eq_true, if_false, BitVec.toNat_setWidth, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by omega)]; exact hz
    rw [show ((sign_extend (m := 64) w : BitVec 64) != 0#64) = true from by
      simp only [bne_iff_ne, ne_eq]; intro h; exact hne (by rw [h]; rfl)]
    rw [show (w.toNat != 0) = true from by simp only [bne_iff_ne, ne_eq]; exact hz]

/-! ## `blockC_bool` — the `EX_BOOL` arm: `lw`, then `armTail_v`

`ArmEntryK … 0x80003420 Value_boolLoaded (.bool b) → PreEpilogueV … (.bool b)`.
Runs the payload `lw a1,8(a2)` (arm entry 0x80003420 → 0x80003424), then closes
the two-instruction tail `jal value_bool; j 0x800033ec` through `armTail_v` at the
jal PC `0x80003424` with `value_bool_spec_full`. -/
theorem blockC_bool
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (b : Bool)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem)
    -- the sret buffer is disjoint from `value_bool`'s code `[0x800027f8, 0x8000280c)`
    (hsret_vbool : sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK g N A SL φf φc st (0x80003420#64) Value_boolLoaded (.bool b)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c)
      (fun c => ∃ mpre, PreEpilogueV g N A SL φf φc st (.bool b) sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hc
  obtain ⟨ment, hG, htick, hpc, ha0, hs1, ha2, hsp, hra, hmiEx, hout, hmem, hcode, hviCode,
    hexpr, houtStr, hexprAl, hexprLo, hexprHi, hexprWin,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemframe_m0,
    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLlo, hSLwin, hSLloSp, hraAl, _hx11, _hx8, _hx18⟩ := hc
  obtain ⟨vmi, hmi⟩ := hmiEx
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- payload address no-wrap for `lw a1,8(a2)`
  have hpayaddr : (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 := by
    have hsext : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hsext, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := aExpr.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  -- the payload word value `bw = read32 ment (aExpr+8)` and `b = (bw ≠ 0)`,
  -- from `ExprRepr ment aExpr (.bool b)` (both `boolTrue`/`boolFalse` cases).
  obtain ⟨bw, hbw, hbeq⟩ : ∃ bw, read32 ment (aExpr.toNat + 8) = some bw ∧ (bw != 0) = b := by
    cases hexpr with
    | boolTrue hk hp hbne => exact ⟨_, hp, by simp only [bne_iff_ne, ne_eq]; exact hbne⟩
    | boolFalse hk hp => exact ⟨0, hp, by rfl⟩
  obtain ⟨pb0, pb1, pb2, pb3, hpb0, hpb1, hpb2, hpb3, hprec⟩ := read32_bytes ment (aExpr.toNat + 8) bw hbw
  -- the loaded payload BitVec value, and `(payV != 0) = b`
  let payV : BitVec 64 := sign_extend (m := 64) ((((pb3.append pb2).append pb1).append pb0) : BitVec (8 * 4))
  have hpayVnat : ((((pb3.append pb2).append pb1).append pb0) : BitVec (8 * 4)).toNat = bw := by
    rw [word_toNat_recon]; exact hprec
  have hbool : (payV != 0#64) = b := by
    show ((sign_extend (m := 64) ((((pb3.append pb2).append pb1).append pb0) : BitVec (8 * 4)) : BitVec 64) != 0#64) = b
    rw [sext32_ne_zero, hpayVnat]; exact hbeq
  -- ============ 0x80003420: lw a1,8(a2) → x11 := payV ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80003420_ee c.σ c.tick c.steps (0x80003420#64) vmi aExpr pb0 pb1 pb2 pb3
      hG hpc hmi ha2 (hmem ▸ hcode) rfl
      (by rw [hpayaddr]; omega) (by rw [hpayaddr]; omega)
      (by rw [hpayaddr, htoh]; right; omega) (by rw [hpayaddr]; omega)
      (by rw [hpayaddr, hmem]; exact hpb0) (by rw [hpayaddr, hmem]; exact hpb1)
      (by rw [hpayaddr, hmem]; exact hpb2) (by rw [hpayaddr, hmem]; exact hpb3) htick
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80003424#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80003420#64) 4 = (0x80003424#64:BitVec 64) from by decide] at this
  have hx11_1 : σ1.regs.get? Register.x11 = some payV :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have ha0_1 : σ1.regs.get? Register.x10 = some sret :=
    obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have hs1_1 : σ1.regs.get? Register.x9 = some sret :=
    obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp-1088#64) :=
    obs_alu_other' hobs1 Register.x2 (by decide) hsp
  have hra_1 : σ1.regs.get? Register.x1 = some r :=
    obs_alu_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hviCode1 : Value_boolLoaded σ1.mem := by rw [hmem1e]; exact hviCode
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  -- the epilogue g-frame across the `lw` (writes x11, excluded by AbiPreservedNoise)
  have hframe1 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      σ1.regs.get? R = g R := by
    intro R hR he8 he9 he18 he2
    have hab : AbiPreserved R = true := hR.1
    have abi_ne' : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false := by
      intro X hX
      rcases hXR : (X == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
    have hx11 : (Register.x11 == R) = false := abi_ne' (by decide)
    obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx11 hnpc' hmii')
    rw [f1]; exact hframe R ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ he8 he9 he18 he2
  have hBoolReg : BoolRegion sret := ⟨hsretAl, hsretLo, hsretHi, hsretWin, hsret_vbool⟩
  have hrettgt : (BitVec.update ((0x80003428#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt (0x80003428#64) (by decide)]; decide
  -- ============ 0x80003424: jal value_bool → PC := 0x800027f8, x1 := 0x80003428 ============
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80003424_ee σ1 i1 (c.steps + 1) (0x80003424#64) vmi1 hG1 hpc1 hmi1 hcode1 rfl
      (by rw [show (0x80003424#64 + sign_extend (m := 64) (0x1ff3d4#21) : BitVec 64) = 0x800027f8#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x800027f8#64) := by
    have := obs_jal_pc hobs2
    rwa [show (0x80003424#64 + sign_extend (m := 64) (0x1ff3d4#21) : BitVec 64) = 0x800027f8#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink2 : σ2.regs.get? Register.x1 = some (0x80003428#64) := by
    have := obs_jal_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80003424#64 : BitVec 64) 4 = (0x80003428#64:BitVec 64) from by decide] at this
  have ha0_2 : σ2.regs.get? Register.x10 = some sret := obs_jal_other' hobs2 Register.x10 (by decide) ha0_1
  have hx11_2 : σ2.regs.get? Register.x11 = some payV := obs_jal_other' hobs2 Register.x11 (by decide) hx11_1
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_jal_other' hobs2 Register.x9 (by decide) hs1_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp-1088#64) := obs_jal_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_jal_minstret hobs2
  have hviCode2 : Value_boolLoaded σ2.mem := by rw [hmem2e]; exact hviCode
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_jal]; exact hout1
  -- ============ jal callee: value_bool_spec_full at vb := payV ============
  obtain ⟨c3, hs3, hG3, hpc3, ha0_3, hlink3, hmi3, htick3, hval3, hout3, hmemframe3, _hMemExt3, hframe3⟩ :=
    value_bool_spec_full (fun R => σ2.regs.get? R) sret payV (0x80003428#64) N φc ment out0
      ⟨σ2, i2, c.steps + 1 + 1⟩
      ⟨hG2, hviCode2, hmem2e, hpc2, ha0_2, hx11_2, hlink2, ⟨vmi2, hmi2⟩, hi2, hBoolReg, hrettgt, hout2,
        fun R _ => rfl⟩
  -- produced value is `.bool (payV != 0#64) = .bool b`
  have hvalB : ValueRepr c3.σ.mem N φc sret.toNat (.bool b) := by
    rw [show ((.bool b) : Value) = .bool (payV != 0#64) from by rw [hbool]]; exact hval3
  -- recover callee-preserved regs: s1(x9), sp(x2) via NotWrittenV frame (= σ2 reads)
  have hs1_3 : c3.σ.regs.get? Register.x9 = some sret := by
    rw [hframe3 Register.x9 (by decide)]; exact hs1_2
  have hsp_3 : c3.σ.regs.get? Register.x2 = some (sp-1088#64) := by
    rw [hframe3 Register.x2 (by decide)]; exact hsp_2
  have hpc3' : c3.σ.regs.get? Register.PC = some (0x80003428#64) := by
    rw [hpc3, show (BitVec.update ((0x80003428#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1) = 0x80003428#64 from by apply BitVec.eq_of_toNat_eq; decide]
  -- memory agreement ment ↔ c3.mem outside the sret buffer
  have hAgree : AgreeP (fun k => ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24)) ment c3.σ.mem :=
    fun k hk => hmemframe3 k hk
  have hslotRa3 : read64 c3.σ.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by rcases hsretStk with h | h <;> omega)]; exact hslotRa
  have hslotS03 : read64 c3.σ.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by rcases hsretStk with h | h <;> omega)]; exact hslotS0
  have hslotS13 : read64 c3.σ.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by rcases hsretStk with h | h <;> omega)]; exact hslotS1
  have hslotS23 : read64 c3.σ.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by rcases hsretStk with h | h <;> omega)]; exact hslotS2
  have hstore3 : StoreRepr c3.σ.mem N A φf φc st.store :=
    hstoreSurv c3.σ.mem (fun k _ hk2 => hmemframe3 k hk2)
  have hcode3 : Eval_exprLoaded c3.σ.mem :=
    loaded_eval_expr_agreeP ment c3.σ.mem
      (fun k hk => hmemframe3 k (by rcases hsretEvalCode with h | h <;> omega)) (hmem1e ▸ hcode1)
  obtain ⟨vmi3, hmi3'⟩ := hmi3
  -- ============ 0x80003428: j 0x800033ec → PC := 0x800033ec ============
  obtain ⟨c4, i4', hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80003428_ee c3.σ c3.tick c3.steps (0x80003428#64) vmi3 hG3 hpc3' hmi3' hcode3 rfl
      (by rw [show (0x80003428#64 + sign_extend (m := 64) (0x1fffc4#21) : BitVec 64) = 0x800033ec#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide) htick3
  have hstep4 : Step c3 ⟨c4, i4', c3.steps + 1⟩ := by cases c3; exact hs4
  have hmem4e : c4.mem = c3.σ.mem := hmem4
  have hpc4 : c4.regs.get? Register.PC = some (0x800033ec#64) := by
    have := obs_jr_pc hobs4
    rwa [show (0x80003428#64 + sign_extend (m := 64) (0x1fffc4#21) : BitVec 64) = 0x800033ec#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hs1_4 : c4.regs.get? Register.x9 = some sret := obs_jr_other' hobs4 Register.x9 (by decide) hs1_3
  have hsp_4 : c4.regs.get? Register.x2 = some (sp-1088#64) := obs_jr_other' hobs4 Register.x2 (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_jr_minstret hobs4
  have hout4 : c4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_jump_x0]; exact hout3
  -- assemble PreEpilogueV at `.bool b`
  refine ⟨⟨c4, i4', c3.steps + 1⟩, ?_, c4.mem, hG4, hi4, hpc4, hs1_4, hsp_4, ⟨_, hmi4⟩, hout4, houtStr,
    rfl, hmem4e ▸ hcode3, hmem4e ▸ hvalB, hmem4e ▸ hstore3,
    ?_,
    hmem4e ▸ hslotRa3, hmem4e ▸ hslotS03, hmem4e ▸ hslotS13, hmem4e ▸ hslotS23,
    hgx8, hgx9, hgx18, hgx2, ?_,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩
  · -- the composed run: step1(lw) ; step2(jal) ; callee steps ; step4(j)
    exact (Steps.single hstep1).trans ((Steps.single hstep2).trans (hs3.trans (Steps.single hstep4)))
  · -- the epilogue g-frame: callee-saved (excl x8/x9/x18/x2) preserved across block C.
    intro R hR he8 he9 he18 he2
    have hab : AbiPreserved R = true := hR.1
    have abi_ne' : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false := by
      intro X hX
      rcases hXR : (X == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
    have hx11 : (Register.x11 == R) = false := abi_ne' (by decide)
    have hx15 : (Register.x15 == R) = false := abi_ne' (by decide)
    have hx1 : (Register.x1 == R) = false := abi_ne' (by decide)
    obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    -- σ1: lw writes x11
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx11 hnpc' hmii')
    -- σ2: jal writes x1
    have f2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' hx1 hnpc' hmii')
    -- c3: value_bool NotWrittenV frame
    have f3 : c3.σ.regs.get? R = σ2.regs.get? R := by
      rw [hframe3 R ⟨hx11, hx15, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩]
    -- c4: j writes PC
    have f4 : c4.regs.get? R = c3.σ.regs.get? R :=
      (hobs4.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    rw [f4, f3, f2, f1]
    exact hframe R ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ he8 he9 he18 he2
  · -- memFrame: mpre (= c3.mem) vs m0.
    intro aa haa _
    rw [hmem4e]
    by_cases hsr : sret.toNat ≤ aa ∧ aa < sret.toNat + 24
    · exact Or.inl hsr
    · exact Or.inr ((hmemframe3 aa hsr).symm.trans (hmemframe_m0 aa haa))

/-! ## `BoolSlotPinned` — the `EX_BOOL` (tag 2) jump-table slot pin

The slot at `jumpTableBase + 8` holds `c8 94 fe ff` (LE) = offset `0xfffe94c8`,
and `0x80019f58 + (Int32)0xfffe94c8 = 0x80003420` (the bool arm). Mirrors
`NullSlotPinned`; discharges `KindSlotPinned 2 0x80003420` for the loaded image. -/
def BoolSlotPinned (m : Mem) : Prop :=
  m[(jumpTableBase + 8 : Nat)]? = some (0xc8 : BitVec 8) ∧
  m[(jumpTableBase + 9 : Nat)]? = some (0x94 : BitVec 8) ∧
  m[(jumpTableBase + 10 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(jumpTableBase + 11 : Nat)]? = some (0xff : BitVec 8)

theorem bool_slot_kindPinned {m : Mem} (h : BoolSlotPinned m) :
    KindSlotPinned 2 (0x80003420#64) m := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨0xc8#8, 0x94#8, 0xfe#8, 0xff#8, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using p0
  · simpa using p1
  · simpa using p2
  · simpa using p3
  · apply BitVec.eq_of_toNat_eq; simp only [jumpTableBase]; decide

/-! ## `EvalBoolEntry` — the machine precondition for the `EvalE.bool` case

Mirrors `EvalNullEntry` (`EvalNullSim.lean`), but carries `BoolSlotPinned` +
`Value_boolLoaded` (with the value_bool geometry) in place of the null-specific
`null_slot`/`value_null_code`, and `ExprRepr … (.bool b)` (`read32 = 2`). -/
structure EvalBoolEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Vsa.While.Addr) (b : Bool)
    (sp r sret aEnv aExpr : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 evalExprEntry)
  a0 : c.σ.regs.get? Register.x10 = some sret
  a1 : c.σ.regs.get? Register.x11 = some aEnv
  a2 : c.σ.regs.get? Register.x12 = some aExpr
  ra : c.σ.regs.get? Register.x1 = some r
  ra_align : r.toNat % 4 = 0
  spReg : c.σ.regs.get? Register.x2 = some sp
  stackOK : StackOK SL sp (1088 + 1088)
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  mem : c.σ.mem = m0
  code : InterpCodeLoaded c.σ.mem
  expr : ExprRepr c.σ.mem aExpr.toNat (.bool b)
  store : StoreRepr c.σ.mem N A φf φc st.store
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
      c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  out : OutRepr c.σ st
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R
  code_stack_disjoint : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  expr_stack_disjoint : aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  expr_align : aExpr.toNat % 8 = 0
  expr_ram : 0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000
  expr_win : tohostAddr + 16 ≤ aExpr.toNat
  sret_align : sret.toNat % 8 = 0
  sret_ram : 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000
  sret_win : tohostAddr + 16 ≤ sret.toNat
  /-- sret disjoint from the `value_int` code — the shared `ArmEntryK` field. For
  the bool arm this is unused geometrically but kept so `ArmEntryK` is satisfied. -/
  sret_vicode_disjoint : sret.toNat + 24 ≤ 0x8000280c ∨ 0x8000281c ≤ sret.toNat
  /-- sret disjoint from the `value_bool` code `[0x800027f8, 0x8000280c)` — the
  bool callee's sret-write region (`BoolRegion.code_disjoint`). -/
  sret_vboolcode_disjoint : sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat
  sret_stack_disjoint : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat
  sret_evalcode_disjoint : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat
  /-- `value_bool` code `[0x800027f8, 0x8000280c)` disjoint from the stack region —
  keeps `Value_boolLoaded` across the prologue spills. -/
  vboolcode_stack_disjoint : (0x8000280c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027f8
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  value_bool_code : Value_boolLoaded c.σ.mem
  bool_slot : BoolSlotPinned c.σ.mem
  table_stack_disjoint : (0x80019f58 : Nat) + 16 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 8
  spill_defined : (∃ v, c.σ.regs.get? Register.x8 = some v) ∧
    (∃ v, c.σ.regs.get? Register.x9 = some v) ∧ (∃ v, c.σ.regs.get? Register.x18 = some v)

/-- The `EX_BOOL` kind tag `read32 = some 2`, from `ExprRepr … (.bool b)`. -/
theorem exprRepr_bool_kind {m : Mem} {a : Nat} {b : Bool} (h : ExprRepr m a (.bool b)) :
    read32 m a = some 2 := by
  cases h with
  | boolTrue hk _ _ => exact hk
  | boolFalse hk _ => exact hk

/-- **The `EvalE.bool` simulation goal.** -/
def EvalBoolSimGoal : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Addr) (b : Bool)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    EvalE st d a (.bool b) st (.bool b) →
    Triple
      (EvalBoolEntry g N A SL φf φc st d a b sp r sret aEnv aExpr m0)
      (EvalExit g N A SL φf φc st (.bool b) sp r sret m0)

/-- **The M4 `EvalE.bool` gate.** Composes `blockA_k` (prologue + dispatch →
`ArmEntryK` at the bool arm), `blockC_bool` (arm + `value_bool` → epilogue entry),
and `blockD_v` at `.bool b` (epilogue → return). -/
theorem evalBoolSim : EvalBoolSimGoal := by
  intro g N A SL φf φc st d a b sp r sret aEnv aExpr m0 _hEvalE
  intro c hc
  -- === block A: prologue + dispatch → ArmEntryK (via blockA_k) ===
  have hkm0 : read32 m0 aExpr.toNat = some 2 := hc.mem ▸ exprRepr_bool_kind hc.expr
  obtain ⟨c1, hs1, ment, v8, v9, v18, hArm⟩ :=
    blockA_k g N A SL φf φc st (.bool b) 2 (0x80003420#64) Value_boolLoaded
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      (bool_slot_kindPinned (hc.mem ▸ hc.bool_slot)) (hc.mem ▸ hc.value_bool_code)
      (fun mem a8 dd hlo hhi hh => by
        have hvb := hc.vboolcode_stack_disjoint
        exact loaded_bool_writeMap8 mem a8 dd (by omega) hh)
      (fun m' hag => by
        -- ExprRepr m' aExpr (.bool b) from read32 m' (aExpr) = read32 m0 = some 2
        -- AND read32 m' (aExpr+8) = read32 m0 (aExpr+8) (the payload word survives).
        have hstk := hc.expr_stack_disjoint
        have hlo := hc.stackOK.1
        -- the surviving kind word (aExpr)
        have hkindSurv : read32 m' aExpr.toNat = some 2 := by
          obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hrec⟩ := read32_bytes m0 aExpr.toNat 2 hkm0
          simp only [read32, readLE, bind, Option.bind]
          rw [← hag aExpr.toNat (by omega), ← hag (aExpr.toNat + 1) (by omega),
              ← hag (aExpr.toNat + 2) (by omega), ← hag (aExpr.toNat + 3) (by omega),
              hb0, hb1, hb2, hb3]
          simp only []; apply congrArg some; omega
        -- the surviving payload word (aExpr+8)
        have hpaySurv : ∀ bw, read32 m0 (aExpr.toNat + 8) = some bw →
            read32 m' (aExpr.toNat + 8) = some bw := by
          intro bw hbw
          obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hrec⟩ := read32_bytes m0 (aExpr.toNat + 8) bw hbw
          simp only [read32, readLE, bind, Option.bind]
          rw [← hag (aExpr.toNat + 8) (by omega), ← hag (aExpr.toNat + 8 + 1) (by omega),
              ← hag (aExpr.toNat + 8 + 2) (by omega), ← hag (aExpr.toNat + 8 + 3) (by omega),
              hb0, hb1, hb2, hb3]
          simp only []; apply congrArg some; omega
        cases (hc.mem ▸ hc.expr) with
        | boolTrue hk hp hbne => exact ExprRepr.boolTrue hkindSurv (hpaySurv _ hp) hbne
        | boolFalse hk hp => exact ExprRepr.boolFalse hkindSurv (hpaySurv _ hp))
      (by decide)
      (by have := hc.table_stack_disjoint; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
      hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
      hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_align, hc.expr_ram,
      hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint,
      hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
      hc.spill_defined⟩, rfl⟩
  -- === block C: arm (lw a1,8(a2); jal value_bool; j) → PreEpilogueV (.bool b) ===
  obtain ⟨c2, hs2, mpre, hPre⟩ :=
    blockC_bool g N A SL φf φc st b sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0
      hc.sret_vboolcode_disjoint c1 ⟨ment, hArm⟩
  -- === block D: epilogue → EvalExit (.bool b) ===
  obtain ⟨c3, hs3, hExit, _⟩ :=
    blockD_v g N A SL φf φc st (.bool b) sp r sret v8 v9 v18 c.σ.sailOutput m0 (fun _ => True)
      c2 ⟨mpre, hPre, trivial⟩
  exact ⟨c3, (hs1.trans hs2).trans hs3, hExit⟩

end Vsa.Sim
