import Vsa.Sim.EvalRecCommon
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch09Part03
import Vsa.Sim.DecodeTable.Batch14Part06
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 pilot RECURSIVE case: the `EX_UNARY` arm head (`blockB_unary`)

The FIRST recursive `EvalE` case walk: the `EX_UNARY` arm of `eval_expr`
(`ExprKind` tag `k = 8`, jump-table slot bytes `88 96 fe ff` @ `0x80019f78`,
arm PC `0x800035e0`). Decoded machine path (`experiments/pctrace.md`):

```
800035e0: ld   a2,16(a2)      -- a2 := e->as.unary.operand
800035e4: addi a0,sp,144      -- a0 := sub-result buffer (sp' + 144 = sp - 944)
800035e8: jal  80003164       -- RECURSIVE eval_expr(subsret, in, operand, env)
-- post-call (op dispatch): --
800035ec: lw   a4,8(s0)       -- op (T_MINUS = 12 → neg @ 0x800039ac; else not)
…
800039ac..800039dc (neg):     -- kind check (VAL_INT = 2), neg a1,a1,
                              -- mv a0,s1, jal value_int, j 0x800033ec
```

This module lands the arm HEAD: the three sites (`ld`/`addi`/`jal`) and
**`blockB_unary`** — from the dispatch landing (`ArmEntryK` at `0x800035e0`
plus the recursive-case extras `blockA_k` does not yet expose) through the
payload load, the sub-buffer setup, and the recursive call *composed with the
induction hypothesis* (`armTail_rec`, `EvalRecCommon.lean`), to
`SubEvalReturn`: control back at `0x800035ec` with the sub-value represented
at `sp - 944`, the store re-represented for the sub-derivation's post state,
the outer frame's spill slots intact, and `eval_expr` still loaded.

`blockB_unary` is op-agnostic (`neg` and `not` share the arm head; the op is
inspected only post-call). The post-call `neg` tail
(`0x800035ec–f8, 0x800039ac–dc` + `value_int` + `blockD_v`) is the next
module (`blockC_neg`); the residuals for wiring `blockA_k` into this case are
recorded in `memory/m4-recursive-cases.md`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The three `EX_UNARY` arm-head sites (@0x800035e0/e4/e8) -/

/-- 0x800035e0: `ld a2,16(a2)` (`0x01063603`) — the operand pointer. Writes `x12`. -/
theorem site_800035e0_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vexpr : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some vexpr)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800035e0#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vexpr + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (vexpr + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vexpr + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vexpr + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (vexpr + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vexpr + sign_extend (m := 64) (0x010#12)).toNat]? = some b0)
    (h1 : σ.mem[(vexpr + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vexpr + sign_extend (m := 64) (0x010#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vexpr + sign_extend (m := 64) (0x010#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vexpr + sign_extend (m := 64) (0x010#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vexpr + sign_extend (m := 64) (0x010#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vexpr + sign_extend (m := 64) (0x010#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vexpr + sign_extend (m := 64) (0x010#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_800035e0 hmem
  have hx12₂ : (afterNextPC (afterPrelude σ) (0x800035e0#64)).regs.get? Register.x12 = some vexpr := by
    rw [get?_afterNextPC σ (0x800035e0#64) _ (by decide) (by decide)]; exact hx12
  exact stepObs_alu σ i u (0x800035e0#64) vminstret (0x01063603#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, false, 8))
    Register.x12 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x36#8) (0x06#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_01063603 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800035e0#64) (0x010#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5)
      (sigma3_alu σ (0x800035e0#64) Register.x12
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vexpr b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x12 _ vexpr hx12₂)
      (wX_bits_x12 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- `addi a0,sp,144` execute characterization (rd = x10, rs1 = x2). -/
theorem exec_addi_a0_sp144_un (σ : MState) (pc : BitVec 64) (vsp : BitVec 64)
    (hx2 : σ.regs.get? Register.x2 = some vsp) :
    (execute (instruction.ITYPE (0x090#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0a#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 (vsp + sign_extend (m := 64) (0x090#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx2
  exact execute_itype_addi_char (0x090#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0a#5) vsp
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x10 (vsp + sign_extend (m := 64) (0x090#12)))
    (rX_bits_x2 _ vsp h₂) (wX_bits_x10 _ (vsp + sign_extend (m := 64) (0x090#12)))

/-- 0x800035e4: `addi a0,sp,144` (`0x09010513`) — the sub-result buffer. Writes `x10`. -/
theorem site_800035e4_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800035e4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (vsp + sign_extend (m := 64) (0x090#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_800035e4 hmem
  exact stepObs_alu σ i u (0x800035e4#64) vminstret (0x09010513#32)
    (instruction.ITYPE (0x090#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (vsp + sign_extend (m := 64) (0x090#12)) (0x13#8) (0x05#8) (0x01#8) (0x09#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_09010513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a0_sp144_un σ (0x800035e4#64) vsp hx2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800035e8: `jal eval_expr` (`0xb7dff0ef`, imm `0x1ffb7c` → `0x80003164`,
rd = x1 = ra). THE recursive call. -/
theorem site_800035e8_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800035e8#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1ffb7c#21)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1ffb7c#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_800035e8 hmem
  exact stepObs_jal σ i u (0x800035e8#64) vminstret (0xb7dff0ef#32) (0x1ffb7c#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800035e8#64) 4)
    (0xef#8) (0xf0#8) (0xdf#8) (0xb7#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_b7dff0ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt (0x800035e8#64) 4)) hi

/-! ## The unary-arm callee bundle

The dispatch must carry through the spills everything the ARM (not just one
`value_*` callee) needs loaded: the sub-call's `EvalEntry` demands
`Value_intLoaded` AND the `EX_INT` jump-table slot (`IntSlotPinned` — the
operand may be an int literal), and the `neg` tail itself calls `value_int`.
This is the `calleeLoaded` instantiation for `blockA_k` at this arm. -/
/-- Wave 47f (`GeomFrom`): the recursive-arm callee bundle also carries the
null/bool/str pins so child `EvalEntry.nbs_pins` can be filled. -/
def UnaryArmCallee (m : Mem) : Prop := Value_intLoaded m ∧ IntSlotPinned m ∧ NBSPins m

/-! ## `blockB_unary` — arm head + recursive call, composed with the IH

`ArmEntryK` (at arm PC `0x800035e0`, callee bundle `UnaryArmCallee`, expression
`.unary op esub`) plus the RECURSIVE-CASE EXTRAS — facts the current
`blockA_k`/`ArmEntryK` do not yet thread (recorded as the `ArmEntryK` widening
residual): the live `a1 = interp*` register, the call-point ghost frame `gpre`,
the operand node's `ExprRepr` + geometry, the extra 1088-byte stack headroom,
and the arena/code/table disjointness facts. Output: `SubEvalReturn` at the
link PC `0x800035ec` with sub-result buffer `(sp - 1088) + 144`, plus the
memory frame of the pre-call memory against the case entry memory `m0`. -/
theorem blockB_unary
    (gouter gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (op : UnOp) (esub : Expr) (vsub : Value)
    (sp r sret aExpr aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hIH : EvalIH st d env esub st' vsub) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800035e0#64) UnaryArmCallee (.unary op esub)
          sp r sret aExpr aIn v8 v9 v18 out0 m0 ment c ∧
        -- ===== recursive-case extras (the ArmEntryK widening residual) =====
        c.σ.regs.get? Register.x11 = some aIn ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        read64 ment (aExpr.toNat + 16) = some aOperand.toNat ∧
        ExprRepr ment aOperand.toNat esub ∧
        -- WAVE 47i: the child's entry-ground bundle (derived at the sim from
        -- `hc.ground` via `EvalGround.child_at`).
        EvalGround ment SL A (sp - 1088#64)
          ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aOperand.toNat esub ∧
        aExpr.toNat + 24 ≤ 0x100000000 ∧
        aOperand.toNat % 8 = 0 ∧
        0x80000000 ≤ aOperand.toNat ∧ aOperand.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aOperand.toNat ∧
        (aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        SL.hi ≤ 0x100000000 ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
        ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        -- ITEM ZERO B1: the operand's recursion-sound budget at `sp - 1088`, its
        -- `.fn`-bodies bound, and the store-bodies invariant (threaded from the
        -- parent `.unary op esub` node's budget by the arm-entry supplier).
        StackOK SL (sp - 1088#64)
          (esub.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget esub = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget)
      (fun c => ∃ mcall,
        SubEvalReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' vsub sp r sret
          ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) (0x800035ec#64)
          v8 v9 v18 mcall c ∧
        (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?)) := by
  intro c hpre
  obtain ⟨ment, hArm, hx11, hgframe, hg8, hg18, hpay, hsubexpr, hground, hexprHi24,
    hopAl, hopLo, hopHi, hopWin, hopStk,
    hsproom, hspSLhi, hsp16, hSLhiRam,
    hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
    hstackBudget, hexprBodies, hstoreBodies⟩ := hpre
  obtain ⟨hG, htick, hpc, ha0, hs1, ha2, hsp, hra, ⟨vmi, hmi⟩, hout, hmem, hcode, hviCode,
    hexpr, houtStr, hexprAl, hexprLo, hexprHi, hexprWin,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemframe_m0,
    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLlo, hSLwin, hSLloSp, hraAl,
    _hAEx11, _hAEx8, _hAEx18⟩ := hArm
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨hviInt, hviSlot, hnbs⟩ : Value_intLoaded ment ∧ IntSlotPinned ment ∧ NBSPins ment := hviCode
  -- address arithmetic
  have h16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have haddr16 : (aExpr + sign_extend (m := 64) (0x010#12)).toNat = aExpr.toNat + 16 := by
    rw [h16, BitVec.toNat_add]
    have hv : (16#64 : BitVec 64).toNat = 16 := by decide
    rw [hv]; omega
  -- operand-pointer bytes (an sd-free read64 → 8 byte pins + sext reassembly)
  obtain ⟨pb0, pb1, pb2, pb3, pb4, pb5, pb6, pb7, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hpsext⟩ :=
    spill_roundtrip_ee ment (aExpr.toNat + 16) aOperand hpay
  -- ============ 0x800035e0: ld a2,16(a2) → x12 := aOperand ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_800035e0_ee c.σ c.tick c.steps (0x800035e0#64) vmi aExpr pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
      hG hpc hmi ha2 (hmem ▸ hcode) rfl
      (by rw [haddr16]; omega) (by rw [haddr16]; omega)
      (by rw [haddr16, htoh]; right; omega) (by rw [haddr16]; omega)
      (by rw [haddr16, hmem]; exact hp0) (by rw [haddr16, hmem]; exact hp1)
      (by rw [haddr16, hmem]; exact hp2) (by rw [haddr16, hmem]; exact hp3)
      (by rw [haddr16, hmem]; exact hp4) (by rw [haddr16, hmem]; exact hp5)
      (by rw [haddr16, hmem]; exact hp6) (by rw [haddr16, hmem]; exact hp7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x800035e4#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800035e0#64) 4 = (0x800035e4#64 : BitVec 64) from by decide] at this
  have hx12_1 : σ1.regs.get? Register.x12 = some aOperand := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hpsext] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some sret := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hx11_1 : σ1.regs.get? Register.x11 = some aIn := obs_alu_other' hobs1 Register.x11 (by decide) hx11
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by
    rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- ============ 0x800035e4: addi a0,sp,144 → x10 := (sp-1088) + 144 ============
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_800035e4_ee σ1 i1 (c.steps + 1) (0x800035e4#64) vmi1 (sp - 1088#64)
      hG1 hpc1 hmi1 hsp_1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x800035e8#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800035e4#64) 4 = (0x800035e8#64 : BitVec 64) from by decide] at this
  have hx10_2 : σ2.regs.get? Register.x10
      = some ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  have hx11_2 : σ2.regs.get? Register.x11 = some aIn := obs_alu_other' hobs2 Register.x11 (by decide) hx11_1
  have hx12_2 : σ2.regs.get? Register.x12 = some aOperand := obs_alu_other' hobs2 Register.x12 (by decide) hx12_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by
    rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  -- the call-point ghost frame: `gpre` survives the two ALU writes (x12, x10)
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have hframeB : ∀ R : Register, AbiPreservedNoise R → σ2.regs.get? R = gpre R := by
    intro R hR
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have h12R : (Register.x12 == R) = false := abi_ne' (by decide) hab
    have h10R : (Register.x10 == R) = false := abi_ne' (by decide) hab
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h12R hnpcR hmiiR)
    have f2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h10R hnpcR hmiiR)
    rw [f2, f1]; exact hgframe R hR'
  -- sub-result buffer arithmetic: (sp-1088) + 144 = sp - 944
  have hsub944 : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by omega) hsp1088
  -- ============ 0x800035e8 (jal) + the sub-call, via armTail_rec ============
  obtain ⟨c3, hs3, hpost⟩ :=
    armTail_rec gpre N A SL φf φc st st' d env esub vsub
      (0x800035e8#64) (0x800035ec#64) (0x1ffb7c#21)
      sp r sret ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aIn aOperand v8 v9 v18
      out0 ment
      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (by decide)
      (fun σ i u vmi hGσ hpcσ hmiσ hcodeσ hiσ =>
        site_800035e8_ee σ i u (0x800035e8#64) vmi hGσ hpcσ hmiσ hcodeσ rfl
          (by
            rw [show ((0x800035e8#64 : BitVec 64) + sign_extend (m := 64) (0x1ffb7c#21))
              = (0x80003164#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide]
            decide) hiσ)
      hIH
      ⟨σ2, i2, c.steps + 1 + 1⟩
      ⟨hG2, hi2, hpc2, hx10_2, hs1_2, hx11_2, hx12_2, hsp_2, ⟨vmi2, hmi2⟩, hout2, houtStr,
        hmem2e, hcode, hviInt, hviSlot, hnbs, hground, hsubexpr, hstore, hstoreSurv, hframeB, ⟨hg8, hg18⟩,
        hslotRa, hslotS0, hslotS1, hslotS2,
        hopAl, hopLo, hopHi, hopWin, hopStk,
        (by rw [hsub944]; omega), (by rw [hsub944]; omega), (by rw [hsub944]; omega),
        hsproom, hspSLhi, hsp16, hsphi, hSLlo, hSLhiRam, hSLwin,
        hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
        hstackBudget, hexprBodies, hstoreBodies⟩
  exact ⟨c3, (Steps.single hstep1).trans ((Steps.single hstep2).trans hs3),
    ment, hpost, hmemframe_m0⟩

end Vsa.Sim
