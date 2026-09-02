import Vsa.Sim.EvalRecCommon
import Vsa.Sim.EvalNegSim
import Vsa.Sim.EvalNegSim2
import Vsa.Sim.EvalNotSim
import Vsa.Sim.EvalIntSim2
import Vsa.Sim.LogicalSites
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.EvalBoolSim
import Vsa.Sim.ObsAvoid
import Vsa.Sim.LoadSitesTotB
import Vsa.Sim.EntryGroundKit

/-!
# Layer 4 — M4 recursive case: the logical `.and` short-circuit (`evalAndSim`)

The FIRST control-flow-bearing expression case. Unlike every other `EvalE` case,
the compiled `EX_LOGICAL` arm SHORT-CIRCUITS: it evaluates the left operand, tests
its truthiness, and either short-circuits (`.and` with a falsy left → `.bool false`)
or evaluates the right operand.

Decoded machine path (`experiments/pctrace.md`, jump-table slot 7 @0x80019f6c →
arm `0x8000355c`; verified against `riscv64-elf-objdump -d`):

```
8000355c: ld   a2,16(a2)      # a2 := e->as.logical.left  (offset 16)
80003560: addi a0,sp,120      # a0 := sub-sret_L = (sp-1088)+120 = sp-968
80003564: sd   a3,0(sp)       # spill env (a3) to sp-1088  (reloaded @3598, RIGHT path)
80003568: jal  eval_expr      # eval LEFT; ra := 0x8000356c
-- post-call: op dispatch --
8000356c: lw   a4,8(s0)       # op token (s0 = Expr*, callee-saved)
80003570: li   a5,25          # LOGIC_OR token = 25
80003574: ld   a2,120(sp)     # a2 := lv kind dword @ sub-sret_L
80003578: beq  a4,a5,80003978 # OR vs AND split  (op==25 → OR; .and falls through)
-- .and arm (op != 25): copy lv into the value_truthy arg buffer sp+64 --
8000357c: ld   a4,128(sp)     # lv payload
80003580: ld   a5,136(sp)     # lv[16..24)
80003584: addi a0,sp,64       # a0 := value_truthy arg buf = sp-1024
80003588: sd   a2,64(sp)      # copy lv kind
8000358c: sd   a4,72(sp)      # copy lv payload
80003590: sd   a5,80(sp)      # copy lv[16..24)
80003594: jal  value_truthy   # a0 := lv.truthy ; ra = 0x80003598
80003598: ld   a3,0(sp)       # reload env  (dead on the false arm)
8000359c: beqz a0,800036d4    # SHORT-CIRCUIT: lv.truthy==false → 0x800036d4
-- and-false block @0x800036d4 (lv.truthy = false) --
800036d4: li   a1,0           # a1 := 0 (false)
800036d8: mv   a0,s1          # a0 := outer sret
800036dc: jal  value_bool     # value_bool(sret, false) → .bool false ; ra = 0x800036e0
800036e0: j    800033ec       # shared epilogue → blockD_v_rec
```

(The truthy arm — `800035a0..800035dc`: eval RIGHT, `value_truthy(rv)`, `value_bool` —
is the `andTrue` constructor; left as remaining, see the report.)

This module lands the arm HEAD `blockB_logical` (the analogue of `blockB_unary`,
but with the env-spill `sd a3,0(sp)` before the `jal` and the `sp+120` sub-sret
offset), from the widened `ArmEntryK` at `0x8000355c` through the LEFT recursive
call composed with the induction hypothesis (`armTail_rec`), to `SubEvalReturn` at
`0x8000356c`.

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

/-! ## The `EX_LOGICAL` arm callee bundle

The dispatch carries `Value_truthyLoaded` and `Value_boolLoaded` (both callees the
arm invokes) plus, for the recursive sub-call's `EvalEntry`, `Value_intLoaded` and
`IntSlotPinned` (the left/right sub-expression may itself be an int literal). -/
/-- Wave 47f (`GeomFrom`): also carries the null/bool/str pins (child
`EvalEntry.nbs_pins`). -/
def LogicalArmCallee (m : Mem) : Prop :=
  Value_intLoaded m ∧ IntSlotPinned m ∧ Value_truthyLoaded m ∧ Value_boolLoaded m ∧ NBSPins m

/-! ## `blockB_logical` — arm head + LEFT recursive call, composed with the IH

`ArmEntryK` (at arm PC `0x8000355c`, callee bundle `LogicalArmCallee`, expression
`.logical op el er`) plus the recursive-case extras (identical shape to
`blockB_unary`'s: the live `a1 = interp*`, the call-point ghost frame `gpre`, the
LEFT-operand node's `ExprRepr` + geometry, the extra 1088-byte headroom, and the
arena/code/table disjointness). The LEFT operand `el` sits at node offset 16, so
its pointer is `read64 ment (aExpr+16)` (same slot the unary operand uses).

The head differs from `blockB_unary` only by the interleaved env-spill
`sd a3,0(sp)` (writing the pre-call memory `mcall = writeMap8 ment (sp-1088) …`)
and the `sp+120` sub-result buffer (`subsret_L = sp-968`).

Output: `SubEvalReturn` at the link PC `0x8000356c` with sub-result buffer
`(sp-1088)+120`, plus the frame of the pre-call memory `mcall` against `m0` outside
the scribbled stack window. -/
theorem blockB_logical
    (gouter gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (op : LogOp) (el er : Expr) (vl : Value)
    (sp r sret aExpr aIn aLeft aEnv3 : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hIH : EvalIH st d env el st' vl) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x8000355c#64) LogicalArmCallee (.logical op el er)
          sp r sret aExpr aIn v8 v9 v18 out0 m0 ment c ∧
        -- ===== recursive-case extras (mirrors `blockB_unary`) =====
        c.σ.regs.get? Register.x11 = some aIn ∧
        c.σ.regs.get? Register.x13 = some aEnv3 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        read64 ment (aExpr.toNat + 16) = some aLeft.toNat ∧
        -- LEFT-operand `ExprRepr`-survival (mirrors `blockB_binary`'s `lexpr_surv`):
        -- a generic `ExprRepr`-agreeP lemma over an arbitrary sub-tree is not
        -- available, so it is threaded as a survival closure keyed to the stack window.
        (∀ m' : Mem,
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m'[a]?) →
          ExprRepr m' aLeft.toNat el) ∧
        -- WAVE 47i: the parent node's entry-ground bundle at the arm entry
        -- (the LEFT child is derived inside via the `EntryGroundKit`).
        EvalGround ment SL A sp sret aExpr.toNat (.logical op el er) ∧
        aExpr.toNat + 24 ≤ 0x100000000 ∧
        aLeft.toNat % 8 = 0 ∧
        0x80000000 ≤ aLeft.toNat ∧ aLeft.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aLeft.toNat ∧
        (aLeft.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aLeft.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        SL.hi ≤ 0x100000000 ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
        ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        -- ITEM ZERO B1: the LEFT operand's recursion-sound budget at `sp - 1088`,
        -- its `.fn`-bodies bound, and the store-bodies invariant (threaded from
        -- the parent `.logical op el er` node's budget by the arm-entry supplier).
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget)
      (fun c => ∃ mcall,
        SubEvalReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' vl sp r sret
          ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) (0x8000356c#64)
          v8 v9 v18 mcall c ∧
        (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?)) := by
  intro c hpre
  obtain ⟨ment, hArm, hx11, hx13, hgframe, hg8, hg18, hpay, hexprSurv, hgroundP, hexprHi24,
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
  obtain ⟨hviInt, hviSlot, hviTruthy, hviBool, hnbs⟩ :
      Value_intLoaded ment ∧ IntSlotPinned ment ∧ Value_truthyLoaded ment ∧ Value_boolLoaded ment ∧
        NBSPins ment :=
    hviCode
  -- address arithmetic for the LEFT-operand load (offset 16) and sub-sret (offset 120)
  have h16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have haddr16 : (aExpr + sign_extend (m := 64) (0x010#12)).toNat = aExpr.toNat + 16 := by
    rw [h16, BitVec.toNat_add]
    have hv : (16#64 : BitVec 64).toNat = 16 := by decide
    rw [hv]; omega
  -- the sub-result buffer offset (sp-1088)+120 = sp-968
  have hsub968 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by omega) hsp1088
  -- the env-spill addr (sp-1088)+0 = sp-1088
  have hspill0 : ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 :=
    spill_addr sp (0x000#12) 1088 (by decide) (by omega) hsp1088
  -- operand-pointer bytes (an sd-free read64 → 8 byte pins + sext reassembly)
  obtain ⟨pb0, pb1, pb2, pb3, pb4, pb5, pb6, pb7, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hpsext⟩ :=
    spill_roundtrip_ee ment (aExpr.toNat + 16) aLeft hpay
  -- ============ 0x8000355c: ld a2,16(a2) → x12 := aLeft ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_8000355c_totb c.σ c.tick c.steps (0x8000355c#64) vmi aExpr pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
      hG hpc hmi ha2 (hmem ▸ hcode) rfl
      (by rw [haddr16]; omega) (by rw [haddr16]; omega)
      (by rw [haddr16, htoh]; right; omega) (by rw [haddr16]; omega)
      (by rw [haddr16, hmem]; try (first | exact hp0 | exact lpin_of_present hp0)) (by rw [haddr16, hmem]; try (first | exact hp1 | exact lpin_of_present hp1))
      (by rw [haddr16, hmem]; try (first | exact hp2 | exact lpin_of_present hp2)) (by rw [haddr16, hmem]; try (first | exact hp3 | exact lpin_of_present hp3))
      (by rw [haddr16, hmem]; try (first | exact hp4 | exact lpin_of_present hp4)) (by rw [haddr16, hmem]; try (first | exact hp5 | exact lpin_of_present hp5))
      (by rw [haddr16, hmem]; try (first | exact hp6 | exact lpin_of_present hp6)) (by rw [haddr16, hmem]; try (first | exact hp7 | exact lpin_of_present hp7)) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80003560#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000355c#64) 4 = (0x80003560#64 : BitVec 64) from by decide] at this
  have hx12_1 : σ1.regs.get? Register.x12 = some aLeft := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hpsext] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some sret := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hx11_1 : σ1.regs.get? Register.x11 = some aIn := obs_alu_other' hobs1 Register.x11 (by decide) hx11
  have hx13_1 : σ1.regs.get? Register.x13 = some aEnv3 := obs_alu_other' hobs1 Register.x13 (by decide) hx13
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by
    rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- ============ 0x80003560: addi a0,sp,120 → x10 := (sp-1088) + 120 ============
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80003560_lg σ1 i1 (c.steps + 1) (0x80003560#64) vmi1 (sp - 1088#64)
      hG1 hpc1 hmi1 hsp_1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x80003564#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80003560#64) 4 = (0x80003564#64 : BitVec 64) from by decide] at this
  have hx10_2 : σ2.regs.get? Register.x10
      = some ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  have hx11_2 : σ2.regs.get? Register.x11 = some aIn := obs_alu_other' hobs2 Register.x11 (by decide) hx11_1
  have hx12_2 : σ2.regs.get? Register.x12 = some aLeft := obs_alu_other' hobs2 Register.x12 (by decide) hx12_1
  have hx13_2 : σ2.regs.get? Register.x13 = some aEnv3 := obs_alu_other' hobs2 Register.x13 (by decide) hx13_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by
    rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  have hcode2 : Eval_exprLoaded σ2.mem := by rw [hmem2e]; exact hcode
  -- ============ 0x80003564: sd a3,0(sp) → mcall := writeMap8 ment (sp-1088) (sdData_val aEnv3) ============
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_80003564_lg σ2 i2 (c.steps + 1 + 1) (0x80003564#64) vmi2 (sp - 1088#64) aEnv3
      hG2 hpc2 hmi2 hsp_2 hx13_2 hcode2 rfl
      (by rw [hspill0]; omega) (by rw [hspill0]; omega)
      (by rw [hspill0, htoh]; omega) (by rw [hspill0]; omega) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  -- the pre-call memory
  let mcall : Mem := writeMap8 ment (sp.toNat - 1088) (sdData_val aEnv3)
  have hmcalldef : mcall = writeMap8 ment (sp.toNat - 1088) (sdData_val aEnv3) := rfl
  have hmem3e : σ3.mem = mcall := by
    rw [hmem3, hmcalldef]
    have hmi : (afterNextPC (afterPrelude σ2) (0x80003564#64)).mem = ment := by
      rw [mem_afterNextPC, mem_afterPrelude]; exact hmem2e
    rw [hmi, hspill0]
  have hpc3 : σ3.regs.get? Register.PC = some (0x80003568#64) := by
    have := obs_store_pc hobs3
    rwa [show BitVec.addInt (0x80003564#64) 4 = (0x80003568#64 : BitVec 64) from by decide] at this
  have hx10_3 : σ3.regs.get? Register.x10
      = some ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) :=
    obs_store_other' hobs3 Register.x10 (by decide) hx10_2
  have hs1_3 : σ3.regs.get? Register.x9 = some sret := obs_store_other' hobs3 Register.x9 (by decide) hs1_2
  have hx11_3 : σ3.regs.get? Register.x11 = some aIn := obs_store_other' hobs3 Register.x11 (by decide) hx11_2
  have hx13_3 : σ3.regs.get? Register.x13 = some aEnv3 := obs_store_other' hobs3 Register.x13 (by decide) hx13_2
  have hx12_3 : σ3.regs.get? Register.x12 = some aLeft := obs_store_other' hobs3 Register.x12 (by decide) hx12_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_store_other' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret hobs3
  have hout3 : σ3.sailOutput = out0 := by
    rw [hobs3.out, sailOutput_sigmaPost_store]; exact hout2
  -- ===== the env-spill preserves everything armTail_rec needs (write at sp-1088 ∈ [SL.lo,sp)) =====
  -- agreement: mcall agrees with ment away from [sp-1088, sp-1080)
  have hAgSpill : ∀ k : Nat, ¬ (sp.toNat - 1088 ≤ k ∧ k < sp.toNat - 1088 + 8) →
      mcall[k]? = ment[k]? := by
    intro k hk
    rw [hmcalldef, getElem_writeMap8_disjoint ment (sp.toNat - 1088) k (sdData_val aEnv3) (by omega)]
  -- mcall ↔ m0 outside the scribbled stack window [SL.lo, sp)
  have hMcallM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]? := by
    intro a ha
    rw [hAgSpill a (by omega)]; exact hmemframe_m0 a ha
  -- Eval_exprLoaded mcall (code disjoint from the spill window ⊂ stack)
  have hcodeMcall : Eval_exprLoaded mcall :=
    loaded_eval_expr_agreeP ment mcall
      (fun a ha => (hAgSpill a (by rcases hcodeStk with h | h <;> omega)).symm) hcode
  -- Value_intLoaded mcall
  have hviIntMcall : Value_intLoaded mcall :=
    loaded_value_int_agreeP ment mcall
      (fun a ha => (hAgSpill a (by rcases hviStk with h | h <;> omega)).symm) hviInt
  -- IntSlotPinned mcall (jump-table slot disjoint from stack)
  have hviSlotMcall : IntSlotPinned mcall := by
    obtain ⟨q0, q1, q2, q3⟩ := hviSlot
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (rw [hAgSpill _ (by simp only [jumpTableBase] at *; rcases htableStk with h | h <;> omega)]; assumption)
  -- NBSPins mcall (value_* text + slots 1-3 disjoint from the spill window ⊂ stack)
  have hnbsMcall : NBSPins mcall :=
    hnbs.transport
      (fun a ha => (hAgSpill a (by rcases hviStk with h | h <;> omega)).symm)
      (fun a ha => (hAgSpill a (by rcases htableStk with h | h <;> omega)).symm)
  -- ExprRepr mcall aLeft el (operand node disjoint from stack; via the survival closure)
  have hExprMcall : ExprRepr mcall aLeft.toNat el :=
    hexprSurv mcall (fun a ha => (hAgSpill a (by omega)).symm)
  -- StoreRepr mcall (uses the entry survival clause: change confined to the spill window ⊂ stack)
  have hStoreMcall : StoreRepr mcall N A φf φc st.store := by
    refine hstoreSurv mcall (fun k hk1 _ => ?_)
    exact (hAgSpill k (by omega)).symm
  -- StoreRepr survival for mcall (compose the entry survival with the spill-window peel)
  have hStoreSurvMcall : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        mcall[k]? = m'[k]?) → StoreRepr m' N A φf φc st.store := by
    intro m' hag
    refine hstoreSurv m' (fun k hk1 hk2 => ?_)
    rw [← hag k hk1 hk2, hAgSpill k (by omega)]
  -- spill slots [sp-8/16/24/32] survive (disjoint from [sp-1088, sp-1080))
  have hslotRaMcall : read64 mcall (sp.toNat - 8) = some r.toNat := by
    rw [read64_agreeP (P := fun k => sp.toNat - 8 ≤ k ∧ k < sp.toNat) (m := mcall) (m' := ment)
      (fun j hj => hAgSpill j (by omega)) (fun j hj => by omega)]; exact hslotRa
  have hslotS0Mcall : read64 mcall (sp.toNat - 16) = some v8.toNat := by
    rw [read64_agreeP (P := fun k => sp.toNat - 16 ≤ k ∧ k < sp.toNat - 8) (m := mcall) (m' := ment)
      (fun j hj => hAgSpill j (by omega)) (fun j hj => by omega)]; exact hslotS0
  have hslotS1Mcall : read64 mcall (sp.toNat - 24) = some v9.toNat := by
    rw [read64_agreeP (P := fun k => sp.toNat - 24 ≤ k ∧ k < sp.toNat - 16) (m := mcall) (m' := ment)
      (fun j hj => hAgSpill j (by omega)) (fun j hj => by omega)]; exact hslotS1
  have hslotS2Mcall : read64 mcall (sp.toNat - 32) = some v18.toNat := by
    rw [read64_agreeP (P := fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat - 24) (m := mcall) (m' := ment)
      (fun j hj => hAgSpill j (by omega)) (fun j hj => by omega)]; exact hslotS2
  -- the call-point ghost frame: `gpre` survives the two ALU writes (x12, x10) + the store
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have hframeB : ∀ R : Register, AbiPreservedNoise R → σ3.regs.get? R = gpre R := by
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
    have f3 : σ3.regs.get? R = σ2.regs.get? R :=
      (hobs3.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_store _ _ _ _ R hmiR hpcR hnpcR hmiiR)
    rw [f3, f2, f1]; exact hgframe R hR'
  -- WAVE 47i: the LEFT child's entry-ground bundle (kit moves 1+2+3; the
  -- env-spill is inside the scribble, so the off-stack transport carries it).
  have hGroundMc : EvalGround mcall SL A sp sret aExpr.toNat (.logical op el er) :=
    hgroundP.transport_offstack htableStk hspSLhi
      (fun a ha => hAgSpill a (by have := hsproom; have := hSLlo; omega))
  have hpayMc : read64 mcall (aExpr.toNat + 16) = some aLeft.toNat := by
    have hag := evalGround_ast_read64_agree hgroundP hspSLhi
      (fun a ha => hAgSpill a (by have := hsproom; have := hSLlo; omega))
      (off := 16) (by omega)
    rw [hag]; exact hpay
  have hspsubL : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have hGroundChildL : EvalGround mcall SL A (sp - 1088#64)
      ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) aLeft.toNat el :=
    hGroundMc.child_params (fun lo hi hin => exprIn_logical_left hin aLeft.toNat hpayMc)
      htableStk hspSLhi (by omega)
      (by rw [hsub968]; have := hsproom; have := hSLlo; omega)
      (by rw [hsub968]; have := hsproom; have := hSLlo; omega)
  -- ============ 0x80003568 (jal) + the sub-call, via armTail_rec ============
  obtain ⟨c4, hs4, hpost⟩ :=
    armTail_rec gpre N A SL φf φc st st' d env el vl
      (0x80003568#64) (0x8000356c#64) (0x1ffbfc#21)
      sp r sret ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) aIn aLeft v8 v9 v18
      out0 mcall
      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (by decide)
      (fun σ i u vmi hGσ hpcσ hmiσ hcodeσ hiσ =>
        site_80003568_lg σ i u (0x80003568#64) vmi hGσ hpcσ hmiσ hcodeσ rfl hiσ)
      hIH
      ⟨σ3, i3, c.steps + 1 + 1 + 1⟩
      ⟨hG3, hi3, hpc3, hx10_3, hs1_3, hx11_3, ⟨_, hx13_3⟩, hx12_3, hsp_3, ⟨vmi3, hmi3⟩, hout3, houtStr,
        hmem3e, hcodeMcall, hviIntMcall, hviSlotMcall, hnbsMcall, hGroundChildL, hExprMcall, hStoreMcall, hStoreSurvMcall,
        hframeB, ⟨hg8, hg18⟩,
        hslotRaMcall, hslotS0Mcall, hslotS1Mcall, hslotS2Mcall,
        hopAl, hopLo, hopHi, hopWin, hopStk,
        (by rw [hsub968]; omega), (by rw [hsub968]; omega), (by rw [hsub968]; omega),
        hsproom, hspSLhi, hsp16, hsphi, hSLlo, hSLhiRam, hSLwin,
        hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
        hstackBudget, hexprBodies, hstoreBodies⟩
  exact ⟨c4, (Steps.single hstep1).trans ((Steps.single hstep2).trans
      ((Steps.single hstep3).trans hs4)),
    mcall, hpost, hMcallM0⟩

/-! ## `LogicalBufExtras` — the value_truthy arg-buffer geometry (mirrors `NotExtras`)

The `value_truthy` arg buffer lives at `sp - 1024` (`sp'+64`), the LEFT sub-value
at `sp - 968` (`sp'+120`). Same shape as `EvalNotSim.NotExtras` but keyed to the
`sp-968` source. -/
structure LogicalBufExtras
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φc' : Addr → Nat)
    (vl : Value) (sp sret : BitVec 64) (m : Mem) : Prop where
  buf_lo : 0x80000000 + 1024 ≤ sp.toNat
  buf_win : tohostAddr + 16 + 1024 ≤ sp.toNat
  pay_disj : ∀ (p : Nat) (s : String),
    ValueRepr m N φc' (sp.toNat - 968) vl → read64 m (sp.toNat - 968 + 8) = some p →
    ∀ k, k ≤ s.length → (p + k < sp.toNat - 1024 ∨ sp.toNat - 1024 + 24 ≤ p + k)

/-! ## `blockC_andFalse` — the `.and` post-call short-circuit (falsy left) tail

From `SubEvalReturn @0x8000356c` (LEFT value `vl` at `sp-968`) for a
`.logical .and el er` node with `vl.truthy = false`, the machine short-circuits:
op-dispatch (`beq` NOT taken since `logOpTok .and = 24 ≠ 25`), copy `vl` into the
`value_truthy` arg buffer `sp-1024`, `value_truthy(vl) = 0`, `beqz` TAKEN →
`0x800036d4` (`li a1,0; mv a0,s1; jal value_bool`), producing `.bool false`.

Output: `PreEpilogueVD … (.bool false) 0x800033ec` (fed to `blockD_v_rec`). -/
theorem blockC_andFalse
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : Vsa.While.St) (vl : Value)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (el er : Expr) (m0 : Mem)
    (hvlfalse : vl.truthy = false) :
    Triple
      (fun c => ∃ mcall,
        SubEvalReturn gpre N A SL φf φc nf nc st' vl sp r sret
          ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) (0x8000356c#64)
          v8 v9 v18 mcall c ∧
        gpre Register.x8 = some aExpr ∧
        ExprRepr mcall aExpr.toNat (.logical .and el er) ∧
        -- WAVE 47i (`McallPopTotality` amendment): presence ONLY on the actual
        -- dead-byte read footprint — the lowered-frame window `[sp-1120, sp)`
        -- plus the node's line-word bytes `[aExpr+4, aExpr+8)` — replacing the
        -- REFUTED total-population oracle.
        -- WAVE 48k: the dead-byte presence conjunct is GONE (total reads).
        -- presence-monotonicity over the entry `m0` (`mem_ext` residual).
        MemExtends m0 mcall ∧
        aExpr.toNat % 4 = 0 ∧
        0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 8 ≤ aExpr.toNat ∧
        (aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat) ∧
        (aExpr.toNat + 16 ≤ A.lo ∨ A.hi ≤ aExpr.toNat) ∧
        (aExpr.toNat + 16 ≤ sp.toNat - 968 ∨ sp.toNat - 968 + 24 ≤ aExpr.toNat) ∧
        String.join out0.toList = st'.out ∧
        sret.toNat % 8 = 0 ∧ 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ sret.toNat ∧
        (sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat) ∧
        (sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat) ∧
        r.toNat % 4 = 0 ∧
        SL.lo + 1088 ≤ sp.toNat ∧ 0x80000000 ≤ SL.lo ∧ tohostAddr + 16 ≤ SL.lo ∧
        c.σ.sailOutput = out0 ∧
        Value_truthyLoaded mcall ∧ Value_boolLoaded mcall ∧
        (∀ φc' : Addr → Nat, ValueRepr c.σ.mem N φc' (sp.toNat - 968) vl →
          LogicalBufExtras N A SL φc' vl sp sret c.σ.mem) ∧
        (sp.toNat ≤ 0x8000282c ∨ 0x8000285c ≤ SL.lo) ∧
        (sp.toNat ≤ 0x800027f8 ∨ 0x8000280c ≤ SL.lo) ∧
        (sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat) ∧
        (A.hi ≤ 0x8000282c ∨ 0x8000285c ≤ A.lo) ∧
        (A.hi ≤ 0x800027f8 ∨ 0x8000280c ≤ A.lo) ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        (SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi) ∧
        (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
          mcall[a]? = m0[a]?) ∧
        sp.toNat ≤ 0x100000000 ∧ sp.toNat % 8 = 0 ∧ SL.hi ≤ 0x100000000 ∧ sp.toNat ≤ SL.hi ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (fun c => ∃ (mpre : Mem) (φfe φce : Addr → Nat),
        PhiExtends φf φfe nf ∧
        PhiExtends φc φce nc ∧
        PreEpilogueVD g N A SL φfe φce st' (.bool false) sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hpre
  obtain ⟨mcall, hSub, hgx8, hexpr, hMemExtM0, hexprAl, hexprLo, hexprHi, hexprWin,
    hexprSL, hexprA, hexprSub,
    houtStr, hsretAl, hsretLo, hsretHi, hsretWin, hsretStk, hsretEvalCode,
    hraAl, hSLloSp, hSLlo, hSLwin,
    hout0eq, hVtruthyMcall, hVboolMcall, hBufExtras, hTruthyStk, hBoolStk, hSretBoolCode,
    hTruthyArena, hBoolArena, hcodeStk, hsretInSL, hMcallM0,
    hsphiRam, hsp8, hSLhiRam, hspSLhi, hgv8, hgv9, hgv18, hgv2, hbridge⟩ := hpre
  obtain ⟨hG, htick, hpc, ha0, hra, hs1, hsp, ⟨vmi, hmi⟩, hout, hframe,
    ⟨φcv, hpcv, hvalSub⟩, hstoreBundle, hcode,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemFrame, hMemExt⟩ := hSub
  obtain ⟨φf', φc', hpf', hpc', hstore', hstoreSurv'⟩ := hstoreBundle
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp1088 : 1088 ≤ sp.toNat := by omega
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have hsub968 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by omega) hsp1088
  -- the sub-value at subsret = sp-968 at c.σ.mem (φcv-extended)
  have hvalSub' : ValueRepr c.σ.mem N φcv (sp.toNat - 968) vl := by rwa [hsub968] at hvalSub
  have hBE : LogicalBufExtras N A SL φcv vl sp sret c.σ.mem := hBufExtras φcv hvalSub'
  -- x8 = aExpr (callee-saved survives the sub-call)
  have hx8 : c.σ.regs.get? Register.x8 = some aExpr := (hframe Register.x8 (by decide)).trans hgx8
  -- op-token addr aExpr+8
  have hop8 : (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 := by
    have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hs, BitVec.toNat_add]; have hv : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [hv]; have := aExpr.isLt; rw [Nat.mod_eq_of_lt (by omega)]
  -- ExprRepr (.logical .and el er): kind = 7, op-token = logOpTok .and = 24
  obtain ⟨lptr, rptr, hk7, hoptok, hlptr, hlR, hrptr, hrR⟩ : ∃ lp rp,
      read32 mcall aExpr.toNat = some 7 ∧ read32 mcall (aExpr.toNat + 8) = some (logOpTok .and) ∧
      read64 mcall (aExpr.toNat + 16) = some lp ∧ ExprRepr mcall lp el ∧
      read64 mcall (aExpr.toNat + 24) = some rp ∧ ExprRepr mcall rp er := by
    cases hexpr with | logical hk htok hl hlp hr hrp => exact ⟨_, _, hk, htok, hl, hlp, hr, hrp⟩
  have hoptok24 : read32 mcall (aExpr.toNat + 8) = some 24 := by simpa [logOpTok] using hoptok
  obtain ⟨ob0, ob1, ob2, ob3, hob0, hob1, hob2, hob3, hobrec⟩ :=
    read32_bytes mcall (aExpr.toNat + 8) 24 hoptok24
  -- op-token bytes with VALUE in c.σ.mem (aExpr node is AST memory, agrees with mcall)
  have hAgOp : ∀ k : Nat, aExpr.toNat + 8 ≤ k → k < aExpr.toNat + 12 →
      c.σ.mem[k]? = mcall[k]? := by
    intro k hk1 hk2
    rcases hmemFrame k
      (by rw [hspsub] at *; rcases hexprSL with h | h <;> omega)
      (by rcases hexprA with h | h <;> omega) with hin | heq
    · exact absurd hin (by rcases hexprSub with h | h <;> omega)
    · exact heq
  have hoc0 : c.σ.mem[aExpr.toNat + 8]? = some ob0 := (hAgOp _ (by omega) (by omega)).trans hob0
  have hoc1 : c.σ.mem[aExpr.toNat + 8 + 1]? = some ob1 := (hAgOp _ (by omega) (by omega)).trans hob1
  have hoc2 : c.σ.mem[aExpr.toNat + 8 + 2]? = some ob2 := (hAgOp _ (by omega) (by omega)).trans hob2
  have hoc3 : c.σ.mem[aExpr.toNat + 8 + 3]? = some ob3 := (hAgOp _ (by omega) (by omega)).trans hob3
  -- the op-token loaded value = 24#64, the li a5,25 = 25#64
  have hopVal : (sign_extend (m := 64) ((((ob3.append ob2).append ob1).append ob0) : BitVec (8*4)))
      = (24#64 : BitVec 64) := by
    rw [sext_word_small _ 24 (by decide) (by rw [word_toNat_recon]; exact hobrec)]
  have hli25 : ((0#64 : BitVec 64) + sign_extend (m := 64) (0x019#12)) = (25#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hne2425 : ((24#64 : BitVec 64) == (25#64 : BitVec 64)) = false := by decide
  -- the whole 24-byte sub-Value buffer bytes at c.σ.mem[sp-968 .. +24) (present).
  -- WAVE 48k: TOTAL reads.  The model's `readByte` is `getD 0`, so these dead
  -- sub-`Value`/node bytes need no map presence at all — each is simply NAMED
  -- as its own total read.  (This replaces the refuted `frame_pop` oracle;
  -- the window hypothesis is kept so every call site is unchanged.)
  have hStackPopC : ∀ a : Nat,
      (sp.toNat - 1120 ≤ a ∧ a < sp.toNat) ∨
        (aExpr.toNat + 4 ≤ a ∧ a < aExpr.toNat + 8) →
      ∃ b : BitVec 8, (c.σ.mem[a]?).getD 0 = b :=
    fun _ _ => ⟨_, rfl⟩
  obtain ⟨kb0, hkb0⟩ := hStackPopC (sp.toNat - 968) (by omega)
  obtain ⟨kb1, hkb1⟩ := hStackPopC (sp.toNat - 968 + 1) (by omega)
  obtain ⟨kb2, hkb2⟩ := hStackPopC (sp.toNat - 968 + 2) (by omega)
  obtain ⟨kb3, hkb3⟩ := hStackPopC (sp.toNat - 968 + 3) (by omega)
  obtain ⟨kb4, hkb4⟩ := hStackPopC (sp.toNat - 968 + 4) (by omega)
  obtain ⟨kb5, hkb5⟩ := hStackPopC (sp.toNat - 968 + 5) (by omega)
  obtain ⟨kb6, hkb6⟩ := hStackPopC (sp.toNat - 968 + 6) (by omega)
  obtain ⟨kb7, hkb7⟩ := hStackPopC (sp.toNat - 968 + 7) (by omega)
  obtain ⟨pb0, hpb0⟩ := hStackPopC (sp.toNat - 960) (by omega)
  obtain ⟨pb1, hpb1⟩ := hStackPopC (sp.toNat - 960 + 1) (by omega)
  obtain ⟨pb2, hpb2⟩ := hStackPopC (sp.toNat - 960 + 2) (by omega)
  obtain ⟨pb3, hpb3⟩ := hStackPopC (sp.toNat - 960 + 3) (by omega)
  obtain ⟨pb4, hpb4⟩ := hStackPopC (sp.toNat - 960 + 4) (by omega)
  obtain ⟨pb5, hpb5⟩ := hStackPopC (sp.toNat - 960 + 5) (by omega)
  obtain ⟨pb6, hpb6⟩ := hStackPopC (sp.toNat - 960 + 6) (by omega)
  obtain ⟨pb7, hpb7⟩ := hStackPopC (sp.toNat - 960 + 7) (by omega)
  obtain ⟨qb0, hqb0⟩ := hStackPopC (sp.toNat - 952) (by omega)
  obtain ⟨qb1, hqb1⟩ := hStackPopC (sp.toNat - 952 + 1) (by omega)
  obtain ⟨qb2, hqb2⟩ := hStackPopC (sp.toNat - 952 + 2) (by omega)
  obtain ⟨qb3, hqb3⟩ := hStackPopC (sp.toNat - 952 + 3) (by omega)
  obtain ⟨qb4, hqb4⟩ := hStackPopC (sp.toNat - 952 + 4) (by omega)
  obtain ⟨qb5, hqb5⟩ := hStackPopC (sp.toNat - 952 + 5) (by omega)
  obtain ⟨qb6, hqb6⟩ := hStackPopC (sp.toNat - 952 + 6) (by omega)
  obtain ⟨qb7, hqb7⟩ := hStackPopC (sp.toNat - 952 + 7) (by omega)
  -- the three load values reassembled (kind K into x12, PV into x14, QV into x15)
  let K13 : BitVec 64 := sign_extend (m := 64)
    ((((((((kb7.append kb6).append kb5).append kb4).append kb3).append kb2).append kb1).append kb0) : BitVec (8*8))
  let PV : BitVec 64 := sign_extend (m := 64)
    ((((((((pb7.append pb6).append pb5).append pb4).append pb3).append pb2).append pb1).append pb0) : BitVec (8*8))
  let QV : BitVec 64 := sign_extend (m := 64)
    ((((((((qb7.append qb6).append qb5).append qb4).append qb3).append qb2).append qb1).append qb0) : BitVec (8*8))
  -- addresses of the tail loads (120/128/136) and stores (64/72/80) as sp - k
  have haddr120 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 := hsub968
  have haddr128 : ((sp - 1088#64) + sign_extend (m := 64) (0x080#12)).toNat = sp.toNat - 960 :=
    spill_addr sp (0x080#12) 960 (by decide) (by omega) hsp1088
  have haddr136 : ((sp - 1088#64) + sign_extend (m := 64) (0x088#12)).toNat = sp.toNat - 952 :=
    spill_addr sp (0x088#12) 952 (by decide) (by omega) hsp1088
  have haddr64 : ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)).toNat = sp.toNat - 1024 :=
    spill_addr sp (0x040#12) 1024 (by decide) (by omega) hsp1088
  have haddr72 : ((sp - 1088#64) + sign_extend (m := 64) (0x048#12)).toNat = sp.toNat - 1016 :=
    spill_addr sp (0x048#12) 1016 (by decide) (by omega) hsp1088
  have haddr80 : ((sp - 1088#64) + sign_extend (m := 64) (0x050#12)).toNat = sp.toNat - 1008 :=
    spill_addr sp (0x050#12) 1008 (by decide) (by omega) hsp1088
  ------------------------------------------------------------------------
  -- 0x8000356c → 0x80003584: op check (beq NOT taken), loads, addi.
  ------------------------------------------------------------------------
  -- 0x8000356c: lw a4,8(s0) → x14 := 24 (op token)
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_8000356c_totb c.σ c.tick c.steps (0x8000356c#64) vmi aExpr
      ob0 ob1 ob2 ob3 hG hpc hmi hx8 hcode rfl
      (by rw [hop8]; omega) (by rw [hop8]; omega)
      (by rw [hop8, htoh]; right; omega) (by rw [hop8]; omega)
      (by rw [hop8]; try (first | exact hoc0 | exact lpin_of_present hoc0)) (by rw [hop8]; try (first | exact hoc1 | exact lpin_of_present hoc1))
      (by rw [hop8]; try (first | exact hoc2 | exact lpin_of_present hoc2)) (by rw [hop8]; try (first | exact hoc3 | exact lpin_of_present hoc3)) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = c.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80003570#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000356c#64) 4 = (0x80003570#64 : BitVec 64) from by decide] at this
  have hx14_1 : σ1.regs.get? Register.x14 = some (24#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hopVal] at this
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  have hx8_1 : σ1.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs1 Register.x8 (by decide) hx8
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout0eq
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- 0x80003570: li a5,25 → x15 := 25
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80003570_lg σ1 i1 (c.steps + 1) (0x80003570#64) vmi1 hG1 hpc1 hmi1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = c.σ.mem := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x80003574#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80003570#64) 4 = (0x80003574#64 : BitVec 64) from by decide] at this
  have hx15_2 : σ2.regs.get? Register.x15 = some (25#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hli25] at this
  have hx14_2 : σ2.regs.get? Register.x14 = some (24#64) := obs_alu_other' hobs2 Register.x14 (by decide) hx14_1
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  have hcode2 : Eval_exprLoaded σ2.mem := by rw [hmem2e]; exact hcode
  -- 0x80003574: ld a2,120(sp) → x12 := K13 (kind dword)
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_80003574_totb σ2 i2 (c.steps + 1 + 1) (0x80003574#64) vmi2 (sp - 1088#64)
      kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7 hG2 hpc2 hmi2 hsp_2 hcode2 rfl
      (by rw [haddr120]; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, htoh]; right; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, hmem2e]; exact hkb0) (by rw [haddr120, hmem2e]; exact hkb1)
      (by rw [haddr120, hmem2e]; exact hkb2) (by rw [haddr120, hmem2e]; exact hkb3)
      (by rw [haddr120, hmem2e]; exact hkb4) (by rw [haddr120, hmem2e]; exact hkb5)
      (by rw [haddr120, hmem2e]; exact hkb6) (by rw [haddr120, hmem2e]; exact hkb7) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  have hmem3e : σ3.mem = c.σ.mem := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x80003578#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80003574#64) 4 = (0x80003578#64 : BitVec 64) from by decide] at this
  have hx12_3 : σ3.regs.get? Register.x12 = some K13 :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx14_3 : σ3.regs.get? Register.x14 = some (24#64) := obs_alu_other' hobs3 Register.x14 (by decide) hx14_2
  have hx15_3 : σ3.regs.get? Register.x15 = some (25#64) := obs_alu_other' hobs3 Register.x15 (by decide) hx15_2
  have hs1_3 : σ3.regs.get? Register.x9 = some sret := obs_alu_other' hobs3 Register.x9 (by decide) hs1_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_alu]; exact hout2
  have hcode3 : Eval_exprLoaded σ3.mem := by rw [hmem3e]; exact hcode
  -- 0x80003578: beq a4,a5 (NOT taken, 24 != 25) → 0x8000357c
  obtain ⟨σ4, i4, hs4', hi4, hG4, hmem4, hobs4⟩ :=
    site_80003578_nottaken_lg σ3 i3 (c.steps + 1 + 1 + 1) (0x80003578#64) vmi3 (24#64) (25#64)
      hG3 hpc3 hmi3 hx14_3 hx15_3 hcode3 rfl hne2425 hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4'
  have hmem4e : σ4.mem = c.σ.mem := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000357c#64) := by
    have := obs_branch_nottaken_pc hobs4
    rwa [show BitVec.addInt (0x80003578#64) 4 = (0x8000357c#64 : BitVec 64) from by decide] at this
  have hx12_4 : σ4.regs.get? Register.x12 = some K13 := obs_branch_nottaken_other' hobs4 Register.x12 (by decide) hx12_3
  have hs1_4 : σ4.regs.get? Register.x9 = some sret := obs_branch_nottaken_other' hobs4 Register.x9 (by decide) hs1_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_nottaken_other' hobs4 Register.x2 (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_branch_nottaken_minstret hobs4
  have hout4 : σ4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_branch_nottaken]; exact hout3
  have hcode4 : Eval_exprLoaded σ4.mem := by rw [hmem4e]; exact hcode
  -- 0x8000357c: ld a4,128(sp) → x14 := PV
  obtain ⟨σ5, i5, hs5', hi5, hG5, hmem5, hobs5⟩ :=
    site_8000357c_totb σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000357c#64) vmi4 (sp - 1088#64)
      pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 hG4 hpc4 hmi4 hsp_4 hcode4 rfl
      (by rw [haddr128]; omega) (by rw [haddr128]; omega)
      (by rw [haddr128, htoh]; right; omega) (by rw [haddr128]; omega)
      (by rw [haddr128, hmem4e]; try (first | exact hpb0 | exact lpin_of_present hpb0)) (by rw [haddr128, hmem4e]; try (first | exact hpb1 | exact lpin_of_present hpb1))
      (by rw [haddr128, hmem4e]; try (first | exact hpb2 | exact lpin_of_present hpb2)) (by rw [haddr128, hmem4e]; try (first | exact hpb3 | exact lpin_of_present hpb3))
      (by rw [haddr128, hmem4e]; try (first | exact hpb4 | exact lpin_of_present hpb4)) (by rw [haddr128, hmem4e]; try (first | exact hpb5 | exact lpin_of_present hpb5))
      (by rw [haddr128, hmem4e]; try (first | exact hpb6 | exact lpin_of_present hpb6)) (by rw [haddr128, hmem4e]; try (first | exact hpb7 | exact lpin_of_present hpb7)) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5'
  have hmem5e : σ5.mem = c.σ.mem := by rw [hmem5]; exact hmem4e
  have hpc5 : σ5.regs.get? Register.PC = some (0x80003580#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x8000357c#64) 4 = (0x80003580#64 : BitVec 64) from by decide] at this
  have hx14_5 : σ5.regs.get? Register.x14 = some PV :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx12_5 : σ5.regs.get? Register.x12 = some K13 := obs_alu_other' hobs5 Register.x12 (by decide) hx12_4
  have hs1_5 : σ5.regs.get? Register.x9 = some sret := obs_alu_other' hobs5 Register.x9 (by decide) hs1_4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs5 Register.x2 (by decide) hsp_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hout5 : σ5.sailOutput = out0 := by rw [hobs5.out, sailOutput_sigmaPost_alu]; exact hout4
  have hcode5 : Eval_exprLoaded σ5.mem := by rw [hmem5e]; exact hcode
  -- 0x80003580: ld a5,136(sp) → x15 := QV
  obtain ⟨σ6, i6, hs6', hi6, hG6, hmem6, hobs6⟩ :=
    site_80003580_totb σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80003580#64) vmi5 (sp - 1088#64)
      qb0 qb1 qb2 qb3 qb4 qb5 qb6 qb7 hG5 hpc5 hmi5 hsp_5 hcode5 rfl
      (by rw [haddr136]; omega) (by rw [haddr136]; omega)
      (by rw [haddr136, htoh]; right; omega) (by rw [haddr136]; omega)
      (by rw [haddr136, hmem5e]; try (first | exact hqb0 | exact lpin_of_present hqb0)) (by rw [haddr136, hmem5e]; try (first | exact hqb1 | exact lpin_of_present hqb1))
      (by rw [haddr136, hmem5e]; try (first | exact hqb2 | exact lpin_of_present hqb2)) (by rw [haddr136, hmem5e]; try (first | exact hqb3 | exact lpin_of_present hqb3))
      (by rw [haddr136, hmem5e]; try (first | exact hqb4 | exact lpin_of_present hqb4)) (by rw [haddr136, hmem5e]; try (first | exact hqb5 | exact lpin_of_present hqb5))
      (by rw [haddr136, hmem5e]; try (first | exact hqb6 | exact lpin_of_present hqb6)) (by rw [haddr136, hmem5e]; try (first | exact hqb7 | exact lpin_of_present hqb7)) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6'
  have hmem6e : σ6.mem = c.σ.mem := by rw [hmem6]; exact hmem5e
  have hpc6 : σ6.regs.get? Register.PC = some (0x80003584#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80003580#64) 4 = (0x80003584#64 : BitVec 64) from by decide] at this
  have hx15_6 : σ6.regs.get? Register.x15 = some QV :=
    obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx12_6 : σ6.regs.get? Register.x12 = some K13 := obs_alu_other' hobs6 Register.x12 (by decide) hx12_5
  have hx14_6 : σ6.regs.get? Register.x14 = some PV := obs_alu_other' hobs6 Register.x14 (by decide) hx14_5
  have hs1_6 : σ6.regs.get? Register.x9 = some sret := obs_alu_other' hobs6 Register.x9 (by decide) hs1_5
  have hsp_6 : σ6.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs6 Register.x2 (by decide) hsp_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hout6 : σ6.sailOutput = out0 := by rw [hobs6.out, sailOutput_sigmaPost_alu]; exact hout5
  have hcode6 : Eval_exprLoaded σ6.mem := by rw [hmem6e]; exact hcode
  -- 0x80003584: addi a0,sp,64 → x10 := (sp-1088)+64 = sp-1024 (buf)
  obtain ⟨σ7, i7, hs7', hi7, hG7, hmem7, hobs7⟩ :=
    site_80003584_lg σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80003584#64) vmi6 (sp - 1088#64)
      hG6 hpc6 hmi6 hsp_6 hcode6 rfl hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs7'
  have hmem7e : σ7.mem = c.σ.mem := by rw [hmem7]; exact hmem6e
  have hpc7 : σ7.regs.get? Register.PC = some (0x80003588#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80003584#64) 4 = (0x80003588#64 : BitVec 64) from by decide] at this
  have hx10_7 : σ7.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) :=
    obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx12_7 : σ7.regs.get? Register.x12 = some K13 := obs_alu_other' hobs7 Register.x12 (by decide) hx12_6
  have hx14_7 : σ7.regs.get? Register.x14 = some PV := obs_alu_other' hobs7 Register.x14 (by decide) hx14_6
  have hx15_7 : σ7.regs.get? Register.x15 = some QV := obs_alu_other' hobs7 Register.x15 (by decide) hx15_6
  have hs1_7 : σ7.regs.get? Register.x9 = some sret := obs_alu_other' hobs7 Register.x9 (by decide) hs1_6
  have hsp_7 : σ7.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs7 Register.x2 (by decide) hsp_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hout7 : σ7.sailOutput = out0 := by rw [hobs7.out, sailOutput_sigmaPost_alu]; exact hout6
  have hcode7 : Eval_exprLoaded σ7.mem := by rw [hmem7e]; exact hcode
  ------------------------------------------------------------------------
  -- 0x80003588 / 358c / 3590: the three copy stores. Memory towers m1/m2/m3.
  ------------------------------------------------------------------------
  let m1 : Mem := writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val K13)
  let m2 : Mem := writeMap8 m1 (sp.toNat - 1016) (sdData_val PV)
  let m3 : Mem := writeMap8 m2 (sp.toNat - 1008) (sdData_val QV)
  -- 0x80003588: sd a2,64(sp) → m1 (stores x12 = K13)
  obtain ⟨σ8, i8, hs8', hi8, hG8, hmem8, hobs8⟩ :=
    site_80003588_lg σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003588#64) vmi7 (sp - 1088#64) K13
      hG7 hpc7 hmi7 hsp_7 hx12_7 hcode7 rfl
      (by rw [haddr64]; omega) (by rw [haddr64]; omega) (by rw [haddr64, htoh]; omega) (by rw [haddr64]; omega) hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs8'
  have hmem8e : σ8.mem = m1 := by
    rw [hmem8, mem_afterNextPC, haddr64, hmem7e]
  have hpc8 : σ8.regs.get? Register.PC = some (0x8000358c#64) := by
    have := obs_store_pc_val hobs8
    rwa [show BitVec.addInt (0x80003588#64) 4 = (0x8000358c#64 : BitVec 64) from by decide] at this
  have hx10_8 := obs_store_other_val' hobs8 Register.x10 (by decide) hx10_7
  have hx14_8 := obs_store_other_val' hobs8 Register.x14 (by decide) hx14_7
  have hx15_8 := obs_store_other_val' hobs8 Register.x15 (by decide) hx15_7
  have hs1_8 := obs_store_other_val' hobs8 Register.x9 (by decide) hs1_7
  have hsp_8 := obs_store_other_val' hobs8 Register.x2 (by decide) hsp_7
  obtain ⟨vmi8, hmi8⟩ := obs_store_minstret_val hobs8
  have hout8 : σ8.sailOutput = out0 := by rw [hobs8.out, sailOutput_sigmaPost_store]; exact hout7
  have hcode8 : Eval_exprLoaded σ8.mem := by
    rw [hmem8e]
    exact loaded_eval_expr_agreeP c.σ.mem m1
      (fun k hk => (getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) k (sdData_val K13)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcode
  -- 0x8000358c: sd a4,72(sp) → m2 (stores x14 = PV)
  obtain ⟨σ9, i9, hs9', hi9, hG9, hmem9, hobs9⟩ :=
    site_8000358c_lg σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000358c#64) vmi8 (sp - 1088#64) PV
      hG8 hpc8 hmi8 hsp_8 hx14_8 hcode8 rfl
      (by rw [haddr72]; omega) (by rw [haddr72]; omega) (by rw [haddr72, htoh]; omega) (by rw [haddr72]; omega) hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs9'
  have hmem9e : σ9.mem = m2 := by
    rw [hmem9, mem_afterNextPC, haddr72, hmem8e]
  have hpc9 : σ9.regs.get? Register.PC = some (0x80003590#64) := by
    have := obs_store_pc_val hobs9
    rwa [show BitVec.addInt (0x8000358c#64) 4 = (0x80003590#64 : BitVec 64) from by decide] at this
  have hx10_9 := obs_store_other_val' hobs9 Register.x10 (by decide) hx10_8
  have hx15_9 := obs_store_other_val' hobs9 Register.x15 (by decide) hx15_8
  have hs1_9 := obs_store_other_val' hobs9 Register.x9 (by decide) hs1_8
  have hsp_9 := obs_store_other_val' hobs9 Register.x2 (by decide) hsp_8
  obtain ⟨vmi9, hmi9⟩ := obs_store_minstret_val hobs9
  have hout9 : σ9.sailOutput = out0 := by rw [hobs9.out, sailOutput_sigmaPost_store]; exact hout8
  have hcode9 : Eval_exprLoaded σ9.mem := by
    rw [hmem9e]
    exact loaded_eval_expr_agreeP m1 m2
      (fun k hk => (getElem_writeMap8_disjoint m1 (sp.toNat-1016) k (sdData_val PV)
        (by rcases hcodeStk with h | h <;> omega)).symm) (hmem8e ▸ hcode8)
  -- 0x80003590: sd a5,80(sp) → m3 (stores x15 = QV)
  obtain ⟨σ10, i10, hs10', hi10, hG10, hmem10, hobs10⟩ :=
    site_80003590_lg σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003590#64) vmi9 (sp - 1088#64) QV
      hG9 hpc9 hmi9 hsp_9 hx15_9 hcode9 rfl
      (by rw [haddr80]; omega) (by rw [haddr80]; omega) (by rw [haddr80, htoh]; omega) (by rw [haddr80]; omega) hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs10'
  have hmem10e : σ10.mem = m3 := by
    rw [hmem10, mem_afterNextPC, haddr80, hmem9e]
  have hpc10 : σ10.regs.get? Register.PC = some (0x80003594#64) := by
    have := obs_store_pc_val hobs10
    rwa [show BitVec.addInt (0x80003590#64) 4 = (0x80003594#64 : BitVec 64) from by decide] at this
  have hx10_10 := obs_store_other_val' hobs10 Register.x10 (by decide) hx10_9
  have hs1_10 := obs_store_other_val' hobs10 Register.x9 (by decide) hs1_9
  have hsp_10 := obs_store_other_val' hobs10 Register.x2 (by decide) hsp_9
  obtain ⟨vmi10, hmi10⟩ := obs_store_minstret_val hobs10
  have hout10 : σ10.sailOutput = out0 := by rw [hobs10.out, sailOutput_sigmaPost_store]; exact hout9
  have hcode_m3 : Eval_exprLoaded m3 :=
    loaded_eval_expr_agreeP m2 m3
      (fun k hk => (getElem_writeMap8_disjoint m2 (sp.toNat-1008) k (sdData_val QV)
        (by rcases hcodeStk with h | h <;> omega)).symm) (hmem9e ▸ hcode9)
  have hcode10 : Eval_exprLoaded σ10.mem := by rw [hmem10e]; exact hcode_m3
  have hx10_10' : σ10.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) := hx10_10
  ------------------------------------------------------------------------
  -- the copied 24-byte buffer represents `vl`: ValueRepr m3 (sp-1024) vl.
  ------------------------------------------------------------------------
  have hm3_out : ∀ a, (a < sp.toNat - 1024 ∨ sp.toNat - 1024 + 24 ≤ a) → m3[a]? = c.σ.mem[a]? := by
    intro a ha
    show (writeMap8 m2 (sp.toNat-1008) (sdData_val QV))[a]? = c.σ.mem[a]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) a (sdData_val QV) (by omega)]
    show (writeMap8 m1 (sp.toNat-1016) (sdData_val PV))[a]? = c.σ.mem[a]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) a (sdData_val PV) (by omega)]
    show (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val K13))[a]? = c.σ.mem[a]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) a (sdData_val K13) (by omega)]
  obtain ⟨eK0, eK1, eK2, eK3, eK4, eK5, eK6, eK7⟩ := sdData_sext_bytes kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7
  obtain ⟨eP0, eP1, eP2, eP3, eP4, eP5, eP6, eP7⟩ := sdData_sext_bytes pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
  obtain ⟨eQ0, eQ1, eQ2, eQ3, eQ4, eQ5, eQ6, eQ7⟩ := sdData_sext_bytes qb0 qb1 qb2 qb3 qb4 qb5 qb6 qb7
  have hK : ∀ o : Nat, o < 8 →
      m3[sp.toNat - 1024 + o]? = (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val K13))[sp.toNat - 1024 + o]? := by
    intro o ho
    show (writeMap8 m2 (sp.toNat-1008) (sdData_val QV))[_]? = _
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) _ (sdData_val QV) (by omega)]
    show (writeMap8 m1 (sp.toNat-1016) (sdData_val PV))[_]? = _
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) _ (sdData_val PV) (by omega)]
  have hP : ∀ o : Nat, o < 8 →
      m3[sp.toNat - 1016 + o]? = (writeMap8 m1 (sp.toNat-1016) (sdData_val PV))[sp.toNat - 1016 + o]? := by
    intro o ho
    show (writeMap8 m2 (sp.toNat-1008) (sdData_val QV))[_]? = _
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) _ (sdData_val QV) (by omega)]
  have hm3_copy : ∀ j, j < 24 → m3[(sp.toNat - 1024) + j]? = some ((c.σ.mem[(sp.toNat - 968) + j]?).getD 0) := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
        j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨
        j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 from by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hK 0 (by omega), show sp.toNat-1024+0 = sp.toNat-1024 from by omega,
        getElem_writeMap8_0, eK0, show sp.toNat-968+0 = sp.toNat-968 from by omega]; exact congrArg some hkb0.symm
    · rw [hK 1 (by omega), getElem_writeMap8_1, eK1]; exact congrArg some hkb1.symm
    · rw [hK 2 (by omega), getElem_writeMap8_2, eK2]; exact congrArg some hkb2.symm
    · rw [hK 3 (by omega), getElem_writeMap8_3, eK3]; exact congrArg some hkb3.symm
    · rw [hK 4 (by omega), getElem_writeMap8_4, eK4]; exact congrArg some hkb4.symm
    · rw [hK 5 (by omega), getElem_writeMap8_5, eK5]; exact congrArg some hkb5.symm
    · rw [hK 6 (by omega), getElem_writeMap8_6, eK6]; exact congrArg some hkb6.symm
    · rw [hK 7 (by omega), getElem_writeMap8_7, eK7]; exact congrArg some hkb7.symm
    · rw [show sp.toNat-1024+8 = sp.toNat-1016+0 from by omega, hP 0 (by omega),
        show sp.toNat-1016+0 = sp.toNat-1016 from by omega, getElem_writeMap8_0, eP0,
        show sp.toNat-968+8 = sp.toNat-960 from by omega]; exact congrArg some hpb0.symm
    · rw [show sp.toNat-1024+9 = sp.toNat-1016+1 from by omega, hP 1 (by omega), getElem_writeMap8_1, eP1,
        show sp.toNat-968+9 = sp.toNat-960+1 from by omega]; exact congrArg some hpb1.symm
    · rw [show sp.toNat-1024+10 = sp.toNat-1016+2 from by omega, hP 2 (by omega), getElem_writeMap8_2, eP2,
        show sp.toNat-968+10 = sp.toNat-960+2 from by omega]; exact congrArg some hpb2.symm
    · rw [show sp.toNat-1024+11 = sp.toNat-1016+3 from by omega, hP 3 (by omega), getElem_writeMap8_3, eP3,
        show sp.toNat-968+11 = sp.toNat-960+3 from by omega]; exact congrArg some hpb3.symm
    · rw [show sp.toNat-1024+12 = sp.toNat-1016+4 from by omega, hP 4 (by omega), getElem_writeMap8_4, eP4,
        show sp.toNat-968+12 = sp.toNat-960+4 from by omega]; exact congrArg some hpb4.symm
    · rw [show sp.toNat-1024+13 = sp.toNat-1016+5 from by omega, hP 5 (by omega), getElem_writeMap8_5, eP5,
        show sp.toNat-968+13 = sp.toNat-960+5 from by omega]; exact congrArg some hpb5.symm
    · rw [show sp.toNat-1024+14 = sp.toNat-1016+6 from by omega, hP 6 (by omega), getElem_writeMap8_6, eP6,
        show sp.toNat-968+14 = sp.toNat-960+6 from by omega]; exact congrArg some hpb6.symm
    · rw [show sp.toNat-1024+15 = sp.toNat-1016+7 from by omega, hP 7 (by omega), getElem_writeMap8_7, eP7,
        show sp.toNat-968+15 = sp.toNat-960+7 from by omega]; exact congrArg some hpb7.symm
    · rw [show sp.toNat-1024+16 = sp.toNat-1008 from by omega, getElem_writeMap8_0, eQ0,
        show sp.toNat-968+16 = sp.toNat-952 from by omega]; exact congrArg some hqb0.symm
    · rw [show sp.toNat-1024+17 = sp.toNat-1008+1 from by omega, getElem_writeMap8_1, eQ1,
        show sp.toNat-968+17 = sp.toNat-952+1 from by omega]; exact congrArg some hqb1.symm
    · rw [show sp.toNat-1024+18 = sp.toNat-1008+2 from by omega, getElem_writeMap8_2, eQ2,
        show sp.toNat-968+18 = sp.toNat-952+2 from by omega]; exact congrArg some hqb2.symm
    · rw [show sp.toNat-1024+19 = sp.toNat-1008+3 from by omega, getElem_writeMap8_3, eQ3,
        show sp.toNat-968+19 = sp.toNat-952+3 from by omega]; exact congrArg some hqb3.symm
    · rw [show sp.toNat-1024+20 = sp.toNat-1008+4 from by omega, getElem_writeMap8_4, eQ4,
        show sp.toNat-968+20 = sp.toNat-952+4 from by omega]; exact congrArg some hqb4.symm
    · rw [show sp.toNat-1024+21 = sp.toNat-1008+5 from by omega, getElem_writeMap8_5, eQ5,
        show sp.toNat-968+21 = sp.toNat-952+5 from by omega]; exact congrArg some hqb5.symm
    · rw [show sp.toNat-1024+22 = sp.toNat-1008+6 from by omega, getElem_writeMap8_6, eQ6,
        show sp.toNat-968+22 = sp.toNat-952+6 from by omega]; exact congrArg some hqb6.symm
    · rw [show sp.toNat-1024+23 = sp.toNat-1008+7 from by omega, getElem_writeMap8_7, eQ7,
        show sp.toNat-968+23 = sp.toNat-952+7 from by omega]; exact congrArg some hqb7.symm
  have hbufRepr : ValueRepr m3 N φcv (sp.toNat - 1024) vl :=
    valueRepr_copy_total_of_writeWindow (srcAddr := sp.toNat - 968) (dstAddr := sp.toNat - 1024)
      hm3_copy hm3_out
      (fun p s hp k hk => hBE.pay_disj p s hvalSub' hp k hk) hvalSub'
  ------------------------------------------------------------------------
  -- 0x80003594: jal value_truthy → PC := value_truthy entry, ra := 0x80003598
  ------------------------------------------------------------------------
  obtain ⟨σ11, i11, hs11', hi11, hG11, hmem11, hobs11⟩ :=
    site_80003594_lg σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003594#64) vmi10
      hG10 hpc10 hmi10 hcode10 rfl hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs11'
  have hmem11e : σ11.mem = m3 := by rw [hmem11]; exact hmem10e
  have hpc11 : σ11.regs.get? Register.PC = some (0x8000282c#64) := by
    have := obs_jal_pc hobs11
    rwa [show ((0x80003594#64 : BitVec 64) + sign_extend (m := 64) (0x1ff298#21)) = 0x8000282c#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink11 : σ11.regs.get? Register.x1 = some (0x80003598#64) := by
    have := obs_jal_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80003594#64 : BitVec 64) 4 = (0x80003598#64:BitVec 64) from by decide] at this
  have hx10_11 : σ11.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) :=
    obs_jal_other' hobs11 Register.x10 (by decide) hx10_10'
  have hs1_11 : σ11.regs.get? Register.x9 = some sret := obs_jal_other' hobs11 Register.x9 (by decide) hs1_10
  have hsp_11 : σ11.regs.get? Register.x2 = some (sp - 1088#64) := obs_jal_other' hobs11 Register.x2 (by decide) hsp_10
  obtain ⟨vmi11, hmi11⟩ := obs_jal_minstret hobs11
  have hout11 : σ11.sailOutput = out0 := by rw [hobs11.out, sailOutput_sigmaPost_jal]; exact hout10
  -- Value_truthyLoaded / Value_boolLoaded at c.σ.mem
  have hVtruthy_c : Value_truthyLoaded c.σ.mem := by
    refine loaded_truthy_agreeP mcall c.σ.mem (fun a ha => ?_) hVtruthyMcall
    rcases hmemFrame a (by rw [hspsub] at *; rcases hTruthyStk with h | h <;> omega)
      (by rcases hTruthyArena with h | h <;> omega) with hin | heq
    · exact absurd hin (by rcases hTruthyStk with h | h <;> omega)
    · exact heq.symm
  have hVbool_c : Value_boolLoaded c.σ.mem := by
    refine loaded_bool_agreeP mcall c.σ.mem (fun a ha => ?_) hVboolMcall
    rcases hmemFrame a (by rw [hspsub] at *; rcases hBoolStk with h | h <;> omega)
      (by rcases hBoolArena with h | h <;> omega) with hin | heq
    · exact absurd hin (by rcases hBoolStk with h | h <;> omega)
    · exact heq.symm
  have hVtruthy_m3 : Value_truthyLoaded m3 :=
    loaded_truthy_writeMap8 m2 (sp.toNat - 1008) (sdData_val QV) (by rcases hTruthyStk with h | h <;> omega)
      (loaded_truthy_writeMap8 m1 (sp.toNat - 1016) (sdData_val PV) (by rcases hTruthyStk with h | h <;> omega)
        (loaded_truthy_writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val K13) (by rcases hTruthyStk with h | h <;> omega) hVtruthy_c))
  have hVbool_m3 : Value_boolLoaded m3 :=
    loaded_bool_writeMap8 m2 (sp.toNat - 1008) (sdData_val QV) (by rcases hBoolStk with h | h <;> omega)
      (loaded_bool_writeMap8 m1 (sp.toNat - 1016) (sdData_val PV) (by rcases hBoolStk with h | h <;> omega)
        (loaded_bool_writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val K13) (by rcases hBoolStk with h | h <;> omega) hVbool_c))
  have hcode_m3' : Eval_exprLoaded m3 := hcode_m3
  -- the buffer region facts
  have hbuftag : ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) = (sp - 1024#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub]
    have h1024 : (1024#64 : BitVec 64).toNat = 1024 := by decide
    have : ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)).toNat = sp.toNat - 1024 := haddr64
    rw [this, h1024]; have := sp.isLt; omega
  have hbufNat : (sp - 1024#64 : BitVec 64).toNat = sp.toNat - 1024 := by
    rw [BitVec.toNat_sub]; have h1024 : (1024#64 : BitVec 64).toNat = 1024 := by decide
    rw [h1024]; have := sp.isLt; omega
  have hTruthyReg : TruthyRegion (sp - 1024#64) :=
    ⟨by rw [hbufNat]; omega, by rw [hbufNat]; have := hBE.buf_lo; omega,
     by rw [hbufNat]; omega, by rw [hbufNat, htoh]; have := hBE.buf_win; rw [htoh] at this; omega⟩
  have hrettgt_t : (BitVec.update ((0x80003598#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by decide
  have hbufRepr' : ValueRepr m3 N φcv (sp - 1024#64).toNat vl := by rw [hbufNat]; exact hbufRepr
  have hx10_11' : σ11.regs.get? Register.x10 = some (sp - 1024#64) := by rw [hx10_11, hbuftag]
  ------------------------------------------------------------------------
  -- value_truthy(vl) via value_truthy_spec, buf = sp-1024, ra = 0x80003598
  ------------------------------------------------------------------------
  obtain ⟨cT, hsT, hGT, hpcT, ha0T, hraT, ⟨vmiT, hmiT⟩, htickT, hmemT, houtT, hframeT⟩ :=
    value_truthy_spec (fun R => σ11.regs.get? R) (sp - 1024#64) (0x80003598#64) N φcv vl m3 out0
      ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨hG11, hmem11e ▸ hVtruthy_m3, hmem11e, hpc11, hx10_11', hlink11, ⟨vmi11, hmi11⟩, hi11,
        hbufRepr', hTruthyReg, hrettgt_t, hout11, fun R _ => rfl⟩
  have hmemT' : cT.σ.mem = m3 := hmemT
  have hpcT' : cT.σ.regs.get? Register.PC = some (0x80003598#64) := by
    rw [hpcT, show (BitVec.update ((0x80003598#64:BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = 0x80003598#64 from by apply BitVec.eq_of_toNat_eq; decide]
  -- value_truthy returns a0 = cond vl.truthy 1 0 = 0 (vl.truthy = false)
  have ha0T0 : cT.σ.regs.get? Register.x10 = some (0#64) := by
    rw [ha0T, hvlfalse]; rfl
  have hs1_T : cT.σ.regs.get? Register.x9 = some sret := by
    rw [hframeT Register.x9 (by decide)]; exact hs1_11
  have hsp_T : cT.σ.regs.get? Register.x2 = some (sp - 1088#64) := by
    rw [hframeT Register.x2 (by decide)]; exact hsp_11
  have hVbool_T : Value_boolLoaded cT.σ.mem := by rw [hmemT']; exact hVbool_m3
  have hcode_T : Eval_exprLoaded cT.σ.mem := by rw [hmemT']; exact hcode_m3
  ------------------------------------------------------------------------
  -- 0x80003598: ld a3,0(sp) → reload env (dead value; only need PC/regs)
  ------------------------------------------------------------------------
  -- the env-spill slot at sp-1088 is present (mcall fully populated ⇒ σ present)
  have hspill0Nat : ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 :=
    spill_addr sp (0x000#12) 1088 (by decide) (by omega) hsp1088
  -- present bytes at [sp-1088, sp-1080) in cT.σ.mem = m3 (from c.σ.mem present + writes disjoint)
  -- WAVE 48k: TOTAL reads.  The model's `readByte` is `getD 0`, so these dead
  -- sub-`Value`/node bytes need no map presence at all — each is simply NAMED
  -- as its own total read.  (This replaces the refuted `frame_pop` oracle;
  -- the window hypothesis is kept so every call site is unchanged.)
  have hStackPopM3 : ∀ a : Nat,
      (sp.toNat - 1120 ≤ a ∧ a < sp.toNat) ∨
        (aExpr.toNat + 4 ≤ a ∧ a < aExpr.toNat + 8) →
      ∃ b : BitVec 8, (m3[a]?).getD 0 = b :=
    fun _ _ => ⟨_, rfl⟩
  obtain ⟨eb0, heb0⟩ := hStackPopM3 (sp.toNat - 1088) (by omega)
  obtain ⟨eb1, heb1⟩ := hStackPopM3 (sp.toNat - 1088 + 1) (by omega)
  obtain ⟨eb2, heb2⟩ := hStackPopM3 (sp.toNat - 1088 + 2) (by omega)
  obtain ⟨eb3, heb3⟩ := hStackPopM3 (sp.toNat - 1088 + 3) (by omega)
  obtain ⟨eb4, heb4⟩ := hStackPopM3 (sp.toNat - 1088 + 4) (by omega)
  obtain ⟨eb5, heb5⟩ := hStackPopM3 (sp.toNat - 1088 + 5) (by omega)
  obtain ⟨eb6, heb6⟩ := hStackPopM3 (sp.toNat - 1088 + 6) (by omega)
  obtain ⟨eb7, heb7⟩ := hStackPopM3 (sp.toNat - 1088 + 7) (by omega)
  obtain ⟨σ12, i12, hs12', hi12, hG12, hmem12, hobs12⟩ :=
    site_80003598_totb cT.σ cT.tick cT.steps (0x80003598#64) vmiT (sp - 1088#64)
      eb0 eb1 eb2 eb3 eb4 eb5 eb6 eb7 hGT hpcT' hmiT hsp_T (hmemT' ▸ hcode_m3) rfl
      (by rw [hspill0Nat]; omega) (by rw [hspill0Nat]; omega)
      (by rw [hspill0Nat, htoh]; right; omega) (by rw [hspill0Nat]; omega)
      (by rw [hspill0Nat, hmemT']; exact heb0) (by rw [hspill0Nat, hmemT']; exact heb1)
      (by rw [hspill0Nat, hmemT']; exact heb2) (by rw [hspill0Nat, hmemT']; exact heb3)
      (by rw [hspill0Nat, hmemT']; exact heb4) (by rw [hspill0Nat, hmemT']; exact heb5)
      (by rw [hspill0Nat, hmemT']; exact heb6) (by rw [hspill0Nat, hmemT']; exact heb7) htickT
  have hstep12 : Step cT ⟨σ12, i12, cT.steps + 1⟩ := by cases cT; exact hs12'
  have hmem12e : σ12.mem = m3 := by rw [hmem12]; exact hmemT'
  have hpc12 : σ12.regs.get? Register.PC = some (0x8000359c#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x80003598#64) 4 = (0x8000359c#64 : BitVec 64) from by decide] at this
  have ha0_12 : σ12.regs.get? Register.x10 = some (0#64) := obs_alu_other' hobs12 Register.x10 (by decide) ha0T0
  have hs1_12 : σ12.regs.get? Register.x9 = some sret := obs_alu_other' hobs12 Register.x9 (by decide) hs1_T
  have hsp_12 : σ12.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs12 Register.x2 (by decide) hsp_T
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hout12 : σ12.sailOutput = out0 := by rw [hobs12.out, sailOutput_sigmaPost_alu]; exact houtT
  have hVbool_12 : Value_boolLoaded σ12.mem := by rw [hmem12e]; exact hVbool_m3
  have hcode_12 : Eval_exprLoaded σ12.mem := by rw [hmem12e]; exact hcode_m3
  ------------------------------------------------------------------------
  -- 0x8000359c: beqz a0 → 0x800036d4 (TAKEN, a0 = 0)
  ------------------------------------------------------------------------
  obtain ⟨σ13, i13, hs13', hi13, hG13, hmem13, hobs13⟩ :=
    site_8000359c_taken_lg σ12 i12 (cT.steps + 1) (0x8000359c#64) vmi12 (0#64)
      hG12 hpc12 hmi12 ha0_12 hcode_12 rfl (by decide) hi12
  have hstep13 : Step ⟨σ12, i12, cT.steps + 1⟩ ⟨σ13, i13, cT.steps + 1 + 1⟩ := hs13'
  have hmem13e : σ13.mem = m3 := by rw [hmem13]; exact hmem12e
  have hpc13 : σ13.regs.get? Register.PC = some (0x800036d4#64) := by
    have := obs_branch_taken_pc hobs13
    rwa [site_8000359c_taken_lg_tgt] at this
  have hs1_13 : σ13.regs.get? Register.x9 = some sret := obs_branch_taken_other' hobs13 Register.x9 (by decide) hs1_12
  have hsp_13 : σ13.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_taken_other' hobs13 Register.x2 (by decide) hsp_12
  obtain ⟨vmi13, hmi13⟩ := obs_branch_taken_minstret hobs13
  have hout13 : σ13.sailOutput = out0 := by rw [hobs13.out, sailOutput_sigmaPost_branch_taken]; exact hout12
  have hVbool_13 : Value_boolLoaded σ13.mem := by rw [hmem13e]; exact hVbool_m3
  have hcode_13 : Eval_exprLoaded σ13.mem := by rw [hmem13e]; exact hcode_m3
  ------------------------------------------------------------------------
  -- 0x800036d4: li a1,0 → x11 := 0
  ------------------------------------------------------------------------
  obtain ⟨σ14, i14, hs14', hi14, hG14, hmem14, hobs14⟩ :=
    site_800036d4_lg σ13 i13 (cT.steps + 1 + 1) (0x800036d4#64) vmi13 hG13 hpc13 hmi13 hcode_13 rfl hi13
  have hstep14 : Step ⟨σ13, i13, cT.steps + 1 + 1⟩ ⟨σ14, i14, cT.steps + 1 + 1 + 1⟩ := hs14'
  have hmem14e : σ14.mem = m3 := by rw [hmem14]; exact hmem13e
  have hpc14 : σ14.regs.get? Register.PC = some (0x800036d8#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x800036d4#64) 4 = (0x800036d8#64 : BitVec 64) from by decide] at this
  have hx11_14 : σ14.regs.get? Register.x11 = some (0#64) := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) = 0#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hs1_14 : σ14.regs.get? Register.x9 = some sret := obs_alu_other' hobs14 Register.x9 (by decide) hs1_13
  have hsp_14 : σ14.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs14 Register.x2 (by decide) hsp_13
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hout14 : σ14.sailOutput = out0 := by rw [hobs14.out, sailOutput_sigmaPost_alu]; exact hout13
  have hVbool_14 : Value_boolLoaded σ14.mem := by rw [hmem14e]; exact hVbool_m3
  have hcode_14 : Eval_exprLoaded σ14.mem := by rw [hmem14e]; exact hcode_m3
  ------------------------------------------------------------------------
  -- 0x800036d8: mv a0,s1 → x10 := sret
  ------------------------------------------------------------------------
  obtain ⟨σ15, i15, hs15', hi15, hG15, hmem15, hobs15⟩ :=
    site_800036d8_lg σ14 i14 (cT.steps + 1 + 1 + 1) (0x800036d8#64) vmi14 sret hG14 hpc14 hmi14 hs1_14 hcode_14 rfl hi14
  have hstep15 : Step ⟨σ14, i14, cT.steps + 1 + 1 + 1⟩ ⟨σ15, i15, cT.steps + 1 + 1 + 1 + 1⟩ := hs15'
  have hmem15e : σ15.mem = m3 := by rw [hmem15]; exact hmem14e
  have hpc15 : σ15.regs.get? Register.PC = some (0x800036dc#64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x800036d8#64) 4 = (0x800036dc#64 : BitVec 64) from by decide] at this
  have hx10_15 : σ15.regs.get? Register.x10 = some sret := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sret + sign_extend (m := 64) (0x000#12) : BitVec 64) = sret from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
        apply BitVec.eq_of_toNat_eq; decide]; rw [BitVec.add_zero]] at this
  have hx11_15 : σ15.regs.get? Register.x11 = some (0#64) := obs_alu_other' hobs15 Register.x11 (by decide) hx11_14
  have hs1_15 : σ15.regs.get? Register.x9 = some sret := obs_alu_other' hobs15 Register.x9 (by decide) hs1_14
  have hsp_15 : σ15.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs15 Register.x2 (by decide) hsp_14
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hout15 : σ15.sailOutput = out0 := by rw [hobs15.out, sailOutput_sigmaPost_alu]; exact hout14
  have hVbool_15 : Value_boolLoaded σ15.mem := by rw [hmem15e]; exact hVbool_m3
  have hBoolReg : BoolRegion sret := ⟨hsretAl, hsretLo, hsretHi, hsretWin, hSretBoolCode⟩
  have hrettgt_b : (BitVec.update ((0x800036e0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by decide
  ------------------------------------------------------------------------
  -- 0x800036dc: jal value_bool → PC := value_bool entry, ra := 0x800036e0
  ------------------------------------------------------------------------
  have hcode_15 : Eval_exprLoaded σ15.mem := by rw [hmem15e]; exact hcode_m3
  obtain ⟨σ16, i16, hs16', hi16, hG16, hmem16, hobs16⟩ :=
    site_800036dc_lg σ15 i15 (cT.steps + 1 + 1 + 1 + 1) (0x800036dc#64) vmi15 hG15 hpc15 hmi15 hcode_15 rfl hi15
  have hstep16 : Step ⟨σ15, i15, cT.steps + 1 + 1 + 1 + 1⟩ ⟨σ16, i16, cT.steps + 1 + 1 + 1 + 1 + 1⟩ := hs16'
  have hmem16e : σ16.mem = m3 := by rw [hmem16]; exact hmem15e
  have hpc16 : σ16.regs.get? Register.PC = some (0x800027f8#64) := by
    have := obs_jal_pc hobs16
    rwa [show ((0x800036dc#64 : BitVec 64) + sign_extend (m := 64) (0x1ff11c#21)) = 0x800027f8#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink16 : σ16.regs.get? Register.x1 = some (0x800036e0#64) := by
    have := obs_jal_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x800036dc#64 : BitVec 64) 4 = (0x800036e0#64:BitVec 64) from by decide] at this
  have hx10_16 : σ16.regs.get? Register.x10 = some sret := obs_jal_other' hobs16 Register.x10 (by decide) hx10_15
  have hx11_16 : σ16.regs.get? Register.x11 = some (0#64) := obs_jal_other' hobs16 Register.x11 (by decide) hx11_15
  have hs1_16 : σ16.regs.get? Register.x9 = some sret := obs_jal_other' hobs16 Register.x9 (by decide) hs1_15
  have hsp_16 : σ16.regs.get? Register.x2 = some (sp - 1088#64) := obs_jal_other' hobs16 Register.x2 (by decide) hsp_15
  obtain ⟨vmi16, hmi16⟩ := obs_jal_minstret hobs16
  have hout16 : σ16.sailOutput = out0 := by rw [hobs16.out, sailOutput_sigmaPost_jal]; exact hout15
  have hVbool_16 : Value_boolLoaded σ16.mem := by rw [hmem16e]; exact hVbool_m3
  ------------------------------------------------------------------------
  -- value_bool(sret, 0) via value_bool_spec_full → .bool (0 != 0) = .bool false
  ------------------------------------------------------------------------
  obtain ⟨cB, hsB, hGB, hpcB, ha0B, hraB, ⟨vmiB, hmiB⟩, htickB, hvalB, houtB, hmemframeB, hMemExtB, hframeB⟩ :=
    value_bool_spec_full (fun R => σ16.regs.get? R) sret (0#64) (0x800036e0#64) N φc' m3 out0
      ⟨σ16, i16, cT.steps + 1 + 1 + 1 + 1 + 1⟩
      ⟨hG16, hVbool_16, hmem16e, hpc16, hx10_16, hx11_16, hlink16, ⟨vmi16, hmi16⟩, hi16,
        hBoolReg, hrettgt_b, hout16, fun R _ => rfl⟩
  have hvalfalse : ValueRepr cB.σ.mem N φc' sret.toNat (.bool false) := by
    rw [show ((.bool false) : Value) = .bool ((0#64 : BitVec 64) != 0#64) from by decide]; exact hvalB
  have hpcB' : cB.σ.regs.get? Register.PC = some (0x800036e0#64) := by
    rw [hpcB, show (BitVec.update ((0x800036e0#64:BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = 0x800036e0#64 from by apply BitVec.eq_of_toNat_eq; decide]
  have hs1_B : cB.σ.regs.get? Register.x9 = some sret := by
    rw [hframeB Register.x9 (by decide)]; exact hs1_16
  have hsp_B : cB.σ.regs.get? Register.x2 = some (sp - 1088#64) := by
    rw [hframeB Register.x2 (by decide)]; exact hsp_16
  have hcode_B : Eval_exprLoaded cB.σ.mem :=
    loaded_eval_expr_agreeP m3 cB.σ.mem
      (fun k hk => hmemframeB k (by rcases hsretEvalCode with h | h <;> omega)) hcode_m3
  ------------------------------------------------------------------------
  -- 0x800036e0: j 0x800033ec → shared epilogue entry
  ------------------------------------------------------------------------
  obtain ⟨σ18, i18, hs18', hi18, hG18, hmem18, hobs18⟩ :=
    site_800036e0_lg cB.σ cB.tick cB.steps (0x800036e0#64) vmiB hGB hpcB' hmiB hcode_B rfl
      (by rw [show ((0x800036e0#64:BitVec 64) + sign_extend (m := 64) (0x1ffd0c#21)) = 0x800033ec#64 from by
            apply BitVec.eq_of_toNat_eq; decide]; decide) htickB
  have hstep18 : Step cB ⟨σ18, i18, cB.steps + 1⟩ := by cases cB; exact hs18'
  have hmem18e : σ18.mem = cB.σ.mem := hmem18
  have hpc_fin : σ18.regs.get? Register.PC = some (0x800033ec#64) := by
    have := obs_jr_pc hobs18
    rwa [show ((0x800036e0#64:BitVec 64) + sign_extend (m := 64) (0x1ffd0c#21)) = 0x800033ec#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hs1_fin : σ18.regs.get? Register.x9 = some sret := obs_jr_other' hobs18 Register.x9 (by decide) hs1_B
  have hsp_fin : σ18.regs.get? Register.x2 = some (sp - 1088#64) := obs_jr_other' hobs18 Register.x2 (by decide) hsp_B
  obtain ⟨vmifin, hmifin⟩ := obs_jr_minstret hobs18
  have hout_fin : σ18.sailOutput = out0 := by
    rw [hobs18.out, sailOutput_sigmaPost_jump_x0]; exact houtB
  ------------------------------------------------------------------------
  -- spill slots survive: [sp-32,sp) disjoint from the 3 buffer stores (below
  -- sp-1008) and from value_bool's sret write.
  ------------------------------------------------------------------------
  have hslotAgree : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) c.σ.mem σ18.mem := by
    intro k hk
    rw [hmem18e, ← hmemframeB k (by rcases hsretStk with h | h <;> omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat-1008) (sdData_val QV))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) k (sdData_val QV) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat-1016) (sdData_val PV))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) k (sdData_val PV) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val K13))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) k (sdData_val K13) (by omega)]
  have hslotRa_f : read64 σ18.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotRa
  have hslotS0_f : read64 σ18.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS0
  have hslotS1_f : read64 σ18.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS1
  have hslotS2_f : read64 σ18.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS2
  -- StoreRepr survives: all writes (3 buffer stores + sret) land in [SL.lo, SL.hi).
  have hSL18 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = σ18.mem[k]? := by
    intro k hk
    rw [hmem18e, ← hmemframeB k (by rcases hsretInSL with ⟨hl, hr⟩; omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat-1008) (sdData_val QV))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) k (sdData_val QV) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat-1016) (sdData_val PV))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) k (sdData_val PV) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val K13))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) k (sdData_val K13) (by omega)]
  have hstore_fin : StoreRepr σ18.mem N A φf' φc' st'.store :=
    hstoreSurv' σ18.mem (fun k hk => hSL18 k hk)
  have hSurvSL_fin : ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → σ18.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store :=
    fun m' hm' => hstoreSurv' m' (fun k hk => (hSL18 k hk).trans (hm' k hk))
  -- MemExtends m0 σ18.mem
  have hMemExt_m0_c : MemExtends m0 c.σ.mem := hMemExtM0.trans hMemExt
  have hMemExt_c_16 : MemExtends c.σ.mem σ16.mem := by
    rw [hmem16e]
    exact ((MemExtends.refl c.σ.mem).trans
      (memExtends_writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val K13))).trans
      ((memExtends_writeMap8 m1 (sp.toNat - 1016) (sdData_val PV)).trans
        (memExtends_writeMap8 m2 (sp.toNat - 1008) (sdData_val QV)))
  have hMemExt_16_18 : MemExtends σ16.mem σ18.mem := by
    rw [hmem18e, hmem16e]; exact hMemExtB
  have hMemExt_fin : MemExtends m0 σ18.mem :=
    (hMemExt_m0_c.trans hMemExt_c_16).trans hMemExt_16_18
  -- callee-saved (noise) frame across the whole tail, then the prologue bridge.
  have hframeG : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      σ18.regs.get? R = g R := by
    intro R hR he8 he9 he18 he2
    obtain ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have abi_ne' : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false := by
      intro X hX
      rcases hXR : (X == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
    have hx11R : (Register.x11 == R) = false := abi_ne' (by decide)
    have hx12R : (Register.x12 == R) = false := abi_ne' (by decide)
    have hx13R : (Register.x13 == R) = false := abi_ne' (by decide)
    have hx14R : (Register.x14 == R) = false := abi_ne' (by decide)
    have hx15R : (Register.x15 == R) = false := abi_ne' (by decide)
    have hx10R : (Register.x10 == R) = false := abi_ne' (by decide)
    have hx1R : (Register.x1 == R) = false := abi_ne' (by decide)
    -- σ1..σ7: lw/li/ld/beq/ld/ld/addi (write x14/x15/x12/PC/x14/x15/x10)
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx14R hnpc' hmii')
    have f2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx15R hnpc' hmii')
    have f3 : σ3.regs.get? R = σ2.regs.get? R :=
      (hobs3.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx12R hnpc' hmii')
    have f4 : σ4.regs.get? R = σ3.regs.get? R :=
      (hobs4.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
    have f5 : σ5.regs.get? R = σ4.regs.get? R :=
      (hobs5.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx14R hnpc' hmii')
    have f6 : σ6.regs.get? R = σ5.regs.get? R :=
      (hobs6.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx15R hnpc' hmii')
    have f7 : σ7.regs.get? R = σ6.regs.get? R :=
      (hobs7.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx10R hnpc' hmii')
    -- σ8..σ10: sd/sd/sd (write memory, not R)
    have f8 : σ8.regs.get? R = σ7.regs.get? R := frame_store_v hobs8 R ⟨hx11R, hx15R, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have f9 : σ9.regs.get? R = σ8.regs.get? R := frame_store_v hobs9 R ⟨hx11R, hx15R, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have f10 : σ10.regs.get? R = σ9.regs.get? R := frame_store_v hobs10 R ⟨hx11R, hx15R, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    -- σ11: jal value_truthy (writes x1)
    have f11 : σ11.regs.get? R = σ10.regs.get? R :=
      (hobs11.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' hx1R hnpc' hmii')
    -- cT: value_truthy NotWrittenT frame
    have fT : cT.σ.regs.get? R = σ11.regs.get? R :=
      hframeT R ⟨hx10R, hx14R, hx15R, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    -- σ12: ld a3,0(sp) (writes x13)
    have f12 : σ12.regs.get? R = cT.σ.regs.get? R :=
      (hobs12.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx13R hnpc' hmii')
    -- σ13: beqz taken (writes PC)
    have f13 : σ13.regs.get? R = σ12.regs.get? R :=
      (hobs13.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_taken _ _ _ _ R hmi' hpc' hnpc' hmii')
    -- σ14: li a1,0 (writes x11)
    have f14 : σ14.regs.get? R = σ13.regs.get? R :=
      (hobs14.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx11R hnpc' hmii')
    -- σ15: mv a0,s1 (writes x10)
    have f15 : σ15.regs.get? R = σ14.regs.get? R :=
      (hobs15.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx10R hnpc' hmii')
    -- σ16: jal value_bool (writes x1)
    have f16 : σ16.regs.get? R = σ15.regs.get? R :=
      (hobs16.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' hx1R hnpc' hmii')
    -- cB: value_bool NotWrittenV frame
    have fB : cB.σ.regs.get? R = σ16.regs.get? R :=
      hframeB R ⟨hx11R, hx15R, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    -- σ18: j (writes PC)
    have f18 : σ18.regs.get? R = cB.σ.regs.get? R :=
      (hobs18.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    rw [f18, fB, f16, f15, f14, f13, f12, fT, f11, f10, f9, f8, f7, f6, f5, f4, f3, f2, f1]
    exact (hframe R hR').trans (hbridge R hR' he8 he9 he18 he2)
  ------------------------------------------------------------------------
  -- assemble the epilogue-entry package `PreEpilogueVD` at the extended maps
  ------------------------------------------------------------------------
  have hSteps : Steps c ⟨σ18, i18, cB.steps + 1⟩ := by
    refine (Steps.single hstep1).trans (?_)
    refine (Steps.single hstep2).trans (?_)
    refine (Steps.single hstep3).trans (?_)
    refine (Steps.single hstep4).trans (?_)
    refine (Steps.single hstep5).trans (?_)
    refine (Steps.single hstep6).trans (?_)
    refine (Steps.single hstep7).trans (?_)
    refine (Steps.single hstep8).trans (?_)
    refine (Steps.single hstep9).trans (?_)
    refine (Steps.single hstep10).trans (?_)
    refine (Steps.single hstep11).trans (?_)
    refine hsT.trans (?_)
    refine (Steps.single hstep12).trans (?_)
    refine (Steps.single hstep13).trans (?_)
    refine (Steps.single hstep14).trans (?_)
    refine (Steps.single hstep15).trans (?_)
    refine (Steps.single hstep16).trans (?_)
    refine hsB.trans (?_)
    exact Steps.single hstep18
  refine ⟨⟨σ18, i18, cB.steps + 1⟩, hSteps, σ18.mem, φf', φc', hpf', hpc',
    ⟨?_, hMemExt_fin, hSurvSL_fin⟩⟩
  refine ⟨hG18, hi18, hpc_fin, hs1_fin, hsp_fin, ⟨vmifin, hmifin⟩,
    hout_fin, houtStr, ?_,
    (by rw [hmem18e]; exact hcode_B), (by rw [hmem18e]; exact hvalfalse), hstore_fin, hframeG,
    hslotRa_f, hslotS0_f, hslotS1_f, hslotS2_f, hgv8, hgv9, hgv18, hgv2, ?_,
    (by omega), hsphiRam, (by omega), (by omega), hsp8, hraAl⟩
  · rfl
  · intro a ha hA
    by_cases hsr : sret.toNat ≤ a ∧ a < sret.toNat + 24
    · exact Or.inl hsr
    · refine Or.inr ?_
      rw [hmem18e, ← hmemframeB a hsr]
      show (writeMap8 m2 (sp.toNat-1008) (sdData_val QV))[a]? = m0[a]?
      rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) a (sdData_val QV) (by omega)]
      show (writeMap8 m1 (sp.toNat-1016) (sdData_val PV))[a]? = m0[a]?
      rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) a (sdData_val PV) (by omega)]
      show (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val K13))[a]? = m0[a]?
      rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) a (sdData_val K13) (by omega)]
      rcases hmemFrame a (by omega) hA with hin | heq
      · exact absurd hin (by omega)
      · rw [heq]; exact hMcallM0 a ha hA

/-! ## `AndFalseExtras` — the recursive-case facts beyond `EvalEntry`

Mirrors `EvalNotSim.NotSimExtras` but keyed to the `EX_LOGICAL` arm (slot 7,
arm PC `0x8000355c`), the LEFT operand `el` at node offset 16, the sub-result
buffer at `sp-968`, and the `.logical .and el er` AST. -/
structure AndFalseExtras
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (el er : Expr) (vl : Value)
    (sp sret aExpr aLeft : BitVec 64)
    (m0 : Mem) : Prop where
  slot7 : KindSlotPinned 7 (0x8000355c#64) m0
  expr_survives : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
    ExprRepr m' aExpr.toNat (.logical .and el er)
  left_survives : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
    ExprRepr m' aLeft.toNat el
  pay : read64 m0 (aExpr.toNat + 16) = some aLeft.toNat
  expr24 : aExpr.toNat + 24 ≤ 0x100000000
  expr24_stk : aExpr.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  op_align : aLeft.toNat % 8 = 0
  op_lo : 0x80000000 ≤ aLeft.toNat
  op_hi : aLeft.toNat + 16 ≤ 0x100000000
  op_win : tohostAddr + 16 ≤ aLeft.toNat
  op_stk : aLeft.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aLeft.toNat
  sp_headroom : SL.lo + 3264 ≤ sp.toNat
  sp_SLhi : sp.toNat ≤ SL.hi
  sp16 : sp.toNat % 16 = 0
  SLhi_ram : SL.hi ≤ 0x100000000
  code_stk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  vicode_stk : (0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec
  table_stk : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ (0x80019f58 : Nat)
  arena_stk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arena_code : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo
  expr_align4 : aExpr.toNat % 4 = 0
  expr_win8 : tohostAddr + 8 ≤ aExpr.toNat
  expr_A : aExpr.toNat + 16 ≤ A.lo ∨ A.hi ≤ aExpr.toNat
  expr_sub : aExpr.toNat + 16 ≤ sp.toNat - 968 ∨ sp.toNat - 968 + 24 ≤ aExpr.toNat
  sret_inSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  truthy_loaded : Value_truthyLoaded m0
  bool_loaded : Value_boolLoaded m0
  int_loaded : Value_intLoaded m0
  intslot : IntSlotPinned m0
  truthy_stk : sp.toNat ≤ 0x8000282c ∨ 0x8000285c ≤ SL.lo
  boolcode_stk : sp.toNat ≤ 0x800027f8 ∨ 0x8000280c ≤ SL.lo
  sret_boolcode : sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat
  truthy_arena : A.hi ≤ 0x8000282c ∨ 0x8000285c ≤ A.lo
  bool_arena : A.hi ≤ 0x800027f8 ∨ 0x8000280c ≤ A.lo
  pay_disj : ∀ (m : Mem) (φc' : Addr → Nat) (p : Nat) (s : String),
    ValueRepr m N φc' (sp.toNat - 968) vl → read64 m (sp.toNat - 968 + 8) = some p →
    ∀ k, k ≤ s.length → (p + k < sp.toNat - 1024 ∨ sp.toNat - 1024 + 24 ≤ p + k)

/-! ## `EvalAndSimGoal` — the `EvalE.andFalse` (short-circuit) projection

In the `EvalIH` motive shape. The spec's `andFalse` constructor: one eval of the
left operand (`hIH`) with a falsy result (`vl.truthy = false`) short-circuits to
`.bool false`. Conditional ONLY on `AndFalseExtras` (recursive-case program
structure), `hMcallPop` (M6 Layout: pre-call memory fully populated), and a
`hreach`-style `x13`-survival residual (the `env` register `a3` is passed through
the prologue+dispatch untouched to the arm entry `0x8000355c` — an
`env_get_found`-style mid-state fact a `blockA_k` widening would discharge). -/
def EvalAndSimGoal : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl : Value)
    (sp r sret aEnv aExpr aLeft aEnv3 : BitVec 64)
    (m0 : Mem),
    vl.truthy = false →
    EvalIH st d env el st' vl →
    EvalE st d env (.logical .and el er) st' (.bool false) →
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env (.logical .and el er) sp r sret aEnv aExpr m0 c ∧
        AndFalseExtras N A SL el er vl sp sret aExpr aLeft m0 ∧
        (∀ cm : Config, Steps c cm →
          cm.σ.regs.get? Register.PC = some (0x8000355c#64) →
          cm.σ.regs.get? Register.x13 = some aEnv3) ∧
        -- WAVE 47i (`McallPopTotality` amendment): windowed frame/node presence
        -- + `mem_ext`, replacing the refuted totality oracle.
        -- WAVE 48k: the dead-byte presence CLOSURE is GONE (total reads).
        (∀ mcall : Mem,
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
          MemExtends m0 mcall))
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' (.bool false) sp r sret m0)

/-- `read32 m aExpr = some 7` from `ExprRepr m aExpr (.logical op el er)`. -/
theorem exprRepr_logical_kind {m : Mem} {a : Nat} {op : LogOp} {el er : Expr}
    (h : ExprRepr m a (.logical op el er)) : read32 m a = some 7 := by
  cases h with | logical hk _ _ _ _ _ => exact hk

/-- `LogicalArmCallee` survives a disjoint 8-byte store. -/
theorem logicalCallee_writeMap8 (mem : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hint : a8 + 8 ≤ 0x8000280c ∨ 0x8000281c ≤ a8)
    (hslot : a8 + 8 ≤ jumpTableBase ∨ jumpTableBase + 4 ≤ a8)
    (htruthy : a8 + 8 ≤ 0x8000282c ∨ 0x8000285c ≤ a8)
    (hbool : a8 + 8 ≤ 0x800027f8 ∨ 0x8000280c ≤ a8)
    (hnbstext : a8 + 8 ≤ 0x800027ec ∨ 0x8000282c ≤ a8)
    (hnbstable : a8 + 8 ≤ 0x80019f5c ∨ 0x80019f68 ≤ a8)
    (h : LogicalArmCallee mem) : LogicalArmCallee (writeMap8 mem a8 d) := by
  obtain ⟨hvi, hsl, htr, hbo, hnb⟩ := h
  exact ⟨loaded_int_writeMap8 mem a8 d hint hvi,
    intSlot_writeMap8 mem a8 d hslot hsl,
    loaded_truthy_writeMap8 mem a8 d htruthy htr,
    loaded_bool_writeMap8 mem a8 d hbool hbo,
    nbsPins_writeMap8 mem a8 d hnbstext hnbstable hnb⟩

/-- **`evalAndSim`** — the `EvalE.andFalse` (short-circuit) recursive case, in the
`EvalIH` motive shape. Composes `blockA_k` (prologue+dispatch → widened
`ArmEntryK` @0x8000355c), `blockB_logical` (arm head + LEFT recursive call ⋈ IH →
`SubEvalReturn @0x8000356c`), `blockC_andFalse` (post-call short-circuit tail →
`PreEpilogueVD .bool false`), and `blockD_v_rec` (shared epilogue → `EvalExitD`).
Mirrors `evalNotSim`; the AND-TRUE constructor (two evals) is documented as remaining. -/
theorem evalAndSim : EvalAndSimGoal := by
  intro g N A SL φf φc st st' d env el er vl sp r sret aEnv aExpr aLeft aEnv3
    m0 hvlfalse hIH _hEvalE
  intro c ⟨hc, hx, hx13reach, hMemExtRes⟩
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === block A: prologue + dispatch → widened ArmEntryK @0x8000355c ===
  have hkm0 : read32 m0 aExpr.toNat = some 7 := exprRepr_logical_kind (hc.mem ▸ hc.expr)
  obtain ⟨c1, hs1, ment, v8, v9, v18, _v13, hArm, _hpresM, _hx13⟩ :=
    blockA_k g N A SL φf φc st (.logical .and el er) 7 (0x8000355c#64) LogicalArmCallee
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      hx.slot7
      ⟨hx.int_loaded, hx.intslot, hx.truthy_loaded, hx.bool_loaded, hc.mem ▸ hc.nbs_pins⟩
      (fun mem a8 dd hlo hhi hcl =>
        logicalCallee_writeMap8 mem a8 dd
          (by have := hx.vicode_stk; omega)
          (by simp only [jumpTableBase]; have := hx.table_stk; omega)
          (by have := hx.truthy_stk; omega)
          (by have := hx.boolcode_stk; omega)
          (by have := hx.vicode_stk; omega)
          (by have := hx.table_stk; omega) hcl)
      (fun m' hag => hx.expr_survives m' hag)
      (by decide)
      (by have := hx.table_stk; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
        hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
        hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_align, hc.expr_ram,
        hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint_int,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
        ⟨hc.spill_defined.1, hc.spill_defined.2.1, hc.spill_defined.2.2, hc.x13_defined⟩⟩, rfl⟩
  have hArmCopy := hArm
  obtain ⟨_hAG, _hAtick, hApc, _hAa0, _hAs1, _hAa2, _hAsp, _hAra, _hAmi, _hAout,
    _hAmem, _hAcode, _hAvi, _hAexpr, _hAstr, _hAxAl, _hAxLo, _hAxHi, _hAxWin,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, hArmMemM0,
    hArmg8, hArmg9, hArmg18, hArmg2, _hAstore, _hAstoreSurv, hArmFrame,
    _hAsretAl, _hAsretLo, _hAsretHi, _hAsretWin, _hAsretVi, _hAsretStk, _hAsretEc,
    _hAsp1088, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hASLlo, _hASLwin, _hASLloSp, _hAraAl,
    hAEx11, hAEx8, hAEx18⟩ := hArmCopy
  have hx11c1 : c1.σ.regs.get? Register.x11 = some aEnv := hAEx11
  -- x13 = aEnv3 at the arm entry (from the `hreach` residual, at c1 with PC = 0x8000355c)
  have hx13c1 : c1.σ.regs.get? Register.x13 = some aEnv3 := hx13reach c1 hs1 hApc
  have hgpreframe : ∀ R : Register, AbiPreservedNoise R →
      c1.σ.regs.get? R = (fun R => c1.σ.regs.get? R) R := fun R _ => rfl
  have hgpre_x8 : (fun R => c1.σ.regs.get? R) Register.x8 = some aExpr := hAEx8
  have hgpre18 : ∃ w, (fun R => c1.σ.regs.get? R) Register.x18 = some w := ⟨aEnv, hAEx18⟩
  have hbridge : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      (fun R => c1.σ.regs.get? R) R = g R :=
    fun R hR he8 he9 he18 he2 => hArmFrame R hR he8 he9 he18 he2
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  have hExprMent : ExprRepr ment aExpr.toNat (.logical .and el er) :=
    hx.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  obtain ⟨lp, rp, hk7m, hopTok, hlptrM, hlRM, hrptrM, hrRM⟩ : ∃ lp rp,
      read32 ment aExpr.toNat = some 7 ∧
      read32 ment (aExpr.toNat + 8) = some (logOpTok .and) ∧
      read64 ment (aExpr.toNat + 16) = some lp ∧ ExprRepr ment lp el ∧
      read64 ment (aExpr.toNat + 24) = some rp ∧ ExprRepr ment rp er := by
    cases hExprMent with | logical hk htok hl hlp hr hrp => exact ⟨_, _, hk, htok, hl, hlp, hr, hrp⟩
  have hlptrM' : read64 ment (aExpr.toNat + 16) = some aLeft.toNat := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ :=
      read64_bytes m0 (aExpr.toNat + 16) aLeft.toNat hx.pay
    have hstk := hx.expr24_stk
    simp only [read64, readLE, bind, Option.bind]
    rw [hMentM0 (aExpr.toNat + 16) (by omega), hMentM0 (aExpr.toNat + 16 + 1) (by omega),
        hMentM0 (aExpr.toNat + 16 + 2) (by omega), hMentM0 (aExpr.toNat + 16 + 3) (by omega),
        hMentM0 (aExpr.toNat + 16 + 4) (by omega), hMentM0 (aExpr.toNat + 16 + 5) (by omega),
        hMentM0 (aExpr.toNat + 16 + 6) (by omega), hMentM0 (aExpr.toNat + 16 + 7) (by omega),
        e0, e1, e2, e3, e4, e5, e6, e7]
    simp only []; apply congrArg some; omega
  -- === block B: arm head + LEFT recursive call ⋈ IH → SubEvalReturn @0x8000356c ===
  obtain ⟨c2, hs2, hSub⟩ :=
    blockB_logical g (fun R => c1.σ.regs.get? R) N A SL φf φc st st' d env .and el er vl
      sp r sret aExpr aEnv aLeft aEnv3 v8 v9 v18 c.σ.sailOutput m0 hIH
      c1 ⟨ment, hArm, hx11c1, hx13c1, hgpreframe, ⟨aExpr, hgpre_x8⟩, hgpre18,
        hlptrM',
        (fun m' hag => hx.left_survives m' (fun a ha => (hMentM0 a ha).symm.trans (hag a ha))),
        -- WAVE 47i: the parent ground at the arm entry (ONE kit call).
        ((hc.mem ▸ hc.ground).transport_offstack hc.table_stack_disjoint
          hx.sp_SLhi hMentM0),
        hx.expr24,
        hx.op_align, hx.op_lo, hx.op_hi, hx.op_win, hx.op_stk,
        hx.sp_headroom, hx.sp_SLhi, hx.sp16, hx.SLhi_ram,
        hx.code_stk, hx.vicode_stk, (by have := hx.table_stk; omega),
        hx.arena_stk, hx.arena_code,
        -- ITEM ZERO B1: the LEFT child budget, DERIVED from the entry's
        -- budgeted fields (`StackOK.child` + `bodiesBound_logical`).
        hc.stackBudget.child (by decide)
          (by
            have h1 : (Expr.logical LogOp.and el er).stackNeed
                = evalFrame + max el.stackNeed er.stackNeed := rfl
            have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
            have hm := Nat.le_max_left el.stackNeed er.stackNeed
            simp only [h1, h2, evalFrame]; omega),
        (Expr.bodiesBound_logical hc.expr_bodies).1,
        hc.store_bodies⟩
  obtain ⟨mcall, hSubR, hMcallM0stk⟩ := hSub
  have hAgM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]? := hMcallM0stk
  have hOutC2 : OutRepr c2.σ st' := hSubR.2.2.2.2.2.2.2.2.1
  have houtStr : String.join c2.σ.sailOutput.toList = st'.out := hOutC2
  have hVtruthyMcall : Value_truthyLoaded mcall :=
    loaded_truthy_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.truthy_stk; omega)).symm) hx.truthy_loaded
  have hVboolMcall : Value_boolLoaded mcall :=
    loaded_bool_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.boolcode_stk; omega)).symm) hx.bool_loaded
  have hMcallM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mcall[a]? = m0[a]? := fun a ha _ => hAgM0 a ha
  have hMemExtM0mc : MemExtends m0 mcall := hMemExtRes mcall hAgM0
  have hExprMcall : ExprRepr mcall aExpr.toNat (.logical .and el er) :=
    hx.expr_survives mcall (fun a ha => (hAgM0 a ha).symm)
  have hBufExtras : ∀ φc' : Addr → Nat, ValueRepr c2.σ.mem N φc' (sp.toNat - 968) vl →
      LogicalBufExtras N A SL φc' vl sp sret c2.σ.mem := by
    intro φc' hvr
    exact ⟨(by have := hx.op_lo; have := hx.sp_headroom; omega),
      (by have := hx.sp_headroom; omega),
      (fun p s hvr' hp k hk => hx.pay_disj c2.σ.mem φc' p s hvr' hp k hk)⟩
  -- === block C: post-call short-circuit tail → PreEpilogueVD .bool false @0x800033ec ===
  obtain ⟨c3, hs3, mpreC, φfe, φce, hpfe, hpce, hPreD⟩ :=
    blockC_andFalse (fun R => c1.σ.regs.get? R) g N A SL φf φc st.store.frames.size
      st.store.closures.size st' vl sp r sret aExpr v8 v9 v18
      c2.σ.sailOutput el er m0 hvlfalse
      c2 ⟨mcall, hSubR, hgpre_x8, hExprMcall, hMemExtM0mc,
        hx.expr_align4, hc.expr_ram.1, hc.expr_ram.2, hx.expr_win8,
        hc.expr_stack_disjoint, hx.expr_A, hx.expr_sub,
        houtStr, hc.sret_align, hc.sret_ram.1, hc.sret_ram.2, hc.sret_win,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint,
        hc.ra_align, (by have := hx.sp_headroom; omega), hc.stack_ram.1, hc.stack_win,
        rfl, hVtruthyMcall, hVboolMcall, hBufExtras,
        hx.truthy_stk, hx.boolcode_stk, hx.sret_boolcode, hx.truthy_arena, hx.bool_arena,
        hx.code_stk, hx.sret_inSL, hMcallM0,
        (by have := hx.sp_SLhi; have := hx.SLhi_ram; omega), (by have := hx.sp16; omega),
        hx.SLhi_ram, hx.sp_SLhi,
        hArmg8, hArmg9, hArmg18, hArmg2, hbridge⟩
  -- === block D: shared epilogue → EvalExitD .bool false (via blockD_v_rec) ===
  obtain ⟨c4, hs4, hExitDe⟩ :=
    blockD_v_rec g N A SL φfe φce st' (.bool false) sp r sret v8 v9 v18 c2.σ.sailOutput m0
      c3 ⟨mpreC, hPreD⟩
  obtain ⟨hExitE, hMemExt, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hStoreLe := evalE_store_mono _hEvalE
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st' (.bool false) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfe hpce hExitE hStoreLe.1 hStoreLe.2
  exact ⟨c4, ((hs1.trans hs2).trans hs3).trans hs4, hExit, hMemExt,
    φf', φc', hpfe.trans (PhiExtends.mono hStoreLe.1 hpf'),
    hpce.trans (PhiExtends.mono hStoreLe.2 hpc'), hSurv⟩

end Vsa.Sim
