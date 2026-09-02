import Vsa.Sim.StagePreSuppliers
import Vsa.Sim.StagePreSuppliers2
import Vsa.Sim.EvalNegSim3
import Vsa.Sim.EvalAndSim

/-!
# `blockA_unaryGenArm` — GENERATED arm dispatch bridge (scripts/gen_arm_bridge.py)

The EX_UNARY arm entry bridge (regenerated twin of the hand blockA_unaryArm, tag 8).

The op-independent prologue+dispatch multiplier `EvalEntry .unary op esub → blockB_unaryGen_stagePre`'s entry bundle: run `blockA_k` at `(tag 8, 0x800035e0#64, UnaryArmCallee)`, destructure the widened `ArmEntryK`, transport the operand pointer(s) `m0→ment`, repackage the stagePre `hpre`.  GENERALIZED from the hand `blockA_unaryArm`/`blockA_logicalArm` twins by `gen_arm_bridge.py`.

GENERATED — DO NOT hand-edit.  Regenerate via `gen_arm_bridge.py`.
NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats` bump beyond the block-A files' standing budget.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
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

/-! ## `UnaryArmExtrasGen` — the unaryGen-arm facts beyond `EvalEntry`. -/
structure UnaryArmExtrasGen
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (op : UnOp) (esub : Expr)
    (sp sret aExpr aOperand : BitVec 64)
    (m0 : Mem) : Prop where
  slot8 : KindSlotPinned 8 (0x800035e0#64) m0
  expr_survives : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
    ExprRepr m' aExpr.toNat (.unary op esub)
  pay : read64 m0 (aExpr.toNat + 16) = some aOperand.toNat
  operand_repr : ExprRepr m0 aOperand.toNat esub
  expr24 : aExpr.toNat + 24 ≤ 0x100000000
  expr24_stk : aExpr.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  op_align : aOperand.toNat % 8 = 0
  op_lo : 0x80000000 ≤ aOperand.toNat
  op_hi : aOperand.toNat + 16 ≤ 0x100000000
  op_win : tohostAddr + 16 ≤ aOperand.toNat
  op_stk : aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat
  sp_headroom : SL.lo + 3264 ≤ sp.toNat
  sp_SLhi : sp.toNat ≤ SL.hi
  sp16 : sp.toNat % 16 = 0
  SLhi_ram : SL.hi ≤ 0x100000000
  code_stk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  vicode_stk : (0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c
  table_stk : (0x80019f7c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58
  arena_stk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arena_code : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo

/-- **`blockA_unaryGenArm`** — the .unary op esub arm entry bridge. -/
theorem blockA_unaryGenArm
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (op : UnOp) (esub : Expr)
    (sp r sret aEnv aExpr aOperand : BitVec 64)
    (m0 : Mem)
    (hX : UnaryArmExtrasGen N A SL op esub sp sret aExpr aOperand m0) :
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env (.unary op esub) sp r sret aEnv aExpr m0 c)
      (fun c => ∃ (v8 v9 v18 : BitVec 64) (ment : Mem),
        ArmEntryK g N A SL φf φc st (0x800035e0#64) UnaryArmCallee (.unary op esub)
          sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0 ment c ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = (fun R => c.σ.regs.get? R) R) ∧
        (∃ w, (fun R => c.σ.regs.get? R) Register.x8 = some w) ∧
        (∃ w, (fun R => c.σ.regs.get? R) Register.x18 = some w) ∧
        read64 ment (aExpr.toNat + 16) = some aOperand.toNat ∧
        ExprRepr ment aOperand.toNat esub ∧
        aExpr.toNat + 24 ≤ 0x100000000 ∧
        aOperand.toNat % 8 = 0 ∧
        0x80000000 ≤ aOperand.toNat ∧ aOperand.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aOperand.toNat ∧
        (aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        SL.hi ≤ 0x100000000 ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧
        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)) := by
  intro c hc
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hkm0 : read32 m0 aExpr.toNat = some 8 := by
    cases (hc.mem ▸ hc.expr) with | unary hk _ _ _ => exact hk
  -- === block A: prologue + dispatch → widened ArmEntryK @0x800035e0#64 ===
  obtain ⟨c1, hs1, ment, v8, v9, v18, hArm, _hpresM⟩ :=
    blockA_k g N A SL φf φc st (.unary op esub) 8 (0x800035e0#64) UnaryArmCallee
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      hX.slot8
      ⟨hc.mem ▸ hc.value_int_code, hc.mem ▸ hc.int_slot⟩
      (fun mem a8 dd hlo hhi hcl => by
        obtain ⟨hvi, hsl⟩ := hcl
        refine ⟨loaded_int_writeMap8 mem a8 dd (by
          have := hc.vicode_stack_disjoint; omega) hvi, ?_⟩
        exact intSlot_writeMap8 mem a8 dd (by
          have := hc.table_stack_disjoint; simp only [jumpTableBase]; omega) hsl)
      (fun m' hag => hX.expr_survives m' hag)
      (by decide)
      (by have := hX.table_stk; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
        hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
        hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_align, hc.expr_ram,
        hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
        hc.spill_defined⟩, rfl⟩
  have hArmCopy := hArm
  obtain ⟨_hAG, _hAtick, hApc, _hAa0, _hAs1, _hAa2, _hAsp, _hAra, _hAmi, _hAout,
    _hAmem, _hAcode, _hAvi, _hAexpr, _hAstr, _hAxAl, _hAxLo, _hAxHi, _hAxWin,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, hArmMemM0,
    _hArmg8, _hArmg9, _hArmg18, _hArmg2, _hAstore, _hAstoreSurv, hArmFrame,
    _hAsretAl, _hAsretLo, _hAsretHi, _hAsretWin, _hAsretVi, _hAsretStk, _hAsretEc,
    _hAsp1088, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hASLlo, _hASLwin, _hASLloSp, _hAraAl,
    hAEx11, hAEx8, hAEx18⟩ := hArmCopy
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  have hExprMent : ExprRepr ment aExpr.toNat (.unary op esub) :=
    hX.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  have hpayMent' : read64 ment (aExpr.toNat + 16) = some aOperand.toNat := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ :=
      read64_bytes m0 (aExpr.toNat + 16) aOperand.toNat hX.pay
    have hstk := hX.expr24_stk
    simp only [read64, readLE, bind, Option.bind]
    rw [hMentM0 (aExpr.toNat + 16) (by omega), hMentM0 (aExpr.toNat + 16 + 1) (by omega),
        hMentM0 (aExpr.toNat + 16 + 2) (by omega), hMentM0 (aExpr.toNat + 16 + 3) (by omega),
        hMentM0 (aExpr.toNat + 16 + 4) (by omega), hMentM0 (aExpr.toNat + 16 + 5) (by omega),
        hMentM0 (aExpr.toNat + 16 + 6) (by omega), hMentM0 (aExpr.toNat + 16 + 7) (by omega),
        e0, e1, e2, e3, e4, e5, e6, e7]
    simp only []; apply congrArg some; omega
  obtain ⟨p, hk8m, hopTok, hpayMent, hsubReprMent⟩ : ∃ p,
      read32 ment aExpr.toNat = some 8 ∧
      read32 ment (aExpr.toNat + 8) = some (unOpTok op) ∧
      read64 ment (aExpr.toNat + 16) = some p ∧ ExprRepr ment p esub := by
    cases hExprMent with | unary hk htok hp hpe => exact ⟨_, hk, htok, hp, hpe⟩
  have hpeq : p = aOperand.toNat := Option.some.inj (hpayMent.symm.trans hpayMent')
  subst hpeq
  -- realign the ArmEntryK `out0` from the entry to the reached `c1.σ.sailOutput`
  have hArm' : ArmEntryK g N A SL φf φc st (0x800035e0#64) UnaryArmCallee (.unary op esub)
      sp r sret aExpr aEnv v8 v9 v18 c1.σ.sailOutput m0 ment c1 := _hAout.symm ▸ hArm
  refine ⟨c1, hs1, v8, v9, v18, ment, hArm', hAEx11, (fun R _ => rfl), ⟨aExpr, hAEx8⟩, ⟨aEnv, hAEx18⟩,
    hpayMent', hsubReprMent, hX.expr24,
    hX.op_align, hX.op_lo, hX.op_hi, hX.op_win, hX.op_stk,
    hX.sp_headroom, hX.sp_SLhi, hX.sp16, hX.SLhi_ram,
    hX.code_stk, hX.vicode_stk, (by have := hX.table_stk; omega),
    hX.arena_stk, hX.arena_code⟩

#print axioms blockA_unaryGenArm

end Vsa.Sim
