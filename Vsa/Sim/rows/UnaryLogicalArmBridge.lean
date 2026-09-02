import Vsa.Sim.StagePreSuppliers
import Vsa.Sim.StagePreSuppliers2
import Vsa.Sim.EvalNegSim3
import Vsa.Sim.EvalAndSim

/-!
# `UnaryLogicalArmBridge` — the EX_UNARY / EX_LOGICAL arm entry bridges

The unary/logical companions of `rows/BinArmBridge.blockA_binaryArm`: the two
`EvalEntry node → the `blockB_*_stagePre` entry bundle` dispatch multipliers,
completing the parametrization of the arm-dispatch bridge across all three
recursive eval-arm families (binary already done).

Each is the op-INDEPENDENT prologue+dispatch: run `blockA_k` at
`(k, armPC, calleeLoaded)`, destructure the widened `ArmEntryK`, transport the
operand pointer(s) from the entry memory `m0` into the arm-entry memory `ment`,
and repackage the `blockB_*_stagePre` `hpre` bundle.  The whole body is bit-for-bit
the block-A prefix already inside `EvalNegSim3.evalNegSim` / `EvalAndSim.evalAndSim`
(the `blockA_k → blockB_*` composition) — here cut off at the stagePre `hpre`
instead of consuming the eval IH, so `evalChildField_of_blockA_stage` can compose it
with the landed `blockB_*_stagePre` staging cut into the `unary`/`logicalL`
`EvalChildStages` fields.

The three bridges differ ONLY in `{tag, armPC, calleeLoaded + its survival lemma,
number of operands transported, output post shape}`; the `blockA_k` run,
`ArmEntryK`-copy destructure, `gpre := c1.σ.regs.get?` call-point ghost, and the
node-`ExprRepr` transport are shared verbatim.  `UnaryArmExtras`/`LogicalArmExtras`
name the geometry each consumes (the `NegExtras`/`AndFalseExtras` subset that the
stagePre `hpre` demands — NOT the post-call blockC facts, which the stagePre cut
does not touch).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats` bump
beyond the block-A files' standing budget.
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

/-! ## §1. `UnaryArmExtras` — the unary-arm facts beyond `EvalEntry`

The `NegExtras` subset the stagePre `hpre` (not blockC) demands.  Stated over the
entry memory `m0`; `aOperand` is the single operand-node address. -/
structure UnaryArmExtras
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

/-- **`blockA_unaryArm`** — the EX_UNARY arm entry bridge.  `EvalEntry (.unary op esub)
→ `blockB_unary_stagePre`'s `hpre`.  The op-independent prologue+dispatch multiplier
for the whole unary family, modelled on `blockA_binaryArm`; composes with
`blockB_unary_stagePre` into the `EvalChildStages.unary` field. -/
theorem blockA_unaryArm
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (op : UnOp) (esub : Expr)
    (sp r sret aEnv aExpr aOperand : BitVec 64)
    (m0 : Mem)
    (hX : UnaryArmExtras N A SL op esub sp sret aExpr aOperand m0) :
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
  -- === block A: prologue + dispatch → widened ArmEntryK @0x800035e0 ===
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
  obtain ⟨_hAG, _hAtick, _hApc, _hAa0, _hAs1, _hAa2, _hAsp, _hAra, _hAmi, _hAout,
    _hAmem, _hAcode, _hAvi, _hAexpr, _hAstr, _hAxAl, _hAxLo, _hAxHi, _hAxWin,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, hArmMemM0,
    _hArmg8, _hArmg9, _hArmg18, _hArmg2, _hAstore, _hAstoreSurv, hArmFrame,
    _hAsretAl, _hAsretLo, _hAsretHi, _hAsretWin, _hAsretVi, _hAsretStk, _hAsretEc,
    _hAsp1088, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hASLlo, _hASLwin, _hASLloSp, _hAraAl,
    hAEx11, hAEx8, hAEx18⟩ := hArmCopy
  -- `ment ↔ m0` outside the stack window (from the widened `ArmEntryK` memframe)
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  -- transport the node's operand pointer from `m0` to `ment`
  have hExprMent : ExprRepr ment aExpr.toNat (.unary op esub) :=
    hX.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  obtain ⟨p, hk8m, hopTok, hpayMent, hsubReprMent⟩ : ∃ p,
      read32 ment aExpr.toNat = some 8 ∧
      read32 ment (aExpr.toNat + 8) = some (unOpTok op) ∧
      read64 ment (aExpr.toNat + 16) = some p ∧ ExprRepr ment p esub := by
    cases hExprMent with | unary hk htok hp hpe => exact ⟨_, hk, htok, hp, hpe⟩
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
  have hpeq : p = aOperand.toNat := Option.some.inj (hpayMent.symm.trans hpayMent')
  subst hpeq
  -- realign the ArmEntryK `out0` from the entry `c.σ.sailOutput` to the reached `c1.σ.sailOutput`
  have hArm' : ArmEntryK g N A SL φf φc st (0x800035e0#64) UnaryArmCallee (.unary op esub)
      sp r sret aExpr aEnv v8 v9 v18 c1.σ.sailOutput m0 ment c1 := _hAout.symm ▸ hArm
  refine ⟨c1, hs1, v8, v9, v18, ment, hArm', hAEx11, (fun R _ => rfl), ⟨aExpr, hAEx8⟩, ⟨aEnv, hAEx18⟩,
    hpayMent', hsubReprMent, hX.expr24,
    hX.op_align, hX.op_lo, hX.op_hi, hX.op_win, hX.op_stk,
    hX.sp_headroom, hX.sp_SLhi, hX.sp16, hX.SLhi_ram,
    hX.code_stk, hX.vicode_stk, (by have := hX.table_stk; omega),
    hX.arena_stk, hX.arena_code⟩

#print axioms blockA_unaryArm

/-! ## §2. `LogicalArmExtras` — the logical-arm facts beyond `EvalEntry`

The `AndFalseExtras` subset the stagePre `hpre` demands (tag 7, `0x8000355c`,
`LogicalArmCallee`), plus the `x13`-reach residual (`env` in `a3` survives the
prologue+dispatch to the arm entry — a `blockA_k`-widening / `hreach`-style fact,
the same one `evalAndSim` threads).  `aLeft` is the LEFT operand-node address. -/
structure LogicalArmExtras
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (op : LogOp) (el er : Expr)
    (sp sret aExpr aLeft : BitVec 64)
    (m0 : Mem) : Prop where
  slot7 : KindSlotPinned 7 (0x8000355c#64) m0
  expr_survives : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
    ExprRepr m' aExpr.toNat (.logical op el er)
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
  vicode_stk : (0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c
  table_stk : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ (0x80019f58 : Nat)
  arena_stk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arena_code : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo
  truthy_loaded : Value_truthyLoaded m0
  bool_loaded : Value_boolLoaded m0
  int_loaded : Value_intLoaded m0
  intslot : IntSlotPinned m0
  truthy_stk : sp.toNat ≤ 0x8000282c ∨ 0x8000285c ≤ SL.lo
  boolcode_stk : sp.toNat ≤ 0x800027f8 ∨ 0x8000280c ≤ SL.lo

/-- **`blockA_logicalArm`** — the EX_LOGICAL arm entry bridge.  `EvalEntry
(.logical op el er) → `blockB_logical_stagePre`'s `hpre`.  The op-independent
prologue+dispatch multiplier for both logical operators, modelled on
`blockA_binaryArm`/`evalAndSim`'s block-A; composes with `blockB_logical_stagePre`
into the `EvalChildStages.logicalL` field.  The `x13`-reach residual (`env` in `a3`
survives to the arm entry) is threaded as `hx13reach` — the `hreach`-style fact
`evalAndSim` also assumes, over the reached config at `0x8000355c`. -/
theorem blockA_logicalArm
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (op : LogOp) (el er : Expr)
    (sp r sret aEnv aExpr aLeft aEnv3 : BitVec 64)
    (m0 : Mem)
    (hX : LogicalArmExtras N A SL op el er sp sret aExpr aLeft m0) :
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env (.logical op el er) sp r sret aEnv aExpr m0 c ∧
        (∀ cm : Config, Steps c cm →
          cm.σ.regs.get? Register.PC = some (0x8000355c#64) →
          cm.σ.regs.get? Register.x13 = some aEnv3))
      (fun c => ∃ (v8 v9 v18 : BitVec 64) (ment : Mem),
        ArmEntryK g N A SL φf φc st (0x8000355c#64) LogicalArmCallee (.logical op el er)
          sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0 ment c ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnv3 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = (fun R => c.σ.regs.get? R) R) ∧
        (∃ w, (fun R => c.σ.regs.get? R) Register.x8 = some w) ∧
        (∃ w, (fun R => c.σ.regs.get? R) Register.x18 = some w) ∧
        read64 ment (aExpr.toNat + 16) = some aLeft.toNat ∧
        (∀ m' : Mem,
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m'[a]?) →
          ExprRepr m' aLeft.toNat el) ∧
        aExpr.toNat + 24 ≤ 0x100000000 ∧
        aLeft.toNat % 8 = 0 ∧
        0x80000000 ≤ aLeft.toNat ∧ aLeft.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aLeft.toNat ∧
        (aLeft.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aLeft.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        SL.hi ≤ 0x100000000 ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧
        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)) := by
  intro c ⟨hc, hx13reachC⟩
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hkm0 : read32 m0 aExpr.toNat = some 7 := by
    cases (hc.mem ▸ hc.expr) with | logical hk _ _ _ _ _ => exact hk
  -- === block A: prologue + dispatch → widened ArmEntryK @0x8000355c ===
  obtain ⟨c1, hs1, ment, v8, v9, v18, hArm, _hpresM⟩ :=
    blockA_k g N A SL φf φc st (.logical op el er) 7 (0x8000355c#64) LogicalArmCallee
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      hX.slot7
      ⟨hX.int_loaded, hX.intslot, hX.truthy_loaded, hX.bool_loaded⟩
      (fun mem a8 dd hlo hhi hcl =>
        logicalCallee_writeMap8 mem a8 dd
          (by have := hX.vicode_stk; omega)
          (by simp only [jumpTableBase]; have := hX.table_stk; omega)
          (by have := hX.truthy_stk; omega)
          (by have := hX.boolcode_stk; omega) hcl)
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
  have hx13c1 : c1.σ.regs.get? Register.x13 = some aEnv3 := hx13reachC c1 hs1 hApc
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  have hExprMent : ExprRepr ment aExpr.toNat (.logical op el er) :=
    hX.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  obtain ⟨lp, rp, hk7m, hopTok, hlptrM, hlRM, hrptrM, hrRM⟩ : ∃ lp rp,
      read32 ment aExpr.toNat = some 7 ∧
      read32 ment (aExpr.toNat + 8) = some (logOpTok op) ∧
      read64 ment (aExpr.toNat + 16) = some lp ∧ ExprRepr ment lp el ∧
      read64 ment (aExpr.toNat + 24) = some rp ∧ ExprRepr ment rp er := by
    cases hExprMent with | logical hk htok hl hlp hr hrp => exact ⟨_, _, hk, htok, hl, hlp, hr, hrp⟩
  have hlptrM' : read64 ment (aExpr.toNat + 16) = some aLeft.toNat := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ :=
      read64_bytes m0 (aExpr.toNat + 16) aLeft.toNat hX.pay
    have hstk := hX.expr24_stk
    simp only [read64, readLE, bind, Option.bind]
    rw [hMentM0 (aExpr.toNat + 16) (by omega), hMentM0 (aExpr.toNat + 16 + 1) (by omega),
        hMentM0 (aExpr.toNat + 16 + 2) (by omega), hMentM0 (aExpr.toNat + 16 + 3) (by omega),
        hMentM0 (aExpr.toNat + 16 + 4) (by omega), hMentM0 (aExpr.toNat + 16 + 5) (by omega),
        hMentM0 (aExpr.toNat + 16 + 6) (by omega), hMentM0 (aExpr.toNat + 16 + 7) (by omega),
        e0, e1, e2, e3, e4, e5, e6, e7]
    simp only []; apply congrArg some; omega
  have hArm' : ArmEntryK g N A SL φf φc st (0x8000355c#64) LogicalArmCallee (.logical op el er)
      sp r sret aExpr aEnv v8 v9 v18 c1.σ.sailOutput m0 ment c1 := _hAout.symm ▸ hArm
  refine ⟨c1, hs1, v8, v9, v18, ment, hArm', hAEx11, hx13c1, (fun R _ => rfl),
    ⟨aExpr, hAEx8⟩, ⟨aEnv, hAEx18⟩, hlptrM',
    (fun m' hag => hX.left_survives m' (fun a ha => (hMentM0 a ha).symm.trans (hag a ha))),
    hX.expr24, hX.op_align, hX.op_lo, hX.op_hi, hX.op_win, hX.op_stk,
    hX.sp_headroom, hX.sp_SLhi, hX.sp16, hX.SLhi_ram,
    hX.code_stk, hX.vicode_stk, (by have := hX.table_stk; omega),
    hX.arena_stk, hX.arena_code⟩

#print axioms blockA_logicalArm

end Vsa.Sim
