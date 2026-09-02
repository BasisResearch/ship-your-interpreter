import Vsa.Sim.StagePreSuppliers
import Vsa.Sim.StagePreSuppliers2
import Vsa.Sim.rows.BinArmBridge
import Vsa.Sim.rows.UnaryLogicalArmBridge
import Vsa.Sim.EntryGroundKit

/-!
# `EvalChildFieldCombinator` — the parametric arm-head field composer (Task #81 item 1)

Three eval-child arm-head cuts had already landed as ~200-line hand batteries
(`blockB_unary_stagePre`, `blockB_binary_leftStagePre`, `blockB_logical_stagePre`),
each stated over the `ArmEntryK`-∃ **entry bundle** (their `hpre`), NOT over the
`EvalChildStages`-field entry `EEntryC`.  The gap between the two is the
case-INDEPENDENT dispatch bridge `EvalEntry → ArmEntryK`-∃ (`blockA_binaryArm` for
the binary arm; `blockA_k` inline for unary/logical).  Every eval-child field's
supplier is then the SAME two-factor composition:

```
EEntryC node  --unpack ghosts-->  EvalEntry node
              --blockA (a Triple)-->  (the stagePre entry bundle, a config-post)
              --stagePre (a LandedN)-->  JalPreBundle child
```

Building that composition BY HAND for each of the ~14 eval-child fields is the third
clone the discipline (Law 3) forbids.  This file factors it ONCE as
`evalChildField_of_blockA_stage`: given a `blockA` bridge (`Triple` from the rich
`EvalEntry` to any intermediate config-post `Mid`) and a `stagePre` consumer
(`∀ c, Mid c → LandedN k c (JalPreBundle child)` with `1 ≤ k`), it yields the field
shape `LandedN 1 c (JalPreBundle child)`.  The `blockA` `Triple` (an unbounded
`Steps` prefix) and the `stagePre` `LandedN k` compose by lifting the prefix to a
`StepsN` (`Steps.toN`) and adding counts (`StepsN.trans_add`); the total count is
`≥ k ≥ 1`, so `LandedN 1` holds with the marshalling bridge downstream untouched.

`binaryL_field_of_extras` is the FIRST fully-composed eval-child field: it threads
`blockA_binaryArm` (whose POST is EXACTLY `blockB_binary_leftStagePre`'s `hpre`) into
the combinator, closing `EvalChildStages.binaryL` MODULO one honest named premise —
`BinArmExtras` (the op-independent arm geometry the dispatch bridge consumes).  No
new machine steps: both halves are landed; the combinator is the pure seam.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats` bump.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.ApproxArmReseat

namespace Vsa.Sim

set_option linter.unusedVariables false

/-! ## §1. The parametric composer -/

/-- **The parametric arm-head field composer.**  A dispatch bridge `blockA` reaching
an intermediate post `Mid` (a `Triple` — an unbounded `Steps` prefix from the rich
`EvalEntry`) composes with an arm-head staging cut `stage` (a `LandedN k` from `Mid`
to `JalPreBundle child`, `1 ≤ k`) into the `EvalChildStages`-field landing
`LandedN 1 c (JalPreBundle child)`.

The prefix `Steps` is lifted to `StepsN` (`Steps.toN`) and the two runs are added
(`StepsN.trans_add`); the sum is `≥ k ≥ 1`.  This is the ONE seam every eval-child
arm-head cut plugs into, factoring the hand composition out of all ~14 fields. -/
theorem evalChildField_of_blockA_stage
    {P Mid : Config → Prop} {child : Expr}
    {st : Vsa.While.St} {d : Nat} {env : Addr} {k : Nat}
    (hk : 1 ≤ k)
    (blockA : Triple P Mid)
    (stage : ∀ c, Mid c → LandedN k c (fun c' => JalPreBundle child c' st d env))
    (c : Config) (hc : P c) :
    LandedN 1 c (fun c' => JalPreBundle child c' st d env) := by
  -- run the dispatch bridge to the intermediate post `Mid`
  obtain ⟨c1, hs1, hMid⟩ := blockA c hc
  -- run the arm-head staging cut from there
  obtain ⟨m2, c2, hm2, hs2, hpb⟩ := stage c1 hMid
  -- lift the prefix `Steps` to a counted run and add
  obtain ⟨n1, hn1⟩ := hs1.toN
  exact ⟨n1 + m2, c2, by omega, hn1.trans_add hs2, hpb⟩

#print axioms evalChildField_of_blockA_stage

/-! ## §2. The binary-LEFT field instantiation — the first fully-composed eval-child

`blockA_binaryArm`'s POST is bit-for-bit `blockB_binary_leftStagePre`'s `hpre`: the
`ArmEntryK` bundle at `0x800034e8` plus `BinExtras`, the `x11`/`x13`/`x19` pins, the
`gpre` frame, the two operand-pointer read-backs, the sub-frame presence, and
`MemExtends`.  So the two landed halves compose with ZERO impedance — the combinator
threads them and the `binaryL` field is closed modulo `BinArmExtras` alone. -/

/-- **`BinArmGeomProvider`** — the honest `binaryL`-field arm-geometry residual.
`EEntryC (.binary op l r)` unpacks to `EvalEntry` at SOME layout ghosts; the dispatch
bridge `blockA_binaryArm` consumes `BinArmExtras` for exactly those ghosts (plus the
two operand-node addresses `aLOp`/`aROp`, which `EvalEntry` does not pin — they are
read out of the node at run time, so they ride under the ∃ here).  This names that
residual once: for the rich entry's own ghosts, the arm geometry holds. -/
def BinArmGeomProvider
    (op : BinOp) (l r : Expr) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r0 sret aEnv aExpr : BitVec 64) (m0 : Mem),
    EvalEntry g N A SL φf φc st d env (.binary op l r) sp r0 sret aEnv aExpr m0 c →
    ∃ (aLOp aROp : BitVec 64), BinArmExtras g N A SL op l r sp r0 sret aExpr aLOp aROp m0

/-- **The `EvalChildStages.binaryL` field, composed from the two landed halves.**
From the `EEntryC (.binary op l r)` entry plus the op-independent arm geometry
(`BinArmGeomProvider`), the dispatch bridge `blockA_binaryArm` reaches
`blockB_binary_leftStagePre`'s entry bundle, and that cut stages the LEFT sub-call —
landing at `JalPreBundle l`.  The honest remaining premise is `BinArmGeomProvider`
(the standing arm-geometry residual `blockA` consumes); everything else is discharged
by the two landed lemmas + the §1 seam.  This is a drop-in `EvalChildStages.binaryL`
supplier — the FIRST eval-child field whose whole `EEntryC → JalPreBundle` path is
machine-composed (dispatch bridge + arm-head cut), no hand re-threading. -/
theorem binaryL_field_of_extras
    (op : BinOp) (l r : Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hGeom : BinArmGeomProvider op l r st d env c)
    (hEE : EEntryC c st d env (.binary op l r)) :
    LandedN 1 c (fun c' => JalPreBundle l c' st d env) := by
  obtain ⟨g, N, A, SL, φf, φc, sp, r0, sret, aEnv, aExpr, m0, hEntry⟩ := hEE
  obtain ⟨aLOp, aROp, hX⟩ := hGeom g N A SL φf φc sp r0 sret aEnv aExpr m0 hEntry
  refine evalChildField_of_blockA_stage (k := 4) (by omega)
    (blockA_binaryArm g N A SL φf φc st d env op l r sp r0 sret aEnv aExpr aLOp aROp m0 hX)
    (fun c' hMid => ?_) c hEntry
  -- unpack `blockA_binaryArm`'s POST → feed `blockB_binary_leftStagePre`'s `hpre`
  obtain ⟨gpre, aEnvReg, v8, v9, v18, v19, ment, hArm, hBE, hx11, hx13, hx19,
    hgframe, hg8, hg18, hgx8v, hgx18v, hgx19v, hpayL, hexprL, hpayR, hexprR,
    hMentPop, hMemExtM0, hGmt47⟩ := hMid
  exact blockB_binary_leftStagePre g gpre N A SL φf φc st d env op l r
    sp r0 sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 c'.σ.sailOutput m0 c'
    ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8, hg18, hgx8v, hgx18v, hgx19v,
      hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0, hGmt47,
      -- ITEM ZERO B1: the LEFT child budget, DERIVED from the entry's fields.
      hEntry.stackBudget.child (by decide)
        (by
          have h1 : (Expr.binary op l r).stackNeed
              = evalFrame + max l.stackNeed r.stackNeed := rfl
          have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
          have hm := Nat.le_max_left l.stackNeed r.stackNeed
          simp only [h1, h2, evalFrame]; omega),
      (Expr.bodiesBound_binary hEntry.expr_bodies).1,
      hEntry.store_bodies⟩

#print axioms binaryL_field_of_extras

/-! ## §3. The unary field — via `blockA_unaryArm` ≫ `blockB_unary_stagePre` -/

/-- **`UnaryArmGeomProvider`** — the honest `unary`-field arm-geometry residual (the
`BinArmGeomProvider` analogue).  For the rich entry's own layout ghosts, the unary
arm geometry (`UnaryArmExtras`, at SOME operand-node addr `aOperand`) holds. -/
def UnaryArmGeomProvider
    (op : UnOp) (e : Expr) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r0 sret aEnv aExpr : BitVec 64) (m0 : Mem),
    EvalEntry g N A SL φf φc st d env (.unary op e) sp r0 sret aEnv aExpr m0 c →
    ∃ (aOperand : BitVec 64), UnaryArmExtras N A SL op e sp sret aExpr aOperand m0

/-- **The `EvalChildStages.unary` field, machine-composed.**  From `EEntryC (.unary op e)`
plus the op-independent arm geometry (`UnaryArmGeomProvider`), the dispatch bridge
`blockA_unaryArm` reaches `blockB_unary_stagePre`'s entry bundle, and that cut stages
the operand sub-call — landing at `JalPreBundle e`.  The honest remaining premise is
`UnaryArmGeomProvider`; everything else is the two landed lemmas + the §1 seam. -/
theorem unaryE_field_of_extras
    (op : UnOp) (e : Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hGeom : UnaryArmGeomProvider op e st d env c)
    (hEE : EEntryC c st d env (.unary op e)) :
    LandedN 1 c (fun c' => JalPreBundle e c' st d env) := by
  obtain ⟨g, N, A, SL, φf, φc, sp, r0, sret, aEnv, aExpr, m0, hEntry⟩ := hEE
  obtain ⟨aOperand, hX⟩ := hGeom g N A SL φf φc sp r0 sret aEnv aExpr m0 hEntry
  refine evalChildField_of_blockA_stage (k := 2) (by omega)
    (blockA_unaryArm g N A SL φf φc st d env op e sp r0 sret aEnv aExpr aOperand m0 hX)
    (fun c' hMid => ?_) c hEntry
  obtain ⟨v8, v9, v18, ment, hArm, hx11, hx13, hgframe, hg8, hg18,
    hpayL, hexprL, hground, hexprHi24, hopAl, hopLo, hopHi, hopWin, hopStk,
    hsproom, hspSLhi, hsp16, hSLhiRam, hcodeStk, hviStk, htableStk,
    harenaStk, harenaCode⟩ := hMid
  exact blockB_unary_stagePre g (fun R => c'.σ.regs.get? R) N A SL φf φc st d env op e
    sp r0 sret aExpr aEnv aOperand v8 v9 v18 c'.σ.sailOutput m0 c'
    ⟨ment, hArm, hx11, hx13, hgframe, hg8, hg18, hpayL, hexprL, hground, hexprHi24,
      hopAl, hopLo, hopHi, hopWin, hopStk, hsproom, hspSLhi, hsp16, hSLhiRam,
      hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
      -- ITEM ZERO B1: the operand's child budget, DERIVED from the entry's fields.
      hEntry.stackBudget.child (by decide)
        (by
          have h1 : (Expr.unary op e).stackNeed = evalFrame + e.stackNeed := rfl
          have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
          simp only [h1, h2, evalFrame]; omega),
      Expr.bodiesBound_unary hEntry.expr_bodies,
      hEntry.store_bodies⟩

#print axioms unaryE_field_of_extras

/-! ## §4. The logical-LEFT field — via `blockA_logicalArm` ≫ `blockB_logical_stagePre` -/

/-- **`LogicalArmGeomProvider`** — the honest `logicalL`-field arm-geometry residual.
Carries `LogicalArmExtras` AND the `x13`-reach fact (`env` in `a3` survives to the arm
entry `0x8000355c`), both over the rich entry's own ghosts, at SOME left-operand addr
`aLeft` and env-slot value `aEnv3`. -/
def LogicalArmGeomProvider
    (op : Vsa.While.LogOp) (l r : Expr) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r0 sret aEnv aExpr : BitVec 64) (m0 : Mem),
    EvalEntry g N A SL φf φc st d env (.logical op l r) sp r0 sret aEnv aExpr m0 c →
    ∃ (aLeft aEnv3 : BitVec 64),
      LogicalArmExtras N A SL op l r sp sret aExpr aLeft m0 ∧
      (∀ cm : Config, Steps c cm →
        cm.σ.regs.get? Register.PC = some (0x8000355c#64) →
        cm.σ.regs.get? Register.x13 = some aEnv3)

/-- **The `EvalChildStages.logicalL` field, machine-composed.**  From
`EEntryC (.logical op l r)` plus the op-independent arm geometry
(`LogicalArmGeomProvider`), the dispatch bridge `blockA_logicalArm` reaches
`blockB_logical_stagePre`'s entry bundle, and that cut stages the LEFT operand — landing
at `JalPreBundle l`.  The honest remaining premise is `LogicalArmGeomProvider`. -/
theorem logicalL_field_of_extras
    (op : Vsa.While.LogOp) (l r : Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hGeom : LogicalArmGeomProvider op l r st d env c)
    (hEE : EEntryC c st d env (.logical op l r)) :
    LandedN 1 c (fun c' => JalPreBundle l c' st d env) := by
  obtain ⟨g, N, A, SL, φf, φc, sp, r0, sret, aEnv, aExpr, m0, hEntry⟩ := hEE
  obtain ⟨aLeft, aEnv3, hX, hReach⟩ := hGeom g N A SL φf φc sp r0 sret aEnv aExpr m0 hEntry
  refine evalChildField_of_blockA_stage (k := 3) (by omega)
    (blockA_logicalArm g N A SL φf φc st d env op l r sp r0 sret aEnv aExpr aLeft aEnv3 m0 hX)
    (fun c' hMid => ?_) c ⟨hEntry, hReach⟩
  obtain ⟨v8, v9, v18, ment, hArm, hx11, hx13, hgframe, hg8, hg18,
    hpayL, hexprSurvL, hgroundP, hexprHi24, hopAl, hopLo, hopHi, hopWin, hopStk,
    hsproom, hspSLhi, hsp16, hSLhiRam, hcodeStk, hviStk, htableStk,
    harenaStk, harenaCode⟩ := hMid
  exact blockB_logical_stagePre g (fun R => c'.σ.regs.get? R) N A SL φf φc st d env op l r
    sp r0 sret aExpr aEnv aLeft aEnv3 v8 v9 v18 c'.σ.sailOutput m0 c'
    ⟨ment, hArm, hx11, hx13, hgframe, hg8, hg18, hpayL, hexprSurvL, hgroundP, hexprHi24,
      hopAl, hopLo, hopHi, hopWin, hopStk, hsproom, hspSLhi, hsp16, hSLhiRam,
      hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
      -- ITEM ZERO B1: the LEFT child budget, DERIVED from the entry's fields.
      hEntry.stackBudget.child (by decide)
        (by
          have h1 : (Expr.logical op l r).stackNeed
              = evalFrame + max l.stackNeed r.stackNeed := rfl
          have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
          have hm := Nat.le_max_left l.stackNeed r.stackNeed
          simp only [h1, h2, evalFrame]; omega),
      (Expr.bodiesBound_logical hEntry.expr_bodies).1,
      hEntry.store_bodies⟩

#print axioms logicalL_field_of_extras

end Vsa.Sim
