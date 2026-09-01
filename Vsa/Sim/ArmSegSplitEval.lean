import Vsa.Sim.ArmSegSplit
import Vsa.Sim.ApproxArmReseat

/-!
# `ArmSegSplitEval` — the `EEntryC`-valued jal→child bridge + the unary split (Task #75)

`ArmSegSplit.evalEntry_of_jalPrefix` lands the recursive `jal eval_expr` prefix at
the child's rich `EvalEntry`.  `ApproxArmReseat`'s divergence-fold entries are the
∃-ghost bundles `EEntryC c st d env e := ∃ ghosts, EvalEntry … e … c`.  This file
supplies:

* `landedN_eentryC_of_jalPrefix` — the marshalling fact re-wrapped into the exact
  `LandedN 1 c (fun c' => EEntryC c' st d env esub)` shape `ApproxArmResid`'s
  fields demand (existentially discharging the layout ghosts).  This is the ONE
  reusable bridge from `ArmSegSplit` into the divergence-fold entry type — every
  Eval-child arm class (unary / binaryL / binaryR / logicalL / … / callF /
  argsHead / stmtExpr / …) closes through it after its own arm-head staging span
  establishes the `evalEntry_of_jalPrefix` pre-bundle.

* `unaryE_split` — the **unary class** field of `ApproxArmResidGap`, delivered as a
  precisely-typed split lemma.  Its statement is `ApproxArmResid.unaryE` with the
  interior entries pinned to `EEntryC`, EXCEPT it additionally takes the
  **arm-head staging bundle** `UnaryStagePre` as a hypothesis — the machine-checked
  obstruction below.

## Machine-checked obstruction: why `unaryE` needs staging premises beyond `EEntryC`

`ApproxArmResid.unaryE` asks `EEntryC c st d env (.unary op e) → LandedN 1 c
(EEntryC e)`.  But `EEntryC (.unary op e)` = `∃ ghosts, EvalEntry (.unary op e)`,
and `EvalEntry (.unary op e)`:
  1. is at `eval_expr`'s ENTRY (`pc = evalExprEntry`), NOT at the recursive
     `jal eval_expr` PC (`0x800035e8`).  Reaching the jal requires the WHOLE
     dispatch (`blockA_k`: prologue spills + kind read + jump-table dispatch to the
     arm PC `0x800035e0`) THEN the arm head (`ld a2,16(a2)` operand load; `addi
     a0,sp,144` sub-buffer) — dozens of machine steps, not a named prefix cut.
  2. bakes in the OUTER frame's `sp`, geometry, and `ExprRepr (.unary op e)`.  The
     child entry needs the LOWERED frame `sp - 1088`, the operand node's
     `ExprRepr esub` at `aOperand` (read out of the parent node), and the
     recursive-case extras (`a1 = interp*`, `SL.lo + 3264 ≤ sp` headroom, the
     operand/sub-buffer disjointness at `sp - 1088`).  These are exactly the
     "recursive-case extras" `EvalNegSim.blockB_unary` carries BEYOND its
     `ArmEntryK` — the `ArmEntryK` widening residual — and are NOT projectable from
     `EvalEntry (.unary op e)`.

So the split is genuinely `(dispatch ∘ arm-head staging) ⊗ (jal marshalling)`; the
second factor is `evalEntry_of_jalPrefix` (built + verified), the first is the
UNBUILT arm-head+dispatch staging span (`EvalNegSim.blockB_unary`'s body up to its
`armTail_rec` call, re-cut to land at the pre-bundle instead of consuming the IH).
`unaryE_split` names that span precisely as `UnaryStagePre` and discharges the rest,
making the residual a single, upstream-dischargeable staging lemma.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
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

/-! ## §1. The reusable `EEntryC`-valued bridge -/

/-- **`ArmSegSplit` → the divergence-fold entry type.**  `evalEntry_of_jalPrefix`
lands the recursive `jal eval_expr` prefix at `EvalEntry … esub …`; wrapping the
layout ghosts existentially gives the exact `LandedN 1 c (fun c' => EEntryC c' st d
env esub)` shape `ApproxArmResid`'s Eval-child fields demand.  This is the ONE
bridge every Eval-child arm class reuses after staging its `evalEntry_of_jalPrefix`
pre-bundle. -/
theorem landedN_eentryC_of_jalPrefix
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r sret subsret aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem)
    (c : Config)
    (hjaltgt : (callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 evalExprEntry)
    (hlink : (BitVec.addInt callPC 4) = retPC)
    (hretAl : retPC.toNat % 4 = 0)
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Eval_exprLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4)))
    (hpre :
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some callPC ∧
        c.σ.regs.get? Register.x10 = some subsret ∧
        c.σ.regs.get? Register.x9 = some sret ∧
        c.σ.regs.get? Register.x11 = some aIn ∧
        c.σ.regs.get? Register.x12 = some aOperand ∧
        c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        c.σ.sailOutput = out0 ∧
        String.join out0.toList = st.out ∧
        c.σ.mem = mcall ∧
        Eval_exprLoaded mcall ∧ Value_intLoaded mcall ∧ IntSlotPinned mcall ∧
        ExprRepr mcall aOperand.toNat esub ∧
        StoreRepr mcall N A φf φc st.store ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
            mcall[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        ((∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w)) ∧
        read64 mcall (sp.toNat - 8) = some r.toNat ∧
        read64 mcall (sp.toNat - 16) = some v8.toNat ∧
        read64 mcall (sp.toNat - 24) = some v9.toNat ∧
        read64 mcall (sp.toNat - 32) = some v18.toNat ∧
        aOperand.toNat % 8 = 0 ∧
        0x80000000 ≤ aOperand.toNat ∧ aOperand.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aOperand.toNat ∧
        (aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat) ∧
        subsret.toNat % 8 = 0 ∧
        sp.toNat - 1088 ≤ subsret.toNat ∧ subsret.toNat + 24 ≤ sp.toNat - 32 ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        sp.toNat ≤ 0x100000000 ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧
        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)) :
    LandedN 1 c (fun c' => EEntryC c' st d env esub) := by
  have h := evalEntry_of_jalPrefix gpre N A SL φf φc st d env esub
    callPC retPC jalImm sp r sret subsret aIn aOperand v8 v9 v18 out0 mcall c
    hjaltgt hlink hretAl hjalSite hpre
  -- weaken the rich `EvalEntry` post into the ∃-ghost `EEntryC` bundle.
  exact LandedN.weaken h (fun c' hEE =>
    ⟨fun R => c'.σ.regs.get? R, N, A, SL, φf, φc,
      sp - 1088#64, retPC, subsret, aIn, aOperand, mcall, hEE⟩)

#print axioms landedN_eentryC_of_jalPrefix

/-! ## §2. The unary-class split — `ApproxArmResid.unaryE` at `EEntryC`

The arm-head staging bundle `UnaryStagePre op e c st d env` is the precise,
upstream-dischargeable residual: it says the config `c` at `EEntryC (.unary op e)`
can be advanced (through the dispatch + arm head — the UNBUILT staging span) to a
config satisfying the `evalEntry_of_jalPrefix` pre-bundle for the operand `e`, at a
lowered frame.  Equivalently (and this is the honest packaging), `UnaryStagePre` is
just the existence of the fully-staged jal pre-bundle reached from `c` — a
`LandedN` to the pre-bundle.  With it, the split is `LandedN.bind` of the staging
onto the marshalling bridge (`LandedN.bind` adds the counts, so `1 ≤` is
preserved). -/

-- discipline: allow(R7-conj-tower-def) `JalPreBundle` is the SANCTIONED ∃-ghost
-- LANDING BUNDLE (same precedent as `ApproxArmReseat`'s EEntryC/AEntryC/…): it
-- carries layout DATA (`Addr → Nat` φ-maps, `Arena`, `StackLayout`, the per-arm
-- `callPC`/`retPC`/`jalImm`) that a `structure : Prop` CANNOT project, so it must
-- be a `∃` over that data. It IS the `armTail_rec`/`evalEntry_of_jalPrefix`
-- named pre-bundle (a fixed, doc'd contract), not an ad-hoc anonymous post tower;
-- every consumer goes through the ONE named destructurer `landedN_eentryC_of_preBundle`.
set_option linter.unusedVariables false in
/-- **The `evalEntry_of_jalPrefix` PRE-bundle, as a config predicate over the
operand `e`.**  This is the state at the recursive `jal eval_expr` PC with the
operand's sub-call fully staged (args in `a0`/`a1`/`a2`, `sp` lowered, all
lowered-frame geometry).  Factored out so `UnaryStagePre` can name "the staging
span reaches THIS" and `unaryE_split` can feed it straight to the bridge.  The
`jalImm`/`callPC`/`retPC` are existential because the staging span picks the
concrete arm PCs.  `d`/`env` are carried so the child `EEntryC` inherits the SAME
depth/env as the parent arm (the operand evaluates in the same frame); the
pre-bundle itself constrains only the operand `e` and store `st`. -/
def JalPreBundle (e : Expr) (c' : Config) (st : Vsa.While.St) (d : Nat)
    (env : Addr) : Prop :=
  ∃ (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r sret subsret aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem),
    ((callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 evalExprEntry) ∧
    ((BitVec.addInt callPC 4) = retPC) ∧ retPC.toNat % 4 = 0 ∧
    (∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Eval_exprLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4))) ∧
    GoodState c'.σ ∧ c'.tick < 2 ∧
    c'.σ.regs.get? Register.PC = some callPC ∧
    c'.σ.regs.get? Register.x10 = some subsret ∧
    c'.σ.regs.get? Register.x9 = some sret ∧
    c'.σ.regs.get? Register.x11 = some aIn ∧
    c'.σ.regs.get? Register.x12 = some aOperand ∧
    c'.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
    (∃ w, c'.σ.regs.get? Register.minstret = some w) ∧
    c'.σ.sailOutput = out0 ∧
    String.join out0.toList = st.out ∧
    c'.σ.mem = mcall ∧
    Eval_exprLoaded mcall ∧ Value_intLoaded mcall ∧ IntSlotPinned mcall ∧
    ExprRepr mcall aOperand.toNat e ∧
    StoreRepr mcall N A φf φc st.store ∧
    (∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        mcall[k]? = m'[k]?) →
      StoreRepr m' N A φf φc st.store) ∧
    (∀ R : Register, AbiPreservedNoise R → c'.σ.regs.get? R = gpre R) ∧
    ((∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w)) ∧
    read64 mcall (sp.toNat - 8) = some r.toNat ∧
    read64 mcall (sp.toNat - 16) = some v8.toNat ∧
    read64 mcall (sp.toNat - 24) = some v9.toNat ∧
    read64 mcall (sp.toNat - 32) = some v18.toNat ∧
    aOperand.toNat % 8 = 0 ∧
    0x80000000 ≤ aOperand.toNat ∧ aOperand.toNat + 16 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ aOperand.toNat ∧
    (aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat) ∧
    subsret.toNat % 8 = 0 ∧
    sp.toNat - 1088 ≤ subsret.toNat ∧ subsret.toNat + 24 ≤ sp.toNat - 32 ∧
    SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
    sp.toNat ≤ 0x100000000 ∧
    0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
    (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
    ((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧
    ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
    (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
    (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)

/-- **The jal pre-bundle drives into `EEntryC`.**  A config at `JalPreBundle e`
lands (in `≥ 1` step, the `jal`) at `EEntryC e` — pure application of the
marshalling bridge `landedN_eentryC_of_jalPrefix` after destructuring the bundle.
This is the reusable "pre-bundle ⇒ child entry" half, shared by every Eval-child
class that stages a `jal eval_expr`. -/
theorem landedN_eentryC_of_preBundle
    (e : Expr) (c' : Config) (st : Vsa.While.St) (d : Nat) (env : Addr)
    (h : JalPreBundle e c' st d env) :
    LandedN 1 c' (fun c'' => EEntryC c'' st d env e) := by
  obtain ⟨gpre, N, A, SL, φf, φc, callPC, retPC, jalImm, sp, r, sret, subsret,
    aIn, aOperand, v8, v9, v18, out0, mcall, hjaltgt, hlink, hretAl, hjalSite, hrest⟩ := h
  exact landedN_eentryC_of_jalPrefix gpre N A SL φf φc st d env e
    callPC retPC jalImm sp r sret subsret aIn aOperand v8 v9 v18 out0 mcall c'
    hjaltgt hlink hretAl hjalSite hrest

#print axioms landedN_eentryC_of_preBundle

/-- The arm-head staging residual for the unary class: from `EEntryC (.unary op
e)`, the dispatch + arm-head span reaches (in `≥ 1` steps) a config satisfying the
`JalPreBundle` for the operand `e`.  This is STRICTLY SMALLER than the `unaryE`
conclusion — it stops at the jal pre-bundle, letting the verified marshalling
bridge finish.  UNBUILT span = `EvalNegSim.blockB_unary`'s body (dispatch + operand
load + sub-buffer `addi`) re-cut to LAND at the pre-bundle rather than consume the
IH. -/
def UnaryStagePre (op : UnOp) (e : Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr) : Prop :=
  EEntryC c st d env (.unary op e) →
  LandedN 1 c (fun c' => JalPreBundle e c' st d env)

/-- **The unary class field of `ApproxArmResidGap`.**  Given the arm-head staging
residual `UnaryStagePre` (which stops at the jal pre-bundle), the split has EXACTLY
the `ApproxArmResid.unaryE` type at the concrete `EEntryC` entry: `LandedN.bind`
composes the staging (`≥ 1` step to the pre-bundle) with the verified marshalling
bridge (`≥ 1` step, `jal`, to `EEntryC e`).  `LandedN.bind` adds the counts
(`1 + 1`), then `weakenCount` drops to `1`.  The marshalling fact
`evalEntry_of_jalPrefix` is now LOAD-BEARING in the split; only `UnaryStagePre`
remains upstream. -/
theorem unaryE_split (op : UnOp) (e : Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hstage : UnaryStagePre op e c st d env) :
    EEntryC c st d env (.unary op e) →
    LandedN 1 c (fun c' => EEntryC c' st d env e) := by
  intro hEE
  have hstaged : LandedN 1 c (fun c' => JalPreBundle e c' st d env) := hstage hEE
  have hcomp : LandedN (1 + 1) c (fun c' => EEntryC c' st d env e) :=
    LandedN.bind hstaged (fun c' hpb => landedN_eentryC_of_preBundle e c' st d env hpb)
  exact LandedN.weakenCount (by omega) hcomp

#print axioms unaryE_split

/-! ## §3. The generic Eval-child split combinator + the binary/logical classes

Every Eval-child arm field of `ApproxArmResid` has the shape "from `EEntryC` at a
COMPOUND node, land (`≥ 1` step) at `EEntryC` of a CHILD sub-expression".  The
divergence-fold proof is ALWAYS the same: the arm-head staging span reaches
`JalPreBundle child`, then the verified marshalling bridge finishes.  This
combinator captures that composition ONCE; each class supplies only its staging
residual (a `LandedN 1 … (JalPreBundle child)`). -/

/-- **Generic Eval-child split.**  A staging landing to `JalPreBundle child`
composes with the marshalling bridge to a `LandedN 1` to `EEntryC child`.  This is
the shared body of EVERY Eval-child arm field (unary/binaryL/binaryR/logicalL/…/
callF/argsHead/stmtExpr/stmtRet/stmtVarInit/stmtIfCond/stmtWhileCond/flCond). -/
theorem evalChildSplit_of_stage
    (child : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr)
    (hstaged : LandedN 1 c (fun c' => JalPreBundle child c' st d env)) :
    LandedN 1 c (fun c' => EEntryC c' st d env child) :=
  LandedN.weakenCount (by omega : 1 ≤ 1 + 1)
    (LandedN.bind hstaged
      (fun c' hpb => landedN_eentryC_of_preBundle child c' st d env hpb))

#print axioms evalChildSplit_of_stage

/-- **`binaryL` class field.**  `EEntryC (.binary op l r) → LandedN 1 (EEntryC l)`.
Left operand: the binary arm head (`blockA_binaryArm`'s dispatch + the
`0x800034e8..0x800034f8` operand-pointer load span) stages the LEFT sub-call, then
`armTail_rec`'s front (`evalEntry_of_jalPrefix`) marshals — SAME `armTail_rec`
seam as unary (`EvalBinSim.blockB_binary:513`).  Residual = the left-staging span
reaching `JalPreBundle l`. -/
theorem binaryL_split (op : BinOp) (l r : Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hstage : EEntryC c st d env (.binary op l r) →
      LandedN 1 c (fun c' => JalPreBundle l c' st d env)) :
    EEntryC c st d env (.binary op l r) →
    LandedN 1 c (fun c' => EEntryC c' st d env l) :=
  fun hEE => evalChildSplit_of_stage l c st d env (hstage hEE)

#print axioms binaryL_split

/-- **`binaryR` class field.**  `EvalE l st' lv → EEntryC (.binary op l r) →
LandedN 1 (EEntryC l→r at st')`.  Right operand: the MID-arm re-staging span (the
second `jal eval_expr` at `0x80003518`, after the LEFT returned into the spill and
the right operand pointer is reloaded — `EvalBinSim.blockB_binary:611..911`) stages
the RIGHT sub-call at the updated store `st'`, then the SAME `armTail_rec` seam
marshals.  The staging residual carries the `EvalE l st' lv` fact (the left result
determines `st'`) AND — wave 36 — the MACHINE-level left IH `EvalIH st d env l st'
lv` (`hIH`): reaching the mid-arm requires actually RUNNING the left `jal eval_expr`
and returning (`armTail_rec`), which the spec-level `EvalE` cannot drive
(observation `2026-09-01 binaryR-field-lacks-machine-IH`, proposal (b)).  The split's
CONCLUSION keeps the `ApproxArmResid.binaryR` type unchanged; the IH is discharged by
the bundle's `evalIH` link in `armResidGap_evalChildFields`. -/
theorem binaryR_split (op : BinOp) (l r : Expr) (c : Config) (st st' : Vsa.While.St)
    (d : Nat) (env : Addr) (lv : Value)
    (hIH : EvalIH st d env l st' lv)
    (hstage : EvalIH st d env l st' lv → EvalE st d env l st' lv →
      EEntryC c st d env (.binary op l r) →
      LandedN 1 c (fun c' => JalPreBundle r c' st' d env)) :
    EvalE st d env l st' lv → EEntryC c st d env (.binary op l r) →
    LandedN 1 c (fun c' => EEntryC c' st' d env r) :=
  fun hEval hEE => evalChildSplit_of_stage r c st' d env (hstage hIH hEval hEE)

#print axioms binaryR_split

/-- **`logicalL` class field.**  Identical shape to `binaryL` — the logical arm
(`&&`/`||`) shares the two-operand arm head; `l` is the first sub-call. -/
theorem logicalL_split (lop : Vsa.While.LogOp) (l r : Expr) (c : Config)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (hstage : EEntryC c st d env (.logical lop l r) →
      LandedN 1 c (fun c' => JalPreBundle l c' st d env)) :
    EEntryC c st d env (.logical lop l r) →
    LandedN 1 c (fun c' => EEntryC c' st d env l) :=
  fun hEE => evalChildSplit_of_stage l c st d env (hstage hEE)

#print axioms logicalL_split

/-- **`logicalR` class field.**  Identical shape to `binaryR` — the second logical
sub-call at store `st'` after the left short-circuit test evaluated; carries the
same machine-level left IH (wave 36). -/
theorem logicalR_split (lop : Vsa.While.LogOp) (l r : Expr) (c : Config)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (lv : Value)
    (hIH : EvalIH st d env l st' lv)
    (hstage : EvalIH st d env l st' lv → EvalE st d env l st' lv →
      EEntryC c st d env (.logical lop l r) →
      LandedN 1 c (fun c' => JalPreBundle r c' st' d env)) :
    EvalE st d env l st' lv → EEntryC c st d env (.logical lop l r) →
    LandedN 1 c (fun c' => EEntryC c' st' d env r) :=
  fun hEval hEE => evalChildSplit_of_stage r c st' d env (hstage hIH hEval hEE)

#print axioms logicalR_split

/-- **`assignE` class field.**  `EEntryC (.assign x e) → LandedN 1 (EEntryC e)`.
The assign arm evaluates the RHS `e` first (its recursive `jal eval_expr`), then
does `env_set`; the RHS sub-call stages exactly as the unary operand.  Residual =
the assign-arm-head span reaching `JalPreBundle e`. -/
theorem assignE_split (x : String) (e : Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hstage : EEntryC c st d env (.assign x e) →
      LandedN 1 c (fun c' => JalPreBundle e c' st d env)) :
    EEntryC c st d env (.assign x e) →
    LandedN 1 c (fun c' => EEntryC c' st d env e) :=
  fun hEE => evalChildSplit_of_stage e c st d env (hstage hEE)

#print axioms assignE_split

/-- **`callF` class field.**  `EEntryC (.call f args) → LandedN 1 (EEntryC f)`.
The call arm evaluates the CALLEE expression `f` first; its sub-call stages as a
single operand.  Residual = the call-arm-head span reaching `JalPreBundle f`. -/
theorem callF_split (f : Expr) (args : List Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hstage : EEntryC c st d env (.call f args) →
      LandedN 1 c (fun c' => JalPreBundle f c' st d env)) :
    EEntryC c st d env (.call f args) →
    LandedN 1 c (fun c' => EEntryC c' st d env f) :=
  fun hEE => evalChildSplit_of_stage f c st d env (hstage hEE)

#print axioms callF_split

/-! ## §4. The exec-dispatch → eval-child classes

The statement arms that evaluate a sub-EXPRESSION (`stmtExpr`, `stmtRet`,
`stmtVarInit`, `stmtIfCond`, `stmtWhileCond`) and the for-cond arm (`flCond`) all
land at an `EEntryC` (a child expression), so they reuse the SAME
`evalChildSplit_of_stage` combinator — only their SOURCE entry differs
(`SEntryC`/`FEntryC` instead of `EEntryC`).  The staging residual is the
exec-dispatch prefix (`ExecDispatch`'s prologue + kind read + jump-table dispatch
to the arm) plus the arm head reaching the `jal eval_expr` — re-cut to land at
`JalPreBundle` rather than consume the eval IH. -/

/-- **`stmtExpr` class field.**  `SEntryC (.expr e) → LandedN 1 (EEntryC e)`. -/
theorem stmtExpr_split (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat)
    (env : Addr)
    (hstage : SEntryC c st d env (.expr e) →
      LandedN 1 c (fun c' => JalPreBundle e c' st d env)) :
    SEntryC c st d env (.expr e) →
    LandedN 1 c (fun c' => EEntryC c' st d env e) :=
  fun hSE => evalChildSplit_of_stage e c st d env (hstage hSE)

#print axioms stmtExpr_split

/-- **`stmtRet` class field.**  `SEntryC (.ret (some e)) → LandedN 1 (EEntryC e)`. -/
theorem stmtRet_split (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat)
    (env : Addr)
    (hstage : SEntryC c st d env (.ret (some e)) →
      LandedN 1 c (fun c' => JalPreBundle e c' st d env)) :
    SEntryC c st d env (.ret (some e)) →
    LandedN 1 c (fun c' => EEntryC c' st d env e) :=
  fun hSE => evalChildSplit_of_stage e c st d env (hstage hSE)

#print axioms stmtRet_split

/-- **`stmtVarInit` class field.**  `SEntryC (.varDecl x (some e)) → LandedN 1
(EEntryC e)`. -/
theorem stmtVarInit_split (x : String) (e : Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hstage : SEntryC c st d env (.varDecl x (some e)) →
      LandedN 1 c (fun c' => JalPreBundle e c' st d env)) :
    SEntryC c st d env (.varDecl x (some e)) →
    LandedN 1 c (fun c' => EEntryC c' st d env e) :=
  fun hSE => evalChildSplit_of_stage e c st d env (hstage hSE)

#print axioms stmtVarInit_split

/-- **`stmtIfCond` class field.**  `SEntryC (.ifStmt cnd t e) → LandedN 1
(EEntryC cnd)`. -/
theorem stmtIfCond_split (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (hstage : SEntryC c st d env (.ifStmt cnd t e) →
      LandedN 1 c (fun c' => JalPreBundle cnd c' st d env)) :
    SEntryC c st d env (.ifStmt cnd t e) →
    LandedN 1 c (fun c' => EEntryC c' st d env cnd) :=
  fun hSE => evalChildSplit_of_stage cnd c st d env (hstage hSE)

#print axioms stmtIfCond_split

/-- **`stmtWhileCond` class field.**  `SEntryC (.whileStmt cnd b) → LandedN 1
(EEntryC cnd)`. -/
theorem stmtWhileCond_split (cnd : Expr) (b : Stmt) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hstage : SEntryC c st d env (.whileStmt cnd b) →
      LandedN 1 c (fun c' => JalPreBundle cnd c' st d env)) :
    SEntryC c st d env (.whileStmt cnd b) →
    LandedN 1 c (fun c' => EEntryC c' st d env cnd) :=
  fun hSE => evalChildSplit_of_stage cnd c st d env (hstage hSE)

#print axioms stmtWhileCond_split

/-- **`flCond` class field.**  `FEntryC (some cc) step b → LandedN 1 (EEntryC cc)`.
The for-loop condition sub-expression evaluates via the same `jal eval_expr`
seam. -/
theorem flCond_split (cc : Expr) (step : Option Expr) (b : Stmt) (c : Config)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (hstage : FEntryC c st d env (some cc) step b →
      LandedN 1 c (fun c' => JalPreBundle cc c' st d env)) :
    FEntryC c st d env (some cc) step b →
    LandedN 1 c (fun c' => EEntryC c' st d env cc) :=
  fun hFE => evalChildSplit_of_stage cc c st d env (hstage hFE)

#print axioms flCond_split

/-- **`flStep` class field.**  `ForCond … → ExecS … → status normal/cont → FEntryC
(some e) → LandedN 1 (EEntryC e)`.  The for-loop STEP sub-expression (post-body)
evaluates via the same seam; the extra `ForCond`/`ExecS`/status hypotheses pin the
spec state `st''` at which the step is evaluated. -/
theorem flStep_split (cnd : Option Expr) (e : Expr) (b : Stmt) (status : Status)
    (c : Config) (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr)
    (hstage : ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → FEntryC c st d env cnd (some e) b →
      LandedN 1 c (fun c' => JalPreBundle e c' st'' d env)) :
    ForCond st d env cnd st' → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → FEntryC c st d env cnd (some e) b →
    LandedN 1 c (fun c' => EEntryC c' st'' d env e) :=
  fun hFC hEx hst hFE => evalChildSplit_of_stage e c st'' d env (hstage hFC hEx hst hFE)

#print axioms flStep_split

/-- **`argsHead` class field.**  `AEntryC (e :: es) → LandedN 1 (EEntryC e)`.  The
arg loop evaluates the head arg `e` via the same `jal eval_expr` seam (from the
arg-loop control point), landing at the child expr entry. -/
theorem argsHead_split (e : Expr) (es : List Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hstage : AEntryC c st d env (e :: es) →
      LandedN 1 c (fun c' => JalPreBundle e c' st d env)) :
    AEntryC c st d env (e :: es) →
    LandedN 1 c (fun c' => EEntryC c' st d env e) :=
  fun hAE => evalChildSplit_of_stage e c st d env (hstage hAE)

#print axioms argsHead_split

/-! ## §5. Capstone — the eval-child staging bundle

`EvalChildStages` bundles the staging residuals for 14 EVAL-CHILD-LANDING
fields of `ApproxArmResidGap` (the fields whose post is `EEntryC <child expr>`,
with no extra spec-side hypotheses; `flStep` also lands at `EEntryC` but carries
`ForCond`/`ExecS`/status premises, so it is the separate `flStep_split`).
Each residual is STRICTLY SMALLER than the raw field: it stops at `JalPreBundle`,
and the verified marshalling bridge (`landedN_eentryC_of_preBundle`, built on
`evalEntry_of_jalPrefix`) finishes.  A future supplier that lands the 14 staging
spans (arm-head + dispatch re-cut to `JalPreBundle`) fills these 14 fields of
`ApproxArmResidGap` by the `*_split` corollaries below (plus `flStep_split`).

The remaining fields land at NON-`EEntryC` entries (`AEntryC` arg-loop tail,
`CEntryC` callee body, `SEntryC`/`SqEntryC`/`FEntryC` statement/for control) and
need their OWN marshalling facts (`exec_stmt`-entry / `SegEntry`-anchored), NOT
the eval-child bridge — they stay named in `ApproxArmResidGap`. -/

/-- The staging residuals for the 15 eval-child-landing fields.  Each is the
per-class arm-head-to-`JalPreBundle` span (the strictly-smaller upstream residual).
Bundling them lets the capstone discharge all 15 fields uniformly through
`evalChildSplit_of_stage`. -/
structure EvalChildStages : Prop where
  /-- **The completed-sub-derivation simulation link `EvalE → EvalIH` (wave 36).**
  The `binaryR`/`logicalR` staging spans must RUN the completed LEFT sub-eval on the
  machine (`armTail_rec`), which needs the machine-level `EvalIH` — underivable from
  the spec `EvalE` alone, and NOT derivable inside the divergence fold (its strong
  induction yields only `Divg` step lower bounds for still-running derivations).
  SUPPLIER: `TermSimAssembly.term_sim_of_cases` — its conclusion `mEvalE … t` IS
  `EvalIH st d env e st' v` (`TermSimAssembly.lean:80-82`) for every derivation
  `t : EvalE …` — i.e. the term-family capstone, conditionally on the M4 residual
  bundle.  Non-circular: `term_sim_of_cases` is the `@EvalE.rec` assembly and does
  not depend on any divergence-family theorem. -/
  evalIH : ∀ (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (st' : Vsa.While.St) (v : Value),
    EvalE st d env e st' v → EvalIH st d env e st' v
  unary : ∀ (op : UnOp) (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
    EEntryC c st d env (.unary op e) → LandedN 1 c (fun c' => JalPreBundle e c' st d env)
  binaryL : ∀ (op : BinOp) (l r : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
    EEntryC c st d env (.binary op l r) → LandedN 1 c (fun c' => JalPreBundle l c' st d env)
  binaryR : ∀ (op : BinOp) (l r : Expr) (c : Config) (st st' : Vsa.While.St) (d : Nat)
    (env : Addr) (lv : Value),
    EvalIH st d env l st' lv →
    EvalE st d env l st' lv → EEntryC c st d env (.binary op l r) →
    LandedN 1 c (fun c' => JalPreBundle r c' st' d env)
  logicalL : ∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr),
    EEntryC c st d env (.logical lop l r) → LandedN 1 c (fun c' => JalPreBundle l c' st d env)
  logicalR : ∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st st' : Vsa.While.St)
    (d : Nat) (env : Addr) (lv : Value),
    EvalIH st d env l st' lv →
    EvalE st d env l st' lv → EEntryC c st d env (.logical lop l r) →
    LandedN 1 c (fun c' => JalPreBundle r c' st' d env)
  assignE : ∀ (x : String) (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
    EEntryC c st d env (.assign x e) → LandedN 1 c (fun c' => JalPreBundle e c' st d env)
  callF : ∀ (f : Expr) (args : List Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
    EEntryC c st d env (.call f args) → LandedN 1 c (fun c' => JalPreBundle f c' st d env)
  argsHead : ∀ (e : Expr) (es : List Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
    AEntryC c st d env (e :: es) → LandedN 1 c (fun c' => JalPreBundle e c' st d env)
  stmtExpr : ∀ (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
    SEntryC c st d env (.expr e) → LandedN 1 c (fun c' => JalPreBundle e c' st d env)
  stmtRet : ∀ (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
    SEntryC c st d env (.ret (some e)) → LandedN 1 c (fun c' => JalPreBundle e c' st d env)
  stmtVarInit : ∀ (x : String) (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
    SEntryC c st d env (.varDecl x (some e)) → LandedN 1 c (fun c' => JalPreBundle e c' st d env)
  stmtIfCond : ∀ (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr),
    SEntryC c st d env (.ifStmt cnd t e) → LandedN 1 c (fun c' => JalPreBundle cnd c' st d env)
  stmtWhileCond : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
    SEntryC c st d env (.whileStmt cnd b) → LandedN 1 c (fun c' => JalPreBundle cnd c' st d env)
  flCond : ∀ (cc : Expr) (step : Option Expr) (b : Stmt) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr),
    FEntryC c st d env (some cc) step b → LandedN 1 c (fun c' => JalPreBundle cc c' st d env)

/-- **The 15 eval-child fields of `ApproxArmResidGap`, discharged from
`EvalChildStages`.**  Each is `<field>_split` fed the bundled staging residual.
Returned as a conjunction (the exact field types of `ApproxArmResid`) so the final
`ApproxArmResidGap` assembly consumes them directly.  This is the "per-class
field-group theorem the final assembly can consume" the brief asks for: the 15
eval-child fields are DONE modulo the staging bundle; the other 21 stay open. -/
theorem armResidGap_evalChildFields (S : EvalChildStages) :
    (∀ (op : UnOp) (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
      EEntryC c st d env (.unary op e) → LandedN 1 c (fun c' => EEntryC c' st d env e)) ∧
    (∀ (op : BinOp) (l r : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
      EEntryC c st d env (.binary op l r) → LandedN 1 c (fun c' => EEntryC c' st d env l)) ∧
    (∀ (op : BinOp) (l r : Expr) (c : Config) (st st' : Vsa.While.St) (d : Nat) (env : Addr)
      (lv : Value), EvalE st d env l st' lv → EEntryC c st d env (.binary op l r) →
      LandedN 1 c (fun c' => EEntryC c' st' d env r)) ∧
    (∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
      EEntryC c st d env (.logical lop l r) → LandedN 1 c (fun c' => EEntryC c' st d env l)) ∧
    (∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st st' : Vsa.While.St) (d : Nat)
      (env : Addr) (lv : Value), EvalE st d env l st' lv → EEntryC c st d env (.logical lop l r) →
      LandedN 1 c (fun c' => EEntryC c' st' d env r)) ∧
    (∀ (x : String) (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
      EEntryC c st d env (.assign x e) → LandedN 1 c (fun c' => EEntryC c' st d env e)) ∧
    (∀ (f : Expr) (args : List Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
      EEntryC c st d env (.call f args) → LandedN 1 c (fun c' => EEntryC c' st d env f)) ∧
    (∀ (e : Expr) (es : List Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
      AEntryC c st d env (e :: es) → LandedN 1 c (fun c' => EEntryC c' st d env e)) ∧
    (∀ (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
      SEntryC c st d env (.expr e) → LandedN 1 c (fun c' => EEntryC c' st d env e)) ∧
    (∀ (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
      SEntryC c st d env (.ret (some e)) → LandedN 1 c (fun c' => EEntryC c' st d env e)) ∧
    (∀ (x : String) (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
      SEntryC c st d env (.varDecl x (some e)) → LandedN 1 c (fun c' => EEntryC c' st d env e)) ∧
    (∀ (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st : Vsa.While.St) (d : Nat)
      (env : Addr), SEntryC c st d env (.ifStmt cnd t e) →
      LandedN 1 c (fun c' => EEntryC c' st d env cnd)) ∧
    (∀ (cnd : Expr) (b : Stmt) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr),
      SEntryC c st d env (.whileStmt cnd b) → LandedN 1 c (fun c' => EEntryC c' st d env cnd)) ∧
    (∀ (cc : Expr) (step : Option Expr) (b : Stmt) (c : Config) (st : Vsa.While.St) (d : Nat)
      (env : Addr), FEntryC c st d env (some cc) step b →
      LandedN 1 c (fun c' => EEntryC c' st d env cc)) :=
  ⟨fun op e c st d env => unaryE_split op e c st d env (S.unary op e c st d env),
   fun op l r c st d env => binaryL_split op l r c st d env (S.binaryL op l r c st d env),
   fun op l r c st st' d env lv hEv => binaryR_split op l r c st st' d env lv
     (S.evalIH st d env l st' lv hEv) (S.binaryR op l r c st st' d env lv) hEv,
   fun lop l r c st d env => logicalL_split lop l r c st d env (S.logicalL lop l r c st d env),
   fun lop l r c st st' d env lv hEv => logicalR_split lop l r c st st' d env lv
     (S.evalIH st d env l st' lv hEv) (S.logicalR lop l r c st st' d env lv) hEv,
   fun x e c st d env => assignE_split x e c st d env (S.assignE x e c st d env),
   fun f args c st d env => callF_split f args c st d env (S.callF f args c st d env),
   fun e es c st d env => argsHead_split e es c st d env (S.argsHead e es c st d env),
   fun e c st d env => stmtExpr_split e c st d env (S.stmtExpr e c st d env),
   fun e c st d env => stmtRet_split e c st d env (S.stmtRet e c st d env),
   fun x e c st d env => stmtVarInit_split x e c st d env (S.stmtVarInit x e c st d env),
   fun cnd t e c st d env => stmtIfCond_split cnd t e c st d env (S.stmtIfCond cnd t e c st d env),
   fun cnd b c st d env => stmtWhileCond_split cnd b c st d env (S.stmtWhileCond cnd b c st d env),
   fun cc step b c st d env => flCond_split cc step b c st d env (S.flCond cc step b c st d env)⟩

#print axioms armResidGap_evalChildFields

end Vsa.Sim
