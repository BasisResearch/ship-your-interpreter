import Vsa.Sim.MidArmFieldIH

/-!
# `MidArmFieldWire` — closing the re-typed `binaryR`/`logicalR` fields (Wave 36)

Wave 36 re-typed `EvalChildStages.binaryR`/`logicalR` to carry the machine-level left
IH (`EvalIH st d env l st' lv`), unblocking the landed mid-arm seam
`MidArmFieldIH.midArmField_of_IH` (`armTail_rec` ≫ `binaryR_midStage1`).  This file
wires the seam into the two fields:

* `MidArmLeftJalBundle` — the ∃-ghost LANDING BUNDLE for the mid-arm staging
  residual: a config at the shared left `jal eval_expr` PC (`0x800034f8`) satisfying
  `armTail_rec`'s precondition, together with the right-operand marshal
  (`MidArmRightMarshal`) on every `SubEvalReturn` config AT THE SAME GHOSTS.  The
  ghosts must cohere between the pre and the marshal, so both live under ONE ∃ —
  `JalPreBundle l` cannot be reused (its ∃ forgets the PC pins and cannot mention the
  marshal).  The jal-site fact is NOT carried: it is the landed
  `BinHeadSites.site_800034f8_ee`, discharged here.  (Tower duplication recorded:
  observation `2026-09-01 armtailrec-pre-tower-has-no-named-def`.)

* `jalPreBundle_of_midArmBundle` — the destructurer: bundle + `EvalIH` →
  `LandedN 1 (JalPreBundle er)`.  ONE `midArmField_of_IH` call; the three fixed-target
  facts are `decide`d (`0x800034f8 + 0x1ffc6c → evalExprEntry`, link `0x800034fc`).

* `BinaryRStagePre` / `LogicalRStagePre` — the per-arm honest staging residuals
  (the `BinArmGeomProvider` analogue): arm entry `EEntryC` → `LandedN 1` to
  `MidArmLeftJalBundle`.  STRICTLY SMALLER than the fields they discharge: they stop
  at the LEFT jal; the recursive left call (`armTail_rec`, via the IH) and the 7
  mid-arm sites (`binaryR_midStagePre`) are load-bearing downstream, never re-derived.

* `binaryR_field_of_stage` / `logicalR_field_of_stage` — the field closers: staging
  residual + IH → the exact (re-typed) `EvalChildStages.binaryR`/`logicalR` field
  bodies, by `LandedN.bind`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats` bump.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
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

-- discipline: allow(R7-conj-tower-def) `MidArmLeftJalBundle` is a SANCTIONED ∃-ghost
-- LANDING BUNDLE (same precedent as `JalPreBundle`/`EEntryC`): it carries layout DATA
-- (φ-maps, `Arena`, `StackLayout`, per-arm registers) that a `structure : Prop` cannot
-- project, and its pre-tower is `armTail_rec`'s fixed contract (spelled once more —
-- see observation `armtailrec-pre-tower-has-no-named-def` for the factoring proposal).
-- Every consumer goes through the ONE named destructurer `jalPreBundle_of_midArmBundle`.
/-- **The mid-arm staging landing bundle.**  The config `c'` sits at the shared LEFT
`jal eval_expr` PC (`0x800034f8`) with the left sub-call staged (= `armTail_rec`'s
precondition, `l` in the operand register), and — at the SAME ghosts — the
right-operand marshal holds on every `SubEvalReturn` config the left call can produce.
`st`/`st'`/`lv` pin the pre/post spec states and left value of the completed left
eval; `er` is the RIGHT operand whose `JalPreBundle` the mid-arm lands. -/
def MidArmLeftJalBundle (l er : Expr) (c' : Config) (st st' : Vsa.While.St)
    (d : Nat) (env : Addr) (lv : Value) : Prop :=
  ∃ (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp rr sret subsret aIn aLOp aROp aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem),
    -- the right-operand marshalling residual on every SubEvalReturn config:
    (∀ cL : Config,
      SubEvalReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' lv sp rr sret subsret (0x800034fc#64) v8 v9 v18 mcall cL →
      MidArmRightMarshal gpre N A SL φf φc st' d env er
        sp rr sret aExpr aEnv aROp v8 v9 v18 cL) ∧
    -- `armTail_rec`'s precondition (= `JalPreBundle l`'s content, PCs pinned) at `c'`:
    (GoodState c'.σ ∧ c'.tick < 2 ∧
     c'.σ.regs.get? Register.PC = some (0x800034f8#64) ∧
     c'.σ.regs.get? Register.x10 = some subsret ∧
     c'.σ.regs.get? Register.x9 = some sret ∧
     c'.σ.regs.get? Register.x11 = some aIn ∧
     c'.σ.regs.get? Register.x12 = some aLOp ∧
     c'.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
     (∃ w, c'.σ.regs.get? Register.minstret = some w) ∧
     c'.σ.sailOutput = out0 ∧
     String.join out0.toList = st.out ∧
     c'.σ.mem = mcall ∧
     Eval_exprLoaded mcall ∧ Value_intLoaded mcall ∧ IntSlotPinned mcall ∧
     ExprRepr mcall aLOp.toNat l ∧
     StoreRepr mcall N A φf φc st.store ∧
     (∀ m' : Mem,
       (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
         mcall[k]? = m'[k]?) →
       StoreRepr m' N A φf φc st.store) ∧
     (∀ R : Register, AbiPreservedNoise R → c'.σ.regs.get? R = gpre R) ∧
     ((∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w)) ∧
     read64 mcall (sp.toNat - 8) = some rr.toNat ∧
     read64 mcall (sp.toNat - 16) = some v8.toNat ∧
     read64 mcall (sp.toNat - 24) = some v9.toNat ∧
     read64 mcall (sp.toNat - 32) = some v18.toNat ∧
     aLOp.toNat % 8 = 0 ∧
     0x80000000 ≤ aLOp.toNat ∧ aLOp.toNat + 16 ≤ 0x100000000 ∧
     tohostAddr + 16 ≤ aLOp.toNat ∧
     (aLOp.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aLOp.toNat) ∧
     subsret.toNat % 8 = 0 ∧
     sp.toNat - 1088 ≤ subsret.toNat ∧ subsret.toNat + 24 ≤ sp.toNat - 32 ∧
     SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
     sp.toNat ≤ 0x100000000 ∧
     0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
     (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
     ((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧
     ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
     (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
     (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
     -- ITEM ZERO B1: the LEFT operand's recursion-sound budget at `sp - 1088`,
     -- its `.fn`-bodies bound, and the store-bodies invariant (the amended
     -- `armTail_rec` pre-tail).
     StackOK SL (sp - 1088#64)
       (l.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
     Expr.bodiesBound Vsa.While.perCallBudget l = true ∧
     Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget)

/-- **The named destructurer: bundle + left IH ⇒ `JalPreBundle er`.**  ONE
`midArmField_of_IH` call: the three fixed-target facts are `decide`d, the jal-site
step is the landed `site_800034f8_ee`, the marshal and the pre come from the bundle.
Every consumer of `MidArmLeftJalBundle` goes through this. -/
theorem jalPreBundle_of_midArmBundle
    (l er : Expr) (c' : Config) (st st' : Vsa.While.St) (d : Nat) (env : Addr)
    (lv : Value)
    (hIH : EvalIH st d env l st' lv)
    (h : MidArmLeftJalBundle l er c' st st' d env lv) :
    LandedN 1 c' (fun c'' => JalPreBundle er c'' st' d env) := by
  obtain ⟨gpre, N, A, SL, φf, φc, sp, rr, sret, subsret, aIn, aLOp, aROp, aExpr, aEnv,
    v8, v9, v18, out0, mcall, hMarshalAll, hpre⟩ := h
  exact midArmField_of_IH gpre N A SL φf φc st st' d env l er lv
    sp rr sret subsret aIn aLOp aROp aExpr aEnv v8 v9 v18 out0 mcall c'
    (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (by decide)
    (fun σ i u vmi hGσ hpcσ hmiσ hcodeσ hiσ =>
      site_800034f8_ee σ i u (0x800034f8#64) vmi hGσ hpcσ hmiσ hcodeσ rfl hiσ)
    hIH hMarshalAll hpre

#print axioms jalPreBundle_of_midArmBundle

/-! ## The per-arm staging residuals + the field closers -/

/-- **The `binaryR` staging residual** (the `BinArmGeomProvider` analogue): from the
arm entry `EEntryC (.binary op l r)` (with the completed left eval known), the
dispatch + arm-head span reaches (≥ 1 step) the LEFT-jal landing bundle.  Strictly
smaller than the `binaryR` field: it stops BEFORE the left recursive call. -/
def BinaryRStagePre (op : BinOp) (l r : Expr) (c : Config) (st st' : Vsa.While.St)
    (d : Nat) (env : Addr) (lv : Value) : Prop :=
  EvalE st d env l st' lv → EEntryC c st d env (.binary op l r) →
  LandedN 1 c (fun c' => MidArmLeftJalBundle l r c' st st' d env lv)

/-- **The `logicalR` staging residual** — identical shape at the `.logical` entry
(the left-jal PC and the mid-arm span are binary/logical-shared). -/
def LogicalRStagePre (lop : Vsa.While.LogOp) (l r : Expr) (c : Config)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (lv : Value) : Prop :=
  EvalE st d env l st' lv → EEntryC c st d env (.logical lop l r) →
  LandedN 1 c (fun c' => MidArmLeftJalBundle l r c' st st' d env lv)

/-- **The (re-typed) `EvalChildStages.binaryR` field, machine-composed.**  Staging
residual ≫ (`armTail_rec` via the IH ≫ `binaryR_midStage1`), by `LandedN.bind`.
The left recursive call and the 7 mid-arm sites are LOAD-BEARING; only the arm-head
staging (`BinaryRStagePre`) remains upstream. -/
theorem binaryR_field_of_stage (op : BinOp) (l r : Expr) (c : Config)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (lv : Value)
    (hstage : BinaryRStagePre op l r c st st' d env lv)
    (hIH : EvalIH st d env l st' lv)
    (hEv : EvalE st d env l st' lv)
    (hEE : EEntryC c st d env (.binary op l r)) :
    LandedN 1 c (fun c' => JalPreBundle r c' st' d env) :=
  LandedN.weakenCount (by omega : 1 ≤ 1 + 1)
    (LandedN.bind (hstage hEv hEE)
      (fun c' hb => jalPreBundle_of_midArmBundle l r c' st st' d env lv hIH hb))

#print axioms binaryR_field_of_stage

/-- **The (re-typed) `EvalChildStages.logicalR` field, machine-composed.**  Same
one-call composition through the SAME mid-arm seam. -/
theorem logicalR_field_of_stage (lop : Vsa.While.LogOp) (l r : Expr) (c : Config)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (lv : Value)
    (hstage : LogicalRStagePre lop l r c st st' d env lv)
    (hIH : EvalIH st d env l st' lv)
    (hEv : EvalE st d env l st' lv)
    (hEE : EEntryC c st d env (.logical lop l r)) :
    LandedN 1 c (fun c' => JalPreBundle r c' st' d env) :=
  LandedN.weakenCount (by omega : 1 ≤ 1 + 1)
    (LandedN.bind (hstage hEv hEE)
      (fun c' hb => jalPreBundle_of_midArmBundle l r c' st st' d env lv hIH hb))

#print axioms logicalR_field_of_stage

end Vsa.Sim
