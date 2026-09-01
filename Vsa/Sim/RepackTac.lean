import Vsa.Sim.SegToTripleFramed

/-!
# `repack` — the field-matching bundle→bundle marshaller

The repo's R6/R7 discipline states every post/entry as a named-field
`structure … : Prop where` bundle (`FoundSt`/`GeomFacts`/`FramedSegPost`/
`WInv`/…).  A recurring, purely mechanical proof shape is converting ONE such
bundle into ANOTHER whose fields are a subset / reordering / defeq-rewrite of
the source's (framed seg post → next block's carrier, `WInv` → `WAtBne`-style
join hops, crux-marshal rows, StagePre → JalPreBundle).  Hand-written
`{ field := h.field, … }` records break on every reorder and bury the genuine
content among the transported fields; this file lands the marshalling ONCE.

```
repack h₁, h₂, …
```

* whnfs the goal (default transparency, so `abbrev`-wrapped and parameterized
  bundles reduce) to a structure application and builds its constructor with
  one metavariable per field;
* for each field, scans the given hypotheses — each must itself whnf to a
  named-field structure application — trying first the WHOLE hypothesis, then
  each of its projections `h.f`, in declaration order, and assigns the FIRST
  candidate whose type is defeq to the field's type (ambiguity between defeq
  candidates is harmless: they prove the same Prop);
* leaves every unmatched field as a fresh goal TAGGED with the field name, so
  the genuine content is closed as `case kle => …` bullets;
* FAILS LOUDLY (`throwError`) if ≥1 hypothesis was given and ZERO fields
  matched — never a silent no-op (the `chain-facts-no-op-after-have` lesson,
  observations.md 2026-09-01).

With no hypotheses, `repack` just splits the bundle into one tagged goal per
field (a named `constructor`).

Scope: non-dependent Prop bundles — every bundle in this repo.  ∃-typed and
arrow-typed fields are ordinary terms and marshal fine; fields whose TYPE
mentions an earlier field's value would let defeq matching assign the earlier
metavariable as a side effect (no such bundle exists here).  Goal structures
must be flat (no `extends`) — again all of them.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Verify with `lake env lean Vsa/Sim/RepackTac.lean`.
-/

open Lean Elab Tactic Meta
open LeanRV64DExecutable Vsa Register
open Vsa.Machine (MState Config Steps)

namespace Vsa.Sim

/-- whnf `ty` and return `(structName, levels, whnf'd type)` if it is an
application of a structure type. -/
private def rpStructApp? (ty : Expr) : MetaM (Option (Name × List Level × Expr)) := do
  let tyW ← whnf ty
  let .const nm us := tyW.getAppFn | return none
  unless isStructure (← getEnv) nm do return none
  return some (nm, us, tyW)

/-- `repack h₁, h₂, …` — build the goal bundle field-by-field from the given
bundle hypotheses, matching field TYPES up to defeq; unmatched fields become
goals tagged with the field name; errors if nothing matched. -/
elab "repack" hs:term,* : tactic => do
  let g ← getMainGoal
  g.withContext do
    let env ← getEnv
    let ty ← instantiateMVars (← g.getType)
    let some (sName, us, tyW) ← rpStructApp? ty
      | throwError "repack: goal{indentExpr ty}\nis not a named-field structure application"
    -- Candidate terms: each hypothesis itself, then its projections, in order.
    let mut cands : Array (Expr × Expr) := #[]
    let mut nHyps := 0
    for hStx in hs.getElems do
      let h ← Tactic.elabTerm hStx none
      let h ← instantiateMVars h
      nHyps := nHyps + 1
      let hTy ← instantiateMVars (← inferType h)
      let some (hName, _, hTyW) ← rpStructApp? hTy
        | throwError "repack: hypothesis {hStx} :{indentExpr hTy}\nis not a named-field structure application"
      cands := cands.push (h, hTyW)
      for f in getStructureFieldsFlattened env hName (includeSubobjectFields := false) do
        let proj ← mkProjection h f
        cands := cands.push (proj, ← inferType proj)
    -- Constructor application with one synthetic-opaque mvar per field,
    -- tagged with the field name (the `case <field>` handle).
    let ctor := getStructureCtor env sName
    let mut e := mkAppN (mkConst ctor.name us) tyW.getAppArgs
    let mut ctorTy ← inferType e
    let mut fieldMVars : Array (Name × Expr) := #[]
    for f in getStructureFields env sName do
      let ctorTyW ← whnf ctorTy
      let .forallE _ dom body _ := ctorTyW
        | throwError "repack: constructor arity mismatch at field '{f}' of {sName}"
      let mv ← mkFreshExprSyntheticOpaqueMVar dom (tag := f)
      fieldMVars := fieldMVars.push (f, mv)
      e := mkApp e mv
      ctorTy := body.instantiate1 mv
    -- Match every field against the candidates; first defeq candidate wins.
    let mut filled := 0
    for (_, mv) in fieldMVars do
      let mvId := mv.mvarId!
      unless ← mvId.isAssigned do
        let mvTy ← instantiateMVars (← mvId.getType)
        for (cand, candTy) in cands do
          unless ← mvId.isAssigned do
            -- probe without polluting the mctx on failure, then commit
            if ← withoutModifyingState (isDefEq mvTy candTy) then
              discard <| isDefEq mvTy candTy
              mvId.assign cand
              filled := filled + 1
    if filled == 0 && nHyps > 0 then
      throwError "repack: matched ZERO fields of {sName} against the given {nHyps} hypothesis(es) — wrong bundle, wrong instantiation, or the fields genuinely differ (goal{indentExpr tyW})"
    g.assign e
    let mut leftovers : List MVarId := []
    for (_, mv) in fieldMVars do
      unless ← mv.mvarId!.isAssigned do
        leftovers := leftovers ++ [mv.mvarId!]
    replaceMainGoal leftovers

/-! ## Demo A — synthetic superset → subset with reordered, renamed fields

Field names deliberately DIFFER between source and target (matching is by
TYPE); the target is `abbrev`-wrapped; one field is ∃-typed.  ONE `repack h`
closes everything. -/

structure RepackBigDemo (n : Nat) : Prop where
  lower : 1 ≤ n
  upper : n ≤ 10
  ne5 : n ≠ 5
  wit : ∃ m, m + m = n + n

structure RepackSmallDemo (n : Nat) : Prop where
  w : ∃ m, m + m = n + n
  ne : n ≠ 5
  lo : 1 ≤ n

abbrev RepackSmallDemo' (n : Nat) : Prop := RepackSmallDemo n

theorem repackDemoA (n : Nat) (h : RepackBigDemo n) : RepackSmallDemo' n := by
  repack h

/-! ## Demo B — `FramedSegPost` → a smaller reordered carrier

The exact live shape: a gen_fn block's framed post handed to the next stage as
a thinner bundle (outcome fields only, keep/tick/pw/th dropped, order
scrambled).  ONE `repack h`. -/

structure RepackSegOutcome (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (outp : Array String) (c : Vsa.Machine.Config) : Prop where
  pc : c.σ.regs.get? Register.PC
    = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs)
  good : GoodState c.σ
  out : c.σ.sailOutput = outp
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  mem : c.σ.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log

theorem repackDemoB (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (keep : GRegs) (outp : Array String) (pwv : BitVec 4) (c : Vsa.Machine.Config)
    (h : FramedSegPost bs L lds pc0 m0 keep outp pwv c) :
    RepackSegOutcome bs L lds pc0 m0 outp c := by
  repack h

/-! ## Demo C — the leftover-goals contract (`WInv` → `WAtBne` style)

Two target fields (`kle`, `klt20`) are light REWRITES of the source's `klt`
(not defeq), so `repack h` transports the matchable fields and leaves exactly
those two as `case`-tagged goals — the genuine content, closed manually. -/

structure RepackWInvDemo (n : Nat) (c : Vsa.Machine.Config) : Prop where
  klt : n < 10
  pc : c.σ.regs.get? Register.PC = some 0x8000004c#64
  out : c.σ.sailOutput = #[]

structure RepackWAtBneDemo (n : Nat) (c : Vsa.Machine.Config) : Prop where
  kle : n ≤ 10
  pc : c.σ.regs.get? Register.PC = some 0x8000004c#64
  klt20 : n < 20
  out : c.σ.sailOutput = #[]

theorem repackDemoC (n : Nat) (c : Vsa.Machine.Config) (h : RepackWInvDemo n c) :
    RepackWAtBneDemo n c := by
  repack h
  case kle => exact Nat.le_of_lt h.klt
  case klt20 => exact Nat.lt_of_lt_of_le h.klt (by decide)

/-! ## Loud-failure contract — zero matches is an ERROR, never a silent no-op -/

/-- A bundle sharing NOTHING with `RepackSmallDemo`. -/
structure RepackDisjointDemo (n : Nat) : Prop where
  big : 100 ≤ n

/--
error: repack: matched ZERO fields of Vsa.Sim.RepackSmallDemo against the given 1 hypothesis(es) — wrong bundle, wrong instantiation, or the fields genuinely differ (goal
  RepackSmallDemo n)
-/
#guard_msgs in
example (n : Nat) (h : RepackDisjointDemo n) : RepackSmallDemo n := by
  repack h

#print axioms repackDemoA
#print axioms repackDemoB
#print axioms repackDemoC

end Vsa.Sim
