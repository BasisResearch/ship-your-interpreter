# Wave 44 — armdispatch lane (parametric arm-dispatch combinator)

HEAD at start: 8991fdd.  Lane brief: the ≥3 rule applied to the 12 open
`*ArmDispatch` residuals — design ONE combinator per group, instantiate.

## Landed (all green via `lake env lean`, axioms ⊆ {propext, Classical.choice, Quot.sound})

1. `Vsa/Sim/rows/ArmDispatchCombinator.lean` (~1.2s)
   - `structure EvalArmHeadExtras g N A SL k armPC e ce payOff nodeHi sp sret aExpr aChild m0`
     — the ONE shared Group-A entry-side residual (slot pin, node/child
     survivals, payload read, geometry, `x13_pres` liveness closure =
     `BinArmExtras.x13_pres` generalized over armPC).
   - `theorem evalArmDispatch_of_slot` — parametric over
     `(k, armPC, e, ce, payOff, nodeHi)`: runs the LANDED `blockA_k`
     (`EvalIntSim2`) off the extras and produces the exact
     `Triple (· = c) (arm-head Mid tower)` the eval `*ArmDispatch` defs demand
     (`gpre := reached regs` so the ghost frame is `rfl`; child payload
     transported `m0 → ment` by `read64_agreeP` + `node_stk`).

2. `Vsa/Sim/rows/ArmDispatchCombinatorExec.lean` (~1.2s)
   - `structure ExecArmHeadExtras N A SL φf φc st k armPC ce payOff nodeHi sp aInterp aStmt aChild m0`
     — the ONE shared Group-B residual (StmtSlotPinned pin + `StackDisjoint`
     table geom, payload/child survival, `Eval_exprLoaded`/`Value_intLoaded`/
     `IntSlotPinned` at m0, the WIDE-window StoreRepr survival
     `[SL.lo,(sp-176)+1088)` minus interp hole, `jsp`-form geometry).
   - `theorem execArmDispatch_of_slot` — runs the LANDED `execBlockA`
     (`ExecBrkCont`), transports eval-code/rodata facts across the spills via
     `loaded_eval_expr_agreeP`/`loaded_value_int_agreeP`/pointwise memframe
     rewrites, composes the wide survival, assembles the exec Mid tower.
     No x13 residual on the exec side (the Mids never read a3 post-prologue).

3. `Vsa/Sim/rows/ArmDispatchInstancesEval.lean` (~1.2s)
   - `def EvalArmDispatchResid k armPC e ce payOff nodeHi st d env c` (the ∀-entry
     wrapper of the extras — the new, strictly-smaller frontier).
   - `assignArmDispatch_of_resid` : Resid 5 0x8000347c (.assign x e) e 16 24 → `AssignArmDispatch`
   - `callArmDispatch_of_resid`   : Resid 9 0x800031b0 (.call f args) f 8 16 → `CallArmDispatch`
   - kind reads by one `cases (hE.mem ▸ hE.expr)` per instance; the Mid towers
     are DEFEQ to the combinator's conclusion at the row params (plain `exact`).

4. `Vsa/Sim/rows/ArmDispatchInstancesExec.lean` (~2.3s)
   - `def ExecArmDispatchResid k armPC s ce payOff nodeHi st d env c`
   - `stmtExprArmDispatch_of_resid`      (0, 0x80004170, +8, 16)
   - `stmtRetArmDispatch_of_resid`       (6, 0x80004120, +8, 16)
   - `stmtVarInitArmDispatch_of_resid`   (1, 0x800040d8, +16, 24)
   - `stmtIfCondArmDispatch_of_resid`    (3, 0x800041e8, +8, 16; both if ctors)
   - `stmtWhileCondArmDispatch_of_resid` (4, 0x8000403c, +8, 16)

Discipline gate: `scripts/check_discipline.py` OK (files split so no file
exceeds the ∃-count rule; heartbeats at the blockA-family standing 8000000).

## Coverage: 7 of the 12 discharged

NOT dischargeable by any slot combinator (recorded in observations.md
`armdispatch-class-split`): `FlCondArmDispatch`, `FlBodyArmDispatch`,
`WhileBodyArmDispatch`, `ForInitArmDispatch`, `ArgsHeadDispatch` — their
entries are `FEntryC`/`AEntryC` = `InductionScaffold.SegEntry` ∃-packs at a
GHOST interior `entryPC` (no node address / arg-reg ABI / StmtRepr), so there
is no jump-table run to consume.  That is the standing SegEntry-opacity gap
(different missing abstraction; model for the fix = the wave-43 `*ArmHeadInv`
named entries).

## Wiring (NOT applied — Vsa.lean not owned this wave)

```
import Vsa.Sim.rows.ArmDispatchCombinator
import Vsa.Sim.rows.ArmDispatchCombinatorExec
import Vsa.Sim.rows.ArmDispatchInstancesEval
import Vsa.Sim.rows.ArmDispatchInstancesExec
```
(place after the `rows/Stmt*ArmStagePre` imports, ~line 600).  check_all axiom
list candidates: `evalArmDispatch_of_slot`, `execArmDispatch_of_slot`,
`assignArmDispatch_of_resid`, `callArmDispatch_of_resid`,
`stmtExprArmDispatch_of_resid`, `stmtRetArmDispatch_of_resid`,
`stmtVarInitArmDispatch_of_resid`, `stmtIfCondArmDispatch_of_resid`,
`stmtWhileCondArmDispatch_of_resid`.

## Notes / gotchas hit

- The `*ArmDispatch` Mid towers are α/defeq-identical across arms modulo
  `(armPC, payOff, nodeHi, child expr)` — writing the combinator's conclusion
  as the literal parametric tower makes every instance a plain `exact`.
- `ArmEntryK`/`ExecArmEntryK` are consumed by ONE flat positional `obtain`
  copied verbatim from the landed `BinArmBridge`/`execBlockD` patterns (safe:
  field order is frozen by those green files).
- `hAout.symm ▸ hArm` realigns the `out0` ghost to the reached config's
  `sailOutput` (both blockA layers take `out0 := entry sailOutput`).
- Group-A x13: kept the `BinArmExtras.x13_pres` closure shape, parametric in
  armPC (see observations `blockA_k-x13-loss-now-parametric`).
