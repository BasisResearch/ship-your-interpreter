# Wave 41 — argsHead: the last eval-child staging field

Task (plan queue item 3): supply the `argsHead` stage-pre for `EvalChildStages`
(`AEntryC c st d env (e :: es) → LandedN 1 c (fun c' => JalPreBundle e c' st d env)`),
consuming `CallArgLoopInv` (rows/CallClosureSplice.lean); reuse the generated
arg-loop-entry seg by name.

## Grounding (before any edit)

- `argsHead` field type (ArmSegSplitEval.lean:561): `AEntryC c st d env (e :: es) →
  LandedN 1 c (fun c' => JalPreBundle e c' st d env)`. NOTE: unlike the exec-eval
  fields (which land at `EEntryC` directly), argsHead lands at `JalPreBundle` — the
  `argsHead_split` combinator (ArmSegSplitEval.lean:495) marshals it to `EEntryC`.
- `AEntryC c st d env (e::es)` (ApproxArmReseat.lean:122) = `∃ ghosts argLoopPC m0,
  SegEntry g N A SL φf φc st d dLeft aLeft argLoopPC m0 c`. For the arg loop,
  `argLoopPC = evalArgsLoopPC = 0x800031dc` (CallEntry.lean:215, EvalArgs.lean:11).
- The head arg `e` is evaluated by `jal eval_expr @0x80003220`. The loop body is the
  straight-line span `0x800031dc → 0x8000321c` (16 instrs of index arithmetic + 4
  spills) THEN `jal @0x80003220`.
- `CallArgLoopInv N A SL φf φc stK vsPre n sp cnode ip envp m0 c` (CallClosureSplice.lean:79)
  sits AT `evalArgsLoopPC = 0x800031dc` with pins a6=index(vsPre.length), a5=argc(n),
  s0=call node(cnode, args array at 16(s0)), s2=interp(ip), a3=env(envp), the evaluated
  prefix `vsPre` in slots `sp+240+24·i`, memFrame, `vsPre.length ≤ n`. For the FRESH
  head arg: `vsPre = []`, `n = (e::es).length ≥ 1`.
- `CallArgLoopInv` has NO consumers yet (grep confirms) — I am the first. wave38
  explicitly deferred argsHead to consume it once it exposes a JalPreBundle cut.
- All 18 body/jal decode lemmas exist (checked Batch*).
- Mandatory abstraction for the body span: `#derive_case` seg + `bridgeOfSeg`
  (BridgeSeg.lean) — the "straight-line body ≫ jal" combinator (its literal purpose).
  A bespoke `site_*` battery would be a discipline violation (16 hand sites).

## Honest split (mirrors wave-37 callF: dispatch residual + landed staging span)

1. `ArgsHeadDispatch` — named residual: `AEntryC (e::es) → CallArgLoopInv (vsPre=[]) c`.
   The bare `SegEntry` (from AEntryC) lacks the arg-loop pins (a6/a5/s0/s2/a3, the
   arg-array node); this is the analog of `CallArmDispatch`. GENUINE gap (SegEntry
   is pin-agnostic).
2. `ArgsHeadStagePre` — the staging span consuming `CallArgLoopInv (vsPre=[])`:
   run body `0x800031dc→0x8000321c` (#derive_case seg) ≫ `jal @0x80003220`
   (bridgeOfSeg) → `JalPreBundle e`.
3. `argsHead_field_of_dispatch` — composes 1+2 → the field.

## Status log

### LANDING 1 (green + axiom-clean) — the body seg + bridge
- `argsHeadBodySeg` (#derive_case, 16 instrs 0x800031dc→0x8000321c) DERIVES.
- `argsHeadBodyBridge` (bridgeOfSeg): body run ≫ jal eval_expr @0x80003220
  (target 0x80003164, link 0x80003224) → parked at eval_expr entry, GHolds out.regs,
  writeLog m0 out.log, ABI frame. AXIOM-CLEAN {propext, Classical.choice, Quot.sound}.
- Modelled exactly on GEN loopHeadArgSetupBridge. hjalSeam + hfacts named residuals.
- Pin list L = [(2,sp),(8,s0),(16,a6),(15,a5),(18,s2),(13,a3)] (regs body reads).

### LANDING 2 (green + axiom-clean) — the composition layer
- `ArgsLoopHeadInv` — config predicate = CallArgLoopInv (vsPre=[], n=(e::es).length) +
  ExprRepr of head-arg node. FIRST consumer of the crux's CallArgLoopInv.
- `ArgsHeadStagePre` (∀ c') — named staging residual: loop-head bundle → JalPreBundle e.
- `ArgsHeadDispatch` — named dispatch residual: AEntryC (e::es) → LandedN 0 to bundle +
  the stagePre. Analog of CallArmDispatch.
- `argsHead_field_of_dispatch` — composes both into the EvalChildStages.argsHead field
  type `AEntryC (e::es) → LandedN 1 (JalPreBundle e)`. AXIOM-CLEAN.
- Two honest named residuals remain: ArgsHeadDispatch (upstream, AEntryC→bundle, incl.
  the head-node ExprRepr the crux inv lacks) + ArgsHeadStagePre (the JalPreBundle
  marshalling from argsHeadBodyBridge's GHolds/writeLog output).

### NEXT: attempt to discharge ArgsHeadStagePre (the real CallArgLoopInv consumption).

### FINAL STATE (green + axiom-clean + discipline OK)
File `Vsa/Sim/rows/ArgsHeadArmStagePre.lean` — 3 landed items:
1. `argsHeadBodySeg` (#derive_case) + `argsHeadBodyBridge` (bridgeOfSeg) — the whole
   16-instr arg-loop body run ≫ jal eval_expr, PROVED (one ChainOK decide). The
   exponentiating win: 16 hand site_* lemmas → one seg + one bridge.
2. `ArgsLoopHeadInv` / `ArgsHeadStagePre` / `ArgsHeadDispatch` — the honest residuals.
3. `argsHead_field_of_dispatch` — the EvalChildStages.argsHead field composer.
- Discipline: OK (no site-battery exemptions — used the mandated #derive_case/bridgeOfSeg).
- FIRST consumer of the crux's CallArgLoopInv (as mandated).

### EvalChildStages closure status
argsHead is now FIELD-COMPOSED (9/14 eval-child). EvalChildStages is NOT fully
closed: the 5 remaining exec-eval fields (stmtRet/stmtVarInit/stmtIfCond/
stmtWhileCond/flCond) are owned by other lanes. So `evalChildStages_mk` cannot yet
be fully supplied. When those 5 land, argsHead plugs in via the wiring below.

### WIRING (return-only; other lanes own these files)
- Vsa.lean: `import Vsa.Sim.rows.ArgsHeadArmStagePre` (after ArmSegSplitEval +
  rows.CallClosureSplice, both already imported).
- scripts/check_all.sh THEOREMS: add
    Vsa.Sim.argsHeadBodyBridge                        # rows/ArgsHeadArmStagePre (arg-loop body ≫ jal eval_expr via bridgeOfSeg)
    Vsa.Sim.argsHead_field_of_dispatch                # rows/ArgsHeadArmStagePre (argsHead FIELD-COMPOSED — 9/14 eval-child)
- ArmStagesWave34.lean (other lane): a new `evalChildStages_ublracSEA_wired` swapping
  the `argsHead ∀`-premise for the strictly-smaller `ArgsHeadDispatch` residual, wiring
  `fun e es c st d env hAE => argsHead_field_of_dispatch e es c st d env (hArgsDisp e es c st d env) hAE`
  — exactly the wave40 stmtExpr pattern. (5 exec-eval fields must land first for the
  full builder; until then argsHead can be threaded into evalChildStages_mk directly.)
