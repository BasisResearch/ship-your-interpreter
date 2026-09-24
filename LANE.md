# Lane E4: the call family (closure call, natives, call errors)

Branch `lane-e4` (from `wave4-base`). Design: `VsaIris/INTERP_DESIGN.md` §4,
§6, §8 (row "call"). Rows: `scripts/iris_arms/arms.d/e4-call.tsv`.

## Interface for lane E6: the argument loop (`VsaIris/Interp/ArgsLoop.lean`)

The call arm needs `EvalArgs` as a loop lemma. Its statement is in
`ArgsLoop.lean` (statement only, no proof): E4 takes it as a hypothesis, E6
proves it. Please keep the statement (or tell me what has to change):

- `argsLoopT_body … st d env args st' vs n D` (total, the motive of
  `EvalArgsCost`) and `argsLoopP_body … Core d env args` (partial, structural
  over `args`, additive return/abort pair).
- Start: `ms 0x800031d8 R (evalS s) Mt` (the `blez a5`), registers
  `ArgsHead` (`sp = s-1088`, `s0` = call node, `s2 = in`, `a3 = env`,
  `a5 = argc`, `a6 = 0`), node facts `CallNode` (tag, callee, array pointer,
  count, `ExprArrayReprWithin`, view `callView`), stack
  `stackScratch (s-1088) m'` covering every argument's `evalNeed`.
- End: `ms 0x80003254 R' (evalS s) Mt'` with `ArgsExit` (callee-saved kept,
  `a5 = argc`, frame unchanged outside `ArgsScratch` = `sp+0..32`,
  `sp+64..88`, `sp+240..240+24·argc`) and `valsImg N (imgM Mt') (sp+240) vs`
  (each argument's words, persistent).

## Done
- `ArgsLoop.lean`: the argument-loop statement (above).

## In flight
- The shared call prefix (callee child, argc test, loop, kind dispatch) and
  the native arms (`jalr a6` call rule).

## Holes
None added.
