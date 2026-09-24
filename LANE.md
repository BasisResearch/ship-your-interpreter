# Lane E6: the shared loop lemmas

Branch `lane-e6` (from `wave4-base`). Design: `VsaIris/INTERP_DESIGN.md` §4.3,
§8 ("loop lemmas"). Family: `while` (4 outcomes), `for` (`ForLoop` 4,
`ForCond` 2, `ExecStep` 2, `ExecInit` 2), `EvalArgs` (the call argument
loop), both modes. `seqLoop` (all three sites, both modes) was landed by lane
G (`Interp/SeqLoop*.lean`) and is reused as is.

## Statements (landed: `VsaIris/Interp/SpecLoop.lean`) — for E4 and E5

Every loop is stated at its loop HEAD inside the enclosing frame, in the
continuation form of G's `blockSeqT_body` (no `F` parameter: the continuation
wand captures the arm's frame).

| motive | head PC | exit | consumer |
|---|---|---|---|
| `whileT_body st d env c b st' status n` | `0x8000403c` | `loopExit status` | E5 while arm (total) |
| `whileP_body Core d env c b` | `0x8000403c` | `loopExit status` / abort | E5 while arm (partial) |
| `execInitT_body st d outer init st' n` | `0x8000423c` (after `env_new`, scope in `a0`) | `0x8000426c`, scope in `s3` | E5 for arm |
| `execInitP_body Core d outer init` | same | same / abort | E5 for arm |
| `forLoopT_body st d env cnd step b st' status n` | `0x8000426c` | `loopExit status` | E5 for arm |
| `forLoopP_body Core d env cnd step b` | same | same / abort | E5 for arm |
| `forCondT_body`, `execStepT_body` | `0x8000426c` → `0x800042a8`; `0x80004264` → `0x8000426c` | | A's recursor (ForCond/ExecStep motives) |
| `evalArgsT_body st d env es st' vs n` | `0x800031dc` (nonempty suffix) | `0x80003254` | E4 call arm |
| `evalArgsP_body Core d env es` | same | same / abort (`ms_callEvalP`'s shape) | E4 call arm |

- Exits: `loopExit (.ret v) = 0x80004150` (the `ret` epilogue), otherwise
  `0x8000409c` with `a0 = 0` (`R' 10 = statusCode status` in both).
- Frame: the loops write only the scratch words `execW s = [sp+16, sp+128)`
  (`argsW s` for the argument loop); every other byte of the frame is
  `Untouched`, which is how the arm's epilogue finds its saved registers.
- Registers at the head: `StmtHead` (`sp = s-176`, `s0` node, `s1` in, `s2`
  ret slot, `s3` frame), `InitHead` (`a0` the new scope), `ArgsHead`
  (`sp = s-1088`, `s0` node, `s2` in, `a3` env, `a6` index, `a5` count).
- Stack: `WhileFits`/`ForFits` (named fields: each present child fits in the
  lowered stack `m'` and bounds its bodies).
- Arguments: `argVals N img (argsBase s) 0 vs` (persistent: `vs[j]` in the
  three words at `sp+240+24j`).
- Total mode: the motives are D-free predicates of the cost relation's
  indices. A's recursor uses, for `ExecSCost`,
  `execSpecT_body D ∧ ∀ c b, sm = .whileStmt c b → whileT_body …`; for
  `ForLoopCost`/`ForCondCost`/`ExecStepCost`/`ExecInitCost`/`EvalArgsCost`
  the motive itself. Case lemmas (one per constructor) take the children's
  `evalSpecT_body`/`execSpecT_body` and the recursive premise's motive.
- Partial mode: `whileP_all`, `forLoopP_all` (Löb; the back edge's
  `jal eval_expr` pays the later), `execInitP_all`, `evalArgsP_all`
  (structure) — theorems, no hypothesis for the consumer to discharge beyond
  `evalSpecsP`/`execSpecsP`.

## Generator
The loops are block lemmas at a loop head, not arms from a function entry
(G's row format requires a run from the entry and a final `ret`), so
`scripts/iris_arms/arms.d/e6-loops.tsv` has no rows. Like G's `seqLoop`, they
are `#ix_seg` runs plus `#ix_piece` glue.

## In flight
- Proofs: `Interp/LoopWhile.lean`, `Interp/LoopFor.lean`, `Interp/LoopArgs.lean`.

## Holes
None added.
