# Store-size refactor completion

Completed the incomplete uncommitted refactor that threads store-size ghosts
(`nf nc` = `st.store.frames.size` / `st.store.closures.size`) through the M4
`Eval*`/`Exec*` simulation stack, replacing the former `hSizeF`/`hSizeC`
equality-assumption rebases with `PhiExtends.mono` collapses backed by the
per-relation store-monotonicity lemmas (`evalE_store_mono` etc.) in
`Vsa/While/Cost.lean`.

## Result

- Full tree green: **1120 jobs, `Build completed successfully`**.
- `bash scripts/check_all.sh --skip-build`: **OK, 309/309 audited theorems
  axiom-clean** ⊆ {propext, Classical.choice, Quot.sound}; stage-b scanned 999
  files (no sorry/native_decide/axiom).
- No file was reverted; all 32 pre-modified files kept.

## The established pattern (from the already-updated callsites)

`EvalExit`/`ExecExit`/`SegExit` and the `Sub*Return`/`TwoSubReturn` structures
gained `(nf nc : Nat)` parameters. At a **pack/produce** site the caller passes
`st.store.frames.size st.store.closures.size` (the ROW-entry state). At a
**leaf** (`st' = st`) the same. The former `hSizeF ▸ hpfm` two-phase rebase is
replaced by:

```
have hmono := evalE_store_mono _hEvalE      -- StoreLe st.store st''.store
have hleF' := hSizeF ▸ hmono.1              -- st.store.fs ≤ st'.store.fs
have hpfF := hpfm.trans (PhiExtends.mono hleF' hpfe)
… evalExit_of_phiExtends hpfF hpcF hExitE hmono.1 hmono.2
… hpfF.trans (PhiExtends.mono hmono.1 hpf')
```

`evalExit_of_phiExtends` now takes the two `≤` monotonicity args; `EvalExitD`/
`TwoSubReturn`'s inner φ-chain was re-based from `st''`-sized to `st'`-sized.

## Files fixed (consumers the refactor never updated)

Mechanical `nf nc` propagation, smallest pattern-conformant edit:

**Named in the brief:**
- `EvalBoolSim.lean`, `EvalStrSim.lean` — leaf goal `EvalExit … st.store.*.size`.
- `ExecRetNull.lean` — `SubExecReturnR`/`ExecExit` goal `st.store.*.size`; also
  propagated `nf nc` into `SubStmtReturn` (def + `armExec_rec` target) in
  `ExecBlock.lean`, which the refactor left at `st'`-sized.

**Row family (Gt/Lt/Le/Add/Sub/Mul/Div/Mod/Ge/EqNe) — `Vsa/Sim/rows/*`:**
Each `blockC_*` got `(nf nc)` params; input `TwoSubReturn`/output φ-chain
re-based (`nf`, then `st'`-sized inner legs); the sim's `EvalGtSimGoal`-style
goal + `hResid` `TwoSubReturn` + tail rewritten with `evalE_store_mono` +
`PhiExtends.mono`. Gt/Lt/Le/Add/Sub/Ge inline their tail; Mul/Div/Mod go through
the shared `intBoxEpilogue`; EqNe through `boolBoxEpilogue`.

**Shared epilogue combinators — generalized to 4 free size params
`(nf nc nf2 nc2)`** so both the `TwoSubReturn`-based rows (Mul/Div/Mod, first leg
`st.store`, second `st'`) and the `EqResid`-based EqNe (first leg `st'`, second
`st''`) can instantiate them:
- `Vsa/Sim/rows/IntPostEpilogue.lean` (`intPostToEpilogue`),
- `Vsa/Sim/BinopTailGen.lean` (`intBoxEpilogue`),
- `Vsa/Sim/BoolBoxEpilogue.lean` (`boolBoxEpilogue`).

**EqNe subsystem** (`rows/EvalEqNeRow.lean`, `rows/EvalEqNeFront.lean`,
`EqNeDispatchInput.lean`): `blockC_eqne`/`blockC_eq`/`blockC_ne` kept their
`EqResid`-driven `st'/st''` store chain (they do NOT consume `TwoSubReturn`'s
chain) — only the `boolBoxEpilogue` sizes were supplied explicitly; the top-level
`evalEqNeSim`/`evalEqSim`/`evalNeSim`/`evalEqSimD`/`evalNeSimD` gained an
`_hEvalE` hypothesis so the `st.store`-sized goal is reached via
`evalE_store_mono`; `evalEqNeChain_dispatch_of_twoSubReturn`/`eqBlockC_bridge`
got `nf nc` threaded (they ignore the φ facts).

**Logical two-eval cases** (`EvalLogical4.lean` — `blockC_orFalse` / `orFalse`):
the refactor had already added `blockC_orFalse`'s `(nf nc)` params and the
`hnf : nf ≤ st'.store.*.size` hypothesis but not USED it; completed the tail to
collapse via `hnf` + `PhiExtends.mono`, fixed the `hφagree'` (st''-sized) mixup,
and supplied `hnf` (from `evalE_store_mono _hEvalE` + `hSizeF/hSizeC`) at the
`evalOrFalseSim` callsite. (`EvalLogical3`/andTrue compiled unchanged.)

**Leaf hub** (`EvalLeafD.lean`): `LeafWiden`/`evalExitD_of_evalExit` + five `*D`
leaves threaded `st'.store.*.size` (= `st.store` for leaves).

**Scaffold / recursor-plug** (`TermSimAssembly.lean` motives, `ExecDispatch.lean`
`ExecDispatchIH`, `LoopScaffoldClose.lean` `segIdentity_of_eq`, `CallEntry.lean`
`EvalArgsExit`/`CallExitP` abbrevs + `evalArgsNil`, `EvalCallNative.lean`,
`EvalCallPrint.lean`, `EvalCall.lean`): entry(`st`)-sized `SegExit`/`ExecExit`/
`EvalExit`. The `CallExitP`/`EvalArgsExit` abbrevs and `segExit_extend` gained
`nf nc` params.

**Loop recursions** (`EvalArgs.lean`, `ExecIf2.lean`, `ExecWhile.lean`,
`ExecWhile2.lean`, `ExecFor.lean`, `ExecForStart.lean`, `rows/LoopSteps.lean`):
sized the goal by the ENTRY `st.store` to match the recursor motives
(`InductionScaffold.motive_*` are entry-sized). The loop-back inductions needed a
size-LOWERING (`stMid`/`stFin` down to `st`), so:
- `segExit_extend`/`execExit_extend` generalized to `(nf nc nf' nc')` + an
  `hle : nf ≤ nf' ∧ nc ≤ nc'` mono arg (mirrors `evalExit_of_phiExtends`);
- `execWhileLoopSim`/`execForLoopSim` gained `hSizeMid`/`hSizeFin` (`st ≤ st''`,
  `st ≤ st'''`) params, supplied by their callers `execWhileSim`/`execForLoopBody`
  from the inverted `whileLoop`/`ForLoop.loop` sub-derivations via store-mono;
- `EvalArgs`'s `evalArgsLoop` cons case weakens `hstep`'s `st'`-sized φ and lowers
  the `stMid`-sized tail exit, both to `st.store` size.

## New Cost.lean lemmas (pure additions, no statement changes)

To support the loop-back size-lowering, added — mirroring the refactor's own
`evalArgs_store_mono` — `forCond_store_mono`, `execStep_store_mono`,
`forLoop_store_mono` (`ForLoop.loop` composes cond ≫ body ≫ step ≫ tail).
`EvalArgs.lean` gained `import Vsa.While.Cost` (was not in its closure; no cycle —
Cost imports no `Sim`).

## Non-mechanical findings

None that block. Two design decisions the refactor forced but had not resolved,
both discharged from available data (not invented):

1. **EqNe / logical / loop rows lacked `_hEvalE`.** The `st.store`-sized goal is
   not reachable from `hSizeF/hSizeC` alone (equality of `st'`/`st''` sizes does
   not give `st.store ≤ st''.store`). Added the `EvalE …`/`ExecS …` hypothesis
   (present for every recursor case) and used `evalE_store_mono`/`execS_store_mono`
   — the same tool the refactor introduced. The GT-family rows already carried
   `_hEvalE`, so this is consistent.

2. **`execWhileLoopSim`/`execForLoopSim` cannot derive `st ≤ st''` (one-iteration
   growth) from their own hypotheses** (`_hExec` jumps entry→final). Threaded the
   needed `≤` facts as explicit parameters, supplied by the dispatch caller which
   HAS the constructor sub-derivations after `cases`. No semantics invented.

## Timing

Isolated `lake env lean` (baseline is loaded time; isolated ≈ baseline/3):
- `rows/EvalGtRow` 35s (baseline 174 → ≈58s expected) — faster, no regression.
- `rows/EvalMulRow` 9s (≈13s expected) — under.
- **`EvalLogical4` 64s (baseline 109 → ≈36s expected) — ~78% over.** Notable
  regression; the file was already heavy (`maxHeartbeats 8000000`) and the added
  `evalE_store_mono` + `PhiExtends.mono` term in the two-eval tail elaborates
  slowly. Not blocking (the 120s per-file budget is waived for already-heavy
  files) but worth a follow-up golf if the two-eval tail is revisited.
