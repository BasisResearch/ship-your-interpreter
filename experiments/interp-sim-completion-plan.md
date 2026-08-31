# InterpSim completion plan (2026-08-31)

`InterpSimFinal.interpSimClosed_of_families L hterm htri hdivFam herrFam :
InterpSim L` is a complete theorem; completion = discharging the four bundles.
The metaprogram layer (chain_facts, #derive_error_site, segToTriple,
loopFromBody, callSeg) and the row/reduction layer are both built: every bundle
is reduced to named typed residuals, none unscoped. check_all: OK, 400/400
axiom-audited. History lives in git (waves `7813980`..`34dbd7e`), the memory
file `interpsim-completion-campaign.md`, and the per-front ledgers in
`experiments/`.

## Where the four bundles stand

- **herrFam** — CLOSED (`errFamilyClosed`).
- **htri** — rests on `StmtDispatchD` + `hroot`
  (`trichotomy_of_stmtDispatchD`, `Vsa/While/Trichotomy.lean` §5). The
  within-statement-divergence spec bug is fixed (`SApprox` family +
  `Approx.head`; demo `loopP_diverges`).
- **hdivFam** — `DivCorrFamily`: supplied by the same forward-sim Triples as
  hterm (progress-only skeleton), nothing independent to build.
- **hterm** — ~26/50 recursor premises have slot-verified rows; the rest of the
  work is discharging the rows' named residuals plus the un-rowed ExecS
  dispatch/loop family, then the table assembly.

## Discharge queue

Ordered by leverage and dependency; each item is scoped with reuse identified
(details in the session task board and ledgers).

1. **env_define bridges** (6 of 9 remain: bridgeStore via a FrameRepr-append
   core lemma; namesToVals/appendHead via a GrowEnvEntry struct-pin seam;
   hUpdate + dispatch scan via the env_get scan shape; memcpy word-route framed
   epilogue). Unblocks hAssign, hSVarInit/hSVarNull/hSBlock, and the
   Call.closure env-fold.
2. **ExecS dispatch/loop arms** (if/while/for/block/seq) — the largest un-rowed
   family; `execBlockA`/`execBlockD` + the loop shapes exist, each arm is a
   chain instance.
3. **Call residuals** — native print char-loop body, `CallArmSpec`/`FnArmSpec`
   (unblocked by `blockD_v_phic`), retNull glue assembly, `ArgsNilHop`,
   `ArgsBodyOracle`.
4. **hBinary str cells** — str-cmp arm chain (sign tails + callees landed;
   `StrCmpOrderBridge` = String.lt ↔ strcmp sign is the one spec-layer gap) and
   the stringify/concat path (biggest single new development; `stringify` has
   no spec).
5. **hVar last layer** — `VarPostRepack` + `EnvGetCallerGeom` discharge at the
   arm (marshalling + framed post landed).
6. **Entry seams** — `StoreInitSeam` (env_new startup decode) +
   `EpilogueFrame` (`restoreRetChain_run` reuse); closes hEntryHalts.
7. **hCallClosure** — after (1): arity + depth guard + env_new +
   env_define-fold + body-ExecSeq at d+1, all callSeg seams.
8. **StmtDispatchD + hroot** — classical totality induction over the Stmt/Expr
   mutual family (runs ∨ errors ∨ SApprox-∀); closes htri.
9. **Assembly + M6** — unify residuals into `TermShared`/`TermCallees`/
   `TermGuards`, fill the `@EvalE.rec` table, `termSimClosed`, hdivFam from the
   same Triples, Layout bundling into `Vsa.Refine.refinement`, final axiom
   audit, end-to-end theorem into check_all.

Non-blocking exponentiation refactors, do opportunistically: strlen byte-tail
on block-reflection; AbiFrameKit hoist; re-seat `interpContSeg_of` on
`restoreRetChain_run`; generic-`w` cmp fixup bridges; generator for the
thrice-duplicated 42-premise error-site list.

## Execution notes

- Coordinator owns `Vsa.lean` + `scripts/check_all.sh`; agents return wiring
  lines. Run `scripts/abs_inventory.sh` before every dispatch; reuse by name.
- Elaboration-budget law: no heartbeat/timeout raises — a timeout means the
  construction is wrong; fix with more abstraction (check ground literals
  first on whnf timeouts). Residuals are named typed premises, never sorry.
- ≤3 concurrent lean; agents use `lake env lean` only, never `lake build`,
  never LSP. Under API instability: single-agent regime, no check_all
  concurrent with agents, bake salvaged diagnoses into relaunches, do
  near-done or spec-layer items inline.
- check_all stage b scans untracked files — move agent WIP aside for
  validating runs; read the output tail, not just the exit code.
