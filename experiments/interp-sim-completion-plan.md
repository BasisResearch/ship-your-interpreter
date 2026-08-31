# InterpSim completion plan (updated 2026-08-31; original 2026-08-30)

State: `InterpSimFinal.interpSimClosed_of_families L hterm htri hdivFam herrFam :
InterpSim L` is a complete theorem. Completion = discharging the four residual
bundles. The v2 metaprogram layer is complete; the 2026-08-30/31 campaign
(waves 1-5, commits `7813980`/`00c2475`/`6de8d77`/`409c6b7`/`34dbd7e`, every
wave check_all: OK, currently 400/400 axiom-audited) additionally built the
ROW/REDUCTION LAYER: every bundle is now reduced to named, typed residuals.
Remaining work = discharging those residuals; no unscoped gaps remain.

Coordination: coordinator owns `Vsa.lean` + `scripts/check_all.sh`; agents
return wiring lines. Standing rules: `scripts/abs_inventory.sh` before every
dispatch; reuse by name; elaboration-budget law (no heartbeat/timeout raises —
a timeout means the construction is wrong, fix with more abstraction); agents
return blocker details, never workarounds; residuals are named typed premises,
never sorry.

## Status of the original steps

1. **eq/ne front** — DONE (commits through `46667a2`; evalEqSimD/evalNeSimD
   consumed by the binary dispatcher).
2. **ge, mul** — DONE (pre-campaign).
3. **M5 error family** — DONE (`errFamilyClosed`; ExitPathSpans wired).
4. **Shape-C loops** — LAYER DONE (`LoopSteps.lean`, `evalArgsStepOf`
   marshalling paid once per shape); per-arm machine chains remain (see below).
5. **env_define/realloc** — composition landed (`envDefContract` +
   append/grow); framed-callee posts landed for strlen (tick-complete) +
   memcpy byte-route; **3/9 Shape-A bridges closed**
   (strlenPre/mallocPre/capCompute). Open: bridgeStore (FrameRepr-append core),
   namesToVals/appendHead (need the grow-seam struct-field pins — GrowEnvEntry
   carrier), hUpdate + dispatch scan (reuse env_get scan shape), memcpy
   word-route framed epilogue.
6. **Residual unification / rows** — LAYER BUILT: ~26 of the 50 recursor
   premises have landed slot-verified rows (10 EvalE leaf/logical/unary,
   hBinary dispatcher `eval_binary_row` + `binary_row_fills_hBinary`, hVar
   (`eval_var_row_closed`), all 7 call-subsystem, hSBrk/hSCont/hSExpr/hSRet/
   hSRetNull). The three exit wideners exist (`LeafWiden`/`ExecRecWiden`/
   `EvalRecWiden` + `blockD_v_phic`). Open premises: hAssign (env_define-gated),
   hCallClosure (depth crux), ExecS dispatch/loop arms (if/while/for/block/seq),
   scaffold premises; then the `@EvalE.rec` table assembly (naming discipline).
7. **M5 second half + M6** — MAJOR PROGRESS: the trichotomy spec bug
   (machine-checked in `Vsa/While/StmtDispatch.lean`: pre-amendment `Approx`
   could not witness within-statement divergence; `hExclude` unsatisfiable;
   `Trichotomy` false at `[while(true){}]`) is FIXED by the wave-5 amendment —
   `SApprox` mutual fuel family (1:1 mirror of the error judgment) +
   `Approx.head`; exclusion proved by contraposition; `loopP_diverges` demo.
   `htri` now rests on `StmtDispatchD` + `hroot`
   (`trichotomy_of_stmtDispatchD`, both honestly provable). `hdivFam` =
   `DivCorrFamily` (gated on the same forward-sim Triples as hterm; `DivStep`
   redefined as a conjunction so downstream signatures were unchanged).
   M6 close (Layout bundling + `Vsa.Refine.refinement` plug) still open.

## Remaining work (the discharge queue, by front)

Machine-side (each scoped, callees/reuse identified in the session task notes):
- **env_define bridges** (6 remaining; agent pattern established) → unblocks
  hAssign, hSVarInit/hSVarNull/hSBlock, and the Call.closure env-fold.
- **ExecS dispatch/loop arms** — the largest un-rowed family; loop shapes and
  `execBlockA`/`execBlockD` exist, each arm is a chain instance.
- **hBinary str cells**: str-cmp arm chain (sign tails + all callees landed;
  order bridge `StrCmpOrderBridge` = String.lt ↔ strcmp sign, spec layer has
  only equality today) + stringify/concat path (biggest single new
  development; `stringify` = the snprintf-family formatter, no spec yet).
- **Call residuals**: native print char-loop body (`NativeBodyContract`),
  `CallArmSpec`/`FnArmSpec` (unblocked by `blockD_v_phic`), retNull glue
  assembly (site batteries + `NullBridgeSeam` landed), `ArgsNilHop`,
  `ArgsBodyOracle` (mutual-recursor-gated).
- **hVar last layer**: `VarPostRepack` + `EnvGetCallerGeom` discharge at the
  arm (marshalling `foundSt_of_storeRepr` + framed post landed).
- **Entry seams**: `StoreInitSeam` (env_new startup decode) + `EpilogueFrame`
  (mostly `restoreRetChain_run` reuse). Closes hEntryHalts.
- **hCallClosure** — the depth crux; after env_define lands, it is
  arity+depth-guard+env_new+env_define-fold+body-ExecSeq at d+1 via callSeg.

Spec-side:
- **`StmtDispatchD` + `hroot`** — the final htri residuals; classical totality
  induction over the Stmt/Expr mutual family (runs ∨ errors ∨ SApprox-∀).

Exponentiation refactors (queued, non-blocking):
- strlen byte-tail rebuild on block-reflection (kills ~1000 hand lines).
- AbiFrameKit hoist (frame primitives proven callee-generic by verbatim reuse).
- re-seat `interpContSeg_of` on `restoreRetChain_run`; generic-`w` cmp fixup
  bridges (serve int + str arms); generator for the thrice-duplicated
  42-premise error-site list.

Then: residual unification into `TermShared`/`TermCallees`/`TermGuards`, the
recursor table assembly, `termSimClosed`, `hdivFam` from the same Triples, M6
Layout close, final `#print axioms` audit, end-to-end theorem into check_all.

## Execution notes

- ≤3 concurrent lean; agents use `lake env lean` only, never `lake build`,
  never LSP. During API instability: single-agent regime, never run check_all
  concurrently with agents, bake salvaged diagnoses into relaunches, do
  near-done/spec-layer items inline.
- check_all stage b scans UNTRACKED files — move agent WIP aside for
  validating runs; read the output tail, not just the exit code.
- Full session state: memory `interpsim-completion-campaign.md` + the task
  board (#6/#10/#11/#13/#15/#18/#20/#21/#24/#26 open at time of writing).
