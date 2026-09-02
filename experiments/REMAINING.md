# REMAINING.md — the authoritative remaining-work map

**Snapshot: tree @ea30e22 (2026-09-02), incl. the IN-FLIGHT wave-48d write.**
This file is THE single source of remaining work. It supersedes the ledgers in
`post-tooling-fanout-plan.md` and `run1-brief.md` (both now HISTORICAL). Regenerate
after any wave by re-running `scripts/field_census.py` + a `git log` diff against
the last snapshot line above.

> **Wave 48d caveat.** `field_hSBrk`/`field_hSCont` are premise-free in the
> working tree (uncommitted; `ExecArmMemExt` deleted) but `field-census.tsv` was
> committed at 4/58. On 48d landing, re-run `field_census.py` and confirm 6/58.
> The census rows for hSBrk/hSCont are pre-flipped here to FOUND.

## Rollup

- `TermResidualsCore`: 58 fields. **6 FOUND** (hInt, hNull, hBool, hStr, hSBrk,
  hSCont) → **52 open**.
- `ErrWork`/`hErrFam`: 19 error-arm linkages (split out of the core; the 19
  `errSite` Triples are LANDED, residual = per-arm `Reaches`).
- **Bounded tasks remaining: ~31** (per MASTER), of which ~18 are near-landed
  relights + mined dispatch bridges + loop-folds, ~10 are X6 callee-seam campaign
  lanes, 3 are recursor/capstone oracles.
- **Genuinely-hard items (flagged, no combinator supplies them): 5** —
  (1) hCallClosure depth **crux** (X7), (2) **vfprintf** family (io, large),
  (3) **String bridges** (StrConcat / StrCmpOrderBridge, X6), (4) **ErrWork reach**
  (19 caller-linkages, no combinator), (5) **final assembly** (capstone recursor:
  hDivCorr / hSBlock / hSForStart IHs + `term_sim` residual-unification).

## What LANDED (the big deltas prior docs missed)

- `EvalEntry.ground`/`ExecEntry.ground` INSERTION — **wave 47i** (MASTER Wave-0
  0b; docs called it MISSING). This is the gate that flipped hStr and enabled
  brk/cont.
- 19 `errSite` Triples (`ErrSitesBatch{0..3}`), `LayoutVpTableGen` vp jump-table
  pins (w44/45), `ValuePrintContract` (Fputs/Fwrite/Fprintf), env_get_found /
  env_define composition, StackNeed budget layer (B0), io_write loop-fold, snprintf
  %lld (M3), all block-reflected int/eq value paths (Add..Ge/Eq/Ne/Div/Mod/Mul).
- io-buffering "falsity" RETRACTED (setvbuf _IONBF; `IoEmits` correct as stated).

## Per-field map (52 open + the 19 ErrWork linkages)

Format: **field** — blocker — landed assets that serve it — MASTER task.

### loop-arm cluster (36 open)

**LA-int (11): hIAdd hISub hIMul hIDiv hIMod hILt hILe hIGt hIGe hEq hNe**
— blocker: X2 (cell stated under ∀-`m0`, no `entry` carry); value paths LANDED.
— assets: `EvalAddRow`…`GeResid`/`EqNeDispatchStrong` (block-reflected, in tree),
`.ground` field (47i), mined KindBridge (BATCH-REPORT, all SURVIVED).
— task: **T-LA-carry** (add `entry` to `BinIntCellResid`) + **T-LA-int-relight**
(pure recompile). Record-fill class once carry lands.

**LA-stmt (12): hSExpr hSRet hSRetNull hSIfNone hSIfTrue hSIfFalse hSWhileFalse
hSeqNil hSeqConsNormal hSeqConsAbrupt hSWhileBreak hAssign**
— blocker: B5 (∀-`m0` slot pin) + B6 (code-free SegEntry for seq); NOW supplied by
`ExecEntry.ground`. — assets: `execGround_caseGeom_*`, `stmtRepr_kind`,
`StmtTablePins`, round-3 relational pilot (`exec_brk_bridge.lean`), the
`execExprSim`/`execVarDeclSim`/`execIfNoneSim`/`execWhileFalseSim` arm Triples
(in check_all, conditional on hGlue). — task: **T-LA-stmt-dispatch** (~3 sessions,
batched by dispatch origin) via `StmtArmResid`.

**LA-unary (2): hNeg hNot** + **LA-logic (4): hOrTrue hAndFalse hOrFalse hAndTrue**
— blocker: B2 (`sp_headroom` under ∀-`sp`) + X1 (`hMcallPop` totality); fixed by
`entry` carry + `deadPres` footprint field. — assets: `.ground`/`nbs_pins`,
`Field_hNull`/`Field_hNeg` template, obstruction files (negative validation).
— task: **T-LA-unary** + **T-LA-logic** (`UnaryArmResid` with `deadPres`).

**LA-str (6): hStrAddL hStrAddR hStrLt hStrLe hStrGt hStrGe** + **LA-div-ov (1): hDivOv**
— blocker: **X6 callee seams** (genuine content, NOT a falsity). — assets:
`strcmp_full_spec` slots, `StrCmpSignTail`/`StrCmpBlockC` (strcmp memory), div seam
`divdi3_spec`. — task: **T-LA-str/divov** (X6 campaign; **FLAGGED HARD** — String
bridges: `StrConcatCellResid` blocked on stringify spec, `StrCmpOrderBridge` lacks
String.lt agreement in spec layer).

### error-jal-seam cluster (19 ErrWork linkages, NOT core-census fields)

**err_800034e4, err_80002e90, err_80002ebc, err_80003950, err_80003b54,
err_80003b9c, err_80003bc8, err_80003c10, err_80003c7c, err_80003cc4, err_80003ce8,
err_80003d14, err_80003d5c, err_80003da0, err_80003de8, err_80003e98, err_80003f58,
err_80003fac, err_80003fdc**
— blocker: per-arm `Reaches` caller-linkage (`hsite`); ~14 also need
`value_kind_name` readback. — assets: **19 `errSite` Triples LANDED**
(`ErrSitesBatch{0..3}`, `#derive_error_site`), `runtime_error_spec`, spec
EvalErr/ExecErr transitions. — task: **T-ERR-restate** (`ErrArmResid` 19-field
structure) + **T-ERR-reach** (~2-3 batches; **FLAGGED HARD** — no combinator
supplies caller-linkage) + **T-ERR-kindname**.

### io-loop-fold cluster (feeds 3 core fields via native print)

**hCallPrint, hCallPrintln, hCallAssertOk** (the 3 core fields these serve)
— blocker: the print-path compose (io_value_print dispatch + CallPrint* structures).
— 16 io machine fns feed these: io_write/_r/_swrite/putc/fputc/fputs/fwrite/
sfvwrite/sbprintf/swbuf/sflush/fflush/fflush_r/svfprintf/vfprintf/snprintf +
io_value_print. — assets: io_write fold LANDED, `ValuePrintContract`, `LayoutVpTableGen`,
snprintf %lld (M3). — tasks: **T-IO-reachability-audit** (do FIRST, prune vfprintf),
**T-IO-flushloops** (×3, mine+`loopFromBody`), **T-IO-shims** (×2), **T-IO-valueprint**
(×1), **T-IO-compose** (×1). **vfprintf FLAGGED HARD** (28 blocks) but likely
off-path for the record fields (audit confirms).

### env-seam cluster (13 open)

**hVar** — env_get caller-linkage — `env_get_found_uncond''` LANDED — **T-ES-var-bridge**
(`EvalVarCallBridge` missing).
**hSVarInit, hSVarNull** — env_define splice — envdefine-composition LANDED —
**T-ES-vardecl** (Shape-A straight-line bridges missing).
**hArgsNil, hArgsCons** — args loop code-grounding (X5) — `loopFromBody` LANDED,
`SeqSpanGround` (seq) LANDED — **T-ES-args** (`mEvalArgs` SeqSpanGround table entry
missing).
**hCall** — call-arm (non-crux) — `callSeg`/`CallResid` — **T-ES-call-arm**.
**hCallClosure** — X7 depth **crux** — StackNeed budget (B0) LANDED —
**T-ES-crux** (**FLAGGED HARD**, sibling-owned).
**hSBlock, hSForStart** — X4 self-referential loop IH — capstone recursor —
**T-ES-loopbody** (recursor-threaded, NOT bounded; **part of final-assembly flag**).
**hInitStore** — X8 interp_init decode — MISSING — **T-ES-initstore**.
(hCallPrint/Println/AssertOk routed to io cluster above.)

### singletons cluster (owned by the wave-48d writer — see `design/singletons.md`)

**hStr** — FOUND (47g→47i via `strAstRegionBody_of_ground`).
**hSBrk, hSCont** — FOUND (wave 48d X3-c; premise-free, in-flight tree).
**vparm_VP_{NULL,BOOL,INT,STR,CLOSURE,NATIVE} (6)** — feed hCallPrint*; straight-span
value_print arms — `LayoutVpTableGen` pins, Fputs/Fwrite/Fprintf contracts —
**T-S-vparm**.
**hFn** — closure-alloc arm + native-store repr — malloc/fwrite/exit LANDED,
`NativeStoreRepr` MISSING — **T-S-hFn**.
**hEpilogueSpill** — interp_run epilogue restore — MISSING (bounded `block_facts`)
— **T-S-epilogue**.
**hDivCorr** — divergence oracle family (X8) — capstone recursor — **T-S-divcorr**
(recursor-threaded; **part of final-assembly flag**; divergence endgame CLOSED per
memory onto hEntry+hIter+ArmStages).

## Ordered by unlock-leverage (do in this order)

1. **T-LA-carry + T-LA-int-relight** — 11 fields, pure statement+recompile, all
   value paths landed. Highest field-count-per-effort.
2. **T-LA-stmt-dispatch** — 12 fields, `.ground` now supplies the pins; the arm
   Triples exist. Second-highest leverage.
3. **T-LA-unary + T-LA-logic** — 6 fields, `deadPres` footprint.
4. **T-ES-var-bridge / T-ES-vardecl / T-ES-args** — 5 fields, landed callee
   contracts, bounded bridges.
5. **T-IO-audit → T-IO-valueprint → T-IO-compose** — unlocks 3 print fields (+ 6
   vparm) once value_print dispatch lands.
6. **T-S-vparm / T-S-hFn / T-S-epilogue** — 8 fields, bounded segs.
7. **T-ERR-restate + T-ERR-reach + T-ERR-kindname** — the 19 error linkages.
8. **HARD LANE (parallel campaign):** T-LA-str/divov (String bridges),
   T-IO-flushloops/vfprintf, T-ES-crux (hCallClosure).
9. **FINAL ASSEMBLY (capstone, last):** hDivCorr, hSBlock/hSForStart loop IHs,
   `term_sim` residual-unification — assembled once, not per-field.

## The 5 genuinely-hard items (no combinator; expect research)

1. **hCallClosure crux** (X7) — recursion-depth/budget; StackNeed B0 landed,
   budgeted-entry re-index B1 in flight; falsity-#13 class.
2. **vfprintf / svfprintf** — 28-block io fns; likely off-path (audit first).
3. **String bridges** — `StrConcatCellResid` (stringify spec) + `StrCmpOrderBridge`
   (spec layer lacks String.lt agreement; only equality landed).
4. **ErrWork reach** — 19 per-arm caller-linkages; no combinator, reachability facts.
5. **Final assembly** — capstone mutual-recursor: hDivCorr + hSBlock/hSForStart
   IHs + `term_sim` residual-unification interface close.

## Appendix — staleness prevention (why this reconciliation was needed)

The tree repeatedly outran the plans (Wave-0 0b landed by 47i before MASTER
shipped; vparm/error rows "missing" while landed; two verification batches spent
sessions rediscovering "already done"). Three rules stop the recurrence:

1. **Reconcile-first for every brief.** Before writing or executing a brief/plan,
   diff the tree against the plan's stated snapshot (`git log <plan-date>..HEAD`
   + `field_census.tsv`). Trust order: **tree → logs → docs.** Never drive work
   from a doc's ledger without confirming the ledger against the tree first.
2. **Grep for target artifacts before generating.** Before building any
   `field_X`/`errSite_X`/`X_row`/generator output, `grep -rl` for it in `Vsa/`
   (and check `check_all.sh`). If it exists, the task is a record-fill or a
   no-op, not a build. (The `abs_inventory.sh` rule already mandates this for
   abstractions; extend it to target artifacts.)
3. **Commit-stamp design snapshots.** Every design/plan doc carries a
   "tree @<HEAD>" line at the top and stamps items LANDED-BY-<commit> / OPEN /
   GATED-ON as they change. A design without a HEAD stamp is presumed stale.
   REMAINING.md is the one authoritative map; regenerate its snapshot line each wave.
