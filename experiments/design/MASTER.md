# MASTER — global design pass for the 55 remaining record fields

> **RECONCILED against tree @ea30e22 (2026-09-02).** Per-item status stamped
> inline below (LANDED-BY / OPEN / GATED-ON). The single largest delta: **Wave-0
> item 0b (the `EvalEntry.ground`/`ExecEntry.ground` INSERTION) already LANDED in
> wave 47i** — both entry structures now carry the `ground` field
> (`InterpEntry.lean:598`, `ExecEntry.ground` `ExecEntry.lean:429`); it was
> "MISSING" only because this design shipped after 47i. That insertion is what
> flipped hStr→FOUND (`field_hStr` via `strAstRegionBody_of_ground`) and made the
> brk/cont X3 flip mechanical. Wave-0 0c's vp jump-table generator ALSO partly
> landed (`LayoutVpTableGen.lean`, wave 44/45 mkind-lwu). Live census (tree, incl.
> the in-flight wave-48d write): **6/58 FOUND** = hInt, hNull, hBool, hStr, hSBrk,
> hSCont. The authoritative remaining map is `experiments/REMAINING.md`.
>
> **NOTE — wave 48d is IN FLIGHT** (uncommitted working-tree edits to
> `ExecBrkCont`/`ExecCaseGeom`/`ExecLeafD`/`ExecLeafPin`): `field_hSBrk`/
> `field_hSCont` are premise-free (`ExecArmMemExt` DELETED) in the tree but
> `field-census.tsv`/`wave0.md` may lag. Fold its final green verdict in on landing.
>
> **0a (residual→named-field restate): PARTIALLY OPEN.** The flat-∧ towers are NOT
> yet uniformly restated as `structure … : Prop` — spot-check `ExecCaseGeom.lean`
> shows 0 structures. Treat 0a as an OPEN statement-wave, tracked in REMAINING.md.

One coherent design sitting (2026-09-02). Designs the statement shapes,
invariants, bridge shapes, supplier DAGs, and bounded proving tasks for ALL
remaining `TermResidualsCore`/`ErrWork` fields, so proving agents execute
against fuzz-validated designs instead of re-discovering statement bugs.

Per-cluster detail: `loop-arm.md`, `error-jal-seam.md`, `io-loop-fold.md`,
`env-seam.md`, `singletons.md`.

## The ONE governing finding

All landed obstructions (`fleet/obstructions/*.lean`) refute the current fields
via FOUR statement-shape defects, none semantic:

| Defect | Class | Fields | Fix (statement-layer) |
|--------|-------|--------|-----------------------|
| ∀-`m0` slot pin (`StmtSlotPinned … ∅`) | B5 | 12 exec dispatch + 6 vparm | condition on the pinned image: carry `Exec/Eval/IoGround` (N1/N2 table pins, LANDED interface) |
| `sp_headroom` under ∀-`sp` | B2 | hNeg hNot + 4 logical | carry `EvalEntry` as a HYPOTHESIS field |
| ∀-`mcall` totality (`hMcallPop`) | X1 | 6 unary/logical | replace with a `deadPres` field on the ACTUAL read footprint |
| code-free `SegEntry` off-diagonal | B6 | seq/args/for spans | `SeqSpanGround` code-pin (seq LANDED; args/for MISSING) |

Plus the bridge-review mandate: **every residual becomes a named-field
`structure … : Prop`** (kills the flat-∧ towers, so `repack`/`EntryBridge` close
the entry-transport seam with no positional `.2.2`). This restatement wave
touches the SAME rows as the `ground` insertion — sequence them together.

The genuine (non-statement) remaining content is X6 callee seams (str/div/env/
native) and X4/X7 recursor oracles (loop IHs, hCallClosure crux) — no combinator
supplies these; they are per-arm campaign work.

## Generator-vs-hand split

**Generated** (`gen_layout.py` extensions, ELF ground truth — NO proof risk):
- N1 kind jump-table pins (`LayoutJumpTableGen`, LANDED)
- N2 stmt jump-table pins (`LayoutStmtTableGen`, LANDED)
- **N-vp** value_print jump-table pins (`0x80019f10`, `IoGround`) — MISSING, add
  as the 3rd generator (small).
- errSite Triples (19) — LANDED (`ErrSitesBatch*`, `#derive_error_site`).
- per-arm `#derive_case`/`segToTriple` seg rows — generator-driven (`gen_fn.py`).

**Hand** (bounded seg/callSeg/loopFromBody instantiations, ≤1 session each):
- the relational-mined dispatch bridges (exec arms, vparm) — mine then discharge.
- the loop-folds (io flush loops, args loop) — `loopFromBody` + back-edge.
- the callee-seam splices (X6) — `callSeg`/`bridgeOfSeg` per callee.
- the recursor oracles (X4/X7) — capstone-threaded, NOT per-field.

**Statement-layer wave** (touches all rows, no proof): the residual→structure
restatement + the `EvalEntry.ground`/`ExecEntry.ground` INSERTION (fleet-scale
plumbing, audit §D map — 15 ctor sites, 26-file `NBSPins` conduit, ~304-file
regen; every supply term pre-proved in `EntryGroundRows.lean`).

## Cross-cluster sequencing (critical path)

```
WAVE 0 (statement + generator, no proof risk):
  0a. residual→named-field-structure restatement (ALL clusters, bridge-review)   [OPEN — not yet uniform]
  0b. EvalEntry.ground / ExecEntry.ground INSERTION (audit §D fleet wave)         [LANDED-BY 47i]
  0c. IoGround / VpTablePins generator (singletons + io)                          [PARTIAL: LayoutVpTableGen LANDED w44/45; IoGround MISSING]
  ⇒ UNLOCKED (actual): hStr (47g→47i), hSBrk/hSCont (48d in-flight). B5/B2/X1
     refutations dissolve for the fields whose rows now consume `.ground`.

WAVE 1 (near-landed, ride Wave 0):
  1a. LA-int relight (11 cells, value paths LANDED) — T-LA-carry + T-LA-int-relight
  1b. error family (19 errSite DONE) — T-ERR-restate + T-ERR-reach + T-ERR-kindname
  1c. io_write + shims + value_print — T-IO-relight + T-IO-shims + T-IO-valueprint
  1d. vparm(6) + hFn + hEpilogueSpill — T-S-vparm, T-S-hFn, T-S-epilogue

WAVE 2 (relational-mined dispatch + loop-folds):
  2a. LA-stmt dispatch (12) — T-LA-stmt-dispatch (mine per arm)
  2b. LA-unary/logic (6) — T-LA-unary + T-LA-logic (deadPres footprint)
  2c. io flush loops — T-IO-flushloops (mine + loopFromBody)
  2d. env args + var + vardecl — T-ES-args, T-ES-var-bridge, T-ES-vardecl

WAVE 3 (genuine callee content, X6 — parallel campaign lanes):
  3a. LA-str (6) + LA-div-ov (1) — strConcat / StrCmpOrderBridge / div seam
  3b. env call-arm (hCall), native print (hCallPrint/Println/AssertOk via io)
  3c. hInitStore (X8 interp_init)

WAVE 4 (recursor/capstone — NOT per-field, assembled last):
  4a. hCallClosure crux (X7, StackNeed budget)
  4b. hSBlock/hSForStart loop IHs (X4)
  4c. hDivCorr divergence family (X8, divergence endgame CLOSED per memory)
```

Wave 0 is the gate: it is the highest-leverage single action (turns 24+ refuted
fields into record fills + relight-recompiles). Everything else parallelizes.

## Honest total — bounded tasks (≤1 session each)

| Cluster | Bounded tasks | Record-fills (ride Wave 0) | Recursor/capstone-threaded | X6 seams (separate campaign) |
|---------|:---:|:---:|:---:|:---:|
| loop-arm (36) | 6 | — | — | 7 (6 str + 1 divov) |
| error-jal-seam (19) | 5 | — | — | — |
| io-loop-fold (16) | 8 | — | — | (large fns pruned by audit) |
| env-seam (13) | 6 | — | 2 (hSBlock/ForStart) | 3 (native routed to io) |
| singletons (13) | 3 | 2 (hStr, brk/cont) | 1 (hDivCorr) | — |
| **Wave 0 (shared)** | **3** (0a restate, 0b insert, 0c generator) | — | — | — |
| **TOTAL** | **31 bounded tasks** | 4 | 3 | ~10 |

**31 bounded proving/tooling tasks** close the 55 fields, of which:
- 3 are the Wave-0 statement/generator gate (fleet-scale plumbing, zero proof risk),
- ~18 are near-landed relights + mined dispatch bridges + loop-folds,
- ~10 are genuine X6 callee-seam campaign lanes (str/div/native/env — pre-existing lanes),
- 4 are record-fills that cost nothing once Wave 0 lands,
- 3 are recursor/capstone oracles assembled at the top (not per-field work).

## Validation done this pass

Every NEW statement shape fuzzed with `scripts/statement_fuzz.py --file --prop
--struct` (hermetic mode): `StmtArmResid`(conditioned), `UnaryArmResid`(deadPres),
`BinIntCellResid`(entry-carry), `WriteLoopInv`, `CallPrintResid`, `ErrArmResid`,
`VParmArmResid`(conditioned), `FnResid`, `LeafResidAmended` — ALL SURVIVED. The
OLD refuted shapes stay machine-checked-false in `fleet/obstructions/` (the
negative validation). Spot-checked designs vs corpus: loop-arm (hIAdd 9-block
slice), error-jal-seam (err_80003b54 shared-slice caveat → 19 distinct armPCs),
io (io_write tohost loop matches `WriteLoopInv`), exec-leaf (hSBrk/hSCont vs the
round-3 brk/cont relational pilot — field-for-field).

## Note for provers

The `--struct` fuzzer synthesizes per-field `by decide` witnesses, so it
confirms field-type INHABITABILITY, not cross-field consistency. It CANNOT
catch a cross-field contradiction where field B is false for every value making
field A true. The design guard against that is structural (carry the entry
hypothesis so preconditions are supplied, not derived), and is what the
obstruction files already machine-check on the OLD shapes. When instantiating,
Law 4 still applies: an in-proof failure is a new CTI, feed it back.
