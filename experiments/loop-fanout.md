# Shape-C loop fan-out — step-contract producers (2026-08-30)

Step 4 of `experiments/interp-sim-completion-plan.md`. The M4 loop cases are
landed CONDITIONAL on named per-iteration step contracts. This pass inventories
every one, classifies by loop shape, and supplies the missing **producers** — the
per-shape lemmas that build the step contract from a mechanical machine-iteration
body oracle + the recursion IH(s) — collapsing each shape's residual to ONE body
chain.

Deliverable: `Vsa/Sim/rows/LoopSteps.lean` (green, axiom-clean
`{propext, Classical.choice, Quot.sound}`, elab 1.3s, imported in `Vsa.lean`,
4 theorems added to `scripts/check_all.sh`).

## Inventory — the named step-contract residuals

| Contract | File:line (def) | Consumers | Post shape | IH(s) in body |
|----------|-----------------|-----------|------------|---------------|
| `ExecWhileStep` | `ExecWhile.lean:277` | `execWhileExit` (`ExecWhile.lean:312`), `execWhileLoopSim` (`ExecWhile2.lean:129`), `execWhileSim` (`ExecWhile2.lean:195`) | `Triple ExecEntry (loop-back ∨ exit)` keyed on `bodyStatus` | cond `EvalIH` + body `ExecIH` |
| `ExecForStep` | `ExecFor.lean:132` | `execForExit` (`ExecFor.lean:169`), `execForLoopSim` (`ExecFor.lean:216`), `execForLoopBody`, `execForStartSim` (`ExecForStart.lean`) | `Triple ExecEntry (loop-back ∨ exit)` keyed on `bodyStatus` | cond `EvalIH` (opt) + body `ExecIH` |
| `EvalArgsStep` | `EvalArgs.lean:115` | `evalArgsLoop` (`EvalArgs.lean:183`), `evalArgsCons` (`EvalArgs.lean:248`) | `EvalE → Triple SegEntry (always-loop-back)` | one arg `EvalIH` |
| `ExecSeqStep` | `ExecSeqLoop.lean:126` | `execSeqLoop` (`ExecSeqLoop.lean:190`) | `ExecS → Triple ExecSeqEntry (normal ∨ abrupt)` | body `ExecIH` |
| `env_get` scan (`hreach`) | `EnvGetSpec6.lean:1086` | `env_get_found_spec` | straight-line reach + `AtHit`→`HitTailSt` repack | — (scan itself already closed) |

## Shape classification (5 loop shapes → 3 producer families)

1. **while re-dispatch** (`ExecWhileStep`) and **for re-dispatch** (`ExecForStep`)
   are the SAME shape: `Triple ExecEntry (loop-back ∨ exit)` with a two-IH body
   (cond eval + body exec) and a `bodyStatus`-keyed disjunction. ONE marshalling
   proof serves both — `execWhileStepOf` / `execForStepOf` are byte-for-byte
   identical modulo `.whileStmt c b` ↔ `.forStmt oinit ocond ostep b` and the
   scope (`env` ↔ `outer`).
2. **args-cons loop** (`EvalArgsStep`) is the DEGENERATE case: no abrupt exit ⇒ a
   single always-loop-back post (no `bodyStatus` keying), a one-IH body.
   `evalArgsStepOf`.
3. **statement-seq loop** (`ExecSeqStep`) was **already produced** by
   `execBlockStep` (`ExecBlock2.lean:210`) — the exemplar this pass mirrors.
4. **env-scan** (`env_get`/`env_define`) is **NOT a residual loop shape** — see
   below.

## What was built (mechanical / shape-level)

`Vsa/Sim/rows/LoopSteps.lean`:

* `execWhileStepOf` — produces `ExecWhileStep` from `hbody` (the machine-iteration
  body oracle, packaged as the loop-back∨exit disjunction, φ-extension over the
  intermediate `stMid`) + `hphi` (the `stMid`→`stFin` φ-alloc upgrade). ~10-line
  body: destructure the oracle's outcome, upgrade the loop-back φ-extension,
  forward the exit disjunct unchanged. This is the `execBlockStep` marshalling,
  proven once.
* `execForStepOf` — the `for` twin (identical marshalling; the shape-level reuse).
* `evalArgsStepOf` — the args twin (single-disjunct; discharges the spec `EvalE`
  premise, forwards, threads the `stFin` φ-upgrade + mid-to-`m0` memFrame clause).
* `execWhileExit_of_bodyOracle` — a WRAPPER showing the substitution:
  `execWhileExit` with its abstract `hstep` supplied by `execWhileStepOf`,
  leaving only the body oracle + φ-glue + exit witness. Demonstrates the loop
  rules become fully closed on the per-shape mechanical oracle **without changing
  any existing theorem statement** (the same idiom applies to
  `execForExit`/`evalArgsLoop`; not spelled out to avoid churn — they are the
  identical two-line `hstep :=` substitution).

The **exponentiating win**: the disjunct/`Triple` marshalling — the spec-side glue
mapping a raw `∃ c', Steps c c' ∧ (post-disjunction)` into the contract's `Triple`,
including the loop-back `stFin` φ-upgrade — is now proven ONCE PER SHAPE (3 proofs),
and while/for share one. Previously this glue was only present for the seq shape
(inside `execBlockStep`); the while/for/args contracts had NO producer at all
(consumed purely abstractly). Each loop shape's residual is now exactly the two
inputs `execBlockStep` already isolated: the IH(s) [hypothetical, correct per
mission point 3] + the single body-chain oracle `hbody`.

## What remains (the genuine machine content — NOT dischargeable in this pass)

The body oracle `hbody` per shape — the compiled loop-body chain decode:

* **while/for**: `cond-eval-setup ≫ jal eval_expr [EvalIH] ≫ value_truthy ≫ jal
  exec_stmt [ExecIH] ≫ status-dispatch (beqz/bne/beq) ≫ back-edge` — a TWO-IH
  body. Back-edge PCs: while head `0x8000403c`, for cond head `0x8000426c`.
* **args**: `arg-load ≫ jal eval_expr [EvalIH] ≫ 24-byte Value copy to
  sp+32+i*24+208 ≫ i++ ≫ bne back-edge` at `0x800031dc` — a ONE-IH body.

These are a `#derive_case`/`chain_facts` prefix segment ≫ `armTail_rec`/
`armExec_rec` (the `jal`-IH seam, `EvalRecCommon.armTail_rec` /
`ExecBlock.armExec_rec`) ≫ `LoopStep.loopStep` (the back-edge run) assembly — every
combinator exists. They are NOT closable now because:

1. **No body-site battery exists** for the while/for/args loop bodies.
   `ExecWhileSites.lean` covers ONLY the trivial `li a0,0 ; j 0x8000409c` exit
   tail; there is no `for`/`args` body-site file. Producing them is a
   `#derive_case` fan-out (mechanical, but real decode work — each body is a
   multi-block chain with two `jal` seams, not a paste-table).
2. **`execBlockStep`'s analogous `hbody` is itself still OPEN** — its docstring
   (`ExecBlock2.lean:191-201`) states it is "supplied by the (later)
   mutual-recursor scaffolding that re-lands `armExec_rec` at each site" and is
   "BLOCKED unconditionally only on the AST-repr transport `StmtRepr`-agreeP
   across the `sd i` spill (the recurring `exprRepr_agreeP` residual) + the
   branch-control decode". The seq shape — the ONE with a producer — has not
   closed its oracle, so closing while/for/args oracles is gated on the SAME
   `exprRepr_agreeP`/mutual-recursor pieces. Building them ahead of the seq oracle
   would duplicate that gap three more times; the correct sequencing is to land
   the `exprRepr_agreeP` transport + one body oracle (seq), then fan the identical
   `#derive_case`+`armExec_rec`+`loopStep` recipe across while/for/args using the
   producers landed here.

So the honest end-state: the step-contract **marshalling** is now uniform and
closed for all four control-flow loop shapes (was closed for one). The residual is
the per-shape body-chain oracle, blocked on `exprRepr_agreeP` (AST-repr transport
across the counter spill) — a Layer-4 semantic gap shared with the already-landed
seq producer, not a Shape-C combinator gap.

## env-scan — reported precisely (NOT closed here, and correctly so)

The mission flagged `env_get_found`'s `hreach` (`EnvGetSpec6.lean:1086`) as
possibly belonging to the scan-loop shape. It does **NOT**:

* The scan loop itself is **already discharged UNCONDITIONALLY** —
  `EnvGetSpec4.env_get_scan_spec'` proves `Triple ScanInvE (ScanExit …)` with NO
  `hbody` hypothesis (the per-iteration `env_get_scan_body`/`scan_iter` is proven
  from the `EnvGetSpec2` sites). So there is no scan loop-body residual to feed a
  Shape-C producer.
* `hreach` (`EnvGetSpec6.lean:1059-1073`) bundles only (1) the **straight-line**
  prologue reach `0x80002c10 → scan entry` (7 callee-saved spills, `sp -= 64`,
  loads `s4=env`/`s2=count`/`s1=names`, `j` to the scan test) — a Shape-A segment,
  not a loop; and (2) the repackaging of `ScanExit`'s `AtHit` (PC + first-match +
  `GoodState`) into the richer `HitTailSt` — the missing fields (`FrameRepr`,
  spill readbacks) come from the PROLOGUE spills, not from any scan iteration.

So the env-scan "shape" needs the `env_get` **prologue** `#derive_case` segment +
the `AtHit`→`HitTailSt` field bridge — NOT a loop-body oracle. It is a Shape-A
(straight-line) + marshalling residual, correctly out of scope for the Shape-C
loop fan-out. `evalVarSim` stays conditional on `env_get_found` until that
prologue segment + repack land (a separate, non-loop task).

## Mechanical patterns observed

* **while ≡ for**: the two re-dispatch producers are the same proof; a single
  parameterized lemma over `(Stmt-index, scope)` would merge them, but the two
  `ExecEntry` node indices (`.whileStmt` vs `.forStmt`) make the shared form only
  marginally shorter than the two copies — the copies are ~30 lines each, so the
  clone is cheaper than the abstraction here (documented, not forced).
* **the marshalling is pure `Triple`/`∃`/disjunction algebra** — no reflection, no
  decode — so it is fast (1.3s whole file) and needs none of the DecodeTable
  batteries. This is why it could be closed now while the oracles cannot.
* the producers slot into the consumers by a two-line `hstep :=` substitution
  (`execWhileExit_of_bodyOracle` shows it); no consumer statement changes.
