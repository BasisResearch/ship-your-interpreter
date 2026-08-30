# Seq body oracle — the shared loop-repr gap, pinned and closed (2026-08-30)

Follow-up to `experiments/loop-fanout.md` blocker 1. That pass landed the
per-shape step-contract *marshalling* (`Vsa/Sim/rows/LoopSteps.lean`) and found
that every loop-body oracle `hbody` (seq/while/for/args) is gated on the SAME
piece: the AST representation of the statement/expression being run must survive
the iteration's loop-counter spill (`sd i, k(sp)`) — the recurring
`exprRepr_agreeP`/`stmtRepr_agreeP` residual. This pass PINS that gap to its
exact conjunct and CLOSES it with one reusable transport, then applies it to the
seq (exemplar) shape.

## The gap, pinned precisely

The block do-while body's FIRST decode step (`execBlockIter`, `ExecBlock2.lean`
doc §155) runs the seven setup instructions ending in the counter spill
`sd x16, 0x8(x2)` at `0x800041c0` (`x2 = sp - 176`, so the write hits
`sp - 168`), then invokes `armExec_rec` (`ExecBlock.lean:185`) for the recursive
`jal exec_stmt`. `armExec_rec`'s precondition **`ExecBlock.lean:224`** demands:

```
StmtRepr mcall aStmtSub.toNat sSub
```

where `mcall = writeMap8 m0 (sp-168) (sdData_val i)` is the loop-head memory `m0`
AFTER the spill. `ExecStepGeom` (`ExecBlock2.lean:106`) pins `StmtRepr m0 …` — so
the sole missing link is: **the spill lands in `[SL.lo, sp)` (the stack window),
the AST lives in the read-only script region disjoint from it, therefore the
`StmtRepr` survives**. That is *exactly* one `stmtRepr_agreeP` application whose
footprint-disjointness side condition (`StmtFp ∉ stack window`) `ExecStepGeom`
does NOT itself carry — it pins only the tag-node disjointness
(`aStmtSub+16 ≤ SL.lo ∨ sp ≤ aStmtSub`), exactly as `ExecDispatch.execPrologue`
(`ExecDispatch.lean:179`) pushes the deep `hfpDisj` to its caller.

Reproduced live in `/tmp/gap_repro.lean` (not committed): the `armExec_rec`
line-224 conjunct is discharged verbatim by the new transport.

## What landed

### `Vsa/Sim/ReprStackSurvival.lean` — the reusable transport (ONE lemma, all four loops)

The exact reusable statement the mission asked for — *any write inside
`[SL.lo, sp)` (∪ the arena) preserves any `StmtRepr`/`ExprRepr` over the script
region*. Belongs to the `ReprSurvival.lean` `*_agreeP` pattern family; it is the
stack-window specialization of `AstTransport.stmtRepr_agreeP`. Elab <1s,
axiom-clean `{propext, Classical.choice, Quot.sound}`.

* `StackWindow`/`OffStackWindow`/`OffStackArena SL sp A` — the window and its
  complement footprint predicates.
* `writeLog_agreeP_offStackArena` — a reflected body `writeLog` whose store
  windows are `WinsInSA` (in the stack window or arena, `LoopStep.lean:63`) with
  1/4/8 widths agrees with the entry memory everywhere off stack ∪ arena.
  (Composes `BlockAdapter.writeLog_agreeP_disjoint` + the `WinsInSA` geometry.)
* **`stmtRepr_survives_writeLog`** / `exprRepr_survives_writeLog` — the
  consumer-facing form: `WinsInSA` log + 1/4/8 widths + footprint ∉ stack ∪
  arena ⇒ the repr survives the whole iteration's writes. THE lemma the four
  body oracles reuse.
* **`stmtRepr_survives_spill`** / `exprRepr_survives_spill` — the tightest form:
  a single `writeMap8 m tgt d` at an in-window slot (`SL.lo ≤ tgt`,
  `tgt+8 ≤ sp`) preserves the repr with one `omega` side condition. The exact
  `sd i` counter-spill shape, no `writeLog` plumbing.
* `stmtRepr_survives_stackWrite` / `exprRepr_survives_stackWrite` — the raw
  `AgreeP (OffStackWindow) m m'` + footprint-disjoint core (used by the above).

### `Vsa/Sim/SeqBodyOracle.lean` — the seq-shape application (exemplar)

* `blockSpillSlot sp := sp - 168`, `blockSpillSlot_in_window`
  (`SL.lo + 2352 ≤ sp ⇒ slot ∈ [SL.lo, sp)`, from the loop's recursion headroom).
* **`blockIter_stmtRepr_ready`** — the seam: from `ExecStepGeom`'s pinned
  `StmtRepr m0` + the stack-headroom geometry + the caller's deep footprint
  disjointness `hfpDisj`, delivers `StmtRepr (writeMap8 m0 (sp-168) d) aStmtSub s`
  — the exact `armExec_rec` line-224 conjunct. Axiom-clean, elab <1s.

Both files imported in `Vsa.lean` (after `LoopStep`/`LoopSteps`); the 5 public
theorems added to `scripts/check_all.sh` stage-c.

## Is the seq loop's step contract closed modulo IH only?

**Not yet fully** — and honestly so. `execBlockStep`'s `hbody` is a two-part
decode: (a) the AST-repr transport across the spill [NOW CLOSED by
`blockIter_stmtRepr_ready`], and (b) the pure machine register-threading of the
seven setup sites + `armExec_rec`'s IH-seam + the branch-control sites
(`0x800041c8` `bnez`, `0x800041cc-0x800041dc` reload/inc/back-edge). Part (b) is
the ~250-line site-chain assembly the `ExecBlockSites.lean` battery already
supports but which no combinator yet folds; it is IH-shaped (the only recursion
is `armExec_rec`'s `hIH`), carries NO further AST-repr transport, and is the
genuine remaining machine content. So after this pass the seq `hbody` residual is
**decode-only + IH** — the shared semantic gap the fan-out flagged is gone.

## While/for/args clone table (what the fan-out clones per loop)

The transport (`stmtRepr_survives_writeLog` / `_spill` and the `Expr` twins) is
loop-agnostic — the SAME lemma serves all four. Only the per-loop geometry
(spill slot, body PCs, back-edge, which repr) changes:

| Loop | contract | body spill (`sd counter`) | back-edge PC | repr to survive | transport call |
|------|----------|---------------------------|--------------|-----------------|----------------|
| **seq** (exemplar) | `ExecSeqStep` | `sd i, 8(sp-176)` @ `0x800041c0` → `sp-168` | `blt` @ `0x800041dc` → `0x800041a4` | `StmtRepr` of `stmts[i]` | `blockIter_stmtRepr_ready` (= `stmtRepr_survives_spill`) |
| **while** | `ExecWhileStep` | body-frame counter spill @ while body | `0x8000403c` (while head) | `ExprRepr` of cond `c` + `StmtRepr` of body `b` | `exprRepr_survives_spill` (cond) + `stmtRepr_survives_spill` (body) |
| **for** | `ExecForStep` | body-frame counter spill @ for body | `0x8000426c` (for cond head) | `ExprRepr` of cond + `StmtRepr` of body (+ opt init/step exprs) | same pair, plus `exprRepr_survives_spill` for `ocond`/`ostep` |
| **args** | `EvalArgsStep` | 24-byte `Value` copy + `i++` @ `0x800031dc` | `bne` @ `0x800031dc` | `ExprRepr` of arg expr | `exprRepr_survives_spill` (or `_writeLog` for the wider copy) |

For each loop the clone is:
1. Name the spill slot (`sp - k`) + prove it in-window (`SL.lo + headroom ≤ sp`)
   — a 2-line `blockSpillSlot`/`blockSpillSlot_in_window` copy.
2. Call the matching `*_survives_spill`/`*_survives_writeLog` on the loop-head
   geometry's pinned repr + the caller's `hfpDisj` — the transport is identical.
3. Feed the surviving repr into the shape's `armExec_rec`/`armTail_rec` seam
   (already produced by `execWhileStepOf`/`execForStepOf`/`evalArgsStepOf` in
   `rows/LoopSteps.lean`).

## Fan-out estimate

Each of while/for/args is ~1 short file mirroring `SeqBodyOracle.lean` (~15 code
lines: slot def + in-window lemma + the `*_ready` seam) PLUS the pure
decode-chain of the body sites (the part (b) above, per-shape, gated on a body
site battery — `ExecWhile`/`ExecFor` sites partly exist, args needs the 24-byte
copy sites). The **AST-repr transport itself is 0 additional work** — the
landed lemmas apply verbatim. So the residual per loop is decode-only, not
transport; ~1 day each for the site-chain fold, minutes for the seam.

## Anything infeasible / out of scope this pass

* The full `execBlockStep` `hbody` part-(b) decode (setup-site register
  threading + `armExec_rec` fold + branch-control chain) is NOT folded here — it
  is the ~250-line machine assembly `loop-fanout.md` explicitly deferred, needs a
  body-chain combinator, and carries no AST-repr transport (so it is orthogonal
  to the shared gap this pass closed). `execBlockStep`/`execBlockSim` statements
  are UNCHANGED (no `_closed` variant was needed — `hbody` is still their honest
  hypothesis; this pass supplies the sub-lemma its proof will consume).
* `ExecStepGeom`'s deep `hfpDisj` (AST subtree ∉ stack window) remains a
  caller-supplied premise — it is a geometric script-region fact, correctly the
  mutual-recursor's obligation (same as `execPrologue`'s), not a transport gap.
