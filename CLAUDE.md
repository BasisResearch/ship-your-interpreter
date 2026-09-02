# Proof discipline — the exponentiating layer is MANDATORY

This repo proves a RISC-V interpreter binary correct. Proof effort here went
subexponential exactly when work was done by hand beside an abstraction that
already existed (measured: a fully-decode-tabled region accumulated four
hand-rolled site batteries because the surrounding files modeled the legacy
idiom). The layer below is not advisory. `scripts/check_all.sh` stage a4
(`scripts/check_discipline.py` + `scripts/discipline_rules.tsv`) FAILS new
files that bypass it.

Before ANY proof work: run `scripts/abs_inventory.sh` and reuse by name.

## Mandatory tool per task shape

| Task shape | Use (never hand-roll) |
|---|---|
| WHOLE FUNCTION (multi-block: branches, loops, calls, tail-j, tohost seams) | `scripts/gen_fn.py --fn <f> --entry <pc> [--fold]` — emits the block arms + (recognised counted-loop shape) the derived `FnSummary` fold; fold combinators `FnSummary.{seq,callSplice,tailJump}` + `segRowFramed` (`Vsa/Sim/FnSummary.lean`, `SegToTripleFramed.lean`; model fold: `rows/FnWriteFold.lean`); rule R9 catches hand-rolled multi-seg function files |
| Straight-line OR branch/jump-terminated span | `#derive_case` seg + `segToTriple` (br/j/jr terminators are in-model; model: `Vsa/Sim/EnvDefSeg.lean` — 58 hand lines → 14, `EnvDefBridges4.lean` for branch-ended rows) |
| Span ending in a CALL (`jal`) | `BridgeSeg.bridgeOfSeg` + `jalStep_of_obs` (the jal seam is deliberately outside `TKind`) |
| ABI register frame on a run | `FrameMeta.abiFrame_of_wrChain` (one `decide`) — NEVER per-site frame threading |
| Memory-frame / footprint post | `FrameMeta.memFrame_of_chain` / `bblocks_sound_framed` |
| Framed variant of a callee spec | FrameMeta metatheorems over its reflected chain — NEVER re-run the chain with a ghost conjunct |
| Call splice (prefix ≫ callee ≫ suffix) | `callSeg`/`callSegConseq` (`DeriveCallSeg`) |
| Loop | `loopFromBody` (`DeriveLoop`) / the `LoopSteps` shapes |
| Error-site Triple | `#derive_error_site` table row |
| Recursor case row | the `gen_*_row.py` generators + TSV (TermRouting/ExecRouting/BinDispatchRow) |
| Exit widening | `LeafWiden`/`ExecRecWiden`/`EvalRecWiden`/`blockD_v_phic` |
| Store↔frame marshalling | `foundSt_of_storeRepr` / `frameRepr_append` |
| Load / byte-read obligation | TOTAL reads (`bytesT{1,2,4,8}`, `exec_*_tot`/`_totv`, `LPins*` as total-read equalities, `site_*_tot`/`_totb` from `gen_sites.py`) — the model's `readByte` is `getD 0`, so NEVER demand `m[a]? = some b` for a byte a proof does not already own; if the VALUE matters, thread the write fact (`valueRepr_copy_total`) |
| NEW post/entry predicate | named-field `structure ... : Prop where` (model: `FoundSt`/`GeomFacts`/`FrameCalc`) — NEVER an anonymous ∃/∧ tower |
| Consuming a LANDED ∃/∧ tower | write ONE named destructuring lemma beside the tower's def and consume through it — never `.2.2.2.2` positional chains |
| Entry-side ground fact (jump-table pin / AST-node/string region / arena/result-slot geometry) | `EvalGround`/`ExecGround` (`EntryGround.lean`; region layer `MemRegion.lean`, repr transport `AstTransport.lean`, generated pins `Layout*TableGen`) — NEVER per-site literals; the need audit is `experiments/entry-needs-audit.md` |

## Laws

1. Elaboration budget: NEVER raise `maxHeartbeats`/timeouts. A heartbeat bump
   or whnf timeout means the construction is wrong — check ground literals
   first (a wrong `sigmaPost` literal manifests as a timeout), then use more
   abstraction. One small `decide` per fact; reflect on the first-order
   write-log, never whnf Sail state; emit terms, not tactic scripts.
2. No `sorry`/`axiom`/`native_decide`/`bv_decide`. A genuine gap is a NAMED
   typed premise with a doc comment saying what supplies it.
3. If work feels duplicated/mechanical, STOP and report it — that is a signal
   an abstraction is missing. Build the abstraction (or name it precisely),
   then instantiate. Two similar proofs = factor before writing the third.
3b. THE MOMENT you notice a missing general fact ("no lemma for X, the
   practical way around is Y"), append an entry to
   `experiments/observations.md` (format at its top) BEFORE proceeding with
   any workaround. Entries on disk survive session/agent death; final reports
   don't. Noting a workaround there does not sanction it — the other laws
   still apply.
4. If a plan step is infeasible, return the machine-checked obstruction, not a
   workaround (precedent: the `Trichotomy` spec bug was FOUND as a falsity
   proof, then fixed by amendment — `Vsa/While/StmtDispatch.lean`).
5. Verify with `lake env lean <file>` only; never `lake build`, never LSP
   tools (they spawn racing builds). Axioms of every new theorem ⊆
   {propext, Classical.choice, Quot.sound}.
6. Complexity must be HIDDEN by shape, not navigated by hand. If you find
   yourself counting conjuncts (`h.2.2.2.2…`), tracking positional indices, or
   re-deriving where a fact sits inside a tower, STOP: the statement wants a
   named-field structure (new defs) or a named destructurer (landed defs).
   Positional navigation is fragile (reorders shift every index), slow to
   elaborate, and burns your turns — gate rules R6/R7 enforce this.

## Extending the discipline

- New enforced rule: append a TSV line to `scripts/discipline_rules.tsv`
  (id, glob, regex or `COUNT>N:needle`, message). No code changes.
- Genuine exception: `-- discipline: allow(<rule-id>) <justification>` on or
  above the line — visible and auditable.
- Legacy files are listed in `scripts/discipline_grandfather.txt`; shrink it
  as proofs are re-seated on the layer. Never add new files to it casually.
- New abstraction landed? Add it to the table above and, if bypassable by
  hand, add a rule that catches the hand version.
