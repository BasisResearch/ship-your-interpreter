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
| Straight-line machine run | `#derive_case` seg / `block_facts` / `chain_facts` (model: `Vsa/Sim/EnvDefSeg.lean` — 58 hand lines → 14) |
| ABI register frame on a run | `FrameMeta.abiFrame_of_wrChain` (one `decide`) — NEVER per-site frame threading |
| Memory-frame / footprint post | `FrameMeta.memFrame_of_chain` / `bblocks_sound_framed` |
| Framed variant of a callee spec | FrameMeta metatheorems over its reflected chain — NEVER re-run the chain with a ghost conjunct |
| Call splice (prefix ≫ callee ≫ suffix) | `callSeg`/`callSegConseq` (`DeriveCallSeg`) |
| Loop | `loopFromBody` (`DeriveLoop`) / the `LoopSteps` shapes |
| Error-site Triple | `#derive_error_site` table row |
| Recursor case row | the `gen_*_row.py` generators + TSV (TermRouting/ExecRouting/BinDispatchRow) |
| Exit widening | `LeafWiden`/`ExecRecWiden`/`EvalRecWiden`/`blockD_v_phic` |
| Store↔frame marshalling | `foundSt_of_storeRepr` / `frameRepr_append` |

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
4. If a plan step is infeasible, return the machine-checked obstruction, not a
   workaround (precedent: the `Trichotomy` spec bug was FOUND as a falsity
   proof, then fixed by amendment — `Vsa/While/StmtDispatch.lean`).
5. Verify with `lake env lean <file>` only; never `lake build`, never LSP
   tools (they spawn racing builds). Axioms of every new theorem ⊆
   {propext, Classical.choice, Quot.sound}.

## Extending the discipline

- New enforced rule: append a TSV line to `scripts/discipline_rules.tsv`
  (id, glob, regex or `COUNT>N:needle`, message). No code changes.
- Genuine exception: `-- discipline: allow(<rule-id>) <justification>` on or
  above the line — visible and auditable.
- Legacy files are listed in `scripts/discipline_grandfather.txt`; shrink it
  as proofs are re-seated on the layer. Never add new files to it casually.
- New abstraction landed? Add it to the table above and, if bypassable by
  hand, add a rule that catches the hand version.
