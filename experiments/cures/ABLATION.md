# CEGIS decontamination ablation — `--blind`

The `cegis_cure.py` history acceptance (3× rank-1 rediscovery of the 47i / 48f /
48g cures, `--acceptance`) was CONTAMINATED: the tool's ambient inputs included
the observations.md / design docs that NAME those cures, and the per-case
"expected template" (`ACCEPT[].want`) was hand-written from that knowledge. So a
rank-1 rediscovery could be circular — the answer might have leaked in.

This ablation settles it by removing the answer-bearing inputs (`--blind`) and
keeping ONLY the inputs legitimately available at cure-DESIGN time.

## Input manifest (blind mode)

INCLUDED — the only two inputs, per case:

- **(a) the false statement Prop** — the `def … : Prop := <rhs>` body of the
  reconstructed pre-amendment statement (`experiments/cegis/AcceptX_*.lean`).
  Only the def body is read; the docstring prose (which mentions the cure) is
  ignored by the surface parser (`extract_def` / `split_binders` operate on the
  post-`:=` RHS).
- **(b) its machine-checked obstruction** — the refutation theorem + witness
  under `experiments/fleet/obstructions/`. This is a FACT about the statement
  (it is refutable, and here is the countermodel), legitimately available at
  cure-design time — NOT a doc that names or prescribes a cure.

EXCLUDED — answer-bearing, NOT read in blind mode:

- `experiments/observations.md` (the `cegis-cure-generator` entry names all three cures)
- `experiments/design/*` (MASTER.md + the 6 cluster designs)
- `experiments/REMAINING.md`
- `experiments/run1-brief.md` and the wave-4* logs
- **the `ACCEPT[].want` field** — the hand-written expected template (the
  contaminated ground truth of `--acceptance`)
- the `AcceptX_*.lean` docstrings (file is kept for the Prop; prose ignored)

In blind mode the expected template is **derived** from the obstruction by
`obstruction_signal`, not read from any prose (see below).

## Blind ranks vs contaminated ranks

| case | statement | obstruction | contaminated rank (`--acceptance`) | blind rank (`--blind`) |
|---|---|---|---|---|
| a. NegResid pre-47i | `AcceptA_Neg.lean` | `B2_Field_hNeg.lean` | **1** (entry-conditioning) | **1** (entry-conditioning) |
| b. BinArmExtras.mem_ext pre-48f | `AcceptB_MemExt.lean` | `BinArmExtrasMemExtOverquant.lean` | **1** (conjunct-deletion) | **1** (conjunct-deletion) |
| c. ∀-mcall pair | `AcceptC_McallPair.lean` | `UnaryLogicPresenceOverquant.lean` | **1** (guard/quant repair) | **1** (guard-repair) |

Ranks are identical under both the no-filter fast path and the full
Z3-refute + semantic filter stack. **Rank-1 SURVIVES blind in all three cases.**

## The obstruction → template signal (this is WHY blind works)

The templates were never selected from the docs. `detect_defects` chooses them
by regex over the STATEMENT's Prop text, and the obstruction's refutation
witness points at the same template independently — the countermodel exploits
exactly the structural defect a template repairs:

- **a (entry-conditioning):** the obstruction refutes `NegExtras.sp_headroom`
  (`SL.lo + 3264 ≤ sp.toNat`) at **`sp = 0#64`**. A headroom pin quantified over
  the entry `sp` with no entry linkage, refuted at `sp = 0`. The witness pins
  `SL`/`sp`/`m0` — which is precisely what inserting an entry hypothesis
  (`StackOK`/`EvalEntry`) supplies. Slot-pin-∅ / headroom-at-0 ⇒
  entry-conditioning.
- **b (conjunct-deletion / guard-repair):** the obstruction refutes the
  over-quantified `∀ m, agree-off-[SL.lo,sp) → MemExtends m0 m` with an
  **in-window empty adversary `m = ∅`**. A `∀`-window refutation of a
  block-supplied fact ⇒ delete it (block output supplies it) or flip the guard
  to a covering window that excludes the adversary.
- **c (quantifier-repair / guard-repair):** the obstruction refutes the total
  presence demand `∀ a, ∃ b, mcall[a]? = some b` with an **empty `mcall` at an
  in-window `a`**. An `∀`-totality refutation ⇒ footprint-bound the demand
  (quantifier repair) / demand agreement on a covering window (guard repair).

The signal is mechanical: **which ghost the witness sets to its degenerate value
(`sp=0`, `m=∅`, `mcall=∅`) names the repair.** A headroom/slot pin degenerated
to 0/∅ ⇒ entry-conditioning; an over-quantified `∀m`/`∀mcall` closure refuted by
an in-window empty adversary ⇒ deletion/guard/quantifier repair. The obstruction
alone drives the template selection; the docs were cosmetic.

## Verdict

**GENUINE.** The 3× rank-1 rediscovery is not an artifact of contamination.
When the answer-bearing docs and the hand-written `want` are removed, and the
expected template is derived purely from the statement + its machine-checked
obstruction, the real landed cure still lands at **rank 1 in all three cases**,
under the full filter stack. The obstruction→template signal is the mechanism:
the refutation witness's degenerate ghost points at the repairing template
without any prose.

Caveat (unchanged from the tool's own honesty note): on symbolic-window Resids
the Z3/semantic filters DEFER ("SMT territory / covered"), so within a case the
tool ranks by template + edit-cost rather than machine-refuting the amended
candidate. Blind mode validates that the *template selection* is answer-free; it
does not upgrade the intra-case ranking heuristic. Prospective validation on the
un-cured clusters (per the `cegis-acceptance-contamination` observation) remains
the strongest test and should still be run.

## Reproduce

```
python3 scripts/cegis_cure.py --blind                 # full filter stack
python3 scripts/cegis_cure.py --blind --no-smt --no-semantic   # fast path
```
