# Invariant generation on top of the fuzzer — plan (validated by experiment)

Design-time only: NOTHING here enters a proof. Mined/SMT-checked candidates are
seeds; every invariant still gets its pure Lean proof, gated by check_all
stage-b/c (banned-tactic scan + axiom audit). Same contract as the emulator
harness and statement fuzzer.

## Validation already done (2026-09-02, coordinator-run, artifacts in /tmp)

- **Trace hook**: the Lean emulator (exact proof model) hooked in ~30 min —
  `tracedLoop` in a COPY of riscv-lean (`/tmp/rl-trace`), dumping chosen regs
  at chosen PCs via `print_effect`; build green; ~6 s/run. (NEVER modify the
  real riscv-lean; regeneration recipe is pinned in memory.)
- **Flat Daikon mining** on the `_write` loop head (t5.elf, 13 iterations):
  found the constant putchar command word + all guard orderings; MISSED the
  linear relation because iterations span 5 call instances.
- **Segmented mining** (segment on frame change, intersect per-call invariant
  sets): recovers the COMPLETE hand-written `WInv` of the landed P1 fold —
  `a1` increments, `a1 < a3` guard, per-call constants, and the entry relation
  `a3 = a1 + a2`. The flagship result: a real landed loop invariant is fully
  minable from one 6-second run.

## Architecture (pipeline; each stage a scripts/ tool)

1. **`gen_trace.py`** — trace-harness generator. Input: case id from
   `experiments/corpus/INDEX.md` (gives loop-head/entry/exit PCs) + probe list
   (regs + mem windows). Emits the `tracedLoop` patch into a COW copy of the
   emulator, builds once per probe-set, runs the t5 `.wl` corpus (extend the
   corpus so every remaining case's code path is exercised — corpus INDEX
   knows which fields each case serves; a `.wl` program per case class).
   Structured JSONL out. Mem probes: dump 8-byte words at probed windows
   (arena slots, retslot, stack window edges).
2. **`segment.py`** — call-instance segmentation. General mechanism: track sp
   (frame) + ra at the traced PCs; segment when the frame changes (validated
   heuristic: any per-call-constant register works; sp is the principled one).
3. **`mine.py`** — tiered candidate mining, vocabulary from the corpus
   analysis (which regs/windows the case touches):
   T1 constants/per-call constants; T2 pairwise linear (a−b=k, a=b+c at
   entry); T3 monotone/strides; T4 guard orderings; T5 mem-window facts
   (word at probed slot = f(regs); region untouched across iteration).
   Intersect within segments, then across runs. Output: candidate conjunct
   list per case, tagged by tier.
4. **Relational (machine×spec) mining — the new part.** Run the SPEC side on
   the same programs (`Vsa/While` semantics is executable: `#eval` the
   interpreter on the AST, dumping spec states at eval/exec steps). ALIGN the
   two traces at seam points (call entries/exits — the same points the record
   fields quantify over; alignment key = the step index of eval events, which
   the machine side exposes as arm-entry PCs). Mine cross-side conjuncts:
   `gprGet a0 = reprOf (spec value)`, `store size relation`, `φ-frame count =
   machine frame count`, arena slot k ↔ store binding. These are exactly the
   Approx/Repr facts the bridge proofs state — mined instances tell us the
   TRUE statement shape before we write it.
5. **LLM seeding layer**: prompt = corpus case summary + the landed invariant
   zoo (WInv/WRGOk/SWGOk/loop templates as few-shot) + mined conjuncts →
   propose the STRUCTURED candidate (named-field Lean structure in repo
   idiom, including quantifier placement — the part mining can't do). The
   miner grounds it; the LLM shapes it. Where mining is silent (recursion
   depth relations, φ-rebasing), LLM proposes from the precedent zoo alone.
6. **CTI loop (the fuzzer, closing the circle)**: every candidate goes to
   `statement_fuzz.py` (witness search + z3 side-conditions) → REFUTED
   candidates return to the LLM with the witness (the repair prompt = the
   item-zero amendment shapes); SURVIVING candidates get the cheap
   inductiveness pre-check: symbolic body execution via the seg evaluator —
   `loopFromBody`'s obligation as a reflected `decide` on the candidate's
   decidable conjuncts. Only then does a proving agent see it.

## Contract with the proving pipeline

Output per case: `experiments/invariants/<case>.md` — the candidate structure
(Lean source block), mining evidence (which conjuncts trace-grounded, which
LLM-proposed), fuzz verdict, inductiveness pre-check result. Proving agents
consume these as DRAFTS; Law 4 still applies (a candidate failing in-proof =
new CTI, feed it back). The t5 corpus + proof-ELF sha guard rules apply to
all trace runs (build test ELFs only in /tmp copies).

## Order of attack (highest mining-yield first)

1. io flush chain loops (__sflush_r/_fflush_r/vfprintf digit loop) — pure
   machine loops, T1-T5 mining suffices, no relational needed.
2. exec-arm entry facts (the B5 supplier classes) — relational-lite: arm
   entry reg/slot facts vs spec statement kind; alignment trivial (one seam).
3. The Approx/store bridges (leaf/binop widening posts) — full relational
   mining; the highest-value target: these are the never-yet-factored
   per-instance semantic facts.
4. The crux (hCallClosure) recursion invariants — relational + LLM-heavy;
   mined depth/frame/budget relations from nested-call traces seed the
   statement (the stackBudget ladder would have been FOUND by depth-2 traces:
   sp_headroom demand visibly exceeds the constant at depth 2 — run that
   trace FIRST as the technique's acceptance test on history).

## Effort

Stages 1-3+6 are a day of tooling (validated primitives). Stage 4 alignment
is the research-y piece — bounded by starting relational-lite (single-seam
cases). Stage 5 is prompt engineering over existing artifacts. The
acceptance test on history (crux depth-trace refinding falsity #13) decides
how much to trust it before pointing it at unproven cases.
