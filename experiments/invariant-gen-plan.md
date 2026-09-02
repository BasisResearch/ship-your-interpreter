# Invariant generation on top of the fuzzer — plan (validated by experiment)

> **RECONCILED @ea30e22 (2026-09-02): rounds 1-4 VERIFIED against the tree.**
> Round-4 batch numbers (54 mined+SURVIVED / 17 mining-silent / 26 no-trace-path,
> 0 contradictions) match `invariants/BATCH-REPORT.md` and commit ba31032
> field-for-field. No correction needed. Open items honestly recorded in "What
> remains" (value-repr arm-exit probe, driver call-descent, io-loop mining, LLM
> seeding) are still open in the tree.


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

## Validation round 2 (2026-09-02) — END-TO-END on real cases

Artifacts: `scripts/mine_stack_ladder.py`, `scripts/mine_loop_inv.py`,
`experiments/invariants/io_write_{loop,fuzz,skeleton}.lean`. Trace hook edited
in `/tmp/rl-trace` (probe list only); test ELF `rec_fib.elf` built in
`/tmp/wl-test`. All Lean axiom-clean (⊆ {propext, Classical.choice, Quot.sound}).

**Exp 1 — MINING acceptance on history (falsity #13): PASS.** Traced `fib(4)`
at eval_expr entry 0x80003164 probing sp; 82 entries, reconstructed call
nesting to depth 14 from the sp stack discipline. Miner recovered BOTH machine
frame constants — 1088 (`evalFrame`) and 176 (`execFrame`), matching
`StackNeed.lean` exactly — and the demand ladder `consumed(d) = d·perLevel +
base`. **The constant budget 2176 is exceeded at depth 2 (demand 2208 > 2176)**
— falsity #13's exact class boundary, refound from traces alone. The technique
would have caught #13 before the proof stalled.

**Exp 2 — full loop on an io case: PASS.** Traced the `_write` byte loop (head
0x8000004c, the landed P1 fold's loop) on t5.elf; 13 visits / 5 call-instance
segments. Segmented mining (segment on a3=end constant) recovered the complete
`WInv`: guard `a1<a3`, stride `a1'=a1+1`, entry relation `a3 = a1_entry + a2`,
per-call constants a2/a3/a4, and the GLOBAL putchar-cmd word a4=0x0101…000.
Expressed as `WInvMined` (8-field structure, WInv idiom) → **fuzzer SURVIVED**
(candidate provably self-consistent, axiom-clean).

**Obligation size measurement.** `loopFromBody` collapses the whole loop to
ONE per-iteration body obligation (`write_body_step`). Its arithmetic core =
**3 sub-goals, 4 proof lines, all omega/rfl** (skeleton closes GREEN). The
whole-loop total-correctness fold, exit, and measure recursion are produced by
the combinator — the prover writes none of it. Residual for the REAL
instantiation = only the 5-instruction machine back-edge run (0x4c..0x60) via
`bblock_sound_bt` + the tohost SEAM, both already-landed abstractions. Contrast:
the hand-written `FnWriteFold.lean` fold is 873 lines. **"Small obligation"
claim CONFIRMED: mining + fuzz + loopFromBody reduce a 873-line fold to a
~4-line arithmetic residual plus a drop-in back-edge lemma.**

**Exp 3 — fuzzer robustness (CTI loop live): PASS.** Three mutations of the
mined invariant, each REFUTED axiom-free by witness (`io_write_fuzz.lean`):
(1) DROP the `a1<a3` guard field → refuted by k=len witness (cursor at end);
(2) WIDEN the measure constant to `len-k+1` → refuted by k=0,len=3 witness;
(3) SWAP the bound to `a3<a1` → refuted by the same witness. The CTI loop
(candidate → witness → repair) is demonstrated end-to-end.

### Plan corrections

- **Fuzzer entry-point gap (real).** `statement_fuzz.py` returned UNDECIDABLE on
  the hermetic candidate: (a) `experiments/` is not on the Lean lib roots so
  `--import experiments.invariants.…` doesn't resolve, and (b) the binder-type→
  witness table has no entry for a case-specific ghost struct (`WG`). The
  robust path used here — emit the `¬mutant` probes as axiom-clean theorems
  directly (the fuzzer's OWN acceptance idiom) — worked for all 4. FIX before
  stage 6 scale-out: teach `statement_fuzz.py` to (i) accept a `--file <path>`
  hermetic module and (ii) synthesize witnesses for the candidate's own ghost
  struct by reading its field types (constructor `⟨…⟩` from the per-field
  table), not only the repo's fixed Layout telescope.
- **Miner interleaving (minor).** The naive two-point slope fit was polluted by
  the interleaved exec_stmt (176) frames between eval (1088) levels; least-
  squares over all depths + the delta histogram cleanly separates the two frame
  constants. gen `mine.py` T3 should histogram strides, not diff endpoints.
- Otherwise the pipeline shape holds: T1–T4 mining suffices for the io loop
  (stage-1 claim confirmed), and `loopFromBody` delivers the promised residual
  collapse. Relational (stage 4) untested this round — still the open risk.

## Validation round 3 (2026-09-02) — PRODUCTIONIZED + RELATIONAL PILOT

Stages 1-3 productionized as generic scripts/ tools; the stage-4 relational
core risk retired on the brk/cont exec arms.

**Productionized tool list.**
- `scripts/gen_trace.py` — case-id (+ `--pc`/`--regs`/`--mem` or built-in CASES
  table) → rewrites the `tracedLoop` probe in the COW emulator copy
  (`/tmp/rl-trace`, patches **LeanRiscv.lean** not Main.lean), builds the test
  ELF from a `.wl` program in `/tmp/wl-test`, builds the emulator once per
  probe-set, runs, emits structured JSONL. Mem windows read via
  `Sail.ConcurrencyInterfaceV1.PreSail.readByte` (byte-dumped, miner assembles
  the LE word). Multi-PC probes supported.
- `scripts/segment.py` — call-instance segmentation on a per-call-constant key
  (sp by default; `--stride` for cursor-restart io loops). Library + CLI.
- `scripts/mine.py` — tiered T1–T5 mining, corpus-vocabulary–scoped
  (`--case` reads "regs written on slice" from the corpus card). **Round-2
  corrections folded in:** (1) T3 STRIDE HISTOGRAMMING — the whole-trace sp
  |Δ| histogram cleanly separates evalFrame **1088** (35×) and execFrame
  **176**, where the naive endpoint slope smeared them; verified on the fib
  ladder. (2) case vocabulary. Subsumes both hand miners: recovers the io
  `WInv` (guard `a1<a3`, stride `a1'=a1+1`, entry `a3=a1+len`, global cmd word)
  and the falsity-#13 frame ladder.
- `scripts/mine_relational.py` — stage-4 machine×spec pairing.
- `experiments/spec_trace_brkcont.lean` — `#eval` spec-side driver (executable
  mirror of the WHILE relation over the pilot subset; imports the REAL
  `kindOfStmt`/`Stmt`), dumps `(kindOfStmt, frames, depth)` per exec-step.
- `statement_fuzz.py` **round-2 correction 1 APPLIED**: `--file <path>` hermetic
  mode (elaborates a module directly, no experiments/ lib-root import needed) +
  `--struct` field-type witness synthesis (parses `#check @S.mk`, builds the
  `⟨…⟩` constructor witness, checks INHABITEDNESS = self-consistency). Both
  gaps the round-2 UNDECIDABLE hit are closed.

**RELATIONAL PILOT VERDICT: PASS (mined facts MATCH the landed bridge shape).**
Machine trace @ dispatch `0x80004014` (probing `s0`=aStmt + `read32[aStmt]`)
× spec `kindOfStmt` trace on `while.wl`, aligned by kind tag:
brk(7) machine 1 = spec 1 = arm-entry 1; cont(8) 50 = 50 = 50; if(3) 201 = 201.
The two mined conjuncts —
`read32 m aStmt = some (kindOfStmt s)` and `StmtSlotPinned {7,8} {execArmBrk,
execArmCont} m` — are **field-for-field** the LANDED bridge: `stmtRepr_kind`
(`ExecDispatch.lean:84`) and `StmtTablePins.slot7/.slot8` (`ExecEntry.lean:202-203`,
def at `:178` = `stmtJumpTableBase + sext slotWord = armPC`). Mining found the
true statement shape before writing it. CTI loop live: hermetic candidate
`exec_brk_bridge.lean` SURVIVES (inhabited), mutant (slot mis-tagged) REFUTED
axiom-free. Artifact: `experiments/invariants/exec_brkcont_relational.md`.

**What remains untested.**
- Relational mining on the HARDER classes: stage-3 Approx/store bridges (leaf/
  binop widening posts — `gprGet a0 = reprOf value`, φ-frame counts) and the
  stage-4 crux `hCallClosure` depth/budget relations. The pilot was
  relational-LITE (single seam, discriminating integer tag; alignment by tag +
  count, not a full event-index zip). A multi-seam case (env-seam `hCall`,
  `hSVarInit`) needs a real per-event alignment key, not tag-histogram matching.
- Value-repr conjuncts (`reg ↔ reprOf(spec value)`) need the spec driver to
  emit the actual `Value`/its repr, and the machine probe to dump the boxed
  pointer + read back the payload — deeper than the integer kind tag mined here.
- Stage-5 LLM seeding is unexercised (structured-candidate synthesis from the
  invariant zoo); the pilot hand-wrote the ghost struct the LLM would propose.
- The `#eval` spec driver is a hand-transcribed AST + a subset interpreter, not
  a `.wl` parser feeding the full relational semantics; a general driver must
  parse the same `.wl` the machine runs and cover all stmt/expr forms.

## Validation round 4 (2026-09-02) — GENERAL DRIVER + BATCH ACROSS ALL 97 CASES

Gaps 2 (relational generality) and 3 (orchestration) closed; batch-run over the
full corpus with ZERO LLM calls.  New tools: `scripts/wl_to_lean.py` (a `.wl`→
real-`Vsa.While`-AST transpiler — the While layer has NO Lean parser, so this
supplies the AST the machine also runs), `scripts/spec_trace_driver.lean.tmpl`
(a GENERAL executable spec-trace driver over the real `kindOfStmt`/`Expr`/`Value`,
replacing round-3's hand-transcribed brkcont mirror; dumps event-index / stmt+
expr kind / depth / store size / value-repr per step), an upgraded
`scripts/mine_relational.py` (gap-1b PER-SEAM ORDINAL alignment — Nth machine
dispatch of kind K ↔ Nth spec event of kind K, a real per-event key not tag
histograms; gap-1c value-repr scaffolding), and `scripts/invgen.py` (the
one-command orchestrator + `--batch <cluster|all>`, with a self-fuzz CTI step).

**Gap-1a — general driver: PASS.** The transpiler round-trips all 10 corpus `.wl`
programs into terms that elaborate against the real AST; the driver `#eval`s them
(while.wl → 2425 events, arithmetic → 112, scope → 103, strings → 52).  The
brk(7)/cont(8) counts reproduce the round-3 pilot exactly (50 cont), confirming
the general driver subsumes the hand-written one.

**Gap-1b — multi-seam ordinal alignment: PASS, STRONGER than round 3.** On
while.wl the machine dispatch trace (636 events @ exec 0x80004014) vs the spec
trace agree machine==spec on ALL SEVEN stmt kinds (expr 195, block 174, ifStmt
201, whileStmt 6, varDecl 9, brk 1, cont 50) — not just the 3 discriminating
tags of the pilot.  On arithmetic.wl the EVAL side (dispatch 0x80003164, node
kind@[a2]) agrees on all 8 expr kinds present (int 39, binary 21, var 12, call
12, logical/bool/str/unary 4).  The mined conjunct `read32[node] &&& 0xff =
kindOf{Stmt,Expr} node` is the genuine `stmtRepr_kind`/`ExprRepr` kind bridge,
found field-for-field before writing it.

**Gap-1c — value-repr: SCAFFOLDED, honestly gated.** The driver emits `vtag`/
`vint` per eval step, but the machine value-readback probe at the DISPATCH PC
reads the node's operand field, not the boxed result (that is a0 at the ARM
EXIT).  Probing value-repr at dispatch produces spurious mismatches, so it is
DISABLED and recorded (observations.md `value-repr-needs-arm-exit-probe`): the
kind bridge is the solid mined fact; value-repr needs one extra arm-exit trace
PC per arm (mechanical, not wired this batch).

**Gap 2/3 — orchestration + BATCH: PASS.** `invgen.py --batch all` ran all 97
cases in one loop (ELFs built to SCRATCH names via the auto-found xpack cross-gcc,
tracked `c/while-riscv-htif.elf` restored after each; one emulator build + one
machine trace per PROBE-SET, cached — the 36 loop-arm cases share ONE trace).
Per-case artifacts `experiments/invariants/<case>.{md,lean}` + `BATCH-REPORT.md`.
The CTI loop is BUILT INTO the generator: every relational candidate is emitted
as an inhabitable hermetic ghost struct (`KindBridge` + the mined tag pairing +
a perturbed mutant) and auto-fuzzed in the same pass (`statement_fuzz.py --file
--struct` witness synthesis, `--no-fuzz` to skip); verdicts are fuzz-qualified.
Coverage: **54 candidate-mined+SURVIVED** (loop-arm 36, env-seam 13, loop 2,
leaf-slot/str-seam/value-box-tail 1 each — every one carrying a machine==spec
kind bridge; every mined candidate SURVIVED its fuzz, every mutant REFUTED
axiom-free), **17 mining-silent-needs-LLM** (io-* machine loops with no wired
kind seam), **26 no-trace-path** (error-jal-seam 19 + straight-span 6 + oracle 1
— no spec seam by construction).

**Contradiction shortlist: EMPTY (no pre-proof falsity this run).** No mined fact
contradicted a design-pass shape — the kind bridges all AGREE with the landed
`kindOfStmt`/`kindOfExpr`, which is the correct, expected outcome (these fields
are already proven-shaped).  The 13 env-seam call cases show an informational
KIND-COUNT DIVERGENCE (machine > spec on ret/binary) that is a DRIVER LIMITATION
(the driver evaluates `.call` opaquely, not descending into callee bodies), NOT a
machine falsity — the miner correctly refuses to flag it as a contradiction
(observations.md `spec-driver-call-opacity`).  The value-repr contradiction
channel (the highest-value falsity-catcher) awaits the arm-exit probe.

**Pro offload: NOT PRACTICABLE this run.** The Pro is DERP-only (LAN down); the
machine trace depends on the 167 MB warm-`.lake` COW emulator + the `/tmp/rl-trace`
and `/tmp/wl-test` state, none of which `rbuild.sh` syncs (it excludes `.lake`).
Syncing the emulator over DERP would dwarf the ~13 s/probe-set local cost.  Ran
locally, reniced (+10), ≤2 lean processes; graceful fallback as specified.

**What remains (honest).**  (1) value-repr arm-exit probe (one PC/arm) → the
`gprGet a0 = reprOf value` conjunct + its contradiction channel.  (2) driver call
descent (frame push + closure body under a depth counter) → the env-seam callee
conjuncts and the crux `hCallClosure` depth/budget relations (the falsity-#13
class).  (3) io-* machine-loop mining (per-case loop-head kind probe).  (4)
stage-5 LLM seeding remains the only non-mechanical stage, unexercised by design.

> COORDINATOR NOTE for the SMT-layer builder (read before designing the
> encoder): PREFER a Lean-side `dump_smt_lib` EXPORT TACTIC over a Python
> source-parser as the encoder core. Rationale: it walks the ELABORATED goal
> Expr (real semantics, no re-parse drift), can whnf/unfold reducible window
> predicates (agree-off-W/MemExtends/StackOK) to arithmetic form before
> emitting, and leaves genuinely-semantic predicates (ValueRepr/CString/
> GoodState) as uninterpreted symbols — the opaque boundary becomes a
> principled unfolding policy instead of a hand-list. It PROVES NOTHING
> (pure exporter writing SMT-LIB to a file; the goal is then admitted/failed
> normally) so Law 2 is untouched; metaprogram precedents: RepackTac.lean,
> ChainFactsTac.lean. The .lean tactic file may live under experiments/
> (elaborated via `lake env lean`, never wired into Vsa.lean). Python side
> then shrinks to: invoke probe → run z3 → replay countermodels via the
> statement_fuzz witness idiom. The ENCODING-GAP verdict class stays (a
> replay failure still indicates an export bug).

## Fuzzer v2: descent

`statement_fuzz.py --descend [depth]` (default 2) adds NESTED-QUANTIFIER
WITNESS DESCENT — the gap that let the ∀-mcall over-quant class pass `--file`
fuzzing while the hand-provers refuted it (experiments/fleet/obstructions/
UnaryLogic{MemExt,Presence}Overquant.lean, BinArmExtras{MemExt,FramePop}*.lean,
X2_Field_hIAdd.lean). v1 only instantiated the OUTER telescope; it was blind to
conjuncts of shape `∀ mcall, (mcall agrees with m0 off [SL.lo,sp)) → <presence/
extends demand>`, which are refuted by an `mcall` that differs from `m0` INSIDE
the window (where the agree-hyp says nothing).

- **Mechanism.** After outer-telescope instantiation, descent projects into the
  goal body's ∧-tree (a `first|` cascade over projection paths × ∀-arities, so
  no statement's shape is hard-coded), instantiates the nested conjunct's own
  telescope ADVERSARIALLY, and emits a `¬P` probe machine-checked by
  `lake env lean` (REFUTED ⟺ axioms ⊆ {propext, Classical.choice, Quot.sound}).
- **Adversary-builder table (2 entries), pattern→builder, extensible.** Each
  matches a conclusion shape and supplies the lethal inner witness + a
  conclusion-refuter (the hand files ARE the parameterized templates):
  * `memext` — `MemExtends m0 mcall`: m0 has a byte at 0∈W, adversary `mcall=∅`
    erases it (UnaryLogicMemExt / BinArmExtrasMemExt).
  * `presence` — `∃b, mcall[a]?=some b` on a window ⊆[SL.lo,sp): adversary `∅`,
    a=0 in-window (sp=1120 ⇒ sp-1120=0); covers both the two-disjunct presence
    conjunct (UnaryLogicPresence) and the single-window frame_pop
    (BinArmExtrasFramePop). More shapes (`MemExtends _ demand`→∅, byte-presence
    at addrs→erase, reg-liveness→config with reg absent) drop in as table rows.
- **Acceptance-v2 (`--acceptance-v2`, hard gate).** (a) REFUTES the pre-48f
  over-quant conjuncts reconstructed hermetically (PreMemExt/PrePresence,
  mirroring d7a5c91^ BinArmExtras.mem_ext + 17773c4^ TermRouting ∀-mcall pair);
  (b) does NOT refute the current guarded survivors (CurMemExt/CurPresence,
  agree-on-ALL ⇒ demand, the 48f/48g cure shape); (c) v1 acceptance unchanged
  (no regression). PLUS a non-gating LIVE probe that re-reads HEAD's real
  `TermRouting.NegResid` mem_ext conjunct: currently REFUTED (the raw ∀-mcall
  pair is still on main — wave 48f only dropped the BinArmExtras copy; see
  experiments/observations.md 2026-09-02 fuzzer-descend-live-negresid).
- **Wired into invgen autofuzz.** `invgen.autofuzz` runs a SECOND `--descend`
  pass on the mined Prop whenever it mentions `mcall`/`MemExtends`; a descent
  REFUTED that the struct-witness pass called SURVIVED WINS (records the
  contradiction), closing the ∀-mcall blind spot in the built-in CTI step.
