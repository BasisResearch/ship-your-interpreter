# OVERNIGHT FULL-CLOSE brief (RUN 1 + RUN 2 — the proof ends tonight)

GOAL: `endToEnd` UNCONDITIONAL by morning — RemainingWork premise-free,
ErrWork discharged, full check_all + axiom audit green, committed. Sequence
long poles FIRST. If something is genuinely blocked, the machine-checked
obstruction goes in the wave log — but exhaust the Law-3 move before calling
anything blocked.

You are executing RUN 1 of the two-run contract. The governing plan is
`experiments/post-tooling-fanout-plan.md` — read it FIRST, in full, plus the
last five entries of `experiments/observations.md` (buffering retraction,
empirical sweep, tester recipe) and `experiments/logs/gen-fn-tooling.md`'s
final section (the wave-46 baseline you build on: gen_fn/FnSummary/repack/
framed-genseg/gen_transport/AssemblySkeleton are ALL landed — use them).

CLAUDE.md governs everything. Work incrementally with one log per lane at
`experiments/logs/run1-<lane>.md`, observations at the moment of noticing,
falsity-test hand statements with the emulator harness BEFORE proving
(recipe in plan item 0′; NEVER build in c/ — proof ELF sha256-guarded:
b146c6edb76ea9a0f0f30be381f8176ed2de9717e1ae9b37feff4b2b9ca1d0f0).

## You are the ONLY writer to the main repo tonight

A field-discharge fleet (Claude workers in /tmp/vsa-fleet-* clones) may be
producing `Vsa/Sim/rows/Field_*.lean` files in parallel. They NEVER touch
main. At each of your gate points (and at the end): harvest any completed
clones — copy their `Field_*.lean` files in, verify each with
`lake env lean`, wire imports, plug green ones into
`termResidualsCore_of_skeleton` (rows/AssemblySkeleton.lean), and flip
`experiments/assembly_skeleton.tsv` rows hole→filled. Their logs are at
`<clone>/experiments/logs/fleet-*.md`. Do not wait on them; do not spawn
more of them.

FLEET-OWNED FIELDS (do NOT discharge these yourself tonight): B1 =
hInt/hNull/hBool/hStr, B2 = hNeg/hNot/hOrTrue/hAndFalse/hOrFalse/hAndTrue.
Exception: a field a fleet log records as SKIPPED (with its obstruction)
reverts to you — its obstruction note tells you what to build. Every OTHER
skeleton hole is yours if its suppliers exist (the io lane explicitly
discharges SkelHCallPrint/Println/AssertOk once its folds land).

## ITEM ZERO — THE RECORD AMENDMENT (found by the fleet tonight; gates ALL field work)

The B1/B2 fleet workers machine-checked a SYSTEMATIC falsity class in
`TermResidualsCore` (falsity #12): field statements ∀-close ghosts
(`sp`/`sret`/`m0`/`c : Config`) whose Extras/geometry conclusions demand
entry-side reality — refuted at `sp = 0`, `sret` inside the callee code
window, `m0 = ∅`. Machine-checked refutations + witnesses:
`/tmp/vsa-fleet-B1-leaves/experiments/fleet/obstructions/B1_leaves_obstructions.lean`
(hNull/hBool/hStr false; hInt = 2 named premises, missing `GeomFrom`) and
`/tmp/vsa-fleet-B2-unary-logic/Vsa/Sim/rows/Field_*.lean` (all 6 unary/logical
fields false via `*Extras.sp_headroom`). Amendment proposals are in BOTH
clones' `experiments/observations.md` tails (`b2-resid-fields-refutable`,
`leaf-resid-forall-ghost-falsity`).

B5 COMPLETES THE VERDICT: 11/14 exec-arm fields FALSE (slot pins
unconditioned under ∀ m0 — `StmtSlotPinned … ∅` refutes), 3 more mis-stated
(hSBlock/hSForStart/hSWhileBreak ∀-close `ExecSeqStep`/`ExecForStep`/
`ExecWhileStep` oracles that have NO producer and ARE the recursor's own IHs
— self-referential). Corollary landed in its clone:
`termResidualsCore_false : ∀ L, ¬ TermResidualsCore L` — THE RECORD IS
UNINHABITED AS STATED. Obstructions:
`/tmp/vsa-fleet-B5-execarms/Vsa/Sim/rows/B5ExecArmObstructions.lean`;
observations `exec-resid-slot-pins-uninhabited` +
`loop-geom-self-referential-oracles` (note: audit the EVAL-side
`KindSlotPinned` twins too).

B6 ADDS THE THIRD SHAPE (0/7 seq/for fields, two shared machine-checked
obstructions in `/tmp/vsa-fleet-B6-loopseq/Vsa/Sim/rows/B6LoopSeqObstruction.lean`):
`mExecSeq` quantifies entry `p`/exit `q` INDEPENDENTLY with a code-free
`SegEntry`, and `mForLoop` is identity-PC while every ForLoop constructor
mutates the store. This is the SAME disease `scaffold-motive-independent-pq`
already cured for `mExecInit`/`mForCond` (landed precedent, zero consumer
rethreading) — apply the same cure to `mExecSeq`/`mForLoop` (pin
p=execSeqLoopPC/q=execSeqContPC, honest distinct PCs for the for-loop; or a
SegEntry code-image field — their log has the path). Observations:
`seq-motive-independent-pq-no-code`, `forloop-motive-identity-pc-store-mutation`.

THE AMENDMENT HAS EXACTLY THREE SHAPES (apply uniformly, not per-field):
1. Byte-pin conditioning: `hslot`/`htableStk`/`StmtSlotPinned`/`KindSlotPinned`
   conjuncts get conditioned on a named `RodataPinned m0` (or the wave-43
   `groundSlot_k` shape) — entry-side reality as ONE named-field hypothesis.
2. Oracle threading: loop/seq IH-and-step obligations move OUT of the field
   statements and come FROM the recursor (they are the induction's own
   hypotheses — the scaffold-motive p/q precedent is the model).
3. Motive PC-pinning: `mExecSeq`/`mForLoop` get the scaffold-motive cure
   (concrete PC pins / SegEntry code field) — see the B6 block above.

A SANDBOX AGENT IS EXECUTING ITEM ZERO RIGHT NOW in /tmp/vsa-itemzero-sandbox
(log: experiments/logs/itemzero-sandbox.md in that clone): amendment design +
62-field audit + clone-validated apply + inhabitability evidence + the exact
ordered apply-list for you. HARVEST ITS RESULT FIRST — replay its apply-list
in main rather than redesigning. If it reports blocked or is still running
when you need it, its log is your starting point.

DO FIRST: (a) harvest ALL obstruction sets + observations into main;
(b) design ONE uniform amendment (condition the Resid/field statements on the
entry-side bundle — EvalEntry/ImageGeom/populated-m0 — as ONE named-field
hypothesis structure, NOT per-field ad-hoc guards); (c) AUDIT all 62 fields
for the class (B1's note predicts B5 `BrkResid`/`StmtSlotPinned` shares it —
expect B5/B6 worker reports to confirm); (d) apply, sandbox-validate, regen
`gen_assembly_skeleton.py` + `AssemblySkeleton.lean` + `field_census.py`;
(e) only THEN dispatch/discharge field work. The consumers instantiate at
real configs, so the amendment should thread with near-zero consumer changes
(scaffold-motive p/q precedent) — but verify, don't assume.

## Pre-lane items (do these after ITEM ZERO)

- **D0 residue (30 min, probed tonight)**: add MKinds `.xor` (RTYPE, clone
  the probed `.or` diff, `execute_rtype_xor_char` exists) + `.sllw` (RTYPEW,
  clone `.subw`, `execute_rtypew_sllw_char` exists); optionally `sll`/`srlw`/
  `sraw` for completeness. These appear in `_vfprintf_r`(xor×5)/`memchr`/
  `__call_exitprocs`(sllw) — the ONLY unhandled mnemonics in any needed
  function (binary-wide census 2026-09-01).
- **The wave-45 amendments**: a sandbox agent is validating the re-land RIGHT
  NOW in /tmp/vsa-amend-sandbox (log: experiments/logs/amend-sandbox.md in
  the clone; its final report enumerates the exact consumer-fix list).
  HARVEST ITS RESULT and apply in main FIRST — falsity-#9 gates
  crux-segexit → the hCallClosure crux. If its verdict is "blocked", that is
  your first Law-3 target of the night, before the io lane.
- **%lld reality**: `_svfprintf_r`(0x80007654) and `_vfprintf_r`(0x8000a884)
  are SEPARATE compilations — the landed snprintf %lld specs do NOT cover
  vfprintf's inner loop; it re-instantiates at vfprintf-local PCs. It is the
  night's longest pole: start it EARLY in the io lane (the digit loop is the
  gen_fn counted-loop template; mirror the snprintf spec statements).

## Lanes (dispatch ≤3 concurrent subagents, one lean process each; you may
run lanes serially if fleet workers are still consuming cores)

1. **io lane** (the priority): the output DAG bottom-up via gen_fn folds —
   `_putc_r`/`_fputc_r` → `__sfvwrite_r` (BOTH arms per the mapped route:
   unbuffered arm for real stdout, buffered arm ONLY under the __sbprintf
   synthetic FILE) → `_fputs_r`/`_fwrite_r` → shims → `__sbprintf` (57i) →
   the `_vfprintf_r` pinned fmt paths (exactly "%lld" + "%s"×2; entry →
   sbprintf detour at +0x39c) → splice into
   rows/ValuePrintContract's three contracts (TRUE AS STATED — empirically
   confirmed; do NOT restate them) → close the native
   print/println/assertOk rows → discharge SkelHCallPrint/Println/AssertOk.
2. **mech lane**: arm-dispatch instantiations (combinator landed wave 44);
   repack instantiations over the crux-marshal/stagepre/bridge-twin glue
   (`repack` tactic landed, RepackTac.lean); fn-seam ×4 via gen_fn;
   m4-linkage ×42 via the existing generator + COW fan-out precedent.
3. **decode lane**: Snprintf/MainError/Crt0Exit segments via gen_fn
   (crt0 Code module via gen_code_lemmas.py first); gen_layout.py jump-table
   slot pins for all tags.
4. **bridges lane**: the String.lt order bridge (`StrCmpOrderBridge`) + the
   stringify↔`Value.display` bridge. Direction empirically confirmed
   (observations `field-claims-empirical-sweep`); STRINGIFY PIN WARNING:
   trust ELF bytes, not prose — 19008="true", 19010="false" (the old doc had
   them swapped; fixed).

## Gates and definition of done

- Gate per lane-merge: `scripts/rbuild.sh check` (remote box; keep local
  light) — never local `lake build`.
- DISK + CPU hygiene: `rm -rf` each fleet clone AFTER harvesting it (verify
  its Field_* files green in MAIN first); cap concurrent /tmp clones at ~6;
  COW clones are cheap until they diverge (regenerated oleans are real
  blocks). Never open clone files in an editor (LSP → world rebuild).
- After each gate: re-run `python3 scripts/field_census.py -j4` — the FOUND
  count is the ONLY progress metric that counts. Log it each time.
- A surprise mid-run gets the Law-3 move (land the abstraction in-lane).
  A falsity gets the sandbox-validate→closure-regen→green treatment
  (GoodState precedent). The run may go LONG; it may not multiply.
## RUN 2 (same night, after the lanes)

5. **crux lane** (after amendments land): crux-segexit → crux marshalling
   (repack) → rows/CallClosureRow → discharge SkelHCallClosure. The single
   hardest field; budget accordingly.
6. **err lane**: m4-linkage ×42 (existing generator + COW fan-out precedent),
   MainErrorSeg/Crt0ExitSeg via gen_fn (+ crt0 Code module), SnprintfContract
   closure, hBadClosure + hTopAbrupt bespoke.
7. **oracle sweep**: remaining skeleton holes as their suppliers land
   (hVar/hAssign/hInitStore/hEpilogueSpill/hDivOv/hDivCorr + anything the
   fleet skipped); falsity-test each hand statement first (emulator recipe).
8. **FINAL ASSEMBLY**: plug all Skel holes into termResidualsCore_of_skeleton,
   build ErrWork, construct RemainingWork premise-free, make `endToEnd`
   UNCONDITIONAL. Full check_all + axiom audit. Update
   assembly_skeleton.tsv + field census (should read 62 FOUND).

- DONE = endToEnd unconditional + check_all green + ONE commit (Wave 47:
  THE CLOSE) + wave log with census before/after + anything genuinely
  blocked listed with its machine-checked obstruction.
