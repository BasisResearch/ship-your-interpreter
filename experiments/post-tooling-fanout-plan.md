# Post-tooling closure (plan b) — TWO Fable runs

PRECONDITION: `experiments/gen-fn-tooling-plan.md` landed (gen_fn.py +
FnSummary + pilots `_write`/`_write_r`/`__swrite` green).

Surface (measured 2026-09-01): 63 `TermResidualsCore` fields, `ErrWork` =
42 linkages + 3 segments + 2 passthroughs, 43 open `residuals.tsv` rows.
De-risk pass results baked in below: htif putchar lemma DONE (`Htif.lean`),
value_print arms + contracts + dispatch (mkind-lwu) landed, arm-dispatch
combinator landed wave 44 (instantiations remain), exit-path flush confirmed
(`exit`@0x80004764 → `__call_exitprocs` → `jalr` reent `__cleanup` →
`_fflush_r`), stdout LINE-BUFFERED (`_isatty` = `slti a0,a0,3` → tty for fds
0-2), and **falsity #10 found statically**: the three IO contracts in
`rows/ValuePrintContract.lean` post immediate `output ++ frag`, unprovable
under buffering — observation `io-contracts-buffering-falsity` has the full
amendment recipe. Item 0 below re-states them BEFORE anything consumes them.

The per-item loop everywhere: write TOML/args → run generator
(self-verifying) → wire import → `lake env lean` consumer → flip ledger row.
Any "minutes" item exceeding ~an hour = missing-abstraction signal (Law 3):
STOP, log, name the combinator, land it first.

## THE TWO-RUN CONTRACT (why past "2-3 waves" became 12 — and the countermeasure)

Runs break when discovery happens MID-run: a falsity found while proving, a
missing tool forcing hand-work, a marshalling gap surfacing at assembly time.
Each is moved BEFORE its run:

- **Tooling-run tail (extend the in-flight run; no tool-building inside RUN 1)**:
  (t1) repack marshaller; (t2) genseg `framed = true`/`avoid` emission
  (`bridgeOfSegFramed`); (t3) the per-byte code/pin transport emitter
  (P2's `writeLoaded_of_agree_lo` class — flagged scriptable in its log);
  (t4) `gen_code_lemmas.py` discipline-allow emission; (t5) **the falsity
  sweep**: concrete-trace-test EVERY statement RUN 1 consumes (StreamRepr
  contracts, io-callee preconditions, fn-seam statements, the stringify pin
  addresses vs ELF bytes) and batch-amend GoodState-style (sandbox → closure
  regen → green) BEFORE RUN 1 starts; (t6) **the assembly skeleton**: script-emit
  the 63 `TermResidualsCore` field-discharge stubs with named holes NOW, so
  every supplier↔field marshalling gap is a visible RUN-1 work-list item, not
  a RUN-2 surprise. The unification question is now ASKED MECHANICALLY:
  `scripts/field_census.py` probes every field with `example : <type> := by
  exact?` (~3s each, -j4). BASELINE (2026-09-01, in
  `experiments/field-census.tsv`): **63/63 NOT_FOUND — zero one-term
  discharges exist; every field is marshalling work** (even doc-LANDED
  hVar/hEq/hSeqNil: their landed pieces are sub-suppliers, not field-shaped).
  t6's skeleton supplies the marshalling terms; RE-RUN the census after each
  RUN-1 lane merge — fields flipping NOT_FOUND→FOUND is the assembly
  burn-down metric (trustworthy, unlike doc markers or wave counts).
- **Inside a run, a surprise gets the Law-3 move** (land the abstraction inside
  the run, in-lane), never a new run. A run may run LONG; it may not multiply.

## RUN 1 — mechanical closure (one Fable session, fleet ≤3 lanes inside)

**Item 0 — CANCELLED (empirically retracted 2026-09-01; see observations
`io-buffering-falsity-RETRACTED`).** `main.c:155` = `setvbuf(stdout, NULL,
_IONBF, 0)`, main's FIRST statement (jal@0x800045ac → setvbuf@0x800058c0):
stdout is UNBUFFERED. Confirmed in the Sail model (emulator runs; "1" precedes
a stderr error message; every value_print arm emits exact bytes). The wave-44
contracts' immediate-append posts are TRUE AS STATED — no StreamRepr, no
conOut, no re-seat. What replaces item 0: the io contracts' Pre pins the
stdout FILE state as left by main's setvbuf (__SNBF flag + 1-byte _nbuf) —
one named-field state pin, part of the main-init image the induction already
parameterizes (EntryImage/hInitStore class). Bonus simplifications now in
effect: `__sfvwrite_r` pins to the UNBUFFERED branch (no memchr line scan, no
`_fflush_r`, no `_malloc_r` warm-up on the path) — it drops from
bounded-heavy to ordinary; the exit-time flush is a no-op for stdout.

**Item 0′ (NEW, cheap, mandatory): the empirical falsity tester (t5) is LIVE.**
Recipe: craft `.wl` → `make riscv-htif HTIF_SCRIPT=...` in a /tmp COPY of
`c/` (NEVER build in `c/` — the proof ELF is the object; sha256 guard
b146c6ed…, verify after any session) → `riscv-lean/lean_emulator/.lake/build/
bin/lean_riscv_emulator <elf>` (~10 s) → compare output/exit. Run it over
every hand statement RUN 1 consumes BEFORE proving.

**Lane io — the output DAG, bottom-up gen_fn runs** (after item 0):
`_putc_r`/`_fputc_r` (52i) → `__sfvwrite_r` → `_fputs_r` (82i) /
`_fwrite_r` (122i) → shims (7–22i) → `_vfprintf_r` fmt family → splice into
the landed value_print/NativeBodyPrint layer → close hCallPrint/hCallPrintln/
hCallAssertOk + io-callee(5) + native-serial(4) rows.
One bounded-heavy sub-item remains (a focused sub-lane inside RUN 1), with
the route now FULLY mapped (static probe 2026-09-01):
- **The fprintf-family route takes the `__sbprintf` detour** (guarded call at
  `_vfprintf_r+0x39c` = 0x8000ac20; newlib unbuffered+write streams take it):
  `_vfprintf_r` entry → `__sbprintf` (57i/3b: builds a SYNTHETIC stack FILE —
  every field a concrete write, the nicest possible pinning) → recursive
  `_vfprintf_r` on the fake BUFFERED file → `__sfvwrite_r` BUFFERED arm
  (memcpy-into-stack-buffer path; under the fake FILE all bounds concrete) →
  `_fflush_r`/`__sflush_r` → `__swrite` (swrite_summary LANDED). So:
  - `__sfvwrite_r` needs BOTH arms, each under a concrete pin set:
    UNBUFFERED arm for fputs/fwrite callers (real stdout, __SNBF via
    main's setvbuf), BUFFERED arm ONLY under the __sbprintf synthetic FILE.
  - lock init/close stubs on the sbprintf path (check they're ret-stubs like
    the retarget locks elsewhere; if so, trivial segs).
  Split at internal loop heads into 2–3 gen_fn runs if >20 branches survive
  pinning. Empirical anchor: `print(3)` traverses this ENTIRE route in the
  model and emits "3" (t5/t6 corpus) — the path is known-good end-to-end.
- `_vfprintf_r` (3395i/392b): NEVER whole — exactly THREE reachable fmts,
  TWO shapes (confirmed from `ValuePrintArms.lean` doc rows):
  `"%lld"`@0x800192c0 (the solved snprintf recipe), `"<fn %s>"`@0x800192c8 and
  `"<native %s>"`@0x800192d8 (one `%s` shape, two instances). No float/dtoa/
  malloc fmt paths are reachable. One pinned gen_fn run per shape.

**Lane mech — everything with a landed generator/combinator (parallel):**
- arm-dispatch instantiations ×5+4 (combinator landed wave 44:
  `rows/ArmDispatchCombinator{,Exec}.lean` + LayoutJumpTableGen pins).
- repack marshaller (the ONE new tool in this run: field-matching bundle→bundle
  metaprogram over the R6/R7 named-field structures) + its instantiations:
  crux-marshal(5), stagepre-marshal(1), bridge-twin(2), SqEntry/noneval twins.
- m4-linkage ×42: existing generator + the `error-site-fanout` COW-clone
  protocol, one orchestrated run.
- fn-seam ×4: gen_fn runs over the alloc-build spans.

**Lane decode — stragglers:** Snprintf/MainError/Crt0Exit segments via gen_fn
(crt0 needs a Code module via gen_layout.py first; mainerr-frame dischargeable
from existing MainLoaded); extend gen_layout.py to emit ALL jump-table slot
pins at once (m6-layout ×2).

**Lane bridges (moved UP from RUN 2 — independent of io, pure semantic lane):**
the `String.lt` order bridge (`StrCmpOrderBridge`) + the stringify↔
`Value.display` bridge. The only two lemmas left with genuine String-theory
content (no Mathlib); giving them a full RUN-1 lane keeps RUN 2 near-pure
assembly.

RUN 1 exit criteria: every generator-class ledger row flipped; the io DAG
summaries land in the value_print contracts; check_all green; a written list
of every hole RUN 1 could not close (must be ⊆ RUN 2's list below, else STOP
and report the delta).

## RUN 2 — semantic close + assembly (one Fable session, mostly serial)

1. The 2 wave-45 amendments (falsity-#9 ratify, sentryc re-seat) — re-land
   from their wave-45 log checklists; falsity-test first.
2. Order-bridge maths: `StrCmpOrderBridge` (String.lt agreement) + the
   stringify bridge (snprintf buffer ↔ `Value.display`) → unblocks
   StrConcatCellResid/hStrAddL/R + stringify-conditional blocks.
3. err-stragglers: hBadClosure, hTopAbrupt (non-jal passthroughs).
4. Composition oracles, closed as their RUN-1 inputs land: hInitStore,
   hDivCorr (ArmStages board), hEpilogueSpill, var/assign rows, for-loop GAPs,
   + any invariant holes reported by the tooling pass.
5. **Assembly + audit**: discharge `RemainingWork` fields until the record is
   premise-free — the 63-field count MUST visibly shrink here (it moved 0 in
   waves 40–45; this is the only trustworthy progress metric). Then `ErrWork`.
   End: `endToEnd` unconditional, full check_all + axiom audit, shrink
   `discipline_grandfather.txt`.

## Honest sizing

RUN 1 is wide but every item has a landed tool + a worked precedent; the two
heavy sub-items are bounded by pinning and have solved-shape recipes. RUN 2 is
~10 bespoke lemmas + mechanical assembly. Residual risks after the de-risk
pass: (a) elaboration behaviour of the gen_fn join fold — measured by the
tooling pilots BEFORE these runs start; (b) further statement falsities — cut
off by falsity-testing every hand statement before proving (items 0, RUN-2.1);
(c) an unrecognised loop shape somewhere in the io DAG — degrades to a named
hole, lands in RUN 2.4. The decoder-coverage risk is CLOSED: the full-DAG
mnemonic census (observation `mkind-io-census`) found all 13 missing MKinds,
now plan-a Deliverable D0 with three landed precedents; no io routine uses
anything outside MKind∪D0∪pseudo-ops∪branch/jal/jalr terminators. Nothing
else identified.
