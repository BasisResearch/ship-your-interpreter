# Lane V: adversarial soundness review of `endToEnd_refinement` (paper §9.3)

Branch `lane-v` (from `hub/iris-main` `286c2ad`). Report: `REVIEW.md`.
Tooling and evidence: `experiments/review-v/`.

## Status: done (review written; P5 and P6 landed; P1–P4 handed to lanes B1–B3)

`lake build Vsa VsaIris` green (2587 jobs after the dead-code deletion).
`scripts/check_final_axioms.sh` (new): the final theorem and its boundary
witnesses depend on `[propext, Classical.choice, Quot.sound]` only.
`scripts/check_all.sh --static-only` green (stage a4 was failing at
`hub/iris-main`). `check_iris_holes.py`: 10 ledgered holes, unchanged. The
stage-c sweep over the trimmed `THEOREMS` list: 1037/1037 audited, allowed
axioms only.

## Findings (ranked; details and evidence in `REVIEW.md`)

- **C1 (critical, vacuity).** `ConsoleStream.flags = 0x200a` is false at
  `interp_run`'s entry (real: `0x000a`; `__SORD` is set by the first console
  write after entry). `Loaded interpRunLayout p c` holds for no configuration
  the binary reaches, for any program.
- **C2 (critical, ∀ p).** `FixedRodataLoaded` pins the embedded script
  (`_script_start = 0x80018be0`), so only the `while.wl` build can be
  `Loaded`; no proof reads a script byte.
- **C3 (high).** `stack_bytes`/`topLive` need every stack byte present;
  the loader inserts only `p_filesz` bytes (sparse Sail memory).
- **H1.** No loader-derived `Loaded` witness exists (the control is a
  hand-built dense snapshot); reaching entry takes 85k steps.
- **M1–M3, L1–L4.** `capacity`/`stack_admissible` make `Loaded`
  execution-dependent; Q8/`stringify` quirks are in the spec; ASCII-only
  strings; hygiene gaps (fixed).
- Everything else in `Loaded` holds at the real entry state of every traced
  program (registers, images, statics, `ExitRuntimeData`, initial store,
  `cap = 8`, the full `DlHeap.HeapAt` shape, frame chunks, `ProgramRepr`).

## Empirical cross-check

Lean emulator on the proof ELF, all `c/tests/*.wl` (script blob patched in
place; three minified, `functions.wl` split) and 23 adversarial programs
(depth 999/1000, 58/59/70-character closure names, INT64_MIN division,
33 arguments, 440-deep nesting, non-ASCII, every runtime error, OOM). All
match the semantics' prediction, including both out-of-memory programs
(`out of memory`, exit 1); see `REVIEW.md` §2.

## Hygiene committed

- README no longer says the theorem is conditional on `RemainingWork`.
- `check_all.sh`: stage b scans `VsaIris/`; new stage c2 runs
  `scripts/check_final_axioms.sh`; 35 stale `THEOREMS` entries removed.
- 20 legacy files grandfathered in `discipline_grandfather.txt` (dated
  comment).
- P6: the tower core (`TermAssembly`, `InterpSimFinal`, `rows/AssemblySkeleton`,
  `rows/Field_hStr`) and the residual-ledger tooling removed; `StmtDispatchClose`
  kept (semantics trichotomy). Build green (2583 jobs).
- P5: README states every `InterpRunReadyFacts` requirement, naming
  `capacity` and `stack_admissible`.
- Dead code: 88 modules deleted (unreachable from every root, or
  `RemainingWork`-tower leftovers wired only through `Vsa.lean`), with their
  `Vsa.lean` imports and `abs_inventory.sh`/grandfather lines.
- `PROOF_CLOSURE_PLAN.md`, `INTERP_DESIGN.md` §10, `TOOLING.md` record the
  review.

## Proposals (P1–P4 assigned to lanes B1–B3)

P1 boundary flags `0x000a` + first-write lemma; P2 rodata pin excluding the
script; P3 densification lemma for `Halts`/`Diverges`; P4 loader-derived
`Loaded` witnesses from the entry write log; (P5 and P6 are landed on this branch.)

## Holes

None added; 10 ledgered, unchanged.
