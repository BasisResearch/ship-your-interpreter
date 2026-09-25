# Lane B1: `Loaded` at the real entry state (P1 console flags, P2 script bytes)

Branch `lane-b1` (from `hub/iris-main` `286c2ad`, merged `hub/lane-v`). Brief:
`~/lane-b1-aws.md`. User decision 2026-09-25: `REVIEW.md` P1–P4 approved; this
lane lands P1 and P2.

## Status: done

`lake build Vsa VsaIris VsaIris.Audit` green (2589 jobs). `endToEnd_refinement`,
`Control.loaded` and the new lemmas depend on `[propext, Classical.choice,
Quot.sound]` (`scripts/check_final_axioms.sh`, 16/16). `check_iris_holes.py`:
10 ledgered holes (unchanged). Discipline gate OK; `gen_fixed_image.py --check` OK.

## Done

- **P1: `stdout` unoriented at the boundary.** `ConsoleStreamAt (oriented : Bool)`
  (`Vsa/Sim/ConsoleStream.lean`), `ConsoleStream := ConsoleStreamAt true`,
  `ConsoleBoot := ConsoleStreamAt false`; `InterpRunPhysicalFacts.console :
  ConsoleBoot`. `StdioOKAt o img`, `StdioOK img := ∃ o, StdioOKAt o img`
  (`VsaIris/Vsa/Stdio.lean`). The `ORIENT` proof, once:
  `ConsoleStreamAt.orient` (agreement form), the four `ORIENT` blocks as
  `#derive_case` segments with decided write logs and
  `ConsoleStreamAt.orient_logWH`/`orient_logHW` (`Vsa/Sim/ConsoleOrient.lean`),
  `StdioOKAt.orient` for images (`VsaIris/Vsa/StdioOrient.lean`). Control:
  snapshot `_flags` word `0x000a`, `snapshot_console : ConsoleBoot`.
- **P2: the script is not pinned.** `fixedScriptSize = 454`;
  `FixedRodataLoaded` covers offsets `454 ≤ o < 8464` (generator
  `scripts/gen_fixed_image.py` and `Vsa/Sim/Code/FixedImage.lean`);
  `FixedRodataLoaded.byteAt`; `rodataDom` and `topLive` start at `0x80018da6`.
- **Checker.** `experiments/review-v/trace_corpus.py` (builds and traces the
  corpus outside the repo), `check_loaded.py` checks `ConsoleBoot`, the
  post-script rodata pin, and P1 after entry (every `_flags` change is one
  `ORIENT` `sh` of `0x200a` from `0x000a`; at every newlib call the console
  fields hold at `0x000a` or `0x200a`). Results:
  `experiments/review-v/check_loaded_results.txt`.
- Docs: INTERP_DESIGN.md Decisions + two STATEMENT CHANGEs (lane B1, P1/P2),
  REVIEW.md C1/C2 resolved.

## Holes

None added or removed (`check_iris_holes.py`). The holes' texts are unchanged;
their preconditions widened through `StdioOK` (see below).

## For the newlib lanes (N1, N3, N4, N5)

`stdioOwn` now admits `stdout` at `_flags = 0x000a` (before the run's first
console write) as well as `0x200a`. Every `StdioOK img` is `⟨o, h : StdioOKAt o img⟩`.

- `StdioOK.facts` returns `∃ o, ConsoleStreamAt o … ∧ …`; `StdioOKAt.facts`
  is the old one at a fixed `o`. Lemmas that produced `StdioOK` from a flushed
  state (N1's `StdioOK.written`) should conclude `StdioOKAt true img'` and
  wrap with `.ok`; lemmas that consumed it (`consoleMt_of`, N4's
  `ExitH/Loads.lean`) take `StdioOKAt o` and give `_flags = consoleFlags o`.
- **N1 (`out.fputs`, `out.fputc`, `out.fwrite`) and N5 (`out.fprintf`):** from
  `o = false` the run takes the `ORIENT` block (`_fputs_r` `0x80006418`,
  `_fwrite_r` `0x800050f0`, `__swbuf_r` `0x8000f1b4`, `_vfprintf_r`
  `0x8000a8fc`) instead of the `bltz`/`j` to the oriented path, stores `sw 0`
  at `0x8001bbd0` and `sh 0x200a` at `0x8001bb30`, and rejoins the `o = true`
  path with `_flags = 0x200a` (the same memory as the oriented path).
  The drivers run it (the step tables have these PCs); the memory fact is
  `ConsoleStreamAt.orient_log*` / `StdioOKAt.orient`. The post is oriented.
  `__swrite`'s `_flags &= ~__SOFF` (`0x8000f00c`) rewrites the same value.
- **N3 (`newlib.fprintf`, `newlib.fwrite` to `stderr`) and N2 (`snprintf`):**
  `stdout`'s flags are either value and unchanged by the call; thread `o`.
- **N4 (`newlib.exitHandlers`):** `exit` is reached with `stdout` at
  `0x000a` whenever the run printed nothing to `stdout` (every error-only run
  and `adv_empty` in the corpus): `_fclose_r`/`__sflush_r` on `stdout` run
  from `0x000a` too.

## Next (not this lane)

- P3 (stack presence, C3) and P4 (loader-derived witnesses): the remaining
  `check_loaded.py` failures are `stack_bytes` (sparse view) and L1.
- N lanes: rebase hole proofs on `StdioOK := ∃ o, StdioOKAt o` (above).
