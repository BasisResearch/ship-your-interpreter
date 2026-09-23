# Lane H3 — string and memory helpers (`strlen`, `memcpy`, `strcmp`, `snprintf %lld`)

Branch `lane-h3`, from `hub/iris-main`. Design: `VsaIris/INTERP_DESIGN.md` §9, package H3.

## Done
- (nothing committed yet)

## In flight
- Survey of the reusable layer. Findings:
  - **The loop rule is already landed in F1**, not pending in F3: `wp_localRunW`
    (`VsaIris/LocalRun.lean:266`) is the mode-generic (`MachWP`) fuel-bounded
    owned-footprint run rule, with `segFrom_of_runFact` (`:320`) turning a VSA
    reflected segment into one `SegFrom` step. Its doc comment already carries the
    xv6iris citation (`ProofMemset.v:1-9`, "bounded loop, not iLöb"). So H3 is not
    blocked on F3; a nicer invariant-style wrapper from F3 can be adopted later.
  - Reusable VSA facts for `strlen`: `StrlenSegments.lean` (the `#derive_case`
    blocks), `StrlenMagic.detect_all_ones` (the zero-byte arithmetic, fully
    proved), `StrlenSpecU.detect_takenG`/`detect_nottakenG`,
    `StrlenReadState.wload_boundsG`/`tail_lbu_boundsG`/`head_lbu_bounds`,
    `EvalChildArm.wordLds8`, `StrlenSpec.strlenWordAt`.
  - Baseline for the line-count comparison (VSA's strlen cone):
    `Vsa/Sim/Strlen*.lean` = 9,494 lines over 13 files.
- Shape chosen: the WHOLE of `strlen` is ONE `LocalRun` (entry to `ret`), so the
  Iris layer is one `wp_localRunW` application and the work is a pure-Lean chain
  of `SegFrom` steps. Ownership follows INTERP_DESIGN §3: the string bytes
  `[p, p+len]` are persistent (`text`), the ≤7 slack bytes the word load
  over-reads are exclusively owned and returned unchanged (`S`).

## Holes
- none opened yet.

## Next
1. `VsaIris/Vsa/SegRun.lean`: `segFrom_of_seg`, the read-only reflected segment
   as one local-run step (the abstraction every H3 helper instantiates).
2. `VsaIris/Vsa/Strlen.lean`: the twelve segment steps, the two loop inductions
   (byte peel, word scan), the tail dispatch, `strlen_specW`.
3. `memcpy`, `strcmp`, `snprintf %lld` statements + straight-line parts.
4. Line-count / elaboration-time comparison against the VSA cone.
