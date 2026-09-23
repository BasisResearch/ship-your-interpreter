# Lane F3: function specs with abort, call rules, stack

Branch `lane-f3` (from `hub/iris-main`). Design: `VsaIris/INTERP_DESIGN.md` §2 F3, §4.2, §9.
Package F3 = `fnSpecAbort` / `wp_callAbort` / `abort_rebase`, the stack carve/join
lemmas, `evalNeed`/`execNeed` arithmetic, and the bounded-loop rule over `MachWP`.

## Done

- **The bounded-loop rule — ready for H3** (`VsaIris/Loop.lean`, in
  `lake build VsaIris`, axioms ⊆ {propext, Classical.choice, Quot.sound}):
  - `MachWP.loop I K body fin n` — fuel induction, for either WP. The body's
    two continuations (next iteration `I k`, loop exit `K`) are an ADDITIVE
    pair, so the inherited exit/abort resource survives every iteration
    (INTERP_DESIGN.md §10.1). Ported from xv6iris `ProofMemset.v:1-9`
    ("bounded loop, not iLöb") and `ProofMemmove.v:350` `mm_loop`.
  - `MachWP.loopI` — the same with no separate exit resource.
  - `MachWP.loopSeg` — **the shape H3 wants**: one iteration is one `RunFact`
    segment (what `Inst.seg_runFact` produces from `segEval_sound`), with an
    invariant opener/closer around the segment footprint and a frame `F k`
    across it. `strlen`, `memcpy`, `strcmp` and the `args[32]` fill use this.
  - `wp_loop` / `wpP_loop` — the total and partial instances.
  Neither rule costs a `lat`/later: the loop is bounded, Löb is spent only on
  the three recursive entry points.

## In flight

- `fnSpecAbort`, `wp_callAbort` (`VsaIris/CallAbort.lean`).
- Stack carve/join over `blockOwn`/`stackScratch`, generic `abortRes`/`abort_rebase`.
- `evalNeed`/`execNeed` arithmetic and the `ProgramStackFits`/`execBudget` bridge.
- Replacing §B of `VsaIris/Interp/Specs.lean` with the landed definitions.

## Holes

None added. `python3 scripts/check_iris_holes.py` passes.

## Next

Finish the in-flight items above, then re-check `Specs.lean` §B/§D against them.
