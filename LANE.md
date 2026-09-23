# Lane F3: function specs with abort, call rules, stack

Branch `lane-f3` (from `hub/iris-main`), pushed to `hub`. Design:
`VsaIris/INTERP_DESIGN.md` §2 F3, §4.2, §4.3, §9. All of it is in
`lake build Vsa VsaIris`, axioms ⊆ {propext, Classical.choice, Quot.sound}
(`VsaIris/Audit.lean`).

## Done

### The bounded-loop rule — H3 wants this (`VsaIris/Loop.lean`)

- `MachWP.loop I K body fin n` — fuel induction, for either WP (xv6iris
  `ProofMemset.v:1-9` "bounded loop, not iLöb"; `ProofMemmove.v:350`
  `mm_loop`, induction on `rem`). The body's two continuations — the next
  iteration's `I k` and the loop's inherited exit `K` — are an ADDITIVE pair,
  so an abort/exit resource survives every iteration (INTERP_DESIGN.md §10.1).
- `MachWP.loopI` — no separate exit resource.
- `MachWP.loopSeg` — **the shape for `strlen`/`memcpy`/`strcmp`/`args[32]`**:
  one iteration is one reflected `RunFact` segment, with an invariant
  opener/closer around the segment footprint and a frame `F k` across it.
- `wp_loop` / `wpP_loop` — the total and partial instances. No later is paid.

### Function specs with abort (`VsaIris/CallAbort.lean`)

- `fnSpecAbort Wp entry P Q A` — return and abort as an additive pair.
- `wp_callAbort` and `wp_callAbort_later` (the recursive `jal` under Löb).
- `fnSpecAbort_of_fnSpecW` — call an H1-H4 helper proved only with `fnSpecW`
  from a partial-mode proof carrying an abort continuation.
- `fnSpecAbort_mono` (consequence), `fnSpecAbort_rebase`.

### Stack carve/join and the call step (`VsaIris/Stack.lean`)

- `blockOwn_split` / `blockOwn_join` / `blockOwn_cast` / `blockOwn_emp` —
  interval arithmetic with the successor address and lengths as EQUATIONS, so
  no call site rewrites under `blockOwn`.
- `stackScratch_narrow` / `_widen`; `stackScratch_frame` / `_unframe` (the
  prologue's `addi sp,sp,-f`); `stackScratch_carve` / `stackScratch_join`
  (the composite; side condition `nc + f ≤ n` = `Vsa.Alloc.StackOK.child`'s).
- `abortAt Core s need` with `abortAt_elim`/`abortAt_intro`, and
  `abort_rebase`.
- `wp_callArmW` / `wp_callArmAbort` — **the call step an arm takes, once**:
  lend the callee a narrower region, keep the slack, and re-base BOTH
  continuations. E1-E6 use these instead of re-deriving the carve per site.

### `evalNeed` / `execNeed` (`VsaIris/Interp/Need.lean`)

- `stackBudget need d`, `evalNeed`, `execNeed`, verbatim from
  `EvalEntry.stackBudget`.
- TWO arithmetic lemmas underneath: `stackBudget_child` (the Iris route's
  `StackOK.child`) and `stackBudget_call` (a body at depth `d+1` inside one
  `perCallBudget`). The four eval/exec bridges and one inequality per recursor
  arm (`evalNeed_binary_left`, `execNeed_block`, `execNeed_callBody`, …) are
  one line each over them.
- S1's boundary bridge: `execNeed_of_stackFits` (arithmetic over
  `ProgramStackFits`, the `Loaded` field Q1 added) and `stackScratch_boundary`
  (the Iris carve at `spEntry - interpRunFrame`), plus
  `bodiesBound_of_stackFits`.

### `Specs.lean` and the design

- §B of `VsaIris/Interp/Specs.lean` now points at the landed modules; §D uses
  the landed `evalNeed`/`execNeed`, `abortRes = abortAt abortCore`, and
  `abort_rebase` is a proved corollary (one `sorry` fewer). The three
  remaining elaboration errors are the pre-existing §D `InterpGS` ones, in
  R/A territory.
- INTERP_DESIGN.md §2 F3 / §4.3 / §9 record every change, including the
  STATEMENT CHANGE to `abort_rebase` (it needs `np ≤ sp.toNat` and
  `nc ≤ sc.toNat`; `Nat` subtraction truncates and the intervals otherwise
  fail to join).

## Holes

None added. `python3 scripts/check_iris_holes.py` passes.

## Notes for other lanes

- **H3**: `MachWP.loopSeg`. Merge `hub/lane-f3`.
- **E1-E6 / G**: `wp_callArmAbort` is the per-call rule; `VsaIris.Interp`'s
  `evalNeed_*`/`execNeed_*` are the per-arm budget inequalities.
- **H5**: `abortAt Core s need` is the abort resource's shape; `Core` is
  yours to fix (the landing registers from the `jmp_buf`, or `exit(1)`).
- **R**: `abortRes` in `Specs.lean` §D is `abortAt (abortCore …)`.

## Next

Nothing outstanding in F3's package.
