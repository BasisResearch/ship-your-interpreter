# Lane B2: `Loaded` for real runs — P3, the machine is insensitive to absent bytes

Branch `lane-b2` (from `hub/iris-main` `286c2ad`, merged `hub/lane-v`). Design:
`VsaIris/INTERP_DESIGN.md` "Decisions" (P1–P4, 2026-09-25) and "STATEMENT
CHANGE (lane B2, P3)"; the finding: `REVIEW.md` C3 / §4 P3.

## Status: done

`lake build Vsa VsaIris` green (2596 jobs). `scripts/check_final_axioms.sh`:
15/15 theorems (`endToEnd_refinement`, `endToEnd_refinement_loaded`,
`halts_fillZero`, `diverges_fillZero`, `stepOnce_resp`, `Control.loaded_fill`,
…) depend on `[propext, Classical.choice, Quot.sound]` only.
`check_iris_holes.py`: 10 ledgered holes, unchanged. `check_all.sh
--static-only` green (a3 includes `gen_resp.py --check`). No `sorry`,
`axiom`, `native_decide`, `bv_decide`; no `maxHeartbeats`/`maxRecDepth`
raised anywhere in `Vsa/Densify/`.

## Done

- `Vsa/Densify/Resp.lean`: `MemEqv`/`SEqv` (zero-equivalent Sail states),
  `REqv`, `Resp`/`RespE` (respectful `SailM`/`SailME` computations), the monad
  combinators, fuel and `for` loops (lean-sail's `IntRange`), and `Resp` for
  every lean-sail primitive (`PS.*`).
- `Vsa/Densify/Tactic.lean`: `resp_auto`, a flat bounded loop of one
  `resp_step` per goal; `resp_step` dispatches on the head symbol
  (bind/pure/lift/throw/loops/`if`/`match`/casts/compiled case splits/callee
  lemmas by name/induction hypotheses). Two abstractions were forced by the
  elaboration budget (Law 1, no limit raised): `do` join points are proved
  once and hypothesised in the body (`Resp.letFun{0,1,2}`; inlining them is
  exponential, the decoders nest 60), and literal-pattern matchers (the
  330-alternative CSR name tables) are unfolded head-only and their `dite`
  chains split by a syntactic step, since `split`, `dsimp` and every term
  traversal overflow on them.
- `experiments/densify/Closure.lean` → `closure.tsv`: the 307 monadic model
  functions in `Vsa.stepOnce`'s call graph, in dependency order, with arities
  and monadic callees. `scripts/gen_resp.py` (+ `--check`, stage a3) emits
  `Vsa/Densify/GenA.lean` (165 theorems), `GenB.lean` (84), `GenC.lean` (21,
  ending with `stepOnce_resp`).
- `Vsa/Densify/RecMutual.lean` (the `currentlyEnabled` mutual block, nine
  motives, functional induction) and `RecPt.lean` (`pt_walk`).
- `Vsa/Densify/Transport.lean`: lockstep simulation under `CEqv`
  (`step_sim`, `halted_sim`, `steps_sim`, `stepsN_sim`),
  `halts_iff_of_ceqv`, `diverges_iff_of_ceqv`; `fillZero`
  (noncomputable, `Classical.choose` of the RAM fill: nothing can ever compute
  the 2^27-entry insert), `fillZeroMem_get/_some/_ram`,
  `fillZero_eq_of_dense`. `Vsa/Densify.lean`: `halts_fillZero`,
  `diverges_fillZero`.
- `VsaIris/Interp/EndToEnd.lean`: `endToEnd_refinement` at `fillZero c`;
  `endToEnd_refinement_loaded` is the previous statement.
  `Control.loaded_fill` (`ControlLoaded.lean`) witnesses the new hypothesis.
- `experiments/review-v/check_loaded.py`: the dense view is the `fillZero`
  view, plus `fillZero covers the map`; run over the 35 traced programs
  (`stack_bytes[fillZero]` PASS for all; only C1/C2/L1 fail).
- Docs: INTERP_DESIGN.md, REVIEW.md (C3 resolved), README.md,
  `scripts/check_final_axioms.sh` (five new theorems), `check_all.sh` a3.

## The statement (`VsaIris/Interp/EndToEnd.lean`)

```lean
theorem endToEnd_refinement (h : IrisHoles) :
    ∀ p c, Loaded interpRunLayout p (fillZero c) →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, BigStep p out)
```

`Vsa.Densify.fillZero c` inserts every absent RAM byte `[0x80000000,
0x88000000)` as `some 0` (present bytes unchanged: `fillZeroMem_get`). The
previous statement is `endToEnd_refinement_loaded`. `Refinement.lean`,
`InterpSim`, `Loaded`, every boundary structure and `IrisHoles` are unchanged.

## Note for lanes N1–N5

No precondition inherits this change: the helper specs, `IrisHoles` and the
boundary structures are untouched; the fill is applied at the top only. A
stale `~/vsa-build.lock` (created 14:15:56 with no build running anywhere,
blocking three lanes) was removed at 14:30:27.

## Holes

None added. `IrisHoles` unchanged (10 ledgered holes).

## Next (not this lane)

- P1/P2 (console flags, script blob) make `Loaded … (fillZero c)` true at the
  real boot states; P4 builds loader-derived witnesses. With those, the checker's
  `fillZero` view is the witness's exact shape.
- `experiments/densify/closure.tsv` must be regenerated (`Closure.lean`) if the
  model or `Vsa/Elf.lean` changes; `gen_resp.py --check` catches drift.
