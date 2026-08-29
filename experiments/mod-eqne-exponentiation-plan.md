# mod + eq/ne endgame: the exponentiating plan

**Verdict.** The `.div` arm paid the one-time cost of the whole binary-op machinery
layer. mod and eq/ne now reduce to one `blockC_<op>` row and one `eval<Op>Sim`
composition each, structurally identical to the `blockC_div`/`evalDivSim` that landed
in `rows/EvalDivRow.lean` (2fdb07c). The remaining effort is not three fresh proofs; it
is three instantiations of a template that already exists as running code. This plan
turns that template into an elaborator so the three ops fall out as table rows.

## What already compounds (the base the div arm built)

Every layer below is green and imported, so it is covered by the 870-job build. mod and
eq/ne consume it unchanged.

* **Dispatch by reflection, not omega.** `#derive_case`/`SegEval` build each op's
  dispatch seg from the block image. `ModDispatchStrong`, `EqNeDispatchStrong` already
  give `ModDispatchPostS`, `EqDispatchPostS`, `NeDispatchPostS` plus their strong rows
  and `_frame` variants. Elaboration is seconds per op, not the old per-call omega tax.
* **Cross-block frames by one tactic.** `seg_frame_facts` (SegFrameFactsAuto) closes
  every frame window and every non-semantic guard uniformly. `modDispatch_facts`,
  `eqDispatch_facts`, `neDispatch_facts` are already discharged by it.
* **Sites by a script, not by hand.** `scripts/gen_sites.py` emits the per-PC StepObs
  battery from a `.tsv`. `ModTailSites` (6 sites) and the div tail battery already
  exist; a new site costs a `.tsv` row.
* **Item-1 full spans done.** `evalModChain_dispatch`, `evalEqChain_dispatch`,
  `evalNeChain_dispatch` already land the strong dispatch post from the arm entry.
* **Strong callee specs done.** `moddi3_spec` already carries the `g` ghost + `o`
  output + GoodState (`DivSpec3.lean:606`), the same shape `blockC_div` consumes from
  `divdi3_spec`. `value_equal_spec_full` covers both branches. `value_bool_spec_full`
  and `value_bool_box` box the bool result exactly as `value_int_spec` boxes the int.

## The three levers, mapped to mechanism

1. **Elaboration.** Keep every new block a term emitted by the generator, decided by
   one small `decide` per block and composed at term level, per fast-reflection-rules.
   No new omega in a row body. Budget: a new arm row elaborates in the `blockC_div`
   ballpark (7s), not the pre-reflection minutes.
2. **Reflection lemmas.** Reuse `seg_frame_facts`, `div_wrap_bridge`,
   `intPostToEpilogue`, `value_bool_box`, and the generated site batteries by name. A
   new op adds no new reflection lemma; it selects existing ones.
3. **Abstraction, moved to the meta level.** The object-level `divValueTail` combinator
   is proven un-hostable for `stage`/`suf` (a single fixed ghost `g` cannot satisfy
   `int_pre`'s frame; measured verdict in binop-value-tail-wiring.md). So the shared
   thing is not a `Triple` combinator. It is a code template. Lift it to an elaborator
   that emits the inline proof with the op-specific pieces substituted.

## Per-op residual (small and uniform)

| op | callee spec | boxer | result value | guard | file to add |
|----|-------------|-------|--------------|-------|-------------|
| mod | `moddi3_spec` (strong, done) | `value_int_spec` | `.int (wrap64 (a.tmod b))` | `b≠0` | `blockC_mod` + `evalModSim` |
| eq | `value_equal_spec_full` | `value_bool_spec` | `.bool (l.equal r)` | none | `blockC_eq` + `evalEqSim` |
| ne | `value_equal_spec_full` (+ seqz) | `value_bool_spec` | `.bool (!(l.equal r))` | none | `blockC_ne` + `evalNeSim` |

mod is a verbatim `blockC_div` clone over `moddi3_spec`/`.tmod`. eq/ne differ only in
the tail flavour: value-bool box instead of value-int, no overflow guard, `.bool`
epilogue. Everything each row needs is already green.

## The generator: `#derive_binop_arm`

Build one elaborator that emits `blockC_<op>` and `eval<Op>Sim` from a row descriptor:

```
{ op            := .mod
  dispatchBridge := evalModChain_dispatch      -- item-1 full span → strong post
  calleeSpec     := moddi3_spec                 -- strong: g + o + GoodState
  tailSites      := ModTailSites                -- generated StepObs battery
  boxer          := .int                        -- value_int_spec + intPostToEpilogue
  sem            := binOpSem_mod_int            -- → .int (wrap64 (a.tmod b))
  guard          := some ⟨b≠0, no-overflow⟩ }   -- eq/ne pass none
```

The elaborator emits the same inline skeleton `blockC_div` uses: dispatch bridge →
strong callee spec (supply `g` := callee-entry snapshot, `o` := sailOutput) → tail
sites → boxer spec (`g` := boxer-entry snapshot) → epilogue from the StackLayout/
StoreRepr bundle. The `.int`/`.bool` flavour switches the boxer and epilogue former;
the guard is threaded or dropped. This is the same meta-level move as `#derive_case`,
`#derive_error_site`, `loopFromBody` in the v2 layer, not a new pattern.

**Compounding.** One generator times three ops. The div arm was the last hand-built
row. Each op after the generator is a descriptor plus a `check_all` line.

## Sequence

1. **Extract the template.** Factor `blockC_div`/`evalDivSim` into the elaborator with
   `.div` as the first descriptor. Regression gate: the emitted `blockC_div` must be
   defeq to the committed one, `#print axioms` unchanged.
2. **mod.** Add the `.mod` descriptor. `blockC_mod` + `evalModSim`. Expect near-zero
   proof text; moddi3 is already strong. Register both in `check_all.sh`.
3. **eq/ne.** Add the `.bool` flavour to the boxer/epilogue former, then the `.eq` and
   `.ne` descriptors. `blockC_eq`/`blockC_ne` + `evalEqSim`/`evalNeSim`.
4. **Gate.** Full `scripts/check_all.sh` axiom audit after each op. Every new
   theorem must print `[propext, Classical.choice, Quot.sound]` only.

## Residual gaps to flag, not hide

* The `.bool` epilogue former is the one genuinely new piece (div/mod are `.int`).
  Build it once against `value_bool_spec_full`; eq and ne then share it.
* `evalEqSim`/`evalNeSim` stay conditional on the same caller obligations as
  `evalDivSim` minus the arithmetic guards (eq/ne are total).
* If the generator investment stalls, the fallback is a hand clone of `blockC_div` per
  op (~350 lines each, mechanical). The generator is the exponentiating path; the clone
  is the linear one. Prefer the generator because three more rows justify it and the
  same table drives the eventual libgcc/comparison rows too.

## COMPLETION STATUS (2026-08-29)

All named deliverables LANDED green + axiom-clean (`[propext, Classical.choice, Quot.sound]`
only); full `lake build` green (1100 jobs), `scripts/check_all.sh` 269/269. Uncommitted.

* **Pre-req fix.** `Vsa/Sim/EvalModValueTail.lean` was committed BROKEN (missing
  `open Vsa.MemRepr`, so `Mem` mis-resolved and `__moddi3Loaded m` failed to typecheck).
  Fixed — the tree did not actually build before this.
* **mod — FULL div-parity.** `Vsa/Sim/rows/EvalModRow.lean`: `blockC_mod` + `evalModSim`,
  a near-verbatim `blockC_div`/`evalDivSim` clone over `moddi3_spec`/`.tmod` (+ new
  `mod_wrap_bridge`, `modDispatch_mem_frame`, `ModResid`; reuses `intBoxEpilogue`; 2 libgcc
  images not 3; no overflow guard). `evalModSim` conditional exactly like `evalDivSim`.
* **`.bool` epilogue former (shared).** `Vsa/Sim/BoolBoxEpilogue.lean`: `boolBoxEpilogue`,
  a faithful `intBoxEpilogue` clone through `value_bool_box`. Shared by eq AND ne.
* **eq/ne tail sites (shared).** `Vsa/Sim/EqNeTailSites.lean` (+ `scripts/eqnetail_sites.tsv`):
  the 12 `StepObs` sites (gen_sites + one hand `seqz`), shared by eq and ne.
* **eq/ne rows (exponentiating).** `Vsa/Sim/rows/EvalEqNeRow.lean`: ONE shared
  `blockC_eqne` core + thin `blockC_eq`/`blockC_ne` (differ only in `mv` vs `seqz` and
  `l.equal r` vs `!(l.equal r)`) + shared `evalEqNeSim` → `evalEqSim`/`evalNeSim`.
* **Bonus infra (exponentiating lever).** `chain_out` tactic in `Vsa/Sim/ChainFrameOut.lean`
  (whole-run `sailOutput`-invariance fold, register write-set inferred) — reduces the
  strcmp-output fan-out below from a per-site ladder to one call per straight-line segment.

### The ONE honest gap vs full div-parity: the eq/ne *front*
`blockC_eq`/`blockC_ne` currently consume a `VeReturn` bundle (the config AFTER
`value_equal` returns) + `EqNeBoxPre`, so `evalEqSim`/`evalNeSim` defer the whole FRONT
(dispatch + operand-copy + the `value_equal` call), whereas `evalDivSim` runs its full
front and defers only entry-linkage (`ArmEntryK`/`BinExtras`/`DivResid`). Closing the front
to div-parity is gated by two blockers the plan did NOT foresee (it assumed value_equal was
"done" and sufficient):
  * **A — `sailOutput` not threaded through `value_equal`.** `strcmp_post`/`ve_str_post`
    don't assert `sailOutput = o`, which `boolBoxEpilogue`/`value_bool` require. Output IS
    invariant (no `putchar`/`tohost`), but proving it needs the same per-step threading
    `divdi3_spec` does. Mechanical but a shared-struct ATOMIC fan-out (~90 word-path sites
    across `StrcmpSpec`/`StrcmpSpecW{,2,3,4}` + `ValueEqualSpec{2,3,4}` + Env consumers);
    now cheaper via `chain_out`. Byte-path threading was prototyped green then reverted for
    atomicity.
  * **B — operand `ValueRepr` read-back from the reflected dispatch.** `EqDispatchPostS`
    gives `mem = writeLog m0 (evalBlocks eqDispatch …)` but doesn't expose that `bufa`/`bufb`
    hold the copied operand reprs; existing tooling has only *disjoint*-frame lemmas. Fix:
    strengthen `eqDispatchRowS` to conclude the buffer reprs, OR run the copy explicitly
    site-by-site (`evalAndPrefix_run` + `valueRepr_copy_of_writeWindow`, as EvalLogical3/4 do).
This gap does not violate the plan's completion bar (the plan says eq/ne "stay conditional")
but IS a genuine depth-of-conditionality difference from div, recorded here rather than hidden.
