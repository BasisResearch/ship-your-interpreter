# eq/ne front closure: the exponentiating plan for blockers A and B

**Verdict.** `blockC_eq`/`blockC_ne` already run the whole back half (`value_equal`
return through the shared `boolBoxEpilogue`), so the rows land green and axiom-clean.
What they defer is the *front*: dispatch, the operand copy into the compare buffers,
and the `value_equal` call itself. `evalDivSim` runs its full front and defers only
entry linkage; eq/ne match that once two blockers fall. Blocker A threads `sailOutput`
through `value_equal`. Blocker B reads the operand `ValueRepr`s back out of the reflected
dispatch. Neither is new mathematics. Both are infrastructure that compounds: build the
lever once, apply it uniformly, and the same lever pays for future arms.

## What already compounds (do not rebuild)

Every layer below is green, imported, and gated by `check_all` (269/269). The front
closure consumes it unchanged.

* **`chain_out` (`Vsa/Sim/ChainFrameOut.lean`).** Folds a whole straight-line run's
  output invariance into one call, with the register write set inferred and never named.
  This is the exponentiating primitive for blocker A: per segment, not per site.
* **`boolBoxEpilogue`, `EqNeTailSites`, `blockC_eqne`.** The back half is already shared
  across eq and ne. eq/ne are ~40-line instantiations differing only in `mv` vs `seqz`
  and `l.equal r` vs `!(l.equal r)`.
* **`TwoSubReturn` is value generic** (`Vsa/Sim/EvalBinSim.lean:117`). It hands
  `ValueRepr … (sp-968) vl` and `ValueRepr … (sp-944) vr` for arbitrary operand values,
  the source reprs blocker B copies.
* **Precedents.** `divdi3_spec`/`moddi3_spec` (`Vsa/Sim/DivSpec3.lean`) thread an output
  `o` through a libgcc loop. `valueRepr_copy_of_writeWindow` (`EvalLogical3.lean:323`,
  `EvalLogical4.lean:326`, `EvalOrSim.lean:521`) copies a `ValueRepr` from `sp-968` to
  `sp-1024`, which is exactly the vl copy.

## Blocker A: thread `sailOutput` through `value_equal`

`strcmp_post` and `ve_str_post` do not assert `c.σ.sailOutput = o`, and
`boolBoxEpilogue`/`value_bool` need it. The output is genuinely invariant because
`value_equal` runs no `putchar` or `tohost` store, so the fix is to make the specs say
so, in parallel with the `mem = m0` fact they already carry.

One caveat drives the whole design. Output invariance does not follow from memory
invariance. `htif_store_putchar` (`Vsa/Sim/Htif.lean:164`) is a non-halting store that
pushes to `sailOutput` while leaving `σ.mem` unchanged, so a blanket "non-halting step
preserves output" lemma is false. The `out` fact has to ride the per-step
`sailOutput_sigmaPost_alu`/`_branch_taken`/`_branch_nottaken`/`_load`/`_jal`/`_jr`/
`_jump_x0` witnesses, exactly as `hmem` rides `hobs.mem`.

### The exponentiating move

`chain_out` collapses that per-step ladder to one call per straight-line segment. Add an
`(o : Array String)` parameter after `m0` and an `out : c.σ.sailOutput = o` field to the
shared step structs `BSt`, `B94`, `BF9c`, `BDone`, `PreBCmp`, plus the word-path structs
`WHead`, `WG0mid`, `WNulExit`. At each proof segment, re-establish the `out` field with a
single `chain_out [hobs_1, …, hobs_n]` whose result `.trans`es the entry `out`. The byte
path was already prototyped green this way in `entry_byte` (1.8s), so the template is
proven. The transformation is mechanical and keyed on each existing `mem :=` /
`by rw [hmem…]; exact hmem` site.

### Why it must be atomic

`BSt`/`B94`/`BF9c`/`BDone`/`PreBCmp` are shared between the byte path and all four word
paths, and `strcmp_full_spec` (`StrcmpSpecW4.lean:534`) dispatches on entry alignment
into both, so adding a field breaks every construction until all are fixed. There is no
green partial state between "byte only" and "whole family". Do it as one changeset and
build once at the end.

### File order (one changeset)

1. `Vsa/Sim/StrcmpSpec.lean` (byte path; template already validated). Add `o` to
   `strcmp_pre`/`strcmp_post`/`strcmp_spec`.
2. `Vsa/Sim/StrcmpSpecW.lean` (`WHead`, `WG0mid`, entry).
3. `Vsa/Sim/StrcmpSpecW3.lean` (the `BDone`-producing lanes and NUL tails near lines
   338, 395, 417, 592, 775).
4. `Vsa/Sim/StrcmpSpecW2.lean` (the `swloop` word-loop invariant, `strcmp_word_spec`).
5. `Vsa/Sim/StrcmpSpecW4.lean` (`WNulExit`, `wnul_to_done`, `strcmp_full_pre`/`_post`/
   `_spec`).
6. Consumers: `Vsa/Sim/ValueEqualSpec3.lean` (`ve_str_reaches_result`), then
   `ValueEqualSpec2.lean` (`value_equal_spec_nonstr`), then `ValueEqualSpec4.lean`
   (`value_equal_spec_str`, `value_equal_spec_full`). Add `sailOutput = o` to
   `ve_pre`/`ve_post`/`ve_str_post` and thread it.
7. Fix any remaining break in `EnvGetSpec3/4/8`, `EnvDefSpec2/3/4`, `MemcpySpec`/
   `MemcpySpec3` (grep `strcmp_full_post`/`strcmp_post`/`strcmp_full_spec`/`ve_str_post`
   usages first, so every consumer lands in the same changeset).

### Gate A

`lake build` green. `#print axioms strcmp_spec`, `strcmp_full_spec`,
`value_equal_spec_full` all `[propext, Classical.choice, Quot.sound]`. `check_all`
stays green; add any new capstone to its `THEOREMS` list.

## Blocker B: read operand reprs back out of the reflected dispatch

`evalEqChain_dispatch` lands `EqDispatchPostS sp lds mem out gpre` with
`mem = writeLog m0 (evalBlocks eqDispatch (SegEvalState.init (eqDispL sp) lds)).log`. The
`eqDispatch` block copies vl from `sp-968` to `bufa = sp-1024` and vr from `sp-944` to
`bufb = sp-1056`, but the strong post exposes only registers, not the copied reprs.
`ve_pre` needs `ValueRepr mem N φc bufa.toNat vl` and `… bufb.toNat vr`, so the copy has
to be proven.

### The exponentiating move

Build one reusable lemma, `valueRepr_of_reflected_copy`, that reads a copied 24-byte
`ValueRepr` out of a reflected block's write log given the source repr and the block's
copy geometry. It serves `bufa` and `bufb` in the same call shape, and it serves ne for
free because `neDispatch` is byte identical to `eqDispatch`. Any later reflected-dispatch
arm that copies a `Value` reuses it. The missing primitive underneath is a hit-case
sibling to `writeLog_getElem_disjoint`: reading a slot the reflected log *does* write.

### Two routes, pick on feasibility

* **Route 1 (preferred, exponentiating): strengthen the dispatch.** Extend
  `eqDispatchRowS`/`EqDispatchPostS` (`Vsa/Sim/EqNeDispatchStrong.lean`) to also conclude
  the two buffer reprs, taking the source reprs as premises and proving the copy where
  the block is already reflected. Both operands and both ops share the one proof.
* **Route 2 (fallback, precedented): explicit copy.** Bypass the reflected block for the
  copy and run it site by site on an explicit `writeMap8` tower, as `evalAndPrefix_run`
  does in `EvalLogical3.lean`, so `valueRepr_copy_of_writeWindow` (`srcAddr := sp-968`,
  `dstAddr := sp-1024`) applies directly. This drops the reflected-dispatch reuse but has
  a working precedent in the logical arms.

### Gate B

The two `ValueRepr … bufa vl` / `… bufb vr` facts hold on the post-dispatch memory,
green and axiom-clean, reused by both ops.

## Wiring: fold the front into `blockC_eqne` (div-parity)

With A and B closed, build one shared `eqnePreBridge`: from the common dispatch-post
fields plus the two buffer reprs plus the `jal value_equal` site, land `ve_pre` at
`0x8000285c`. Parameterise it by the jal PC (`0x8000371c` for eq, `0x8000376c` for ne),
so a single bridge serves both, mirroring `blockC_div`'s `divPreBridge`.

Then re-seat `blockC_eqne` to start from `TwoSubReturn` rather than `VeReturn`. The core
becomes: run `evalEqChain_dispatch`/`evalNeChain_dispatch` for the dispatch post, derive
the buffer reprs (blocker B), cross `eqnePreBridge` into `ve_pre`, call
`value_equal_spec_full` (blocker A supplies `sailOutput = o`), and hand the existing
middle-plus-box-plus-epilogue the `VeReturn` it already consumes. Thread the `value_equal`
caller obligations, `StrcmpLoaded`/`MaskPinned`/`JumpTable`/`Value_equalLoaded` and the
str witness `hstrwit`, through an `EqResid` bundle in the goal exactly as `evalDivSim`
threads `DivResid`.

`evalEqNeSim` then composes `blockB_binary ≫ blockC_eqne ≫ blockD_v_rec`, deferring only
`ArmEntryK`/`BinExtras`/`EqResid`, which is div-parity. `blockC_eq`/`blockC_ne` and
`evalEqSim`/`evalNeSim` stay thin instantiations, so the exponentiating shape holds end to
end.

## Sequence

1. **Blocker A**, one atomic changeset over the strcmp family and its consumers. Gate A.
2. **Blocker B**, the readback lemma plus its two applications. Gate B.
3. **`eqnePreBridge`** and the `blockC_eqne` re-seat onto `TwoSubReturn`. Gate.
4. **`EqResid`** and the `evalEqNeSim` recomposition to div-parity. Gate.
5. **Re-typecheck** the eq/ne instantiations; full `check_all` axiom audit.

## Risks to flag, not hide

* Blocker A touches stable, load-bearing specs (`strcmp`, `value_equal`, and their Env
  and memcpy consumers). Keep the byte-path `chain_out` diff as the template, script the
  edit on the `mem`/`out` sites, and never leave the tree broken across a commit.
* Blocker B Route 1 needs the hit-case reflected-log readback lemma, which does not exist
  yet. If it resists, fall back to Route 2, which is precedented and self-contained.
* The `value_equal` str path drags in the full word-path strcmp, so the Env and memcpy
  consumers must ride the same blocker-A changeset or the build breaks.
