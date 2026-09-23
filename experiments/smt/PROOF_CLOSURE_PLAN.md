# Proof closure plan

Prove `remainingWork_closed : RemainingWork interpRunLayout`, then discharge
the `RemainingWork` hypothesis of `endToEnd_refinement`.

## Status

AST and frame consumer hygiene (2026-09-11): **prerequisite checked**.
All eighteen remaining R6 projection findings are removed; thirty other
discipline findings remain. `MemRegionStmtFacts` supplies exact else/body
children. `CallEntryI.facts` retains the existing nineteen facts under the
same maps, memory, resources, and machine endpoint. The closure-row caller
uses that same entry for its stack-pointer equality.
Named segment-return, while-frame, and strcmp-register facts replace the
remaining environment and loop projections. No premise was discharged.

All sixteen edited consumer headers match their original types:
`/private/tmp/vsa-ast-call-20260911/unchanged-consumer-types.json`.
`header-comparison-audit.json` checks complete headers against `HEAD`, ignoring
proof-opener text inside comments. It corrects the previously truncated
`set_scan_iter_from_d2c` receipt; that theorem's full statement is unchanged.
The initial AST/call check built six modules and reused 296 in 21.626 seconds.
The caller check built 121 and reused 884 in 366.703 seconds. Both passed
standard-axiom audits. Receipts: `run-80tc7ffg/receipt.json` and
`run-z1tdji6k/receipt.json` under that directory.

Exact `stmtFp_region` consumption retains `hfp : StmtFp m a s addr` and
`hin : StmtIn m lo hi a s`; the corresponding expression consumer retains
`ExprFp` and `ExprIn`. `CallEntryI.console` retains its complete original
`CallEntryI` premise. Their checkpoint descriptions name every index and
premise. The remaining callers retain their original entry, ghost, geometry,
representation, and recursive-body hypotheses; this does not close the
closure case. Integration passed all 1,968 modules: 697 rebuilt and 1,271
reused, including 127 checked objects promoted with verified provenance.
The affected closure contains 824 modules. This final build measured
2,839.116 compilation seconds; the preceding 127 objects took 367.516
compilation seconds. The slowest module took 119.318 seconds, below the
unchanged 180-second limit. Backend freshness passed.
Allocator contract correction is approved. Migrate the three arbitrary-state
success rules to actual-run contracts with explicit credit and free-chunk
placement, preserving the external theorem statements and validation gates.

Compiled consumers and remaining premises, with exact types in the header receipt:

| Consumer | Remaining premises |
|---|---|
| `stmtFp_region`, `exprFp_region` | The respective footprint and region membership at the same memory and indices. |
| `CallEntryI.storeBounded`, `.valueBounded`, `.valuesBounded`, `.console`, `.spanGround`, `.allocator`, `.ioContracts` | The complete original `CallEntryI` at the same endpoint, maps, store, and resources. |
| `callClosureSim` | `EntryImage`, closure lookup, arity, depth, frame allocation, supported status, universal recursive `hBodyIH`, `CallClosureGeom`, and the Triple's `CallEntryI`. |
| `execWhileCondArmStable_of_stage` | `ExecWhileCondArmStage` at its original ghosts and endpoint. |
| `EnvSetScan.set_scan_iter_from_d2c` | `ScanSt`, absence of earlier matches, and an in-range scan index. |
| `envDefineScanNextCarrier` | Next-index bound, loaded env/strcmp code, `FrameRepr`, `ScanNames`, count equality, actual `EnvDefineScanLivePost`, and saved spill frame. |
| `envDefineScanStart` | Frame/name representations, count equality, positive signed count, scan geometry, and the full machine-entry precondition including loaded code and saved spill frame. |
| `envDefineMissCapDispatch` | `M`, capacity read and signed bound, length bound, arena geometry/alignment, count equality, allocator-invariant stability, and the actual framed scan-done precondition with no matching name. |
| `envDefineAppendEntry_of_cap` | `M`, stack/name ghost equalities, loaded strlen code, string regions/alignment, `CString`, and the actual framed capacity post with saved spills. |

The three exact application checkpoints are `run-1pfm3g4c`, `run-lbbssurq`,
and `run-wvf4q393` under `/private/tmp/vsa-ast-call-20260911/`.
Their descriptions retain every quantified index and proof premise.

The integration axiom audit checks all 1,086 existing gate declarations and
28 additional consumers/helpers, plus the exact console checkpoint witness.
All 1,114 declaration audits passed with standard axioms. Four sequential
batches preserve the 240-second check limit and cover the exact inventory
without duplication. `axiom-coverage.json` records their receipts. The combined
attempt timed out; the first final-batch attempt had a misqualified scan name
and two missing imports. Both failed attempts remain unaccepted evidence.
All nine successful slice receipts passed source, object, tool, and artifact
freshness checks.

Boundary validation initially rejected three changed source hashes. All four
unchanged cases passed against a temporary updated lock before that lock was
installed. Final validation passed all four actual Sail cases over 1,261
input hashes and 298 tests in 28.896 seconds, with six native tests skipped.
Generator checks, forbidden-token checks, whitespace, ELF identity, and the
source-tree object scan passed. The full gate still fails at stage a4 with
30 findings. No exemption, expected outcome, case, or resource limit changed.
Evidence: `/private/tmp/vsa-ast-call-20260911/integration-receipt.json`.
This checkpoint precedes the approved allocator-contract migration.

### Approved allocator correction

Malloc migration checked: **prerequisite**. All three arbitrary-state success
fields are removed from source. `AllocLedger.mallocSuccess` is an explicit successful
operation supplier. Parked malloc, environment creation, and name append now
take concrete entry resources; their selected returns retain unused resources.
The old grow wrapper carries its returned reserve into name allocation.
These consumers pass the frozen-source check.

Exact checked consumer: `Vsa.Sim.mallocReturn_of_parked`. Its full type and
remaining premises are in
`/private/tmp/vsa-realloc-migration-20260911.jAzmk8/malloc-checkpoint.json`.
It requires `M`, `L`, `n ≤ maxReq`, `0 < n`, and the actual `MallocParked`
entry. That entry carries machine-call facts, executable text, ownership,
numeric credit, and concrete placement. The selected successful return retains
the pointer, updated invariant, ownership, and residual credit and placement
at one endpoint. No concrete allocator implementation supplier is constructed.

Receipt:
`/private/tmp/vsa-allocator-correction-20260911.oghh8x/resource-overlay/run-ik2symzn/receipt.json`.
The check selected 1,264 modules, rebuilt 487, and reused 777. Dependency
compilation took 2,198.501 seconds; the full check took 2,217.686 seconds.
All 26 declaration audits and the exact typed consumer use only `propext`,
`Classical.choice`, and `Quot.sound`. The rejected first attempt and its
diagnostic remain in `malloc-failure-1.json` and `malloc-errors-1.log` beside
the checkpoint. Its reserved-keyword error was corrected before this check.

The exact realloc and initial-entry checkpoints were refreshed after the
malloc dependency change. Receipts `resource-overlay/run-zgfui38q/receipt.json`
and `resource-overlay/run-1a8keta2/receipt.json` reuse all 299 and 981 selected
modules respectively, taking 8.660 and 10.913 seconds. Their remaining
premises are unchanged. The initial refresh also checks
`envDefineHitAllocator_run_kept`.

Both preserved regression fixtures pass against the migrated dependencies.
Receipts are `regression-LegacyAllocatorContract/receipt.json` and
`regression-InitialResourceGap/receipt.json` beside the malloc checkpoint.
The legacy exact consumer retains `M` and `arenaHi`; the resource-gap exact
consumer proves `no_credit` for the fixed oversized ledger without premises.
It does not exclude a different initial ledger or refute the external theorem.
All regression audits use standard axioms. Full-source integration and its
validation results follow.

Checkpoint `72962c3` preserves the proof and tooling work before usage limits.
Full-source integration subsequently passed for all 1,976 modules: 632 rebuilt
and 1,344 reused. Dependency compilation took 2,867.866 seconds; the complete
check took 2,887.364 seconds. Its 27 audits use standard axioms. Measured
module times satisfy the existing limits and allowances.
Receipt: `resource-overlay/run-zb5675fb/receipt.json` under the correction
directory. `all-source-coverage.json` beside the malloc checkpoint verifies
that the receipt covers every current library and executable module.

The retained axiom inventory passes: 1,149 declarations, including all 1,086
original gate declarations and the allocator additions. The two legacy
contradiction declarations retain their separate exact fixture audits.
The full-library census inventories 65 fields across 1,976 modules; this
enumerates obligations and does not construct their suppliers.

All four unchanged boundary cases pass against 1,261 pinned inputs. The
candidate replay passed before refreshing only `Vsa/Alloc.lean` and
`Vsa/Sim/ReallocSpec.lean` fingerprints. The final replay also passed.
The validation suite ran 298 tests in 27.925 seconds, with six native tests
skipped. Forbidden-token and whitespace checks pass. External refinement
files and the ELF match the pre-checkpoint revision; no source-tree proof
objects were generated.

The full gate still stops at stage a4 with exactly the same 30 inherited
discipline findings. No exemption, limit, case, or expected outcome changed.
Evidence: `integration-receipt.json`, `axiom-coverage.json`, and
`integration-gate-status.json` beside the malloc checkpoint.
These results establish prerequisite integration, not proof closure.

The successful strdup bridge needs a different producer. The existing
`StringifyStrdupTail.stringifyStrdupTailContract` uses the nullable `M.spec`
post and cannot supply the new successful bridge input. The failure-aware
bridge and its conditional assembly remain; neither is a successful supplier.
The four standalone malloc readers now require a successful post at their
own input state. Source ceilings alone no longer prune their nullable posts.

Allocator-global framing remains a shared-interface gap. Removing
`AllocLedger.priv_arena` alone is insufficient: `EnvNewReturnState.mem_frame`,
`EnvDefineReturnState.mem_frame`, `EnvDefineMissFacts.mem_agree`, and
`GrowMemFacts.offArena` promise preservation outside the arena and stack,
including the mutable top-pointer global. Their allocating consumers need a
named write region covering allocator globals as well as the arena.
Nonallocating store frames may retain their stronger statements.

The exact framing consequence is now checked in `AllocatorGlobalFrame`.
`env_new_top_unchanged` applies the current `EnvNewReturnState.mem_frame` to
all eight bytes of the top-pointer slot. Exact consumer:
`Vsa.Sim.AllocatorGlobalFrame.rejects_top_change`. Its remaining premises are
`0x8001ad28 ≤ A.lo`, `0x8001ad28 ≤ SL.lo ∨ sp.toNat ≤ 0x8001ad20`, and
`read64 cfg.σ.mem 0x8001ad20 ≠ read64 m 0x8001ad20`.
It excludes that endpoint from the current return type. It does not prove
that a particular allocator execution changes the top pointer.

The checkpoint is
`/private/tmp/vsa-realloc-migration-20260911.jAzmk8/global-frame/checkpoint.json`;
receipt `resource-overlay/run-ivfs0yoe/receipt.json` is under the correction
directory. The slice selected 910 modules, rebuilt one, and reused 909.
Compilation took 7.539 seconds; the full check took 18.031 seconds. All three
declaration audits and the exact consumer use standard axioms. This is
prerequisite evidence for correcting the shared frames.

`Reserved.outsidePrivate` already accepts the needed weaker condition:
private bytes outside the arena belong to the caller's writable region.
`HeapOwned.ownedOff`, `entryOff`, `closureBuildOld_of_owned`, and
`envNewPushedRepr` now consume that coverage explicitly:
`∀ k, priv k → ¬ (A.lo ≤ k ∧ k < A.hi) → writes k`.
The allocating callers derive it from their existing `AllocLedger.priv_arena`;
that ledger premise and the allocating return-frame correction remain open.
Seven caller theorem headers are unchanged. Concrete `InitialWriteByte`
covers mutable globals in `[0x8001ad00, 0x8001c168)`. Generic callers still
need their own coverage proof. Static code and rodata precede `0x8001acf0`.
ELF symbols identify allocator globals, but no exhaustive machine-write
footprint or invariant supplier has been proved. Preserve read-only pinned
globals such as `_impure_ptr` separately from mutable allocator storage.

Exact checked consumer: `Vsa.Sim.envNewPushedRepr`. Its complete type and
twelve remaining premises are recorded in `allocator-private-coverage.json`
beside this plan. These retain ownership, stack-write coverage, store
representation, the allocator invariant, private-byte coverage, arena/stack
separation, parent bounds, fresh-block placement/alignment/disjointness,
memory agreement, and the initialized frame representation.

All 1,977 source modules passed: 229 rebuilt and 1,748 reused. Dependency
compilation took 456.531 seconds; the full check took 476.598 seconds.
All 31 audits, including the exact consumer, use standard axioms. The
slowest rebuilt module took 14.249 seconds, within the existing limits.
Receipt: `resource-overlay/run-ph2gv73f/receipt.json` under the allocator
correction directory. Coverage and header evidence are in
`/private/tmp/vsa-private-write-coverage-20260912.LBIVlQ/`.
Both preserved allocator regression fixtures pass against these dependencies.
The retained 1,149-declaration axiom inventory and all four unchanged boundary
cases pass. The census inventories 65 fields across all 1,977 modules.
The validation suite ran 298 tests in 34.785 seconds, with six native skips.
Forbidden-token and whitespace checks pass. External refinement files, the
ELF, boundary input hashes, and validation gates remain unchanged.
The full gate stops at stage a4 with the same 30 inherited discipline findings.
`integration-receipt.json` in the coverage directory records these results.
Implementation commit: `5fc518e`. No completion gate is closed.

Owned AST-region preservation is checked in `MemRegionOwned` and
`EvalGroundOwned`. The expression and statement proofs preserve hereditary
bounds from `ExprReprWithin`/`StmtReprWithin` and agreement on their covered
reads. They require no agreement on unused bytes of an enclosing interval.

`BinaryArmReady.stage_right` now receives the parent AST witness already held
by `run_allocator_at`. It preserves the parent ground and right-child pointer
using the selected left return's `data.agreement`. The right child uses the
same maps, memory, and shared-set inclusion. Static support and saved-stack
reads still consume the existing frame; their global-write correction remains
open. Other statement ground consumers still need ownership-based transport;
the owned sequence suffix is checked below.

Exact checked consumer: `Vsa.Sim.evalBinaryAllocatorOperands_at`, at its
unchanged theorem type. `owned-ast-region-consumer.json` records that type
and all remaining premises: `M`, `L`, the request bound, left source
derivation, store closure bounds, both child contracts, and the actual owned
allocator entry. No initial supplier or child contract is discharged.

All 1,979 source modules passed. Integration rebuilt 13 modules and reused
1,966, after the local consumer checks. Dependency compilation took 50.184
seconds; the complete check took 70.820 seconds. All 36 audits, including
the exact consumer, use standard axioms. Receipt:
`resource-overlay/run-m7sm3mbf/receipt.json` under the correction directory.
The ground adapter's exact checkpoint is `run-fh68rsz3/receipt.json` there.
Descriptions, unchanged-header evidence, and rejected elaboration diagnostics
are in `/private/tmp/vsa-owned-region-20260912.ls053e/`.
Validation completed for implementation commit `04a7916`. All 1,149 axiom
audits passed, including the original 1,086 declarations. Both preserved
allocator regressions and all four boundary cases passed. The 65-field census
checked all 1,979 modules; it remains inventory-only. The test suite passed
298 tests in 28.501 seconds, with six native-tool skips. Forbidden-proof and
whitespace checks passed. The full gate still exits at stage a4 with exactly
the same 30 discipline findings. Boundary input hashes, external theorem
files, and the ELF are unchanged. No validation gate was relaxed.
`integration-receipt.json` in the owned-region directory records these results.
No completion gate is closed.

Owned sequence statement regions are checked in `ExecGroundOwned` and consumed
by `SeqSuffixGround.transport_shared`. Each owned statement is aligned with
the ground array's selected pointer before transport. The same child return
supplies shared agreement, memory presence, and static framing. AST bounds and
representation now use owned reads. Static support and table preservation
still require the existing exit frame; its global-write correction remains open.

Exact checked consumer: `Vsa.Sim.seqInterpAllocatorContinue_of_return`.
`owned-statement-region-consumer.json` records its unchanged type and thirteen
remaining premises: allocator contract and ledger, continuation carrier,
source execution, environment validity, statement and store body bounds,
stack budget, stack RAM and HTIF geometry, static support, initial shared
agreement, and the actual owned child return. The block, closure, and interpreter
continuation sources are unchanged. Their rebuilt consumers pass axiom checks.

All 1,980 source modules passed: 56 rebuilt and 1,924 reused after the local
two-module check. Dependency compilation took 97.529 seconds; the full check
took 118.959 seconds. All 43 audits use standard axioms. Receipt:
`resource-overlay/run-k0iqk9gq/receipt.json` under the correction directory.
Evidence is in `/private/tmp/vsa-stmt-owned-20260912.ruwTgb/`.
Validation completed for implementation commit `62d1f85`. All 1,149 axiom
audits, both allocator regression fixtures, and four boundary cases passed.
The census covered all 1,980 modules and 65 fields; it remains inventory-only.
The test suite passed 298 tests in 28.264 seconds, with six native-tool skips.
Forbidden-proof and whitespace checks passed. The full gate retains exactly
the same 30 stage-a4 discipline findings. Boundary hashes, external theorem
files, and the ELF are unchanged. Elaboration stayed within the existing
180-second limit. `integration-receipt.json` records the validation evidence.
No validation gate was relaxed. No completion gate is closed.

Allocator heap boundary: **boundary strengthened** (approved 2026-09-12).
`InitialOwned.allocator : DlHeap.InitialAllocator` (`Vsa/Sim/DlHeap.lean`)
requires the newlib dlmalloc state `_malloc_r` reads and per-program heap
capacity. `LOADED_BOUNDARY_CORRECTION.md` records the exact fields and the
approval. The final theorem still prints `Loaded interpRunLayout p c`.

The field excludes the zero-top snapshot of `[.block [], .block []]`:
`Vsa.Sim.AllocatorBoundary.not_loaded` proves `¬ Loaded` although the same
snapshot satisfies every physical boundary fact (`physicalFacts`) and has a
terminating source derivation (`source_terminates`). A sparse Sail replay of
that snapshot faults in `_malloc_r` at `0x800047f4` reading address 8, after
following a zero bin pointer; `allocator-boundary-admission.json` names the
exclusion consumer. Replay evidence:
`/private/tmp/vsa-allocator-boundary-20260912.HBcAOj/`.

The admitted control is rebuilt with a consistent heap:
`ControlHeapMemory` writes empty bins, the break, the `sbrk` base, and eight
in-use chunk headers over the repaired control log, and moves the value array
to its own payload at `0x81000100`. `ControlHeapAllocator` proves `HeapAt`
and capacity by cost inversion (both `println()` statements cost 0).
`Control.loaded` now admits `heapConfig`; the stable-control regression
replays `Control.fullLog`. `InitialResourceGap` inherits the same heap; its
extra extents lie in an in-use filler chunk.

Real heaps satisfy the field: the proof ELF run to `interp_run` in the Sail
model (85,483 steps) and three test ELFs from `c/tests` pass the walk, bin,
and top checks, with no free chunks.

The exclusion slice rebuilt 104 modules in 763.9 seconds
(`/private/tmp/vsa-dlheap-work/run-nvtu23tl/receipt.json`). The control slice
checks `Control.loaded`, `readyFacts`, `initialOwned`, `heapAllocator`,
`heapAt`, `heapBins`, `heapTopPtr`, `program_cost`, and `not_loaded`
(`run-xy4s8fhb` in the same overlay). Every audit uses standard axioms. Bin
reads are proved by induction over `binsLog`; the 127-bin log is irreducible
so elaboration never unfolds it, and admission rewrites with
`physicalConfig_mem` rather than evaluating the heap write log.

All 1,984 source modules passed through the same overlay; all 22 audits,
including `endToEnd_refinement` and the exclusion checkpoint consumer, use
standard axioms (`run-quv0c78f`). All four boundary regressions passed against
a candidate lock before it was installed: the stable control is admitted by
`Control.loaded` and halts with `"\n\n"` from the heap snapshot; the three
unsafe snapshots stay excluded. The lock's changed inputs are the edited
boundary sources plus `InterpSpillReads` and `rows/DriveSpillGen`, newly in
the closure. Both allocator fixtures pass, with `InitialResourceGap.heap`
added to its audits. The source-only gate stops at stage a4 with the same 30
inherited discipline findings. Evidence: `/private/tmp/vsa-allocator-heap-20260912/`.

The arena is pinned to `[_end, __heap_end)` (`InitialOwned.arenaHeap`); the
control's ledger covers its AST with a live immutable extent. After the pin,
all 1,984 source modules passed (457 rebuilt, 1,798.5 seconds, receipt
`run-rf029jp0`); all 25 audits use standard axioms. Both allocator fixtures
pass, `InitialResourceGap` now proving `small_arena_excluded` and
`heap_credit`. All four boundary regressions pass against the refreshed lock.
The static gate stops at stage a4 with the same 30 inherited findings.
One obligation remains on this boundary. Capacity soundness relies on
`Vsa/While/Cost.lean` charging every interpreter `malloc`/`realloc` request at
least one 16-byte granule; a difftest comparing `__malloc_max_sbrked_mem`
against modeled cost would check it. No completion gate is closed.

`RuntimeAllocatorState.heap`, `InitialOwned.heap`, and the initial execution
adapter already use `InitialWriteByte SL`. Retain that ownership index.
It describes additional writes outside mutable allocation roles; adding the
whole arena would contradict `Immutable.binding` when a freshly copied name
becomes shared. The allocating frame predicates, including
`BlockEnvNewPost.helper`, require the wider allocator write region separately.
The correction must reach `SeqAllocatorContinueAt.memFrame` and the ordinary
`EvalReturn`/`ExecExitD` frames embedded in allocator returns. Generic
`MallocParked`, `FreeParked`, and environment ledger producers need explicit
private-byte coverage in their own `writes` predicate; concrete runtime
callers can derive it from the ELF interval. Stack-write coverage alone does
not supply this condition.

The private-footprint supplier also remains open inside the arena.
`MallocContract.privFoot` is fixed across states and live ledgers, while
free-list links and split headers occupy reusable storage. A concrete proof
must reconcile those writes with `privFoot_disjoint` at every returned live
ledger. Widening only the global interval does not establish that property.
An extent-indexed footprint is a candidate redesign, not a checked supplier
or a proved necessity.

The retained failure-aware specs have a separate code-entry gap.
`MallocContract.spec/freeSpec`, `ReallocOps.grow/null`, and their run records
omit executable-image premises. `AllocLedger.ainv_private` preserves `AInv`
under memory changes outside private bytes, including text; `GoodState` does
not pin text. The invariant therefore cannot implicitly supply the omitted
image condition. Successful calls already carry `AllocatorCallEntry.code`.
The failure-aware entry producers need the same explicit condition, with
their nullable result relations retained. Immediate consumers include
`env_new_spec`, `mallocCallSpec_sat`, the malloc/realloc `EnvDefCompose`
splices and spill frames, `concatMallocSlot`, `concatFreeSlot`,
`envDefMallocSaved`, `reallocGrowSaved`, and
`stringifyStrdupTailContract_viaSpliceFold`.

This is a source-level inhabitation concern, not a proved allocator
contradiction. `loopDemo` proves one instruction iteration at a different
address; it does not prove non-return from these allocator entries.

Allocator entries also omit saved-register presence. ABI equality to an
option-valued ghost permits absent registers. Disassembly shows incoming
`s0` read by malloc/free, `s0,s1` by non-NULL realloc, and `s0–s3` by the
reachable trim helper. Add a named presence condition for `x8`, `x9`, `x18`,
and `x19` to successful and failure-aware entries. `GoodState`, code, and
memory resources do not supply it. `EvalEntry.spill_defined` together with
`.envset_defined`, or `EnvDefineSavedPresent`, can supply these fields where
available. Other entry producers must retain their own concrete witnesses.
This is a disassembly/type audit; no missing-register contradiction has been
machine-checked. The current successful-operation supplier remains open.

Canonical realloc migration checked (2026-09-11): **prerequisite**.
The approval in `CONTRACT_CORRECTION.md` is recorded. Both arbitrary-state
`ReallocOps` success fields are removed. `ReallocInstance` now supplies an
actual `ReallocSuccessRun`; failure-aware operation specifications remain.

Exact checked consumer: `Vsa.Sim.reallocArray_run`. Its complete type and
remaining premises are in
`/private/tmp/vsa-realloc-migration-20260911.jAzmk8/checkpoint.json`.
It still requires `RI`, `harena`, `hold`, `hmem`, `hnz`, `hgrow`, and the actual
`ReallocSuccessEntry`. That entry carries code, machine-call facts, positive
bounded request, allocator invariant, credit, and concrete placement at the
entry memory. Neither the implementation supplier nor initial resources are
constructed.

`envDefineGrowCallsAt`, `envDefineGrowLaneOwnedAt`, and `envDefineGrowClosed`
now consume the two successful calls in sequence. Each retains its selected
pointer and execution endpoint. The first return supplies the second call's
credit and reserve, transported through the intervening live-payload write.
`reallocGrowSaved` retains its failure-aware statement and proof.
`RuntimeAllocatorState.after_stack` and `.credit_mono` preserve the new reserve
field. `AllocLedger.arena_globals` and `.globals_stack` remain explicit linker
layout premises.

Receipt:
`/private/tmp/vsa-allocator-correction-20260911.oghh8x/resource-overlay/run-1nd6u1oh/receipt.json`.
The slice selected 1,069 modules, rebuilt 91, and reused 978. Compilation took
259.109 seconds; the complete check took 279.407 seconds. All fifteen requested
declaration audits and the exact consumer passed with standard axioms.

Initial and runtime consumers now pass the next selected check. Exact consumer:
`OwnedInitialExecFacts.run_allocator`, recorded in `initial-checkpoint.json`
beside the realloc checkpoint. It requires the same `H`, `F`, `M`, `L`,
`ainv`, `capacity`, `ground`, `stack`, `bodies`, `geometry`, `supplier`, and
`requestBound`, plus independent
`placement : AllocationReserve A before.σ.mem D.exts maxReq (cost + reserve)`.
The actual prefix transports that reserve to the reached statement entry.
`execAllocatorEntry`, `EnvDefineGrowHeapPost.allocator`,
`envDefineGrowAllocator_run`, and `envDefineHitAllocator_run_kept` also pass
their declaration audits. Receipt: `resource-overlay/run-653gx6si/receipt.json`
under the correction directory. This remains prerequisite progress.

The malloc check includes upstream resource propagation.
`EnvDefineGrowEntry_run` now takes entry credit and placement. Its grow
wrapper retains the reserve beside the same append head.
`EnvDefineMissLedger.of_alloc` takes independent three-credit budget and
placement at its original entry. Scan and empty-frame paths transport them
through their actual stack writes. `MallocReturnAt.runtime` and
`EnvNewAllocationPost.runtime` consume reserves at their actual endpoints.
These source changes are checked; their concrete entry suppliers remain open.
The seven direct malloc consumers have been migrated and checked.
Nullable outer concat, closure-allocation, and strdup compositions still need
successful producers. `AllocLedger.priv_arena` still excludes concrete
allocator globals. The current integration checks do not supply those premises.

Pre-compilation static validation still reports 30 inherited findings.
All completion gates A–J remain required. The following receipts describe
earlier checkpoints; affected fingerprints predate the canonical migration.

Resource foundation checked (2026-09-11). `Vsa.AllocResource` supplies the
32-byte minimum; `Vsa.AllocRoom` describes concrete top metadata and payload
geometry. Exact consumer: `ResourceBudget.alloc`, with its unchanged fully
quantified type. Remaining premises: `h : ResourceBudget A maxReq exts (k + 1)`
and `hn : n ≤ maxReq`. The checkpoint is a prerequisite.

The slice selected 273 modules, rebuilt three, and reused 270. Compilation
took 11.025 seconds; the complete check took 24.976 seconds. All fifteen
requested declaration audits and the exact consumer passed with standard
axioms. Receipt:
`/private/tmp/vsa-allocator-correction-20260911.oghh8x/resource-overlay/run-wgxw5kvt/receipt.json`.
`InitialResourceGap.no_credit` now uses the corrected total 4,528; the experiment
and exact consumer passed the regression check below. The earlier full
integration predates these changes. Current full integration and boundary
validation remain due.

Remove the three arbitrary-state success pruners. Preserve their exact old
contract and contradiction in an isolated regression fixture. Keep the
failure-aware operation specs and add successful actual-run contracts with
entry credit, concrete placement, one selected return, and residual resources.
Four old malloc helpers consume only arbitrary return states; replace those
with projections from the actual successful post. Do not add entry capacity
to an unrelated return-state pruning rule.

Read-only source audits identified further concrete obligations:

- `AllocCapacity.physSize` omits dlmalloc's 32-byte minimum for requests ≤ 8.
  Extract pure sizing and budget definitions below `AllocRuns`, retaining
  their names, and use `max 32 (16 * ((n + 23) / 16))`. Existing public
  budget lemmas remain intended obligations. The control ledger includes
  requests of sizes 6, 8, and 7; do not exclude them with a minimum-request
  assumption.
- Concrete top placement reads `__malloc_av_`'s top slot at `0x8001ad20`
  and its size header. The top route needs an aligned, live-extent-disjoint
  chunk with at least the rounded request plus a 32-byte remainder.
  The allocator scans bins first; coherent finite bins and readable metadata
  remain invariant obligations. This is a sufficient placement route, not a
  characterisation of every successful allocation.
- The request conversion rejects rounded sizes ≥ `2^31`. Current callers
  supply a lower bound on `maxReq`, but no adequate upper bound.
- `AllocLedger.priv_arena` excludes actual mutable globals at `0x8001ad20`
  and `0x8001b990`, below the admitted heap lower bound `0x8001c170`.
  Account for allocator globals separately from live heap storage. The
  concrete code-image supplier is also missing from allocator entry specs.
- Grow performs two reallocations. Carry credit into the first call and
  retain placement at its actual returned memory and extent list for the
  second. Public-memory framing alone cannot preserve allocator metadata.

These are source/disassembly findings, not newly checked negation theorems.
Initial metadata, placement, code, and source-resource suppliers remain open.
Preserve `Loaded`, `RemainingWork`, and `endToEnd_refinement` unchanged.

The next interface checkpoint must retain concrete placement for every unused
credit at the selected allocator return. A public frame excludes allocator
metadata, so it cannot reconstruct that reserve. The successful operation
supplier must establish the residual reserve. Its initial supplier and its
transport through non-allocator writes remain explicit obligations.

Successful array adapter checked (2026-09-11):
`reallocArraySuccess_run` consumes `ReallocSuccessRun`, dispatches empty and live
arrays, and retains one `ReallocGrowSuccessExit`. That exit includes the actual
ABI/output/presence/code, pointer, copied bytes, replacement, both affected
extents in the public frame, and residual credit and placement. The new
interfaces take `AInv` and `privFoot` directly; they do not consume the old
arbitrary-state pruners.

Remaining premises are `RI`, `harena`, `hold`, `hmem`, `hnz`, `hgrow`, and the
actual `ReallocSuccessEntry`. The entry contains the loaded executable,
machine call facts, positive bounded request, invariant, numeric credit, and
concrete reserve at that memory. `AllocationResources.room` consumes the
reserve to produce placement for that request. No implementation supplier or
initial resource supplier was proved.

Exact checked consumer type and premises:
`/private/tmp/vsa-allocator-correction-20260911.oghh8x/success-checkpoint.json`.
Receipt: `resource-overlay/run-_y5q6dpf/receipt.json` under that directory.
All seven requested audits and the exact application pass with standard axioms.
The final check reuses all 262 selected modules. An earlier attempt compiled
the three new modules across two passes; the first failed on field shadowing,
the second on a misqualified checkpoint type. Both failures remain recorded.

At this earlier checkpoint, canonical callers still used the old contracts.
Canonical realloc migration is recorded above; malloc migration remains due.
The nine runtime constructor/update sites are `RuntimeAllocatorState.after_stack`,
`.credit_mono`, `OwnedInitialExecFacts.execAllocatorEntry`, `MallocReturnAt.runtime`,
`EnvNewAllocationPost.runtime`, `EnvDefineGrowHeapPost.allocator`,
`EnvDefineNameAppended.allocator`, `EnvDefineNameCopyReady.copy_return`, and
`envDefineHitAllocator_run_kept`. Nonallocating transport needs the actual
top-pointer and header words preserved. New global-slot separation is required;
the old arena bounds do not supply it.

The new `AllocationReserve.after_stack` and `.after_live` proofs transport the
two metadata words through actual byte agreement. Exact `.after_live`
consumption retains four premises: the incoming reserve, agreement outside
live extents, arena containment of those extents, and
`0x8001ad28 ≤ A.lo`. It does not supply that layout fact or any allocator call.
`live-transport-checkpoint.json` records the complete type using the existing
`AgreeP` predicate for memory agreement.

Current checks under `/private/tmp/vsa-allocator-correction-20260911.oghh8x/`:

| Receipt | Selected / rebuilt / reused | Total seconds |
|---|---|---|
| `resource-overlay/run-_y5q6dpf` | 262 / 0 / 262 | 9.039 |
| `resource-overlay/run-3274008z` | 570 / 2 / 568 | 16.704 |
| `resource-overlay/run-fxrql4ct` | 251 / 1 / 250 | 17.170 |
| `resource-overlay/run-h1l5nnhx` | 16 / 0 / 16 | 12.928 |

All four receipts passed source, dependency-object, tool, and checked-artifact
freshness checks. The 570-module slice rechecked `ResourceBudget.alloc` after
the capacity documentation changed. The first resource receipt is historical;
the documentation edit invalidated its dependency fingerprint.

The isolated legacy fixture passed in 4.323 seconds. It copies the old
`MallocContract`, `AInvAt`, `RuntimeAllocatorState`, and physical-accounting
definitions, with explicit namespace qualification. Both old obstruction
theorems and the exact `no_initial_invariant` consumer passed standard-axiom
checks. That consumer still takes the legacy contract and finite-arena bound.
Provenance: `experiments/fleet/obstructions/LegacyAllocatorContract.json`.
Receipt: `regression-LegacyAllocatorContract/receipt.json`.

The corrected resource-gap experiment passed in 2.542 seconds. All ten theorem
audits and the exact `no_credit` consumer passed. Its fixed admitted ledger
requires 4,528 minimum chunk bytes in a 4,096-byte arena, for all request ceilings
and credit counts. The same memory still admits the original affordable ledger.
This obstruction refutes an arbitrary-ledger-preserving budget supplier; it
does not refute another ledger or external refinement. Receipt:
`regression-InitialResourceGap/receipt.json`.

The full gate still stops at discipline stage a4 with 30 inherited findings.
Generator, forbidden-token, whitespace, ELF identity, and source-tree object
checks pass. No limit or exemption changed. Full integration, full census,
and boundary replay remain due after canonical contract and caller migration.
Checkpoint manifest:
`/private/tmp/vsa-allocator-correction-20260911.oghh8x/interface-checkpoint.json`.

Allocator consumer hygiene (2026-09-11): **prerequisite checked**.
Named accessors replace seven deep conjunction projections. `ReallocPost.facts`
retains the actual return's good state, tick, PC, stack pointer, gp, and ABI.
`strlen_post.mem_eq`, `EnvDefMallocPre.mem_eq`, and
`memcpy_bytepath_post.copied` expose the existing memory and copy facts.
No theorem statement or allocator contract changed. All five affected consumer
headers match their prior types; 48 discipline findings remain.

Checked consumers: `growEnvEntry_of_realloc`, `appendHeadSegPre_of_realloc`,
`bridgeMallocPreSaved_closed`, `envDefMallocSaved`, and
`envDefineMemcpyPostCString`. Their compiled axiom checks are in
`/private/tmp/vsa-hygiene-20260911/run-b2bq1qbk/receipt.json`.
Exact unchanged headers: `/private/tmp/vsa-hygiene-20260911/unchanged-consumer-types.json`.
The exact `growEnvEntry_of_realloc` application is checked in
`run-4xmqojsb/receipt.json`; `envDefineMemcpyPostCString` in
`run-b8ie5tvb/receipt.json`; and `envDefMallocSaved` in
`run-vkvzll3i/receipt.json`, under that same directory.

No premise was discharged. Realloc consumers still require `RO`, bounded
requests, growth, saved ABI inputs, loaded code, field reads, public-memory
geometry, and arena bounds. The malloc frame still requires `M`, request
bound, and private/code/stack separation. The strlen bridge still requires
its ghost equalities, invariant stability, and loaded-image implication.
The copied-string consumer still requires length equalities, `CString`,
`StrBytes`, and the actual `memcpy_bytepath_post`.
The three `*-checkpoint.json` descriptions retain the complete explicit types
and named premises. The first slice built five modules and reused 958 in
33.403 seconds. The copied-string check reused 963 in 17.185 seconds;
the realloc-entry check reused 873 in 19.022 seconds; the malloc-frame check
reused 963 in 16.787 seconds. All four receipts matched dependency fingerprints
and checked artifacts at that historical checkpoint, before the AST/call edits.

Integration passed all 1,965 modules: 84 rebuilt, 1,881 reused. Measured
compilation time was 248.073 seconds; the maximum module time was
14.720 seconds. Elaboration limits and backend freshness passed.
The full-library census enumerated 65 fields without establishing suppliers.
Four actual Sail boundary regressions passed against the existing lock.
The suite passed 298 tests in 28.793 seconds, with six native tests skipped.
Generator drift, forbidden-token, and whitespace checks passed. The full
gate still fails at discipline stage a4 with 48 findings; no exemption or
limit changed. Evidence:
`/private/tmp/vsa-hygiene-20260911/integration-receipt.json`.
Allocator specification correction was pending at that historical checkpoint.

`CallEntry`'s separate R7 finding remains structural: its twenty existential
occurrences are existing declarations and fields.

Failure-aware realloc frame (2026-09-11): **prerequisite checked**.
`reallocGrowSaved` now consumes `ReallocGrowResult.outside_arena` for both
failure and success. Its statement is unchanged. `ReallocPre.mem_eq`
supplies the entry baseline through a named destructurer. This removes one
use of the inconsistent non-null rule and one discipline finding; 55 remain.
`ReallocOps` itself still contains both inconsistent success rules.

The exact checked consumer is `Vsa.Sim.reallocGrowSaved` at its full existing
type, including the original `Triple` precondition and postcondition.
Remaining premises: `RO`; request bound `hle`; strict growth `hlt`;
old-pointer nonzero `hpOld`; live extent `hmem`; old arena placement
`hOldArena`; arena separation from spills/code `hArenaSpill`/`hArenaCode`;
private-footprint exclusion `hPrivCode`/`hPrivSpill`; and code/stack separation
`hCodeStack`. The Triple still requires `ReallocPre` and
`EnvDefineSavedSpillFrame` at the actual entry.
Exact types: `/private/tmp/vsa-allocator-contract-audit-20260912/frame-checkpoint.json`.
Receipt: `/private/tmp/vsa-allocator-contract-audit-20260912/frame-overlay/run-q9bq25kp/receipt.json`.
The check reused 873 modules, built none, and took 12.722 seconds. Both new
theorems and the checked consumer use only standard axioms. The preceding
slice built the two changed modules.

Integration passed all 1,964 modules: 84 rebuilt, 1,880 reused. The build
wrapper measured 168.233 seconds across rebuilt modules; the maximum was
10.538 seconds. Existing elaboration limits and backend freshness passed.
Both exact checkpoint receipts matched dependency sources and checked artifacts
at that historical checkpoint. The full-library census enumerated 65 inherited fields;
it did not establish suppliers. All four actual Sail boundary regressions
passed against the existing lock. The Python suite passed 298 tests in
28.769 seconds, with six native tests skipped. Generator drift, forbidden-token,
and whitespace checks passed. The full gate still fails at discipline stage
a4 with 55 findings. No gate or limit was weakened.
Evidence: `/private/tmp/vsa-allocator-contract-audit-20260912/integration-receipt.json`.

Allocator contract obstruction (2026-09-11): **initial consistency is impossible**.
`AllocatorContractObstruction.no_initial_invariant` proves
`A.hi ≤ 0x100000000 → ¬ AInvAt M gpv m exts` for every `MallocContract M`,
memory, and extent list. Its checked consumer is the theorem itself at the
fully quantified type. `no_runtime_state` consumes it to rule out every
`RuntimeAllocatorState` in such an arena. Both use only standard axioms.

`AInvAt` quantifies over every register state with the given gp and memory.
Choose one with x10 equal to zero. `M.nonNull_of_bounded` treats that state
as a null-return case and demands a nonzero pointer in the same register.
The arena bound excludes bitvector wraparound, so these requirements conflict.
The obstruction needs no `AllocLedger`, capacity bound, or particular
ownership witness. Definitions: `Vsa/Alloc.lean` (`nonNull_of_bounded`) and
`Vsa/Sim/AllocRuns.lean` (`AInvAt`). Proof:
`Vsa/Sim/AllocatorContractObstruction.lean`.

This supersedes initial witness selection as the next action. The preceding
allocator adapters compile conditionally, but their entry premises are
uninhabitable. Their receipts establish type checking, not executable closure.
The external refinement theorem is not refuted by this obstruction.

Required correction: keep allocator state independent of the return register;
state allocation success at an actual malloc execution, with sufficient
entry resources. A capacity premise on the same arbitrary-state non-null rule
does not repair its quantifiers. The success consumer must retain the actual
entry, execution, selected result, and reservation under one witness.
Changing the contract and dependent signatures requires a specification pass.
Existing statements, limits, and gates remain unchanged.

Final checked evidence:
`/private/tmp/vsa-allocator-contract-audit-20260912/overlay/run-1oz1qab4/receipt.json`.
The contradiction is instantiated at `maxReq`. The exact consumer checked
299 modules: one built, 298 reused, 15.845 seconds total. Its remaining
premises are `M : MallocContract A SL gpv headroom maxReq` and
`arenaHi : A.hi ≤ 0x100000000`; memory and extents are arbitrary indices.
Specification correction is approved; the concrete proposal is
`/private/tmp/vsa-allocator-contract-audit-20260912/CONTRACT_CORRECTION.md`.
The existing `reallocGrowSaved` consumer needs only a failure-aware public
frame. Removing its use of `nonNullGrow_of_bounded` needs no header change.

Initial statement allocator consumer (2026-09-11): **prerequisite checked**.
`OwnedInitialExecFacts.run_allocator` consumes `execAllocatorEntry` through
the unchanged `ExecAllocatorAt.run`. It composes the actual initial prefix
with the supplied statement execution, returning `InitialExecAllocatorRun`.
The result retains `ExecAllocatorReturn` at `0x80004478`, the selected maps,
shared ownership, and reserve. Its register ghost and memory baseline are
the first statement entry after setup. The complete run starts before setup.

`OwnedInitialExecFacts.allocator_gp` derives x3 from the actual dispatch,
null-call, and argument-setup frames. `execAllocatorEntry` transports
`AInvAt` from the initial memory through the concrete stack writes. Both
allocator consistency and capacity use the same `D.exts` as the reached
ownership. No arbitrary initial ownership witness is presumed affordable.

Remaining premises of this consumer, under the explicit indices in its receipt:

| Premise | Exact obligation / producer |
| --- | --- |
| `H` | `OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after s ss N A phiF phiC D`; supplied existentially by `readyInitialExec_owned`. Resource selection must use that same `D`. |
| `F` | `InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft`; existing initial readiness. |
| `M`, `L` | `MallocContract A stackSL (BitVec.ofNat 64 gpEntry) headroom maxReq` and `AllocLedger A stackSL (BitVec.ofNat 64 gpEntry) headroom maxReq M`; concrete allocator contract and run-global supplier remain open. |
| `ainv` | `AInvAt M (BitVec.ofNat 64 gpEntry) before.σ.mem D.exts`; initial allocator consistency remains open. Its transport is discharged. |
| `capacity` | `ResourceBudget A maxReq D.exts (cost + reserve)`; initial physical capacity remains open. |
| `ground` | `ExecGround after.σ.mem stackSL A 0x87fffc50#64 0x87fffca8#64 (BitVec.ofNat 64 aStmt).toNat s`; hereditary statement ground remains open. |
| `stack` | `StackOK stackSL 0x87fffc50#64 (s.stackNeed + maxCallDepth * perCallBudget + 1088)`. |
| `bodies` | `Stmt.bodiesBound perCallBudget s = true`. |
| `geometry` | `SharedReadGeom D.shared stackSL`; shared read slack remains open. |
| `supplier` | `ExecAllocatorAt N initSt 0 0 s final status cost request`; source recursion must supply the statement case. |
| `requestBound` | `request ≤ maxReq`; select the request ceiling jointly with the supplier and capacity. |

Here `stackSL` and `gpEntry` are the concrete `LayoutInstance` constants.
The acceptance description contains fully qualified types and every binder:
`/private/tmp/vsa-initial-consumer-20260911/checkpoint.json`.
The checked consumer application has only `propext`, `Classical.choice`,
and `Quot.sound`. Receipt:
`/private/tmp/vsa-initial-consumer-20260911/overlay/run-9obn1ryr/receipt.json`.
It checked 929 modules, rebuilt none, reused 929 overlay objects,
and took 16.903 seconds. Integration built the new module
and `Vsa`, reusing 1,960 modules. All 1,962 modules passed.

Static validation still fails on the same 56 inherited discipline findings.
No gate, limit, exemption, external theorem, or ELF was changed.
The full-library inventory enumerated 65 inherited fields; supplier coverage
remains open. All four actual Sail boundary regressions passed against the
unchanged lock. The Python suite ran 298 tests in 31.090 seconds, with six
native tests skipped and no failures. The resumed build-budget and freshness
gate reused all 1,962 modules. The full gate stops at discipline stage a4;
these later checks ran separately. Evidence and rejected attempts:
`/private/tmp/vsa-initial-consumer-20260911/integration-receipt.json`.

The sequence milestone remains the handoff's checked prerequisite:
`ExecSeqAllocatorSupply.nil`, `AllocatorCases.seqConsNormal`,
`AllocatorCases.seqConsAbrupt`, and `AllocatorCases.Residuals.onExecSeq`.
The induction consumer still requires `AuxMotives` and `Residuals`.
All 2,491 baseline proof files were compared with the handoff fingerprints;
only the `Vsa.lean` import changed. The new adapter adds one file.
The sequence dependency sources and initial resource obstruction are unchanged.

After correcting the inconsistent contract, select an allocator-consistent
initial ownership ledger with sufficient physical capacity from the unchanged
`Loaded` boundary. The new consumer does not establish that supplier.
Preserve the closure-case endpoint and
recursive-premise obligations below. `remainingWork_closed` and
`endToEnd_refinement` remain open.

Exact closure-case integration attempt (2026-09-11): **case remains open**.
The unchanged `TermCaseBundle.TermCases.hCallClosure` binders were instantiated
through the actual `CallEntryI` and recursive `mExecSeq` hypothesis. Applying
`ClosureCallPrefix.Pre.complete` fails at the conclusion: the required endpoint
is `CallExitI` at `0x800033ec`; the supplier produces `EvalAllocatorReturn`
after the outer epilogue. Probe: `/private/tmp/vsa-exact-hCallClosure.lean`;
compiler evidence: `/private/tmp/vsa-exact-hCallClosure.log`. This is an
integration attempt, not a discharged case or a proof of impossibility.

Premise inventory for the existing supplier, at the actual recursive entries:

| Premise | Available producer / unresolved connection |
| --- | --- |
| Interpreter depth and placement | `CallEntryI` has `CallDepthGround d`; `EvalAllocatorEntry` has no depth read or interpreter bounds/alignment/result separation. `InterpRunReadyFacts.call_depth` and `.interp_local` are the concrete initial producers. The depth must reach owned recursive entries and survive child returns. |
| Binding placement | `InitialOwned.bindingArena` supplies the concrete heap lower/upper bounds. `AllocLedger` only supplies RAM/HTIF bounds and either direction of stack separation; `RuntimeAllocatorState` does not retain `BindingArena`. |
| Owned allocator and credits | The legacy entry has `CallAllocatorGround`, not `AllocLedger`, `RuntimeAllocatorState`, shared ownership, or `3 * vs.length + bodyCost + reserve + 1` credits. `ArgumentsReady.closure_data` supplies the current owned state on the newer route. |
| Recursive body contract | The exact legacy case supplies `ExecSeqEntryI → ExecSeqExitI`. The existing completion proof consumes `ExecSeqAllocatorAt`; erasing ownership cannot construct this stronger result. The owned recursor supplies `ExecSeqAllocatorSupply` at the exact source body. |
| Binding reads and captured environment | Actual callee and argument ownership, closure lookup, and arity supply `FoldData` and captured-environment validity through `ArgumentsReady.closure_data` and `ClosureObjectReads`. |
| Body execution resources | `ClosureFnReads.body_data` still needs hereditary `ExecGround`, body alignment, body stack budget, and placement. Owned field coverage supplies scalar read geometry, not the legacy whole AST region. Carry the parsed body ground at closure creation and through the store. |
| Binding source invariant | `Pre.complete` requires `StoreUnique`; neither `RuntimeAllocatorState` nor `CallEntryI` retains it. The producer is `storeInvariant_initSt` and preservation through semantic store operations. |
| Request ceiling | Select parameter-name and array-growth bounds with the body supplier before machine entry. They are not consequences of the existing body's request ceiling. |
| Saved registers | The owned entry supplies x19/x20/x21 but does not require x22 or x23 to be present. Actual initial registers and recursive ABI preservation must supply s6/s7. Other caller slots and register equations are supplied by `ArgumentsReady.caller_frame` / `.reg_frame`. |
| Return windows and ownership baseline | Result geometry comes from the original evaluator entry. Interpreter/result separation is still required. Preserve the original shared baseline separately from the shared domain enlarged by argument allocations; do not assume their new bytes agreed with the original memory. |
| Dispatch and count bounds | `ArgumentsReady` supplies the loaded dispatch PC, control pins, real argument slots, and count bound from the source call. The legacy `CallEntryI` alone does not carry every dispatch pin or the source's 32-argument bound. |

Producer changes below are prerequisite progress. They do not remove
`hCallClosure`, alter the external theorem, or establish case closure.

Checked prerequisite progress:
`ReadyPrefixFacts.call_depth` preserves the initialized zero depth through
the actual prefix writes. `OwnedInitialExecFacts.call_depth` supplies it at
the first statement JAL; `.bindingArena` retains the original concrete
placement there. No new initial hypothesis is needed.
`ExecSeqAllocatorSupply.closure_allocation` instantiates the owned body IH
at the constructor's exact allocated frame and parameter-bound store. It
derives that store's closure bounds and selects one request ceiling covering
the body, every `param.length + 1`, and `48 * values.length`. These request
bounds no longer need independent machine-entry premises.
`ArgumentsReady.caller_frame` and `.reg_frame` recover the saved caller
from actual argument execution. `ArgumentsReady.closure_data` selects one
current owned closure/argument representation; `ClosureDataAt.geometry`
derives object and function-field bounds from that representation.

Still required: retain the produced interpreter facts, binding placement,
hereditary closure-body ground, and source uniqueness through recursive
entries. Compose at the required call-join endpoint and use a recursive
contract that retains the ownership the continuation consumes. The exact
legacy case is not closed by the owned component theorem.

Prerequisite integration: all 1,961 modules pass. Eleven declaration checks
use only standard axioms; forbidden-token and whitespace checks pass, with
no new discipline findings. External theorem statements and the ELF are
unchanged. Receipt:
`/private/tmp/vsa-closure-work/equality/closure-case-prerequisites/integration-receipt.json`.

Complete owned argument loop (2026-09-11):
`CallCallee.evaluate_arguments` executes evaluator entry, callee evaluation,
count setup, and the complete argument list to closure dispatch at
`0x80003254`. `Ground.select` derives each indexed child from the represented
call AST. `Input.iterate` composes its staging/JAL, owned evaluation, 24-byte
copy to `sp+240+24*i`, and actual loop branch.

`CallArgReturn.Post.owned` retains the callee and prior arguments at the
child's selected allocator maps. `LoopState.advance` reconstructs the next
source-derived input; `Arguments.run` folds the complete source list.
`Started.loop_state` connects the existing callee return to this fold,
including zero arguments. The combined endpoint retains the outer caller
frame, original ownership baseline, store bounds, output, and caller bytes
above `sp+1008`.

All 1,958 modules pass integration. Eighteen declaration checks use standard
axioms and match the integrated sources and objects. Eleven checked objects
were promoted; full integration built five modules and reused 1,953.
Forbidden-token and whitespace gates pass; no new discipline findings.

Next: supply closure dispatch reads, binding/body resources, and
`CallerFrame` from `ArgumentsReady`; compose `ClosureCallPrefix.Pre.complete`
to close the owned closure source case.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/call-arguments-complete/integration-receipt.json`.

Callee evaluation and argument-loop entry (2026-09-11):
`CallCallee.dispatch` executes the evaluator prologue and call-arm dispatch.
The represented call AST supplies the actual callee pointer, hereditary
child ground, and child stack budget through `StackOK.child`.
`Input.prepare` executes the reflected callee prefix and generated JAL;
`Input.evaluate` runs the owned child and retains its selected result maps,
allocator reserve, saved environment, caller registers, and memory frame.

`CallArgsSetup.run` reads the represented argument count, checks the bound,
saves s7, reloads the environment, and selects the empty or nonempty route.
`Post.owned` retains the owned callee through that spill. `CallCallee.start`
composes the full path from `EvalAllocatorEntry`, rebases ownership to the
original entry memory, and retains the outer caller frame. Zero arguments
reach closure dispatch at `0x80003254`; nonempty arguments reach the loop
head at `0x800031dc`, with index zero.

All 1,943 modules pass integration. Twelve declaration checks use standard
axioms and match the integrated sources and objects. Seven checked objects
were promoted; full integration built three modules and reused 1,940.
Forbidden-token and whitespace gates pass; no new discipline findings.

Next: execute each nonempty argument through the reflected staging/JAL,
copy its returned 24-byte value to `sp+240+24*i`, and fold the source argument
list while retaining the callee and prior arguments at one selected map
pair. Supply the closure source case through `ClosureCallPrefix.Pre.complete`.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/call-argument-entry/integration-receipt.json`.

Complete owned closure return (2026-09-11):
`ClosureCallPrefix.Pre.complete` composes dispatch, fresh scope allocation,
both parameter branches, body execution, and the final caller return.
`ClosureReturn.Post.owned` retains the selected result maps and ownership
through value copying or null construction. `Post.depth_restored` proves
byte-exact depth restoration outside the result slot.

`BodyRunAt.caller_stack` preserves the saved caller frame. The body retains
all remaining ABI registers, including restored s6. `BodyRunAt.epilogue`
constructs the existing owned epilogue entry; `.finish` applies
`blockD_v_return` to produce `EvalAllocatorReturn` with the original map
prefixes, shared bytes, allocator reserve, and caller ABI.

All 1,934 modules pass integration. Ten declaration checks use standard
axioms and match the integrated sources and objects. Thirteen checked objects
were promoted; full integration built one module and reused 1,933.
Forbidden-token and whitespace gates pass; no new discipline findings.

Next: supply dispatch-entry and caller facts from actual callee and argument
evaluation, then assemble the closure allocator source case.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/closure-owned-return/integration-receipt.json`.

Closure body execution and physical return (2026-09-11):
`ClosureFnReads.body_data` derives owned body reads and sequence resources
from the represented closure AST. `SeqSuffixOwned.transport_heap_stack`
preserves those facts through scope allocation and parameter binding.
`ClosureCallPrefix.Pre.prepare_body` executes dispatch, fresh scope creation,
and either parameter-count branch into one selected body input.

`BodyCallAt.run_sequence` executes the complete owned body sequence at the
exact bound source store. Binding and body posts retain the caller's s7 slot,
s5/s3 spills, upper stack, and interpreter depth. `BodyRunAt.return_reads`
recovers those actual reads, including dispatch's incremented depth.

`ClosureReturnDepth.run`, `ClosureReturnJoin.run`, and
`closureReturnNull_run` reuse the reflected return spans and generated JAL.
`ClosureReturn.run` composes both physical routes through the shared epilogue
entry at `0x800033ec`. `BodyRunAt.run_return` selects that execution from the
actual body status. The explicit-return route copies the 24-byte value;
the normal route calls `value_null`. Both restore s3, s5, and s7.

All 1,929 modules pass integration. Thirty-one declaration checks use standard
axioms and match the integrated sources and objects. Seventeen checked objects
were promoted; full integration built four modules and reused 1,925.
Forbidden-token and whitespace gates pass; no new discipline findings.

Next: carry the selected owned result through the return writes, retain the
remaining caller ABI fields, apply the existing final epilogue, and assemble
the closure allocator source case. Continue the case proof.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/closure-body-return/integration-receipt.json`.

Closure dispatch through parameter binding (2026-09-10):
`RuntimeAllocatorState.closure_reads` extracts the actual function node,
owned parameter names, and body from the represented closure.
`ClosureFnReads.fold_data` combines those names with the evaluated argument
slots. `ClosureCallPrefix.reads_of_closure` supplies the dispatch reads from
the represented callee.

`ClosureCallPrefix.run` executes all five dispatch blocks and the generated
JAL into `env_new`. It proves the four branch conditions and retains the
exact write log, saved argument count, caller s5/s3 spills, output, and full
register frame. The call-node read at offset 4 is the diagnostic source line.

`Post.scope_ready` preserves allocator ownership and every argument slot
through those writes. `Pre.bind_params` composes dispatch, scope allocation,
and the complete nonempty parameter fold into one execution reaching body
entry. `Pre.allocate` also executes the zero-parameter bypass;
`AllocatedCallAt.empty_pc` identifies its actual body-initializer endpoint.

All 1,916 modules pass integration. Eighteen declaration checks use standard
axioms and match the integrated sources and objects. Seven checked objects
were promoted; full integration built one module and reused 1,915.
Forbidden-token and whitespace gates pass; no new discipline findings.

Next: supply the owned body inputs from the closure AST on both parameter
branches, execute the body sequence, and compose its result with the caller
return. Continue the case proof.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/closure-call/integration-receipt.json`.

Complete parameter fold and body entry (2026-09-10):
`ClosureParam.FoldData.select` derives each staging input from the owned
name array and actual argument slots at `sp+240`. `FoldStepInput.run` executes
staging, empty/hit/miss binding, and the actual back edge or final branch.
`fold_run` composes those iterations with `storeChainList` over the exact
source `foldStore`, retaining allocation reserve, arguments, shared ownership,
caller registers, memory presence, and the body statements' ground facts.

`ClosureScopePost.bind_params` starts this fold from the actual fresh scope.
The allocator and scope posts now retain its initialized zero capacity.
`FoldLoopAt.run_body` supplies the existing body initializer at the final
`closureBoundStore`, initializes the result slot, and enters the owned sequence.

All 1,909 modules pass integration. Twenty declaration checks use standard
axioms and match the integrated sources and objects. Twelve checked objects
were promoted; full integration built three modules and reused 1,906.
Forbidden-token and whitespace gates pass; no new discipline findings.

Next: connect the closure-call entry to `FoldData` and `FoldBodyData`, handle
the zero-parameter bypass, and compose the owned body sequence with the caller
return. Continue the case proof.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/param-fold/integration-receipt.json`.

Owned binding returns and fold branches (2026-09-10):
`EnvDefineNameAppended.allocator` installs the actual copied name in the
binding ledger and extends the shared domain while retaining the allocation
reserve, array readiness, represented store, and allocator invariant.
`InitialOwned.bindingArena` supplies the unchanged initial heap bounds;
`BindingArena.extend` derives shared read geometry for the new name from
those bounds and the caller's stack headroom.

`EnvDefineAppendAllocatorPost.return_append_owned` returns one selected
`AllocatorResult` with the exact enlarged shared domain and agreement on the
entry's shared bytes. `EnvDefinePrologueAllocatorPost.reach_append` factors
the already checked scan and both capacity arms; plain and owned miss returns
consume the same execution. `ClosureParam.OwnedPost.define_empty_owned`,
`.define_miss_owned`, and `.define_hit_owned` retain that runtime through the
actual helper return. `ClosureParamResume.run_owned` executes the back edge
or final body-entry branch with the selected ownership and reserve intact.

All 1,902 modules pass integration. Nine checked objects were promoted;
full integration reused all 1,902. Fourteen declaration checks use standard
axioms and match the integrated sources and objects. Forbidden-token and
whitespace gates pass; no new discipline findings.

Next: construct the parameter-fold invariant from the actual arguments and
closure data. Compose the owned helper returns and back edge over the source
fold, then supply the body entry. Keep the initial `BindingArena` placement
from the loaded run. Continue the case proof.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/binding-runtime/integration-receipt.json`.

Nonempty miss through caller return (2026-09-10):
`EnvDefinePrologueAllocatorPost.return_miss` executes the complete scan,
capacity dispatch, and either direct append or both array reallocations
followed by append. It then runs the complete name copy, stores, and caller
return. `ClosureParam.OwnedPost.define_miss` supplies this execution from the
actual staged parameter call at `sp+64`, returning at `0x80003314` with the
exact defined store and shared-byte agreement.

The scan and capacity posts retain the names-array header read from actual
memory. `EnvDefineCapacityAllocatorPost.caller` recovers the original caller
registers and saved frame from the scan ghost. Growth consumes that retained
array pointer and the existing allocator proof.

All 1,896 modules pass integration. Thirteen checked objects were promoted;
full integration reused all 1,896. Seven declaration checks use standard
axioms and match the integrated sources and objects. Forbidden-token and
whitespace gates pass; no new discipline findings.

Next: retain the extended binding ownership and allocation reserve through
append, then connect the closure parameter fold. Continue the case proof.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/miss-append/integration-receipt.json`.

Full memcpy and first-parameter return (2026-09-10):
`MemcpyCopy.run` executes the actual entry dispatch, 72-byte loop, eight-byte
loop, trailing bytes, and return for aligned allocation destinations, every
source alignment, and every positive length within the supplied RAM regions.
The bulk loop performs nine loads and nine stores per iteration. Execution
retains ABI registers, output, memory presence, and bytes outside the copy.

`EnvDefineNameCopyReady.copy_return` reconstructs the complete copied CString
at `0x80002b44` and preserves the selected old heap, allocator ledger, staged
value, shared source name, saved frame, and code support.
`EnvDefineNameCopied.append` executes the five stores and epilogue, retaining
the exact defined store, array readiness, allocator invariant, and shared bytes.
`EnvDefineAppendAllocatorPost.return_append` joins strlen, allocation, the
complete copy, append, and the full caller return contract.
`ClosureParam.OwnedPost.define_empty_return` executes the first parameter's
actual env_define call through its return at `0x80003314`, including initial
array allocation. The defined store survives subsequent caller-stack writes.

All 1,893 modules pass integration. The 21 new declaration checks use standard
axioms and match the integrated sources and objects. Forbidden-token and
whitespace gates pass; no new discipline findings. Fourteen checked objects
were promoted; integration built two modules and reused 1,891.

Next: connect the nonempty miss to the append/grow routes and carry the
extended binding ownership through the closure parameter fold. Continue the
case proof; do not run limitation or metaproof campaigns.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/name-copy72/integration-receipt.json`.

Owned name allocation and copy entry (2026-09-10):
`EnvDefineAppendAllocatorPost.prepareCopy` executes strlen, allocates the name
copy, and reaches the actual memcpy entry. It consumes one allocation credit.
The endpoint retains the selected old heap, the fresh-block ledger, represented
store, readable arrays, staged value, owned name, saved caller registers and
spills, shared-byte agreement, and memory presence. The copy destination is
disjoint from the source string.

`SharedReadGeom.strlenRegions` supplies strlen's RAM and HTIF bounds directly
from the shared name bytes. The new scan states use these read bounds;
`strlen_full_spec_kept` and the original public contracts keep their interfaces.
`MallocReturnAt.runtime` retains the store and debits the actual allocation.
`EnvDefineNameAllocated.copy_entry` supplies the reflected copy-call arguments.

All 1,867 modules pass integration. The 35 declaration checks use standard
axioms and match the integrated sources and objects. Forbidden-token and
whitespace gates pass; discipline findings remain at 56. Owned residuals
remain at 40; base closure remains 37/63.

Next: prove memcpy for the fresh aligned destination, arbitrary source
alignment, and the full allocated name length. Compose it with the checked
append tail, retain the expanded shared-read geometry, connect full-capacity
scan to grow, and fold bindings into `ClosureBodyInput`.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/name-allocation/integration-receipt.json`.


Complete strlen run and ledger supplier (2026-09-10):
`StrlenRun.run` executes the actual helper for either pointer alignment.
The byte peel, word scan, all final-byte paths, and return preserve exact
memory, caller ABI registers, output, and the tick bound. The returned length
comes from the represented string. `strlen_full_spec_kept` exposes the full
contract; `strlenRun_closed` supplies the existing allocator-ledger field.

The execution uses generated reflected spans, the existing loop measures and
string arithmetic, and the existing `snez` instruction proof. No reflection
engine changes, new axioms, or raised proof limits were needed.

All 1,862 modules pass integration. The 29 declaration checks use standard
axioms and match the integrated sources and objects. Forbidden-token and
whitespace gates pass; discipline findings remain at 56. Owned residuals
remain at 40; base closure remains 37/63.

Next: connect the checked strlen run to owned name data, allocate the copied
name, and supply memcpy. Compose with the checked append tail, connect
full-capacity scan to grow, and fold bindings into `ClosureBodyInput`.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/strlen/integration-receipt.json`.


Owned append stores and caller return (2026-09-10):
`envDefineAppendInput_of_owned` supplies the existing append-store span from
owned name-copy return data at the caller's actual value slot.
`EnvDefineAppendStoreInput.returned` executes the five stores and epilogue.
Its endpoint retains the exact copied name pointer, all 24 copied value
bytes, word readiness, untouched memory, saved caller registers, and output.

`EnvDefineAppendMemory.heap_owned` reconstructs the extended owned store.
`FrameOwned.append` retains earlier slots; `StoreOwned.append` retains the
other frames and closure data. `Immutable.binding` and `Reserved.binding`
assign and reserve the fresh copied name in `BindingShared`.
`StoreArraysReady.defineAppend` preserves readable arrays. The memory
carrier also supplies `.store_repr` and `.allocatorInvariant`.
`EnvDefineAppendReturned.toReturn` assembles the full caller return contract
from the owned defined store and the retained endpoint.

All 1,854 modules pass integration. The 27 declaration checks use standard
axioms and match the integrated sources and objects. Existing append theorem
headers are unchanged. Forbidden-token and whitespace gates pass; discipline
findings remain at 56. Owned residuals remain at 40; base closure remains 37/63.

Next: supply owned strlen, name allocation, and memcpy. Compose that prefix
with the checked append tail and retain the expanded shared-read geometry.
Connect the full-capacity scan branch to grow, then fold the bindings into
`ClosureBodyInput`.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/define-append/integration-receipt.json`.

Owned env_define grow and first-binding allocation (2026-09-10):
`envDefineGrowAllocator_run` executes both array reallocations at an arbitrary
caller value slot above `esp`. The result retains the selected allocation
roles and extents, copied value-word readiness, represented store, shared
bytes, saved caller frame, and allocator invariant. The two requests consume
two allocation credits. The original grow theorem interfaces remain unchanged
and project the generalized proofs.

`EnvDefineEmptyDispatch.run` executes the existing zero-capacity segment.
`EnvDefinePrologueAllocatorPost.empty_grow` connects it to both initial
allocations. `ClosureParam.OwnedPost.define_empty_grow` reaches the owned
append entry from the actual closure parameter call with its `sp+64` value.
`StoreArraysReady.replaceArrays` preserves readable occupied slots through
array replacement, including copied padding words.

All 1,844 modules pass integration. The 23 declaration checks use standard
axioms and match the integrated sources and objects. Forbidden-token and
whitespace gates pass; discipline findings remain at 56. Owned residuals
remain at 40; base closure remains 37/63.

Next: complete owned append and its helper return. Connect the full-capacity
scan branch to owned grow, then fold the bindings into `ClosureBodyInput`.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/define-grow/integration-receipt.json`.

Owned env_define scan and complete hit return (2026-09-10):
`EnvDefinePrologueAllocatorPost.scan` runs the positive-count name scan using
owned binding strings, owned query data, and the fixed comparison mask.
`EnvDefineScanAllocatorPost.hit_return` derives the selected values-array
address and executes the framed copy and epilogue. The reached endpoint
retains the exact defined store, readable words, allocator reserve, shared
bytes, caller registers, and output.

`EnvDefinePrologueAllocatorPost.return_hit` assembles the full
`EnvDefineReturnState`, including the original caller memory frame and
restored registers. `ClosureParam.OwnedPost.define_hit` connects the actual
`sp+64` argument call through this return at `0x80003314`.

`EnvDefineScanAllocatorPost.miss_capacity` carries the exhaustive miss through
the represented-capacity test. Its owned result selects append at
`0x80002b1c` or grow at `0x80002b90`. Both paths retain exact memory and the
saved caller frame. Named `.resolve` adapters expose the legacy scan and
capacity results.

All 1,839 modules pass integration. The 23 declaration checks use standard
axioms and match the integrated sources and objects. Existing tracked theorem
headers are unchanged. Forbidden-token and whitespace gates pass. Discipline
findings remain at 56; four existing capacity-dispatch findings moved by the
43-line named adapter insertion. Owned residuals remain at 40; base closure
remains 37/63.

Next: supply owned append and grow executions, including the empty-frame
route used by the first parameter. Fold all bindings into `ClosureBodyInput`.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/define-scan/integration-receipt.json`.

Owned env_define prologue and existing-name return (2026-09-10):
`ClosureParam.OwnedPost.run_prologue` consumes the actual staged `sp+64`
argument. `envDefinePrologueAllocator_run` executes the existing spill span
and retains the owned argument, name, saved registers, code support, and
allocator reserve at `0x80002a90`.

`envDefineHitAllocator_run` executes the existing-name copy and epilogue.
The return carries the exact `store.define`, whole-store ownership, readable
value slots, allocator-private invariant, unchanged credits, shared agreement,
and memory presence. `StoreArraysReady.defineHit` preserves alignment and
replaces the selected slot's three readable words.

All 1,833 modules pass integration. The 17 declaration checks use standard
axioms and match the integrated source fingerprints and objects. Existing
update declarations remain unchanged. Forbidden-token and whitespace gates
pass; discipline findings remain at the previous 56. The owned residual
record remains at 40 fields; base closure remains 37/63.

Next: connect the owned finite scan to the existing-name return, retaining
its caller register and output frame; supply append and grow executions.
Fold parameter bindings into `ClosureBodyInput`.
Integration receipt:
`/private/tmp/vsa-closure-work/equality/define-owned/integration-receipt.json`.

Owned parameter staging and return routes (2026-09-10):
`ClosureParam.run` executes the existing argument-copy span and the generated
`env_define` call at `0x80003310`. The reached call retains the exact four
stores, advanced argument cursor, saved index, and complete register frame.
`ClosureParam.Post.owned` carries the copied `ValueWordRepr`, payload
ownership, shared parameter name, and unchanged allocation reserve.

`ClosureParamResume.run` selects the existing loop or exit span from the
saved index and parameter count. The exit restores caller s6. Both routes
preserve exact memory and output. `Pre.of_return` recovers both saved words
and code support from the actual helper return's frame.

All 1,829 modules pass integration. The 17 declaration checks use standard
axioms and match the integrated sources and objects. Site regeneration,
forbidden-token, and whitespace gates pass; discipline findings are unchanged.
Receipt:
`/private/tmp/vsa-closure-work/equality/closure-binding/integration-receipt.json`.
The owned residual record remains at 40 fields; base closure remains 37/63.

Next: connect the owned `env_define` update, append, and grow executions at
the actual `sp+64` argument slot. Assemble the parameter-binding fold into
`ClosureBodyInput`, then finish closure dispatch and return classification.

Owned closure scope and return staging (2026-09-10):
`closureScopeAllocator_run` executes `env_new` and the selected return route.
The saved argument count chooses parameter binding at `0x800032dc` or
body initialization at `0x80003324`. `ClosureEnvNewResume.run` reuses the
existing fold and bypass segments. The positive route retains the exact
saved s6 word, argument cursor, loop bound, and zero index.

The result carries the fresh frame map, owned store, remaining allocation
credit, shared-byte agreement, code support, argument-count read, and
caller frame through the same execution. The owned residual record remains
at 40 fields; base closure remains 37/63.

All 1,825 modules pass integration. The 12 declaration checks use standard
axioms and match the integrated sources and objects. Forbidden-token and
whitespace gates pass; discipline findings are unchanged. Receipt:
`/private/tmp/vsa-closure-work/equality/closure-scope/integration-receipt.json`.

Next: connect closure dispatch to this scope allocator, then execute the
parameter-binding fold into `ClosureBodyInput`. Retain the owned body
result through return classification and the evaluator epilogue.

Owned closure-body setup and execution (2026-09-10):
`closureBodyAllocator_run_sequence` executes return-slot initialization,
the selected body-entry route, and the owned body sequence. Its result
retains the setup caller's memory baseline, selected maps, shared bytes,
high stack, and remaining allocation credit. The owned residual record
remains at 40 fields; base closure remains 37/63.

`ClosureBodyDispatch.run` reuses `callClosureBodyEntrySeg` and
`callClosureBodyBypassSeg`. Actual body-pointer and count reads select the
branch. Both routes retain exact memory, the body pointer, and zero index.
`closureBodyNull_run` uses the existing call segment and a generated JAL
site. `SegCallFacts.valueNull` retains the complete call frame and exact
24-byte write boundary; `interpValueNull_run` now uses the same adapter.

`ClosureBodyInput` describes the bound body at `0x80003324`: current
registers, shared header reads, owned suffix, sequence resources, runtime
code support, and stack geometry. `closureBodyAllocator_run` derives the
null-buffer region and load bounds, transports ownership through the actual
initialization, and constructs `ExecSeqAllocatorEntry` for either body
shape. `ClosureBodyPost.run_sequence` consumes that entry and rebases the
actual owned sequence return.

All 1,823 modules pass integration: 7 rebuilt, 1,816 reused; 11.52 seconds
compiling. The build reused 15 checked slice objects, representing 38.05
seconds of recorded compilation. All 20 declaration audits, including the
nine induction roots, use standard axioms and match the integrated source
fingerprints and object hashes. Two original theorem headers are unchanged.
Site regeneration, forbidden-token, and whitespace gates pass. Discipline
retains the same 56 findings. Receipt:
`/private/tmp/vsa-closure-work/equality/closure-body-setup/integration-receipt.json`.

Next: supply the closure dispatch, `env_new` return staging, and parameter
binding into `ClosureBodyInput`. Reuse `envNewAllocator_run`,
`callClosureEnvNewRetFoldSeg`, `callClosureEnvNewRetBypassSeg`, and the
existing parameter-fold spans. Then retain the owned body result through
the normal/returned-value classification and enclosing evaluator epilogue.

Owned block statement source case (2026-09-10):
`ExecAllocatorSupply.block` now supplies `ExecS.block` from the owned body
contract. Generated `AllocatorCases` uses it in all nine induction roots.
The owned residual record decreases from 41 to 40 fields: `hSBlock` is
removed. Base closure remains 37/63.

`envNewRetainedReturn_of_ledger` retains the actual malloc block,
initialization writes, allocator invariant, and fresh frame map from the
existing execution. `envNewAllocator_run` consumes one credit and preserves
the caller's shared bytes. `StoreOwned.pushFrame` and
`StoreArraysReady.pushFrame` retain the old store and the initialized frame.

`blockAllocatorEntry_run` composes dispatch, scope allocation, and the
existing empty/nonempty block continuation. The reached header and cursor
supply the owned sequence entry. The block loop now carries exact separation
of its saved-index word from the arena; the caller derives it from
`AllocLedger.arena_stack`. `BlockAllocatorPost.run_body` runs the owned body
and preserves its selected maps and reserve through `blockEpilogue_memory`.

All 1,817 modules pass integration: 24 rebuilt, 1,793 reused; 60.72 seconds
compiling. The build reused 29 checked slice objects, representing 70.67
seconds of recorded compilation. All 39 declaration audits, including the
nine induction roots, use standard axioms and match the integrated source
fingerprints and object hashes. Four original theorem headers are unchanged.
The 22 generator tests, generator drift, Ruff, the generator's mypy check,
forbidden-token, and whitespace gates pass. Discipline retains the same 56
findings. Receipt:
`/private/tmp/vsa-closure-work/equality/block-caller/integration-receipt.json`.

Next: connect the owned closure sequence to its caller. Reuse the checked
`envNewAllocator_run` for scope allocation and the existing closure-call
prefix, argument binding, body continuation, and return routes.

Owned block sequence source cases (2026-09-10):
`SeqBlockDispatch.consNormal`, `.consFinal`, and `.consAbrupt` execute the
block loop from `0x800041a4` through its statement call and selected return
route. The continuing route reloads the saved index and shared count,
advances the index, and runs the owned tail. Final and abrupt routes exit
at `0x8000409c`, retaining the actual child's maps, reserve, and status.

`ExecSeqCursorRepr.block` exposes the original cursor through named fields.
`LoopInput.of_entry` derives the dispatch and continuation inputs from that
cursor, the owned suffix, and `ExecSeqBlockResources.At`. The resources
retain header coverage, protected saved-index space, and register presence;
the actual normal back edge preserves them for the next iteration.

`ExecSeqAllocatorSupply.block_consNormal` and `.block_consAbrupt` supply
the block source constructors. Generated `AllocatorCases.seqConsNormal`
and `.seqConsAbrupt` now select checked proofs for all three physical
copies. Both sequence residual fields are removed: the owned residual
record decreases from 43 to 41 fields. Base closure remains 37/63.

All 1,809 modules pass integration: 244 rebuilt, 1,565 reused; 668.43 seconds
compiling. The build reused 220 checked slice objects after verifying their
source fingerprints, object hashes, and compilation times. Those objects
represent 540.50 seconds of recorded compilation.

All 38 declaration audits, including the nine induction roots, use standard
axioms and match the integrated fingerprints and object hashes. Six original
sequence definition headers are unchanged. The 22 generator tests, drift,
Ruff, mypy, forbidden-token, and whitespace checks pass. Discipline retains
the same 56 finding identities; `ExecSimCommon`'s existing existential count
changes from 25 to 26 for its named block cursor destructurer. Receipt:
`/private/tmp/vsa-closure-work/equality/sequence-block-assembly/integration-receipt.json`.

Next: connect the owned sequence suppliers to their callers, starting with
block entry after `env_new`. Reuse `envNewParked_of_entry`, the existing
allocator call, and `envNewSuccess_run`; `frameOwned_of_envNewSuccess`
supplies the new frame's ownership from those actual initialization stores.

Owned interpreter source cases (2026-09-10):
`ExecSeqAllocatorSupply.interp_consNormal` supplies the normal source
constructor from the statement and tail contracts. It selects the final
iteration for a singleton and composes the continuing route otherwise.
`.interp_consAbrupt` discharges the incompatible status under the
interpreter copy's existing normal-only support contract.

`SeqInterpDispatch.LoopInput.of_entry` now derives all loop inputs from the
owned sequence entry. `ExecSeqInterpResources.At` binds interpreter geometry
and saved registers to the pointer read from that entry's stack.
`OwnedLoopHeadFacts.interpResources` supplies them from actual initial setup;
the child and back-edge proof retain them for the next iteration.
`ExecSeqCursorRepr.interp` exposes the original cursor through named fields.

Generated `AllocatorCases` routes both interpreter sequence constructors
through these proofs in all nine induction roots. `hSeqConsNormalOther`
and `hSeqConsAbruptOther` now cover only the block copy. The owned residual
record remains at 43 fields; base closure remains 37/63.

All 1,796 modules pass integration: 297 rebuilt, 1,499 reused; 878.73 seconds
compiling. The integration cache reused 154 objects from the checked slice
after verifying their source fingerprints, object hashes, and compilation
times. Those objects represent 455.44 seconds of recorded compilation.

The 22 declaration audits, including all nine induction roots, use standard
axioms and match the integrated fingerprints. Six original sequence
declaration headers are unchanged. Generator drift, 22 generator tests,
Ruff, mypy, forbidden tokens, and whitespace checks pass. Discipline retains
the same 56 finding identities; the existing `ExecSimCommon` existential
count changes from 24 to 25 for its named cursor destructurer. Receipt:
`/private/tmp/vsa-closure-work/equality/sequence-interpreter-assembly/integration-receipt.json`.

Next: supply the block sequence copy, then the owned callers. Its dispatch
span is `0x800041a4` through the statement call at `0x800041c4`; the return
at `0x800041c8` branches on status, reloads the saved index and block count,
and either loops or exits at `0x8000409c`.

Owned interpreter loop-head execution (2026-09-10):
`SeqInterpDispatch.consNormal` now starts at `0x8000448c`, executes dispatch,
result-slot initialization, argument setup, the owned statement, the normal
back edge, and the recursive tail. `.consFinal` starts at the same loop head
and finishes the last statement at `0x80004514`. Both retain the selected
maps and allocation reserve.

`SeqInterpHead.run` and `SeqInterpArgs.run` reuse the existing reflected spans
and generated call instruction. `interpValueNull_run` generalizes the
existing initializer to the current stack pointer; `initialValueNull_run`
specializes that proof with its original statement. `SeqInterpDispatch.owned`
constructs the actual statement entry and preserves the owned AST suffix
through the result-slot writes. `.OwnedPost.caller` and `.carrier` derive
the continuation inputs from that execution.

All 1,792 modules pass integration: 13 rebuilt, 1,779 reused; 39.55 seconds
compiling. All 12 declaration audits, including 11 new proofs, use standard
axioms and match the integrated source fingerprints. The three existing
declaration statements in `InitialNullRun` are unchanged. Forbidden tokens
and whitespace checks pass; discipline output is unchanged. Receipt:
`/private/tmp/vsa-closure-work/equality/sequence-interpreter-dispatch/integration-receipt.json`.

Next: derive `SeqInterpDispatch.LoopInput` from the owned sequence entry,
retain interpreter geometry and saved-register presence through the back
edge, and wire the interpreter source constructors. The block copy and
owned callers remain. Base closure remains 37/63; the owned residual record
remains at 43 fields.

Owned interpreter sequence continuation (2026-09-10):
`seqInterpAllocatorConsNormal` executes an owned statement, the reflected
back edge, and the owned recursive tail. `seqInterpAllocatorFinal` executes
the last statement and normal exit. Both preserve the child's selected maps
and the caller's allocation reserve.

`SeqInterpNormal.run` reuses `interpBackEdgeSeg` and supplies its final-branch
variant. Each route takes exactly five instructions, advances the cursor by
eight bytes, and leaves memory unchanged. `SeqInterpCaller.normalPre`
derives the reached registers and code from the actual child return.
`SeqInterpContinueCarrier.readback` preserves the saved interpreter pointer,
script flag, and environment word through that return. The continuation
rebuilds `ExecSeqAllocatorEntry .interpRun` at the advanced owned suffix.

All 1,787 modules pass integration: six rebuilt, 1,781 reused; 12.28 seconds
compiling. All nine new public declaration audits use standard axioms and
match the integrated source fingerprints. Existing Lean declarations are
unchanged. The forbidden-token gate passes; discipline output is unchanged.
Receipt:
`/private/tmp/vsa-closure-work/equality/sequence-interpreter/integration-receipt.json`.

Next: supply interpreter dispatch from the loop head, including result-slot
initialization and argument setup, then wire the source sequence branch.
The block copy and owned callers remain. Base closure remains 37/63;
the owned residual record remains at 43 fields.

Owned closure sequence assembly (2026-09-10):
`ExecSeqAllocatorSupply.closure_consNormal` and `.closure_consAbrupt` supply
the source constructors. Normal execution selects the final-iteration route
or composes the child, back edge, and recursive tail. A value return finishes
at the child endpoint. `execSeqAllocatorSupply_closure` folds these proofs
over a source sequence using owned statement suppliers.

The new owned entry retains `ExecSeqClosureResources`: header coverage,
body geometry, and saved-register presence. `.of_header` supplies these from
the caller's owned block; the actual back-edge proof retains them for the
tail. `LoopInput.of_entry` selects dispatch inputs directly from that entry.
Existing ordinary sequence statements are unchanged.

Generated `AllocatorCases.mExecSeq` now supplies owned sequence execution for
each physical copy. Empty sequences and the closure copy are wired into all
nine mutual induction roots. `hSeqConsNormalOther` and
`hSeqConsAbruptOther` cover only the interpreter and block copies.
`AuxMotives` has six remaining relation contracts; `Residuals` has 43 fields.

All 1,782 modules pass integration: 13 rebuilt, 1,769 reused; 34.53 seconds
compiling. All 33 declaration audits pass with standard axioms, including
the 12 new proofs and all nine generated induction roots. Eight existing
theorem headers were compared byte-for-byte. The 22 generator tests, Ruff,
and the changed generator's mypy check pass. Generator drift and forbidden
tokens pass; discipline output is unchanged. Receipt:
`/private/tmp/vsa-closure-work/equality/sequence-assembly/integration-receipt.json`.

Next: supply the interpreter and block loop copies and their owned callers.
Base closure remains 37/63.

Owned sequence entry (2026-09-10): `execSeqAllocatorAt_nil` supplies the
empty sequence for all three physical copies, preserving the caller reserve.
`ExecSeqEntryI.nilExit` exposes the same zero-step endpoint used by the
unchanged `execSeqNilI` theorem. `ExecSeqCursorRepr.closure` and
`ExecSeqHeadGround.facts` expose named cursor and child facts.
`ExecSeqAllocatorEntry.closureSuffix` identifies the owned statement array
with the actual machine cursor. `SeqClosureDispatch.LoopInput.of_cursor`
derives dispatch geometry from that array, the owned body header, and caller
facts.

All 1,780 modules pass integration: 438 rebuilt, 1,342 reused; 1,056.59 seconds
compiling after the shared sequence module changed. The seven existing
declaration audits, covering all six new proofs and `execSeqNilI`, match the
integrated source fingerprints and use standard axioms. The original nil
theorem header is unchanged. Generator drift and forbidden-token checks pass.
Discipline retains the same 56 finding identities; the existing shared
module's existential count changes from 22 to 24. Receipt:
`/private/tmp/vsa-closure-work/equality/sequence-entry/integration-receipt.json`.

Owned closure exits (2026-09-10): `SeqClosureDispatch.consRet` executes
dispatch and a value-returning child, then finishes at that same child
endpoint. `consFinal` executes dispatch, the last normal child, and the
reflected final-iteration route. Both retain the child's selected maps,
owned values, and caller allocation reserve. `SeqClosureNormalReadback.of_exit`
supplies code and saved words from the actual child frame and shared-byte
agreement. `seqClosureNormalExitRun` retains the final route's unchanged
memory. Ordinary resume theorems project the same runs; their statements
are unchanged. `OwnedPost.returnCarrier` also supplies the common caller
frame used by normal continuation.

All 1,778 modules pass integration: ten rebuilt, 1,768 reused; 25.44 seconds
compiling. Eighteen declaration audits pass, including all nine new proofs.
Six original theorem headers were compared byte-for-byte.
Generator drift and forbidden-token checks pass; discipline output is
unchanged. Receipt:
`/private/tmp/vsa-closure-work/equality/sequence-finish/integration-receipt.json`.
Source sequence assembly still requires entry-fact producers, the initially
empty case, and the other physical loop copies. Base closure remains 37/63.

Owned closure dispatch (2026-09-10): `SeqClosureDispatch.consNormal`
executes the complete normal iteration from the closure loop head:
argument dispatch, owned statement execution, reflected back edge, and
owned tail execution. `OwnedPost.carrier` derives the continuation carrier
from the reached dispatch. The eight-instruction prefix writes only the
saved body word at `sp`; `.owned` retains allocator credit, shared reads,
the actual statement entry, and all remaining child grounds through that
write. The JAL theorem is generated from `sequence_dispatch_sites.tsv`.
`LoopInput` supplies the loop's cursor/header facts and saved-register
presence. Producers for those entry facts and source sequence assembly
remain required. Base closure remains 37/63.

All 1,775 modules pass integration: six rebuilt, 1,769 reused; 9.44 seconds
compiling. All ten new declaration audits use standard axioms. Existing Lean
declaration statements are unchanged. Generated-site
reproduction, owned-recursion drift, and forbidden-token checks pass;
discipline output retains the same 56 findings. Receipt:
`/private/tmp/vsa-closure-work/equality/sequence-dispatch/integration-receipt.json`.

Owned closure sequence continuation (2026-09-10):
`seqClosureAllocatorConsNormal` composes an `ExecAllocatorAt` child, the
reflected closure back edge, and an `ExecSeqAllocatorAt` tail. It starts at
the actual child call and finishes at the sequence return. Costs add;
the request ceiling is their maximum; the caller's reserve survives.
`SeqSuffixOwned.transport_execExit` retains all remaining pointer cells,
owned AST reads, and hereditary child grounds using the actual child return.
`seqClosureAllocatorContinue` rebuilds `ExecSeqAllocatorEntry` at the next
cursor with the child's selected maps and allocator state.
`SeqAllocatorContinueAt.run_tail` rebases the tail return to the caller.
The initially empty sequence and other two physical loop copies still need
owned suppliers. The source sequence constructor is not yet closed.

All 1,770 modules pass integration: five rebuilt, 1,765 reused; 7.69 seconds
compiling. All eight new declaration audits use standard axioms. No existing
Lean declaration changed. The generator drift check
and forbidden-token gate pass; discipline output is unchanged. Receipt:
`/private/tmp/vsa-closure-work/equality/sequence/integration-receipt.json`.
Base closure remains 37/63.

Owned source recursion (2026-09-10): `AllocatorCases.Residuals.onEvalE`
and `.onExecS` assemble `EvalAllocatorSupply` and `ExecAllocatorSupply`
directly through source induction. The seven other relations have matching
induction entry points and explicit contract parameters in `AuxMotives`.
The generated recursion consumes no old `TermCases` bundle. Checked
suppliers fill the five leaves and expression statements. `Residuals.binary`
fills equality and inequality; `hBinaryOther` requires only other operators.
The remaining record has 44 constructor fields. Concrete auxiliary contracts,
their remaining suppliers, and initial allocator entry still require proofs.

`python3 -B -m scripts.gen_allocator_cases` reuses the existing authoritative
50-constructor parser. Stage a3 checks its output for drift. All 1,766 modules
pass integration (two rebuilt, 1,764 reused; 16.39 seconds compiling).
All ten new declaration audits use standard axioms. Receipt:
`/private/tmp/vsa-closure-work/equality/assembly/integration-receipt.json`.
Final audit:
`/private/tmp/vsa-allocator-cases-final/run-kevtmmun/receipt.json`.
The 22 relevant generator tests, Ruff, and mypy pass. The complete Python
suite ran 260 tests with 12 skips and one setup error: the boundary fingerprint
lock is stale against earlier changed proof sources. Log:
`/private/tmp/vsa-allocator-cases-tests.log`. The lock was not rewritten.
The forbidden-token check passes; discipline retains the same 56 findings.
The inherited base fields remain 37/63; the old `hEq` and `hNe` fields are
not supplied by this owned recursion.

Equality source suppliers (2026-09-10): `EvalAllocatorSupply.binary_eqne`
matches the result of the source binary rule and composes independently
proved child resources. The parent cost is the sum of child costs; its
request ceiling is their maximum. The right child's closure bounds follow
from the left source evaluation. `EvalAllocatorSupply` and
`ExecAllocatorSupply` select these resource witnesses before machine entry.
The five literal/variable suppliers and the expression-statement adapter
inhabit these contracts. `execAllocatorSupply_eqne_vars` proves statement
execution for arbitrary successfully looked-up operand kinds, including
closures and native functions.

All 1,765 modules pass integration (five rebuilt, 1,760 reused; 16.16 seconds
compiling). All 15 new declaration audits use standard axioms. Final audit:
`/private/tmp/vsa-equality-supply-final/run-unpnlwnk/receipt.json`.
The generator and forbidden-token checks pass; discipline
retains the same 56 findings. The existing recursive and statement sources
and the ELF are unchanged. Integration receipt:
`/private/tmp/vsa-closure-work/equality/supply/integration-receipt.json`.
The inherited base fields remain 37/63. These are source-case suppliers;
the complete resource recursor and initial allocator entry remain open.

Equality statement execution (2026-09-10): `execAllocatorAt_eqne_fixed`
composes recursive equality with the actual expression-statement dispatch
and normal return. `execAllocatorAt_eqne_nested` supplies nested integer
and string comparisons without child supplier premises. `ExecAllocatorAt N`
retains the current native addresses, selected store maps, and caller reserve
through that return. Existing expression-statement suppliers remain wrappers
with unchanged statements.

All 1,761 modules pass integration (five rebuilt, 1,756 reused; 11.54 seconds
compiling). All 35 recursive equality and statement declaration audits use
standard axioms. All 16 affected existing declaration headers are unchanged.
The ELF is unchanged; the forbidden-token check passes and discipline retains
the same 56 findings. Receipt:
`/private/tmp/vsa-closure-work/equality/statement/integration-receipt.json`.
Final audit:
`/private/tmp/vsa-equality-statement-final/run-qjrqt3ru/receipt.json`.
The inherited base fields remain 37/63. The next step is composing these
owned case suppliers through source recursion and the initial allocator entry.

Recursive equality (2026-09-10): `evalAllocatorAt_eqne_fixed` produces the
same owned child contract it consumes. `EvalAllocatorAt N` retains one run's
native addresses through both recursive calls. `EvalAllocatorIH.at` reuses
existing leaf suppliers. `evalAllocatorAt_eqne_nested` proves nested integer
and string comparisons, with either equality operator at each node, without
child supplier premises. All 12 existing declaration headers in the affected
call chain remain unchanged.

All 1,759 modules pass integration (17 rebuilt, 1,742 reused; 46.07 seconds
compiling). All 26 declaration audits use standard axioms. The ELF is
unchanged; forbidden-token and generator checks pass. Discipline retains
the same 56 findings. Receipt:
`/private/tmp/vsa-closure-work/equality/recursive/integration-receipt.json`.
Final audit:
`/private/tmp/vsa-equality-recursive-final/run-rm6bd90z/receipt.json`.
The inherited base fields remain 37/63. The statement checkpoint above
consumes this recursive supplier.

Owned equality case (2026-09-10): `evalEqAllocator_fixed` proves equality and
inequality through both children, operand copies, `value_equal`, boolean
boxing, and the outer return. It retains one selected store-map pair and
the caller's allocator reserve. Native identity follows from the fixed
binary's three addresses. Child allocator contracts, the allocation ledger,
and initial store closure bounds remain inputs.

The 998-module selected check passes both top-level declaration audits with
standard axioms:
`/private/tmp/vsa-equality-case-check/run-kt1hymo0/receipt.json`.
All 1,757 modules pass integration (12 rebuilt, 1,745 reused; 18.48 seconds
compiling). All 24 new declaration audits use standard axioms. The ELF is
unchanged, the forbidden-token check passes, and discipline retains the same
56 findings. Integration receipt:
`/private/tmp/vsa-closure-work/equality/case-integration-receipt.json`.
Final audit:
`/private/tmp/vsa-equality-case-final/run-fhfuyf0k/receipt.json`.
The inherited base fields remain 37/63; this checkpoint does not yet supply
`hEq` or `hNe`. The next step is recursive residual integration.

Equality helper checkpoint (2026-09-10): `value_equal_spec_present` retains
memory presence at the actual return. The string path retains its exact
spill memory through the epilogue and accepts `StrcmpWSlack` through
`strcmp_full_spec_cond`. The 823-module selected check passes all ten new
declaration audits with standard axioms:
`/private/tmp/vsa-equality-check/run-g507l47s/receipt.json`.
The six existing helper theorem statements remain unchanged.

`blockC_eqne_front_present` composes the call, helper, and `VeReturn` adapter.
It consumes actual return presence and the reflected register frame.
`ValueEqualStringData.of_owned` derives string witnesses from owned payloads,
shared read geometry, and the caller stack. `EqNeOp.DispatchReadback.owned`
retains both copied values, their payload ownership, shared-byte agreement,
and memory presence at the actual dispatch endpoint. Both buffers use the
same representation map. All 1,746 modules pass integration (640 rebuilt,
1,106 reused; 3,359.23 seconds compiling). All 16 final declaration audits
use standard axioms. Receipt:
`/private/tmp/vsa-closure-work/equality/integration-receipt.json`.
The owned equality case above composes these suppliers at the reached
endpoint. No new base field is closed; the last census is 37/63.

Division-overflow residual (2026-09-10): `ScaffoldRows.field_hDivOv` now
inhabits the exact inherited `hDivOv` field. The selected 1,016-module check
passes; its field probe reports `FOUND` with standard axioms only. Receipt:
`/private/tmp/vsa-div-overflow-check/run-9ttwncal/receipt.json`.

`divdi3_wrap_spec` proves the exact quotient word for every nonzero divisor.
The overflow path uses the generated branch blocks, two named constant
negation facts, and `core_call_tail_f`. `divWrapPreBridge` retains the actual
JAL frame. `blockC_div_wrap_footprint`, `evalDivWrapSim`, and generated
`binRow_div_wrap` compose both children, division, boxing, and the outer return.
All existing division theorem statements remain identical. The shared cell
proof checks at 200,000 heartbeats after factoring its footprint composition.
All 1,742 modules pass the integrated build (89 rebuilt, 1,653 reused;
313.96 seconds compiling). The final 21 declaration audits use standard
axioms only. The complete base-field census reports **37/63 closed**, including
`hDivOv`. The ELF is unchanged; discipline retains the same 56 findings.
Integration receipt:
`/private/tmp/vsa-closure-work/div-overflow-integration-receipt.json`.
Final declaration audit:
`/private/tmp/vsa-div-overflow-final/run-g809gizd/receipt.json`.
Complete census:
`/private/tmp/vsa-div-overflow-census/run-huv8xxkw/report.json`.

String-comparison family checkpoint (2026-09-10): `evalAllocatorIH_strCmp`
supplies `<`, `≤`, `>`, and `≥` through their certified descriptors. The four
named suppliers retain both child costs and every caller reserve.
`evalAllocatorIH_strCmp_literals` discharges both literal child suppliers;
it proves the full comparison and return at zero allocation cost.
The initial store's closure-bound premise remains explicit.

All 1,739 modules pass the integrated build (two rebuilt, 1,737 reused;
16.83 seconds compiling). The backend fingerprints match. Seven exact
declaration audits use standard axioms only; the ELF is unchanged and
discipline retains the same 56 findings. Receipt:
`/private/tmp/vsa-closure-work/strcmp-family-integration-receipt.json`.
Selected dependency check:
`/private/tmp/vsa-binary-entry-check/run-yk9uvwgw/receipt.json`.
Base closure remains 36/63; recursive and initial-invariant integration
remain open. Further limitation proofs are paused at the user's direction.

Initial-resource witness check (2026-09-10):
`experiments/fleet/obstructions/InitialResourceGap.lean` proves that the live
boundary admits an ownership witness with 4,480 physical bytes in a
4,096-byte arena. No allocator state can retain that extent list. The same
snapshot also has the original affordable witness (384 physical bytes).
This refutes arbitrary-witness-preserving budget inference, not existential
ledger selection or the refinement theorem. All ten declaration audits use
standard axioms only. Receipt:
`/private/tmp/vsa-closure-work/resource-gap/receipt.json`.
The 1,739-module backend remains fingerprint-current; no library proof changed.

Literal-allocator checkpoint (2026-09-09): all 1,739 source modules pass
(exit 0; two rebuilt, 1,737 reused; 13.71 seconds compiling). Backend
fingerprints and all 106 frozen source hashes match. The exact audit passes
290 declaration reports across 105 affected modules. Receipt:
`/private/tmp/vsa-closure-work/literal-allocator-integration-receipt.json`; log:
`/private/tmp/vsa-closure-work/literal-allocator-integration-build.log`.

Both binary prefixes retain their exact step counts, actual writes, and
register frames. `blockB_binary_leftStaged` and `binaryR_midStaged` retain
fixed `JalPreCore` witnesses. Their allocator-call adapters transport the
allocator and AST through the actual prefix and child execution. The right
call uses the reached register ghost, including its overwritten `x19`.
Ownership rebasing changes the origin memory while retaining the selected
maps and returned endpoint. The legacy theorem statements remain unchanged.
The selected 977-module case check passes both requested declaration audits:
`/private/tmp/vsa-binary-entry-check/run-6miz0t64/receipt.json`.

The ELF hash is unchanged. Four generator checks, the forbidden-token scan
on 1,738 library sources, and `git diff --check` pass. All seven R15 findings
are removed; discipline retains the original 56 findings. Source review
found no concrete defect.

Closure remains 36/63 base fields. The complete string `<` case is proved
from two allocator child contracts. The resource-indexed recursor, allocator
suppliers, initial geometry, `DivWork`, `ErrWork`, and completion gates remain
open. No recursive proof machinery changed in this checkpoint.

### Completed literal allocator suppliers

`evalAllocatorIH_int`, `evalAllocatorIH_null`, `evalAllocatorIH_bool`, and
`evalAllocatorIH_str` preserve every caller reserve at zero allocation cost.
`EvalExitPinned.allocatorReturn` uses the actual leaf memory pin, transports
the allocator through stack writes, and retains the entry representation maps.
The string supplier uses `StrReturnPin.pointer` to identify the returned
pointer with the represented AST pointer; `ExprReprWithin` supplies shared
coverage through the terminator. No child simulation premise remains in these
four suppliers. Source review found no defect.

The selected 938-module check passes all six declaration audits:
`/private/tmp/vsa-binary-entry-check/run-a1yprl_8/receipt.json`.

### Completed case: string `<` execution and return

`evalAllocatorIH_strLt` supplies the full `<` case at cost `costL + costR`,
preserving every caller reserve. It consumes the two allocator child contracts,
the left semantic derivation, and the initial store's closure bounds.

`evalStrCmpAllocator` executes the owned entry, both children, certified
comparison, boolean construction, and outer return. It composes
`evalBinaryAllocatorOperands`, `blockC_strcmp_footprint`, and
`blockD_v_rec_coherent` at their actual endpoints. The final allocator keeps
the children's selected maps, allocations, extents, shared domain, and
reserve. Shared agreement reaches back to the original entry memory; the
actual global pointer is preserved.

`strCmpOperandsAt_of_readOwned` derives comparison geometry from the actual
owned strings and `SharedReadGeom`, reusing `strcmpWSlack_of_shared`. The
cell footprint lies inside the whole stack, so `RuntimeAllocatorState.after_stack`
transports ownership through the tail. Boolean representation is reindexed
at the retained maps at the same returned state.

The `hStrLt` base field still requires recursive and initial-invariant
integration. This checkpoint closes the concrete case under its child contracts.

`BinaryArmReady.stage_right` exposed an excess premise in
`binaryR_midStaged`: the arm supplies `tohostAddr + 16 ≤ node`, while the
staging theorem required `+32`. The reflected load needs only the former.
The failed check is recorded in
`/private/tmp/vsa-closure-work/binary-entry/resume-check-1.log`.
`binaryR_midStaged_of_nodeWindow` uses the supplied bound; the existing
`binaryR_midStaged` statement remains an unchanged wrapper.

`BinaryArmReady.stage_right` constructs the right entry from the left return's coherent store
survival, `EvalGround.sret_inSL`, shared AST agreement, saved environment
word, and frame-map extension. `EvalGround.transport_via` and
`EvalCallSupport.transport_frame` supply ground transport. A generated named
`SubEvalReturn` destructurer exposes the actual child frame and presence.
`BinaryPrefix.bind_operands` consumes the right core call before ownership
rebasing; the high-level right wrapper has already rebased its result and
instead composes through `AllocatorResultAt.bind_return`.

### Shared recursive-call checkpoint

Shared call and operand-composition checkpoint (2026-09-09): all 1,717 source
modules pass (exit 0; 538 rebuilt, 1,179 reused; 1,820.35 seconds compiling).
Backend fingerprints and frozen source hashes match. The exact audit passes
206 declaration reports across 79 affected modules. Receipt:
`/private/tmp/vsa-closure-work/allocator-call-integration-receipt.json`; log:
`/private/tmp/vsa-closure-work/allocator-call-integration-build.log`.
The source manifest is `allocator-call-integration-sources.json` in the same
directory. The selected 837-module check also passes its eight requested
declaration audits: `/private/tmp/vsa-allocator-binary/run-49h4bfsx/receipt.json`.
The ELF hash is unchanged; all module times satisfy the existing budget gate.

`armTail_rec_frame` retains the existing JAL's ABI relation before invoking
the child. `armTail_rec_gen` keeps its original statement and delegates to it.
`EvalAllocatorIH.at_call` and `armTail_rec_allocator` transport captured
allocator and AST facts through the actual entry-memory equality and retain
the coherent allocator return. `AllocatorResultAt.bind_return` uses
`ReturnRepr.bind` to combine actual child returns at the second child's maps.
It derives shared payload survival from the right return and retains both
operands' ownership through domain growth. The caller supplies the left
header frame and semantic closure bound. Source review found no defect.

### Allocator return checkpoint

Allocator return checkpoint (2026-09-09): all 1,714 source modules pass
(exit 0; seven rebuilt, 1,707 reused; 11.34 seconds compiling). Backend
fingerprints and frozen source hashes match. The exact audit passes 195
declaration reports across 75 affected modules, including all eighteen new
theorems. Receipt:
`/private/tmp/vsa-closure-work/allocator-integration-receipt.json`; log:
`/private/tmp/vsa-closure-work/allocator-integration-build-2.log`.

`RuntimeAllocatorState` retains `HeapOwned`, store representation, array
readiness, shared read geometry, `AInvAt`, and credit at one extent list and
memory. `AllocatorResultAt` retains those witnesses at the producer's selected
maps. `EvalAllocatorIH` and `ExecAllocatorIH` require sufficient entry credit
under a request ceiling and retain an arbitrary caller reserve. Entries and
returns pin the actual global pointer. These contracts do not independently
record allocation counts or request sizes along execution.

`evalAllocatorIH_var` preserves the original extents and all credit through
the variable's exact memory frame. `EvalChildArm.call_allocator` retains the
same allocator through statement dispatch and invokes the child contract.
`execAllocatorIH_expr` retains the child result through the unchanged-memory
tail; `execAllocatorIH_var_statement` instantiates it at zero credit cost.
`AllocatorResult.rebase_shared` composes return agreement and domain inclusion
after shared-domain growth. Source review found no proof defect.
`AllocatorIH`, `AllocatorResult`, and `AllocatorChildCall` have no dependency
on `TermSimAssembly`.

Remaining work includes source-derived resource parameters, concrete allocator
suppliers, shared-domain growth through heap updates, recursive case wiring,
and initial geometry. Closure remains 36/63 base fields. The ELF hash is
unchanged. All four generator checks and `git diff --check` pass. The
forbidden-token scan passes on 1,713 library sources; discipline retains the
same 56 findings. The full completion gates remain open.

### Owned recursive data checkpoint

Owned recursive data checkpoint (2026-09-09): all 1,706 source modules pass
(exit 0; seven built, 1,699 reused; 17.56 seconds compiling). Backend
fingerprints and frozen source hashes match. The exact audit passes 177
declaration reports across 67 affected modules. Receipt:
`/private/tmp/vsa-closure-work/runtime-ih-integration-receipt.json`; log:
`/private/tmp/vsa-closure-work/runtime-ih-integration-build.log`.

`RuntimeResultAt` retains the actual runtime, owned values, shared-domain
inclusion, and preservation of the caller's shared bytes. Its allocation and
extent witnesses may evolve. `EvalRuntimeIH` and `ExecRuntimeIH` consume owned
entries; their returns use one coherent representation pair. The contracts
and generic child-call adapter have no dependency on `TermSimAssembly`.
`evalRuntimeIH_var` closes the variable supplier. `execRuntimeIH_expr` invokes
an owned child IH and retains its runtime through the unchanged-memory tail.
`execRuntimeIH_var_statement` connects both. The selected 1,092-module check
passes all thirteen new declaration audits:
`/private/tmp/vsa-runtime-ih/run-vkz5ykj6/receipt.json`.

The `RuntimeIH` contracts retain store data but omit allocator state. Allocating
recursion must retain `HeapOwned`'s immutable reservations, `AInvAt` at the
evolved extent list, and resource bounds. Shared-byte agreement alone cannot
preserve allocator-private metadata. Free/realloc remove extents, so extent
inclusion is not a valid invariant. Existing owned allocator adapters preserve
entry shared bytes; a shared-domain growth adapter remains open. Keep transient
stringification buffers outside that persistent shared domain.

The full resource-indexed recursor and the initial geometry suppliers remain
open. Closure is still 36/63 base fields. The ELF hash is unchanged. The
forbidden-token scan passes on 1,705 library sources; discipline retains the
same 56 findings with none added by this batch.

### Lookup and statement-entry checkpoints

Lookup integration checkpoint (2026-09-09): all 1,694 source modules passed
the resumed build (exit 0; 55 built, 1,639 reused). The 54 installed modules
match their staged source hashes; all 149 canonical declaration reports pass
the exact standard-axiom audit. Backend fingerprints and the ELF hash pass.
Receipt: `/private/tmp/vsa-closure-work/lookup-owned-integration-receipt.json`.
Build log: `/private/tmp/vsa-closure-work/lookup-owned-integration-build.log`.
The preintegration receipt checks 153 draft reports; the canonical generated
`FixedImage_Env_get` prints its full theorem once, omitting four draft chunk
reports. Those chunk proofs remain dependencies of the full theorem.

`EnvGetReflected.eval_var_owned` now executes a variable from
`EvalRuntimeEntry`, deriving its name pointer and shared string from the AST.
The result retains the represented value, ownership, memory presence,
footprint, and query-independent `StoreRuntimeData` at the same endpoint.
The latter retains array readiness and the allocation ledger for subsequent
calls. `eval_var_product` derives the corresponding pointwise product facts.
Ordinary `EvalEntry` still supplies no owned-store precondition; the old
universally quantified `VarProductStep` and recursive motives remain open.

Native names require shared read geometry that admits ELF rodata. The binary
stores `print`, `println`, and `assert` payload pointers at `0x80019538`,
`0x80019540`, and `0x80019548`. `SharedGeom` requires every shared byte to be
above `0x8001acf0`. `native_print_above_image_impossible` proves the resulting
contradiction for the actual print payload pointer. The additive
`SharedReadGeom` permits either side of the comparison code and HTIF windows,
with RAM slack and stack exclusion. `shared_string_window` derives complete
string windows; `native_names_read_geometry` checks the three literal ranges.
The new lookup pipeline uses this geometry. Existing above-image contracts
are unchanged and still need compatible recursive siblings.

Statement dispatch now retains ownership through `ExecRuntimeEntry` and
`EvalChildArm.dispatch_runtime`. The adapter consumes the existing
carrier's exact memory frame and selected child pointer, transporting the
owned store, array readiness, and `StmtReprWithin` before selecting the child
with `StmtExprChild`. `variable_runtime` composes that dispatch with the
actual variable evaluation.

`epilogueTail_memory` and `normalExitTail_memory` retain unchanged memory
from the existing statement epilogue. The original theorem statements are
unchanged. `exec_variable_statement_owned` now proves complete execution of
a variable expression statement, retaining runtime ownership and shared-byte
agreement at its normal return. This supports subsequent statement execution
without reconstructing ownership from an ordinary exit.

The selected 1,115-module dependency check passes all 15 requested declaration
audits. Receipt: `/private/tmp/vsa-runtime-propagation/run-c0wp892b/receipt.json`;
log: `/private/tmp/vsa-closure-work/runtime-propagation-check-5.log`.
Six new modules and the shared epilogue amendment are imported into `Vsa`.
The resumed integration build passed all 1,700 modules (exit 0; 182 built,
1,518 reused). Total compilation time was 523.4 seconds; the slowest module
took 28.6 seconds. All backend fingerprints and frozen source hashes match.
The exact audit passes 164 declaration reports across 61 affected modules,
including the preceding lookup batch. The ELF hash is unchanged.
Receipt: `/private/tmp/vsa-closure-work/runtime-integration-receipt.json`;
log: `/private/tmp/vsa-closure-work/runtime-integration-build.log`.
All four generator checks pass. Discipline still reports the same 56 findings;
this batch adds none. The forbidden-token scan passes on all 1,699 library
sources. `VsaRun` is also included in the source build. These checks do not
close the full completion gates below.

`OwnedInitialExecFacts.execRuntimeEntry` retains the actual initial ownership
and exact statement AST. It still requires hereditary ground, stack/body
bounds, and `SharedReadGeom` for the initial domain. `InitialOwned` supplies
ordinary readability and write exclusion, which do not establish all of that
read geometry. Recursive return motives, allocation updates, and all completion
gates remain open. No base field was newly certified: 36/63 remain certified.

### Earlier checkpoints

Recovery checkpoint (2026-09-09): `/private/tmp/vsa-closure-work` and
`/private/tmp/vsa-full-build.sQd0gM` were absent at resumption. The process
inspection found no running proof compiler. Earlier temporary receipts and
drafts are unavailable on disk; their recorded results need fresh validation.
The recovery build of the 1,640-module source tree stopped at module 981,
`rows/EnvDefineScanLoop.lean` (exit 1). Its `envDefineScanCompare` still assembles
`strcmp_full_pre`, which requires `StrcmpWRegion`, from `ScanNames` fields now
typed as `StrcmpWSlack`. `rows/EnvDefineScanFramed.lean` has the same stale call.
Both now use `StrcmpEntryCond` and `strcmp_full_spec_cond`, as the lookup and
update scans already do. The inherited theorem statements stay fixed. Both
modules compile; their eleven printed declaration reports pass the exact
standard-axiom audit. Receipt:
`/private/tmp/vsa-closure-work/env-define-scan-repair-axioms.json`.
Failure excerpt: `/private/tmp/vsa-closure-work/env-define-scan-first-failure.txt`.
Build log:
`/private/tmp/vsa-closure-work/recovery-build.log`.
The resumed build passed all 1,640 modules (exit 0), reusing 980 and compiling
660. Log: `/private/tmp/vsa-closure-work/recovery-build-2.log`. The draft
checker's backend fingerprint preflight passes on this completed build.

Fresh lookup validation passed all 34 modules and all 98 exact declaration
audits (exit 0, 64 seconds). Receipt directory:
`/private/tmp/vsa-env-get-frame.r3jkuR`; log:
`/private/tmp/vsa-closure-work/draft-check-8.log`. Both backend fingerprint
checks passed. Sources, manifest, objects, logs, and audits are hashed.
`lookup_return` now verifies entry, parent/frame scans, copy, and return at
one endpoint with ownership, memory presence, output, and caller registers.
Its axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
The copy proof stays within default limits by separating segment facts and
the stack-register log equality. Integration into `Vsa`, the variable bridge,
and caller entry/window suppliers remain open. No base-field count changes.

The caller-prefix checkpoint now passes 36 modules and 108 exact axiom
audits (exit 0, 80 seconds). Frozen evidence:
`/private/tmp/vsa-env-get-frame.xzOf6G`; log:
`/private/tmp/vsa-closure-work/draft-check-10.log`. Source and artifact hashes
match; both backend fingerprint checks pass. `EvalVarCallFrame` executes
the generated argument prefix and JAL with its full frame.
`EvalVarLookupEntry.var_lookup` composes it with `lookup_return` from the
semantic `Store.get?` result, retaining the same value, owned store, registers,
memory presence, footprint, and output at `0x80003444`.
`LookupData.var_prologue` derives the header reads and bounds from the owned
represented frame. Caller windows supply spill/mask separation and alignment;
the legacy prologue's stronger `tohostAddr + 64` gap remains explicit.
Source review found no semantic defect. This checkpoint predates the final
variable copy/return tail below.

The complete variable-arm checkpoint passes 43 modules and 133 exact axiom
audits (exit 0, 84 seconds). Frozen evidence:
`/private/tmp/vsa-env-get-frame.FqKWXo`; log:
`/private/tmp/vsa-closure-work/draft-check-13.log`. Source and artifact hashes
match; both backend fingerprint checks pass. The proof ELF is unchanged.
`EvalVarTail*` reuses the generated value-return segment. `var_lookup_tail`
composes successful lookup with the branch, final copy, and register restores.
`VarReturnResult.at_arm` constructs `EvalReturn` from the actual return and
`ArmEntryK`, retaining store/value ownership at the same maps and memory.
It derives whole-stack store survival and the tighter footprint below the
original stack pointer. `var_arm_data` supplies caller windows, saved words,
tail geometry, and the legacy HTIF gap from the reached arm and 2,176-byte
entry headroom. `var_arm_return` checks the complete arm execution.

The remaining entry work is explicit: retain `blockA_k`'s memory presence
and environment register, transport lookup ownership and array readiness to
the arm, and supply whole-stack arena separation. `EvalEntry.envset_defined`
already supplies x19–21; `EvalEntry.ground.sret_inSL` supplies destination
membership. The ordinary entry still lacks the owned-store supplier.
`ArmEntryRetained.lean` now verifies the shared prologue adapter through
`blockA_k`, retaining those two outputs at the same arm endpoint. The final
checkpoint passes all 44 draft modules and 134 exact axiom audits (exit 0,
84 seconds): `/private/tmp/vsa-env-get-frame.NaIo6m`, log
`/private/tmp/vsa-closure-work/draft-check-14.log`. Every current draft source
matches its frozen copy; source/artifact hashes and backend fingerprints pass.
Integration into `Vsa`, recursive ownership propagation,
the product clause, and the completion gates remain open. No base field was
newly certified.
The draft history below records earlier, unvalidated stages.

Seventeen recovered lookup modules and the return/bridge patches are preserved
in `experiments/wip/env-get-frame/`. Its README records source variants and
recovery provenance. The owned-name supplier imports the identical ownership
lemmas already in `RuntimeOwnershipLookup`. The parent import is corrected;
the parent and scan-start address proofs now reduce bitvector numerals before
`omega`. These repairs await compilation after the active rebuild. Both
patches pass `git apply --check`. All four generator checks pass. The discipline
gate still reports 56 findings. No new field is certified by this checkpoint.

`EnvGetFrameParent.lean` adds a draft composition of the represented parent
read and the generated taken branch, retaining `FrameRegisters` and the eight
caller registers. `kept_of_members` now supplies the fixed-scan, count, and
parent register-set checks. This eighteenth module awaits compilation;
prologue execution and hit-tail composition remain open.
`experiments/wip/env-get-frame/check.sh` checks the recovered dependency order
against a fingerprint-current backend. Shell syntax passes, and its preflight
correctly rejects the incomplete recovery backend before launching Lean
(`recovered-check-refusal.log`). Axiom reports still require auditing.

`EnvGetLookupData.lean` stages the nineteenth module: `LookupData.frame_state`
supplies any reached frame from ownership and array readiness; `frameIndex`
uses `StoreRepr.φf_inj` to decode its pointer; `measure_head` identifies the
outer-loop rank with the source frame index plus one. `LookupData.parents`
retains `StoreParents`, which makes a parent index smaller.
`EnvGetLookupLoop.lean` adds the twentieth module: `lookup_loop_body` composes
frame scanning with the represented parent transition and proves that rank
decreases; `lookup_loop` folds it through `loopFromBody`. The exit retains
the selected source binding, caller registers, output, and unchanged memory
at `0x80002c70`. Prologue ownership transport must supply `LookupData` at its
actual memory; the hit-copy and return tail still need composition. All these
declarations await compilation. A source-only review found no further concrete issue in
the parent and frame adapters; it supplies no compilation evidence.

`EnvGetLookupTransport.lean` adds the twenty-first draft module.
`LookupData.after_spill` applies the existing owned-store, representation,
array-readiness, shared-string, and mask transport lemmas to the actual
prologue memory agreement. `LookupSpillWindow` retains stack containment and
arena/mask separation, to be supplied from the caller geometry. This adapter
awaits compilation with the other drafts; prologue execution and the copy/return
tail remain open.

`EnvGetPrologueData.lean` and `EnvGetPrologueFramed.lean` draft the generated
non-null branch and spill-block composition. `prologue_log` normalises the
actual write log; `prologue_saved` reads its seven saved words through
`read64_of_writeLog_at`; `prologue_framed` retains those words, the reached
`FrameRegisters`, both code predicates, output, and the caller register frame
at `0x80002c40`. `TransportEnv_getRange.lean` is emitted by `gen_transport.py
env_get --exact-range --stdout`. The checker now includes twenty-four modules.
These additions await compilation; entry-to-loop composition and copy/return
closure remain open.

`EnvGetLookupEntry.lean` drafts `lookup_entry`, composing `prologue_framed`,
`LookupData.after_spill`, and `lookup_loop`. `EntryLookupResult` retains the
selected source binding, ownership/read suppliers, saved words, caller frame,
output, and spill agreement at the actual copy-head memory. This twenty-fifth
module awaits compilation. The copy/return tail and caller-geometry suppliers
remain open.
Source review of the prologue and entry composition found a missing namespace
opening, now repaired, and no further concrete issue. Shell syntax and
`git diff --check` pass. These checks supply no Lean-validation evidence.

`EnvGetLookupSource.lean` drafts `LookupExit.owned_hit`. It derives
`EnvGetOwnedSource` and `EnvGetSourceAccess` for the exact frame and index
retained by the scan, together with the reached copy registers. The checker
includes this twenty-sixth module; compilation remains pending.

`EnvGetCopyLog.lean` drafts the generated hit-copy log equality and its
representation/ownership result through the shared `copy3Log` lemmas. The
checker includes twenty-seven modules. This does not yet execute the copy:
the interleaved load facts and restore-tail composition remain open.
Source review found no concrete issue in the log equality or copy result;
compilation and axiom checks remain pending. `git diff --check` and checker
shell syntax pass; the ELF hash matches the recovery baseline.

`EnvGetRestore.lean` drafts `restore_framed`: seven `WordLoadFacts` from the
actual saved-word reads supply the generated restore/return segment. Its
result retains the caller frame, restored registers, unchanged memory, and
output at the return address. The checker includes twenty-eight modules;
compilation remains pending. Copy execution and its composition with this
tail remain open.
`PrologueSaved.transport` retains those words across the actual copy's byte
agreement. Source review found no concrete issue in the restore execution;
it is not compilation evidence. Checker shell syntax and `git diff --check`
pass.

`EnvGetCopyData.lean` drafts `copy_data`. It supplies the header and three
value-word loads through `WordLoadFacts`; source/output separation transports
the two loads after destination writes at their actual memories. The same
byte witnesses determine the generated log through `copy_log_of_loads`.
The checker includes twenty-nine modules. Compilation is pending; copy
execution, restore composition, and caller geometry still need closure.
Source review caught a missing `Sail` namespace opening, now fixed, and
found no further concrete issue. This supplies no compilation evidence.

`EnvGetCopyFramed.lean` drafts `copy_framed`, applying `segment_framed` to
the supplied copy facts. It retains the stack pointer, success result,
caller frame, code, and exact copied memory at the restore head. The checker
includes thirty modules. All await compilation; restore composition and
caller-geometry suppliers remain open.
Source review found no concrete issue in the copy execution wrapper. Checker
shell syntax and `git diff --check` pass; none certifies the Lean declarations.

`EnvGetHitTail.lean` drafts the copy/restore composition for the machine-selected
owned binding. Its result retains the represented value, ownership, exact copy
memory, caller frame, and return registers. Source review found no concrete
issue. `EnvGetHitGeometry.lean` derives the tail's source bounds from the
selected frame and slot; `CallerTailWindow` and `SharedGeom` supply output
separation. The load-only HTIF bounds now use eight bytes, matching
`LookupData.arenaHtif`; stores retain their sixteen-byte condition. The checker
includes thirty-two modules. Compilation and whole-entry composition remain
pending; the caller must still supply the static windows and entry data.
Source review found no concrete issue in the geometry supplier. Checker shell
syntax and `git diff --check` pass; neither substitutes for Lean validation.

`EnvGetOutputTransport.lean` drafts owned-store and lookup-data transport
through the actual output-copy frame. `EnvGetLookupReturn.lean` composes the
prologue, parent/frame scans, selected copy, and restore at one return state.
It retains value/store ownership, caller registers, memory presence, the
output/spill footprint, and output. The prologue and entry carriers now retain
memory presence from the actual write log. The checker includes thirty-four
modules; compilation is pending. Entry-data/window suppliers and integration
with the variable-expression bridge remain open.
The complete return also retains the inherited `EnvGetEntryPost` at the same
endpoint, using the actual hit memory as its intermediate witness.
`HitTailResult.toValuePost` projects its value post. Source review found no
concrete issue in these adapters or the memory-presence/data transports;
compilation and axiom audits remain pending.
The draft declaration audit found 94 explicit theorems and two locally
generated destructurer declarations. Four generated code-transport chunk
helpers had only aggregate axiom coverage; each now has its own print command.
All 96 declarations have direct report requests. No reports have yet been
validated against a fresh compilation of these drafts.
`axioms.json` now lists those 96 exact names across all 34 modules. The checker
freezes and hashes it with the sources and calls `proof_slice.audit_axioms`
after each compilation. Manifest coverage, uniqueness, shell syntax, and
`git diff --check` pass. Actual compilation remains queued behind the recovery
build; these metadata checks do not validate a proof.

**36 of 63 base fields certified; 27 remain.** `DivWork`, `ErrWork`, and the
final constructor remain open. The certified fields cover literals, unary and
logical operations, nine integer cells, break/continue, both initializers,
all four while cases, the expression statement, all three `if` cases, all
four for-loop cases, and the null return. Their shared entry and ownership
suppliers still need integration.

The null return, the null declaration, the initialised declaration, the
block, and the for-loop start are on the helper-call layer (`HelperCall`,
task 4): the generic in-frame call of a runtime helper from any parked
state, one adapter per callee, and the shared retslot/declaration tails.
`hSRetNull` is closed. `hSVarNull` and `hSVarInit` are closed down to the
`env_define` contract (`EnvDefineContract`), plus for `hSVarInit` the payload
window (`VarInitPayloadOff`); `hSBlock` and `hSForStart` are closed down to
the `env_new` contract (`EnvNewContract`). Both contracts are proved from
named per-entry ledgers of external facts (allocator invariant and runs,
ownership, pinned `gp`, geometry; task 2), so every statement field above
rests on those ledgers only. The child's coherent exit is the recursor
motive (`mEvalE := EvalReturnIH TrivialOwned`), not a premise. The three
legacy files of these leaves (1,548 lines) are removed.

The expression statement, the three `if` cases, and the four for-loop cases
are closed by the parametric statement-arm layers (`EvalChildArm`,
`StmtChildArm`, `TruthyCopy`, see task 4): generic dispatch of an expression
or statement child (from the statement entry or from an in-frame arm state),
exit kits, condition copy with `value_truthy`, reflected routes from any
parked return, the normal-exit and return heads, the loop-head re-entry, and
the map/memory rebase, instantiated per arm by a descriptor and
certificates. The value-return arm is closed on the layer down to one named
payload premise; the initialised-declaration arm's resume needs the
`env_define` contract (task 4).

The four string-comparison cells (`hStrLt`, `hStrLe`, `hStrGt`, `hStrGe`) are
on the string-comparison cell layer (`StrCmpCell`, task 4): one descriptor and
one decided certificate per operator instantiate ONE generic proof of the
dispatch, the kind check, the `strcmp` call, the rejoin, the operator's sign
tail, and the `value_bool` box. Each cell is closed down to the two residuals
the layer shares, `StrCmpOperandsSupply` (both operand payloads are
`strcmp`-admissible regions at the actual return) and `StrLeftSurvivesSupply`
(the left string survives the right child). The second is the `hVlSurv`
premise of `blockB_binary_data`, recorded below as an obstruction for arena
payloads; it is the same premise the equality cells carry.

The last completed checkpoint passed 1,587 modules (private resumed build
after the sequence-boundary amendment), 1,054 declaration axiom audits
(1,040 with exactly {propext, Classical.choice, Quot.sound}, 14 axiom-free),
four boundary regressions, 200 Python tests, and the generator checks.
There are 56 inherited discipline findings (unchanged by this checkpoint).
Receipt: `/private/tmp/vsa-helpercall/receipt.json`.

Indexed child returns and the shared coherent epilogue now pass the full
1,539-module build and cache-fingerprint verification. Log:
`/private/tmp/vsa-indexed-child/integration.log`. The parametric layers, the
closed expression statement, the three `if` cases, and the four for-loop
cases pass the resumed private build, the complete-library census (35 FOUND
of 65 inventoried fields), the four boundary regressions with a refreshed
input lock, 200 Python tests, and the axiom audit of every new declaration.
Evidence: `/private/tmp/vsa-evalchildarm/` (`integration*.log`,
`all-fields*/`, `boundary-lock-changes*.json`, `discipline-delta*.json`).

The helper-call layer and its three fields pass the resumed private build
(1,566 modules, exit 0; log `/private/tmp/vsa-helpercall/logs/integration.log`)
and the census of the affected fields (`hSRetNull` FOUND; `hSRet`,
`hSVarNull`, `hSVarInit` NO_MATCH, each with a hypothesis-taking supplier;
`/private/tmp/vsa-helpercall/census/`), the four boundary regressions with
the input lock refreshed for the eight changed proof sources
(`/private/tmp/vsa-helpercall/boundary/summary.json`,
`boundary-lock-changes.json`), 200 Python tests, and the generator checks.
The discipline gate (stage a4) reports 32 inherited findings and none in the
new files (`discipline-delta.json`); the gate stops there, so stage c was
run by hand against the private build. Twelve audit entries naming
declarations no longer present (`execVarNullSimD`, `bin_add_cell_ofBundle`,
`argsConsResid_of_oracle`, `argsNilResid_of_hop`, the three
`native*Spec_of_span`, `errFamily_ofArmLinks`,
`divEntryDrive_of_driveToLoopHead`, and the commented-out `errFamilyClosed`,
`errFamilyClosed_ofClasses`, `errFamily_ofShared`) were pruned, and
`rows/EvalVarBridgeCallee` (compiled but never imported by `Vsa`) is wired so
its two audited theorems resolve. The hand-run audit of the 987 remaining
entries reports every axiom set within `propext`, `Classical.choice`,
`Quot.sound` (13 entries axiom-free; no `sorryAx`, `native_decide`, or
`ofReduceBool`; log `/private/tmp/vsa-helpercall/logs/stagec.log`). The full
SMT/fuzzer campaigns are pending.
The string-comparison cell layer passes the resumed private build (1,591
modules, 25 rebuilt, exit 0; log
`/private/tmp/claude-501/-Users-kirancodes-Documents-code-verified-semantic-abstraction/3f98120e-d469-40e3-ab61-f89a096c4e7c/scratchpad/integration.log`),
the backend verification, the four boundary regressions with the input lock
refreshed for the fifteen changed proof sources (`boundary/summary.json` and
`boundary-lock-changes.json` in the same directory), 200 Python tests, the
generator checks, and the discipline gate with the 56 inherited findings
unchanged and none in the new files. The stage c audit (run by hand, the gate
stopping at stage a4 as before) covers 1,060 entries after replacing the seven
retired scaffolding names by the seven new theorems and removing eight
duplicate names from the list; every axiom set is within `propext`,
`Classical.choice`, `Quot.sound` (`stagec3.out` in the same directory).

The induction-hypothesis tower (task 0) passes the resumed private build
(1,621 modules, 455 rebuilt, exit 0), the backend verification, the four
boundary regressions with the input lock refreshed for 26 changed sources,
241 Python tests, the four generator drift checks, stage b, and the
discipline gate with the 56 inherited findings unchanged and none in the 41
new files; the stage c audit (run by hand) covers 1,081 entries after adding
the tower's key theorems. Evidence under the session scratchpad
(`integration2.log`, `boundary2/summary.json`, `boundary-lock-changes-2.json`,
`stagec4.out`).

The allocator layer (task 2) lands `Vsa/Sim/AllocOff.lean` and
`Vsa/Sim/AllocLedger.lean`: one run-global `AllocLedger` in place of the
allocator fields each per-entry ledger restated, one `OwnedOff`/`EntryOff` proof
in place of the per-lane separation derivations, ledger movement
(`HeapOwned.fresh`/`.free`/`.pushClosure`), and the `malloc`/`free` call adapters
`mallocReturn_of_parked`/`freeReturn_of_parked`. The two modules add 48
declarations, 26 of them audited by `#print axioms` at exactly `propext`,
`Classical.choice`, `Quot.sound`. Three landed sites are
reseated on it: `envNewPushedRepr` and the `env_define` append and grow lanes
(53 hand lines of separation replaced by 24, all of it projection). Discipline
rule R14 catches a hand-rolled allocator ledger field; the gate reports 68
findings, the 56 inherited ones plus the 12 per-entry ledger declarations the
new `of_alloc` projections supply and the reseat will delete.

Verified over the eleven-module dependency closure of the change plus `Vsa` and
`VsaRun`, all thirteen compiling clean in 62 s with every axiom set inside
`propext`, `Classical.choice`, `Quot.sound`; the generator drift checks pass and
no source of this change is a boundary-lock input, so the input lock needs no
refresh. Log: `rebuild.log` under the session scratchpad. NOT yet run for this
change: the complete-library census and the full resumed integration build, both
deferred because a second session holds concurrent in-flight edits to the
induction-hypothesis tower in the same checkout.

Recompute the census before changing the certified count.

## Remaining tasks, in dependency order

### 0. Induction-hypothesis clauses through the tower

A new fact about a child's execution (a memory footprint, payload ownership,
shared-byte agreement) is a CLAUSE, never an edit of `mEvalE` or of a landed
row's post. The tower that makes a clause cheap:

1. Effect summaries: every arm block has a footprint-carrying sibling
   (`blockC_<cell>_footprint`, `blockB_*_footprint`, `blockD_v_rec_footprint`)
   and every row an `EvalIHF F` supplier (`Vsa/Sim/ExitFootprint.lean`, the
   `*Footprint.lean` modules). The landed theorem is always the projection of
   its sibling, so no certified row changes statement.
2. Clause metatheorems: a clause SHAPE is one lemma over `MemFootprint`
   (`Vsa/Sim/IHClauseFootprintMeta.lean`); the per-case steps of a clause are
   generic over arms (`Vsa/Sim/IHClauseGeneric.lean`, allocating arms in
   `IHClauseGenericAlloc.lean` over the allocator contracts).
3. Generation: `scripts/ih_clauses.tsv` + `scripts/gen_ih_clause.py` emit the
   clause's `EvalIHWithM` motive, one named `Residuals` field per recursor
   case, and the recursion (`rows/IHClause_<Name>.lean`); declaring a clause
   never breaks the build.
4. Automation: `scripts/ih_clause_status.py` (WIRED/HOOK/MANUAL per field,
   backend lemma probe, `--suggest` drafts), `ih_clause_fuzz.py`
   (refute-before-prove), `ih_clause_ledger.py`, `proof_slice --structure`,
   `check_all.sh` stage a5.

Open steps on the tower, in order: (a) DONE: the generator has a `guard`
column (`scripts/gen_ih_clause.py`, `scripts/ih_clauses.tsv`) — a guard makes
the `EvalE` motive `<guard> → EvalIHWithM extraM …`, and the new tag
`unguarded:<term>|<proj_1>|…|<proj_k>` wires a step stated without it. Clause
`FootprintNA` (`Vsa/Sim/rows/IHClause_FootprintNA.lean`, guard
`IHClauseGeneric.noAllocExpr e = true`) has 13 of 15 fields wired: the three
allocating cases vacuously (`footprintNA.{hAssign,hFn,hCall}`), the four leaves
from the unguarded closed leaf steps, and `hNeg`/`hNot`/the four logical steps
from `footprintNA.<case>` applied to the closed row contracts of
`Vsa/Sim/IHClauseGenericSupply.lean`. Clause `Footprint` wires the four closed
leaves and the six one-child arms (`IHClauseGeneric.footprint.<case>`) and keeps
five `generic:footprint` hooks (`hVar`, `hBinary`, and the three allocating
cases, which are FALSE at `noArenaFoot`). OPEN in (a):
`FootprintNA.hVar` (supply from `Rows.evalVarIHF` over `Rows.VarLeafResidF`;
`footprint.hVar_of`'s `VarPinnedSim` is uninhabitable as stated) and `FootprintNA.hBinary` (`footprint.hBinary_of_cells` needs
`BinaryFootprintCells`), i.e. step (b); the guarded clause is a stepping stone —
allocating arms need the `allocFoot` family of task 2. (b) LANDED except the var
leaf (`Vsa/Sim/IHClauseGenericSupply.lean`): the six one-child steps
`footprint.{hNeg,hNot,hOrTrue,hAndFalse,hOrFalse,hAndTrue}` are CLOSED from the
landed `eval<Arm>IHF` suppliers; the nine `IntCellF` cells are closed from
`bin<Op>CellF_of` + `ScaffoldRows.field_hI<Op>` (division's `INT64_MIN / -1`
subcase is the named premise `DivOverflowCellF`, the footprint twin of
`eval_binary_row`'s `hDivOv`); `eqCellF_of`/`neCellF_of`
(`Vsa/Sim/rows/EvalEqNeRowFootprint.lean`, over `eqBlockC_bridge_footprint` ≫
`blockC_eq/ne_footprint`) supply the two `EqCellF` cells from the landed
`BinEqCell` residuals; and `footprint{,NA}.hBinary_of_base` closes `hBinary` on
exactly `eval_binary_row`'s remaining hypotheses.
`BinaryHeadFootprintSupplyCov` is DISCHARGED (`binaryHeadFootprintSupplyCov`)
over the parametric head `blockB_binary_footprint_gen` (`EvalBinSim.lean`; the
landed `blockB_binary_footprint` is its projection at the trivial left-child
fact), so `ScaffoldRows.field_hStr{Lt,Le,Gt,Ge}_of_clauses` need only
`StrCmpOwnedOperands` and the two closed clause recursions. The four
`BinStrCmpCellF` cells are CLOSED but for the shared operand residual: the
PRODUCT clause (footprint × payload coverage, `EvalIHFP noArenaFoot`) is declared
as the TSV line `FootprintCov` (`Vsa/Sim/rows/IHClause_FootprintCov.lean`,
generator kind `motive` — the `pred` column is the `EvalE` motive itself, since
the coverage half is indexed by the returned value), with the four leaves and the
six one-child arms wired from `IHClauseGeneric.footprintCov.<case>`
(payload-free results, plus the string literal's `evalStrPayloadIHF`) and the
same five steps open as `Footprint`. `Vsa/Sim/IHClauseGenericSupply.lean` states
the cell with its left child at the product clause (`BinStrCmpCellFP`), supplies
it from `StrCmpOperandsSupply` alone (`binStrCmpCellFP_cov`, over
`binRow_strcmpF_cov` and `binaryHeadFootprintSupplyCov`), and lowers it to the
plain `BinStrCmpCellF` through the closed product clause (`binStrCmpCellF_cov` at
`FootprintPayloadClause`); `binaryFootprintCells_of` and
`footprint{,NA}.hBinary_of_base` therefore take `StrCmpOperandsSupply` and
`FootprintPayloadClause` in place of the four cells. Left open in (b):
`hVar` at the `VarPinnedSim` shape (superseded: `Rows.evalVarIHF` over
`Rows.VarLeafResidF` lands the leaf; wire it in place of `footprint.hVar_of`),
and `hBinary`'s remaining `DivOverflowCellF` and equality pair; (c) declare `Call`/`ExecSeq` motives in the
`motives` column so `hCall` receives the callee's clause; (d) the allocating
family `allocFoot` over `MallocRun`/`HeapOwned.pushClosure`/`EnvNewContract`;
(e) DONE: `scripts/gen_footprint_row.py` + `scripts/footprint_rows.tsv` emit all
fifteen `*RowFootprint` modules (five family templates; `--check` in stage a3), and
`ExitFootprint.lean` carries the shared `intCellFoot`/`truthyArgCellFoot` whose
`_noArena` lemmas close the cell half of every `<arm>NodeFoot_noArena`. The per-op
`<op>CellFoot` stay stated beside their cells in the row files (definitionally the
shared predicate); folding them into aliases needs an edit of the landed row files.
`StrCmpOwnedOperands` (`Vsa/Sim/StrCmpCellClauses.lean`) is UNREACHABLE AS
STATED, and the verdict is stronger than "unproven": it quantifies an arbitrary
configuration constrained only by `TwoSubReturn`, which pins the operands solely
by `ValueRepr … (.str s)`, so the payload pointer may lie inside the stack,
inside the arena, or in the top eight bytes of the address space, and no shared
set satisfies `SharedGeom` for such a configuration. The derived-theorem
technique (keep the name, derive the content) was tried and does not fit. CLOSED
BY RETENTION instead: `blockB_binary_footprint_gen2` (`Vsa/Sim/EvalBinSim.lean`)
retains `BinaryOperandRetained` at the head's actual return, with the left
operand transported across the right child's footprint by
`ownedSlot_head_transport`; `binRow_strcmpF_owned`, `binStrCmpCell_of_owned` and
`ScaffoldRows.field_hStr{Lt,Le,Gt,Ge}_of_owned` consume it there. Every landed
name keeps its statement; the configuration-quantified definition survives as a
documented dead branch. The four string-comparison cells now take exactly a
shared-set choice (`OwnedIndex`, discharged at `stdShared` by `ownedIndex_std`),
the Layout premise `SharedTopSlackAll` (the pinned AST region and the arena end
far below `0x100000000`, so the `strcmp` word loop's eight-byte read stays in
RAM), and the two product-clause recursions.

The product clause is `FootprintCov` (`scripts/ih_clauses.tsv`, generated into
`rows/IHClause_FootprintCov.lean`), declared at the landed `EvalIHFP noArenaFoot`.
It needed a new clause KIND: `ValuePayloadCovered` is indexed by the RETURNED
VALUE, which an `EvalExtraM` cannot see, so `kind = motive` takes the `EvalE`
motive itself as the predicate. Ten steps are closed;
`binStrCmpCellF_cov`/`binStrCmpCellFP_cov` supply the four string cells, and
`hBinary`'s residual set shrank from seven to three.

After (a)–(d) the four string cells close from `StrCmpOwnedOperands` alone,
and `hEq`/`hNe` lose their `hVlSurv` conjunct the same way.

The two premises of `ScaffoldRows.field_hStr{Lt,Le,Gt,Ge}_of_owned` are supplied
by ONE recursion: the clause `FootprintPayloadOwned` (`scripts/ih_clauses.tsv`,
kind `motive`, guard `IHClauseGeneric.noAllocExpr e = true`, generated into
`rows/IHClause_FootprintPayloadOwned.lean`) at the landed `EvalIHFPO stdShared
noArenaFoot`; the right-operand premise `FootprintOwnedClause` is that clause
with the coverage conjunct dropped (`EvalIHFPO.forgetCov`). The three conjuncts
cannot be assembled from the landed `FootprintCov` and `OwnedPayload` clauses —
two `EvalIHWithM` recursions each quantify their own reached configuration — so
the steps are proved at the conjunction in `Vsa/Sim/IHClauseGenericProduct.lean`,
over the same rows the three landed families use: `EvalIHWithM.monoD` reads the
ownership and coverage halves off the child's OWN exit (`EvalExitD`'s
`ValueRepr`) for every payload-free result, `evalStrProductIHF` lands all three
conjuncts for the string literal at one run of `evalStrSimP_exact`, and
`IHClauseGenericProduct.hBinary` dispatches the binary arm with the four string
comparisons discharged by `binRow_strcmpF_owned` AT THE STEP'S OWN CHILD IHs
(the only place the left child's coverage and both operands' ownership exist
together). Thirteen of fifteen fields are wired; `hVar` (`VarProductStep`) and
`hBinary` (`DivOverflowCellF` + the two `BinEqCell`s) stay residual. The cells
close at `BinStrCmpCellNA` — the `BinDispatchRow` field restricted to operands
that do not allocate — because the guard is what makes `hAssign`/`hFn`/`hCall`
and `.add` vacuous; lifting it needs the `allocFoot` family of (d)/task 2.

OBSTRUCTION (the `SharedTopSlackAll` premise). `SharedTopSlackAll stdShared` is
FALSE, not merely unproven: `stdShared` is the envelope `k < 0x100000000`, which
contains the top eight bytes of the address space
(`not_sharedTopSlackAll_std`, `Vsa/Sim/IHClauseGenericProduct.lean`), so
`ScaffoldRows.field_hStr*_closed` (`Vsa/Sim/rows/StrCmpCellsOwnedClosed.lean`)
are vacuous as stated. And no index repairs it while
`AstRegionSpec.hi_ram` is `hi ≤ 0x100000000`: `OwnedIndex.ast` puts every byte of
every entry's AST region into the shared set, so the slack forces `hi + 7 ≤
0x100000000` on every AST region (`astRegionSlack_forced`), which the entry does
not carry. FIX: amend `AstRegionSpec.hi_ram` (`Vsa/Sim/InterpEntry.lean`) to
`hi + 8 ≤ 0x100000000` at its concrete Layout supplier. The landing pad is
already in place: the repaired index `stdSharedSlack` has `SharedTopSlackAll` as
a THEOREM (`sharedTopSlackAll_stdSlack`), `OwnedIndex stdSharedSlack` reduces to
the two named entry-layer premises `AstRegionSlack`/`ArenaSlack`
(`ownedIndex_stdSlack`), the clause is generated at it
(`FootprintPayloadOwnedSlack`), and `ScaffoldRows.field_hStr*_closedSlack` close
the four cells there with no false premise; the amendment discharges
`AstRegionSlack` outright.

#### The AST-region slack amendment

`AstRegionSpec.hi_ram` (`Vsa/Sim/InterpEntry.lean`) and its statement-side twin
`StmtRegionSpec.hi_ram` (`Vsa/Sim/ExecEntry.lean`) bounded the syntax region by
`hi ≤ 0x100000000`, the top of RAM. The `strcmp` word loop reads eight bytes at
a time and may read past a payload's final NUL, so that bound left the read
unjustified, and `IHClauseGenericProduct.astRegionSlack_forced` shows no choice
of shared index repairs it downstream: `OwnedIndex.ast` puts every syntax byte
into the shared set, so the set inherits exactly the region's bound. Both fields
are now `hi + 8 ≤ 0x100000000`. The two must move together, because a child
expression's region is derived from its statement's; that derivation
(`EntryGroundKit`) was the only site that broke.

The amendment strengthens an already-open assumption rather than adding a new
one: no proof constructs either field from concrete layout facts, every
occurrence propagates it from the entry bundles' assumption. What it does
discharge is `AstRegionSlack`, which is that field verbatim and is now the
theorem `astRegionSlack_holds` (`Vsa/Sim/IHClauseGenericProduct.lean`). The
field itself is true of the loaded image, whose syntax region sits in low RAM,
and it is discharged with the rest of `AstRegionSpec` when the entry-side region
assumptions are replaced by exact coverage (task 1). What it buys is that the
string-comparison closure is no longer vacuous: `SharedTopSlackAll stdShared` is
FALSE (`not_sharedTopSlackAll_std`, machine-checked, since `stdShared` is the
whole `k < 0x100000000` envelope and so contains the top eight bytes), and the
repaired index `stdSharedSlack` now derives its slack from these fields instead.

`ScaffoldRows.field_hStr*_closedSlack` and `strCmpCellsNA_slack`
(`Vsa/Sim/rows/StrCmpCellsOwnedClosed.lean`) therefore no longer carry
`AstRegionSlack`; `ownedIndex_stdSlack` is applied to `astRegionSlack_holds`.
The four cells at the repaired index rest on `ArenaSlack` (supplier: the
allocator ledger's concrete arena bounds, task 2), `VarProductStep`,
`DivOverflowCellF`, and the two `BinEqCell`s — each a named premise with a
supplier, none false. Slice-checked axiom-clean.

Two consumers needed weakening. `EvalChildArm.lean` and
`WhileCondDispatchClosed.lean` derive a child expression's region bound from
its statement's and wanted the old `hi ≤ 0x100000000`; they now compose
`Nat.le_add_right` with the strengthened field. The source audit found no other
direct use at the old bound. Other occurrences feed `omega` or rebuild the
amended twin spec.

#### Verification state of the amendment

| Step | State |
|---|---|
| Both `hi_ram` fields strengthened, both consumers weakened, `AstRegionSlack` discharged | Source complete |
| Integration build, all sources, `--resume` on the private cache | All 1,640 modules fingerprint-current, exit 0, including the executable and modules outside `Vsa`'s imports. The last run rebuilt exactly the three modules edited after the preceding build began (`rows/IHClause_FootprintPayloadOwnedSlack`, `rows/StrCmpCellsOwnedClosed`, `Vsa.lean`) and reused 1,637 |
| Generator checks (`gen_m4_term_row`, `gen_term_case_bundle`, `gen_ih_clause`, `gen_footprint_row` `--check`), `git diff --check` | PASS |
| `scripts/tests` | 257 run, 12 skipped, ONE error: `BoundaryInputTests` input fingerprint drift. Every other test passes |
| Boundary lock refresh | Refreshed for the amendment's four proof sources (ELF, fixture, case inventory and expectations all unchanged). It has since drifted again on five `EnvGetSpec` modules under concurrent edit; those are not part of the amendment, so the lock is left for whoever lands them. Boundary execution rerun pending |
| `check_all.sh` stage a4 (discipline) | FAIL, pre-existing: 56 findings across 27 files, none of them modified in the tree, so all present at HEAD. Recorded here per CLAUDE.md; the amendment adds none |
| `check_all.sh` stage b (forbidden tokens) | OK — 1,639 `.lean` files scanned, no `sorry`/`native_decide`/`bv_decide`/`axiom` |
| `check_all.sh` stage c (axioms) | OK — 1,086/1,086 theorems audited, axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`}. Stage a4's failure aborts the script, so b and c were run standalone against the same tree |
| `check_all.sh` stage a5 (IH clause status, informational) | 7 clauses, 105 residual fields. `FootprintPayloadOwnedSlack`: 12 WIRED, 3 MANUAL (`hStr`, `hVar`, `hBinary`) |

#### Residuals left open on the tower

The current selected check of `rows/StrCmpCellsOwnedClosed` passed: 950
modules, 889 reused and 61 rebuilt. Both requested declaration audits,
`astRegionSlack_holds` and `strCmpCellsNA_slack`, use only allowed axioms.
The driver checked selected source/object fingerprints before writing
`/private/tmp/vsa-slack-discharge/run-sky3uquq/receipt.json`.
`/private/tmp/vsa-closure-work/slack-slice-receipt.json` records that receipt,
the audit log, hashes, and counts. The external process is terminal; its exact
shell exit status was not directly observed. The all-source lookup integration
build remains live. This slice does not change the certified base-field count.

The amendment closes the string-comparison cells at
`ScaffoldRows.field_hStr*_closedSlack`. It closes nothing else. Still open:

- `VarProductStep` — `hVar` at the product clause. The current recursive
  lookup already retains its write set (`env_get_lookup_from_entry`);
  `varBridge_callee` drops it. The caller interfaces also need repair and
  store ownership must reach the clause entry. See the variable-lookup audit
  below; the older immediate-frame lookup is not the active supplier path.
- `DivOverflowCellF` — the footprint twin of `eval_binary_row`'s `hDivOv`, the
  `INT64_MIN / -1` subcase.
- The two `BinEqCell`s — `hEq`/`hNe`, which lose their `hVlSurv` conjunct by
  the same retention route the string cells took.
- Guard lifting: the cells close at `BinStrCmpCellNA`, operands that do not
  allocate, because the guard is what makes `hAssign`/`hFn`/`hCall` and `.add`
  vacuous. Lifting it needs the `allocFoot` family, step (d) over task 2's
  allocator ledger.

### 1. Finish recursive return and ownership contracts

- Initial resource gap: `Loaded` (`Vsa/Refinement.lean`) supplies program
  representation and `InterpRunReady`. Its existential `aLeft` is constrained
  only by `A.lo + aLeft ≤ A.hi`; no field connects it to the source execution's
  allocation cost or request ceiling. `InitialOwned` explicitly omits allocator
  metadata consistency and capacity. Applying `EvalAllocatorIH` requires
  `AInvAt` and `ResourceBudget A maxReq exts (cost + reserve)`.
  `InitialResourceGap.no_budget_supplier` now refutes budget inference that
  preserves every admitted `InitialOwned` witness. Its concrete ledger adds
  64 disjoint 49-byte payload extents in spare arena space. The payload
  geometry passes, but physical chunk costs exceed the arena before any
  future allocation. `no_allocator_state` rules out an allocator state with
  those extents, at any memory or credit count. `original_zero_credit` proves
  that the same snapshot also admits an affordable witness. Thus the initial
  adapter must select a suitable allocator-consistent ledger; the obstruction
  does not rule out such a selection or refute `RemainingWork`.
  `InitialOwned.allocator` now supplies the dlmalloc heap shape and capacity
  below `__heap_end` for every terminating derivation, and `arenaHeap` pins
  the arena to `[_end, __heap_end)`. `InitialResourceGap.small_arena_excluded`
  shows the pinned boundary excludes its 4 KiB arena; `heap_credit` gives the
  same oversized ledger room for a million maximal requests. The initial
  adapter still has to select an allocator-consistent ledger and derive
  `AInvAt` for the concrete malloc contract from `HeapAt`.
  `Vsa/While/Cost.lean` already proves `bigStep_budget_exists`, but that bound
  counts rounded requested bytes and does not establish available physical
  capacity. Reuse it when constructing request counts and ceilings; do not
  infer heap adequacy from cost finiteness.
- The clause generator already supports arbitrary evaluator motives through
  `kind=motive`, and all eight other motives through TSV overrides. A resource
  clause can quantify cost and request ceiling outside the machine-entry
  quantifiers and require the initial semantic closure bound. Its generated
  recursion still takes the old `TermCases` bundle. It does not discharge that
  bundle. The generated `AllocatorCases` recursion now consumes owned
  evaluator/statement suppliers directly, with all seven auxiliary contracts
  explicit and no old `TermCases` prerequisite. `EvalAllocatorSupply` and
  `ExecAllocatorSupply` package the
  resource witnesses; `EvalAllocatorAt.request_mono` and
  `ExecAllocatorAt.request_mono` supply request-ceiling weakening. All seven
  auxiliary relation contracts remain needed; the for-loop context contracts live in
  `TermSimAssembly`. Keep new allocator data below that module.
- Migrate `TermSimAssembly.mEvalE` and the execution, sequence, and call
  producers to coherent returns. Wire `ReturnRepr.bind` into binary recursion
  so results, store representation, and ownership use one selected map pair.
  The owned variable path now reaches a complete expression-statement return
  through `ExecRuntimeEntry`, `EvalChildArm.variable_runtime`, and
  `exec_variable_statement_owned`. Its initial adapter is
  `OwnedInitialExecFacts.execRuntimeEntry`; shared read geometry and the
  existing ground/stack/body obligations remain explicit.
  `EvalReturnIH`, `EvalIHWithM`, and `ExecIH` still accept ordinary entries.
  `RuntimeIH` provides owned recursive data contracts below the execution
  adapters. `AllocatorIH` extends them with allocator state, sufficient entry
  credit, a request ceiling, and retained reserve. Its variable and
  expression-statement suppliers are checked; the remaining cases and full
  recursor motives are open. `AllocatorResult.rebase_shared` composes shared
  domain inclusion and agreement across successive returns. Importing
  `EnvGetReflected.EvalRuntimeEntry` into the motive layer would cycle through
  `ArmEntryRetained`, `DeriveMetaTowers`, `TermCaseBundle`, and
  `TermSimAssembly`. Keep runtime return data at that lower layer too.
- Supply `PreEpilogueOwned` at each actual producer endpoint. Fresh closures
  must retain their allocation map through `blockD_v_return`.
  `EqualityReturnMapObstruction` and `CoherentReturnObstruction` establish
  why independent witnesses and entry-prefix bounds cannot supply this.
- `armTail_rec_frame` now exposes the actual child ghost frame's ABI relation
  to the parent. `armTail_rec_allocator` uses it to preserve the pinned global
  pointer; the existing helper remains a projection.
  Coherent operand rebasing also needs
  `ValueClosuresBounded st'.store.closures.size vl`.
  `(storeClosuresBounded_mutual.onEvalE hLeft hInitialBound).2` supplies it
  from `hInitialBound : StoreClosuresBounded st.store`; the allocator entry
  currently omits this semantic invariant. Closure `ValueOwned` is `True`
  and cannot supply the bound. `AllocatorResultAt.bind_return` now retains
  the left operand's transported ownership alongside the right results.
- Replace legacy `EvalGround.ast`, `ExecGround.ast`, and `SeqArrayReadSafe`
  region assumptions with exact `ExprReprWithin`/`StmtReprWithin` coverage,
  indexed arrays, and `AstReadGeometry`. Keep the fixed AST domain inside the
  evolving `SharedReadDomain`; preserve its bytes through actual effects.
- Propagate `StoreArraysReady`, source store invariants, body/stack bounds,
  and distinct addresses for the three native functions through entries.
- Replace `VarCallLinkage.payloadDisj` and its unpinned `LeafWiden` premise
  with facts about the actual returned value and memory.
  The active field is `VarLeafResid`'s `LeafReturnWiden`: its `pres` and
  `surv` quantify over every `EvalExit`, which omits byte presence and permits
  arena changes. `VarLeafResidF` retains that same premise. `evalVarSimQ`
  discards the prologue's `_hpresM`; its final post retains agreement outside
  the result slot but no presence witness. Retain presence and the exact
  footprint through the actual prologue, lookup, and copy, then derive store
  survival from the entry at that returned memory.
  `/private/tmp/vsa-closure-work/return-repair/` stages
  `evalReturn_of_exit_facts`, which consumes presence and store survival at
  one return. The existing `evalReturn_of_exit_id` keeps its statement and
  projects the new lemma. `check-return-facts.sh` passed (exit 0): 142 selected
  modules, 141 reused, one rebuilt in 38.808 seconds. Both declaration audits
  report only `propext`, `Classical.choice`, and `Quot.sound`. Receipt:
  `return-repair/backend/run-yv1xs_o6/receipt.json`. The patch remains staged;
  actual variable-return presence and store-survival suppliers, consumer
  wiring, and full integration remain open.
- Obstruction (string and equality cells): `blockB_binary_data` takes the left
  value's survival across the right child as `hVlSurv`, quantified over ALL
  memory pairs that agree outside the right child's frame, the arena, and the
  right result slot. For a string payload inside the arena that statement is
  false (the pair may differ on the payload), so `StrLeftSurvivesSupply`
  (`StrCmpCell.lean`) and the first conjunct of `BinEqCellResid` are
  supplyable only for payloads outside the arena. Cure: restate the survival at
  the right child's actual exit — the recursive motive already retains the
  store's survival (`EvalReturn`); extend it to the left temporary through
  `ValueOwned` and thread that fact into `TwoSubReturn` in place of `hVlSurv`.
  Evidence: the hypothesis shape at `Vsa/Sim/EvalBinSim.lean`
  (`blockB_binary_data`, `hVlSurv`).

Reuse the implemented separation rules, `StableUnder`, `ReprDelta`,
`OutputDelta`, `CertifiedSegment`, and `RecursiveStepGeom` throughout.

### 2. Complete allocation and resource suppliers

Malloc is not verified; `MallocContract` stays an assumed contract. It must
remain satisfiable by the binary's newlib dlmalloc, or the final theorem is
vacuous. Its current frame is not: `privFoot` is one state-independent
predicate, required inside the arena (`AllocLedger.priv_arena`) and off every
live payload in every invariant state (`privFoot_disjoint`), and `spec`,
`MallocSuccessRun`, and `HeapPublicFrame` leave every byte outside it and the
stack window unchanged. dlmalloc writes chunk headers at state-dependent arena
addresses. On the admitted control heap (top chunk `0x82000200`),
`malloc(32)` writes the new top header at `0x82000238`, while `malloc(64)`
from the same state returns `[0x82000210, 0x82000250)`, which contains it. No
single `privFoot` covers the first write and avoids the second payload.
Correction: frame the allocator by the current live extents — it may write
arena bytes outside every live extent plus fixed allocator globals outside the
arena — and drop `priv_arena`. Evidence: the `_malloc_r` top-split path in
`experiments/disasm.txt`; not yet machine-checked. 47 modules consume
`privFoot`.

Machine-checked since (`VsaIris`, branch `iris-heap`): the obstruction is
`VsaIris.no_fixed_privFoot`. The live-relative frame admits both calls at the
actual control memory (`VsaIris.VsaHeap.Control.live_relative_frame_admits_both`,
`malloc64_end`). `HeapAt` reads only the globals plus the arena outside the
live extents (`VsaIris.VsaHeap.BlockHeapAt.transport`). In the Iris route
the frame comes from ownership (`isHeap` owns exactly that set). The
remaining allocator assumption is the first-order runs
`VsaIris.MallocLocalRun`/`FreeLocalRun`/`MallocRoomRun`. The `MallocReturnAt`
fields that `EnvDefineAppendAllocatorPost.prepareCopy` consumes follow from
the Iris spec without `privFoot`
(`VsaIris.VsaHeap.mallocRoomCallerFacts_of_iris`).

OBSTRUCTION (machine-checked, `VsaIris.VsaHeap.vsa_reserve_fails_after_split`,
`split24_vsa_reserve_false`): `TopChunkRoom.disjoint` requires every live
extent to avoid the whole top chunk. dlmalloc's usable size is the chunk size
minus 8, so a returned block may cover the first word of the chunk after it.
After a top split for `malloc(24)` (a 32-byte chunk at `top`), the ledger
entry `(top + 16, 24)` ends at `top + 40`, inside the new top chunk at
`top + 32`. So `AllocationReserve` with a credit left is false, and
`MallocReturnAt.reserve` / `MallocSuccessRun`'s post cannot be met by the
binary whenever `n + 16 > physSize n` (for example, most name copies). The
corrected clause keeps only the top's header word off live extents:
`e.1 + e.2 ≤ top + 8 ∨ top + bytes ≤ e.1` (`VsaIris.VsaHeap.TopReserve`).
Affected: `AllocationReserve`, `TopChunkRoom`, and every supplier and consumer
of `reserve`.

Machine-checked run (`VsaIris`, branch `iris-heap`): `malloc`'s top-split path
for every request `n ≤ maxReq ≤ 487`, from the binary's reflected code, is
`VsaIris.MallocFast.mallocRoomRun_fast`. It covers a heap with no free chunk,
`binblocks = 0`, and the corrected top reserve. It is instantiated at an
approved boundary by `vsaDlMallocRoomImpl_boundary`, which takes the code bytes
from `FixedTextLoaded`/`ImageStaticsLoaded`.

MISSING SUPPLIER (`VsaIris.MallocFast.AllocBytesPresent`): the Iris model
requires the allocator's bytes to be present (`VsaOk.live`) to read VSA's
`HeapAt` from the owned image (`shape_iff_state`, `mallocCallerFacts_of_iris`).
`InterpRunPhysicalFacts` states byte presence for the stack (`stack_bytes`).
For the allocator globals and the arena it states presence only at the words
`HeapAt` reads, not at every byte. The loader supplies it; it is not derivable
from the current boundary. Affected: `vsaFoot_live` and every consumer
instantiating `hlive` at the boundary.

Machine-checked `free` (`VsaIris`, branch `iris-heap`): `_free_r`'s top-merge
path is `VsaIris.MallocFast.freeRoomRun_fast` / `vsaDlFreeRoomImpl_boundary`.
The heap half is `VsaIris.VsaHeap.FastAt.merge`. `realloc` has an Iris spec,
`VsaIris.reallocSpec`, whose success arm feeds `ReallocGrowResult`'s
fresh-block and copy clauses (`reallocBlock_of_fresh`, `reallocCopies_of_owned`).
Its machine run `ReallocLocalRun` remains a named hypothesis.

**The allocator layer.** Allocator facts are RUN-GLOBAL, not per entry. One
`AllocLedger` (`Vsa/Sim/AllocLedger.lean`) carries the `malloc`/`free`/`realloc`
runs (`MallocRun`, the new `FreeRun`, `ReallocInstance`), the `strlen`/`memcpy`
runs, the private footprint's arena residence, the arena/stack/HTIF geometry, the
footprint discipline `ainv_private`, the request and headroom bounds, and one new
named clause `ainv_perm` (the abstract live list is a set, needed because
`MallocContract.freeSpec` pops the head). The three landed per-entry ledgers are
now projections of it: `EnvNewLedger.of_alloc`, `EnvDefineUpdateLedger.of_alloc`,
`EnvDefineMissLedger.of_alloc`. `AInvAt` states the allocator invariant at a
memory with the pinned `gp`; `AllocLedger.ainv_stable` and `.ainvAt_transport`
replace every per-entry `ainv_stable` field.

- Ownership preservation through malloc, free, reuse, and realloc is ONE proof.
  `HeapOwned.ownedOff` (`Vsa/Sim/AllocOff.lean`) derives `OwnedOff` — every owned
  extent and shared byte is outside the stack region, the allocator-private set,
  and the fresh blocks — from the ledger, the caller's stack write footprint, and
  `MallocContract.privFoot_disjoint`; `HeapOwned.transport_off`/`.repr_off`
  consume it for ownership and representation. `HeapOwned.entryOff` is its
  entry-side (`fresh = []`) presentation, `EntryOff`, in the shape the landed
  lanes consume. Ledger movement is `HeapOwned.fresh` (a block enters
  unassigned), `HeapOwned.free` (an unassigned block leaves; `HeapArena.nodup`
  and `.freshErase` supply the list side), and the existing
  `Ledger.replace`/`.replaceArray` for realloc.
- The call adapters are `mallocReturn_of_parked` and `freeReturn_of_parked`: from
  a parked call carrying the caller's ownership to a named return that hands over
  the fresh block (`MallocBlock`), the advanced invariant, the memory frame, the
  footprint (`MallocReturnAt.allocFoot`, at the `allocFoot` family of
  `IHClauseGenericAlloc`), and the caller's `HeapOwned` and `StoreRepr` survived.
  A new allocating site adds no allocator fields and no separation derivation.
- Reseated so far: `envNewPushedRepr` (27 hand lines of separation → 7 on
  `HeapOwned.ownedOff`), and the `env_define` append and grow lanes (the four
  entry-side facts, derived twice by hand, → `HeapOwned.entryOff`). Remaining
  step is DONE. `Vsa/Sim/AllocRuns.lean` now holds the runs (`MallocRun`,
  `FreeRun`, `ReallocRun`/`ReallocInstance`, `StrlenRun`, `MemcpyRun`) and the
  `AllocLedger` record BELOW every per-entry ledger, which removes the import
  cycle that had forced each ledger to restate the allocator: `MallocRun` used
  to be declared in `rows/EnvNewContractSupply.lean` and the other three runs in
  `rows/EnvDefineMissLedger.lean`, above the record that bundles them. Each of
  the three per-entry ledgers now carries ONE `alloc : AllocLedger …` field, and
  36 consumer references across the four `env_define` lane files and
  `EnvNewContractSupply` project through it. The discipline gate falls from 68
  findings to 60 and R14 from 12 to 3.
  `ainv_stable` is gone too: each ledger now carries the arithmetic fact
  `stack_hi : esp.toNat ≤ SL.hi` (the entry's own `StackOK`) and DERIVES the
  footprint discipline as a theorem, `EnvNewLedger.ainv_stable` /
  `EnvDefineUpdateLedger.ainv_stable` / `EnvDefineUpdateOracles.ainv_stable`, so
  the five consumers are unchanged. `EnvDefineUpdateOracles.arena_htif` is
  derived the same way. R14 now reports 0 and the discipline gate is back to its
  56 inherited findings. `ainv_entry` stays a field and is not flagged: it
  mentions this entry's memory and extents, so it is the per-entry
  instantiation rather than a run-global fact.
- OPEN (unchanged, and outside this layer): relating `MallocContract.privFoot` to
  dlmalloc's actual indirect bin-link writes. That is the verified-allocator
  obligation behind `MallocContract` itself, not a fact any interpreter call site
  can supply; the proof consumes it only through `AllocLedger.ainv_private` and
  `MallocContract.privFoot_disjoint`, both named.
- `env_new` is supplied: `envNewContract_of_ledger`
  (`rows/EnvNewContractSupply.lean`) proves `EnvNewContract` from
  `EnvNewLedger` (one named ledger per entry: pinned `gp`, `s0` ghost
  presence, headroom and request bounds, `M.AInv` at entry and its stack-window
  stability, `MallocRun` — `MallocContract.spec` with the console-output and
  byte-presence clauses it omits —, the private footprint inside the arena,
  arena/HTIF/stack geometry, `StoreParents`, and `HeapOwned` with the stack
  region in the write footprint). The prologue is `envNewPrologueSeg` +
  `site_80002a10_env` (`envNewParked_of_entry`), the suffix
  `envNewSuccess_run`, the pushed store `storeRepr_allocFrame` after
  `StoreOwned.repr_transport` and the frame-map rebase `storeRepr_phif_mono`
  (`envNewPushedRepr`). `env_new_spec` stays unused (its `∀ p, EnvRegions … p`
  premise is false at `p = 0`).
- `HeapOwned.pushClosure` is DONE (`Vsa/Sim/AllocOff.lean`), over
  `StoreOwned.pushClosure`: old roles and bytes survive the build's memory through
  `OwnedOff`, the fresh record takes the `closure` role at the new index, captured
  environments stay allocated, and the pushed closure's AST is shared.
- `AllocBuildEntry.hOld` and `AllocBuildTailFacts.hOld` were UNINHABITABLE, and
  are FIXED. Each demanded `StoreRepr mpre …` for EVERY `mpre` agreeing with the
  post-malloc memory outside the stack window, the arena and the result slot.
  The arena was excluded from that agreement, so `mpre` could differ arbitrarily
  inside `[A.lo, A.hi)` — and `StoreRepr.frames` reads `FrameRepr` at `φf fa`,
  which `StoreRepr.frames_arena` places inside the arena. Perturbing one frame
  byte satisfied the hypothesis and refuted the conclusion, so anything built on
  these bundles was vacuous for a non-empty store. `hExprRepr` carried the same
  defect for the same reason: the `fn` AST node is arena-resident too.
  The cure is `BuildOff p sret` (`rows/AllocClosureInhab.lean`): the closure
  build's OWN write window, the fresh 16-byte record and the 24-byte result
  slot, which are the only bytes it stores to between the post-malloc and
  post-build memories. `hExprRepr`, `hOld` and `hCodeSurvive` now take agreement
  off that window, which is both weaker as a premise (so the fields are
  inhabitable) and true of the actual build; `hMpreFrame` states the same window,
  which is stronger and is what the reflected write log satisfies. The two
  consumers are rewired: the second composes through `A.contains p 16`, since a
  byte outside the arena is outside the fresh block. `allocClosureContract_of`
  and `storeRepr_pushClosure` audit at `propext`, `Classical.choice`,
  `Quot.sound`.
  Both repaired fields are now SUPPLIED, not merely inhabitable
  (`rows/ClosureBuildSupply.lean`): `closureBuildOld_of_owned` gives `hOld` and
  `closureBuildExpr_of_owned` gives `hExprRepr`, each from `HeapOwned.ownedOff`
  plus `buildOff_of_allocOff` (the result slot is a caller stack slot, so
  `AllocOff` refines `BuildOff`). The store side composes
  `StoreOwned.repr_transport` with `storeRepr_phic_mono`; the AST side is
  `exprRepr_agreeP` over the shared bytes. All three audit at `propext`,
  `Classical.choice`, `Quot.sound`, and `buildOff_of_allocOff` is axiom-free.
  REMAINING here: the bundle's ~28 machine-side fields (registers, spill
  readbacks, chain facts) are still open, and `closurePushed_of_mallocReturn`
  needs a bridge from the `fn` arm's own malloc plumbing (`mallocCallSpec`, the
  pruned `ExitP`) to `MallocReturnAt`, since that arm does not route through
  `mallocReturn_of_parked`.
- `EnvDefineContract` is proved by `envDefineContract_of_ledgers`
  (`rows/EnvDefineContractSupply.lean`) from the two ledgers per entry,
  `EnvDefineUpdateLedger` and `EnvDefineMissLedger`
  (`rows/EnvDefineMissLedger.lean`). The hit lane is
  `envDefineUpdateLane_ledger`. A miss on a non-empty frame runs
  `envDefineMissLane` to the cap dispatch, then `envDefineMissReady_run`
  (`rows/EnvDefineMissHead.lean`): the append arm is `envDefineAppendLane`
  (`rows/EnvDefineAppendLane.lean`: `strlen ≫ malloc ≫ memcpy ≫` the append
  store block `≫` epilogue over `StrlenRun`/`MallocRun`/`MemcpyRun`, the
  store side `frameRepr_append` + `storeDefineAdvance_of_append`); the grow
  arm is `envDefineGrowLane` (`rows/EnvDefineGrowLane.lean`: `cap' ≫
  realloc(names) ≫ realloc(values) ≫` rejoin over a `ReallocInstance`, one
  owned array per call through `reallocArray_run`, the ownership ledger
  re-seated by `Ledger/Immutable/Reserved.replaceArray` and
  `StoreOwned.replaceArrays`/`storeRepr_replaceArrays`
  (`RuntimeOwnershipArrays.lean`)) then the append lane. The empty frame is
  `envDefineEmptyLane` (`rows/EnvDefineEmptyLane.lean`): the CAP-INIT block
  as `#derive_case` segs run by `segRowKeepGhost`, then the append lane
  (`cap ≠ 0`) or the grow lane's `realloc(NULL,·)` entry
  (`EnvDefineGrowKind.init`, `cap = 0`); `envDefineCapInitGrow_unreachable`
  proves the `bnez` route's chain facts contradictory. Every call site is a
  `bridgeOfSegFull` parking (`rows/EnvDefineCallRuns.lean`), so
  `sailOutput` and byte presence reach `EnvDefineReturnState`;
  `bridgeMallocPre_at` states the malloc bridge at the actual memory.
  `EnvDefineMissLedger` names the external facts: `MallocRun`, the
  `ReallocInstance` (`ReallocOps` + `ReallocRun`), `StrlenRun`, `MemcpyRun`
  (each the landed spec plus its omitted `sailOutput`/presence clauses; the
  `memcpy` route hypothesis covers the byte route and the ≤ 64-byte word
  route), `ainv_private` (the allocator invariant reads only `gp` and its
  private footprint), the private footprint inside the arena, arena/stack
  disjointness, the queried name's arena residence, alignment and
  `StrRegions`, `copy_fit` (`8 * ((x.length + 1) / 8) ≤ 64`: identifiers of
  at most 71 bytes; the larger aligned `memcpy` route is outside every landed
  spec), and the request bounds. The ledger's ownership is runtime
  `HeapOwned` (`EnvDefineOwned`): the legacy `StoreHeapOwned` with `HeapArena`
  is uninhabitable for a fresh frame (`env_new` sets `cap = 0`, `names =
  vals = NULL`, and `FrameHeapOwned.arrays` demands `(NULL, 0) ∈ exts`).
- Physical accounting and arena capacity are `Vsa/Sim/AllocCapacity.lean`.
  `physSize n = 16 * ((n + 8 + 15) / 16)` is the chunk cost, header and
  16-byte alignment included, so `physSize_32 : physSize 32 = 48` is the plan's
  recorded figure as a checked theorem; `physTotal` sums it over a ledger.
  `extents_total_le` is the capacity theorem — pairwise-disjoint extents inside
  `[A.lo, A.hi)` have total size at most `A.hi - A.lo`, by strong induction on
  the ledger splitting each tail around its head extent into the part ending
  below it and the part starting above it. Nothing bounded the live set before
  this: `HeapArena` constrains each extent and their disjointness but never
  their total, so `MallocContract.nonNull_of_bounded` had no capacity content
  behind it. `ResourceBound` names the source-side obligation (the live
  ledger's physical cost leaves room for one more request at the static
  ceiling) and `arena_has_room` derives that the arena holds enough BYTES for the
  next bounded request. That is necessary, not sufficient: a byte total exhibits
  no contiguous PLACEMENT, so external fragmentation and the allocator's bin and
  coalescing behaviour stay behind `MallocContract`. `physSize` covers internal
  fragmentation only.
  `ResourceBudget A maxReq exts k` is the same statement indexed by how many
  further requests it still covers, which is what an induction along an
  execution needs. `.alloc` spends exactly one unit per request within the
  ceiling, whatever its size (`physSize_mono`); `.free` spends none and may
  recover some (`physTotal_erase_le`, over `physTotal_le_of_sublist`); `.mono`
  weakens the count; `.toBound` turns any budget with room to spare into the
  bound at that point.
  PARKED, NOT LANDED: the capacity precondition itself. `MallocContract.
  nonNull_of_bounded` currently quantifies over every machine state and every
  live list with no capacity condition anywhere in its statement, so read alone
  it says `malloc` never returns NULL for a bounded request however full the
  arena is. A future dlmalloc verification could not discharge that with
  dlmalloc's own heap invariant. It is inhabitable today only because `AInv` is
  a field of the same structure, so an inhabitant may define `AInv` to include
  "the arena has room" — which moves a CLIENT obligation inside the allocator's
  spec, hidden in an opaque predicate, and makes the contract unverifiable in
  isolation. The amendment adds `ArenaHasRoom A maxReq exts` (stated in
  `Vsa/Alloc.lean` beside `physSize`/`physTotal`) as an explicit precondition of
  `nonNull_of_bounded`, threaded through the eight call sites that prune OOM
  branches: as a ledger field on `EnvNewLedger` and `EnvDefineMissLedger`, and
  as a named premise on `prune_of_exit`, `concatOOM_prune`,
  `envDefMallocSuccessSaved_of_post`, `strdupMemcpy_prune_null` and
  `mallocReturn_of_parked`. The allocator side then reads "if there is room, it
  finds one", which is about dlmalloc alone; the client side is the caller's,
  discharged by `ResourceBudget`. UNVERIFIED: `Vsa/Alloc.lean` sits near the
  bottom of the graph, so the change invalidates ~1000 modules and 233 remain
  unbuilt. `Vsa.Alloc` and `Vsa.Sim.AllocCapacity` compile clean directly; that
  is no evidence of a proof error and no evidence of correctness for the rest.
  The diff is `capacity-precondition.patch` in the session scratchpad, checked
  to reverse-apply against the tree before it was parked.
  REMAINING: supply the COUNT. The carry lemmas reduce the obligation from
  "the live set is bounded at every point of every finite prefix" to "the source
  program makes at most `k` allocations", a static accounting over the
  interpreter's allocating constructs (environment records and their arrays,
  copied binding names, closure records, string payloads). That count then has
  to be connected to `Loaded` and the concrete arena bounds of the linker
  script.
  Discharging `nonNull_of_bounded` itself additionally needs the allocator's
  own placement argument, which is behind `MallocContract`.

### 3. Close sequence and for-loop recursion

- Close `hSeqSteps` for interpreter, closure-body, and block-body copies.
  Thread reached dispatch/resume carriers and whole-suffix invariants through
  empty, final, and continuing routes. Reuse `SeqSuffixGround` and the compiled
  closure return, normal-exit, and continuation lemmas. The block-body copy's
  child boundary demands `ExecSeqStackFrame .blockBody` (the parent's window
  `[esp+136, SL.hi)` outside the retslot and the arena); it follows from each
  child's `ExecExitD` by `blockBodyStackFrame_of_execExitD` with no geometry.
  Every sequence exit now also supplies `mem_extends` and `store_survives`
  (`ExecSeqExitI`), and every sequence entry `store_survives`
  (`ExecSeqEntryI`); the step suppliers take both from the child's `ExecExitD`.
- At closure child entry, derive `Exec_stmt` code, register presence
  (`x9`, `x20`, `x21`), header/array reads, and arena/stack geometry.
- Retain environment validity and machine geometry in `FEntryC`, `mForCond`,
  and `mExecStep`. `FlCondArmDispatchObstruction` refutes dispatch from the
  erased environment premise.
- Complete false-condition, body break/return, normal/continue, step, and
  next-iteration for-loop routes. Reuse the certified initializer and while
  suppliers after shared-contract integration.

### 4. Close the remaining terminating cases

| Family | Remaining work |
|---|---|
| Expressions | Variable lookup, assignment, constructor dispatch, equality/inequality, and the two string concatenation cells. `hDivOv` is supplied by `ScaffoldRows.field_hDivOv`. Equality needs coherent operand maps, allocated bounds, payload coverage, and native identity. The four string comparison cells are on the `StrCmpCell` layer down to `StrCmpOperandsSupply` and `StrLeftSurvivesSupply` (below). |
| Arguments | Empty/nonempty loop assembly and `EvalArgsStep`; preserve spill slots `sp+24` and `sp+16`. Discharge the Lean supplier before removing SMT premise `argsLoopBoundAcrossCall`. |
| Calls and functions | `hCall`, `hCallClosure`, `hFn`; parameter bindings, depth bounds, allocation, and result marshalling. Complete the existing `CallClosureRow`/`CallClosureSplice` stage providers. |
| Native/output | Print, println, successful assert, `fprintf`/`_vfprintf_r`, `__swbuf_r`, `_putc_r`, and enclosing fputc folds. Preserve stdout/errno/HTIF state and output suffixes; reuse existing flush/write frames. |
| Statements | `hExecRouteCases`. The null declaration and the initialised declaration wait only for the named `env_define` contract (and, for the latter, the fresh-closure coherence and the payload window); the value return waits for the payload window; the for-start waits only for the named `env_new` contract; the block waits for `env_new` and the sequence-exit epilogue seam (below). All are on the layer. |
| Entry/exit | `hInitStore`: extend the owned initial execution to the full loop entry. `hEpilogueSpill`: retain code, saved slots, and runtime state through the reached sequence exit. The universal exit widener is refuted in `/private/tmp/vsa-epilogue-audit/EpilogueSpillObstruction.lean`. |

#### The parametric statement-arm layer

`Vsa/Sim/EvalChildArm.lean` states the `exec_stmt` arm → `eval_expr` child
seam once, over a descriptor (`kind`, `armPC`, reflected prefix, `jal` PC and
immediate, sub-result-slot immediate, child field offset) and two certificate
records: `Cert` (chain well-formedness, register fold, end PC, `jal` site; all
`decide`/`rfl`) and `Sem s e` (tag, child field, region projection, budget,
bodies bound, prefix chain facts). Generic theorems: `dispatch` (statement
entry → child `EvalEntry` plus the parent `Carrier`), `exitKit_at_exit`
(parent ground/AST/code/truthiness header at the child's widened exit),
`normalExitPre_of_exit` (a normal completion parked at the arm's `li a0,0`),
and `normalExitTail` (`ExecNormalExitTail.lean`: the parametric
`li a0,0; j 0x8000409c; epilogue`).

Instances (`rows/EvalChildArm{While,If,Expr,Ret,VarInit,ForCond}.lean`) are one
`#derive_case` prefix, one descriptor, and the certificates each.
`execWhileCondDispatch_closed_of_generic` re-derives the hand-closed
`WhileCondDispatchClosed` statement from the while instance. Measured on the
resumed private build:

| Arm | Hand-closed dispatch | Instance | Compile |
|---|---|---|---|
| while condition | 397 lines (`WhileCondPrefix` + `WhileCondDispatchClosed`), 3.2 s | 161 lines (reuses the seg) | 4.5 s incl. confirmation |
| if condition | none | 131 lines | 1.3 s |
| expression statement | none | 118 lines | 4.5 s |
| value return | none | 135 lines | 1.7 s |
| initialised declaration | none | 139 lines | 1.5 s |
| for-loop condition (in-frame) | none | 225 lines | 4.5 s |

The dispatch is split into `armState_of_entry` (prologue and jump table,
needs `EntryCert`) and `dispatch_of_armState` (the arm prefix and `jal`). The
for-loop condition enters the second half from the real loop head:
`EvalChildArm.ArmState.ofForLoopReady` and `forCond_dispatchFromLoopHead`.

`Vsa/Sim/TruthyCopy.lean` states the condition copy and `value_truthy` seam
once over a descriptor `TruthyCopy` (copy segment, `jal value_truthy` PC and
immediate) and `TruthyCopy.Cert D T` (register fold, the write log as three
`sd`s, the copy's chain facts, the generated call site). Generic theorems:
`copyReady_of_exitKit`, `truthyReturn_of_copyReady`, `route_of_truthyReturn`
(any reflected route from the return; routes may reload `s0`, so they are
framed by `abiButS0` rather than the full ABI set), and
`normalExitPre_of_route`. `rows/TruthyCopyWhile.lean` confirms
`ExecWhileCondCopyReady` from the generic parked state;
`rows/TruthyCopyIf.lean` carries the if copy and its three routes with their
chain facts. The `jal value_truthy` sites are generated from
`scripts/truthy_copy_sites.tsv`.

The generic layer is 996 + 178 + 696 lines and compiles in about 15 s; the
if copy seam with its three routes is 283 lines at 1.9 s, the closed
`hSIfNone` supplier is 110 lines at 1.6 s, the closed `hSIfTrue`/`hSIfFalse`
supplier (`rows/Field_hSIfBranchClosed.lean`, one shared `ifBranch_resume`)
is 340 lines, and the closed `hFlCondFalse` supplier
(`rows/Field_hFlCondFalseClosed.lean`, with `rows/TruthyCopyFor.lean`) is
120 + 150 lines. Rules R10 and R11
(`scripts/discipline_rules.tsv`) fail any new file that reflects an exec-arm
prefix (expression or statement child) by hand.

`Vsa/Sim/StmtChildArm.lean` states the in-frame call of a child statement
once, over a descriptor (`armPC`, reflected prefix, `jal` PC and immediate,
child field offset) with `Cert` and `Sem s sc`: `dispatch_of_armState` lands
the child's `ExecEntry` with the parent `Carrier`, `exitKit_of_exit`
recovers the parent at the child's `ExecExitD`, and the exit heads after a
status route are `normalExitPre_of_routeHead` and `retExit_of_routeHead`.
The same file carries the pieces every in-frame continuation shares:
`FrameFacts` (the parent frame at any in-frame point, with `transport`,
`afterExit`, and `EvalChildArm.frameFacts_at_exit`), `ArmState` generalised
over its PC with `ArmState.of_routeHead`, `TruthyCopy.RouteReady` and
`route_of_gholds`/`route_of_ready` (a reflected route from any parked
return, keyed by `a0`), and `LoopFrame` (memory bookkeeping across an
iteration for the final rebase). The `ForCond` and `ExecStep` motives now
carry the condition's and step's eval IHs (`ForCondIH`, `ExecStepIH` in
`TermSimAssembly.lean`; rows `hFcSome_row`/`hEsSome_row`).

The for-loop instances (`rows/ForLoopArms.lean`, 356 lines: the body call
`forBodyArm`, the in-frame step arm `forStepArm`, and seven reflected
routes) and the closed `hFlBodyBreak`/`hFlBodyRet`/`hFlLoop` suppliers
(`rows/Field_hFlBodyClosed.lean`, 418 lines) compile in under 10 s; the
generic layer file is 1,114 lines and the ret-arm resume
(`rows/RetSlotCopy.lean`) is 477 lines. The step arm and body call are entered
from arm states reached by routes, never through the prologue.

#### The helper-call layer

`Vsa/Sim/HelperCall.lean` states the in-frame call of a runtime helper once,
over a descriptor `HelperCall` (head PC, reflected prefix, `jal` PC and
immediate, callee entry) and a certificate `Cert` (link alignment, `jal`
target, ABI-avoiding prefix, the generated `jal` site from
`scripts/helper_call_sites.tsv`). `parked_of_gholds` runs the prefix and the
`jal` from any state whose pinned registers hold a list `L`
(`bridgeOfSegOut`) and lands `Parked` at the callee entry; `parked_of_armState`
enters from an `ArmState` (the five frame registers), `parked_of_ready` from
a `RouteReady` (the six call registers `callL`; the link register is
rewritten). The helper's return is `Return`: a `RouteReady` at the link PC
plus the memory footprint. Each callee has one adapter from its contract:
`nullReturn_of_parked` (`HelperCallNull.lean`, over `value_null_spec_full`)
and `envDefineReturn_of_parked` (`HelperCallEnvDefine.lean`, over the named
`EnvDefineContract`). The continuation reuses the existing kit
(`RouteHead.toRouteReady`, `ArmState.frameFacts`,
`FrameFacts.afterStackHelper`/`.afterExit`, `normalExitPre_of_routeHead`),
`armState_of_entry_kind` reaches any arm from the statement entry by its tag,
and the two shared tails are `retSlotResume` (`rows/RetSlotCopy.lean`: the
retslot copy and the status-3 epilogue from any route-ready state; the value
return is re-proved through it) and `envDefineTail_run`
(`rows/EnvDefineCall.lean`: `ld a1,8(s0)`, the copy to `esp+16`, the
`env_define` call, the normal exit). The three-word copy's byte facts
(`copy3_total`/`copy3_frame`) and the payload premise (`PayloadOffWindow`, the
former `RetPayloadOffSlot`) are shared. Rule R12 fails a hand-reflected helper
prefix.

Measured on the private overlay (warm imports):

| Leaf | Legacy (hand) | On the layer | Result |
|---|---|---|---|
| `ret;` (`hSRetNull`) | `ExecRetNull` 760 lines (`maxHeartbeats 8000000`) + `ExecRetNullGlue` 516 lines + `ExecRetNullGeom`; seam still open | `rows/Field_hSRetNullClosed` 167 lines, 3.7 s | closed |
| `var x;` (`hSVarNull`) | `ExecVarNull` 272 lines; `value_null`, the copy and `env_define` inside one open glue | `rows/Field_hSVarNullClosed` 168 lines, 3 s | `EnvDefineContract` only |
| `var x = e;` resume (`hSVarInit`) | `ExecVarInitGeom` glue oracle (child IH, copy, `env_define`) | `rows/Field_hSVarInitClosed` 112 lines, 2.4 s | `EnvDefineContract` + `VarInitPayloadOff` (the child's coherent exit is the motive `mEvalE := EvalReturnIH TrivialOwned`, not a premise) |
| shared | — | `HelperCall` 572, `HelperCallNull` 89, `HelperCallEnvDefine` 188, `rows/EnvDefineCall` 341 lines; 4–7 s each | — |

| `for` start (`hSForStart`) | `hArm` oracle in `ForStartGeom` | `rows/Field_hSForStartClosed` 205 lines, 3.5 s: `ExecInitReady` at the `env_new` return | `EnvNewContract` only |
| block (`hSBlock`) | `hArm`/`hEpi` oracles in `BlockGeom` | `rows/BlockArmEnvNew` 470 lines, 4.3 s: `ExecSeqEntryI .blockBody` at the loop head (nonempty) or the epilogue entry (empty) with the retained parent frame `Rows.BlockArmFrame`; `blockEpilogue_run` = sequence exit ≫ `epilogueTail` | `EnvNewContract` |

The `env_define` contract (`EnvDefineEntryState` → `EnvDefineReturnState`,
`HelperCallEnvDefine.lean`) is the one seam shared by `hSVarNull`,
`hSVarInit`, `hAssign`, and `hCallClosure`. The `env_new` contract
(`EnvNewEntryState` → `EnvNewReturnState` with `EnvNewFresh`: the returned
address, the extended frame map, and the pushed store represented under it;
`HelperCallEnvNew.lean`) is the seam shared by `hSBlock`, `hSForStart`, and
the closure call. Both are consumed through one adapter each
(`envDefineReturn_of_parked`, `envNewReturn_of_parked`).

Suppliers. `env_define`: the closed exact lanes (`rows/EnvDefinePrologueSaved`,
`rows/EnvDefineScanFramed.envDefineScanFiniteFramed`,
`rows/EnvDefineUpdateExact.envDefineUpdateClosed_of_heap_owned`,
`rows/EnvDefineDispatchExact.envDefineMissCapDispatch`,
`rows/EnvDefineAppendClosed`, `rows/EnvDefineGrowExact.envDefineGrowClosed`,
`rows/EnvDefineEpilogue`) composed under `MallocContract`, `ReallocOps`, the
ownership ledger (`StoreHeapOwned`/`ValueHeapOwned`), `FrameUnique`, and the
allocator-private footprint inside the arena; the per-lane geometry records
(`EnvDefRegions`, `EnvDefineUpdateGeom`, `AppendStoreFactsGeom`,
`EnvDefineGrowClosedGeom`) are the remaining caller data. `env_new`:
`env_new_spec` with `MallocContract`, `storeRepr_allocFrame`
(`rows/CallClosureEnvNewMarshal`) for the pushed store under `pushFrameMap`,
and the freshness of the returned block against every represented frame,
which needs the ledger relating `StoreRepr` images to the allocator's extents
(task 2; no such lemma exists).

`rows/EnvDefineContractUpdate.lean` (12 s) composes the `env_define` update
path from the statement arms' entry state: `envDefineUpdateLaneKeep` runs a
framed prologue (one `#derive_case` of the 13 instructions), the scan hit, the
keep-set-framed exact update and epilogue (`rows/EnvDefineTailFramed.lean`:
`segRowKeepGhost` instantiated for `updateStoreSeg` and
`envDefineEpilogueSeg`), and `envDefineUpdateLane_full` closes
`EnvDefineReturnState` with no residual hypothesis. The three former
`EnvDefineReturnResiduals` are discharged: `sailOutput` rides the scan frame
(`EnvDefineScanEntryFrame.out`/`EnvDefineScanFrame.out`, fed across the
`strcmp` seam by `rows/EnvDefineScanCallOut.envDefineScanCallRead64Out` over
`bridgeOfSegFull`), the untouched `x3`/`x4`/`x23–x27` come off the scan
frame's ABI ghost through `KeepGhost`, and `a0` is the hit's `strcmp` result
kept by both rows. `envDefineMissLane` runs the miss to `EnvDefineMissReady`
at the cap dispatch. The oracle record `EnvDefineUpdateOracles` is derived by
`EnvDefineUpdateOracles.of_entry` from `EnvDefineMem` (fixed-text projections
`FixedTextLoaded.Env_defineLoaded`/`.StrcmpLoaded`, `slot_in_stack`,
`value_words`, `arena_image`; the last three are new `EnvDefineMem` fields
supplied at the call site by `FrameFacts.geom`, `copy3_total`, and
`ExecGround.eval_call.image.arena`) and the external ledger
`EnvDefineUpdateLedger` (gp pin, saved-register presence, allocator headroom,
allocator invariant at entry and its footprint stability, `HeapArena`, arena
RAM/HTIF bounds, `StoreHeapOwned`/`ValueHeapOwned`, `FrameUnique`, the scan
string regions `ScanNames`, array alignment, and `define_survives` — the
defined store's survival, whose supplier is `StoreOwned.repr_transport` after
`HeapOwned.defineHit`). Not covered: the empty-frame path (`count = 0`
branches to `0x80002bf4`, no landed lane) and the append/grow lanes from
`EnvDefineMissReady` (`rows/EnvDefineAppendClosed`,
`rows/EnvDefineGrowExact.envDefineGrowClosed` under `ReallocOps`).

The block's epilogue seam is closed (`blockEpilogue_run`,
`rows/BlockArmEnvNew.lean`). The indexed sequence boundary carries what the
shared epilogue needs: `ExecSeqStackFrame .blockBody` keeps the parent's
window `[esp+136, SL.hi)` outside the retslot and the arena, and
`ExecSeqExitI` carries presence (`mem_extends`) and store survival
(`store_survives`) like `ExecExitD`. The arm retains the parent frame as
`Rows.BlockArmFrame` (spill slots, ghost tie, memory relation to the entry);
`EpilogueReady`/`epilogueTail` (`ExecNormalExitTail.lean`) run the epilogue
from any status over `execBlockDQR`, whose carried memory predicate supplies
the `ret` value. `normalExitTail` is the `li a0,0; j` prefix of the same
tail.

Residuals restated in the dispatch/resume shape (`Rows.RetCaseGeom`,
`Rows.VarInitCaseGeom`, `Rows.IfNoneCaseGeom`): the dispatch half is supplied
by `retResid_of_resume`, `varInitResid_of_resume`, and the closed
`field_hSIfNone`; the named resume seams still open are:

- `Rows.RetResumeResid` (`hSRet`): closed on the layer
  (`retSlotResume`) down to `PayloadOffWindow`: the returned string or native
  payload lies outside the retslot window. `retResumeResid_of_payload`
  supplies the residual from that premise. The premise is not derivable at
  `EvalExitD`: `ValueRepr` fixes no payload location, and the ground bundle
  relates the arena to the stack only below `sp` (`ExecGround.arena_stack`)
  while the retslot lies above `sp`. Suppliers: the ownership layer's payload
  location (`ValueOwned`, payload in the arena or the AST region) plus an
  arena/retslot separation fact in `ExecGround`.
- `Rows.VarInitResumeResid` (`hSVarInit`): closed on the layer
  (`varInit_resume`, through `envDefineTail_run`) down to two named premises:
  `EnvDefineContract` and `VarInitPayloadOff` (the `PayloadOffWindow` class at
  the call buffer `[esp+16, esp+40)`). The child's coherence is no premise:
  the recursor motive is `mEvalE := EvalReturnIH TrivialOwned` (`EvalReturn.lean`,
  `TermSimAssembly.lean`), so every child returns `EvalReturn` — the widened
  exit plus ONE selected map pair (`EvalReturn.repr`) representing its value,
  its store, and the store's survival across the stack region — and the resume
  consumes that pair directly. Producers: the four pinned leaves through
  `pinnedLeafReturn` (`eval*SimR`); the variable leaf through
  `evalReturn_of_exit_id` from the identity-map result `evalVarSim` now exposes
  (`blockC_var`'s post) and the identity-map widener `LeafReturnWiden`
  (`VarLeafResid`); the integer/boolean/string arms (unary, logical, binary)
  through `EvalIH.coherent_of_bounded` (`binOpSem_closuresBounded`); the
  allocating arms land the coherent epilogue themselves through
  `armReturn_of_facts` (= `blockD_v_return` from `EpilogueEntryFacts` at the
  arm's selected pair): `fn` in `fnResid_of_pipeline` (`FnArmGeom.hArm` at the
  widened `φc'`, the fresh index mapped to the allocated block; the bundle's
  former exit-level `EvalRecWiden` conjunct is replaced by the epilogue-entry
  facts at that pair), `call` in `callReturn_of_stages` (`CallArmHandoff` now
  carries the facts at the pair its children selected). `AssignArmSpec` is
  restated at the coherent motive. Consumers that need only the widened exit
  project `EvalReturnIH.forget`. Remaining split below the eval motive: the
  statement/call motives (`ExecExit.retval`, `CallExitI`) still select the
  returned value's map independently of the store's; the call arm's
  `callToEpilogue` stage is where that pair is currently selected.
- `Rows.ForStartPrefixResid` (`hSForStart`) is supplied by `forStart_run`
  from `EnvNewContract`; `Rows.BlockCaseResid` (`hSBlock`) by
  `field_hSBlock` from `EnvNewContract`.
- `Rows.VarNullResid` (`hSVarNull`) and `Rows.RetNullResid` (`hSRetNull`)
  are restated as the leaf simulation Triple (statement entry to widened
  exit); `field_hSRetNull` is closed and `field_hSVarNull` takes
  `EnvDefineContract`.

Three obstructions recorded by the layer were resolved in place:

- `ForLoopReady`, `ExecInitReady`, and `InitSomeStage` now carry
  `parentSp : g x2 = some sp`, `ra_align : r.toNat % 4 = 0`, and
  `mem_extends : MemExtends m0 ment`; `Field_hInitNone`, `Field_hInitSome`,
  and `InitSomeReturnReady` supply them from the actual initializer run.
  `forCond_dispatchFromLoopHead` takes only the record.
- `ExecDispatchReady` keeps its strong memory frame. The if-branch residuals
  (`Rows.IfBranchCaseGeom`, `IfTrueCaseResid`/`IfFalseCaseResid`) instantiate
  its ghost memory as the reached memory and rebase the branch's `ExecExitD`
  to the entry memory with `Rows.execExitD_rebaseMem` (memory extension plus
  the arena/retslot-excepted frame). `exec_ifTrue_row`/`exec_ifFalse_row`
  are re-proved by composition. `Field_hSIfBranchClosed` closes both fields;
  the `auipc a4; addi a4` table base is read back from the reflected route
  by unfolding the register fold (`if_route_a4`), not by `rfl`.
- `SubExecReturnR`'s payload clause is conditioned on the returned value's
  actual string (`Vsa.Sim.ValuePayload v s`, `ReprCopy.lean`): it is vacuous
  for integer, boolean, and null payloads and names the string or native
  payload otherwise. `valueRepr_copy` and `valueRepr_copy_of_writeWindow`
  take the same guard; `ExecRet`, `ExecRetNull`, `EvalCallNative2`,
  `FrameCalc`, `EnvGetSpec6`, and `EvalVarBridge` consume it.

#### The string-comparison cell layer

`Vsa/Sim/StrCmpCell.lean` states the four string-comparison cells once over a
descriptor `StrCmpOp` (operator, result function, token, jump-table index and
slot, the landed slot predicate, the sign-tail seg, the `jal value_bool` /
`ld s3` / `j` PCs and immediates) and a certificate `StrCmpOp.Cert` (the token
and slot arithmetic, the sign tail's `ChainOK`/facts/end PC/readbacks, the
three generated box sites, the box wiring, the `binOpSem` closure, and the
proved `StrCmpOrderBridge`). Generic theorems:

- `strCmpKindEntry_of_twoSubReturn` — the shared operator dispatch
  (`evalBinopChain_run`) from the actual return of both children, reading both
  kind tags and payload pointers back from the represented operand boxes
  (`strOperandsStaged_of_twoSubReturn`, `BinaryReturnLoads`);
- `strCmpTailReady_of_kindEntry` (`Vsa/Sim/StrCmpSeam.lean`) — the
  operator-independent middle: the landed kind check `strKindCheck`, the seam
  seg `strSeamSeg` (`mv a1,a7; mv a0,s3; sd a2,0(sp)`) with the generated
  `site_80003b18_sc` through `bridgeOfSegOut`, `strcmp_full_spec`, and the
  landed rejoin `strRejoin` with the token read back through the write log; the
  exit `StrCmpTailReady` ties the `strcmp` word to the operand strings for every
  proved order bridge; `FixedRodataLoaded.maskPinned` supplies the word mask
  from the fixed image;
- `blockC_strcmp` — dispatch ≫ seam ≫ the operator's sign tail (a framed
  `segEval_sound` run over the certificate) ≫ the `jal value_bool` site ≫
  `boolBoxEpilogue`, landing the integer rows' `PreEpilogueVD` post;
- `evalStrCmpSim`, `binRow_strcmp`, `binStrCmpCell_of` — the recursive case
  from the arm entry (`blockB_binary_data ≫ blockC_strcmp ≫ blockD_v_rec`), from
  the node entry (`blockA_binaryArm_budgeted`), and the field supplier. The
  reached data `StrCmpResid` is supplied by `EvalEntry.binaryPostGeom` and
  `EvalEntry.binaryReturnImage`; the operand regions are the named residual.

Instances (`rows/StrCmpCellInstances.lean`) are one descriptor and one
certificate each; `ScaffoldRows.field_hStr{Lt,Le,Gt,Ge}_of` take the two shared
residuals. Measured on the private overlay (warm imports, `proof_slice`):

| Layer or cell | Lines | Compile |
|---|---|---|
| `StrCmpSeam` (op-independent middle) | 471 | 2.8 s |
| `StrCmpCell` (dispatch, block C, sim, row, supplier) | 868 | 4.6 s |
| `StrCmpSeamSites` (generated) | 52 | — |
| all four instances (`StrCmpCellInstances`) | 237 (≈55 per cell) | 4.7 s |
| one INTEGER comparison cell for comparison (`rows/EvalLtRow` + `EvalLtChain`, hand-rolled, `maxHeartbeats 8000000`) | 1,912 | — |

Every declaration of the three new files depends only on `propext`,
`Classical.choice`, and `Quot.sound`. The superseded hand scaffolding
(`StrArmFrontData`, `strArmFront`, `StrArmPrologue`, `StrArmMachineResid`,
`StrSeamSpan2`, `StrArmToStrcmp`, `StrArmStageSpan`) is removed; the residual
bundle field `TermGuards.strArmProlog` is replaced by `strCmpOperands` and
`strLeftSurvives`. Rule R13 (`scripts/discipline_rules.tsv`) fails any new file
that reflects the seam by hand.

The residual `StrCmpOperandsSupply` is true and derivable: string payloads live
in the arena (`value_str`, concatenation) or in the AST region (literals), both
inside RAM, 8-aligned, and disjoint from the `strcmp` code, the HTIF window,
and the callee's spill slot; the supplier is the ownership layer's payload
location (`ValueOwned`) plus `EvalGround`'s arena/stack geometry. The residual
`StrLeftSurvivesSupply` is the `hVlSurv` obstruction recorded in task 1.

Footprint-carrying exit (IH tower, Level 1; contract in the session scratchpad
`ih-tower/L1-interface.md`). `Vsa/Sim/ExitFootprint.lean` states `MemFootprint`
(named field `agree`), the standard windows (`stackWin`, `resultSlot`,
`arenaWin`, `word8`) and families (`FootFam`, `noArenaFoot`, `exitFoot`,
`binaryHeadFoot`), and the exit siblings `EvalExitF F` / `EvalIHF F` over
`EvalIHWithM`: an `EvalExtra` cannot see `sp` or the entry memory `m0`, and a
footprint is relative to `m0`, so the footprint contract is the `sp`/`m0`-aware
`EvalIHWithM`, with `EvalIHWith.toM`, `EvalIHF.forget`, `EvalIHF.mono`, and
`EvalIH.exitFoot` (the weak exit is the footprint `exitFoot`). Glue, all
statement-preserving: `armTail_rec_gen` (`EvalRecCommon`; `armTail_rec_with` is
its corollary), `armTail_rec_withM`/`armTail_rec_footprint`
(`ArmTailFootprint`), `blockD_v_rec_footprint`, `boolBoxEpilogue_footprint`,
`blockC_strcmp_footprint`, `blockC_lt_footprint`, and `blockB_binary_footprint`
(`EvalBinSim`; `blockB_binary_data` is its projection at `exitFoot`).
`BinaryHeadFootprintSupply` (`BinaryHeadFootprint.lean`) is discharged by
`binaryHeadFootprintSupply`. Pilots: `StrCmpCellFootprint.lean`
(`evalStrCmpSimF`, `binRow_strcmpF`, `binStrCmpCellF_of` at
`EvalIHF noArenaFoot`, from the two `StrCmpCell` residuals) and
`rows/EvalLtRowFootprint.lean` (`evalLtSimF`, `binRow_ltF`). A generated
`Footprint` clause must be an `EvalExtraM` motive (`EvalIHF F`), not an
`EvalExtra`; the recursion glue at a child call is `armTail_rec_gen`.
Integer cells (Level 1B, all eight, `ih-tower/L1B-int.md`): `blockC_<op>_footprint`
(`.add .sub .mul .div .mod .le .gt .ge`; each landed `blockC_<op>` is its
projection) with the cell footprint `<op>CellFoot` = the three dispatch-ladder
temporaries `sp-848/840/832` ∪ the result slot — identical for all nine integer
cells; the libgcc callees (`muldi3_post`, `divdi3_post`, `moddi3_post`) state
memory unchanged, so no scratch window enters. `.div`/`.mod` write through a
reflected `writeLog`: `evalBlocks_store_offsets_exact` +
`divDispatch_footprint`/`modDispatch_footprint` (`rows/EvalDivRow.lean`,
`rows/EvalModRow.lean`) refine the landed `[v2, v2+0x108)` window to the exact
`{0xf0, 0xf8, 0x100}` stores. `intBoxEpilogue_footprint` (`BinopTailGen`) is the
int twin of `boolBoxEpilogue_footprint`. `rows/Eval<Op>RowFootprint.lean`:
`eval<Op>SimF`, `binRow_<op>F` (residual at the entry config as
`BinIntCellResid`), `Bin<Op>CellF` + `bin<Op>CellF_of` discharged by the landed
`BinIntCell .<op>` suppliers (`ScaffoldRows.field_hI<Op>`); no new residual.
Duplication signal: eight per-op copies of one template — a generator + one
shared `intCellFoot` is the next step.

Clauses as metatheorems over footprints (IH tower, Level 2; contract in the
session scratchpad `ih-tower/L2-clauses.md`). `Vsa/Sim/IHClauseFootprintMeta.lean`
derives the two clause shapes once over `MemFootprint` (region preservation:
`agreeP_of_disjoint`/`region`/`EvalIHF.regionPreserved`; payload survival:
`cstring`/`valueRepr`/`sharedCString`/`valueOwned`/`EvalIHF.cstringSurvives`) and
`strLeftSurvives_of_footprint`, the left temporary's survival at the ACTUAL
memories from the right child's `noArenaFoot` footprint and the left payload's
whole-stack coverage. `Vsa/Sim/IHClauseGeneric.lean` holds the `Footprint`
clause's generic steps at the generator's field types (`EvalIHF noArenaFoot`
motive): `hInt`/`hStr`/`hBool`/`hNull` CLOSED (`leafExitF_of_pinned`: the pinned
leaf exit IS the `noArenaFoot` footprint); `hVar` from `Rows.VarLeafResidF` (`Rows.evalVarIHF`;
`VarPinnedSim` is uninhabitable as stated — see the variable-leaf paragraph); `hNeg`/`hNot`/the four logical cases from the
arms' footprint row contracts `NegRowF`/`NotRowF`/`LogicalShortRowF`/
`LogicalFallRowF` (Level 1B: the `F` siblings of the closed fields); `hBinary`
from `BinaryFootprintCells` (`.lt` supplied by `intCellF_lt` over pilot B, the
four string comparisons by `binStrCmpCellF_of`). OBSTRUCTION: at `noArenaFoot`
the clause is uninhabited — `hAssign`, `hFn`, `hCall`, and `hBinary` at `.add`
with a string operand write the arena (`StrAddLCellF`/`StrAddRCellF` are
unsatisfiable). The closable shape is the guarded motive
`noAllocExpr e = true → EvalIHF noArenaFoot …` (`IHClauseGeneric.footprintNA`,
all 15 steps; needs a generator `guard` column), or the allocating family
`allocFoot` (`Vsa/Sim/IHClauseGenericAlloc.lean`: `EvalIHAlloc priv`, named
premises `FnArmFootprint M`, `CallArmFootprint M`, `StrAddFootprint M` from
`MallocRun`, `HeapOwned.pushClosure`, `EnvNewContract`, `Reserved.outsideFresh`;
`value_str` does not allocate). String cells (`Vsa/Sim/StrCmpCellClauses.lean`):
`strCmpOperandsAt_of_owned` derives `StrCmpOperandsAt` from both returned values
being owned (`ValueOwned`, the `Owned` index of `EvalReturn`) under
`SharedGeom shared SL`; `StrCmpOperandsSupply` reduces to `StrCmpOwnedOperands`.
The alignment defect is fixed: `strcmp_full_spec_cond` (`StrcmpSpecCond.lean`)
derives the word-path alignment from the entry test (`align8_of_test`) and
`StrCmpRegion.wordRegion` is the alignment-free `StrcmpWSlack`. `StrLeftSurvivesSupply`
is replaced by the head premise `BinaryHeadFootprintSupplyCov` (Level 1B:
`blockB_binary_footprint` with the left child at the product clause `EvalIHFP`
and `strLeftSurvives_of_footprint` at `hvalL_R`); the exact `BinDispatchRow`
fields follow (`field_hStr{Lt,Le,Gt,Ge}_of_clauses`) from it, `StrCmpOwnedOperands`,
and the closed clause recursions `FootprintPayloadClause`/`FootprintClause`.

One-child arms and leaves at the footprint exit (L1B-una). Heads:
`blockB_unary_gen` (`EvalNegSim`; `blockB_unary_with`/`blockB_unary` are its
projections) and `blockB_logical_gen` (`EvalAndSim`; `blockB_logical` is its
projection) take the child at any retained fact `Q mcall`;
`blockB_unary_footprint` (`UnaryHeadFootprint.lean`, `unaryHeadFoot F`) and
`blockB_logical_footprint` (`LogicalHeadFootprint.lean`, `logicalHeadFoot F`,
`logShortNodeFoot`, `logFallNodeFoot`) are their `EvalIHF F` instances. Cells,
each with the landed theorem as projection: `blockC_neg_footprint`
(`negCellFoot`: `sp-848/840/832` + the box), `blockC_not_footprint`,
`blockC_andFalse_footprint`, `blockC_orTrue_footprint`, `blockC_logTail_footprint`
(all `truthyCellFoot`: the `value_truthy` argument copy `[sp-1024, sp-1000)` + the
box), `blockC_andTrue_footprint Fr`/`blockC_orFalse_footprint Fr`
(`logFallCellFoot Fr 848`/`944`, the RIGHT child through `armTail_rec_footprint`).
Rows `rows/Eval{Neg,Not,OrTrue,AndFalse,AndTrue,OrFalse}RowFootprint.lean` land
`eval<Arm>SimF`, `<arm>RowF`, and the unconditional `EvalIHF noArenaFoot` supplier
`eval<Arm>IHF`. Leaves (`LeafFootprint.lean`): `pinnedLeafExitF` turns the pinned
exit (`LeafMemPin.agree` = `noArenaFoot`) into `EvalExitF noArenaFoot`; `evalIntIHF`
is unconditional, `evalNullIHF`/`evalBoolIHF`/`evalStrIHF` take the named
`EvalEntry → Eval*Entry` bridges (`NullEntryBridge`/`BoolEntryBridge`, supplied
inline by `rows/TermRouting.lean`'s `eval_null_row`/`eval_bool_row`; `StrEntryBridge`
open on `EvalEntryStrAstRegion`). Variable leaf
(`rows/EvalVarRowFootprint.lean`): LANDED at `EvalIHF noArenaFoot` — the SAME
family as the literal leaves — down to ONE named conjunct. `evalVarSimQ`
(`EvalVarSim.lean`; `evalVarSim` is its `Q := True` projection) threads any fact
`Q` about the `env_get` call-return memory through `blockC_var_gen` (`blockC_var`
is ITS projection), which retains the arm's own write window `[sret, sret+24)`.
`Rows.VarLeafResidF` is `Rows.VarLeafResid` with the `env_get_found` oracle's post
strengthened by `Rows.VarPostCallPin SL sp m0 mpc`
(`∀ a ∉ [SL.lo, sp), mpc[a]? = m0[a]?` — no arena drift); `varLeafResid_of_F`
projects it back onto the landed residual, and `evalVarIHF`/`eval_var_rowF` land
the leaf at the generator's `hVar` field type. The conjunct has a proved supplier:
`env_get`'s write set is `[out, out+24) ∪ [sp0-64, sp0)` with
`out = (sp-1088)+0xf0`, `sp0 = sp-1088`, both inside `[SL.lo, sp)` under the entry's
`StackOK SL sp 2176`; `EnvGetSpec10.env_get_found_framed` already carries that frame
and `envGetFramedPost_pin` (`rows/EvalVarBridgeCallee.lean`) converts it to
`VarPostCallPin`, with `varCallLinkage_calleeF` composing it through an assumed
memory-transparent repack. The active recursive path already carries the same
write windows in `env_get_lookup_from_entry`; retain them through
`varBridge_callee` instead of changing `VarCallLinkage.finalMemFrame`.
The existing arena-carved post cannot recover this discarded information.
Consequently
`IHClauseGeneric.VarPinnedSim` is NOT provable as stated (from `EvalVarEntry` alone
nothing constrains the arena on the call-return memory); the `Footprint` clause's
`hVar` step should take `Rows.VarLeafResidF` (→ `Rows.evalVarIHF`) instead of
`Rows.VarLeafResid` + `VarPinnedSim`.

#### Variable-lookup supplier audit

The retained caller path must also preserve the prefix and final copy facts.
Reuse `OutputAliasLoaded.traceSeg015` in `OutputAliasRun/Part00.lean`
(`0x80003434` through `0x8000343c`) with `bridgeOfSegFull` and
`site_80003440_var`. Consume `LookupReturnResult` directly at that call's
return. For the final copy and restore, reuse `evalValueReturnTailSeg`
(`EvalValueReturnTail.lean`) through `segEval_selected_framed`, preceded by
the successful branch at `0x80003444`. The existing prefix and tail wrappers
discard the needed frame; `blockC_var_gen` retains `Q` only at the call-return
memory, so `Q` alone cannot supply final byte presence. Retain the actual
write log and apply `copy3_memExtends` and `ValueOwned.copy_total` there.
These are source-checked reuse points, not a compiled caller bridge.

The active supplier is `env_get_lookup_from_entry`
(`Vsa/Sim/EnvGetRecursive.lean`), which covers parent-chain lookup. Its return
retains the prologue spill agreement and `EnvGetValuePost.mem` retains the
output-buffer agreement. `varBridge_callee` obtains both and discards them
while constructing `VarPostCall`. Retaining their composition at that actual
return supplies the footprint; strengthening `finalMemFrame` is unnecessary.
The immediate-hit adapter in `rows/EvalVarBridgeCallee.lean` still assumes its
repackaging and cannot supply the general parent-chain path.

The source audit identified additional contract gaps:

- `VarRowResid` (`rows/EvalVarBridge.lean`) quantifies over arbitrary ghosts
  and arbitrary `ment/v8/v9/v18`. Choosing the everywhere-`none` ghost makes
  the demanded `VarCallLinkage.g8` read `none = some 0`. Its replacement must
  receive both the actual `EvalEntry` and actual `ArmEntryK` witnesses.
  Consumers: `varLeafResid_of_rowResid`, `eval_var_row_closed`.
- `VarCallLinkage.payloadDisj`, `EnvGetHitGeom.payDisj`,
  `HitTailSt.payDisj`, `FoundSt.pvVals`, `EnvGetCallerGeom.pvVals`, and
  `FrameStackDisj.valstr`
  quantify over unrelated strings. The downstream copy theorem already
  requires `ValuePayload v s`, but these callers discard that guard.
  The unguarded proposition forces every payload word above the destination,
  excluding integer zero and valid lower-addressed strings. Use the actual
  value's `ValuePayload` guard throughout the lookup/copy chain; ownership
  supplies its equivalent `ValuePayloadCovered` predicate. The spill-frame
  transport needs the same guard on each binding's actual value.
- `VarCallLinkage.finalFrame` quantifies over arbitrary `EnvGetValuePost`
  witnesses. That post omits the full saved-register frame. Retain it through
  the recursive execution and scan seams. `finalMinstret` is already supplied
  by `EnvGetValuePost.good.minstret`; it needs no additional retention.
  The post already restores `x19`–`x21`; with the linkage's ghost pins,
  only `x3`, `x4`, and `x22`–`x27` remain. `gen_fn.py --fn env_get
  --entry 0x80002c10 --cfg-only` identifies 51 instructions, twelve blocks,
  two loop back-edges, and one `strcmp` call. Its generated block draft is
  `/private/tmp/vsa-closure-work/FnEnvGet.lean`; use those segments with
  `segRowFramed`/`segRowKeepGhost` to retain the eight registers. The generic
  generator does not supply a fold for these loops. The draft is uncompiled.
  `EnvGetSegments.lean` extracts its seventeen generated branch/block variants
  and pin lists, then applies `segEval_selected_framed` through one wrapper.
  `check-env-get-segments.sh` passed (exit 0): all seventeen variants avoid
  `x3`, `x4`, and `x22`–`x27`. Its 783-module dependency slice reused every
  module. The three segment declarations have only allowed axioms.
  `EnvGetSegments.receipt.json` records source/object/log hashes and the
  dependency receipt; `extract-env-get-segments.py` and
  `EnvGetSegments.sources.json` retain extraction provenance. This verifies
  the blocks and frame wrapper; call and loop composition remain pending.
  `EnvGetCallFrame.lean` now stages the call seam: `call_framed` uses
  `bridgeOfSegFull` and `site_80002c68_eg2` to retain the generated argument
  block's computed result, output, and eight-register frame at the actual
  `strcmp` entry. It takes the block's `ChainFacts`; it does not yet assemble
  the string inputs or compose the comparison and recursive loop.
  `check-env-get-call.sh` passed (exit 0), with all 788 dependency modules
  reused. `call_framed` reports only the allowed axioms. Frozen sources and
  logs are in `/private/tmp/vsa-closure-work/call-source/`; provenance and
  object hashes are in `EnvGetCallFrame.receipt.json`. The comparison and
  recursive loop remain outside that check.
  `EnvGetCompareFrame.lean` stages the subsequent `strcmp` composition.
  A generated `strcmp_post.destruct` exposes the legacy post by name;
  `CallResult.compare` combines its full saved-register frame with the call's
  retained frame at the same endpoint. `EnvGetReflected.scan_compare` in
  `EnvGetScanCompare.lean` stages the caller: from `ScanSt`, it selects the binding pointer, obtains
  reflected load facts through `wordLoadFacts_of_read64`, and assembles
  `StrcmpEntryCond` at the actual call endpoint. `check-env-get-scan.sh` failed in `EnvGetCompareFrame`: its unbounded
  register proposition lacked a `Decidable` instance, and the destructurer
  was generated under the wrong namespace. Its 824-module dependency slice
  passed (819 reused, five rebuilt); both dependency audits use only allowed
  axioms. The segment and call modules also compiled. The comparison caller
  was not reached. `scan-repair-source/` contains a fresh seven-module snapshot
  with a bounded register proof and the destructurer invoked at root scope.
  `check-env-get-scan-repair.sh` used the verified dependency slice;
  it checks comparison, scan transport, branching, and semantic decision.
  The corrected 824-module slice passed with all modules reused.
  `EnvGetCompareFrame` then compiled, and all six declaration audits use
  only allowed axioms. `EnvGetCompareFrame.receipt.json` records the source,
  object, log, and dependency receipt. `EnvGetScanCompare` and
  `EnvGetScanState` also compiled, with four further allowed-axiom audits.
  `EnvGetScanState.receipt.json` records both modules. The result branch also
  passed its two audits (`EnvGetScanBranch.receipt.json`). The check then failed
  in `CompareResult.value`: its local zero-sign equivalence left one integer
  sign case open. `scan-advance-source/` replaces the ambiguous `split` with
  an explicit sign case split. The decision theorem remains unverified.
  No loop frame is yet proved.
  `EnvGetScanState.lean` adds the shared `ScanSt.transport` adapter;
  `CompareResult.scan` uses it at the actual `0x80002c6c` return.
  `scan_compare_state` keeps the semantic comparison and scan carrier at
  one endpoint. `EnvGetScanBranch.lean` instantiates the generated result
  branch for both polarities through `segEval_selected_framed`, retaining
  the scan carrier, output, and caller frame. The obsolete queued
  `check-env-get-scan-branch.sh` was retired before starting because it used
  the same failed comparison source. Its snapshot remains preserved in
  `scan-branch-source/`. The corrected check covers these additions.
  `EnvGetScanDecision.lean` stages the semantic composition:
  `CompareResult.value` exposes the actual `a0` with its name-equality
  equivalence; `scan_decision` composes the slot load, call, and branch while
  retaining the scan, output, and caller frame at one endpoint. Its source
  and dependency-manifest hashes are in `EnvGetScanDecision.sources.json`.
  This draft is included in the corrected scan check and has not been compiled.
  `scan-advance-source/` stages the generated `c54` back-edge for both
  count-branch polarities. `ScanSt.reseat` centralises carrier construction;
  `ScanSt.transport` projects it for unchanged indices. `scan_advance` selects
  the incremented index and cursor from the same reflected result, retains
  the caller frame, and relates the exit branch to semantic exhaustion.
  The snapshot records source and reused-object hashes. Its four unchanged
  prefix modules are verified; `check-env-get-scan-advance.sh` is queued to
  check the factored carrier, branch, repaired semantic decision, and back-edge.
  The factored scan carrier, result branch, and repaired semantic decision
  have now compiled with eight allowed-axiom audits. Their source/object/log
  hashes are in `EnvGetScanDecision.receipt.json`. The back-edge then failed:
  `sign_extend` needed the `LeanRV64DExecutable.Functions` namespace, and
  `gholds_lookup` needed its register-list argument before the held-register
  proof. `scan-loop-source/` fixes those references and reuses the seven
  verified prefix modules. The corrected back-edge compiled and passed its
  three allowed-axiom audits. `EnvGetScanAdvance.receipt.json` records source,
  object, log, and dependencies.
  `EnvGetScanLoop.lean` stages the fold through
  `loopFromBody`: named scan points retain the first-match invariant, a typed
  position distinguishes head/hit/exhaustion, and the loop invariant retains
  the actual caller frame and output. Its measure is remaining names at the
  generated `c60` load head and zero at either exit. Source and dependency
  hashes are in `EnvGetScanLoop.sources.json`. The frozen nine-module snapshot
  is in `scan-loop-source/`. `check-env-get-scan-loop.sh` is queued to include
  the missing `DeriveLoop` dependency, check the corrected back-edge, and then
  check this fold. Its complete 825-module slice passed (29 reused from the
  loop cache and 796 from the scan cache). The back-edge passed; compilation
  reached the loop fold, which failed only at `scanLoopMeasure_head`: its
  simplifier left `if True` unreduced. `scan-loop-repair-source/` rewrites the
  known guard before simplifying the index read. `check-env-get-scan-loop-repair.sh`
  reuses all eight verified dependency modules and checks only the corrected
  loop module. The corrected fold passed (exit 0), with six declaration audits
  using only allowed axioms. `EnvGetScanLoop.receipt.json` records its frozen
  source, object, log, dependencies, and the compiler-overlap incident below.
  A post-check hash audit matched all 825 selected dependency objects.
  This closes the inner scan loop with its actual caller frame and output.
  The whole lookup still needs prologue, parent traversal, hit copy, and return
  composition. `EnvGetScanOutcome.lean` stages the semantic exit adapter through
  `lookup_first_match` and `lookup_scan_miss`. `EnvGetParentBranch.lean` stages
  the generated parent load/branch with its actual loaded pointer and frame.
  The parent check failed before elaboration because its unnecessary
  `EnvGetSpec5` import was absent from the selected backend. The frozen
  `parent-outcome-repair-source/` snapshot imports `Code.Env_get` directly and
  reuses the verified loop objects. Both adapters await compilation.
  `EnvGetScanStart.lean` stages the generated `c48` pointer/index
  initialisation and its composition with the loop. `ScanStartReady` names
  the reached positive-count state, header read, and ownership-derived scan
  names. `scan_frame` retains the source lookup outcome and actual caller
  frame through initialisation and scanning. The frozen `scan-entry-source/`
  snapshot contains all three candidates and nine verified dependency objects.
  `check-env-get-scan-entry.sh` checks the independent parent branch, then the
  outcome and initialisation consumers. Its shell syntax check passed.
  `wait-for-lookup-checks.py` is now live with process visibility, waiting for
  the two existing build drivers, their wrappers, and project compiler children
  before entering the compiler lock. It aborts on permission failure and never
  reclaims a lock while waiting. Log: `scan-entry-wait.log`; session `44848`.
  No additional compiler has started. The positive-count
  branch must still supply `ScanStartReady` from the reached outer-loop state.
  `EnvGetCountHead.lean` now stages that generated `c40` load/test, retaining
  the loaded count, branch destination, unchanged memory, output, and saved
  registers. It reuses `wordLds4`, `bytesVal_lw_wordLds4`, and the `blez_guard`
  lemmas in `HelperCall`. Its signed count bound comes from
  `FrameOwned.length_signed`. The frozen `count-head-source/` snapshot awaits
  the additional `HelperCall` dependency and compilation. The dependency
  preview selected 906 modules, with 880 reusable and 26 pending rebuilds in
  the then-current full backend (`count-head-dependencies-plan.log`).
  `check-env-get-count-head.sh` will re-evaluate that plan, check dependencies,
  and compile the count test. `wait-for-count-check.py` is live with process
  visibility behind the builds and scan waiter; session `26008`, log
  `count-head-wait.log`. The script's syntax check passed. The count result
  has an uncompiled composition in `EnvGetFrameScan.lean`. `FrameState` retains
  frame data before scan registers are initialised; its `after_count` and
  `scan_ready` adapters supply the positive branch from the actual count result.
  `frame_scan` composes the generated count test, initialisation, and inner
  scan. `FrameOutcome.miss` unifies empty and exhausted frames at the parent
  entry, while `.hit` retains the source lookup's first binding. Source and
  pending-dependency hashes are in `EnvGetFrameScan.sources.json`. This candidate
  awaits the queued count/scan checks before compilation. Prologue and parent
  traversal must still supply `FrameState` from actual owned-store entries.
  `EnvGetOwnedFrameState.lean` stages that data supplier. `owned_frame_state`
  combines reached `FrameRegisters` with `StoreOwned`, `StoreRepr`,
  `StoreArraysReady`, `Ledger`, query ownership, and comparison geometry. It
  selects the actual names pointer and reuses the verified `scanNames` and
  `length_signed` suppliers. `FrameRegisters.after_parent` preserves the
  reached pins through `ParentResult`. Hashes and pending dependencies are in
  `EnvGetOwnedFrameState.sources.json`. These adapters are uncompiled; prologue
  execution and ownership transport to reached memory remain obligations.
  The queued `VarRowResidObstruction.lean` now also contains
  `EnvGetValuePost.with_gp` and `envGetPost_gp_not_determined`: replacing `x3`
  preserves `GoodState` by `insert_nonpinned` and every recorded post field,
  so an inhabited post cannot determine `gp`. These candidates still await
  compilation; they concern arbitrary post witnesses, not the actual run.
- `VarProductStep` needs the source store's ownership at entry. `EvalEntry`
  currently carries `StoreRepr`, not `StoreOwned`. The suppliers are
  `StoreOwned.frames`, `FrameOwned.values`, `ValueOwned.covered`, and
  `ValueOwned.copy_total`; their ownership input remains unsupplied.
- `ScanNames.nameRegW` and `bindRegW` in both `EnvGetSpec3` and
  `EnvSetScanCore` require `StrcmpWRegion` unconditionally. Together with
  `nameCStr`, the query clause forces `name.toNat % 8 = 0`, including calls
  that take the byte path. `VarRowResidObstruction.lean` now stages
  `ScanNames.name_aligned` and `scanNames_unaligned_false`; compilation is
  pending. Use the existing `StrcmpWSlack` and `strcmp_full_spec_cond`, which
  derives word alignment from the executed branch test. Keep names-array
  slot alignment separate from string-pointer alignment.

The applied alignment repair was checked in
`/private/tmp/vsa-closure-work/alignment-repair/`, over the payload-repair
snapshot. Seven files replace the two scan carriers' word regions and migrate
five comparison call sites in lookup, update, and definition scans to
`StrcmpEntryCond`. `EnvSetScan.scanMiss_to_chain` remains a direct carrier
conversion. `check-scan-alignment.sh` passed (exit 0): 860 selected modules,
833 reused and 27 rebuilt; summed module build time 2,232.6 seconds. Its four
declaration audits (`env_get_lookup_from_entry`, `scanMiss_to_chain`,
`envDefineScanCompare`, `envDefineScanCompareFramed`) report only `propext`,
`Classical.choice`, and `Quot.sound`. Receipt, source fingerprints, object
hashes, and audit log are in
`/private/tmp/vsa-closure-work/alignment-repair/backend/run-s2icy46k/`.
The module log `alignment-repair/backend/logs/Vsa_Sim_EnvGetSpec6.log` also
audits `env_get_hit_tail` and `env_get_found_spec` with the same allowed axioms.
This checks the selected dependency closure. The combined check below
also covers the marshalling consumer. Full integration remains pending.

The combined payload/alignment patch and twelve-file hash manifest are
`combined-lookup-repair.patch` and `combined-lookup-repair.sources.json`
under `/private/tmp/vsa-closure-work/`. `git apply --check` passed against
the recorded root hashes. `check-combined-lookup.sh` passed (exit 0): 862 selected modules,
860 reused, two rebuilt, and thirteen declaration audits with only allowed
axioms. This includes `EnvGetMarshal` and the lookup, update, and definition
consumers. Receipt: `combined-lookup-backend/run-6m_zxu3l/receipt.json`.
The twelve-file patch is now applied to the worktree. Full integration remains
pending in `check-lookup-integration.sh`, queued under the compiler lock.

Candidate counterexamples and recursive footprint adapters are in
`/private/tmp/vsa-closure-work/`. `check.sh` passed its 364-module dependency
slice (all reused) and the lookup audit, then failed in the obstruction file:
`St` resolved to the wrong declaration, and `insert_nonpinned` lacked its
explicit register argument. The footprint file was not reached.
`footprint-repair-source/` fixes both elaboration errors and preserves source
hashes and the dependency receipt. `check-footprint-repair.sh` checks the
footprint file first and then the obstruction file, retaining both results.
The footprint file passed all six declaration audits with allowed axioms;
`EnvGetFootprint.receipt.json` records source, object, log, and dependencies.
The obstruction file still failed because `SpecSt` is not an exported alias;
`obstruction-repair-source/` now uses the exact semantic type `Vsa.While.St`.
Its corrected check passed (exit 0), with seven allowed-axiom audits against
the preserved pre-amendment contracts. `VarRowResidObstruction.receipt.json`
records the source, object, log, and dependency snapshot. The word-alignment
obstruction concerns the old carrier, already amended in the worktree.
The arbitrary-post `gp` obstruction confirms that `VarCallLinkage.finalFrame`
must be replaced in the actual-run path by retained execution frame facts.
The variable residual remains open.
`EnvGetFootprint.lean` also contains `EnvGetEntryPost` and
`env_get_lookup_from_entry_framed`: a named adapter retaining the prologue
frame and value post at one return configuration. Its `.footprint` composes
the spill and result windows. The queued check covers these additions.
Its `.callerFootprint` composes that result with the arm-entry frame.
`ArmEntryK.destruct.memFrame` already supplies agreement outside the caller's
stack, including arena bytes; no stronger arm-memory premise is needed.
The caller still supplies `SL.lo + 1152 ≤ sp.toNat` from the actual eval entry.
`/private/tmp/vsa-closure-work/bridge-repair/` stages the consumer change over
the alignment snapshot. `varBridge_calleeQ` retains an extra memory fact at
the actual lookup return; the old `varBridge_callee` projects it.
`varBridgeF` composes the existing argument prefix and arm-entry frame with
the recursive lookup footprint. It retains `VarCallLinkage`'s outstanding
register-frame premise. This draft awaits the helper and alignment checks;
it has not been compiled or counted as a closed residual.

`EnvGetOwnedSource.lean` in that directory adds the candidate
`StoreOwned.lookupSource`: `get?_terminal_first`, `FirstMatch.index`, and
`frame_slot_valueRepr` select the same source slot that `FrameOwned.values`
owns. `EnvGetOwnedSource.copy_owned` transports its payload through the actual
total copy via `ValueOwned.copy_total`. This covers terminal frames reached
through parents. It still requires the entry's store ownership and the
copy's shared-byte agreement. `check-owned.sh` stopped before elaborating the candidate because its
dependency slice omitted the imported `RuntimeOwnershipInitial` module.
`check-owned-repair.sh` passed the complete 236-module dependency slice
(all reused), then failed because `Frame` resolved to the machine-frame
predicate. `owned-frame-repair-source/` qualifies all semantic frame types
as `Vsa.While.Frame` and records source hashes and the verified dependency
receipt. `check-owned-frame-repair.sh` passed (exit 0), with all eight
candidate audits using only allowed axioms. `EnvGetOwnedSource.receipt.json`
records the source, object, log, and dependency receipt. Entry ownership
remains unsupplied; this does not close the variable residual.
The same candidate now derives the guarded copy premise through
`ValueOwned.payload_disjoint`, and the source slot's arena bounds through
`ArrayOwned.slot_in_arena` and `FrameOwned.value_slot_in_arena`. The latter
uses the actual values-pointer read and the live allocation ledger. These
facts supply payload and source-slot geometry; they do not supply the
entry's ownership, array readiness, or scan-register facts.
`EnvGetOwnedSource.access` additionally selects all three copied words from
`StoreArraysReady`, derives source alignment, and uses
`FrameOwned.length_signed` to bound the semantic scan index by `2^31`.
These additions passed with the ownership candidate above.

`EnvGetOwnedNames.lean` stages the next consumer against the alignment repair.
`SharedCString.strcmpSlack` derives comparison geometry from the actual string
and `SharedGeom`; `FrameOwned.bindingString` selects the owned key through its
actual names-array read. `FrameOwned.scanNames` combines those facts with
`Ledger`, names-array alignment, query ownership, and mask bytes to construct
the repaired `ScanNames` carrier for every occupied slot. Its array bounds use
`ArrayOwned.slot_in_arena`. `owned-names-source/` now qualifies the semantic
frame types and imports `SharedGeometry` directly. The staged
`shared-geometry-repair/repair.patch` moves the unchanged `SharedGeom` record
out of `StrCmpCellClauses`, avoiding a dependency on the recursive cell proofs
from the entry/lookup geometry layer. `git apply --check` passed; the patch
is now applied to the worktree. `check-owned-names.sh` is queued against that frozen source
snapshot, reusing ownership and alignment dependencies before checking both
ownership modules. Its 238-module dependency slice passed (22 reused from
the ownership cache, 215 from alignment, one new geometry module built).
The ownership helper then recompiled with eight allowed-axiom audits. The name
carrier failed on its missing `EnvGetSpec9` import for `cstr_unique_eg9`.
`owned-names-repair-source/` adds that import and reuses the verified ownership
object; `check-owned-names-repair.sh` is queued to check the additional dependency
and name carrier. The corrected check passed (exit 0): 242 selected modules,
238 reused from the output cache and four from the alignment backend, with
no rebuilds. All four name-carrier declaration audits use only allowed axioms.
`EnvGetOwnedNames.receipt.json` records source, object, log, dependencies, and
the compiler-overlap incident. A post-check hash audit matched all 242 selected
dependency objects. The existing cell consumer still requires integration.
Entry ownership, shared geometry, and the fixed mask supplier remain obligations.

The payload-guard repair is staged in
`/private/tmp/vsa-closure-work/payload-repair/repair.patch`, with source hashes
in `sources.json`. It guards all six affected contracts by the actual
binding's `ValuePayload` and preserves that guard at the copy and spill
transport consumers. Its isolated source snapshot needs eleven modules
rebuilt in a 364-module dependency closure; 353 match the private backend.
The unstarted `check-payload.sh` was retired after the combined repair check
passed both of its imports and all ten declaration audits. The combined patch
supersedes this isolated candidate and is now applied to the worktree.

### 5. Close divergence, errors, and final assembly

- Construct `DivWork`: loop-head representation, `Loaded` entry drive,
  iteration/re-entry, and the 29-arm approximate recursive dispatch.
- Construct `ErrWork`: loaded-program-indexed leaves, recursive error
  propagation, formatted error/exit tail, and top-level abrupt completion.
  Complete auxiliary `hCallTooMany` with its indexed child and signed count
  bridge; reuse the bad-closure impossibility proof.
- Construct all 63 `TermResidualsBase` fields, then `RemainingWork`, then the
  final refinement theorem. Remove the 30 remaining discipline findings and the
  12 per-entry allocator ledger fields R14 reports (supplied by `of_alloc`).

### Verification hygiene: an overlay is not the backend

`rows/ClosureBuildSupply.lean` was committed (`fef1ec8`) and imported from
`Vsa.lean`, but only ever compiled into a private `proof_slice` overlay. Its
object was therefore absent from the shared backend, and the next full
`build_private` run failed at `Vsa.lean` with a missing-object error for it.
The module itself is fine; the mistake was treating "verified in my overlay" as
"verified", when the two differ exactly on whether the rest of the tree can see
the result.

The rule this implies: a slice verifies a change, but only a full build verifies
that the change is INTEGRATED. Any commit that adds a module and imports it from
a root has to be followed by a build that compiles the root against the shared
backend, or it breaks the next person's gate rather than your own. Overlays stay
the right tool for iteration — the shared backend must not be written by hand —
but the integration build is not optional, and the gap between them is a commit
that looks green and is not.

## Validation and automation still to finish

Repository artifact cleanup removed twelve tracked `.olean` files under
`experiments/`; their Lean sources remain. The active build imports none of
those experiment modules. `difftest.sh` and `smt_check.py` compile their
experiment dependencies into private directories. Backups and hashes are in
`/private/tmp/vsa-closure-work/tracked-olean-backup/removed.json`.
The source-tree scan, including ignored files and excluding dependency/Lake
directories, now finds no `.olean` or `.ilean` files. `.gitignore` excludes
both extensions. `houdini_summary_remote.sh` now requires a fingerprint-current
private backend and recompiles both experiment modules into a fresh temporary
directory before emission. Its five refusal tests and shell syntax check pass;
no remote campaign was run.
Project compiler objects also remain under `.lake/build`; they were not
removed during the live integration build.
This cleanup does not close the remaining hygiene or validation gates.

- Export typed Lean authority for each query, field, span, stop, semantic
  relation, effect, dependency, and source hash. Replace duplicated Python
  allowlists for migrated contracts. Reject missing, duplicate, stale, or
  mismatched certificates.
- Connect certified effects to SMT rewriting and post-dependent slicing.
  Parse terms before rewriting. Retain preserved inputs as dependencies;
  memory framing alone does not establish noninterference between executions.
- Project summaries onto live registers, memory, output, status, store, and
  environment. Match recursive summaries to the typed induction hypotheses.
- Finish contract-driven Houdini mining, shared summaries, incremental Z3,
  and exact-fingerprint result caching. Require convergence before validation;
  report query sizes, symbols, solve times, and unsat cores.
- For each helper family, connect a finite SMT relation, independent Python
  oracle, and Lean semantic bridge. Cover environment operations, equality,
  truthiness, strings, allocation, boxing, and output.
- Compare actual ELF/Sail traces, SMT reflection, and the independent oracle.
  Check claimed register, memory-footprint, and output effects, including
  composition. Cover zero/one/many iterations, every status, argument and
  parameter boundaries, shadowing/update/miss, parent chains, and output
  prefixes/suffixes. Kill branch, boundary, effect, and semantic mutants.
- Complete the coverage ledger for 63 base fields, `DivWork`, `ErrWork`, and
  `hCallTooMany`. Record execution, SMT, oracle, mutation, Lean-bridge, and
  full-residual evidence independently, with explicit finite/composite/
  Lean-only/nonfinite capabilities.
- Rerun the full supplier search at exact inherited types and the complete
  library census. Preserve all four initial-boundary regression cases.
- Allocator-layer checks: rule R14 (`scripts/discipline_rules.tsv`) fires on any
  hand-rolled allocator ledger field outside `AllocLedger`; the census must find
  `EnvNewLedger.of_alloc`, `EnvDefineUpdateLedger.of_alloc` and
  `EnvDefineMissLedger.of_alloc` at their inherited types, and `FreeRun` and
  `AllocLedger.ainv_perm` are new named premises needing SMT/oracle evidence
  rows in the coverage ledger.
- Induction-hypothesis clauses (`scripts/ih_clauses.tsv`, `gen_ih_clause.py`,
  `Vsa/Sim/IHClauseSupport.lean`): a clause is an `EvalExtraM` (or an
  `EvalExtra` embedded through `EvalIHWith.toM`) recursed as the `EvalIHWithM`
  motive beside the old motive (product recursor); each recursor case is a
  named `Residuals` field (`Vsa.Sim.IHClause.<Name>.Residuals.<case>`).
  `Trivial` is closed (`closed`, axiom-clean). `Footprint` is
  `footExtra noArenaFoot` (`Vsa/Sim/ExitFootprint.lean`): its 15 `EvalE`
  fields (children `EvalIHF noArenaFoot` → parent `EvalIHF noArenaFoot`) are
  the generic `footprint` hooks. Motives
  of the other eight relations default to `True`, so a clause step at `hCall`
  receives nothing from the callee: a footprint-style clause needs the `Call`
  and `ExecSeq` motives declared in the `motives` column before its `hCall`
  field is inhabited.
- Clause-field automation (`scripts/ih_clause_status.py`, `ih_clause_fuzz.py`,
  `ih_clause_ledger.py`, `proof_slice --structure`; TOOLING.md "Validation"):
  per field WIRED/HOOK/MANUAL/STALE, hook-lemma probes, census re-check of the
  wirings, drafted candidates checked in Lean, refutation verdicts, and an
  evidence ledger. Measured on the overlay: `Trivial` 15/15 WIRED (census
  FOUND); `Footprint` (`footExtra noArenaFoot`) 15/15 HOOK,
  `Vsa.Sim.IHClauseGeneric.footprint.*` missing, every drafted candidate
  (hook lemma, `trivialStep_of_old`, `withMaps_of_old` bare/`.toM`) rejected
  by Lean (FAILED ×15). Unwired steps are outside the statement_fuzz/smt_check
  fragment (motive conclusions); the bounded engines report ENCODE-GAP. No
  trace query targets a clause step (execution evidence 0/30).

The current checkpoint's four actual Sail boundary regressions passed against
matching source hashes. The three unsafe snapshots are excluded by the current
boundary; the admitted stable control matches source output and termination.
`/private/tmp/vsa-closure-work/integration-boundary-receipt.json` records the
summary hash, all 1,254 verified input hashes, eight artifact hashes, and all
four case results. The checkpoint then passed all 260 Python tests in 80.211
seconds without skips and the four generator checks. It stopped at stage a4
with 56 discipline findings; later stages did not run. Exact log hash and
findings: `integration-checkpoint-receipt.json` in the same directory.
The separate declaration audit passed all 1,086 entries with allowed axioms.
`integration-axiom-receipt.json` retains its script/log hashes and the preceding
backend manifest. These checkpoint results predate the lookup integration batch.

The worktree now contains the twelve lookup amendments,
`Vsa/Sim/SharedGeometry.lean` with the unchanged geometry record, and
`Vsa/Sim/RuntimeOwnershipLookup.lean` with the verified ownership suppliers.
`Vsa.lean` imports the ownership module. `lookup-integration-sources.json`
records the sixteen affected source hashes. `check-lookup-integration.sh` has
completed the all-source private compilation (exit 0). Backend verification
failed (exit 2): `Vsa.Sim.rows.IHClause_FootprintPayloadOwnedSlack`,
`Vsa.Sim.rows.StrCmpCellsOwnedClosed`, and `Vsa` were stale.
`lookup-integration-receipt.json` retains the exit codes and log hashes.
This does not establish a fingerprint-current integration checkpoint.
The queued scan-entry check also finished: `EnvGetScanOutcome` passed;
`EnvGetParentBranch` and `EnvGetScanStart` failed on unreduced bitvector
numerals in address arithmetic. Failed declarations are not accepted proof
evidence. `EnvGetScanEntry.receipt.json` records the aggregate failure.
The count-head check passed (exit 0), recorded in
`EnvGetCountHead.receipt.json`. Frame-scan and owned-frame-state composition
remain uncompiled private drafts.
Fresh boundary validation and the complete supplier search remain required.
The final residual construction remains open.

## Completion gates

Run against one frozen source snapshot. Partial checks do not close these gates.

| Gate | Required evidence |
|---|---|
| A — Emission | Fresh, complete emission of all 72 finite queries with typed capabilities and provenance. |
| B — SMT | Every executable semantic projection decided; no unknown, timeout, malformed query, inconsistent premise, or assumed validity. |
| C — Certificates | Query, field, span, theorem, footprint, and provenance mutations all rejected. |
| D — Fuzzing | Every claimed executable leaf covered; clean findings and all required mutants killed. |
| E — Semantic seams | Exact Lean theorem coverage for every non-SMT seam. |
| F — Termination | Compiled, hypothesis-free constructor for all 63 base fields. |
| G — Divergence/errors | Compiled `DivWork` and `ErrWork` for the concrete layout and loaded-program index. |
| H — Assembly | `remainingWork_closed : RemainingWork interpRunLayout`. |
| I — Refinement | `endToEnd_refinement remainingWork_closed` compiles; axioms limited to `propext`, `Classical.choice`, and `Quot.sound`. |
| J — Hygiene | Discipline and generator checks pass; unchanged ELF; no admitted proofs, extra axioms, `native_decide`, `bv_decide`, raised limits, stale objects, or repository-generated `.olean` files. |

## Execution rules

Follow [CLAUDE.md](../../CLAUDE.md) for proof discipline and
[TOOLING.md](../../TOOLING.md) for commands. Run the abstraction inventory
before proof work. Record each new contract gap beside its task, with the
affected declaration, missing supplier, obstruction evidence, and import
dependents. Update this plan in place; keep build transcripts in receipts.

Use one compiler or full solver/fuzzer campaign at a time. Preserve the private
cache `/private/tmp/vsa-full-build.sQd0gM` and resume it with `--resume`.
Check changed dependencies before consumers; run the all-source gate at a
completed residual or shared-interface checkpoint. Record fingerprints,
built/reused counts, exit status, log, and timing. Documentation edits need
no Lean rebuild.

The latest parent-branch launch exposed a lock-wrapper failure: `kill -0`
reported live owners as unavailable, and the wrapper reclaimed their locks.
Process inspection confirmed overlapping external, integration, name-carrier,
and loop checks. Preserve those running jobs and their snapshots. Launch no
further compiler until they finish. Future lock acquisition must have process
visibility; permission failure is not evidence that an owner is dead.
`lock-visibility-receipt.json` records the confirming probe: sandboxed
`kill -0 58547` failed with `operation not permitted`; the same probe with
process visibility succeeded. Launch future compiler wrappers with
`require_escalated`; do not modify the running wrapper or reclaim its lock.
