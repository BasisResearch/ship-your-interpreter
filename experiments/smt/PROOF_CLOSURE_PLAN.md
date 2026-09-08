# Proof closure plan

Prove `remainingWork_closed : RemainingWork interpRunLayout`, then discharge
the `RemainingWork` hypothesis of `endToEnd_refinement`.

## Status

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

Open steps on the tower, in order: (a) generator `guard` column so the
footprint clause is declared at `noAllocExpr e = true → EvalIHF noArenaFoot`
(`IHClauseGeneric.footprintNA`, all 15 steps proved) and wire the four closed
leaf steps as `exact:`; (b) supply the row-contract premises of the generic
steps from the landed `*RowFootprint` suppliers (`NegRowF`, `NotRowF`,
`LogicalShortRowF`, `LogicalFallRowF`, the remaining `IntCellF`/`EqCellF` cells
from `binRow_<op>F`, `VarPinnedSim` after the `env_get` write-set conjunct)
and `BinaryHeadFootprintSupplyCov`; (c) declare `Call`/`ExecSeq` motives in the
`motives` column so `hCall` receives the callee's clause; (d) the allocating
family `allocFoot` over `MallocRun`/`HeapOwned.pushClosure`/`EnvNewContract`;
(e) a generator for the `*RowFootprint` modules and one shared `intCellFoot`
(the eight integer modules and six one-child modules are one template each).
After (a)–(d) the four string cells close from `StrCmpOwnedOperands` alone,
and `hEq`/`hNe` lose their `hVlSurv` conjunct the same way.

### 1. Finish recursive return and ownership contracts

- Migrate `TermSimAssembly.mEvalE` and the execution, sequence, and call
  producers to coherent returns. Wire `ReturnRepr.bind` into binary recursion
  so results, store representation, and ownership use one selected map pair.
- Supply `PreEpilogueOwned` at each actual producer endpoint. Fresh closures
  must retain their allocation map through `blockD_v_return`.
  `EqualityReturnMapObstruction` and `CoherentReturnObstruction` establish
  why independent witnesses and entry-prefix bounds cannot supply this.
- Replace legacy `EvalGround.ast`, `ExecGround.ast`, and `SeqArrayReadSafe`
  region assumptions with exact `ExprReprWithin`/`StmtReprWithin` coverage,
  indexed arrays, and `AstReadGeometry`. Keep the fixed AST domain inside the
  evolving `SharedReadDomain`; preserve its bytes through actual effects.
- Propagate `StoreArraysReady`, source store invariants, body/stack bounds,
  and distinct addresses for the three native functions through entries.
- Replace `VarCallLinkage.payloadDisj` and its unpinned `LeafWiden` premise
  with facts about the actual returned value and memory.
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
  mechanical step: replace the allocator fields of the three per-entry ledgers by
  one `AllocLedger` field and rewire their consumers. Discipline rule R14 fires
  on exactly those 12 declarations.
  That step needs ONE preparatory move, because the callee runs are currently
  declared above the ledger that would carry them: `MallocEntry`/`MallocExit`/
  `MallocRun` live in `rows/EnvNewContractSupply.lean` and `ReallocRun`/
  `ReallocInstance`/`StrlenRun`/`MemcpyRun` in `rows/EnvDefineMissLedger.lean`,
  while `AllocLedger` (which bundles all of them) imports the latter — so a
  per-entry ledger cannot take an `AllocLedger` field without a cycle. Cure:
  move the run declarations and the `AllocLedger` record down into one new
  module below both (`Vsa/Sim/AllocRuns.lean`), leave the call adapters in
  `AllocLedger.lean`, then give each per-entry ledger a single `alloc` field.
  The consumer rewiring is 36 references (26 `LM.<field>` across the four
  `env_define` lane files, 10 `L.<field>` in `EnvNewContractSupply`), all
  mechanical renames to `.alloc.<field>`.
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
- `AllocBuildEntry.hOld` and `AllocBuildTailFacts.hOld` demand store survival
  under arbitrary arena changes. Their replacement supplier is
  `closurePushed_of_mallocReturn` (`AllocLedger.lean`), which derives the old
  store at the extended closure map from the ACTUAL `malloc` frame plus the build's
  own writes, then lands `storeRepr_pushClosure`. Remaining: rewire
  `rows/FnArmSeams.lean` to take `ClosurePushed` instead of the two `hOld` fields.
  The drafts in `/private/tmp/vsa-indexed-child/` remain unchecked and are
  superseded by this supplier.
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
  REMAINING: supply `ResourceBound` from a source-level accounting of the
  interpreter's allocation behaviour over every finite execution prefix, and
  connect it to `Loaded` and the concrete arena bounds of the linker script.
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
| Expressions | Variable lookup, assignment, constructor dispatch, equality/inequality, the two string concatenation cells, and `hDivOv`. Equality needs coherent operand maps, allocated bounds, payload coverage, and native identity. The four string comparison cells are on the `StrCmpCell` layer down to `StrCmpOperandsSupply` and `StrLeftSurvivesSupply` (below). |
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
leaf exit IS the `noArenaFoot` footprint); `hVar` from `Rows.VarLeafResid` +
the named premise `VarPinnedSim`; `hNeg`/`hNot`/the four logical cases from the
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
open on `EvalEntryStrAstRegion`). Obstruction (var leaf): `evalVarSim` retains no
write set because `env_get_found_uncond''` (`EnvGetSpec9.lean:371`) exposes only
`c'.σ.mem = m'`; the prologue agreement `houtside` (`EnvGetSpec8.lean`, the
`hScanReady` continuation of `env_get_found_uncond'`) is consumed by
`foundSt_scanReady` and dropped. Missing supplier: one agreement conjunct
`∀ a ∉ [sp0-64, sp0) ∪ [out, out+24), m'[a]? = m0[a]?` through `foundSt_scanReady`,
`env_get_found_uncond''`, `EvalVarEntry.env_get_found`/`VarPostCall.memFrame`, and
`blockC_var` (≈40 lines); until then the variable leaf is available at `exitFoot`
only (`EvalIH.exitFoot`).

### 5. Close divergence, errors, and final assembly

- Construct `DivWork`: loop-head representation, `Loaded` entry drive,
  iteration/re-entry, and the 29-arm approximate recursive dispatch.
- Construct `ErrWork`: loaded-program-indexed leaves, recursive error
  propagation, formatted error/exit tail, and top-level abrupt completion.
  Complete auxiliary `hCallTooMany` with its indexed child and signed count
  bridge; reuse the bad-closure impossibility proof.
- Construct all 63 `TermResidualsBase` fields, then `RemainingWork`, then the
  final refinement theorem. Remove the 56 inherited discipline findings and the
  12 per-entry allocator ledger fields R14 reports (supplied by `of_alloc`).

## Validation and automation still to finish

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
