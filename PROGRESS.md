# iris-machine progress

Branch `iris-machine`, HEAD after the pilot. `lake build Vsa VsaIris` is green
(2234 jobs). Every new theorem depends only on `propext`, `Classical.choice`,
`Quot.sound` (`VsaIris/Audit.lean`). No sorry, axiom, native_decide or raised
limit. `iris-heap` is merged, and the sibling has fast-forwarded to it.

## Done

1. **Multi-step segment rule** (`VsaIris/Step.lean`: `wp_run`, `RunFact`).
   VSA's facts are segment facts: `n` instructions with an end-state frame
   only. The state interpretation (`fullInterp`, `Ptsto.lean`) lets the ghost
   maps lag the machine by `j` steps. `j` is recorded in a control ghost map,
   `mTWP` hands its prover the key-0 cell at 0 (`cpuTok`), so clients always
   see `j = 0` (`mstateInterp`). `wp_local_step` is the one-step case.
   `MachineModel.ok` is a global invariant (default `True`).
2. **Instance** (`VsaIris/Vsa/Instance.lean`).
   - `vsaModel live` runs over `Config` and `stepOnce`. The PC is register
     32, GPRs are read through `gprGet`, memory is the total read.
     `VsaOk live` = `GoodState`, tick < 2, GPR presence, presence of the
     `live` bytes.
   - `vsa_adequacy`: the loop's total WP with postcondition `(0, out)` gives
     `Vsa.Machine.Halts c out 0`, verbatim.
3. **Bridge from reflection.**
   - `seg_runFact` turns `segEval_sound` into a `RunFact`. `wp_seg` is the
     one generic Iris rule for any `#derive_case` segment, with named
     ownership: PC, pinned GPRs, written bytes, read-only bytes.
   - `jalExec_of_site` (`Tools.lean`) turns VSA's `JalStep` into `JalExec`.
   - Write logs are pointwise (`Pointwise`, `writeLog_getD_congr`,
     `writeLog_present`).
   - `segToTriple` and `bblocks_sound_framed` are projections of the same
     `segEval_sound`/`bblocks_sound_bt` endpoint, so `wp_seg` subsumes them.
     `Triple`/`TripleN` carry no frame, so they cannot feed a footprint rule
     directly: the segment-level facts are the right producer.
4. **Pilot: env_new** (`VsaIris/Vsa/EnvNewPilot.lean`).
   - `envNew_spec` is a continuation-style (MachCSL) spec of the whole
     function:
     - the 5-instruction prefix segment goes through `wp_seg`;
     - `jal malloc` goes through `wp_call_malloc_owns`, with the stack frame
       as the owned set;
     - the existing `envNewSuccessSeg` goes through `wp_seg`.
   - The fresh block comes back as `envBlock p par`: owned bytes with
     `read64` facts for all four `Env` words. Callee-saved registers, the
     frame, and everything else the caller owns come back by ownership.
   - `envNew_spec_vsa` instantiates it at the real allocator (`vsaLayout`,
     `vsaDlMallocImpl`, arena geometry by `decide`).

## Numbers (pilot versus VSA's `envNewAllocator_run` cone)

Lines are raw lines (non-blank, non-comment lines in parentheses).
Elaboration is `lake env lean` wall time minus an imports-only stub, median of
3 runs, load average about 2.

| | lines | elaboration |
|---|---|---|
| **Iris pilot** `EnvNewPilot.lean` | 525 (443) | 1.4 s |
| Iris shared, one-time: `Instance.lean` + `Tools.lean` | 750 (572) | 0.3 s |
| **VSA env_new cone** (10 files below) | 3414 (2747) | ~5.3 s |
| `EnvNewSpec` | 1197 (904) | 3.7 s |
| `EnvNewSites` | 691 (603) | 0.2 s |
| `rows/EnvNewContractSupply` | 682 (567) | 0.8 s |
| `EnvNewSuccessSuffix` | 291 (262) | 0.6 s |
| `HelperCallEnvNew`, `CallClosureEnvNewMarshal`, `EnvNewRetained`, `RuntimeOwnershipEnvNew`, `EnvNewAllocatorReturn`, `EnvNewAllocator` | 553 | ≈0 s each |

Caveats. The comparison is not apples to apples.
- **The pilot reuses VSA.** It uses `envNewSuccessSeg` (defined in
  `EnvNewSuccessSuffix`), the geometry structures and address lemmas from
  `EnvNewSpec`, two decode lemmas from `EnvNewSites`, the generated
  `Code.Env_new`, and the decode tables. These are exec-fact producers, which
  is the intended split.
- **VSA proves more semantics.**
  - `EnvNewAllocatorPost` includes the semantic frame (`EnvNewFresh`), the
    runtime allocator ledger (`RuntimeAllocatorState` with the allocation map
    and credits), and shared-byte agreement.
  - The Iris spec states the machine-level effect only: bytes, registers,
    and `isHeap`.
  - Rebuilding those facts needs Iris representation predicates (DESIGN.md
    migration step 4), and those are not written yet.
- **NULL handling differs.** VSA assumes arena non-exhaustion. The pilot
  hands the NULL return to a caller continuation. The sibling's credit-indexed
  `mallocRoomSpec` could remove that continuation.
- **The pilot is a single, simple function.** Most of VSA's cost there is
  hand-threaded framing per site (`NotWrittenEnv`, `obs_*_other`, the
  `hloaded` threading through every store), which the Iris proof never
  states.
- **Time.** Both are fast on this machine; neither is a bottleneck. The Iris
  proof mode needed `iexact` where `iframe` failed on non-syntactic matches,
  and `rw` on Iris goals also rewrites hypotheses. These are friction, not
  cost.

## Holes

- `MallocLocalRun`, `FreeLocalRun` (sibling, `VsaIris/MallocRun.lean`). These
  are the instruction-level runs of `_malloc_r`/`_free_r`, the only allocator
  assumptions `envNew_spec_vsa` takes. The sibling is proving the top-split
  path.
- The `envNew_spec` NULL continuation `Knull` is the caller's obligation.
  The error path is `fwrite`, then `exit(1)`.
- `live` and `text` are parameters. They should be instantiated from the
  loaded image (`Code.FixedTextLoaded`) when the whole-program adequacy is
  assembled.
- `stuck_sim` (partial WP) and the interpreter-level `fnSpec`s are not
  started; see DESIGN.md.

## Next

1. Representation predicates for the store/frame (`Env` block ↦ semantic
   frame), then state `env_new`'s post against them. This recovers
   `EnvNewFresh`/`RuntimeAllocatorState` as derived facts.
2. Switch the pilot to `mallocRoomSpec` to drop `Knull`.
3. Next function: `env_define` (the malloc/realloc/memcpy consumer). This is
   where VSA's hand framing (`AllocOff`, transports) is heaviest.

## Recommendation

Migrate. Keep all reflection (`#derive_case`, `segEval_sound`, site/decode
lemmas) as the exec-fact producer, and consume it only through `wp_seg`,
`jalExec_of_site` and the call rules. Port function by function, leaf
callees first (`env_new`, `value_*`, `strlen`, `memcpy`). Each function gets
one continuation-style spec, and callers use it by the frame rule.
- **Build first:** representation predicates over owned bytes (store, frame,
  value, AST) before porting interpreter cases. Without them each
  function's post stays machine-level, as in this pilot.
- **Don't port:** the framing rows of CLAUDE.md's table (`FrameMeta`
  metatheorems, `AllocOff`, transports, `ReturnedWith`). The pilot needed
  none of them.
- **Main risk:** loops and recursion, which need measures under the total WP
  (`LoopSteps` exists). The pilot has no loop; `strlen`'s word loop is the
  natural next test.

## QUESTIONS

- `live`: a points-to fixes the *total* read (`getD 0`). Fetch facts need
  `σ.mem[a]? = some b`, so code-byte presence comes from `VsaOk.live`, a
  fixed set that stores never shrink. The alternative is an `Option`-valued
  memory projection, where points-to implies presence. That makes
  never-written arena bytes unownable, which would break `isHeap`. I chose
  the total read plus `live`.

# iris-heap (sibling) status, merged

Branch `iris-heap`, rebased on `iris-machine` `074583c` (`VsaIris/Vsa/Instance.lean`). `lake build Vsa VsaIris` is green. Every headline theorem depends only on `propext`, `Classical.choice` and `Quot.sound`; see `VsaIris/Vsa/HeapAudit.lean`. There is no sorry, axiom or raised limit.

### Done

1. **Heap shape** (`VsaIris/Vsa/HeapShape.lean`).
   - `vsaLayout` instantiates `DlLayout`:
     - `global = allocGlobal`, read off the ELF symbol table: `__malloc_av_`, `brk.0`, the sbrk/trim/top-pad/max-mem words, `__malloc_current_mallinfo`, and both errno words that `_sbrk_r`/`_malloc_r` write.
     - The arena is `[_end, __heap_end)`.
     - `Shape = imgShape`, which is `DlHeap.HeapAt` read off the owned image, with every live extent an exact chunk payload (`BlockHeapAt`).
   - **`BlockHeapAt.transport`**: `HeapAt` reads only `vsaFoot H` = globals ∪ (arena \ live extents) = `heapFoot vsaLayout H`. `vsaFoot_iff` shows the footprint and the live blocks partition the arena.
   - So `isHeap` owns exactly the bytes the shape constrains, plus the free bytes malloc may write. The frame is the live-relative one that §2 asks for.
   - `blockHeapAt_of_heapAt` and `blockHeap_of_initial` turn VSA's boundary heap (`InitialAllocatorAt`, `InitialOwned.allocator`) into the Iris shape. The live blocks are the in-use chunk payloads, and they cover every VSA ledger extent.
2. **eb73d8c test** (`Vsa/ControlWitness.lean`, `Vsa/ControlEnd.lean`), at the real `Control.heapMem`:
   - The Iris shape holds.
   - `malloc(32)` and `malloc(64)` on `_malloc_r`'s top-split path both write only `heapFoot vsaLayout controlBlocks`, and both reach the block shape with their block live.
   - `0x82000238`, written by `malloc(32)`, lies in `malloc(64)`'s fresh block and then belongs to the caller (`ObstructionAdmitted`).
   - The `malloc(64)` return satisfies `MallocEnd` and `MallocRoomEnd` (`malloc64_end`, `malloc64_roomEnd`).
   - `control_no_fixed_privFoot` is the old obstruction at the same blocks.
3. **Spec repair** (`VsaIris/DlHeap.lean`). The original `DlMallocImpl` could not be satisfied by any real allocator:
   - `⊢ mallocSpec` gave the callee no code bytes;
   - `_malloc_r` spills `s0-s3`, whose ghost cells stayed with the caller.
   - It now takes `textOwn text` (persistent) and `savedOwn saved` (returned at the same values). `heapFoot_carve_gen` is the carve lemma for any per-byte resource.
4. **Run rule** (`VsaIris/LocalRun.lean`).
   - `wp_localRun` is the rule for a chain of segments over an owned register list and an owned byte *set*, built on the sibling's lagging state interpretation (`seg_aux`).
   - `segFrom_of_runFact` turns a VSA `RunFact` (from `Inst.seg_runFact` / `segEval_sound`) into one segment.
5. **DlMallocImpl** (`VsaIris/MallocRun.lean`, `Vsa/Malloc.lean`).
   - `allocCall_of_localRun` is the single proof core; malloc, free and the credit-indexed malloc are instances of it.
   - `dlMallocImpl_of_localRuns` and `vsaDlMallocImpl` build it for `vsaModel`/`vsaLayout`. The register lists come from the disassembly: `vsaClob` and `vsaSaved = s0 s1 s2 s3`.
   - The credit-indexed spec: `isHeapRoom`, `mallocRoomSpec`, `DlMallocRoomImpl`, and `vsaRoom` = VSA's `AllocationReserve` over the image, which is local (`AllocationReserve.transport_foot`).
6. **Consumer adapter** (`Vsa/MallocConsumer.lean`) for `EnvDefineAppendAllocatorPost.prepareCopy` / `envNewAllocator_run`'s malloc call:
   - `wp_call_malloc_owns`: the caller's owned byte set comes back unchanged, and is off the fresh block and the new footprint.
   - `ownSet_agree_state`: owned bytes pin the machine memory.
   - `mallocRoomCallerFacts_of_iris`: every `MallocReturnAt` field that consumer uses (`block`, `owned0`, `owned`, `store`, shared agreement, `budget`, `reserve`) follows, with no `MallocContract`, `AllocLedger`, `privFoot`, `OwnedOff` or stack-window arithmetic. `ainv` is `isHeapRoom` itself.

### Holes left (named, not proved)
- **`MallocLocalRun`, `FreeLocalRun`, `MallocRoomRun`** (`VsaIris/MallocRun.lean`). These are the instruction-level runs of `_malloc_r`/`_free_r`. Each is a chain of end-framed segments over `allocRegs` and `stackWin ∪ heapFoot` (free adds the freed block), ending in `MallocEnd`/`FreeEnd`/`MallocRoomEnd`.
  - They replace `MallocContract.spec/freeSpec`, `MallocSuccessRun` and the `privFoot` clauses.
  - Satisfiability evidence: `ControlEnd`/`ControlWitness`. These are consistency checks against post-states computed from the disassembly, not a Sail run of `_malloc_r`.
- **realloc** is not ported (`ReallocInstance` stays VSA-side).
- **`text`** (the allocator's code bytes) is a parameter. It should be instantiated from `Code.FixedTextLoaded` / the loaded image.

### Is the obstruction gone?
- **Yes, in the specification.**
  - No state-independent footprint appears anywhere.
  - Caller bytes survive by ghost exclusivity.
  - The concrete eb73d8c pair satisfies the new end conditions, while `no_fixed_privFoot` refutes the old ones.
- **Not yet in the final theorem.**
  - VSA's `term_sim` still takes `MallocContract` via `AllocLedger`.
  - The Iris route replaces it only once the interpreter specs are rebuilt on `fnSpec` (DESIGN.md migration step 4).
  - Until then, `mallocRoomCallerFacts_of_iris` shows the consumer's premises are derivable without the contract.

### Next
1. Prove `MallocRoomRun` for the top-split fast path by chaining `seg_runFact` segments with `segFrom_of_runFact`. This is the path every control allocation takes.
2. Instantiate `text` from the loaded image, and `live ⊇ allocGlobal ∪ arena` from `VsaOk`.
3. Port realloc as a third `allocCall_of_localRun` instance.
4. Use `wp_call_malloc_owns` in the sibling's `EnvNewPilot` to replace its allocator premises.

### DECIDED (confirmed by the user)
- The in-place signature change stays: `DlMallocImpl`/`mallocSpec`/`freeSpec`/`wp_call_malloc*` take the allocator's code (`textOwn`) and the callee-saved registers it spills (`savedOwn`, `s0-s3`).
- Iris live blocks are whole chunk payloads. VSA's finer ledger extents live inside blocks (`Covered`).
