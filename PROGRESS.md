# iris-heap progress

Branch `iris-heap`, rebased on `iris-machine` `074583c` (`VsaIris/Vsa/Instance.lean`). `lake build Vsa VsaIris` is green. Every headline theorem depends only on `propext`, `Classical.choice` and `Quot.sound`; see `VsaIris/Vsa/HeapAudit.lean`. There is no sorry, axiom or raised limit.

## Done

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

## Holes left (named, not proved)
- **`MallocLocalRun`, `FreeLocalRun`, `MallocRoomRun`** (`VsaIris/MallocRun.lean`). These are the instruction-level runs of `_malloc_r`/`_free_r`. Each is a chain of end-framed segments over `allocRegs` and `stackWin ∪ heapFoot` (free adds the freed block), ending in `MallocEnd`/`FreeEnd`/`MallocRoomEnd`.
  - They replace `MallocContract.spec/freeSpec`, `MallocSuccessRun` and the `privFoot` clauses.
  - Satisfiability evidence: `ControlEnd`/`ControlWitness`. These are consistency checks against post-states computed from the disassembly, not a Sail run of `_malloc_r`.
- **realloc** is not ported (`ReallocInstance` stays VSA-side).
- **`text`** (the allocator's code bytes) is a parameter. It should be instantiated from `Code.FixedTextLoaded` / the loaded image.

## Is the obstruction gone?
- **Yes, in the specification.**
  - No state-independent footprint appears anywhere.
  - Caller bytes survive by ghost exclusivity.
  - The concrete eb73d8c pair satisfies the new end conditions, while `no_fixed_privFoot` refutes the old ones.
- **Not yet in the final theorem.**
  - VSA's `term_sim` still takes `MallocContract` via `AllocLedger`.
  - The Iris route replaces it only once the interpreter specs are rebuilt on `fnSpec` (DESIGN.md migration step 4).
  - Until then, `mallocRoomCallerFacts_of_iris` shows the consumer's premises are derivable without the contract.

## Next
1. Prove `MallocRoomRun` for the top-split fast path by chaining `seg_runFact` segments with `segFrom_of_runFact`. This is the path every control allocation takes.
2. Instantiate `text` from the loaded image, and `live ⊇ allocGlobal ∪ arena` from `VsaOk`.
3. Port realloc as a third `allocCall_of_localRun` instance.
4. Use `wp_call_malloc_owns` in the sibling's `EnvNewPilot` to replace its allocator premises.

## DECIDED (confirmed by the user)
- The in-place signature change stays: `DlMallocImpl`/`mallocSpec`/`freeSpec`/`wp_call_malloc*` take the allocator's code (`textOwn`) and the callee-saved registers it spills (`savedOwn`, `s0-s3`).
- Iris live blocks are whole chunk payloads. VSA's finer ledger extents live inside blocks (`Covered`).
