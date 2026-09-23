# vsa-iris-logic: MachCSL in iris-lean, for VSA

This project ports the parts of MachCSL (Kaashoek and Zeldovich,
arXiv:2609.04043; Rocq development `mit-pdos/xv6iris` at `8438e55`) that VSA
needs. It re-states them in iris-lean (`leanprover-community/iris-lean` at
`740e2c4`, core `Iris` library only, no Mathlib) on Lean 4.34. The target is
VSA's open allocator problem: `MallocContract` frames malloc with a
state-independent `privFoot`. Commit `eb73d8c` records that no such
footprint exists for dlmalloc.

Everything builds. There is no `sorry`, and every headline theorem depends
only on `propext`, `Classical.choice` and `Quot.sound` (`VsaIris/Audit.lean`).
The one assumption is the allocator's instruction-level proof. It is carried
as a structure parameter (`DlMallocImpl`), the way MachCSL carries an
unproved callee as a `Module Type`.

## Files

| File | Ports | Content |
| --- | --- | --- |
| `Machine.lean` | `RiscvLang.v:765-775` (`mexpr`, `LoopE`), `:1593-1604` (`mval`, `prim_step`), `:2254` (`riscv_lang`) | `MachineModel` (abstract deterministic ISA step with total register and memory projections) and its Iris `Language`: the expression is the CPU loop |
| `Ptsto.lean` | `RiscvPtsto.v:1359` (`reg_pointsto`), `:1584` (`mem_pointsto`), `:2207-2219` (`reg_agree`, `reg_interp_at`), `:2340` (`mstate_interp`), `:2909-2926` (`reg_valid`, `reg_update`), `:2622` (the `irisGS` instance) | `r ↦ᵣ v`, `a ↦ₘ b`, the two ghost-map bridges, and the state interpretation |
| `Step.lean` | `RiscvPtsto.v:2804-2809` (`wp_triv`, `mWP`); the `wp_exec_step` → `wp_instr` layering in `claude-notes/design/execution-model.md` | `mTWP` (the loop's total WP), `wp_exec_step`, `wp_exec_halt`, and `wp_local_step`, the footprint rule every instruction leaf reduces to |
| `Adequacy.lean` | `RiscvAdequacy.v:182-196` (initial ghost maps), `:1533` (`riscv_power_adequacy`) | `mach_adequacy`: from the loop's total WP, the machine halts and its exit satisfies `φ`; `MachGF`, a concrete functor list, so the theorem is not vacuous |
| `Call.lean` | paper Figs. 7-8 and §4.3-4.6; `SpecKalloc.v:30-56` for the spec shape | `wp_ret`, `wp_jal`, `fnSpec` (continuation-style function spec), and `wp_call` |
| `DlHeap.lean` | `KallocInv.v:149-159` (`byte_any`, `page_own`), `:281` (`freelist_chain`), `:394` (`kmem_res`), `:403-434` (pop/push), `:436-445` (`kalloc_post`, `kfree_pre`); `SpecKalloc.v`/`SpecKfree.v`; `Module Type KALLOC` (`SpecKalloc.v:52`) | `isHeap L H`, `blockOwn`, carve/return lemmas, `mallocSpec`/`freeSpec`, `DlMallocImpl`, `wp_call_malloc`, `wp_call_malloc_keeps`, `no_fixed_privFoot`, `eb73d8c_witness` |
| `Example.lean` | none | A toy countdown machine carried through the whole stack to `Halts`, as a check that nothing is vacuous |
| `LocalRun.lean` | none | `wp_localRun`: a chain of segments over an owned register list and an owned byte *set*, on the lagging interpretation; `segFrom_of_runFact` takes VSA `RunFact`s as segments |
| `MallocRun.lean` | none | `allocCall_of_localRun` (one allocator call from its local run); `DlMallocImpl` and the credit-indexed `DlMallocRoomImpl` from the first-order runs `MallocLocalRun`/`FreeLocalRun`/`MallocRoomRun` |
| `Vsa/HeapShape.lean`, `Vsa/Malloc.lean` | none | `vsaLayout` (`Shape` = `DlHeap.HeapAt` with exact live blocks; `BlockHeapAt.transport`: it reads only `heapFoot`), `vsaRoom` (`AllocationReserve`), `vsaDlMallocImpl`, `vsaDlMallocRoomImpl` |
| `Vsa/ControlWitness.lean`, `Vsa/ControlEnd.lean` | none | the eb73d8c control heap: its Iris shape, both calls' post-states inside the live-relative frame, and `MallocEnd`/`MallocRoomEnd` at the concrete `malloc(64)` return |
| `Vsa/MallocConsumer.lean` | none | `wp_call_malloc_owns`, `ownSet_agree_state`, and `mallocRoomCallerFacts_of_iris`: every `MallocReturnAt` field `prepareCopy` uses, from the Iris spec |

The project is 1,599 lines. MachCSL's corresponding Rocq layers run to
several thousand lines, but most of that is multi-hart, TSO, device, and
page-table machinery that VSA does not need.

## How the malloc frame obstruction goes away

`MallocContract.privFoot` had two jobs:

- cover every byte malloc may write, in every state;
- avoid every live payload, in every state.

On the admitted control heap, `malloc(32)` writes `0x82000238`. From the same
state, `malloc(64)` returns `[0x82000210, 0x82000250)`, which contains that
byte. `no_fixed_privFoot` proves that no footprint does both jobs.

MachCSL never states a footprint. Instead, the allocator owns its storage
(`kmem_res` owns every free page). Here, `isHeap L H` owns `heapFoot L H`:
the allocator globals plus every arena byte outside the live extents `H`.
That set is relative to the current live list.

`eb73d8c_witness` checks the concrete case:

1. From `H0`, the allocator owns `0x82000238`, so `malloc(32)` may write it.
2. `malloc(64)` returns a fresh block that contains the byte.
3. After that call, the byte belongs to the caller's `blockOwn`, not to
   `heapFoot ((0x82000210, 64) :: H0)`.

`heapFoot_carve` and `heapFoot_return` are the set-level cores of malloc's
return and free's entry. They are the analogues of `kmem_res`'s pop and
`kmem_res_push`.

The caller's side is `wp_call_malloc`. An arbitrary resource `R` that the
caller owns reaches the continuation unchanged, because malloc's spec never
mentions it. `wp_call_malloc_keeps` specialises this to one byte `a ↦ₘ b`
and adds the disjointness facts VSA derives by hand: `a` is outside the
returned block and outside the allocator's new footprint. Both follow from
ghost exclusivity (`owned_off`), not from a contract clause.

The stack window below `sp`, which `MallocContract`'s frame special-cases, is
here an owned resource (`stackScratch`) that the caller lends and gets back.

## Deviations from MachCSL, and why

1. **The language has values, and the WP is total.** MachCSL's loop never
   stops (`mval := Empty_set`), and `wp CpuLoop` is a safety statement.
   VSA's `term_sim` needs `Halts c out 0`. The loop therefore steps to
   `done e out` when the ISA model signals HTIF exit. `mTWP` is iris-lean's
   total WP (`TotalWeakestPre.lean`), and adequacy combines `twp_total`
   (strong normalisation) with `twp.to_wp` and `wp_adequacy_gen` (not stuck,
   plus the postcondition at the exit). Determinism turns these into `Halts`.
2. **Whole-instruction steps.** MachCSL steps one Sail-monad node at a time
   (`hart_node_step`, `RiscvLang.v:1147`) so that invariants can open
   between memory events on multiple harts. VSA is single-core and already
   has instruction-level facts, so a primitive step is one `stepOnce`.
3. **Memory uses the partial-agreement bridge.** MachCSL uses
   `gen_heap_interp σ.mem` (exact agreement) for memory and an existential
   agreeing map only for registers. Here both use the register-style bridge.
   The ghost map only has to agree with the state where it is defined, so
   the Sail memory (unmapped bytes read as zero) never has to be a finite map
   mirrored in ghost state. Initial ownership is any finite map that agrees
   with the initial state.
4. **Dropped: TSO, interrupts, devices, multiple harts, power cycles, page
   tables, and the TLB.** None exist in VSA. Also dropped: the lock around
   the allocator (`is_lock … "kmem"`). `isHeap` is an exclusive resource
   threaded through the interpreter, like MachCSL's boot-mode
   `kalloc_avail (Some n)`.
5. **No page-count ghost** (`kmem_avail_auth`). VSA's capacity bound
   (`InitialAllocatorAt.capacity`) stays a pure fact.
6. **Set ownership instead of fixed big-seps.** `page_own` is 4096 `byte_any`
   cells. dlmalloc's free storage is a state-dependent set, so `ownSet S Φ`
   owns a finite set through an existential duplicate-free list. Carving and
   joining are `ownSet_split` and `ownSet_join`.
7. **Exec facts are hypotheses.** MachCSL proves instruction leaves by
   evaluating the Sail decoder (`decode_bridge_*`). Here `RetExec` and
   `JalExec` are the leaf-level facts, stated as `LocalStep` against a
   footprint. VSA's reflected segments (`segEval`, `#derive_case`) already
   produce exactly this shape.
8. **Registers are indexed by `Nat`, with PC at 32.** MachCSL uses the Sail
   `register` type and bundles `PC ∗ nextPC ∗ minstret ∗ clock` into
   `pc_is`. VSA's counters (`tick`, `steps`, CSRs) change on every step and
   are simply not projected, so no one owns them.
9. **`sepL` is a local structural big-op.** It is used instead of
   `[∗list]`, so that footprint lemmas go by plain list induction.

## Mapping onto VSA

- **`Triple`/`TripleN` → `mTWP`.** `Triple P Q` ("from every `P`-state, some
  finite run reaches `Q`") becomes a WP whose continuation holds `Q`'s
  resources. Termination is still by Lean induction. There is no Löb
  induction under a total WP, so a loop or a recursion is proved by
  induction on a measure or on the `BigStep` derivation, exactly as today
  (`Example.countdown_twp`).
- **`InterpSim.term_sim`.** Prove, by induction on `BigStep p out`,
  `⊢ init_own -∗ mTWP (fun v => ⌜v = (0, out)⌝)`, with one `fnSpec` each for
  `eval_expr`, `exec_stmt` and `interp_run`. Their pre- and postconditions
  are Iris versions of `ExprRepr`/`StoreRepr`/`ValueRepr` over owned bytes,
  plus `isHeap`. Then `mach_adequacy` gives `Halts`. `Loaded L p c` becomes
  the initial ownership maps (`AdequacyHyp`).
- **`InterpSim.stuck_sim`.** Use the partial WP (Löb is available there)
  with postcondition `v.1 ≠ 0`. `wp_adequacy_gen` then says that every exit
  the machine reaches is nonzero. On a deterministic machine that is
  "diverges or error-exits", the disjunction `stuck_sim` asks for. This
  replaces the 29-arm divergence fold's step counting (`TripleN`).
- **`RemainingWork`.** The 63 `TermResidualsBase` fields are per-construct
  obligations. Each becomes a construct case in the `BigStep` induction
  against the per-function specs. The allocator field is `DlMallocImpl`,
  which replaces `MallocContract`.

### What the `CLAUDE.md` hand-framing table collapses into

These rows are instances of the frame rule, `wp_local_step`, or ghost
exclusivity. They disappear rather than get ported:

| Rows in `CLAUDE.md` | Replaced by |
| --- | --- |
| ABI register frame (`FrameMeta.abiFrame_of_wrChain`), callee-saved preservation | Callee-saved registers are not handed to the callee |
| Memory frame and footprint posts (`memFrame_of_chain`, `bblocks_sound_framed`), framed callee variants | The continuation wand; `wp_local_step` touches only its footprint |
| `StableUnder`, `SeparationLogic.FramedTriple.frame`, `frame_machine` | The Iris frame rule |
| `HeapOwned.transport`, `StoreOwned.repr_transport`, `StoreArraysReady.transport`, `ReprSurvival` | Owned representations are untouched by construction |
| `HeapOwned.ownedOff`/`entryOff`, `transport_off`/`repr_off`, `privFoot_disjoint`, `Reserved.outsidePrivate` | `owned_off`, `owned_off_heap`, `owned_off_block` |
| `AllocLedger` per-entry allocator facts (rule R14), `mallocReturn_of_parked`/`freeReturn_of_parked` | `isHeap L H` threaded through, plus `wp_call_malloc` |
| Shared-byte agreement (`shared_agree`, `SharedReadGeom`, `BindingShared`) | Persistent `↦ₘ□` or fractional points-to for shared and immutable bytes |
| "Retains X through the actual Y" (`EvalReturn` selected maps, `transport_stack`/`transport_frame`, `ReturnedWith`, `.forget`) | Resources in the continuation; the returned state is whatever the postcondition owns |
| Exit wideners (`Widen`, `LeafWiden`, `ExecRecWiden`, `EvalRecWiden`) | Continuation-style specs have no exit predicate to widen |
| `StackOK` headroom exceptions | `stackScratch`, an owned block |

These stay, and become exec-fact producers for `wp_local_step`:
decode/segment reflection (`#derive_case`, `gen_fn.py`, `segEval`,
`bridgeOfSeg`), the fast-reflection rules, `BigStep` and the WHILE
semantics, `MemRepr` (restated as ownership predicates), determinism, and
the refinement composition in `Refinement.lean`.

## Migration path

1. **Toolchain** (Spike A): bump VSA to Lean 4.34 and depend on iris-lean
   core. Nothing below can start until this builds.
2. Instantiate `MachineModel` with `Config`/`stepOnce`:
   `reg c k := (c.σ.regs.get? (gpr k)).getD 0`, `mem := readByte`. Prove
   `mach_adequacy` implies `Halts c out 0` for VSA's `Halts`.
3. Write the exec-fact adapter: a reflected segment (`segEval_sound` result
   plus its write log) becomes a chain of `wp_local_step` uses, or better,
   one `wp_segment` rule over a whole segment's footprint. This is the
   exponentiating layer's new output format.
4. Write the three interpreter function specs (`fnSpec` for `eval_expr`,
   `exec_stmt`, `interp_run`) with Iris representation predicates. Port the
   leaf cases first (literals, var), then binary operators, then calls and
   closures. MachCSL's §9.1 lesson applies: humans fix the abstractions and
   the representation predicates, and agents fill the proofs.
5. Replace `MallocContract` with `DlMallocImpl`. Its fields remain the only
   allocator assumption until someone proves `_malloc_r` against it.
6. Reassemble `term_sim` (total WP) and `stuck_sim` (partial WP), and keep
   `Refinement.lean` unchanged.

## Risks

- **Toolchain.** Everything depends on step 1. The 1,968-module VSA build
  and the Sail-generated model are sensitive to elaboration changes.
- **Totality.** A total WP forbids Löb, so every loop in the binary (the
  `interp_run` loop, `strlen`/`memcpy` word loops, bin scans in dlmalloc)
  needs an explicit measure. VSA already has these measures (`LoopSteps`,
  `loopFromBody`), but each spec must quantify its WP over the measure.
  `stuck_sim` needs the partial WP and its own adequacy route, which is
  sketched above but not built here.
- **The allocator is still an assumption.** `DlMallocImpl` is proved from
  the first-order runs `MallocLocalRun` and `FreeLocalRun`, and
  `DlMallocRoomImpl` from `MallocRoomRun` (`MallocRun.lean`). Those runs are
  the only allocator assumption. `Shape` is `HeapAt` over the owned image
  (`Vsa/HeapShape.lean`). The concrete control heap satisfies the runs' end
  conditions (`Vsa/ControlEnd.lean`), but nothing proves `_malloc_r` against
  them. The spec hands the callee its code (`textOwn`) and the callee-saved
  registers it spills (`savedOwn`). Without both, no real allocator could
  meet it. Proving `_malloc_r` itself is a large job (xv6's much simpler
  kalloc took 834 lines of `ProofKalloc.v`). A proof would chain `segEval`
  segments through `segFrom_of_runFact`.
- **Performance.** The state interpretation is two ghost maps, independent
  of Sail state size; only owned cells are tracked. The cost that remains is
  the exec facts, the same Sail evaluation VSA pays today. The proof mode
  handled the small proofs here quickly (each module elaborated in about
  4-17 seconds under a load average near 70). Big footprints (a
  4096-byte-style block) should stay behind opaque definitions, as MachCSL
  does with `Typeclasses Opaque` on `page_own`.
- **Wander.** The Diaframe-style automation from the "Iris in Lean" paper is
  not in iris-lean master at `740e2c4`, so it was not tried. `iframe`,
  `ihave` and `icases` were enough for everything here.
- **Proof-mode friction, for whoever continues this:**
  - `GF` often has to be pinned (`(GF := GF)`, `⊢@{IProp GF}`).
  - Defs must be unfolded in the goal before `iintro` can destructure them;
    `abbrev` helps.
  - `ihave %h := lemma $$ H1 H2` does not consume `H1`/`H2` when the result
    is pure, which is what makes the footprint-reading lemmas cheap.

## Recommendation

Adopt this, but only after step 1 of the migration passes, and in the order
above. The core claim holds: once the allocator owns its storage, the frame
obstruction is not a contract that has to be designed. The frame rule
discharges it (`wp_call_malloc` is an 8-line proof). A large share of
`CLAUDE.md`'s mandatory-tool table is hand-built framing that the logic
provides for free.

Do not port the existing ~2,000 modules proof by proof. Keep the reflection
layer, which produces exec facts, and rebuild the interpreter-level specs on
`fnSpec` with ownership-based representation predicates. That is where
VSA's time has gone, and where MachCSL spent its human design effort
(paper §9.1).
