# Interpreter-level design: `eval_expr`, `exec_stmt`, `interp_run` in the Iris logic

Status: DESIGN, not built. The statement skeleton is `VsaIris/Interp/Specs.lean`
(not imported from `VsaIris.lean`; its lemma bodies are `sorry` and it has never
been elaborated). This page fixes the representation predicates, the function
specs, the assembly of `InterpSim`, and the fan-out. The proofs are left to the
work packages in §9. MachCSL's own rule applies here (paper §9.1, xv6iris
`claude-notes/durable-notes.md` "Orchestration"): the top level owns the specs,
and a proof that fights its interface is evidence the interface is wrong.

Rocq citations are to xv6iris at `8438e55` (`iris/…`, `claude-notes/…`).

## Decisions (user, 2026-09-23)

- **Q1 accepted.** `Loaded` gains a `StackAdmissible` field shaped like `capacity`. The top-level statement narrows honestly; no unprovable stack claim remains. (S1)
- **Q2: `IrisHoles` replaces `RemainingWork`.** Do not keep both. Package A deletes `RemainingWork`, `TermResidualsBase`, `DivWork`, `ErrWork` and their suppliers once `endToEnd_refinement` is re-proved from `IrisHoles`; the name `endToEnd_refinement` is kept.
- **Q3: two WPs** (`mTWP` total, `mWP` partial) behind `MachWP`.
- **Q4: newlib `snprintf`/`fprintf` safety specs stay as named holes for now,** scheduled after E1–E6. They must not be forgotten: every hole lives as a field of `IrisHoles` (so it appears in the final theorem's hypothesis) AND has an entry in `VsaIris/HOLES.md` with owner package, satisfiability evidence and discharge plan. `scripts/check_iris_holes.py` fails if the two disagree.

## STATEMENT CHANGE (S1, Q1 landed): `Loaded interpRunLayout` now carries stack admissibility

`Vsa/Sim/LayoutInstance.lean` `InterpRunReadyFacts` gained the field

```lean
stack_admissible : StackAdmissible c.σ.mem stmts count
-- StackAdmissible m stmts count :=
--   ∀ p, ProgramRepr m stmts count p → ProgramStackFits p
structure ProgramStackFits (p : Program) : Prop where
  need   : stackSL.lo + Stmt.stackNeedList p + maxCallDepth * perCallBudget
             + evalFrame + interpRunFrame ≤ spEntry
  bodies : Stmt.bodiesBoundList perCallBudget p = true
```

- **What narrowed.** `interpRunLayout.atInterpRun`, hence
  `Loaded interpRunLayout p c`, hence the hypothesis of `endToEnd_refinement`
  (and of `endToEnd_refinement_iris`). `Refinement.lean` is unchanged:
  `Loaded` is generic in `Layout`, and the field sits in the concrete layout's
  ready facts, beside `ownership`, which carries
  `DlHeap.InitialAllocatorAt.capacity` (same ∀-over-`ProgramRepr` shape).
- **So `interpRunLayout' = interpRunLayout`.** §5.4 and `Specs.lean` need no
  separate layout. The skeleton's `StackAdmissible` is superseded by the
  landed one.
- **Why.** §10.4: without it, an AST deeper than the 8 MiB stack overflows
  into the heap (`heapEnd = stackSL.lo = 0x87800000`), and `InterpSim` is
  unprovable.
- **The bound's arithmetic.** `interp_run` spills 176 bytes
  (`interpRunFrame`), then calls `exec_stmt` at `spEntry - 176` with depth 0.
  Each top-level statement needs ItemZero's `execNeed s 0 = s.stackNeed +
  maxCallDepth * perCallBudget + evalFrame` below that. The consumer is
  `ProgramStackFits.execBudget`, which gives the `StackOK` at the first call.
- **Not vacuous.**
  - The control program: `NativeNameAudit.Control.readyFacts` (so
    `Control.loaded` still inhabits `Loaded interpRunLayout`).
  - Every `c/tests/*.wl` program and `Validation.recursionSmall`:
    `Vsa/Sim/StackAdmissibleWitness.lean`, one kernel `decide` of
    `programStackFits` each.
  - Needs range from 3440 to 5232 bytes, against about 2.24 MB of slack.

## 0. The design in five sentences

1. Every block of machine code (a reflected segment, a helper call, a loop) is
   proved ONCE, against an abstract WP `W` that both the total WP (`mTWP`) and a
   new partial WP (`mWP`) instantiate (§1).
2. `term_sim` uses TOTAL, derivation-indexed specs, proved by the existing
   mutual recursor over the cost companions (`EvalECost` …), exactly the motive
   pattern `TermSimAssembly` already uses. It needs no determinism lemma and has
   no error arms.
3. `stuck_sim` uses PARTIAL, outcome-quantified specs, proved by Löb. Their
   continuation is an additive pair: return with a derivation, or abort (runtime
   error or out-of-memory exit). This one Löb proof replaces `ErrWork` and
   `DivWork` together.
4. The runtime is owned by representation predicates. Strings, AST and closures
   are persistent. Frames are exclusive inside one `storeRepr`. The allocator is
   `isHeap`/`isHeapRoom` in MachCSL's counted and uncounted regimes. Output is a
   console ghost cell.
5. The final theorem is `Vsa.Refine.refinement` applied to
   `interpSim_iris (h : IrisHoles)`. `Refinement.lean` is unchanged, and
   `IrisHoles` names the allocator machine runs and the newlib safety specs,
   nothing else.

## 1. Two directions, one set of blocks

### Why two WPs

`term_sim` needs termination, so it needs a total WP, and total WPs forbid Löb.
`stuck_sim` needs a statement about programs with *no* derivation, including
divergent ones: "the machine never halts with exit 0". That is a safety
statement, and it needs a partial WP and Löb (partial adequacy: never stuck,
and every halt satisfies `Φ`).

The rejected alternative is one partial WP plus a step-credit resource for
termination (time credits). It would demand an exact step budget per
derivation: string lengths, bin scans in `_malloc_r`, the `strlen` word loop.
That is the brittle counting VSA's `TripleN` already pays for. Two WPs cost one
extra piece of glue per case (the generator emits both, §6). The blocks are
shared, and blocks are where the proof mass lives.

### The shared interface (work package F1, landed)

```lean
structure MachWP (M : MachineModel) where          -- VsaIris/MachWP.lean
  W       : (Nat × String → IProp GF) → IProp GF
  lat     : IProp GF → IProp GF                    -- step modality: id (total), ▷ (partial)
  lat_intro : ∀ P, P ⊢ lat P
  lagRun  : LagFoot M Fp Fp' Pre Post K →          -- the lag kernel (Lag.lean) at W level
            Fp ∗ (∀ σ σf, ⌜Post σ σf⌝ -∗ Fp' σf -∗ lat (W Φ)) ⊢ W Φ
  halt    : …                                      -- VsaIris.wp_exec_halt, abstracted
  fupd    : (|={⊤}=> W Φ) ⊢ W Φ
  -- console (F2): MachWP.runOut and MachWP.haltConsole are derived theorems
```

- `twpW M := ⟨mTWP M, id, …⟩` and `wpW M := ⟨mWP M, ▷, …⟩`.
  `mWP M Φ := cpuTok -∗ WP Loop @ NotStuck; ⊤ {{ Φ }}` (iris-lean
  `ProgramLogic/WeakestPre.lean`) with the same lagging state interpretation
  (`Ptsto.fullInterp`).
- Why `lagRun` rather than a `run` field: a `RunFact` segment and a
  `LocalRun` segment are both instances of one lagged run (`LagFoot`). Both
  WPs prove the kernel once (`Lag.lag_run`, from a single-step rule
  `StepRule lat L`), and `MachWP.run` (= `wp_run`), `MachWP.runL` and
  `wp_localRunW` derive from it for every `Wp`. The earlier draft's `run`
  field could not give the loop rule, whose segments end in a predicate, not
  in exact values.
- `lat` records the later that one step of the partial WP pays for. Blocks use
  the later-free `Wp.run`; `(wpW M).runL` (`wp_run_later`) gives the
  continuation `▷ mWP`, which Löb consumes (`wp_call_later` for a recursive
  `jal`).
- `twp_wp : mTWP M Φ ⊢ mWP M Φ` (iris-lean `twp.to_wp`) is not
  needed by any block, because blocks are generic. The assembly uses it only
  where a partial proof calls something proved only totally (§5.3).
- Partial adequacy: `mach_adequacyP` (`Adequacy.lean`) and, at the VSA
  instance, `Inst.vsa_adequacyP_nonzero`:
  `AdequacyHypP GF (vsaModel live) mr mm (fun v => v.1 ≠ 0) →
   Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0`, `stuck_sim`'s conclusion.

Every lemma below `eval_expr` is stated `∀ (Wp : MachWP M)`. Helper loops are
proved by **fuel induction, not Löb**, which is sound for both WPs and is also
MachCSL's idiom for bounded loops (`ProofMemset.v:1-9` "bounded loop, not
iLöb"; `ProofMemmove.v:350` `mm_loop`, induction on `rem`). Only the three
recursive entry points (`eval_expr`, `exec_stmt`, and the `interp_run` loop) are
mode-specific.

### The mode-generic function spec

`fnSpec` (`Call.lean`) is `fnSpecW Wp` at `Wp := twpW`. `fnSpecW Wp` takes the
WP as a parameter; the body is unchanged. The partial recursive specs need a
second exit, `fnSpecAbort` (§4.2):

```lean
def fnSpecAbort (Wp) (entry) (P Q : BitVec 64 → IProp GF) (A : IProp GF) :=
  □ ∀ r Φ, PC ↦ᵣ entry -∗ ra ↦ᵣ r -∗ P r -∗
    ((PC ↦ᵣ r -∗ ra ↦ᵣ r -∗ Q r -∗ Wp.W Φ) ∧ (A -∗ Wp.W Φ)) -∗ Wp.W Φ
```

The `∧` is xv6iris's rule (`durable-notes.md`, "Contracts and resources": two
continuations of which exactly one fires are an ADDITIVE pair). The return
branch and the abort branch are proved from the SAME resources, so a caller's
frame, and the abort continuation it inherited, are available to both.

## 2. Foundations the specs need (work packages F1–F3)

- **F1, the partial WP (landed).** `mWP` (`PartialWP.lean`); the segment rule
  with a later for it (`wp_run_later`); the halt rule (`wpP_exec_halt`); and
  partial adequacy at the VSA instance (`Inst.vsa_adequacyP`):

  `AdequacyHypP … φ → Diverges c ∨ ∃ out e, Halts c out e ∧ φ (e, out)`

  The loop is deterministic with one non-value expression, so never stuck
  plus no reachable exit gives `Diverges` (`diverges_or_halts_of_adequate`,
  classical case split on exit reachability). It reuses `wp_adequacy_gen`,
  as the total route does.
- **F2, the console (built: `Ptsto.lean`, `Step.lean`, `Vsa/Console.lean`).**
  - `MachineModel` has `out : State → String` (VSA: `Vsa.Machine.output`).
  - The console cell `consoleOwn s` is a ghost map on `MachGS.conName`, key 0.
    Its authority `conInterp` is part of `mstateInterp` and lags with the
    register and memory maps (`lagInterp`, `ConAgree`). MachCSL's console
    authority sits in the state interpretation the same way (paper §7.5,
    Figure 28 `cons_auth`). `consoleOwn_excl`: there is one console.
  - Every run fact frames the output. `RunFactO … o` carries the run's console
    effect `OutStep` (`none` silent, `some o` prints `o`), and `RunFact` is the
    silent case. `SegFrom`, `RetExec` and `JalExec` carry the same conjunct.
    VSA's `segEval_sound` already proves it (`σ'.sailOutput = σ.sailOutput`);
    `jalExec_of_site` takes `StepConFrame` from the jal's observation. A run
    that does not own the console cannot print, so a missing putchar is an
    unprovable goal.
  - The lag kernel carries the console authority: `LagFoot.look`/`commit`
    see all three authorities (`mauths`). `LagFoot.ofRM` builds a silent
    run's instance from register/memory lookup and commit plus its output
    frame; `RunFact.lagFoot` and `SegFrom.lagFoot` use it.
  - `MachWP.runOut` (the `putc` rule), for either WP: a printing run
    (`RunFactO.lagFootPrint`) consumes `consoleOwn s` and returns
    `consoleOwn (s ++ o)`. VSA instance `Inst.wp_putcW` over
    `stepObs_tohost_putchar`, at `_write`'s store `0x8000005c` (`putcSite`).
  - `MachWP.haltConsole` with `HaltFact` (halt/console agreement), for either
    WP, from the `halt` field: at an exit step, `Φ (e, s)` with `s` the
    console cell. VSA instance `Inst.wp_exitW` over `stepOnce_tohost_G`, at
    `_exit`'s store `0x80000190` (`exitSite`). `Inst.vsa_adequacy_exit`
    turns the total WP into `Halts c out e ∧ φ (e, out)`; `vsa_adequacyP`
    does the same for the partial WP.
  - Adequacy allocates the cell at the initial output: `AdequacyHyp` and
    `AdequacyHypP` take the initial output `o` and hand the client
    `consoleOwn o`.
  - Change from the draft: the console rules are derived theorems, not
    `MachWP` fields. `putc` is `lagRun` at a printing footprint, and the halt
    rule is the `halt` field read against `mstateInterp`, which carries the
    console authority.
  - Change from the draft: the console does not own `tohost` bytes. In the
    Sail model a `tohost` store is MMIO: memory is unchanged and the HTIF
    registers decide the effect (`Vsa/Sim/Htif.lean`). What every console
    store needs is an idle mailbox (`htif_payload_writes = 0`); it is a global
    invariant, `VsaOk.htifIdle`, which segments frame and the putchar store
    re-establishes. The binary has no narrow `tohost` store.
  - Change from the draft: `γo` lives in `MachGS`, not `InterpGS`, because
    its authority is in the machine's state interpretation.
- **F3, calling conventions and stack (built: `CallAbort.lean`, `Stack.lean`,
  `Loop.lean`, `Interp/Need.lean`).**
  - `fnSpecAbort Wp entry P Q A` with `wp_callAbort` and the Löb twin
    `wp_callAbort_later`, both mode-generic. `fnSpecAbort_of_fnSpecW` lets a
    partial-mode proof call a helper proved only with `fnSpecW` (H1-H4);
    `fnSpecAbort_mono` is the consequence rule, and `fnSpecAbort_rebase`
    carries the abort-resource difference as an extra precondition.
  - `stackScratch s n` split and join (`blockOwn` arithmetic):
    `blockOwn_split`/`blockOwn_join` state the successor address and the
    lengths as EQUATIONS, so no call site rewrites under `blockOwn`;
    `stackScratch_narrow`/`_widen` and the carve/join pair
    `stackScratch_carve`/`stackScratch_join`, whose side condition
    `nc + f ≤ n` is `Vsa.Alloc.StackOK.child`'s.
  - The ItemZero need `evalNeed e d = e.stackNeed + (maxCallDepth - d) * perCallBudget + evalFrame`,
    verbatim from `EvalEntry.stackBudget` (`Vsa/Sim/InterpEntry.lean:630`).
  - xv6iris spells a budget as the sum, never a round number (`durable-notes.md`
    "A stack-budget premise is arithmetic").
  - Change from the draft: `evalNeed`/`execNeed` are both `stackBudget need d`,
    and the whole kit rests on TWO arithmetic lemmas — `stackBudget_child`
    (the Iris route's `StackOK.child`: a child's budget plus the parent's
    spilled frame fits the parent's, at the same depth) and `stackBudget_call`
    (a closure body at depth `d + 1`, inside one `perCallBudget`). Each arm of
    the two recursors is one line over them (`evalNeed_binary_left`,
    `execNeed_block`, `execNeed_callBody`, ...). The boundary bridge to S1 is
    `execNeed_of_stackFits` (arithmetic) and `stackScratch_boundary` (the Iris
    carve) over `ProgramStackFits`.
  - Change from the draft: the abort resource is `abortAt Core s need :=
    Core ∗ stackScratch s need`, generic in the site-independent `Core`
    (§4.2's `abortRes` is this at `abortCore`, the landing registers and SOME
    world). The skeleton wrote the `stackScratch` INSIDE the existential; it
    binds neither `s` nor `need`, so the two are equivalent, and hoisting it
    is what lets `abort_rebase` move the stack part on its own.
  - Change from the draft: the call step itself is ONE rule, not a per-site
    carve. `wp_callArmW` (ordinary) and `wp_callArmAbort` (partial) lend the
    callee a narrower part of the caller's owned region, keep the slack, and
    on the partial side re-base BOTH continuations: the return branch gets the
    caller's region and frame back, and the abort branch joins the very same
    frame and slack into the caller's `abortAt Core s n`. That the two
    branches use the same bytes is what the `∧` of `fnSpecAbort` buys, and it
    is the step every one of E1-E6's call sites takes.
  - STATEMENT CHANGE (F3): `abort_rebase` needs two more side conditions,
    `np ≤ sp_.toNat` and `nc ≤ sc.toNat`. `Nat` subtraction truncates, so
    without them `stackScratch s n` is `blockOwn 0 n` and the three intervals
    `[s_p - n_p, s_c - n_c)`, `[s_c - n_c, s_c)`, `[s_c, s_p)` do not join.
  - **The bounded-loop rule** (`Loop.lean`, §4.3): `MachWP.loop I K body fin n`
    by fuel induction, for either WP (xv6iris `ProofMemset.v:1-9` "bounded
    loop, not iLöb"; `ProofMemmove.v:350` `mm_loop`, induction on `rem`).
    Change from the draft: the body's two continuations — the next iteration's
    `I k` and the loop's inherited exit `K` — are an ADDITIVE pair, the same
    fix as §10.1. With a separating pair the body consumes `K` and the second
    iteration has none, which is exactly the bug §10.1 records for `while`.
    `MachWP.loopI` is the variant with no separate exit resource, and
    `MachWP.loopSeg` the one whose body is ONE reflected `RunFact` segment
    (an invariant opener/closer around the segment footprint, with a frame
    `F k` across it) — the shape `strlen`, `memcpy`, `strcmp` and the
    `args[32]` fill use (H3).

## 3. Representation predicates (work package R)

The ghost state is a new class `InterpGS GF` with two names, plus the
console from F2:

- `γf : ghost_map Nat Nat`: spec frame address to machine `Env*`.
- `γc : ghost_map Nat Nat`: spec closure address to machine `Closure*`.
- `γo`: the console, `MachGS.conName` (F2), used through `consoleOwn`.

`φf` and `φc` stop being arguments threaded through every lemma (the
`φf φc : Addr → Nat` pairs in `StoreRepr`). They become ghost maps whose
fragments are PERSISTENT: `frameAt fa e := fa ↪[γf]□ e`. A frame's `Env*`
never moves, since only its arrays are reallocated. A closure never moves or
changes.

| predicate | owns | kind | VSA counterpart |
|---|---|---|---|
| `strAt p s` | the bytes of `s` and its NUL at `p`, `↦ₘ□` | persistent | `CString` |
| `astE a e`, `astS a s`, `astSs a n ss` | every AST byte, `↦ₘ□` | persistent | `ExprRepr`/`StmtRepr`/`StmtArrayRepr` |
| `valOf v w0 w1 w2` | the meaning of three words: tag, payload, native address | persistent | `ValueRepr` |
| `valAt a v` | the 24 bytes at `a` (exclusive) with `valOf` | exclusive | `ValueWordRepr` |
| `closAt ca p` / `closOwn ca cd` | the closure's 16 bytes `↦ₘ□`, `fn_expr` AST, `env` link | persistent | `ClosureRepr` |
| `frameOwn fa f` | the `Env` struct, the names/vals arrays with spare capacity (whole heap blocks), each name `strAt`, each slot `valAt` | exclusive | `FrameRepr` |
| `storeRepr s B` | `γf`/`γc` auths over the allocated prefixes, every `frameOwn`, every `closOwn`, and `⌜StoreBodiesBound s perCallBudget⌝`. `B` lists the heap blocks it owns | exclusive | `StoreRepr` + `HeapOwned` + `StoreOwned` |
| `consoleOwn s` | the console cell | exclusive | `OutRepr` |
| `interpCtx d` | `Interp`: `call_depth = d` (exclusive), `globals` (persistent), `on_error` (persistent after `setjmp`), `err_msg` (exclusive) | mixed | `CallEntryI` fields |
| `heapRes ρ H` | `isHeapRoom L Room H k` if `ρ = counted k`; `isHeap L H` if `ρ = uncounted` | exclusive | `AllocLedger` |
| `world ρ st d` | `∃ H B, heapRes ρ H ∗ storeRepr st.store B ∗ consoleOwn st.out ∗ interpCtx d ∗ ⌜B ⊆ H⌝` | exclusive | the whole `EvalEntry` bundle |

Decisions and why:

- **Persistent immutable data** (MachCSL: text as `↦ₓ□`, `claude-notes/design/execution-model.md`).
  - C never writes a string, an AST node or a closure after building it, and
    never frees one. Persistence retires `ReprSurvival`, `store_survives`,
    `shared_agree`, `Reserved`/`BindingShared` and every "survives the child"
    obligation at once.
  - The persistent bytes sit in live heap blocks, which `heapFoot` excludes,
    so the allocator never needs them. xv6iris's warning ("a persistent
    points-to at a WRITABLE image byte is an inconsistent premise",
    `durable-notes.md`) does not bite, because nothing ever writes them.
- **One monolithic `storeRepr`.**
  - BigStep's frames are shared by closures and mutated through parent chains
    (`Store.set`). Every `eval_expr` call can reach any frame, so splitting
    frames across callers buys nothing.
  - `env_get`/`env_set`/`env_define` open ONE frame out of `storeRepr` with a
    single opener/closer (xv6iris `spec-modules.md`: "Simultaneous borrows of a
    sealed bundle need ONE opener").
- **Live blocks are whole chunk payloads** (the user's ruling). Strings carved
    out of a concat or stringify buffer sit inside their block. `B ⊆ H` makes
    `free`/`realloc` of a frame array find its block in `H`.
- **Heap regimes are MachCSL's `kalloc_env (Some n)` / `kalloc_env None`**
  (`KvmSpec.v:123`, paper §6.5). The counted regime (total mode) cannot fail and
  its credits come from the boundary's `capacity` (`DlHeap.InitialAllocatorAt`).
  The uncounted regime (partial mode) lets `malloc` return NULL, and `xmalloc`'s
  arm then takes the out-of-memory exit.

## 4. Function specs (§4.1 total, §4.2 partial)

All three recursive entries are MachCSL `Spec<F>`-shaped (`spec-modules.md`):
the statement lives in ONE `…_body` definition, and callers take it as a
hypothesis, never as a proof import.

Shared entry resources for `eval_expr` (entry `0x80003164`; ABI from
`EvalEntry`: `a0 = sret`, `a1 = env`, `a2 = e`; `in` is not an argument, gcc
dropped it):

```
evalPre ρ st d env e sret aE s :=
  a0 ↦ᵣ sret ∗ a1 ↦ᵣ aE ∗ a2 ↦ᵣ aX ∗ □ astE aX e ∗ □ frameAt env aE ∗
  sp ↦ᵣ s ∗ stackScratch s (evalNeed e d) ∗ savedOwn saved ∗ clobbered clobE ∗
  slot24 sret ∗ ⌜e.bodiesBound perCallBudget ∧ SpOK s⌝ ∗ world ρ st d ∗ □ codeImage
evalPost ρ st' d v sret s :=
  sp ↦ᵣ s ∗ stackScratch s (evalNeed e d) ∗ savedOwn saved ∗ clobbered clobE ∗
  valAt sret v ∗ world ρ st' d
```

`exec_stmt` (entry `0x80003fe0`; `a0 = in`, `a1 = s`, `a2 = env`, `a3 = ret`)
has the same shape. It carries `execNeed` and an exclusive `slot24 ret` that
holds `valAt ret v` exactly when the status is `.ret v` (`statusRet`). The
status comes back in `a0` as `StatusCode`.

### 4.1 Total (`term_sim`)

```lean
def evalSpecT_body (st d env e st' v n) (D : EvalECost st d env e st' v n) :=
  ∀ k sret aE s saved, fnSpecW twpW evalEntry
    (fun r => ⌜r.toNat % 4 = 0⌝ ∗ evalPre (.counted (k + n)) st d env e sret aE s saved)
    (fun _ => evalPost (.counted k) st' d v sret s saved)
```

- **Derivation-indexed.** The continuation receives exactly `D`'s outcome, and
  the credits drop by `D`'s cost.
- **No determinism lemma.** The right child of `binary` starts at `D`'s
  intermediate state, because the left child's continuation was indexed by `D`.
- **No error arms.** Each machine test resolves against `D`'s pure premise: the
  operand kinds, `binOpSem … = some v`, `get? = some`, arity, depth, and
  `truthy` for `assert`.
- `execSpecT_body` is the same shape over `ExecSCost`. The sequence loops,
  `EvalArgs` and `ForLoop` are block lemmas, not specs (§4.3).
- Proof: the mutual recursor over the nine cost companions, with motives
  `m_R … D := evalSpecT_body … D`. This is `TermSimAssembly`'s motive
  mechanism, and the 49 recursor rows become 49 Iris case lemmas.

### 4.2 Partial (`stuck_sim`)

```lean
def evalSpecP_body (st d env e) :=
  ∀ sret aE s saved, fnSpecAbort wpW evalEntry
    (fun r => ⌜r.toNat % 4 = 0⌝ ∗ evalPre .uncounted st d env e sret aE s saved)
    (fun _ => ∃ st' v, ⌜EvalE st d env e st' v⌝ ∗ evalPost .uncounted st' d v sret s saved)
    (abortRes s (evalNeed e d))
```

- **Outcome-quantified.** The return branch builds the derivation from the
  children's, rule by rule, as the machine runs.
- **Error arms go to the abort branch.** A runtime error calls `runtime_error`
  (its spec is H5: `snprintf` into `err_msg`, then `longjmp`), which lands at
  `interp_run`'s `setjmp` return with `a0 = 1`. An out-of-memory NULL goes
  `fprintf`, then `exit(1)`.
- **What the abort branch receives.** `abortRes s n := ∃ kind, landingRegs kind
  ∗ ∃ ρ st d, world ρ st d ∗ stackScratch s n`. It hands back the WHOLE owned
  stack below the site's `sp`.
- **Re-basing at every call.** Callers do not own the abort continuation for
  the child's region. At each call the caller builds the child's
  `abortRes s_c n_c -∗ W Φ` from its own `abortRes s_p n_p -∗ W Φ`, joining its
  frame bytes `[s_c, s_p)` back in (lemma `abort_rebase`, F3). Because of the
  `∧`, those same frame bytes also serve the return branch.
- **Proof: Löb over `evalSpecP_body ∧ execSpecP_body`.** Each recursive `jal`
  follows at least one step, which pays the `▷`. Divergence costs nothing: the
  partial WP allows it.

### 4.3 Sequences and loops are block lemmas

gcc inlined `call_value` and `eval_binary` into `eval_expr`, and there is no
`exec_seq` function. The statement sequence exists three times: the block arm,
the closure body inside the call arm, and `interp_run`'s loop. Following
xv6iris ("A block gcc emitted twice is one lemma, parameterized by its PCs as
literals", `durable-notes.md` "Seams and block lemmas"), it is ONE lemma
`seqLoop (site : SeqSite)`. `SeqSite` records the loop-head PC, where the index
and count live, the `jal exec_stmt` site and the exits. Instantiations:
`blockSite`, `closureSite`, `interpSite`. The lemma is mode-generic.

- Total mode: induction on the `ExecSeqCost` derivation.
- Partial mode: fuel induction on the remaining count, which is bounded by
  `count`. Each statement uses the Löb hypothesis for `exec_stmt`.

The fuel-induction rule itself is F3's `MachWP.loop` (`VsaIris/Loop.lean`),
with `MachWP.loopSeg` for a body that is one reflected `RunFact` segment. Its
body takes the next iteration's invariant and the loop's inherited exit as an
ADDITIVE pair, which is what keeps an abort continuation alive across
iterations (§10.1).

`EvalArgs` (the `args[32]` fill), `while`, and `for` are loop lemmas of the same
kind.

- Total mode: induction on the derivation.
- Partial mode: `while` and `for` loop forever when the program does, so they
  need Löb, not fuel. The loop lemma takes the Löb hypothesis for its own head
  as a premise, `▷ loopSpec`, and the recursive entry discharges it inside the
  one global Löb.

### 4.4 `interp_run` (entry `0x800043ec`)

`interpRunSpecT p D` and `interpRunSpecP p` are ordinary `fnSpecW` specs from
the boundary state. The loop is `seqLoop interpSite`. The partial abort branch
is closed INSIDE `interp_run`'s own proof:

- `setjmp` returns 1, `interp_run` returns 1, `run_source` calls `fprintf` and
  returns 70, then `main`, then `exit`.
- A top-level `ret`/`brk`/`cont` status returns 1, giving exit 70.
- Out of memory gives `exit(1)`.

So the external partial spec's postcondition is `∃ e, ⌜e ≠ 0⌝`-style unless
the program completed normally, and then its continuation receives `ExecSeq
initSt 0 0 p st' .normal`, which is `BigStep p st'.out`.

## 5. Assembly (work package A)

### 5.1 The boundary (A0)

`world_of_boundary : InterpRunReady c a n → ProgramRepr c.σ.mem a n p → ⊢ |==> …`
allocates the ghost state from the initial memory:

- the γf/γc maps at `initSt`'s frame 0;
- the console at `output c.σ`;
- `isHeapRoom … (capacity p)` for total, or `isHeap` for partial, from
  `InitialOwned.allocator` + `vsaRoom`;
- `□ codeImage`, `□ astSs a n p`, `interpCtx 0`, and the top stack region.

It reuses `blockHeapAt_of_heapAt` and `HeapShape`. This is also the place for
xv6iris's vacuity check (`durable-notes.md` "Vacuity"): prove the boundary
bundle is satisfiable at the concrete control program (the `ControlWitness`
image), not only that it typechecks.

### 5.1b The heap credits: Room ↔ Cost (S1, landed)

`VsaIris/Vsa/CostRoom.lean`. The counted regime's index is COST BYTES, so
`heapRes (.counted k) := isHeapRoom vsaLayout costRoom H k`. It is NOT
`vsaRoom`: VSA's `AllocationReserve` is unsatisfiable after `malloc(24)`
(`split24_vsa_reserve_false`), and it counts requests of a uniform `maxReq`,
not bytes.

- **`costRoom img H k`** holds when `av->top + 2k + extendSlack ≤ heapEnd`.
  - It reads only the top word, an allocator global (`roomLocal_cost`), and is
    monotone (`isHeapRoom_cost_mono`).
  - It has no live-extent clause: freshness is `Shape`'s job.
- **Charges cover chunks (2n + slack).** Each C allocation site's request `n`
  sits under its modeled charge `c`, with `16 ≤ c` (`Covers`: `covers_envNew`,
  `covers_closure`, `covers_nameCopy`, `covers_stringify`,
  `covers_concatBuffer`, and `arrayRealloc_split` for the two array
  `realloc`s). Hence `physSize n ≤ 2c` (`physSize_le_two_charge`).
- **Per allocation.** `CostTop.spend`/`.split`: advancing top by at most `2c`
  turns `c + k` credit bytes into `k`. A bin hit, or a free merging into top,
  only helps.
- **Iris malloc at charge `c`.** `mallocCostSpec` is `mallocRoomSpec` at
  `costRoomAt c k` (unit credit = `c` bytes). `isHeapRoom_costAt_one`/`_zero`
  rewrite it to `isHeapRoom costRoom H (c + k) → isHeapRoom costRoom _ k`.
  Its first-order obligation is `MallocCostRun` (H4, the `alloc.mallocRoomRun`
  row of HOLES.md).
- **Boundary (A0).** `costRoom_of_bigStep`: `BigStep` gives a costed
  derivation of cost `n` (`BigStep.cost`), and `InitialAllocatorAt.capacity`
  gives `costRoom` at `n` (`costReserve_of_initial`). Non-vacuous:
  `Control.costReserve` has 2^20 credit bytes at the control heap.
- **Cost existence/soundness** for the recursor: `Vsa/While/CostExists.lean`
  (`EvalECost.exists` … `ExecSeqCost.exists`, and `EvalECost.sound` …, which
  give the `EvalE`-level invariants to a case lemma holding only `D`).

### 5.2 `term_sim`

```lean
theorem term_sim_iris (h : IrisHoles) :
    ∀ p c out, Loaded interpRunLayout' p c → BigStep p out → Halts c out 0
```

1. `BigStep` gives `ExecSeq initSt 0 0 p st' .normal`.
2. `ExecSeqCost.exists` gives the cost `n`. It is proved in S1 if absent.
3. `interpRunSpecT` with `Φ := fun v => ⌜v = (0, st'.out)⌝`.
4. After `interp_run` returns 0: `main`'s epilogue, then `exit(0)`, then the
   halt rule. The console gives `out = st'.out`.
5. `vsa_adequacy` (exists).

### 5.3 `stuck_sim`

```lean
theorem stuck_sim_iris (h : IrisHoles) :
    ∀ p c, Loaded interpRunLayout' p c → (¬ ∃ out, BigStep p out) →
      Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0
```

1. Use `interpRunSpecP` with `Φ := fun v => ⌜v.1 ≠ 0⌝`.
2. Normal completion hands a `BigStep` derivation, which contradicts the
   hypothesis.
3. Every abort and every non-normal top status ends in `exit(70)` or `exit(1)`.
4. Partial adequacy (F1) finishes it.
5. Where a total-only proof is reused (the `snprintf` `%lld` path inside
   `value_print`, if it stays total), `twp_wp` bridges.

### 5.4 The final theorem

```lean
theorem interpSim_iris (h : IrisHoles) : InterpSim interpRunLayout' :=
  ⟨term_sim_iris h, stuck_sim_iris h⟩

theorem endToEnd_refinement_iris (h : IrisHoles) :
    ∀ p c, Loaded interpRunLayout' p c →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, BigStep p out) :=
  Vsa.Refine.refinement (interpSim_iris h)
```

`interpRunLayout'` is `interpRunLayout`: Q1's stack-admissibility field landed
in `InterpRunReadyFacts` (see "STATEMENT CHANGE" at the top).

## 6. The exponentiating layer on Iris (work package G)

The producers do not change. `#derive_case`, `segEval_sound`, `gen_fn.py`,
`gen_sites.py`, `gen_fixed_image.py` and the decode tables keep emitting exec
facts. `seg_runFact` and `segFrom_of_runFact` turn them into `RunFact`s.
`wp_seg` consumes a segment in one application, with its named register pins,
written bytes and read-only bytes.

Two changes:

1. **The row generators emit Iris case lemmas instead of Triples.**
   `gen_m4_term_row.py`, `gen_exec_row.py`, `gen_bin_dispatch_row.py`,
   `gen_allocator_cases.py`, `gen_m5_error_routing.py` and the `*_sites.tsv`
   tables are retargeted. ONE row table (`arms.tsv`) gives each machine arm:
   - its entry PC and dispatch path;
   - its segments;
   - its child calls (which AST field, which slot, which spec);
   - its helper calls;
   - its semantic rule (total), or its rule plus error arms (partial).

   From it the generator writes `Case/<Arm>T.lean` and `Case/<Arm>P.lean`.
   Hand edits go in the table, never in the output (xv6iris
   `code-organization.md`: "no hand-written duplicate beside a generated
   layer").
2. **One file set per function, xv6iris-style** (`spec-modules.md`):
   `Interp/Spec<F>.lean` (the statement only, no code import),
   `Interp/Proof<F>.lean` (takes callee specs as hypotheses) and one assembly
   file. A proof never imports another proof, so the build parallelises.

### Worked case: `binary .add` on two ints, total mode

C path: `eval_expr` then `EX_BINARY` then (inlined `eval_binary`) left child,
right child, operator jump table (`0x80019f58`), the `T_PLUS` int/int arm,
`value_int(a+b)`, epilogue.

```lean
theorem case_binary_add_intT (hl : evalSpecT_body st d env l st₁ (.int a) nₗ Dₗ)
    (hr : evalSpecT_body st₁ d env r st₂ (.int b) nᵣ Dᵣ) :
    evalSpecT_body st d env (.binary .add l r) st₂ (.int (wrap64 (a + b))) (nₗ + nᵣ)
      (.binary … Dₗ Dᵣ rfl) := by
  intro k sret aE s saved; iintro !> %r %Φ Hpc Hra Hpre Hk
  -- (1) prologue + kind dispatch to the binary arm: one reflected segment
  iapply (Wp := twpW) wp_seg evalPrologueBinSeg …;  iframe …;  iintro Hseg
  -- (2) left child into the frame's L slot; everything else framed by the wand
  iapply wp_callW (hl (k + nᵣ) slotL aE (s - 1088) savedL);  iframe …
  iintro Hpc Hra ⟨Hsp, Hstk, Hsv, Hclob, HvL, Hworld⟩
  -- (3) stage the right child: one segment; (4) right child
  iapply wp_seg stageRightSeg …;  iapply wp_callW (hr k slotR aE (s - 1088) savedR);  …
  -- (5) operator dispatch + int/int add + store into sret: one segment whose
  --     branch conditions are pinned by `valOf (.int a)` / `valOf (.int b)`
  iapply wp_seg addIntTailSeg (tagL := 2) (tagR := 2) …
  -- (6) epilogue (one segment) and the continuation
  iapply wp_seg evalEpilogueSeg …;  iapply Hk …
```

- It uses five segment applications and two child calls. The frame rule
  handles the frame bytes, the other slot, the caller's `ra`/`s`-regs and the
  whole `world`. There is no transport, survival or widening lemma.
- The partial twin differs in two places. (2) and (4) use `wp_callAbort` with a
  re-based abort continuation. At (5) the kind test is read off the ACTUAL
  values: int/int continues, str goes to the concat arm (a different row), and
  anything else calls `runtime_error` through the H5 spec.

## 7. What is reused, what is retired

| kept (fact producers) | retired (framing and plumbing) |
|---|---|
| Decode tables, `#derive_case`, `segEval_sound`, `bblocks_sound*`, `gen_fn.py` + `FnSummary`, `StepObs`/`JalStep` (via `jalExec_of_site`) | `WidenMeta`/`LeafWiden`/`ExecRecWiden`/`EvalRecWiden`/`blockD_v_phic` |
| `Vsa/While/*` (semantics, `Cost`, `StackNeed`, `Derive`, `Validation`) | `ReprSurvival`, `store_survives`, `Reserved`/`BindingShared`, `shared_agree*` |
| `MemRepr` (the persistent lift `astE_of_exprRepr` reads it) and `RuntimeRepr` (as the spec of `valOf`/`frameOwn`) | `AllocLedger`, `OwnedOff`/`EntryOff`, `MallocContract`, `privFoot`, the per-entry ledger fields (R14) |
| The helper *segments*: `StrlenSegments`, the memcpy word loop, the `value_equal` jump table, env_* scans (block lemmas re-wrapped as `Wp`-generic) | `EvalEntry`/`ExecEntry`/`CallEntryI` field towers, `EvalReturnIH`/`ReturnRepr` index machinery, the IH clause tower (`IHClause_*`) |
| `LayoutInstance` geometry, `ImageDischarge`, `InitialOwned` (boundary inputs to A0) | `TermResidualsBase` (63 fields), `DivWork`, `ErrWork`, `RemainingWork`: replaced by `IrisHoles` |
| `Refinement.lean` (unchanged) | `SeparationLogic*.lean` (VSA's own, subsumed) |

The discipline gate (`check_discipline.py`) gets rules for the new layer:
- no `sorry` in `VsaIris/Interp`;
- `Spec*` files import no `Proof*` or `Case*` file;
- generated `Case/*` files are not hand-edited (hash check, as the stage-a3
  drift gate does now).

## 8. Case inventory and estimates

Estimates are Lean lines. The basis is the env_new pilot (`EnvNewPilot.lean`,
443 lines against VSA's 2,747 for the same cone) and the generated
`Case/*` shape above.

| family | total rules (T) | partial arms incl. errors (P) | lines (T+P) |
|---|---|---|---|
| leaves: int, str, bool, null, fn | 5 | 5 | 0.8k |
| var (hit / miss), assign (ok / unbound) | 2 | 4 | 0.9k |
| binary: add int, add concat ×2 kinds, sub, mul, div, mod, eq, ne, 4 cmp × {int, str}, type/zero errors | 16 | 22 | 4.5k |
| logical: or ×2, and ×2; unary: neg, not, neg type error | 6 | 7 | 1.4k |
| call: closure (ok), natives print / println / assert-ok; arity, depth, not-callable, too-many-args, assert-fail, brk/cont-escape errors | 4 | 10 | 3.5k |
| exec: expr, varInit, varNull, block, if ×3, while ×4, for (+ForLoop 4, ForCond 2, ExecInit 2, ExecStep 2), ret ×2, brk, cont | 25 | 16 | 5.0k |
| loop lemmas: `seqLoop` (3 sites), `EvalArgs`, while, for | shared | shared | 1.5k |
| helpers (H1–H5), mode-generic | | | 7–9k |
| foundations F1–F3, R, A0, A | | | 5–6k |
| **total** | | | **≈ 30k** |

The generator (G) carries about 60% of the case lines. Hand work concentrates
in F, R, the helpers, and the three loop lemmas.

## 9. Fan-out plan

```
F1 partial WP ──┐
F2 console ─────┼─> F3 fnSpecW/abort/stack ─> R repr ─┬─> H1..H5 helpers ─┐
S1 cost/admiss. ┘                                      └─> G generator ────┼─> E cases (T,P) ─> A assembly
                                                          A0 boundary ─────┘
```

| package | content | depends on | parallel with |
|---|---|---|---|
| **F1** | `mWP`, `MachWP`, `twpW`/`wpW`, `run_later`, partial adequacy at the VSA instance | none | F2, S1 |
| **F2** | console ghost, `out` projection, `putc` rule, halt/console agreement | none | F1, S1 |
| **S1** | `ExecSeqCost.exists`; stack-admissibility predicate (Q1); `Room` ↔ `Cost` bridge (2n + slack against `vsaRoom` credits) | none | F1, F2 |
| **F3** (landed) | `fnSpecAbort`, `wp_callAbort`, `wp_callAbort_later`, `abort_rebase`, `blockOwn`/`stackScratch` carve-join, `evalNeed`/`execNeed` arithmetic and the `ProgramStackFits` bridge, `MachWP.loop`/`loopSeg` | F1 | R (after F1) |
| **R** | `InterpGS`, all §3 predicates, openers (one frame out of `storeRepr`), `astE_of_exprRepr`, the two-owner sanity lemmas | F1, F2 | F3 |
| **A0** | `world_of_boundary`, vacuity check at the control program | R, S1 | H* |
| **H1** | `env_new`, `env_define` (append / grow / hit), `env_get`, `env_set` over `storeRepr` openers | R | H2–H5 |
| **H2** | `value_truthy`, `value_equal`, `value_print`, `stringify`, natives `print`/`println`/`assert` | R, H3 | H1, H4, H5 |
| **H3** | `strlen` (pilot in flight), `memcpy`, `strcmp`, `snprintf` `%lld` | F1 | all |
| **H4** | `_malloc_r`/`_free_r`/`_realloc_r` runs (discharges `IrisHoles.alloc`), regime lemmas, the `xmalloc` site lemma | F1 (iris-heap work continues here) | all |
| **H5** | `runtime_error` + `longjmp`/`setjmp` (landing), `exit`, the abort landing to exit(70) path, the out-of-memory arm | F3, R | H1–H4 |
| **G** | `arms.tsv`, retargeted generators, `Case/*T`/`*P` emitters, drift gate | F3, R (interfaces only) | H* |
| **E1–E6** | the six case families of §8, each T and P | G, H* | each other |
| **A** | recursor assembly (T), Löb assembly (P), `interp_run`, `term_sim_iris`, `stuck_sim_iris`, final theorem, axiom audit | E*, A0 | none |

Parallel width: F1, F2 and S1 together; then R and F3; then H1–H5 and G (six
lanes); then E1–E6 (six lanes).

**Named holes** at the end, in `structure IrisHoles`, each checked satisfiable
(§10):
- `alloc`: `MallocRoomRun`, `MallocLocalRun`, `FreeLocalRun`, `ReallocLocalRun`,
  unless H4 discharges them;
- `newlib`: safety specs of `snprintf` (`%s`/`%d` error messages) and `fprintf`
  on the error/out-of-memory paths. These are only needed for partial mode's
  "never stuck". The `%lld` success path is proved (VSA M3).

## 10. Adversarial review (paper §9.3): what broke, and the fix

1. **Linear abort continuation across a loop.** The first draft put `abortK` in
   the precondition as a plain wand, and the return branch then lost it: the
   while loop's second iteration had no abort. Fix: an additive pair `(return ∧
   abort)`. Both branches are proved from one context, so the loop's return
   branch still holds the inherited `abortK`.
2. **Abort loses the callers' stack frames.** An error at depth k handed the
   top only its own scratch, while the frames between it and `interp_run` sat
   in the callers' return closures, and `fprintf` after the landing needs that
   stack. Fix: `abortRes s n` carries the stack below `s`, and every call
   re-bases the child's abort continuation, joining the caller's frame
   (`abort_rebase`).
3. **Total mode and determinism.** An outcome-quantified total spec would need
   `EvalE` determinism to start the right child at the left child's actual
   state. Fix: derivation-indexed total specs over the recursor. The motives
   supply the children at exactly `D`'s states, and no determinism lemma is
   needed.
4. **The stack budget at the boundary does not bound the program (possible
   falsity of `InterpSim` as stated).**
   - `InterpRunPhysicalFacts.stack_ok` is the constant `176 + 1088`
     (`LayoutInstance.lean:214`), and nothing at the boundary bounds
     `p.stackNeed` or `bodiesBound`.
   - The AST comes from `Loaded`, not from the parser, so any depth is
     admissible.
   - An 8,000-deep `-(-(…))` overflows the 8 MiB stack into the heap directly
     below it (`heapEnd = stack lo = 0x87800000`). After that, nothing
     constrains the machine, and both `term_sim` and `stuck_sim` are
     unprovable.
   - Fix (approved as Q1, landed by S1): `InterpRunReadyFacts.stack_admissible`
     (`ProgramStackFits`, see "STATEMENT CHANGE" at the top), beside
     `capacity`.
5. **The out-of-memory path in partial mode.** The capacity bound only covers
   terminating derivations, so a divergent program can exhaust the heap. That
   is correct behaviour, `exit(1) ≠ 0`, but only if the uncounted regime's
   NULL arm is in the spec. Fix: `heapRes .uncounted` is `isHeap` with
   `mallocSpec`, which has the NULL arm, and the site lemma routes NULL to the
   out-of-memory abort.
6. **Satisfiability of the persistent string bytes.** `stringify` and concat
   write their buffer AFTER `malloc`, so the bytes are exclusive while they
   are written and only then discarded to `↦ₘ□`. The site lemmas must state
   the discard AFTER the copy, never at allocation. A premise `strAt p s`
   before the write is refutable. This is recorded as a rule for H2.
7. **Two owners of the frame arrays.** `storeRepr` owns the array blocks and
   `isHeap` must not also own them: `B ⊆ H` and `heapFoot` excludes `H`.
   Scratch check for R: `storeRepr s B ∗ heapRes ρ H ∗ ⌜B ⊆ H⌝ ⊬ False`,
   proved by exhibiting the boundary world (xv6iris's "two owners of one
   address space" diagnostic, `durable-notes.md`).
8. **A 32-bit `argc`/`paramc` read as a 64-bit word** (xv6iris "A 32-bit
   argument's register premise is the ABI's word"): the arity and too-many-args
   tests are `lw` plus signed compare. The spec pins `sign_extend 64
   (argc : BitVec 32)`. `ExprRepr.call`'s `argc < 2^31` already matches this.
9. **Console versus `tohost` writes inside helpers.** A helper segment that
   does not own `tohost` provably cannot print (F2), so a missing putchar in a
   print path shows up as an unprovable goal, not as a silent output mismatch.

## 11. Open questions for the user

- **Q1 (hard to change later): stack admissibility at the boundary** (§10.4).
  Approve a `stack_admissible` field in `InterpRunReady`, shaped like
  `capacity`? Without it, `InterpSim interpRunLayout` looks false for very deep
  ASTs.
- **Q2: the top-level hypothesis.** `RemainingWork` (63 + Div + Err fields) is
  replaced by `IrisHoles` (the allocator runs plus the newlib safety specs).
  `Refinement.lean` and `InterpSim` are unchanged, and the new theorem is
  `endToEnd_refinement_iris`. Keep `endToEnd_refinement`'s name by redefining
  it over `IrisHoles`, or keep both during migration?
- **Q3: two WPs.** Total derivation-indexed plus partial Löb, with shared
  blocks, is recommended. The alternative is a single partial WP with step
  credits for termination: it avoids the duplicate case glue but needs exact
  step budgets.
- **Q4: newlib safety holes.** `snprintf`/`fprintf` on the error paths are
  needed only so that partial mode is "never stuck". Leave them as named
  holes, or schedule proofs? (`vfprintf` is large.)
