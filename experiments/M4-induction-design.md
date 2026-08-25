# M4 design — the Layer-4 simulation induction (`term_sim`)

> Block-reflection tooling for collapsing the per-arm `StepObs` batteries — the
> reusable abstraction stack, the migration cookbook, and the next-abstraction
> roadmap (program logic / reflected disassembly / discharge tactics) — lives in
> [block-reflection-plan.md](block-reflection-plan.md).

Written at the close of the M3 function-spec campaign (2026-08-23), while
the full pattern context is at hand. This is the kickoff brief for the M4
work: PLAN-InterpSim.md Layer 4, the mutual induction over the eight
big-step relations composing the Layer-3 specs into
`term_sim : ∀ p c out, Loaded L p c → BigStep p out → Halts c out 0`.

## What exists (the inputs)

- **Layer-3 specs, all kernel-clean**: `memcpy_spec`, `strlen_full_spec`,
  `strcmp_full_spec`, `strcpy_full_spec`, `muldi3_spec`, `udivdi3_spec`,
  `umoddi3_spec`, `moddi3_spec`, `divdi3_spec`, `value_{null,bool,int,
  str}_spec`, `value_truthy_spec`, `value_equal_spec_full`, `env_new_spec`
  (+ env_define/env_get/env_set and snprintf `%lld` in the coordinated
  session's tier), `setjmp`/`longjmp` (`JmpSpec`), HTIF store lemmas.
- **The composition discipline**: `experiments/M3-pilot-design.md` with
  both AMENDMENT sections — ghost frames, fresh-ghost crossovers,
  stack-window posts, exit-bundle fullness, literal-PC loop exits,
  jump-table pins, mappedness side conditions.
- **Layer-2 relations**: `ValueRepr`/`ClosureRepr`/`FrameRepr`/`StoreRepr`
  (`Vsa/RuntimeRepr.lean`), `OutRepr`, `MallocContract` (`Vsa/Alloc.lean`).
- **Layer-1**: `Vsa.Logic.Triple`/`TripleN` with `loop`/`seq`/`cases`.

## The induction statement (per the plan)

The eight relations (`EvalE`, `EvalArgs`, `Call`, `ExecS`, `ExecInit`,
`ForLoop`, `ForCond`, `ExecStep`, `ExecSeq` — ~40 constructors total,
`Vsa/While/Semantics.lean:215-438`) get one *simulation lemma family*,
stated per relation and proved by the auto-generated mutual recursor
(`@EvalE.rec` and siblings — the plan's "parameterized by the big-step
derivation": no separate well-founded argument on code).

Statement shape per relation (e.g. `EvalE st a e st' v`):

```
eval_sim : EvalE st a e st' v →
  Triple (EvalEntry g st a e sp r m …) (EvalExit g' st' v sp r …)
```

where `EvalEntry` bundles, at `eval_expr`'s machine entry:
- PC = eval_expr entry, ABI args (a0 = interp*, a1 = env machine addr
  `φf a`, a2 = Expr* node with `ExprRepr` of `e`), ra = r, sp with
  `StackOK` headroom for the recursion depth,
- `StoreRepr m N A φf φc st.store`, `OutRepr σ st`, code-region predicates
  for every reachable function (bundle once as `InterpCodeLoaded`),
- `MallocContract`'s `AInv exts` + the arena-accounting that `Loaded`
  carries, GoodState, tick < 2, ghost frame.

and `EvalExit`: PC = r, a0/a1 carrying the result `Value` per the ABI
(24-byte sret buffer — check eval_expr's actual convention from the
disasm), `StoreRepr` re-established for `st'.store` (with EXTENDED φf/φc
— existentially quantified extensions agreeing on the old domain),
`OutRepr` for `st'`, callee-saved/sp restored (blanket frame), the stack
window below entry-sp released.

## Key design decisions to make early

1. **The φ-extension discipline.** Every allocation extends `φf`/`φc`.
   The exit predicate quantifies `∃ φf' ⊇ φf` (agreeing on the allocated
   prefix). Define the extension order once (`PhiExtends`) with
   composition lemmas — every IH application chains two extensions.
2. **RESOLVED FINDING (2026-08-23): the resource-envelope gap.**
   Verified: `interp.c` has `MAX_CALL_DEPTH 1000` (line 7; exceeded ⇒
   `runtime_error` ⇒ exit 70), and the spec's `Call.closure`
   (Semantics.lean:290) has NO depth guard — likewise the arena is finite
   while the spec allocates unboundedly. Consequence: for a terminating
   program whose evaluation exceeds depth 1000 (or exhausts the arena),
   `BigStep p out` is derivable but the machine exits 70 — `term_sim` as
   stated is FALSE for such programs under any concrete layout. The only
   place resource bounds can enter without touching the proven
   `InterpSim`/`refinement` statements is the `Layout` instantiation:
   `atInterpRun` (Layer 6, "arena and output invariants" per the plan
   sketch) must also bound the represented program's call-tree depth
   (< 1000) and allocation budget (≤ arena). This is a scope decision on
   the final theorem — surfaced to the user before M4 case work that
   depends on it. The `EvalEntry` predicates should carry
   `depthLeft`/`arenaLeft` parameters from day one either way.

3. **Stack accounting.** The interpreter recurses (`call_depth` cap 1000);
   each frame costs a fixed size (read off the prologues). `EvalEntry`'s
   headroom is a function of the remaining depth; the depth-cap error
   path exits to `runtime_error` (Layer 5's territory — `term_sim` only
   handles derivations that DON'T error, so P asserts depth-sufficiency
   derived from the derivation's height... NO: the spec semantics has no
   depth cap, so a deep derivation CAN overflow in the machine. But
   `term_sim` claims Halts for every `BigStep` — reconcile: the plan
   (Layer 5 note) says resource exhaustion lands in the `stuck_sim`
   disjunct; for `term_sim` the `Loaded`/`Layout` must build in enough
   stack for the actual program, OR `BigStep p out` derivations that
   overflow the real stack contradict `term_sim` as stated. READ the
   plan's scope note again and the depth-cap C code: the interpreter
   checks `call_depth >= 1000` and errors — so a `BigStep` derivation
   with call depth ≥ 1000 has NO clean machine halt, and `term_sim` as
   stated would be FALSE for such programs... unless the spec semantics
   also caps (check `Call`'s constructors for a depth guard — the memory
   notes say "depth cap (1000)" is mirrored in the ERROR judgment, Layer
   5). RESOLVE THIS FIRST: either the spec's `Call` carries the depth cap
   (then derivations are bounded and stack headroom is derivable), or
   `Loaded` must assume the program's derivation height < 1000. This is
   a statement-level decision that gates everything.
3. **Arena accounting.** Same shape for the heap: `term_sim` needs malloc
   to never return NULL on the derivation's allocations. The
   `MallocContract` NULL arm must be excluded by a P-side arena-budget
   (env_new's "arena-non-exhaustion" P-constraint pattern, already
   established) — the budget is a function of the derivation size.
   Thread an `AllocBudget derivation ≤ remaining arena` hypothesis.
4. **Case granularity.** ~40 constructors × (spec plumbing per case).
   Each case = one C-code segment walk (compiled eval_expr/exec_stmt
   dispatch arm) composed from: the dispatch (switch → jump table, the
   value_equal `JumpTable` machinery generalizes), the sub-calls (IHs +
   the Layer-3 function specs), and re-establishment of the Layer-2
   relations. Build ONE worked case first (e.g. `EvalE.int` — literal:
   dispatch arm + value_int + sret copy) as the M4 pilot before fanning
   out, exactly like M1's step_addi and M3's muldi3 gates.

## Suggested execution order

1. Resolve design decision 2 (depth cap) by reading `Call`/interp.c —
   it changes `term_sim`'s hypotheses.
2. `Vsa/Sim/InterpEntry.lean`: the `EvalEntry`/`ExecEntry`/`CallEntry`/
   exit predicate definitions + `PhiExtends` + `InterpCodeLoaded` bundle.
3. eval_expr's dispatch skeleton (sites for the switch prologue + jump
   table pins) — shared by ~20 cases.
4. The `EvalE.int` pilot case end-to-end (gate).
5. Fan out constructor cases in dependency order (leaves first: literals,
   var lookup (env_get), assignments (env_set), binary ops (eval_binary +
   soft-arith specs), then statements, then Call/closures last).
6. `interp_run`'s statement loop (`ExecSeq` consumption) + `main`'s exit
   threading into the HTIF exit store → `term_sim` assembly.

## Practical notes for the M4 agents

- eval_expr is 927 instructions — its per-case segments are the units,
  never the whole function. Generate `Vsa/Sim/Code/Eval_expr.lean` once
  (gen_code_lemmas.py handles chunking; verify build time at this size
  before committing to the format — may need larger chunks or splitting
  by address range).
- The mutual recursor: `EvalE.rec` etc. exist auto-generated; motives are
  the per-relation Triple statements. Check binder order with `#check
  @Vsa.While.EvalE.rec` FIRST — mutual recursors' motive plumbing is
  error-prone; a tiny toy instantiation before the real statement.
- The coordinated session (c1826b17) owns env_*/snprintf/stringify/jmp —
  their specs' exact P/Q forms are inputs here; read their final
  statements before fixing the entry predicates.
