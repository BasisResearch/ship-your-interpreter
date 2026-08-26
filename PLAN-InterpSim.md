# Plan: proving `InterpSim` — no sorries, no `native_decide`

> **Validated by experiments** (`experiments/RESULTS.md`), with one
> amendment: the Ext-map state containers are not definitionally
> reducible, so Layer 0 works exclusively through `simp` lemma interfaces
> and staged simp sets — never `rfl` on stateful goals. The symbolic
> decode lemma (half of the M1 spike) is already proved in
> `experiments/E1i_decode_staged.lean` (~3.5 s, kernel-only).

Goal: discharge, in Lean, against the Sail RV64D model and the fixed binary
`while-riscv-htif.elf`:

```lean
term_sim  : ∀ p c out, Loaded L p c → BigStep p out → Machine.Halts c out 0
stuck_sim : ∀ p c,     Loaded L p c → (¬∃ out, BigStep p out) →
            Machine.Diverges c ∨ ∃ out e, Machine.Halts c out e ∧ e ≠ 0
```

for a concrete `Layout L` read off the binary. All reasoning is by
induction over the inductive relations, with side conditions closed by
kernel reduction (`simp`, `decide`, `rfl`, `omega`). Forbidden: `sorry`,
`axiom`, `native_decide`, and `bv_decide` (its LRAT reflection goes through
`ofReduceBool`, i.e. native evaluation — same trust step as
`native_decide`).

Scope note: `Loaded` places the machine at `interp_run` entry with the AST
in memory, so the lexer/parser and libc startup are *outside* this proof.
The code that must be verified is the interpreter core, its runtime
(`env_*`, `value_*`, string helpers), the libc routines they call
(`malloc`, `strcmp`, `strlen`, `strcpy`, `memcpy`, `snprintf` for `%lld`,
`setjmp`/`longjmp`), libgcc soft mul/div (rv64i has no M extension), and
the HTIF output path. Measured from `objdump -d`, on the order of 8–12k
instructions reachable from `interp_run`.

---

## Layer 0 — symbolic execution infrastructure over the Sail model

The make-or-break layer. Everything above it consumes one product: for each
instruction class used by the binary, a **step-characterization lemma**

```lean
theorem step_addi
    (hG : GoodState σ) (hpc : pcOf σ = pc)
    (hfetch : fetch32 σ.mem pc = some w) (hdec : isADDI w rd rs imm) :
    Machine.Step ⟨σ, i, u⟩ ⟨writeGPR (setPC σ (pc+4)) rd (gpr σ rs + sext imm),
                             nextTick i, u+1⟩
    ∧ GoodState … -- state-update form is explicit; GoodState preserved
```

proved by driving `simp` through `stepOnce`/`try_step`/fetch/decode/execute
on a *symbolic* state. Required pieces:

1. **`GoodState` invariant.** Pins every piece of control state the model
   consults on the hot path, at the values that hold for this bare-metal
   binary throughout: M-mode (`cur_privilege = Machine`), address
   translation off, interrupts globally disabled (`mstatus.MIE = 0`,
   `mie = 0` — so `dispatchInterrupt = none` regardless of `mip`; this
   also neutralizes the `tick_clock`/`mtimecmp` hazard, since
   `initializeRegisters` leaves `mtimecmp` undefined and `tick_clock`
   may set `mip.MTI`), `hart_state = HART_ACTIVE`, `htif_done = false`,
   `misa`/`mstatus` at their reset values, PMP entries granting M-mode
   full access. One-time lemmas:
   - `init_good`: after `setupElf`/`init_model`, `GoodState` holds —
     proved by unfolding the reset semantics symbolically (heavy, once).
   - `pmp_allows`: `pmpCheck` in M-mode with the reset PMP configuration
     always allows — kills the 64-entry PMP walk in every memory access.
   - `dispatch_none`: interrupt dispatch returns `none` under `GoodState`.
2. **Memory and register normal forms.** Simp sets for
   `Std.ExtHashMap`/`ExtDHashMap` read-over-write, so fetches and loads
   consume hypotheses of the form `σ.mem[pc+k]? = some b` and register
   reads resolve through pending writes. State updates are kept in a
   canonical `writeReg …/writeMem …` spine (this is the Islaris/Sail-tools
   playbook, done with simp sets instead of SMT).
3. **A `try_step` skeleton lemma.** Factor the common prelude once —
   under `GoodState`: no interrupt, fetch succeeds with `w`, decode gives
   `ast` — so each instruction lemma only reasons about its own execute
   clause. Without this, every lemma re-pays the full model unfolding.
4. **Decode table.** `encdec_backwards w = ast` for each of the concrete
   32-bit words appearing in the binary — pure bitvector matching, closed
   by `decide`/`rfl` (kernel; no state involved). Generated mechanically
   (see Tooling), proved in batches.
5. **HTIF characterization.** Two lemmas from the model's HTIF device:
   a store of byte `c` to `tohost` with the console-write command appends
   exactly one character to `sailOutput`; a store of `(e <<< 1) ||| 1`
   sets `htif_done` and `htif_exit_code = e`. These connect machine
   stores to `Machine.output` and `Machine.Halted`.

**Spike (go/no-go gate):** prove `step_addi` end-to-end first. If the simp
approach cannot close one instruction in acceptable time, the fallback is
per-basic-block lemmas with hand-supplied intermediate states, or porting
Islaris-style automation — decided at this gate, before scaling.

## Layer 1 — a total-correctness program logic over `Step`

Small and fully provable, independent of the model:

```lean
def Triple (P : Config → Prop) (Q : Config → Prop) : Prop :=
  ∀ c, P c → ∃ c', Machine.Steps c c' ∧ Q c'
```

with composition lemmas: sequencing, conditional split on flags/registers,
call/return discipline (RV64 ABI: `ra`, callee-saved `s0–s11`, stack frame
in/out), and a loop rule with invariant + decreasing measure (total
correctness — `term_sim` needs termination, which the simulation induction
supplies at spec level; C-internal loops get measures from data sizes:
list lengths, string lengths, chain depths). Framing is explicit: every
spec carries "memory outside this footprint is unchanged", with region
disjointness lemmas for the fixed memory map (code, script, heap arena,
C stack).

## Layer 2 — runtime representation invariants

Extends `Vsa/MemRepr.lean` (AST structs, done) with the mutable runtime:

- `ValueRepr m a v` — 16-byte `Value` structs (kind tag + payload;
  closures point to `Closure{fn_expr, env}` pairs).
- `EnvRepr m φ a ρ` — C `Env` chains ↔ spec frames, via an injective
  correspondence `φ : spec Addr → machine addr`; sharing is the point:
  two spec frames related iff the C pointers coincide.
- `StoreRepr m φ store` — every reachable spec frame/closure represented,
  heap objects disjoint, all inside the arena.
- `HeapArena` — the no-free discipline: `malloc` results are fresh,
  disjoint, in-bounds. Newlib's allocator is the single largest opaque
  blob. **Decision (CompCert-style, adapted):** do not verify it —
  interface-specify it as a *named hypothesis* `MallocSpec` on the final
  theorem (freshness, 16-byte alignment, arena bounds, termination, NULL
  on exhaustion, allocator-private footprint preserved), the way
  `InterpSim` itself was staged. Not a Lean `axiom`: malloc is internal
  code whose behavior the ISA relation already determines, so a wrong
  axiom about it would make `False` derivable; a hypothesis keeps the
  logic sound and `#print axioms` clean, at the cost of one explicit
  assumption. (CompCert gets to axiomatize `extcall_malloc_sem` only
  because malloc is genuinely external there.) The zero-assumption
  fallback — relink with a 10-line bump allocator and verify it — stays
  available with sign-off. Other libc routines (`memcpy`, `strcmp`,
  `snprintf`) are small and get verified outright, not hypothesized.
- `OutRepr σ st` — `Machine.output σ = st.out` (via the Layer-0 HTIF
  lemmas, output only ever grows by exactly the spec characters).
- `StackRepr` — per-function frame layouts read off the objdump (slot
  offsets for saved `ra`/`s*`, locals); plus the `setjmp` cell contents
  for the error path.

## Layer 3 — function specifications

One total-correctness triple per reachable function, relating ABI-level
entry states to exit states through the Layer-2 invariants. The inventory
(from the call graph under `interp_run`): `exec_stmt`, `eval_expr`,
`eval_binary`, `call_value`, `native_print/println/assert`, `stringify`,
`value_*` (5 small), `env_new/define/get/set`, `interp_run`,
`runtime_error` + `longjmp` (spec: transfers control to `interp_run`'s
`setjmp` continuation with callee-saved registers restored — small
assembly, standard treatment), `strcmp/strlen/strcpy/memcpy`,
`snprintf`-for-`%lld` (spec equals `intToString` — this is why the spec
semantics uses digit recursion), libgcc `__muldi3/__divdi3/__moddi3`
(loop invariants for 64-bit soft arithmetic — classic, self-contained),
`malloc` (per Layer-2 decision).

Mutual recursion (`eval_expr` ↔ `exec_stmt` ↔ `call_value`) is handled by
proving the specs *parameterized by the big-step derivation*: the triple
for `eval_expr` is stated per `EvalE` derivation node and proved by the
Layer-4 induction, so no separate well-founded argument on code is needed;
inner loops (argument evaluation, env walks, block iteration) get measures
from the derivation/list structure.

## Layer 4 — the simulation induction (`term_sim`)

The mutual induction over the eight big-step relations (≈40 constructors),
via the auto-generated mutual recursor. Each case: unfold one C-level
execution segment of the corresponding compiled code path (Layer-3 specs
composed by Layer-1 rules), re-establish `StoreRepr`/`OutRepr`, apply the
IHs for subderivations in evaluation order. Top: `interp_run`'s statement
loop consumes `ExecSeq`, then `main`'s return threads exit 0 into the HTIF
exit store; `Machine.Halts c out 0` follows from the HTIF lemmas with
`out = st'.out` by `OutRepr`. Purely mechanical given Layers 0–3; large
(40 cases × spec plumbing).

## Layer 5 — `stuck_sim`

Two spec-side gadgets, then simulation again:

1. **Error judgment.** Mutual inductive `EvalErr/ExecErr/…` mirroring the
   `runtime_error` sites (undefined variable, type errors, div by zero,
   arity/callee errors, `assert` failure, depth cap). Forward-simulate an
   error derivation to the `longjmp` → diagnostic-print → `exit(70)` path:
   `Halts c out 70` for *some* out (`stuck_sim` doesn't constrain the
   text, deliberately — diagnostics contain line numbers the deep
   embedding doesn't carry).
2. **Bounded progress (trichotomy).** Fuel-indexed inductive
   `Approx n st env s` ("the computation is still running after `n` rule
   steps") with a lemma, by induction on `n` with classical case splits:
   every configuration either terminates (`ExecS`), errors (`ExecErr`),
   or `Approx n` for every `n`. Forward-simulate `Approx n` to ≥ `n`
   machine steps (each spec rule costs ≥ 1 instruction), giving
   `Machine.Diverges`. Note the depth cap (1000) and the arena bound mean
   a real machine run can also abort where the ideal semantics diverges —
   both land in the `Halts _ e ≠ 0` disjunct via the error simulation, so
   `stuck_sim`'s disjunction absorbs resource exhaustion. (This is also
   why `stuck_sim` is stated as a disjunction rather than claiming
   machine divergence exactly when the spec diverges.)

`stuck_sim` then follows: no `BigStep` derivation ⇒ (classically) an error
derivation or `Approx ∀n` ⇒ nonzero halt or divergence.

## Layer 6 — `Layout` instantiation and assembly

`L.atInterpRun c a n` := PC = `interp_run`'s entry (symbol table), `a0` =
interp struct pointer with natives bound (its `ValueRepr`), `a1` = `a`,
`a2` = `n`, `ra`/`sp` well-formed per `StackRepr`, `GoodState`, arena and
output invariants. All concrete constants come from `readelf`/`objdump` of
the fixed binary and enter as *definitions*. Final assembly plugs
`term_sim`/`stuck_sim` into the already-proved `Vsa.Refine.refinement`;
`#print axioms` on the end-to-end theorem must show only `propext`,
`Classical.choice`, `Quot.sound`.

---

## Tooling

- **Disassembly ingestion**: a script (`objdump -d` → Lean) emitting, per
  function, the address/word/operand list as Lean definitions, plus the
  fetch hypotheses (`mem[addr+k]? = some b`) as lemmas about the loaded
  image — proved from `ProgramRepr`-style code-region predicates, not by
  evaluating the 138 KB map (the code region enters `Loaded` as an
  explicit predicate, like the AST does).
- **`seval` tactic**: `simp only` with the Layer-0 sets + `decide`/`omega`
  finishers; grown during the spike, frozen after.
- **CI gates**: `lake build`, a no-`sorry`/no-`axiom` grep, and an
  `#print axioms` check on the final theorem.

## Milestones (each gates the next)

| # | Deliverable | Validates |
|---|---|---|
| M1 | `GoodState`, skeleton lemma, `step_addi` proved | the whole approach; go/no-go |
| M2 | instruction battery (~40–60 classes) + decode table + HTIF lemmas | Layer 0 complete |
| M3 | Triple logic + `env_*`/`value_*`/string/libgcc specs | method scales to real functions |
| M4 | `eval_expr`/`exec_stmt`/`call_value`/`interp_run` specs + Layer-4 induction | `term_sim` |
| M5 | error judgment, `Approx`, divergence simulation | `stuck_sim` |
| M6 | concrete `Layout`, assembly, axiom audit | the theorem |

## Honest scale estimate

M1 is days-to-weeks of expert iteration and decides everything: if one
instruction lemma closes cleanly, the rest is replication with known
techniques. The full plan is realistically **months of sustained work**
(it is an Islaris/Bedrock/CakeML-class binary verification: interpreter-
scale binary proofs against a full ISA model are publishable results).
Nothing in it requires `native_decide` or `sorry` — every reduction is a
kernel-checked `simp`/`decide` on symbolic states with concrete
instruction words, and every behavior claim is by induction over the
inductive relations. The two places where the plan trades scope rather
than proving more: diagnostics text in `stuck_sim` (not tracked, by
design), and the allocator (verify newlib's paths, or relink with a bump
allocator with your sign-off).

---

## Appendix (2026-08-25): tooling and abstractions built during M3 — use for M4–M6

> Block-reflection layer (collapses per-arm `StepObs` batteries onto one kernel
> `decide`): reuse stack + cookbook in `experiments/block-reflection-plan.md`;
> the staged plan to build the next abstractions (Triple-based block program
> logic, reflected disassembly, discharge tactics, meta-generation) and refactor
> onto them is `experiments/block-abstractions-impl-plan.md`. **When a stage of
> that plan lands, update this Appendix's pipeline + the Layer 1 rules + the
> Tooling list in the same commit** (the plan's "Keep the master PLAN updated"
> section is the contract).

Everything below is landed, CI-gated (`scripts/check_all.sh`: build + no-sorry/axiom
grep + `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}), and validated by
re-deriving already-proven artifacts. Ledgers: `experiments/pctrace.md` (per-session),
`scripts/README*.md` (per-tool). The Tooling section's deliverables exist:
disassembly ingestion = `scripts/disasm_to_sites.py`; CI gates = `check_all.sh`;
the `seval` role is filled kernel-cheaply by the reflection block lemmas.

### The pipeline for any new code segment (use in this order)
1. `scripts/disasm_to_sites.py LO HI [--path taken/nottaken-file]` → site TSV
   (classifies from instruction words; `#UNSUPPORTED` marks generator gaps).
2. `scripts/gen_sites.py TSV --code-loaded <XLoaded> --suffix _x` → compiled
   per-site StepObs battery. Byte-pin Code files via `experiments/gen_code_lemmas.py`.
   Hand-site templates for gaps (jalr/sltu/lhu/andi/auipc/slli/srli/jr-imm):
   `SnprintfSitesRet5.lean`, `SnprintfSitesPro4.lean`.
3. Straight-line runs: PREFER `Vsa/Sim/BlockMem.lean` `block_mem_sound` (reflection:
   one application per block, computed write log, ~4× less proof work, O(instrs)
   scaling; ALU+ld/lw/lbu+sd/sw/sb; branch-terminator plan in its header). Otherwise
   `scripts/gen_segment.py` (straight/prologue/epilogue/call/loop modes; `"boundary":
   "segst"` emits zero-hole segments; `"guard": "decide"` for concrete-data branches)
   or the `scripts/pro_emitter/` drivers (real exemplars: gen_spec27..55).
4. Variants of proven segments: `scripts/twin_spec.py` (checked deltas; 100%
   reproduction of Spec46-from-Spec7; deltas in `scripts/deltas/`).
5. Composition lemmas (import and use, never re-derive):
   - registers: `RegPins` (`pins_*` per step, `(by rfl)`; `pins_of_frame` across
     callees), `KeepRegs` (value-free preservation, `decide`-closable) — one line
     per step instead of per step×register;
   - spills/windows: `SlotFrame` (`slot_save/survives_*/reload_bytes/reassemble`),
     width-generic `PinW` (widths 1/2/4/8, `Iff.rfl` bridges to Pin8/Pin4/SlotHolds);
   - pointers: `PtrArith` (sext constants, `ptr_sub`/`ptr_addoff`, `sp_decK_restore`;
     NEVER `simp[toNat_add,toNat_ofNat]` + `2^64−K` rw + `omega` — kernel crash);
   - simp sets (bounded, no search): `bvptr` (EA normalization), `mfr` (memory
     frames), both `simp (disch := omega) only [...]`;
   - Loaded preservation: `CodeRangeInsert` recipe; statics: `ImageStaticsLoaded`
     + `ImageDischarge` (ALL static-data hypotheses discharge from one predicate —
     use it in every new capstone instead of fresh image hypotheses).
6. Block spine as a composed `Triple` (Layer 1, Stage A): once each straight-line
   block is a `<blk>_triple : Triple <blkPre> <blkPost>` (tick`< 2` and the
   register frame ride *inside* the assertions; see `Vsa/Sim/BlockLogic.lean`
   `negPrologue_triple`/`negLoadStore_triple`/`negTail_triple`), the whole spine
   composes as ONE `Triple.seq`/`Triple.conseq` chain — the exemplar is
   `neg_blocks_triple` (σ0→σ15, 3 blocks, 2 seams). Each seam `conseq` marshals
   the register bridges (`bytesVal`↔ghost, kind-int, payload) and threads memory
   survival (`Eval_exprLoaded`/`LdOK`) across the intervening stores via
   `writeLog_getElem_disjoint` (`BlockAdapter`); block-local `m0`-side-conditions
   ride the seams with `Triple.conj_const`. The call seam is `value_int_spec`
   (already a `Triple`), composed by the same `seq`. Prefer this over hand-threading
   per-site `StepObs`+frame bridges for any new multi-block segment.
   **Stage A2/A-refactor landed (2026-08-25):** the block Posts carry a *genuine
   entry→exit register frame* (each Pre/Post takes an `entryRegs` ghost + an
   `out0` sailOutput ghost; the frame conjunct is `c.σ.regs.get? R = entryRegs R`
   under the block's noise/wrRegs guards — assertion-carried framing, NOT a
   generic `Triple.frame`, which would be unsound). `neg_prologue_loadstore_triple`
   /`neg_blocks_triple` `.trans`-compose these to a real σ0-entry frame under the
   union of the blocks' wrRegs guards. `blockC_neg` (M4 neg pilot) now **consumes
   `neg_blocks_triple`** for its whole σ0→σ15 spine: one application replaces the
   three per-block `obtain`s + inter-block seams, and `hframeG` collapses to one
   `hframeSpine …` (each block's wrRegs guard discharged by `block_frame_wr`).

### Iteration-latency rules (measured: 2–4 min → 1–6 s per check)
One segment theorem per module (≤600 lines); `lake env lean` per file while
iterating; `lake build <mod>` for closure after cross-file edits (stale-olean
trap — trust `lake build` over editor LSP diagnostics); Python generation over
tactics/macros (plain terms = floor elaboration cost, zero search).

### For M4 (the mutual induction)
`scripts/gen_m4_case.py` + `scripts/m4_cases.tsv` emit ~78% of a leaf case;
`EvalSimCommon` holds the shared machinery. Recursive-case prerequisites:
the `EvalExit`-shaped `armTail_v` analogue and the IH-application glue
(pilot in flight → `EvalRecCommon`); after extraction, remaining cases are
table rows. `Code/FnFmt.lean` pins the closure-stringify format for that arm.

### For M6
`ImageStaticsLoaded` is the statics half of `Loaded`/`Layout` instantiation;
capstone layout hypotheses are the geometry half — bundle both into the
concrete `Layout L` records at assembly time.

### Known statement-size cost (open work)
Capstone statements carry 40–70 hypotheses and large conjunction posts; the
measured slow glue checks (72 s Spec25, 71 s Spec49) are dominated by
transport simps over huge terms. Mitigation direction: published Pre/Post
records (the `PreSr` pattern) + a `FrameOn (windows : List Window)` predicate
replacing bespoke pointwise-frame conjunctions + the BlockMem write-log as
the canonical post-memory normal form.

### 2026-08-25: semantics amendment — WHILE arithmetic wraps at 64 bits (user-approved)
The M4 recursive-case pilot found `EvalE.neg` on unbounded `Int` unsatisfiable
vs the machine at `n = −2^63` (the compiled interpreter's `long long` arithmetic
wraps; libgcc soft div gives `INT64_MIN/−1 = INT64_MIN`, `rem 0`; div-by-zero is
a `runtime_error`). Resolution (`Vsa/While/Semantics.lean`): every arithmetic
result is passed through `def wrap64 (z : Int) : Int := (BitVec.ofInt 64 z).toInt`
— the canonical machine round-trip — so the spec describes the shipped artifact.
Workhorse lemmas `wrap64_eq_self`/`_range`/`_idem`/`_toInt`/`ofInt_wrap64`;
regression witnesses `wrap64_neg_min`, `wrap64_tdiv_min`, `wrap64_tmod_min` (the
libgcc special cases, C99 `.tdiv`/`.tmod` truncation). Literals are unwrapped
(they arrive in-range from the machine-resident AST per `MemRepr`). Comparisons/
equality unchanged (operands are stored, hence in-range). Downstream `Cost`/
`Derive` adjusted (in-range test cases → `wrap64_eq_self`); full tree + 43/43
axiom audit green.

---

## Appendix (2026-08-26): M4 progress — EvalE cases + statement family opened

Session progress on Layer 4 (`term_sim`), all commits on `main`, each `check_all: OK`
(build + no sorry/axiom + `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}).
Every case is a `Triple` in the `EvalIH`/`ExecEntry` motive shape, conditional on named
program-structure geometry + M6-Layout residuals (the sanctioned `env_get_found`/`evalVarSim`
staging) — the endgame (M6 `Layout` + a uniform residual-discharge + abstraction strengthening)
closes them. See `memory/m4-recursive-cases.md` + `memory/m4-statement-family.md` for the full
per-case decode, the reusable multipliers, and the recurring residual list.

### EvalE (expression) cases — LANDED
- Leaves (pre-session): int, null, bool, str, var.
- Recursive-case machinery: `blockA_k`/`ArmEntryK` widened (`aEnv` + x11/x8/x18), `blockD_v_rec`
  (`PreEpilogueVD → EvalExitD`), `blockB_binary` (two-operand head), `blockB_logical`
  (short-circuit head), `armTail_rec` (single `jal eval_expr` ⋈ IH glue).
- Unary: `neg`, `not`.
- Binary (int): `add`, `sub`, `lt` + the full operator jump-table dispatch decode
  (CSWTCH.18 @0x80019f84). Mechanical follow-ups: `le`/`gt` (cmp foundation `CmpBridges`/
  `CmpTailSites` staged), `eq`/`ne` (value_equal), `mul`/`div`/`mod` (libgcc soft-arith).
  **FLAG: `.ge` (token 23) → machine runtime_error, but spec `binOpSem .ge` succeeds —
  possible spec/machine divergence unless the front-end desugars `>=`. Needs a semantics decision.**
- Logical: `and`/`or` all four constructors (short-circuit + two-eval, shared `blockC_logTail`).

### Statement family (ExecS/ExecSeq) — OPENED + core cases
- `exec_stmt` fully decoded (entry 0x80003fe0, 9 arm PCs, status ABI: a0 = status code).
- Foundation: `ExecEntry`/`ExecExit`, `Exec_stmt` byte-pins (202 fetch lemmas), `execSeqNil`.
- Multipliers: `execBlockA` (prologue+dispatch, UNCONDITIONAL — statement analog of `blockA_k`),
  `execBlockD` (epilogue, UNCONDITIONAL), `armTail_rec_es` (sp-176 statement-frame recursion glue).
- Cases: `brk`, `cont` (register-only), `expr` (recursive, `execExprSimC`), `ret` (retval copy).

### Remaining for term_sim
EvalE: `call` (crux — closures/depth, bridges to ExecSeq), + the mechanical binary ops.
Statements: `retNull`, `varDecl` (env_define), `block`/`ExecSeq` (consNormal/consAbrupt + the
do-while loop, `Triple.loop`), `ifStmt`, `whileStmt`, `forStmt` (loops), + `EvalArgs`/`ForLoop`/
`ForCond`/`ExecStep`/`ExecInit`. Then the Layer-4 mutual-recursor assembly (`InductionScaffold`
`SegEntry`/`SegExit` skeletons → real `ExecEntry`/`ExecExit`), then M5/M6.

---

## Appendix (2026-08-26, later): M4 near-complete case coverage + statement/call families

Continued M4 progress (all on `main`, each `check_all: OK`, axioms ⊆ {propext, Classical.choice, Quot.sound}).
Details in `memory/m4-recursive-cases.md`, `m4-statement-family.md`, `m4-call-subsystem.md`.

### Coverage status — every relation's constructors now have landed conditional Triples
- **EvalE**: leaves (int/null/bool/str/var), unary (neg/not), binary (add/sub/lt; le/gt/eq/ne/mul/div/mod are
  mechanical follow-ups on the proven dispatch), logical (all 4), **call**, **fn**. (`.ge` machine/spec divergence flagged.)
- **EvalArgs**: nil, cons (`evalArgsLoop`).
- **Call**: assertOk (native, conditional on the machine-run); print/println decoded (template ready); **closure = the
  remaining crux** (arity+depth-guard+env_new+env_define-fold+body-ExecSeq at d+1), blocked on the uncomposed
  `env_define` contract (M3 did only its prologue; needs strlen+malloc+memcpy+realloc — no realloc spec).
- **ExecS**: ALL constructors (expr/varInit/varNull/block/if×3/while×4/forStart/ret/retNull/brk/cont).
- **ExecSeq**: nil, cons (`execSeqLoop`). **ForLoop** ×4 (`execForLoopBody`). ExecInit/ForCond/ExecStep folded into loop steps.

### Reusable machinery built this session (the multipliers)
EvalE: `blockA_k` (widened, +aEnv), `blockB_binary`/`blockB_logical`, `blockD_v_rec`→`EvalExitD`, `armTail_rec`.
Statements: `execBlockA`/`execBlockD`, `execPrologue`/`execDispatch` + `ExecDispatchReady`/`ExecDispatchIH`
(the re-dispatch infra for if/while/for), `armTail_rec_es`/`armExec_rec`, `execSeqLoop`, `execExit_extend`.
Cross-cutting: `exprRepr_agreeP`/`stmtRepr_agreeP` (AST-transport), `stmtRepr_kind`.

### Remaining to close `term_sim`
1. The **Layer-4 mutual-recursor assembly** (`InductionScaffold` `@EvalE.rec` + real motives → `term_sim`), which
   supplies each case's IHs. Blocked on residual unification: cases carry heterogeneous named residuals.
2. **Discharge the residuals**: the per-iteration step contracts (`ExecWhileStep`/`ExecForStep`/block-`hstep`/
   `EvalArgsStep`/the native machine runs — concrete machine work), the M6-Layout geometry, the composed
   `env_define`/`realloc` contract (the biggest gap, gates `Call.closure`/`varDecl`/`assign`).
3. Then M5 (`stuck_sim`) and M6 (`Layout` + final theorem + axiom audit).
