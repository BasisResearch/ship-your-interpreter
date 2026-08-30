# `env_define` composition — Shape-D (step 5 of interp-sim-completion-plan)

Landed: `Vsa/Sim/EnvDefCompose.lean` (green, 2.2s, axiom-clean
`{propext, Classical.choice, Quot.sound}`), wired into `Vsa.lean` after
`BinOpValueTails`, 5 capstones added to `check_all` (now 290/290).

## The gap this closes

`env_define` is the biggest semantic gap: its append/grow paths call `strlen`,
`malloc`, `memcpy`, and `realloc` (twice). Every call is a Shape-D `jal rd`
splice `prefix ≫ callee ≫ suffix`. The HARD part is the call-composition
algebra (associativity/seam order across four+ chained calls threading four
different callee contracts); the honest remaining work is the per-block
straight-line machine bridges. This file lands the composition (proved) and
names the bridges precisely — the exact `divValueTail` discipline
(`BinOpValueTails.lean`) scaled from 2 calls to 3 (append) / 2 (grow).

## Control-flow map (from `experiments/disasm.txt`; `EnvDefSpec2` header)

```
PROLOGUE 0x80002a5c..0x80002a90  ── PROVED  (EnvDefSpec17.env_define_prologue)
  blez s3 → CAP-INIT   (count == 0, name absent)
SCAN 0x80002a94..0x80002abc      ── update path (EnvDefSpec3: loop + per-iter strcmp)
  hit  → UPDATE 0x80002ac0..0x80002ae8 → EPILOGUE          (name found)
  miss → CAP-CHECK 0x80002b14: beq cap,count → GROW          (name absent)
APPEND 0x80002b1c..0x80002b8c     ── strlen ≫ malloc ≫ (NULL guard) ≫ memcpy ≫ store
  b20 jal strlen  ;  b2c jal malloc  ;  b34 beqz a0 → OOM  ;  b40 jal memcpy
  b44..b88 store copy into names[count]/vals[count], count++   → EPILOGUE
GROW 0x80002b90..0x80002bcc       ── cap' ≫ realloc(names) ≫ realloc(vals) → APPEND head
  ba0 jal realloc(names,cap'*8)  ;  bbc jal realloc(vals,cap'*24)  ;  bcc → 0xb1c
OOM 0x80002bd0..0x80002bf0  : _impure_ptr / fwrite / exit(1) — never returns
CAP-INIT 0x80002bf4..0x80002c0c : cap==0 entry → APPEND / GROW / init cap:=8
EPILOGUE 0x80002aec..0x80002b10 : restore 7 spills, sp+=64, ret
```

`mallocEntry = 0x80004790` (`Vsa/Alloc.lean`), `reallocEntry = 0x8000527c`
(`EnvDefSpec2`), strlen entry `0x80006cf0` (`StrlenSpec`), memcpy dispatch
`0x80006bc8` (`MemcpySpec4`).

## Segment ledger — PROVED vs NAMED BRIDGE

| Segment | Status |
|---------|--------|
| prologue 0x80002a5c→0x80002a90 | **PROVED** `env_define_prologue` (EnvDefSpec17) |
| scan loop + update block | statement + all ingredients (`EnvDefSpec3`); loop body a documented obligation (`scan_iter_measure_ok`) |
| grow2 arena merge / two-frame compose | **PROVED** `realloc_grow2_arena` / `heapPublicFrame_trans` (EnvDefineClose) |
| **strlen call splice** | **PROVED HERE** `envDefStrlenSplice` over `strlen_spec` |
| **malloc call splice** | **PROVED HERE** `envDefMallocSplice` over `MallocContract.spec` |
| **memcpy call splice** | **PROVED HERE** `envDefMemcpySplice` over `memcpy_spec` |
| **realloc(names)/realloc(vals) splices** | **PROVED HERE** `envDefRealloc{Names,Vals}Splice` over `ReallocOps.grow` |
| **append path composed** | **PROVED HERE** `envDefAppendContract` (strlen ≫ malloc ≫ memcpy ≫ store) |
| **grow path composed** | **PROVED HERE** `envDefGrowContract` (cap' ≫ realloc ≫ realloc ≫ append-head) |
| **top-level dispatch join** | **PROVED HERE** `envDefContract` (update ⊕ append ⊕ grow) |

## `MallocSpec` — already exists, not re-defined

The plan's `MallocSpec` is `Vsa.Alloc.MallocContract` (`Vsa/Alloc.lean`, header
explicitly reads "the plan's `MallocSpec`"). It already bundles every property
the plan lists: freshness + 16-byte alignment + arena bounds + termination
(total-correctness Triple) + NULL-on-exhaustion + allocator-private footprint
preserved + the ABI frame. It is a `structure` field (hypothesis), never a Lean
`axiom`. `ReallocOps` (`Vsa/Sim/ReallocSpec.lean`) is the realloc analogue over
the same `AInv`/`privFoot` ledger. **No new spec structure was needed** — the
composition threads these existing contracts by name, exactly as
`env_new_spec` (EnvNewSpec) threads `MallocContract.spec` for the single-malloc
case. env_define calls newlib `realloc` directly (entry `0x8000527c`), so its
contract is `ReallocOps.grow`, not routed through malloc.

## What composed (proved, axiom-clean)

8 theorems, all pure `callSeg`/`Triple.seq` plumbing — no reflection, constant
elab time:

- `envDefStrlenSplice` / `envDefMallocSplice` / `envDefMemcpySplice` /
  `envDefReallocNamesSplice` / `envDefReallocValsSplice` — the five single-call
  splices, each `callSeg pre <real-contract> suf`.
- `envDefAppendContract` — the WHOLE append path as one `callSeg`-chain over
  `strlen_spec` + `MallocContract.spec` + `memcpy_spec`, all three real callees
  threaded; residual = 4 straight-line bridges.
- `envDefGrowContract` — the WHOLE grow path as one `callSeg`-chain over
  `ReallocOps.grow` twice; residual = 3 straight-line bridges.
- `envDefContract` — the top-level dispatch join: `dispatch ≫ (update ⊕ append ⊕
  grow)`, all three paths landing the common post.

## Precise residual list (strictly smaller gap for next session)

Every residual is a Shape-A straight-line `#derive_case`/`chain_facts` segment
over pinned bytes (NO new call composition, NO new callee contract). Named as
hypotheses of the `*Contract` theorems:

1. **Append bridges** (`envDefAppendContract` premises), all in
   `0x80002b1c..0x80002b88`:
   - `bridgeStrlenPre`  : path-entry → `strlen_pre` (mv a0,s2; jal strlen).
   - `bridgeMallocPre`  : `strlen_post` → malloc entry pred (addi s0,a0,1;
     mv a0,s0; jal malloc). Also carries the `count < cap` frame facts.
   - `bridgeMemcpyPre`  : malloc post → `PreDispatch` (mv s1,a0; beqz a0 NULL
     guard [OOM arm never returns — ruled out as env_new does]; mv a2,s0;
     mv a1,s2; jal memcpy).
   - `bridgeStore`      : `memcpy_bytepath_post` → common post Q. The store
     block `0x80002b44..0x80002b88` (3×sd vals[count], sd names[count], sw
     count+1) + epilogue restore. This is the one bridge that also does the
     spec-side `Store.define` append-frame reconstruction (`define_append_*`
     landed in EnvDefSpec2).

2. **Grow bridges** (`envDefGrowContract` premises), `0x80002b90..0x80002bcc`:
   - `bridgeCapCompute` : path-entry → `ReallocPre` for realloc(names)
     (slliw cap*2; slli newcap*8; sw env->cap; mv a0,s6; jal realloc).
   - `bridgeNamesToVals`: realloc(names) post → `ReallocPre` for realloc(vals)
     (lw newcap; sd env->names; ld a0=vals; slli/add/slli newcap*24; jal
     realloc). Consumes the first `ReallocGrowResult`.
   - `bridgeAppendHead` : realloc(vals) post → common Q (ld new names; sd
     env->vals; beqz names→OOM; bnez vals → 0xb1c append head). Consumes the
     grow2 arena/frame algebra (`realloc_grow2_arena`/`heapPublicFrame_trans`,
     already proved).

3. **Dispatch** (`envDefContract` premise `dispatch`): prologue (PROVED,
   `env_define_prologue`) ≫ the scan loop landing one of Pup/Pap/Pgr. The scan
   loop's `Triple.loop` body (per-iter `strcmp` + `bnez`, measure `count - i`)
   is a Shape-C residual with all ingredients landed in EnvDefSpec3
   (`scanMeasure`, the miss/hit bridges, `scan_iter_measure_ok`); assembling the
   `Triple.loop` is the one loop-shape obligation. CAP-INIT + CAP-CHECK are the
   short straight-line arms choosing among the three path-entries.

4. **Update segment** (`envDefContract` premise `hUpdate`): the update-in-place
   path `Triple` `env_define_update_spec` (EnvDefSpec3, statement recorded,
   threading documented not executed — ~30 site lemmas + the scan loop, all
   verified ingredients present). No allocator, so no call composition — pure
   Shape-A + Shape-C.

## Consumer interface match

Consumers (`Call.closure` in EvalCallClosure/CallEntry, `varDecl` in
ExecVarDecl, `assign`) reference "the `env_define` contract" abstractly as a
`Triple env_define_pre env_define_post`. The canonical pre/post shape is
`env_define_update_pre`/`env_define_update_post` (EnvDefSpec3) — its post is
`FrameRepr (Store.define f nameStr v)` for ANY path (the `if any then map else
++` covers update/append/grow uniformly). `envDefContract` produces exactly a
`Triple P Q` with the three per-path segments landing that common Q, so the
consumer plugs in with a thin adapter (instantiate P = env_define_pre, Q =
env_define_post, and the three segment hypotheses).

## Mechanical / fan-out observations

- **The malloc-call splice shape (`envDefMallocSplice`) is IDENTICAL to
  `env_new`'s** (both `callSeg pre M.spec suf`). `env_new_spec` (EnvNewSpec)
  is the hand-rolled single-malloc case; it should be REFACTORED to
  `envDefMallocSplice` (fan-out signal: one malloc-splice combinator serves
  env_new AND env_define's append). Same for the closure-crux `env_new` call
  in `EvalCallClosure`.
- **The realloc-splice shape repeats verbatim** for names and vals
  (`envDefReallocNamesSplice` = `envDefReallocValsSplice` up to the base/stride
  in the bridges) — one `envDefReallocSplice` combinator with a base/stride
  parameter would collapse the two. Kept as two named theorems here to document
  the two distinct call sites.
- **`envDefContract`'s three-way dispatch join** (`dispatch ≫ ⊕`) is the same
  shape `EvalE.call`'s native/closure/error dispatch needs — reusable as a
  `Triple.cond3` helper (fan-out signal into the M4 call subsystem).
- Every bridge is a `#derive_case` + `chain_facts` + `segToTriple` target
  (Shape-A), budget ≤120s each — the same recipe the binary-op ladders use.
  None needs new callee contracts or new call composition. The COW-clone
  fan-out workflow applies (each bridge independent).
