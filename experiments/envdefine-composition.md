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

## Bridge-discharge ledger (2026-08-30, `Vsa/Sim/EnvDefBridges.lean`)

Machine-bridge discharge session. `EnvDefBridges.lean` builds green + axiom-clean
(`[propext, Classical.choice, Quot.sound]`), wired into `Vsa.lean` after
`EnvDefCompose`. Elab ~1.1s.

**CLOSED: 1 / 9 bridges (+ reusable infrastructure).**

- `bridgeStrlenPre` — **DISCHARGED** as `bridgeStrlenPre_closed`. Entry predicate
  `AppendStrlenEntry namePtr nameStr m0` (a rich `P` supplying the `strlen`
  argument facts: `StrlenLoaded`, `StrRegions`, `namePtr%8=0`, `CString`, plus the
  `0x80002b1c` machine state) runs the `mv a0,s2 ; jal strlen` prefix and lands
  `strlen_pre namePtr 0x80002b24 nameStr m0` at the strlen entry `0x80006cf0`. The
  return address `rStrlen = 0x80002b24` (the `jal` link, 4-aligned). Matches the
  `envDefAppendContract` premise verbatim (`P := AppendStrlenEntry`,
  `rStrlen := 0x80002b24`).

### Shared sub-shape factored (the exponentiating deliverable)

- **`mv rd,rs ; jal callee` prefix idiom.** Every append/grow call prefix is this
  2-instruction shape (arg-marshalling move into `a0`, then the linking `jal` to
  the callee entry). Factored the per-site step lemmas (`site_80002b1c_ed` the
  `mv`, `site_80002b20_ed` the `jal`) and the composed two-step run
  `strlenPrefix_run` (chains both `Step`s via `Steps.trans`, delivers PC=callee
  entry, `x10 = marshalled arg`, `x1 = link`, `mem` unchanged, `minstret` defined).
  The `jal`-marshalling readback helpers (`obs_jal_pc_env`/`obs_jal_rd_env`/
  `obs_jal_other_env`/`obs_jal_minstret_env`, `frame_jal_env`) are REUSED VERBATIM
  from `EnvNewSpec` — env_new's single-malloc splice IS this idiom. Any other
  `mv;jal` prefix (malloc, memcpy, realloc(names)) instantiates the same two site
  lemmas at its own words + one `strlenPrefix_run`-shaped composition.
- Byte substrate is fully present: `Code/Env_define.env_define_at_*` pins the whole
  `0x80002b1c..0x80002c0c` append/grow region, and every append/grow word already
  has a `DecodeTable.decode_<word>` lemma (verified: mv/jal/addi/slliw/slli/sw/
  realloc-jal all present). No per-site StepObs battery exists for these PCs
  (`EnvDefSites` covers only `[0x80002a5c,0x80002b10]`), so each site lemma is
  hand-built from pin + decode + `stepObs_*`, mirroring `EnvNewSites`.

### Resisted, with exact reasons (NO workarounds taken)

- `bridgeMallocPre` — **BLOCKED by underspecified source.** Its stated source is
  literally `strlen_post rStrlen nameStr m0` = `GoodState ∧ PC=r ∧ x10=len ∧ x1=r ∧
  mem=m0`. The target (malloc entry predicate) additionally requires `x2=spM` +
  `StackOK`, `x3=gpv`, the ABI-preserved-registers tie `(∀R, AbiPreserved R → …=gm R)`,
  and `M.AInv`. `strlen_post` carries NONE of `sp`/`gp`/`AInv`/ABI (strlen's contract
  discards all caller-saved context on return). So the bridge is not provable from
  its stated source; it would require `strlen_spec`/`strlen_post` to be a
  frame-preserving version (a statement change, out of scope). Same root cause blocks
  the parts of the chain whose source is a bare callee-post.
- `bridgeMemcpyPre` — **BLOCKED, analogous.** Target `PreDispatch` requires
  `MemcpyLoaded`, `Regions dst src n`, `0<n`, and `MemInv dst src n bs 0 m0`
  (the copy source bytes) — semantic copy facts NOT present in the malloc-post
  source predicate. Needs carried context the stated source lacks.
- `bridgeStore` — feasible in principle (straight-line stores, no `jal`), but its
  target `Q` is abstract AND the honest content is the `Store.define` append-frame
  `FrameRepr` reconstruction over `memcpy_bytepath_post`; large, not attempted in
  budget.
- `bridgeCapCompute` — **FEASIBLE, not completed in budget.** Free source `P` (like
  strlen), so a rich `GrowEntry` could supply the facts. Prefix is
  `slliw a5,a5,1 ; slli a1,a5,3 ; sw a5,4(s4) ; mv a0,s6 ; jal realloc` — 5 sites,
  THREE new instruction classes (SHIFTIWOP/SHIFTIOP/width-4 STORE) whose execute
  helpers exist (`execute_shiftiwop_slliw_char`, `execute_shiftiop_slli_char`,
  `exec_sw`), PLUS the `sw` writes `env->cap` so it threads store-memory and needs
  `AInv`-survives-cap-store carried as a boundary hypothesis (`AInv` is abstract, so
  no generic store-frame lemma). ~150 lines; the `mv;jal` tail reuses this session's
  `strlenPrefix_run` shape.
- `bridgeNamesToVals`, `bridgeAppendHead` — rich sources (`ReallocPost ∧
  ReallocGrowResult` carry sp/gp/ABI/AInv + the arena-frame algebra already proved
  in `EnvDefineClose`), so NOT blocked by underspecification, but each is ~8-10
  straight-line load/store sites consuming `realloc_grow2_arena`/
  `heapPublicFrame_trans`; large, not attempted.
- `hUpdate` (`env_define_update_spec`) — self-contained (no allocator), all
  ingredients in EnvDefSpec3, but is the ~30-site straight-line + scan `Triple.loop`
  assembly; large, not attempted.
- Dispatch scan loop — Shape-C `Triple.loop`; not attempted.

### Net for next session

The `mv;jal` prefix idiom + its two reusable site lemmas are landed and green, so the
remaining FREE-source prefix bridges (`bridgeCapCompute`) drop in by cloning
`strlenPrefix_run` at new words. The two `*Pre` append bridges beyond strlen are
BLOCKED at the stated signature (callee-post sources too narrow) — closing them needs
frame-preserving `strlen`/`memcpy` post-conditions, a statement change flagged here.

## Structural frame-gap FIX — assertion-carried framing (2026-08-30)

Reworked `EnvDefCompose.lean` + `EnvDefBridges.lean`. Both build green +
axiom-clean (`[propext, Classical.choice, Quot.sound]`); elab 1.53s / 1.22s (≤120s
budget). No sorry/axiom/native_decide/bv_decide; oleans regenerated.

### The fix: FRAME-CARRYING seams (`EnvDefFrame`)

The prior session diagnosed the gap correctly: the seam between two callees was the
BARE downstream callee-post (`strlen_post`, malloc-post), discarding sp/gp/ABI
callee-saveds/AInv — so `bridgeMallocPre`/`bridgeMemcpyPre` were unprovable.

Applied the house pattern (assertion-carried framing — `BlockLogic.negProloguePost`,
`BinOpValueTails`, `ReallocPost`; NOT a generic `Triple.frame`, which is unsound per
`BlockLogic.lean:78`). New `EnvDefCompose.EnvDefFrame SL gpv headroom AInv exts sp gm`
bundles the carried caller context: `x2=sp ∧ StackOK ∧ x3=gpv ∧ (AbiPreserved-tie gm)
∧ AInv c.σ exts ∧ c.tick < 2` — exactly the malloc/realloc-entry frame minus the
argument pins (PC/x10/x1/mem).

- `envDefStrlenSplice` is now frame-carrying: it takes a NAMED premise `strlenFramed :
  Triple (strlen_pre ∧ F) (strlen_post ∧ F)` and threads `F` across the call. This is
  the honest, auditable form of strlen's missing preservation clause (below).
- `envDefAppendContract`'s `bridgeStrlenPre`/`bridgeMallocPre` premises are RE-SOURCED
  to `strlen_pre ∧ EnvDefFrame` / `strlen_post ∧ EnvDefFrame`. Top-level names +
  conclusions (`envDefAppendContract`/`envDefGrowContract`/`envDefContract`) unchanged.

### Bridges closed: 2 / 9 (was 1/9) — both frame-carrying

- **`bridgeStrlenPre_closed`** — REPROVED against the enriched seam. `AppendStrlenEntry`
  now also carries the frame ghosts (`SL gpv headroom AInv exts sp gm`); the `mv;jal`
  prefix lands `strlen_pre ∧ EnvDefFrame` at `0x80006cf0`. Frame survives because the
  prefix writes only x10 (mv) / x1 (jal): `strlenPrefix_run` was EXTENDED with x2/x8
  pins + a blanket `NotWrittenEnv` frame clause (via `get?_sigmaPost_alu/jal` readbacks);
  AInv survives by a stability premise `hAInvStable` (mem-agree ∧ gp-agree ⇒ AInv), the
  same `MallocContract`-interface property `env_new` uses (`EnvNewSpec:496`).
- **`bridgeMallocPre_closed`** — NEWLY CLOSED (the previously-BLOCKED bridge). From
  `strlen_post ∧ EnvDefFrame`, the real malloc prefix
  `0x80002b24 addi s0,a0,1 ; 0x80002b28 mv a0,s0 ; 0x80002b2c jal malloc` lands the
  `MallocContract.spec` entry predicate: `nMalloc = nameStr.length+1`, `rM=0x80002b30`,
  `sp/gp/AInv` from the carried frame. NEW: three site lemmas `site_80002b24_ed`
  (addi), `site_80002b28_ed` (mv), `site_80002b2c_ed` (jal, imm=0x001c64 → mallocEntry),
  composed in `mallocPrefix_run` (3-step run + frame). The one callee-saved the prefix
  rewrites is x8/s0 (holds the size across the call), so the malloc-entry ABI ghost `g'`
  differs from the strlen-frame ghost `gm` ONLY on x8 — carried as two clean premises
  `hg'x8`/`hg'other`. Decode lemmas `decode_00150413/00040513/465010ef` all present.

### Contract preservation gaps NAMED (honest residuals, NOT weakened)

The `strlenFramed` premise is UNPROVED here on purpose — it is exactly the set of
`strlen_spec`-conclusion clauses that are MISSING and would let it be discharged. To
close `strlenFramed` (and, symmetrically, the memcpy seam), `strlen_post`/`Done`
(StrlenSpec.lean:763,2139) must be EXTENDED to additionally state (a statement change,
out of my file-ownership scope — flagged, not made):

1. **`c.tick < 2`** — the intra-tick counter bound. `strlen_post` drops it entirely;
   every downstream Step lemma needs `i < 2`. (Carried in `EnvDefFrame` as the stopgap.)
2. **`c.σ.regs.get? Register.x2 = some sp`** (sp preserved) + `StackOK`.
3. **`c.σ.regs.get? Register.x3 = some gpv`** (gp preserved).
4. **`∀ R, AbiPreserved R → c.σ.regs.get? R = g R`** — the ABI callee-saved tie against
   an entry ghost `g` (strlen honours the psABI; leaf reader, no callee-saved clobber).
5. **`AInv`-preservation** (or the `hAInvStable` interface property as a `strlen_spec`
   field), since strlen never stores (`mem = m0`), so any mem+gp-stable AInv survives.

These five are precisely the `strlen_post`↔malloc-entry delta. strlen PHYSICALLY
satisfies all five (8-aligned fast path is a pure reader), but its stated Triple does
not express them. `memcpy_bytepath_post` (MemcpySpec.lean:782) is BETTER: it already
carries `(∀ R, NotWrittenB R → regs R = g R)` (NotWrittenB excludes only x11/x14/x15 +
control, so sp/gp/callee-saveds ARE tied) plus the outside-footprint memory frame — so
the memcpy seam's frame is derivable once its `PreDispatch`-side copy facts
(`MemcpyLoaded`/`Regions`/`MemInv`) are threaded from `P` (not blocked on a memcpy
statement change; blocked only on the store-block bridge machine work).

### Remaining (unchanged budget-scope residuals)

`bridgeMemcpyPre` (needs copy-source facts carried in F + the malloc-post→memcpy-entry
prefix bridge), `bridgeStore`, `bridgeCapCompute`, `bridgeNamesToVals`,
`bridgeAppendHead`, `hUpdate`, dispatch scan loop — each a straight-line/loop machine
segment, none now blocked by seam underspecification (the frame plumbing is in place).
`bridgeCapCompute` drops in by cloning `mallocPrefix_run` at the realloc words.

## strlen_spec_framed — the missing preservation clauses (2026-08-30, IN PROGRESS)

Built `strlen_spec_framed` in `Vsa/Sim/StrlenSpec.lean` (additive; existing
`strlen_spec`/`strlen_post`/`strlen_aligned_spec` UNCHANGED — no consumer touched).
The framed spec threads an ABI-callee-saved register frame
`∀ R, AbiPreserved R → get? R = g R` through the WHOLE aligned strlen run
(entry ≫ word-loop ≫ byte-tail ≫ ret), giving the `strlenFramed` residual's clauses.

### Clause status (the 5 the composition needs)
- **Clause 2 (x2=sp+StackOK), 3 (x3=gp), 4 (callee-saved tie)** — DELIVERED as the
  single conjunct `∀ R, AbiPreserved R → get? R = g R`.  x2/x3 are `AbiPreserved`, so the
  one clause subsumes them; StackOK is an `sp`-value property recovered once x2 survives.
  Sound because strlen's 8-aligned fast path writes ONLY `{x1,x10..x15}` (`ra`,`a0..a5`),
  disjoint from `AbiPreserved = {x2,x3,x4,x8,x9,x18..x27}` (`Vsa.Alloc.AbiPreserved`).
- **Clause 5 (AInv)** — corollary of `mem = m0` (ALREADY in `strlen_post`); exposed as
  `strlen_framed_mem_stable`.  No spec change: strlen never stores.
- **Clause 1 (tick<2)** — NOT yet in the framed post (the framed carrier is the register
  frame only, to avoid re-threading the tick counter).  Per this ledger's prior note,
  `EnvDefFrame` already carries `c.tick < 2` as the stopgap, so the `strlenFramed`
  discharge can source tick from the ENTRY `EnvDefFrame` if the composition tolerates the
  entry-tick; if the exit-tick is strictly needed, the framed blocks must additionally
  thread `c.tick < 2` (every site lemma already yields `i' < 2`, so it is mechanical —
  convert the block carrier to `AbiFrame g = ghost ∧ tick<2`, which is already defined).

### Architecture (exponentiating, per the fast-reflection rules)
Frame primitives `strlenFrame_alu/_btaken/_bnottaken/_jr` (one per `sigmaPost_*` family,
built from `get?_sigmaPost_*` + `hobs.1`, keyed on `AbiPreserved` via `abiPreserved_pinned`
+ `abiPreserved_wr`; NO `StrcmpSpec` dep — that file imports this one).  Two GENERIC
framed-block combinators `tdec_next_k_framed`/`tdec_exit_k_framed` (site lemmas as
callbacks) frame all 5 advances + 6 exits from ONE proof each; concrete
`next{0..4}_framed`/`exit{0..5}_framed` are thin instantiations whose leaf `decide`s are
paid ONCE at their own elaboration; `tail_to_done_framed` composes pre-checked constants
by shallow per-branch `.seq` (no deep-nested-term whnf).  Entry/loop framed by
`entry_aligned_framed` (8-site re-run) + `wloop_to_tail_framed` (`Triple.loop` over
`WLoopI ∧ ghost`, framed `wloop_straight/back/exit`).

### Compile status — BLOCKED on two items + persistent build-lock contention
1. `exit4_framed` hits the 8M-heartbeat `whnf` timeout (offsets 0–3 + 5 elaborate; 4
   tips over).  Root cause = the per-offset 64-bit `BitVec` `decide`s (`himm`/`hbtpc`);
   FIX = precompute those literal facts as named lemmas so the exit is `exact`, not
   `decide` (exponentiating rule: one small decide per fact, reused).
2. Clause-1 tick threading (above).
Verification was repeatedly starved by the shared `.lake` build lock (two other agents
compiling); the last full compile that completed showed exactly these two errors + a now-
FIXED `AbiFrame`-vs-bare-ghost unification in `strlen_aligned_spec_framed` (rewritten as a
tactic proof with an explicit `hmid` intermediate).

### EnvDefCompose wiring — NOT YET applied (blocked on the above closing green)
Once `strlen_spec_framed` is green + tick-carrying, `envDefAppendContract`'s
`strlenFramed` premise discharges by: extract `ghost` from the entry `EnvDefFrame`
(4th conjunct); apply `strlen_spec_framed`; at exit reconstruct `EnvDefFrame` from
`ghost` (x2=sp/x3=gp via the AbiPreserved tie against the entry-pinned `g`), `mem=m0`
(→ AInv via the allocator's mem+gp-stability), and tick.  `bridgeStrlenPre_closed`/
`bridgeMallocPre_closed` are unaffected (they consume `EnvDefFrame`, unchanged).

## strlen_spec_framed — UPDATE (2026-08-30, exit4 elaboration blocker)

`strlen_spec_framed` + the whole framed chain (entry_aligned_framed, wloop_to_tail_framed
with framed straight/back/exit, tail_entry_framed, next{0..4}_framed, exit{0,1,2,3,5}_framed,
tdec_snez_framed, tail_to_done_framed, wattail_to_done_framed, strlen_aligned_spec_framed)
are WRITTEN and individually sound.  `envDefStrlenFramed` (EnvDefCompose) DISCHARGES the
`strlenFramed` premise from `strlen_spec_framed` modulo the named `hExitTick` residual.

**BLOCKER (single, deterministic): `exit4_framed` hits the 8M-heartbeat `whnf` timeout.**
`exit{0,1,2,3,5}_framed` are structurally IDENTICAL thin wrappers over the `exitk_framed`
generic (differing only in offset literals) and elaborate fine; `exit4_framed` (offset 4)
deterministically exceeds the `whnf` budget when the elaborator unifies the `exitk_framed`
application type at k=4.  Tried: term-mode (baseline), `refine … ?_` staged holes,
`attribute [irreducible]` on the generics — none resolved it (irreducible made the WHOLE
file ~2× slower; refine moved the timeout into the same application unification).

**Diagnosis = the tail is NOT built the exponentiating way.**  The per-offset `exitk_framed`
instantiation whnf's Sail-state `sigmaPost_*`/`Done`/`TDec` predicates (violates
fast-reflection rule 1 "reflect on a compact first-order write-log, never the Sail state"
and rule 3 "one small decide per block").  The CORRECT fix is to build the byte-tail via
the block-reflection framework (`#gen_block`/`BlockLogic`, which emits the frame as ONE
reflected write-log clause `∀ n ∈ wrRegsM block.body, gprReg n ≠ R`, checked by one small
`decide` — exactly `negProloguePost`'s pattern), so ALL offsets share one soundness lemma
and NO per-offset whnf.  That is a rebuild of the strlen byte-tail on block-reflection —
the genuine exponentiation work, beyond this session.

**Net:** the register-frame preservation LOGIC (clauses 2/3/4, + clause 5 via
`strlen_framed_mem_stable`) is proved and composed; clause 1 (tick) is the named
`hExitTick` residual in `envDefStrlenFramed`; the ONLY thing keeping the file from green is
`exit4_framed`'s elaboration cost, which needs the block-reflection tail rebuild, not more
proof.  EnvDefCompose's `envDefStrlenFramed` is written and will compile once StrlenSpec is
green.  `bridgeStrlenPre_closed`/`bridgeMallocPre_closed` are untouched (still green).

## strlen_spec_framed — GREEN + WIRED (2026-08-30, FINAL)

**RESOLVED.**  The `exit4_framed` "8M-heartbeat whnf timeout" was NOT an exponentiation
failure — it was a WRONG LITERAL: `exit4_framed` passed `takenimm = 0x0068` to the
`exitk_framed` generic, but `site_80006d54_taken` emits `sigmaPost_branch_taken … 0x0060`.
The `0x0068` vs `0x0060` mismatch forced the elaborator into a pathological `whnf`
unification search that exhausted the budget.  Fix: rebuilt `exit4_framed` self-contained
(inlined `beqz`-taken ≫ `addi` ≫ `ret`, `tdec_snez_framed` shape) with the correct
`0x0060` btaken immediate.  Lesson: a bad ground literal on a `sigmaPost_*` arg surfaces as
a whnf-heartbeat timeout, not a unification error — check literals first.

### Landed GREEN + axiom-clean
- `Vsa/Sim/StrlenSpec.lean` — `strlen_spec_framed : Triple (strlen_pre ∧ ghost)
  (strlen_post ∧ ghost)` where ghost = `∀R, AbiPreserved R → get? R = g R`.  Compiles
  clean; `#print axioms` = `[propext, Classical.choice, Quot.sound]` (no sorry/axiom/
  native_decide/bv_decide).  Full framed chain: `strlenFrame_{alu,btaken,bnottaken,jr}`
  (per-family AbiPreserved readbacks), `entry_aligned_framed`, `wloop_to_tail_framed`
  (framed `Triple.loop`), `tail_entry_framed`, `next{0..4}_framed`, `exit{0..5}_framed`,
  `tdec_snez_framed`, `tail_to_done_framed`, `wattail_to_done_framed`,
  `strlen_aligned_spec_framed`.  `strlen_framed_mem_stable` exposes clause 5's `mem = m0`.
- `Vsa/Sim/EnvDefCompose.lean` — `envDefStrlenFramed` DISCHARGES the `strlenFramed`
  premise from `strlen_spec_framed` + `hAInvStable`, reconstructing the full `EnvDefFrame`
  (x2=sp / x3=gp via the AbiPreserved tie against the entry-pinned `gm`; StackOK unchanged;
  AInv from `mem=m0` via `hAInvStable`) modulo the ONE named `hExitTick` residual.
  Compiles clean (1.6s).

### Clause status (of the 5 the composition needs)
- **2 (x2=sp+StackOK), 3 (x3=gp), 4 (callee-saved tie)** — CLOSED (the one ghost clause).
- **5 (AInv)** — CLOSED as a `mem=m0` corollary via `hAInvStable`.
- **1 (tick<2)** — the SINGLE remaining residual, exposed as the honest named premise
  `hExitTick` in `envDefStrlenFramed`.  `strlen_spec_framed`'s carrier is register-only;
  threading tick through the framed blocks (each site lemma already yields `i'<2`) is
  mechanical follow-up (add `∧ c.tick<2` to the block posts + final constructors — was
  attempted, reverted only because it interacted with the (now-fixed) exit4 literal bug).

### Consumers verified GREEN (serial `lake env lean`)
StrlenSpec (axiom-clean), StrlenSpecU (2.6s), EnvDefCompose (2.0s), EnvDefBridges (1.4s;
`bridgeStrlenPre_closed`/`bridgeMallocPre_closed` still green), StrcmpSpec (1.6s).
All changes ADDITIVE — no existing signature changed; `strlen_spec`/`strlen_post`/`Done`
untouched.  StrlenSpec olean regenerated.
