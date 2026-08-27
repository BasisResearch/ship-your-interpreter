# Resume plan — after machine restart (2026-08-25)

## STATUS UPDATE (2026-08-25, later): STEP 0/1/2 DONE
- Env recovered, Cli restored, full tree green, check_all OK.
- **STEP 1 DONE (commit 6b4f7cb):** NegTailSites wired + committed.
- **STEP 2 DONE (commit 745bc76):** `blockC_neg` proven end-to-end in
  `Vsa/Sim/EvalNegSim2.lean`, wired into Vsa.lean, axioms ⊆
  {propext, Classical.choice, Quot.sound}, full tree + check_all green. WIP
  file deleted. See memory/m4-recursive-cases.md "blockC_neg DONE" for the
  design (entry-ghost bridge, value_int composition, survival) + the premise
  residuals to discharge when composing `evalNegSim`.
- REMAINING: compose evalNegSim (blockA_k widening + gpre→g bridge discharge +
  EvalExitD upgrade of blockD_v), then STEP 3 (writeLog) + STEP 4 (python LSP
  driver) below, then the rest of M4–M6.

---
# ORIGINAL PLAN (below, for STEP 3/4 + M4–M6 reference)


Machine restart needed: process table saturated (fork failures) from over-parallel
subagents + accumulated LSP `lean --worker` processes, AND lake wants to re-clone the
`Cli` dependency (git exit 128 — `.lake` state churned by concurrent `lake build` runs).
Root cause of BOTH: too many parallel subagents each spawning `lake`/`lean`. Restart
clears the process table; the steps below fix the lake state.

## Last known-good state
- **Committed + pushed: `f62aaa8`** on `origin/main`. Green, `check_all.sh` was passing
  (43+ theorems, axioms ⊆ {propext, Classical.choice, Quot.sound}). This includes all of
  M1–M3 (snprintf `%lld` ∀-v: `snprintf_lld_total_spec`), the full tooling stack, the
  reflection layer (BlockPilot/BlockMem/BlockTerm), the wrap64 semantics amendment, the
  FrameOn/SnprintfPost/WriteLogNF statement-size layer, and SnprintfRecords.
- **Working tree (UNCOMMITTED) at restart:**
  - `Vsa.lean` — has `import Vsa.Sim.NegTailSites` added (uncommitted).
  - `Vsa/Sim/NegTailSites.lean` — NEW, 17 neg-tail StepObs sites, reported green by the
    agent but NOT yet verified in-tree (blocked by the Cli re-clone issue).
  - `experiments/wip/EvalNegSim2.lean.wip` — quarantined WIP: `blockC_neg` with a `sorry`
    (setup lemmas proven incl. `neg_wrap_bridge`; first 4 machine steps written; ~9 remain).
  - `experiments/wip/WriteLogDemo.lean.wip` — quarantined: defeq-overflow bug (see Q1 below).
  - `opencode.json` — untracked local config, leave alone.
- **No `sorry` is in the buildable tree** (both WIP files quarantined out of `Vsa/Sim/`).

## STEP 0 — environment recovery (do first, in order)
```
echo ok                              # confirm fork works
pkill -9 lean; pkill -9 lake         # clear any stray workers
git status --short                   # see the uncommitted state above
git diff lake-manifest.json          # <-- LIKELY THE CLI FIX:
git checkout lake-manifest.json      #     restore the committed manifest if it was churned
lake build Cli                       # restore the dep (package is in .lake/packages/Cli)
lake build                           # full tree — confirm f62aaa8 + working tree is green
bash scripts/check_all.sh            # axiom audit
```
If `lake build Cli` still tries to clone and there's no network: the package dir
`.lake/packages/Cli` already exists; the churned manifest is the cause — `git checkout`
of `lake-manifest.json` (and possibly `.lake/`-state) is the fix, not a network fetch.

## STEP 1 — decide NegTailSites
- If `lake build Vsa.Sim.NegTailSites` is green → keep it wired, `git add Vsa.lean
  Vsa/Sim/NegTailSites.lean`, commit ("M4: neg-tail StepObs site battery (NegTailSites)").
- If it does NOT build → `git checkout Vsa.lean` (un-wire) and fix NegTailSites before
  committing. Do NOT commit unverified.

## STEP 2 — finish M4 `blockC_neg` (the frontier)  [SERIAL, one build at a time]
Source: `experiments/wip/EvalNegSim2.lean.wip` (move back to `Vsa/Sim/EvalNegSim2.lean`)
+ handoff in `memory/m4-recursive-cases.md`. The design is COMPLETE:
- `neg_wrap_bridge` (PROVEN): `(BitVec.ofNat 64 (0#64 - n_bv).toNat).toInt = wrap64 (-n)`
  given `n_bv.toInt = n`. Chain: `ofNat_toNat_self64` (`simp [BitVec.setWidth_eq]`) →
  `BitVec.zero_sub` → `← hn` → `unfold wrap64` → `BitVec.ofInt_neg, BitVec.ofInt_toInt`.
- Path 0x800035ec→0x800039dc: lw op-token / li 12 / ld / **beq TAKEN** (op=neg=12) →
  0x800039ac: ld/ld/lw kind / 3 error-staging sd's (land sp-848/840/832, disjoint from
  spills+sret+code, survive via SubEvalReturn StoreRepr `[SL.lo,SL.hi)` clause) / li a2,2 /
  lw s0 / **bne NOT-taken** (kind=VAL_INT=2) / **neg** (=`sub x11,x0,x11`, use
  `site_800039d0_ee`) / mv a0,s1 / **jal value_int** (`value_int_spec`, ValueSpec.lean:542,
  pay = `0#64 - n_bv`, bridge via `neg_wrap_bridge`) / j 0x800033ec.
- Statement: `blockC_neg : Triple (SubEvalReturn … 0x800035ec)
  (PreEpilogueV … (.int (wrap64 (-n))) 0x800033ec)`. Entry extras: `gpre x8 = some aExpr`,
  `ExprRepr … aExpr (.unary .neg esub)`, + 3 disjointness hyps (aExpr node vs sub-frame ∪
  arena ∪ subsret-window). Output feeds `blockD_v` unchanged.
- Then compose `evalNegSim := blockA(dispatch) ≫ blockB_unary ≫ blockC_neg ≫ blockD_v`
  in the InductionScaffold `EvalIH`-parameterized motive shape.
- All 17 sites are in `NegTailSites.lean`. `read64_bytes`/`word8_toNat_recon`/`sext_full`
  in ValueTruthySpec.lean. Gotchas: neg=RTYPE sub; beq/bne via ValueTruthySpec
  value-equality (`(ofNat tok == 12#64)=true` by decide after pinning); dead padding bytes
  read via MemExtends presence-existential; outermost-first store peeling; PtrArith (never
  simp[toNat_add,toNat_ofNat]+2^64-K+omega); trust `lake build` over editor LSP.
- DISCIPLINE: `pkill -9 lean` before each `lake build <mod>`; NO parallel subagents.

## STEP 3 — writeLog fix (Q1, user asked — the abstraction IS worth making usable)
`WriteLogDemo` failed because it asserted `writeMap8³ = writeLog … := hmem'` by defeq over
`Std.ExtHashMap` (not definitionally reducible per Layer-0 → stack overflow). FIX:
- Add to `WriteLogNF.lean` a PROVED bridge:
  `writeMap8_chain_eq_writeLog : writeMap8 (writeMap8 (writeMap8 m a₁ d₁) a₂ d₂) a₃ d₃
     = writeLog m [(a₁,8,d₁),(a₂,8,d₂),(a₃,8,d₃)]` by `simp only [writeLog, applyW,
  List.foldl]` (unfolds the fold once per entry — terminates; NOT defeq).
- BETTER: make `block_mem_sound` (BlockMem.lean) CONCLUDE in `writeLog` form directly
  (it already computes `wlogM`), so no bridge is ever needed and every block post is
  writeLog-shaped for free.
- Then restore `experiments/wip/WriteLogDemo.lean.wip` → `Vsa/Sim/WriteLogDemo.lean`,
  replace the `:= hmem'` ascription with the proved bridge, build green, wire, commit.

## STEP 4 — the strategic tooling shift (Q2, user asked): python Lean-LSP driver
The proofs are highly patterned (6 shapes: StepObs / straight-line-thread / branch /
call-glue / spill / frame). ~78% of a case is mechanical. Build a **python Lean-LSP
client** (use `leanclient` or the `lean-lsp-mcp` project which expose `$/lean/plainGoal`
+ diagnostics — the LSP tool in THIS harness is query-only and insufficient) that closes
an emit-and-fix loop on the MECHANICAL + GLUE layers (goal-state → pick discharging lemma
from a fixed menu → retry on error). Claude reserved for DESIGN + novel lemmas
(decomposition, invariants, `neg_wrap_bridge`) + orchestration.
- WHY it's the right move: faster + cheaper + more reliable than Claude hand-threading
  40-hypothesis blocks, AND **one persistent LSP server + one python driver has a far
  smaller process footprint than N parallel lake-spawning subagents** — it directly
  prevents the saturation that forced this restart.
- Note: the reflection block lemma (`block_mem_sound`) is already SUPERIOR automation for
  the straight-line layer (one kernel computation, no search) — target the driver at the
  GLUE/composition seams, not the threading the block lemma already handles.

## RESOURCE DISCIPLINE (the hard lesson — do not repeat)
- **SERIAL only.** At most ONE subagent at a time. NEVER run parallel `lake build`
  (concurrent access corrupts `.lake` → the Cli re-clone breakage seen here).
- `pkill -9 lean` before each build; watch `pgrep -x lean | wc -l`.
- Prefer main-loop bounded work or the LSP driver over subagent fan-out.

## Remaining plan (M4–M6, per PLAN-InterpSim.md)
- **M4:** finish `blockC_neg`→`evalNegSim` (neg); re-land 5 leaf cases at the widened
  `EvalExitD` exit (shared motive); binary/assign/logical/call arms (each = `armTail_rec`
  instantiation(s) + tail; binary uses it TWICE + `eval_binary`, wrap64 covers its
  overflow via `wrap64_tdiv_min`/`_tmod_min`; assign = `armTail_rec` + `env_set`); then
  the mutual recursor / `term_sim`.
- **M5:** error judgment (`EvalErr`/`ExecErr` mirroring runtime_error sites), fuel-indexed
  `Approx` trichotomy (classical), divergence simulation → `stuck_sim`.
- **M6:** concrete `Layout` instantiation — `ImageStaticsLoaded` (Code/ImageStatics.lean +
  ImageDischarge.lean) is the STATICS half (DONE); build a `scripts/gen_layout.py` for the
  GEOMETRY half (stack/arena/entry constants from the ELF) mirroring `gen_image_pins.py`;
  plug `term_sim`/`stuck_sim` into `Vsa.Refine.refinement`; final `#print axioms` audit
  (must show only propext/Classical.choice/Quot.sound).

## Git commits this session (for reference)
c178009 Specs17-55+tooling · 6270bd6 plan appendix · a336728 statement-size layer ·
98ac530 M4 pilot · 4279c65 wrap64 · 58194a6 Spec26 FrameOn · 8da7305 terminators ·
f62aaa8 SnprintfRecords (HEAD)
