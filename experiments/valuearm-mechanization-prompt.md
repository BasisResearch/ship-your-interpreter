# Value-arm mechanization brief — Phase 0 (hog) + Phase 3 (item-1 gen) + Phase 4 (tail gen)

Implementer prompt for mechanizing the whole binop value-arm family (div, mul, mod, eq,
ne) behind two generators, without increasing elaboration time. Hand to an implementer
agent (or split per phase). Assumes `chain_frame_out` (Part A) is already landed green.

```
Lean 4 repo /Users/kirancodes/Documents/code/verified-semantic-abstraction (branch main).
Machine-checked proof a compiled RISC-V binary implements a source interpreter. NO Mathlib.
Do NOT commit.

PRIME DIRECTIVE: mechanize the binop value-arm family (div, mul, mod, eq, ne) behind two
generators, and REDUCE elaboration time, not increase it. "Scalable, fast, efficient" is the
acceptance bar. A green-but-slower result is a FAILURE.

TWO HARD GATES, checked at EVERY phase boundary:
1. `bash scripts/check_all.sh` = `check_all: OK` (full build; no sorry/native_decide/bv_decide/
   axiom; axiom audit only [propext, Classical.choice, Quot.sound]).
2. No elab regression: every capstone elaborates in ≤ its recorded baseline; generated arms ≤
   the (post-Phase-0) hand arm. Prove it with a before/after table.
NEVER leave the tree red between phases. If a phase can't complete, revert/guard it green, log
the blocker in experiments/valuearm-mechanization-log.md, and CONTINUE to the next independent
phase.

PREREQ ALREADY LANDED (verify green at start):
- Vsa/Sim/ChainFrameOut.lean `chain_frame_out` (folds StepFrameOut across a site run).
- experiments/valuearm-elab-baseline.md — the STEP-0 baseline table (blockC_mul/blockC_div/
  evalMulSim/evalDivSim elab ms+heartbeats). If missing/stale, regenerate FIRST with
  `set_option profiler true in` + `#count_heartbeats in`.
- Vsa/Sim/StepFrameOut.lean, Vsa/Sim/rows/IntPostEpilogue.lean `intPostToEpilogue`,
  Vsa/Sim/rows/EvalMulRow.lean `blockC_mul`/`evalMulSim`, Vsa/Sim/rows/EvalDivRow.lean
  `blockC_div`/`evalDivSim`.
- Strong callee specs: divdi3_spec/moddi3_spec (DivSpec3), muldi3_spec (Muldi3Spec),
  value_equal_spec_full (ValueEqualSpec4); boxes value_int_spec (ValueSpec),
  value_bool_spec_full (EvalBoolSim). Values binOpSem_{div,mod,mul}_int / binOpSem_{eq,ne}.
- Dispatch segs: DivDispatchSeg/ModDispatchSeg/EqNeDispatchSeg (rows exist: DivDispatchPost/
  ModDispatchPost/EqDispatchPost/NeDispatchPost). Item-1 for DIV only: evalDivChain_run +
  evalDivChain_dispatch (EvalDivArm.lean). mod/eq/ne have NO entry-linkage chain yet.
- Tooling: scripts/gen_sites.py + per-op tsv → StepObs batteries; scripts/decode_index.tsv;
  the metaprogram family #derive_case/segToTriple (DeriveCase/DeriveCaseRow), seg_frame_facts
  (SegFrameFactsAuto), callSeg. Read the memory memos `fast-reflection-rules` and
  `elab-wall-diagnosis` — their laws are binding.

Keep a running progress log in experiments/valuearm-mechanization-log.md (phase, what landed,
elab numbers, hogs found+killed). It must survive across phases.

════════════════════════════════════════════════════════════════
PHASE 0 — KILL THE ARM-TAIL omega HOG (prerequisite; before any generation)
════════════════════════════════════════════════════════════════
The profiler shows `blockC_mul` (EvalMulRow.lean) spends ~20-30s across DOZENS of `omega` calls
at 0.5-1.1s each — the per-site geometry side-conditions (address bounds `0x80000000 ≤ addr`,
`addr+w ≤ 0x100000000`, htif-disjointness, `%4/%8` alignment) re-solved by `omega` at EVERY
load/store site. `blockC_div` has the same tax. If the generators clone this, they multiply the
hog x5. Kill it FIRST.
- Diagnose: `set_option profiler true in` + phase markers; count the omega calls and their
  inputs. They almost all reduce to a handful of distinct address facts derived from the
  StackLayout/GeomFacts/sp offsets.
- Fix (follow `elab-wall-diagnosis`, which cut gt/le/lt 3-6x the same way): precompute each
  distinct geometry fact ONCE as a named lemma (from GeomFacts/ObjGeom/the SL bundle), and have
  every site consume it by `exact`/`rfl`, NOT re-`omega`. Where a site needs `(v2+off).toNat`
  bounds, derive a single `off`-parameterized helper instead of inlining omega per offset.
  Reflect on the first-order write-log / addresses, never whnf the Sail state.
- Target: blockC_mul/blockC_div elab drop materially (aim ≥2x) with ZERO omega calls >~200ms
  remaining. Re-measure vs baseline; record the win. Keep evalMulSim/evalDivSim green +
  axiom-clean.
- GATE: check_all OK; new blockC_mul/blockC_div numbers logged and lower.

════════════════════════════════════════════════════════════════
PHASE 3 — `#derive_binop_item1`: the entry-linkage + dispatch generator
════════════════════════════════════════════════════════════════
The entry linkage `evalXChain_run` is a VERBATIM clone of evalGeChain_run/evalDivChain_run
(shared 16-step dispatch prefix + `jr@0x80003558` jump-table routing) swapping only FOUR data
points: op token, jump-table index, jump-table slot address, arm PC. All binops route through
the SAME table at 0x80003558; only (index→target) differs, read from the binary's table bytes.
- Build a command/elaborator `#derive_binop_item1 <op> <token> <jtSlotAddr> <armPC>` that emits:
  (a) `evalXChain_run` (reuse the shared gtChainB1/B2a/B2b bodies verbatim; swap the 4 points)
      with the per-op slot-routing `decide` (the divSlot_routes analogue: the table bytes route
      `jr` to `armPC`);
  (b) the STRONG `XDispatchPost` (the UNIFORM conjunct set div's post got: `∃x12/x13`,
      `tick<2`, `sailOutput=out0`, callee-saved frame `∀R,AbiPreservedNoise R→x8≠R→regs=gpre R`)
      — generate it, don't hand-write;
  (c) the `evalXChain_dispatch` glue = `evalXChain_run ≫ XDispatchPost_of_chainEnd` where the
      chain-end→dispatch step reuses seg_frame_facts/SegFrameFactsAuto on the op's existing
      dispatch seg (the divDispatchPost_of_chainEnd/divDispatchRow_frame pattern, parameterized).
- VALIDATE on div: regenerate evalDivChain_run/evalDivChain_dispatch/DivDispatchPost via the
  generator; confirm defeq-or-interchangeable with the hand ones and evalDivSim stays green, at
  ≤ baseline elab. If slower, isolate (dbg_trace+IO.monoMsNow markers; profiler does NOT flush
  on timeout) and fix before proceeding.
- GENERATE item-1 for mod/eq/ne from their dispatch segs (ModDispatchSeg/EqNeDispatchSeg).
  Author each op's jump-table slot/token/armPC from the binary (grep the Eval_expr code image /
  existing seg headers). Land evalModChain_dispatch/evalEqChain_dispatch/evalNeChain_dispatch +
  their strong DispatchPosts.
- GATE: check_all OK; item-1 present for all 5 ops; elab of each ≤ the div item-1 baseline.

════════════════════════════════════════════════════════════════
PHASE 4 — `derive_binop_all`: the tail generator + fan-out
════════════════════════════════════════════════════════════════
Elaborator that, from a per-op descriptor, emits `blockC_<op> : Triple (XDispatchPost-ish ∧
arm-bundle) (PreEpilogueVD … boxedValue …)` reproducing the FAST (post-Phase-0) hand tail:
apply `evalXChain_dispatch` (Phase 3) → `jal callee` site → strong callee_spec (build `_pre`
from the concrete config; `g := fun R => τ.regs.get? R` snapshot, `o := sailOutput`) →
`mv;mv;(seqz for ne);jal box` sites → box_spec (value_int for div/mod, value_bool for eq/ne;
`g := snapshot`) → `ld;j` sites → `chain_frame_out` collapse → `intPostToEpilogue` (int box) /
`boolPostToEpilogue` (bool box) with the op's binOpSem_* value.
- Descriptor = a plain Lean structure literal (NOT a stringly DSL): token; callee spec + its
  pre/post + entry/return PCs; box ∈ {int,bool}; seqz?; produced-value lemma; tail site-battery
  module. Author each op's tail tsv (mirror divtail_sites.tsv), run gen_sites.py, get the battery.
- WHY this can exist where `divValueTail` couldn't: the elaborator builds the proof INLINE and
  reads `g` off the concrete post-callee/post-box config, so int_pre/boxBool_pre's frame is
  `rfl`; it never exposes `g` as a fixed shared premise. Do NOT reintroduce a fixed-ghost Triple
  combinator (see experiments/binop-value-tail-wiring.md VERDICT).
- PERF LAWS (binding): emit PLAIN TERMS (flat application, not a deep tactic block); one small
  `decide` per block composed at term level, never a monolithic arm-wide `decide`; canonical
  normal form so seams close by `rfl`; NO per-site omega tax (consume Phase-0's precomputed
  geometry lemmas); structural not well-founded recursion.
- VALIDATE on div/mul: generate blockC_div/blockC_mul, swap the hand ones out, keep evalDivSim/
  evalMulSim green, elab ≤ the POST-PHASE-0 hand numbers. Isolate any hog (phase markers around
  dispatch/callee/box/collapse/marshalling) and remove before fan-out.
- FAN OUT: generate blockC_mod/blockC_eq/blockC_ne; compose evalModSim/evalEqSim/evalNeSim =
  `blockB_binary ≫ blockC_<op> ≫ blockD_v_rec` (Phase-3 item-1 on the front, shared blockD on
  the back). ne inserts `seqz` in box-staging; eq/ne use boolPostToEpilogue (the value_bool
  sibling of intPostToEpilogue — build it if absent) + value_equal_spec_full.
- GATE: check_all OK; all 5 evalXxxSim green + axiom-clean; every generated arm ≤ its
  post-Phase-0 hand baseline.

════════════════════════════════════════════════════════════════
CONTINUOUS HOG PROTOCOL (apply after EVERY new capstone, not just at gates)
════════════════════════════════════════════════════════════════
- Diff each new decl's elab (profiler + #count_heartbeats) vs baseline. >10% over its hand
  analogue, or any single leaf omega/simp/decide >~1s (>~200ms in the generated hot path), =
  HOG: STOP, isolate, remove before continuing. Never accumulate a slow arm to "optimize later".
- Locate hogs by binary-searching with `dbg_trace s!"{(← IO.monoMsNow)}"` markers INSIDE the
  metaprogram (trace.profiler does NOT flush on a heartbeat timeout; the cumulative-beat timeout
  lands wherever the 1M-th beat falls, shifting with instrumentation — trust markers, not the
  error line).
- Pre-empt the known hogs: whnf'ing a writeLog/stepMemM fold (reflect on the write-log, not Sail
  state); `decide` over an open keysG/ChainOK (use `show <closed>; decide`); monolithic
  register-frame decide (chain_frame_out avoids it); per-site geometry omega (Phase 0 killed it —
  don't reintroduce in the generator); typeclass search for geometry (project a record).
- Enforce a per-file elab BUDGET; a generated file materially slower than the hand arm it
  replaces is a regression even if green — fix it.

════════════════════════════════════════════════════════════════
FINAL DELIVERABLE (in experiments/valuearm-mechanization-log.md + final message)
════════════════════════════════════════════════════════════════
(1) Baseline vs FINAL elab table (ms + heartbeats) for blockC_{div,mul,mod,eq,ne} +
eval{Div,Mul,Mod,Eq,Ne}Sim, showing Phase-0 speedup AND no generated-arm regression.
(2) `#derive_binop_item1` + `derive_binop_all` APIs (descriptor schema, how class dispatch /
ghost-snapshot / geometry-lemma reuse work). (3) which arms are generated vs hand-built.
(4) every hog found + how removed (with numbers). (5) final check_all tail (OK + audited count)
+ `#print axioms` on the 5 evalXxxSim (must be [propext, Classical.choice, Quot.sound]). Add all
new capstones to scripts/check_all.sh with provenance. Leave GREEN. Do NOT commit.

SEQUENCING (strict; each phase green before the next): verify prereqs green → PHASE 0 (kill omega
hog, measure) → PHASE 3 (item-1 generator, validate on div, fan to mod/eq/ne) → PHASE 4 (tail
generator, validate on div/mul, fan to mod/eq/ne) → final table. Between phases, run full
check_all. If blocked on a phase, log it and do whatever later phases are still independently
reachable.
```
