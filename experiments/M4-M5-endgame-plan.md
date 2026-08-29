# M4/M5 endgame — current discharge plan (2026-08-27)

Supersedes the stale ownership ledger in `exponentiation-plan.md`; that doc still holds for the
STRATEGY (the L0–L8 abstraction stack) and the coordination protocol. This one is the CURRENT,
grounded state + sequencing after the elab-wall P1 campaign closed the eval-arm cohort.

## Where we actually are

- **The whole L0–L8 stack is BUILT and axiom-clean.** GeomFacts (L0, 0 real sorry), SegEval (L1),
  FrameCalc (L2), `#derive_case` (L3), LoopStep (L4), HeapOps/ReallocSpec (L5), ErrorSites (L6).
- **The final theorem is ASSEMBLED, conditional on a named residual bundle:**
  `interpSim_conditional L hterm hstuck : InterpSim L` (via `term_sim_of_cases` + `errorSimFull` +
  the DivergeSim/stuckSim structure). So this is DISCHARGE, not construction.
- **The eval-arm case rows are DONE** (elab-wall P1): gt/le/lt/add/sub EvalE + andTrue/orFalse logical,
  all block-reflection-assembled, green + axiom-clean. These are hand-written block-reflection rows
  (`blockC_*` + `EvalXChain.lean`), NOT `#derive_case` one-liners.

## The strategic split (the key finding — read before picking work)

`#derive_case` (L3) reaches **straight-line segments only** — it is used for M5 error-site bodies
(`ErrorSiteRows`) and the env_define grow block. It does NOT reach the **recursive/marshalling** M4
arms; those need the IH-threading glue (`EvalRecCommon`/`ExecRecCommon` + `armTail_rec`) that the
eval-arm and logical rows use by hand.

**Consequence for sequencing.** The exponentiation payoff (many trivial `#derive_case` one-liners) is
REAL for the ~29 remaining M5 error-sites (straight-line, N-way parallel fan-out). It is NOT the right
tool for the FEW remaining recursive M4 cases (call/closure/assign) — those are cheaper hand-threaded
with the proven `armTail_rec` glue than by extending `#derive_case` to recursion. Do not invest in
recursion-in-`#derive_case`; spend the effort on the handful of hand cases + the close.

## Remaining residuals — NAMED `Prop` HYPOTHESES, not sorries

**There are ZERO real `sorry`/`axiom` anywhere in `Vsa/Sim`** (every grep hit is the word "sorry"
inside a `NO \`sorry\`` prohibition docstring). The whole tree is GREEN and CONDITIONAL:
`interpSim_conditional L hterm hstuck : InterpSim L` is a complete theorem; each landed case Triple is
green *modulo* named `Prop` hypotheses it carries (`CallArmSpec`, `NativeAssertOkSpec`, `FnArmSpec`,
the closure body spec, the 42 error-site specs, `Trichotomy`, `DivFamily`, `GeomFacts`-from-`Layout`,
`HeapArena`). **The work is writing theorems that DISCHARGE those hypotheses**, then threading them
into `hterm`/`hstuck` and instantiating `interpSim_conditional` to an unconditional `interpSim L`.

Obligation clusters (all green-conditional today):
- **M4 call subsystem** — `EvalCall`(CallArmSpec), `EvalCallNative{,2,3}`(NativeAssertOkSpec + closure),
  `EvalCallPrint`(print/println output-append), `CallEntry`.
- **M4 recursion glue** — `EvalRecCommon`/`ExecRecCommon` (`EvalExit→EvalExitD` shape-gap).
- **M4 entry bridge** — `TermEntry` (`hEntryHalts`).
- **M5 error** — `ErrorSiteRows{,2}` (~29 of 42 site specs remain), `ErrorSim`, `ErrorTail`.
- **M5 divergence/trichotomy** — `DivergeSim`, `Trichotomy`.
- **The close** — `TermSimClose`/`StuckSimClose`/`InterpSimFinal`/`LayoutInstance` (thread + instantiate).

L5 `EnvDefineClose`/`ReallocSpec` is landed (the realloc blocker is GONE per the module header), so the
env_define contract the closure crux needs is available to compose.

## Plan — sequenced waves (dependency-ordered)

### Wave 0 — de-risk the crux — ✅ SUBSTANTIALLY DONE (2026-08-27)
`hCallClosure` (Call.closure arm). **Verdict: the crux is ONE focused session away; no new foundational
piece needed.** Landed green + axiom-clean in NEW file `Vsa/Sim/EvalCallClosure.lean` (not yet in
Vsa.lean/check_all.sh):
- **`callClosureSim`** — the crux as a machine `Triple (CallEntryP)(CallExitP)`, composing
  `prefix ≫ body-IH ≫ return` via `Triple.seq`. `#print axioms = {propext,Classical.choice,Quot.sound}`,
  **0 decide / 0 omega / 0 carries** (pure structural composition — constant elab cost). Verified to
  discharge the real `hCallClosure` premise (TermSimAssembly.lean:243) after unfolding `mCall`/`mExecSeq`;
  the recursive body IH instantiates cleanly (recursion fully absorbed by the given `mExecSeq` IH — the
  block-statement-arm analog, no extra recursion proof).
- The residual is now **two straight-line seam specs** (named like `callAssertOk`'s `NativeAssertOkSpec`):
  `ClosureEntrySpec` (prefix: closure-branch + arity + depth-guard `blt 1000` + `jal env_new`=allocFrame
  + `env_define` param-bind fold) and `ClosureRetSpec` (return: status classify + `--call_depth` +
  `value_null`/24-byte body-sret→CALL-sret copy). Both block-reflectable machine runs.
- Decoded seam PCs: `callDispatchPC=0x80003254`, `callBodyLoopPC=0x80003354`, `callBodyRetPC=0x80003378`,
  `callJoinPC=0x800033ec`. Canonical bound-store normal form: `closureBoundStore`/`closureBoundSt`.

**Next for the closure finish (Wave 0b):** the single blocking sub-goal is `ClosureEntrySpec`'s
`env_define` param-bind fold. `EnvDefineClose`/`ReallocSpec` provide the *extent/ledger algebra* but NOT
yet a machine-level `env_define` Triple. Build **one `env_define_spec`** (single iteration:
`jal env_define(frame,name,pv)` → `StoreRepr (store.define frame x v)`, composing `ReallocOps`), fold it
over `params.zip vs` with a small `Triple.seq` induction (measure = remaining params; simpler than
`execSeqLoop` — no abrupt exit). Then `ClosureEntrySpec` prefix + `ClosureRetSpec` are block-reflection
rows (arity/depth/env_new sites 0x80003288–0x800032c0; return is one `value_null` / one 24-byte copy,
both already-specced primitives). Coordinator: wire `import Vsa.Sim.EvalCallClosure` once the two specs land.

### Wave A — parallel, independent (start alongside Wave 0)
- **A1 (rec-glue):** close the `EvalExit→EvalExitD` shape-gap in `EvalRecCommon`/`ExecRecCommon` — this
  unblocks the 5 leaf EvalE re-landings and every recursive arm's exit marshalling.
- **A2 (M5 error fan-out):** the ~29 remaining error-site rows via `#derive_case` — genuinely N-way
  parallel (one file per site under `rows/`, worktree isolation, ≤2–3 concurrent per the protocol).
  This is where the exponentiation multiplier pays; each row is a constant-cost one-liner.
- **A3 (divergence/trichotomy):** `DivergeSim` + `Trichotomy` — classical (`Classical.em` + fuel fold),
  disjoint from everything else, one dedicated agent.

### Wave B — needs Wave 0 + A1
- `hAssign` (native-store), the mechanical-pending binary ops still open (eq/ne/mul/div/mod EvalE) as
  block-reflection rows cloning the gt/add recipe, `hEntryHalts` (program-entry bridge in `TermEntry`).

### Wave C — the close (needs all rows)
- Instantiate `term_sim_of_cases` / `errorSimFull` with the discharged cases → `TermSimClose` /
  `StuckSimClose` conditional only on `{GeomFacts, HeapArena}`.

### Wave D — M6 Layout + final (needs Wave C)
- `LayoutInstance`: read the concrete `Layout L` off the binary, provide the one `GeomFacts` + `Loaded`
  facts; `InterpSimFinal`: `Vsa.Refine.refinement (termSimClose …) (stuckSimClose …)`;
  final `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Gates (every commit)
- `scripts/check_all.sh` green; axioms ⊆ {propext, Classical.choice, Quot.sound}.
- **Deterministic elab gate (not wall-time — the host is too noisy):** the touched file's
  `decide`/`omega`/`obs_*_other` counts must not regress; a `#derive_case` row is a one-liner by
  construction. (See `memory/elab-wall-diagnosis.md` for why wall-time is unreliable here.)
- Migration invariant: keep the hand proof until the new row is green, delete in the same commit.

## Coordination
Per `exponentiation-plan.md`: one NEW file per agent under `Vsa/Sim/rows/`; specific `git add` (never
`-A`); coordinator integrates `Vsa.lean`/`check_all.sh`; PARALLEL fan-out only with `isolation: worktree`,
bounded ≤2–3 concurrent (process-table saturation is per-machine). SERIAL for build-heavy spine work.

## Definition of done
`InterpSimFinal.interpSim L : InterpSim L` unconditional, `#print axioms` clean, full `lake build Vsa`
green.
