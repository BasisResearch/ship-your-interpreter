# Wave 45 — segopacity lane (the 5 SegEntry-opacity ArmDispatch residuals)

HEAD at start: 80aab36 (wave 44). Lane brief: for each of the 5 remaining
dispatch residuals (`FlCondArmDispatch`, `FlBodyArmDispatch`,
`WhileBodyArmDispatch`, `ForInitArmDispatch`, `ArgsHeadDispatch`) determine and
(where tractable) land the discharge via the wave-43 `*ArmHeadInv` enriched-entry
model.

## Architecture map (what each residual actually is)

Every `*ArmDispatch` def is a terminal HYPOTHESIS (`h*Disp`) fed to
`divFamily_wave42` / `nonEvalChildStages_wave43_wired` in
`Vsa/Sim/ArmStagesWave34.lean`. Nobody supplies them — they are the open front.

Each `*_field_of_dispatch` theorem (already landed) reduces the residual to:
  `<entry predicate> → ∃ carrier pins. LandedN 0 c (ArmHeadInv …) ∧ StagePre`
where `StagePre` (the arm-head → child marshalling) is ALREADY landed
(`*BodyBridge`). So the ONLY open content in each of the 5 is:

    from the entry predicate, produce a machine run reaching the enriched
    arm-head bundle (`ArmHeadInv` / `ExecArmEntryK` / `CallArgLoopInv`).

`LandedN 0` = "a run of ≥0 steps"; it is a REAL machine run, `0` is a lower
bound only.

## Two sub-classes (the wave-44 observation lumped these; they differ)

### Class 1 — OPAQUE-entry (`SegEntry`): Args / FlCond / FlBody
- `AEntryC` / `FEntryC` = `InductionScaffold.SegEntry` ∃-pack at a ghost
  interior PC (`evalArgsLoopPC` / `forCondPC = 0x8000426c`).
- `SegEntry` fields (verified `InductionScaffold.lean:150`):
  `good, tick, pc, store, out, mem, frame(=AbiPreservedNoise→g),
   depth_budget, arena_budget`. THAT IS ALL.
- The arm-head bundle needs, e.g. for Args (`CallArgLoopInv`,
  `CallClosureSplice.lean:79`): `idx`(a6/x16), `argc`(a5/x15 = (e::es).length),
  `node`(s0/x8 = args-array base), `interp`(s2/x18), `env`(a3/x13), the head-arg
  `ExprRepr aHead e`, `slots`, `memFrame`, `bound`. **NONE of these is in
  `SegEntry`.** Note `AbiPreservedNoise` covers only callee-saveds, so a5/a6/a3
  (caller-saved arg regs) are not even ghost-pinned; and even s0/s2 are tied to
  the ghost `g`, not to the arg-array / interp SEMANTIC values; and `argc`
  (= arg count) and the head-node `ExprRepr` are pure arg-vector facts with no
  `SegEntry` source at all.

  → machine-grounded obstruction: `SegEntry → CallArgLoopInv` is
  NON-DERIVABLE. The missing facts must be threaded from the AEntryC PRODUCER
  (`CallArgsSegPreB.callArgs_field_of_dispatch`, which collapses the richer
  `CallArgsSetupInv@0x800031d8` down to a bare `SegEntry`, discarding them) or
  the `AEntryC` DEFINITION must be enriched (add the pins). FlCond/FlBody: same
  shape at `forCondPC`; FlCond additionally needs the full `ExecArmEntryK`
  register frame at `0x8000426c` (much richer than SegEntry's `frame`).

  CHECKED (brief item 3): the wave-43/44 crux marshal carriers
  (`CallCruxMarshal2-4`) are about the CALLEE param-define fold
  (`CallParamFoldInv`, closure body) — they do NOT produce `CallArgLoopInv`
  (the arg-EVAL loop head). So they do NOT supply what `ArgsHeadDispatch` needs.
  ArgsHead is NOT unblocked by the crux landings.

### Class 2 — RICH-entry (`ExecEntry`): WhileBody / ForInit
- `SEntryC` = `ExecEntry` (rich: full ABI a0..a3, `StmtRepr` of the WHOLE stmt,
  StackOK, store_survives) but AT `exec_stmt` entry `0x80003fe0`, at the
  whole-stmt granularity.
- The arm-head bundle (`WhileBodyArmHeadInv@0x80004074` /
  `ForInitArmHeadInv@0x80004248`) needs the SUB-node `StmtRepr` (body `b` /
  init, read via `ld a1,16(s0)` / `ld a1,32(s0)`), the body pins
  (`stmtWhileBodyL`/`stmtForInitBodyL`), and the POST-cond/POST-alloc store
  `st'` / `⟨store',…⟩`.
- The run entry→arm-head crosses: the while/for dispatch, a RECURSIVE
  `jal eval_expr` for the condition (While) or `jal env_new`/init-load (ForInit),
  the `value_truthy` nonzero test + taken branch (While), and the body-node load.
  The recursive cond result IS given as a hypothesis (`EvalE st d env cnd st' v`
  / `allocFrame …`), but the SURROUNDING machine spans
  (`SEntryC → cond-jal`, `value_truthy → 0x80004074`) are genuine UNBUILT M4
  arm-seg content — no landed seg spans `0x80003fe0 → 0x80004074` (grep-verified,
  no such seg/bridge/Steps in the tree).

  → this is not a carrier repackaging; it is the recursive-call arm span
  (cut at the recursive `jal`, `value_truthy`-branch join). That is
  divergence/loop-lane content, not a segopacity adapter.

## Verdict: 0 landed this wave. All 5 are genuine upstream gaps.

Landing a `struct Enriched*Entry` + `enriched → *Dispatch` adapter in
`rows/SegOpacity*.lean` would only RELOCATE the ∃-pack: the enriched carrier's
extra fields (argc, node/interp/env pins, head `ExprRepr`; or the recursive-span
Steps) are exactly the missing facts, and the enriched premise would need its
OWN producer with the SAME missing facts. That is content-preserving
repackaging (Law 3: "5 near-identical carriers = factor first / STOP") — and the
correct fix (enrich `SegEntry`/`AEntryC`, or thread the pins from the AEntryC
producer, or build the recursive arm spans) lives in files this lane does NOT
own (`ApproxArmReseat.lean`, `InductionScaffold.lean`, `CallArgsSegPreB.lean`,
the M4 arm segs). Reported as precise upstream gaps per Law 4; no file created,
no workaround forced.

## Per-arm upstream owner (wave-46 statement surgery targets)

| residual | entry | missing at arm-head | where to fix |
|---|---|---|---|
| `ArgsHeadDispatch` | `AEntryC`(SegEntry@0x800031dc) | argc / cnode / ip / envp pins + head `ExprRepr` | thread from `CallArgsSetupInv` through `callArgs_field_of_dispatch` (enrich `AEntryC` def, or add an `ArgLoopEntry` twin carrying `CallArgLoopInv`) |
| `FlCondArmDispatch` | `FEntryC`(SegEntry@0x8000426c) | `ExecArmEntryK` frame + cond payload at 0x8000426c | enrich `FEntryC` def to a for-cond-arm-head twin (à la `StmtWhileCondArmDispatch`'s ExecArmEntryK entry) |
| `FlBodyArmDispatch` | `FEntryC`(SegEntry@0x8000426c) | body pins + body-node `StmtRepr` + `st'` store | for-cond → truthy-nonzero → 0x800042a8 span (loop lane) |
| `WhileBodyArmDispatch` | `SEntryC`(ExecEntry@0x80003fe0) | recursive cond-eval + `value_truthy` branch + body-node load span to 0x80004074 | M4 while-arm seg (divergence/loop lane) |
| `ForInitArmDispatch` | `SEntryC`(ExecEntry@0x80003fe0) | env_new + init-load span to 0x80004248 | M4 for-arm seg (divergence/loop lane) |

## Wiring: NONE (no file created).
