# Legacy-elimination plan: shrinking discipline_grandfather.txt to zero

647 files are grandfathered from the proof-discipline gate (2026-08-31). The
breakdown by rule shows most of the number is ONE artifact, and the honest
plan treats the tiers very differently — elimination means each file either
(a) exits by a config/rule fix, (b) is retired as no-longer-consumed, (c) is
re-seated on the exponentiating layer, or (d) is deliberately FROZEN under a
ratchet. "Rewrite all 647" is not the plan; most files should never be touched.

Measured breakdown (scripts/check_discipline.py rules over the current list):

| rule | files | what they actually are |
|---|---|---|
| R2 heartbeat-raise | 577 | 512 = GENERATED `DecodeTable/Batch*Part*` (uniform `set_option maxHeartbeats 16000000`, one per file, emitted by `gen_decode_table.py`); ~65 = hand files with raises (4000000 etc.) |
| R1 site-battery | 69 | the Layer-3 per-site StepObs battery families (Snprintf* 26, Strcmp/Strcpy/Memcpy/EnvGet/EnvDef/Value/Exec_stmt/Div sites) |
| R5 stepobs-volume | 43 | mostly overlapping R1 (hand-threaded chains) |
| R3 hand-abi-frame | 3 | StrlenSpec + MemcpySpecFramed (real) + FrameMeta (docstring FALSE POSITIVE) |

## Tier 0 — config/rule fixes (hours; 647 → ~130)

1. **DecodeTable heartbeats (512 files).** The value is uniform and
   generator-emitted; the rule's intent is "no ad-hoc raises", not "no
   generated grounding budget". Decide ONE of: (a) measure whether the decode
   lemmas actually need 16M (the build-speed campaign suggests they are the
   dominant build cost — if a lower uniform value passes, change the ONE
   generator constant and regenerate all 512); or (b) scope R2 to exclude
   `Vsa/Sim/DecodeTable/**` with a comment saying the budget is generator-owned.
   Either way 512 files exit the list via one change. Prefer (a): it is a real
   build-time experiment worth the hour.
2. **R3 false positive.** Make the checker comment-aware (skip `--`/`/-`
   content) or add the allow-marker in FrameMeta's docstring line. 1 file.
3. **Regenerate the grandfather list** after 1-2; assert in the gate that the
   list only ever SHRINKS (ratchet, see Enforcement).

## Tier 1 — retirement by subsumption (audit; days)

Files whose STATEMENTS are no longer consumed downstream: superseded pilots and
probes (`DecodePilot`, mul-wip captures, any `*Probe` whose slot-verify was
absorbed into check_all THEOREMS, orphaned experiments). Mechanics: import-graph
audit (who imports X; is any X-theorem in check_all or referenced) → delete or
move to `experiments/attic/`. Zero re-proof. Estimate: 10-30 files.

## Tier 2 — active-path re-seat (the only real rework; do it as-you-touch)

Families on the ACTIVE change path, where legacy idiom keeps breeding new
legacy (measured: 4 hand prefix-runs accreted in EnvDef* beside a fully-tabled
region): `EnvDefBridges*` (3), `EnvGetSites*`, `MemcpySites*` (4),
`Exec_stmtSites*` (3), `DivSites*` (2), the ~65 hand R2-raise files that are
also active (CmpBridges, BinopChain*). Mechanics per file: re-prove the SAME
statements via seg + FrameMeta + callSeg (`EnvDefSeg.lean` is the model,
58→14 lines; `bridgeOfSeg` once #28 lands), delete the battery, drop the
heartbeat raise, remove from grandfather. The mkBridge layer makes each
re-seat ~an hour of agent time; statements unchanged so consumers are
untouched and check_all is the correctness gate. Do NOT batch-rewrite ahead of
need — re-seat when a file is next touched (boy-scout rule, enforced by the
ratchet below), except the three files the open tasks already cover
(#11 strlen byte-tail, #15 word-route epilogue → retires the 2 real R3 files
and StrlenSpec's battery tail).

## Tier 3 — frozen terminals (deliberately NOT reworked)

The cold Layer-3 batteries: `SnprintfSpec*`/`SnprintfSites*` (26+),
`StrcmpSites`/`StrcpySites`, `ValueSites*`, etc. Green, terminal, consumed
only through their capstone specs, never edited. Re-seating is pure churn with
no downstream payoff unless a build-time measurement says otherwise. Plan:
FREEZE under the ratchet (a grandfathered file may not grow new violations),
and re-seat only if (a) the file must be edited anyway, or (b) a measured
elab-cost top-N list puts it above the line. Record the top-N measurement once
(reuse the stage-a2 elab-budget data) and revisit quarterly.

## Enforcement additions (make the plan self-executing)

Extend `scripts/check_discipline.py` (data-only where possible):

1. **Ratchet**: store per-file violation fingerprints (rule → count) in the
   grandfather file; a grandfathered file whose count GROWS fails the gate.
   This enforces boy-scouting without demanding rewrites.
2. **Shrink-only list**: the gate fails if a file is ADDED to
   `discipline_grandfather.txt` (additions require an explicit
   `-- discipline: allow(grandfather) <why>` review marker in the PR… i.e. a
   deliberate edit to the checker's allowlist, not a casual append).
3. **Retirement credit**: `check_discipline.py --report` prints the current
   count by tier/rule so progress is visible in every check_all run.

## Priority stance (2026-08-31)

This plan is NOT on the campaign's critical path. It runs only where it
increases proof-completion RATE: the Tier-0 DecodeTable heartbeat experiment
(a possible rebuild-speed win on the build's dominant cost — worth one slot,
measured before adopted) and Tier 2's as-you-touch re-seats (which happen
anyway through the campaign tasks). Tiers 1/3 and everything cosmetic wait
for post-campaign hygiene; the ratchet prevents rot meanwhile.

## Order and estimate

Tier 0 now (one session, -513 files). Tier 1 audit next quiet slot (-10..30).
Tier 2 rides the existing campaign tasks (#6 remaining bridges, #11, #15, #28
demo) — each front that lands removes its files (-15..20 over the campaign).
Tier 3 freezes (~90 files) — eliminated from RISK, intentionally not from the
list, unless measurement promotes them. End state: a grandfather list of only
frozen terminals with a ratchet, trending to zero as fronts retire them.
