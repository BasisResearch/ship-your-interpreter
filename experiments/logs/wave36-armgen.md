# Wave 36 — the blockA_*Arm dispatch-bridge GENERATOR + exec packaging audit

## Deliverable 1: `scripts/gen_arm_bridge.py` (the blockA_*Arm emitter)

Compiles a per-arm `.toml` → the `blockA_<name>Arm` bridge theorem: the
op-independent prologue+dispatch multiplier `EvalEntry <node> → blockB_*_stagePre`
entry bundle (an `ArmEntryK`-post + geometry conjuncts). GENERALIZES the two hand
instances in `rows/UnaryLogicalArmBridge.lean` (blockA_unaryArm tag-8,
blockA_logicalArm tag-7).

### Input row shape (TOML)
- top: `name, namespace, tag, armPC, callee (calleeLoaded predicate), node_pat,
  node_binders, x13_reach (bool), imports, doc`
- `[extras]` : `name, binders, body` — the `<Name>ArmExtras` structure (verbatim)
- `[triple]` : `thm_binders, triple_pre?, post` — the Triple pre/post (verbatim)
- `[proof]`  : `intro, slot_field, kind_read, callee_loaded_arg, callee_surv,
  operand_addr, armentryk_realign, extra_haves, refine_head, refine_tail` — the
  genuinely-per-arm Lean fragments (quoted once).

The emitter AUTO-GENERATES the invariant 90% (the `blockA_k` invocation with tag/
armPC/callee literals substituted, the `EvalEntry`-destructure `⟨⟨hc.good,…⟩,rfl⟩`,
the 47-way `ArmEntryK` copy destructure, the single-operand `m0→ment` pointer
transport with its 8 `read64_bytes`/`hMentM0` rewrites, the `out0` realign, and the
`#print axioms`). The per-arm Lean (callee-survival block, extras field list,
refine tail) is quoted verbatim in the TOML — NOT re-derived.

### Self-verification protocol (--verify, MANDATORY)
After writing, `verify()` runs `lake env lean <out>` in ROOT; on `rc≠0` it
HARD-ERRORs (SystemExit) with the full Lean output — never reports success on a
broken file. It greps the `#print axioms` line for `sorryAx` (error-recovery
holes) and reports the axiom set. Demonstrated: the first unary run had a real
`read64_bytes … aOperand` (BitVec vs Nat) type error → `sorryAx` surfaced in the
axioms line → the emitter refused to pass; fixed template (`.toNat`), re-ran clean.

## Deliverable 2: regenerate-the-hand-instances comparison (VALIDATION)

Both hand twins regenerated from their TOML and verified in-tree:

| twin | file | tag | armPC | callee | x13 | result |
|---|---|---|---|---|---|---|
| unary   | rows/BlockAUnaryArmGen.lean   | 8 | 0x800035e0 | UnaryArmCallee   | no  | GREEN, axioms ⊆ {propext,Classical.choice,Quot.sound} |
| logical | rows/BlockALogicalArmGen.lean | 7 | 0x8000355c | LogicalArmCallee | yes | GREEN, axioms ⊆ {propext,Classical.choice,Quot.sound} |

Generated body is bit-for-bit the hand `blockA_unaryArm`/`blockA_logicalArm`
scaffold (the shared `blockA_k`→destructure→transport→realign→refine), modulo the
`Gen`-suffixed Extras name. The x13-reach branch (logical) is exercised: the emitter
threads the `∀ cm, Steps c cm → PC=armPC → x13=aEnv3` precondition and the
`hx13c1 := hx13reachC c1 hs1 hApc` reach step. Discipline gate: OK. Oleans compiled
to `.lake/build/lib/lean/Vsa/Sim/rows/`. Hand files LEFT INTACT as regression guards.

## Deliverable 3: eval-side missing arms (assignE / callF / argsHead) — BLOCKED, design finding

These do NOT need a `blockA_*Arm` bridge. `assignE_split`/`callF_split`/
`argsHead_split` (ArmSegSplitEval.lean:361-493) ALREADY close those fields modulo a
`hstage : EEntryC c … → LandedN 1 c (JalPreBundle e …)` STAGING CUT — which is the
`blockB_*_stagePre` FAMILY (a bespoke machine-step chain: per-arm site_* lemmas,
addi sub-buffer offsets, jal-target BitVec arithmetic; model
`blockB_unary_stagePre`), NOT the blockA dispatch bridge the emitter generates. The
blockA bridge is the OTHER factor (EvalEntry → ArmEntryK-post); unary/logical/binary
already have BOTH, so they're closed. Recorded in observations
(`eval-missing-arms-are-stagePre-not-blockA`).

Additionally there is NO `AssignArmCallee`/`CallArmCallee`/`ArgsArmCallee`
calleeLoaded predicate, no `*_writeMap8` survival lemma, and no `KindSlotPinned 5`
assign tag established — so even a blockA bridge for them could not be emitted
without those three per-arm inputs first. The emitter is READY to consume them the
moment they exist (recorded: `blockA-arm-bridge-emitter-scope`).

## Deliverable 4: the ONE-TIME exec dispatch packaging — ALREADY BUILT

Audit finding: the ExecEntry→ExecArmEntryK dispatch bridge the task describes is
`execBlockA` (ExecBrkCont.lean:543) — the exec twin of `blockA_k`, fully
parametrized by `(k, armPC)`, taking `ExecEntry` and producing `ExecArmEntryK`. It
is COMMITTED and already consumed by the exec arms (brk k=7/0x80004098, cont
k=8/0x800040b8, expr, varDecl, block, if …). `ExecDispatch.lean` even factors it
into `execPrologue ≫ execDispatch` (post-prologue re-dispatch at 0x80004014). So the
~100-line hand packaging the task allotted is NOT owed — it exists.

The 9 exec arm PCs (all defined, ExecEntry.lean:162-170): expr 0x80004170,
varDecl 0x800040d8, block 0x8000418c, if 0x800041e8, while 0x8000403c,
for 0x80004234, ret 0x80004120, brk 0x80004098, cont 0x800040b8.

The remaining exec-side work is the per-arm CUTS (arm-head → JalPreBundle /
→ ExecEntry), which are the stagePre family (bespoke machine chains via
`execEntry_of_jalPrefix` / `evalChildSplit_of_stage`), NOT blockA-shaped — so the
blockA emitter does not apply. `execEntry_of_jalPrefix` (ArmSegSplitExec) already
supplies the jal→child-ExecEntry seam for those cuts.

## Counts
- eval blockA bridges emitted GREEN: 2/2 (unary, logical — the two hand twins).
  binary NOT emitted (2-operand post: extra gpre/v19/aEnvReg binders + MemExtends —
  a different post shape than the single-operand template; genuine non-uniformity).
- eval assignE/callF/argsHead: 0 emitted (they need stagePre cuts, not blockA — see D3).
- exec cuts emitted: 0 (stagePre-shaped, not blockA); the exec PACKAGING itself is
  pre-existing (execBlockA).

## Template non-uniformities found (design findings)
1. The eval blockA bridge does NOT reduce to a single theorem: the OUTPUT POST
   genuinely differs per arm (unary: single-operand; logical: +x13 +left-survival
   closure; binary: +gpre/v19/aEnvReg +MemExtends, 2 operands). The wave-34 board
   already noted this. So the emitter parametrizes the post as a verbatim block, not
   a computed shape — a mail-merge for the post, a compiler for the scaffold.
2. The calleeLoaded-survival block is structurally per-arm Lean (unary's inline
   `⟨loaded_int_writeMap8 …, intSlot_writeMap8 …⟩` vs logical's one-line
   `logicalCallee_writeMap8 …`) — quoted, not synthesized.
3. The two arm FAMILIES (blockA dispatch bridge vs blockB stagePre cut) are the two
   factors of `EvalEntry → JalPreBundle`. assignE/callF/argsHead + 6 exec-side arms
   all owe the stagePre factor, which does NOT parametrize cleanly (per-arm site
   lemmas + jal-target arithmetic). This is the real remaining frontier.

## Blockers
- assign/call/args blockA bridges: need `*ArmCallee` predicate + `*_writeMap8`
  survival lemma + `KindSlotPinned 5` tag (none exist). Emitter ready.
- assign/call/args + exec stagePre cuts: bespoke machine chains; a second emitter
  (gen_stagepre.py) would still hit non-uniformity 1 (per-arm JalPreBundle conjunct
  list). Deferred, flagged to coordinator.

## Files
- scripts/gen_arm_bridge.py                    (the emitter)
- scripts/arms/blockA_unary.toml               (unary arm-bridge row)
- scripts/arms/blockA_logical.toml             (logical arm-bridge row)
- Vsa/Sim/rows/BlockAUnaryArmGen.lean          (generated twin, green + axiom-clean)
- Vsa/Sim/rows/BlockALogicalArmGen.lean        (generated twin, green + axiom-clean)
- .lake/build/lib/lean/Vsa/Sim/rows/BlockA{Unary,Logical}ArmGen.olean (compiled)
- experiments/observations.md                  (3 design findings appended)

## Wiring lines (report-only; NOT applied — coordinator owns Vsa.lean/check_all.sh)
Add to Vsa.lean (only if a consumer needs the generated twins; the hand
blockA_unaryArm/blockA_logicalArm remain the live ones):
    import Vsa.Sim.rows.BlockAUnaryArmGen
    import Vsa.Sim.rows.BlockALogicalArmGen
Add to scripts/check_all.sh axiom-checked list (if wired):
    Vsa.Sim.blockA_unaryGenArm
    Vsa.Sim.blockA_logicalGenArm
  (both ⊆ {propext, Classical.choice, Quot.sound})
NOTE: the generated twins are REGRESSION GUARDS for the emitter; the live arm
bridges are the hand blockA_unaryArm/blockA_logicalArm (already wired via
EvalChildFieldCombinator). Wiring the twins is optional.
