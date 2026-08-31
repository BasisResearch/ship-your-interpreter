# Abstraction tower design — the next exponentiating layer (2026-08-31)

Read-only survey + design. Nothing landed. Deliverable: the NEXT tower of
exponentiating abstractions across the ENTIRE codebase, ranked by leverage, so
the remaining discharge queue (`interp-sim-completion-plan.md` §Discharge queue)
and post-campaign hardening become trivial instantiation.

Method: harvested `observations.md` (every entry incl. the two unharvested
proposals: `gholds_lookup_ld` readback, `chain_facts` guard-closing fallback),
`interp-sim-completion-plan.md`, `residual-unification-survey.md` (the
`TermShared`/`TermCallees`/`TermGuards` design — assessed below), `abs_inventory.sh`
output, `discipline_grandfather.txt` (753 files: DecodeTable 515, Sim 169,
Snprintf/site batteries ~120, rows 18), plus a grep-driven pattern sweep.

Measured duplication map (this survey's grep evidence):

| family | count | evidence |
|---|---|---|
| `Eval<Op>Resid` structs (Add/Sub/Div/Mod/Mul/Lt/Le/Gt/Ge/Eq) | 10 | 8 of 10 still carry 23-25 INLINE geometry conjuncts each (`ArmPostGeom` collapse landed for add/sub ONLY) |
| widener defs (LeafWiden/ExecRecWiden/EvalRecWiden/ExecLeafWiden/blockD_v_phic) | 5 | one parametric widener possible — see T1.2 |
| `*Extras` per-case residual bundles | 10 | Neg/Not/NotSim/And*/Or*/Bin/BinArm — all `EvalCaseGeom` subsets |
| `*SimD` relanding lemmas | 14 | mechanical `Sim ∘ widener` compositions |
| `*Tri` local-trichotomy helpers | 6 | eval/args/call/stmt/fl/(fc/es) — byte-identical modulo relation names |
| `route_*` error rows | 42 | ×3 duplicated premise list (ErrorSim/StuckSimClose/InterpSimBundle) |
| `binRow_*` / `strCmpCell_*` / `sTail*Row` thin instances | 9+3+11 | per-op table families |
| generators (gen_*_row/gen_*_routing/gen_sites/gen_segment) | 11 | 5 emit-a-Lean-file generators, each own HEADER/emit/TSV boilerplate |
| DecodeTable files | 515 | uniform 16M-heartbeat, import-aggregators + Part leaves; 80% of build CPU |
| `by decide`/`obtain ⟨` density | 700+/244 top files | the snprintf + site-battery legacy tail (grandfathered) |

The abstraction stack IS heavily used already (#derive_case ×99, callSeg ×72,
segToTriple ×47, chain_facts ×42, bridgeOfSeg ×19). The remaining leverage is NOT
"build a combinator that doesn't exist" — it is (a) FINISH collapses that landed
"thin" (ArmPostGeom covers 2 of 10 ops), (b) unify the FIVE near-identical
generators + FIVE wideners + SIX trichotomies into ONE parametric object each, and
(c) two small metaprogram fixes that unblock a whole class of hand-simp
(the observations-ledger proposals).

---

# TIER 1 — pays for itself WITHIN the remaining campaign queue

Each T1 item retires hand-work that the queue (`interp-sim-completion-plan.md`
items 1-9) would otherwise pay per-instance. Ranked by leverage.

## T1.1 — `ImageGeom` finish + `<Op>Resid := ArmPostGeom` for all 10 ops (+ the ExecS twin)

**Collapses.** The ~30-conjunct disjointness/alignment/RAM/window geometry tower
that appears VERBATIM inside every `blockC_<op>` entry, every `Eval<Op>Resid`
struct, every `*Extras`, and every `EvalEntry`/`ArmEntryK`. Grep-measured: 8 of the
10 op-row files (`EvalDivRow`…`EvalGeRow`) still carry 23-25 inline geometry
conjuncts; only add/sub route through `ArmPostGeom` today. ~200 duplicated lines
across the binary family, replicated again on the ExecS side.

**In-repo precedent/model.** `GeomFacts.lean` (`ObjGeom`/`GeomFacts`/`geom` tactic
— already the projected-record + one-`decide` model), `ReallocSpec` `HeapPublicFrame`,
and the LANDED-but-thin `ArmPostGeom.lean` (`armPostGeom_of_addResid` /
`addResid_of_armPostGeom` prove `AddResid ↔ ArmPostGeom 11 AddSlotPinned` — the exact
pattern to fan out). **`ImageGeom` ALSO already exists** — `Vsa/Sim/TermImageGeom.lean`
has `structure ImageGeom (N A SL) : Prop` with `.stackRam`/`.stackWin`/`.stackBounds`
projections + an `imageGeom_of_layout`-style constructor, axiom-clean. So T1.1 is NOT
"define ImageGeom" — it is: wire `ImageGeom` as the shared field of the residuals and
fan out `<Op>Resid := ArmPostGeom` to the 8 ops that lack it. Both bricks are landed;
only the fan-out + aliasing is missing.

**Design sketch.** `ImageGeom (N A SL) : Prop` (LANDED) bundles the ~30
`(N,A,SL)`-and-`decide` facts (StackLayout↔code↔arena↔jumptable↔tohost
disjointness, RAM bounds, alignment) with its `_of_layout` constructor
(one `decide`). The work: `Eval<Op>Resid := ArmPostGeom S row` for each op
(a `def`-alias + reassociate — NO proof change, per survey §4.1). The two adapters
per op (`armPostGeom_of_<op>Resid` / `<op>Resid_of_armPostGeom`) are pure `⟨…⟩`
projections, ~12 lines each, fannable by the ArmPostGeom template.

**Elaboration story.** Flat: `ImageGeom` is a projected record (fast-reflection
law: "GeomFrom = projected record not searchy typeclass") with a one-`decide`
constructor; the `<Op>Resid` alias is definitional so the seam is `rfl`. Replaces 10×
re-elaboration of a 30-conjunct ∧-tower with 1 shared field + 10 `rfl`-aliases.

**Payoff.** ~200 lines deleted now; but the real win is downstream: `hBinary`'s
`BinIntCellResid`/`BinEqCellResid` providers (the M6 residual an `EvalCaseGeom`
widening must supply — queue item 9) become ONE `decide`, not 10 geometry
re-derivations; str cells (queue item 4) inherit it. Every future arm row is a
`(armPC, tag, slotDef)` triple.

**Cost/risk.** Low. Mechanical reassociation; risk is only that a stray op-row has a
geometry conjunct the others lack (grep shows div/mod carry 25 vs 23 — the extra 2
are the `b≠0`/overflow guards, which belong in `TermGuards`, not `ImageGeom`; keep
them separate).

## T1.2 — `Widen` : ONE parametric exit-widener replacing the 5-widener zoo

**Collapses.** `LeafWiden` (EvalLeafD), `ExecLeafWiden` (ExecCaseGeom),
`ExecRecWiden` (ExecRecRows), `EvalRecWiden` (CallRows), `blockD_v_phic`
(CallArmEpilogue). All five answer the SAME question — "upgrade a bare `Exit`
(`EvalExit`/`ExecExit`) to the motive's `ExitD` by re-supplying the two dropped
clauses: `MemExtends m0 mem` (presence monotonicity) + the `[SL.lo,SL.hi)`
store-survival" — differing only by (a) Eval vs Exec exit predicate, (b) identity-φ
(leaf) vs non-identity-φ (recursive: the sub-derivation mutated the store) and (c)
whether a retslot/allocFrame window is added to the survival footprint.

**In-repo precedent/model.** `EvalLeafD.evalExitD_of_evalExit` is the cleanest
instance; `FrameCalc` (`FrameCalc.trans`/`frameOn`/`pin8`) is the compositional
footprint algebra the parametric version should sit on. The φ-extension is already
`PhiExtends` (`PhiExtends.refl`/`.trans`) — the recursive/leaf difference is just
`refl` vs a supplied `PhiExtends`.

**Design sketch.**
```lean
structure Widen (ExitP : Mem → φType → Config → Prop)   -- EvalExit or ExecExit, curried
    (m0 : Mem) (φf0 φc0 : Addr → Nat) (foot : Nat → Prop) : Prop where
  pres  : ∀ c, ExitP m0 _ c → MemExtends m0 c.σ.mem
  phi   : ∃ φf φc, PhiExtends φf0 φf ∧ PhiExtends φc0 φc          -- refl for leaves
  surv  : ∀ c, ExitP … c → ∀ m', (∀ k, ¬ foot k → c.σ.mem[k]? = m'[k]?) → StoreRepr m' …
theorem exitD_of_exit (hExit) (hW : Widen ExitP m0 …) : ExitD … := …
```
`foot` is the survival window (leaves: `[SL.lo,SL.hi)`; retNull: `∪ [aRet,aRet+24)`;
block: `∪ allocFrame window`) — supplied per row, `FrameCalc`-composed. `LeafWiden`,
`ExecLeafWiden`, `ExecRecWiden`, `EvalRecWiden` become `abbrev`s
(`Widen EvalExit … [SL.lo,SL.hi)`, etc.), `blockD_v_phic` a corollary.

**Elaboration story.** Flat: `Widen` is a projected record; `exitD_of_exit` is a
term-level `⟨…⟩`; the per-row `foot` is a `Nat → Prop` union, not a decide. No
whnf of Sail state — reflects on `MemExtends`/`StoreRepr` presence only.

**Payoff.** 5 defs + 5 `*_of_*` bridges → 1 def + 1 bridge + 5 `abbrev`s. Directly
unblocks queue item 2 (ExecS dispatch/loop — each arm needs a widener; today
`hSRetNull`/`hSVarNull` are BLOCKED precisely because `ExecLeafWiden` is
identity-φ-only, per the step-6b ledger — the parametric `Widen` with a supplied
`PhiExtends` + retslot `foot` closes them) and item 3 (call rows reuse `EvalRecWiden`).

**Cost/risk.** Low-medium. The φType currying (Eval carries `nf nc` store-size
ghosts; Exec carries `status`) needs the ExitP argument to be the fully-applied
predicate so `Widen` is relation-agnostic — a one-time signature design, then free.

## T1.3 — `genrow` : ONE row-generator framework replacing the 5-generator zoo

**Collapses.** `gen_m4_term_row.py` (493 L), `gen_exec_row.py` (125),
`gen_m5_error_routing.py` (264), `gen_bin_dispatch_row.py` (496),
`gen_m4_case.py`-adjacent. Each re-implements: TSV parse, a `HEADER` string, a
per-shape emit function, `open`/`namespace` boilerplate, and the check_all-wiring
echo. 1300+ lines of Python, ~70% shared plumbing.

**In-repo precedent/model.** `gen_m5_error_routing.py` is the canonical "data table
→ uniform emission" the survey already names as the model; `gen_m4_term_row.py`
generalized `leaf_bridge` with `vbinds`/`extra_ghosts` dict-driven fields (§6 ledger)
— that dict-driven-shape idea IS the framework, just not extracted.

**Design sketch.** `scripts/genrow.py` = a library: `Row` dataclass (shape, name,
premise-thm, constants dict), `emit_header(imports, opens)`, `emit_row(row,
templates)`, `wire(check_all_names)`. Each concrete generator becomes a ~40-line
`SHAPES = {...}` template dict + `main()` that calls the library. New row shapes =
one dict entry, not a new 400-line file. A single `scripts/rows.tsv` schema
(columns: `family, shape, name, thm, kind, armPC, tag, slotDef, callee, resid,
guards, subIHs`) subsumes m4_term_rows.tsv / exec_rows.tsv / m5_error_routing.tsv /
the bin-dispatch INT_ROWS table.

**Elaboration story.** N/A (Python), but the EMITTED Lean obeys fast-reflection
laws unchanged (same templates). The win is generator-authoring time + one place to
fix a template bug.

**Payoff.** Queue items 2 (ExecS rows), 3 (call rows), 4 (str cells), 9 (assembly
table) all emit new rows; today each needs a bespoke generator or hand rows.
`genrow` makes each new premise a TSV line. Retires ~800 lines of Python duplication.

**Cost/risk.** Low, but PYTHON not Lean — the discipline gate doesn't cover it, and
a regression in the shared emitter breaks all families at once (mitigate: keep the
per-family golden-output test = re-emit and `git diff` must be empty, which the
existing "regenerate → compiles green" check already provides).

## T1.4 — `TermShared`/`TermCallees`/`TermGuards` : BUILD the survey's bundle (queue item 9 precondition)

**Assessment (prompt asked: is the residual-unification design STILL right
post-campaign?).** YES, and it is now MORE right than when written — but it must be
UPDATED for three facts the campaign discovered:
1. `TermCallees` must gain `envDefine`/`malloc`/`realloc` as the ONLY open `C`
   fields (valueEqual/envGet/divdi3 landed) — matches EnvDefCompose's real
   contracts (`envDefContract`/`envDefAppendContract`/`envDefGrowContract`,
   `MallocContract`, `ReallocOps` — NOT new structs).
2. `TermGuards` must gain `hBadClosure` + `hTopAbrupt` (the two NEW recursor
   residuals from the badclosure-recursor observation) — the error-family now has
   44 named routes, not 42.
3. The 5 str-cell slots + div-overflow slot (BinDispatchRow ledger) are `TermGuards`
   members, not geometry.

**Collapses.** The `@EvalE.rec`/`@ExecS.rec` capstone application (queue item 9)
today would thread 44+ error premises + 50 term premises + 3 bundles POSITIONALLY.
`TermShared` (the `ErrShared` analogue — ONE record of shared L7/L8/geometry) makes
the capstone `errFamily_of_sites`-shaped: rows supplied positionally, bundles
threaded once.

**In-repo precedent/model.** `ErrShared` (`rows/ErrorRouting.lean`) — the survey's
own named model, LANDED and consumed by all 42 `route_*`.

**Design sketch.** Exactly survey §2.1-2.5 with the three updates above.
`TermShared` carries `ImageGeom` (T1.1) as its `geom` field — **T1.1 composes INTO
T1.4**. `termSimClosed L (S : TermShared) (C : TermCallees) (G : TermGuards)
(hEntry)` = the `@EvalE.rec` table.

**Elaboration story.** Flat: bundles are projected records; the capstone is a
positional `.rec` application (no search). The whole point is to AVOID the
`h.2.2.2.2` positional navigation gate rules R6/R7 forbid.

**Payoff.** THE assembly capstone (queue item 9 / `hterm` / `hdivFam`). Every row
already landed (26/50) plugs in unchanged; the remaining rows plug in as they land.

**Cost/risk.** Medium — it is the integration point, so it can only fully close when
the last row lands. But the BUNDLE DEFS (the three structures) can and should land
NOW (empty of the not-yet-proven fields' witnesses — they're `∀`-premises), so every
subsequent row targets the final shape. Build the structures before queue item 2.

## T1.5 — `chain_facts` guard-closing fallback (unharvested observation, closes a live blocker class)

**Collapses.** The ~14-line hand `simp only [runGM,stepGM,wvalM,srcVal,guardB,
<8 field pins>] <;> decide` every seg row whose branch guard is a computed
arithmetic (not a pinned literal) must write TODAY — AND its diagnosis tax: a
SIGABRT native stack overflow with no line number (per the
`chainfacts-branchguard-arith-overflow` observation). Live in StrArmChain span-1;
recurs in every future kind-check / subtract-and-compare guard (queue item 4 str
cells, item 2 ExecS if/while conditions).

**In-repo precedent/model.** `chain_facts` (ChainFactsTac) already HAS the seg's
per-word `mkLine` decode facts; `cmpFixupTail_facts`/`sTailLt_facts` are the
`all_goals rfl` cheap path that works for pinned-literal guards.

**Design sketch.** Extend `chain_facts`'s guard-closing tail: after `rfl` fails, try
`simp only [runGM,stepGM,wvalM,srcVal,guardB, <the seg's own mkLine field pins>]
<;> decide`, driven by the decode table the tactic already holds. Bounds
`maxRecDepth` so a wrong guard is a LOCATED error, not SIGABRT.

**Elaboration story.** Flat by construction — one small `decide` on a reduced
`BitVec` compare, per the symbolic-reduce path the observation already validated by
hand. Never overflows (the simp collapses the `runGM` tower BEFORE decide).

**Payoff.** Turns a 14-line-per-row + nasty-diagnosis hand pattern into a
one-liner, for every arith-guarded seg row remaining. Also the companion
`gholds_lookup_ld` readback (the load-bearing-seg-register observation) is the same
class — bundle both into the ChainFactsTac extension.

**Cost/risk.** Low-medium — a tactic change (metaprogram), so test against the
existing `*_facts` rows (must still pass) + the StrArmChain hand case (must now
close by the fallback). Contained to ChainFactsTac.lean.

---

# TIER 2 — pays at assembly / M6 time

## T2.1 — `parametric trichotomy` : ONE generator for the 6 `*Tri` + `progress*_succ` helpers

**Collapses.** `evalTri`/`argsTri`/`callTri`/`stmtTri`/`flTri` (+ fcTri/esTri) in
`StmtDispatchClose.lean` are byte-identical modulo the relation quadruple
`(Rel, RelErr, RelApprox, existential-shape)` — each is
`by_cases hc:∃… · Or.inl · by_cases he:RelErr · Or.inr∘Or.inl · Or.inr∘Or.inr (h … hc he)`.
The `progress*_succ` companions case on the syntax constructor and route through the
matching `*Tri`.

**Model.** `gen_m5_error_routing.py` (data→emission). A tiny generator (or a Lean
`macro` `derive_trichotomy Rel RelErr RelApprox`) emits all six.

**Payoff.** ~60 lines now; the real value is queue item 8 (error-judgment amendment)
+ item 2 — when `ExecS`/`ForLoop` gain the `badClosure`/`abrupt-head` leaves, the
trichotomies must be re-derived; a generator re-emits instead of hand-editing 6
near-copies. Also feeds the divergence side (`hdivFam`).

**Cost/risk.** Low. A Lean `macro_rules` is cleaner than Python here (keeps it in the
discipline-gated tree). Risk: the `by_cases` classical content — must stay in the
`{propext, Classical.choice, Quot.sound}` axiom set (it does; `Classical.em`).

## T2.2 — `route generator` for the ×3-duplicated 42/44-premise error-site list

**Collapses.** The error-site premise list is written THREE times
(`ErrorSim.lean`, `StuckSimClose.lean`, `InterpSimBundle.lean` — grep-confirmed as
the 42/44 `route_*`/premise mirrors). The `badclosure-recursor` observation already
showed the cost: adding ONE inductive leaf forced a 5-theorem re-thread because the
`@ExecSeqErr.rec` application demanded a new minor premise in each mirror.

**Model.** `gen_m5_error_routing.py` reads the premise SIGNATURES verbatim from
`InterpSimBundle.lean` — extend it to be the SINGLE SOURCE that emits the premise
list into all three consumers (or, better, define the premise list ONCE as a
`structure ErrPremises` and have all three take `(P : ErrPremises)`).

**Payoff.** Queue item 8 (the 3-rule amendment) is exactly the scenario this
prevents — one leaf add → one struct field, not 3 hand-threaded mirrors. Named in
the completion-plan's non-blocking list ("generator for the thrice-duplicated
42-premise error-site list").

**Cost/risk.** Low. The struct-of-premises version is the cleaner Lean-native form;
the generator version is faster to land. Prefer the struct.

## T2.3 — `Contract` uniformity : one framed-callee-spec convention

**Collapses.** The callee contracts (`MallocContract`, `ReallocOps`/`ReallocContract`,
`SnprintfContract`, `envDef*Contract`, the `value_*_spec_full` family, `divdi3_spec`,
`env_get_found`) are consumed with per-callee `*_closed` marshalling wrappers
(EnvDefBridges×5, EntryHaltsSpans, EvalVarBridge, BinStrCells). Each `*_closed` is a
~90-line "prefix ≫ callSeg over the contract ≫ suffix" splice — the SAME shape
`callSeg`/`callSegConseq` already factors, but the framed-post adaptation
(`FrameMeta.abiFrame_of_wrChain`/`memFrame_of_chain`) is re-applied by hand per
callee.

**Model.** `callSeg`/`BridgeSeg.bridgeOfSeg` + `FrameMeta` (both LANDED). The gap is
a CONVENTION: every callee contract should expose a `framed` corollary
(`<callee>_spec_framed`) via `FrameMeta` over its reflected chain ONCE, so callers
never re-frame. CLAUDE.md law already says "Framed variant of a callee spec =
FrameMeta metatheorems — NEVER re-run the chain"; this makes it a landed corollary
per callee instead of a per-caller obligation.

**Payoff.** Queue items 1 (env_define bridges — 5 remain), 6 (entry seams), 7
(hCallClosure env-fold) all splice callees; a pre-framed contract makes each splice
a plain `callSeg`. The memcpy-word-route observation (item 4 in observations) is
exactly a missing `<callee>_spec_framed` — reflect-first, then FrameMeta.

**Cost/risk.** Medium — some contracts (memcpy word route) are still legacy-ghost
form and need reflecting FIRST (the observation's proposal). Do the reflect+frame per
callee as its caller comes up in the queue, not speculatively.

## T2.4 — `EvalCaseGeom`/`ExecCaseGeom` + `blockA_k`/`blockA_stmt` unification (the entry-bridge twin)

**Collapses.** The per-node entry synthesis (`EvalEntry → ArmEntryK` via `blockA_k`;
`blockA_binaryArm` for the binary node; the un-built `blockA_stmt` for ExecS). Survey
§2.2 `EvalCaseGeom` unifies `NegExtras`/`BinExtras`/`hMcallPop` + `blockA_k`'s
side-inputs; the ExecS side needs the `ExecCaseGeom` twin (partly landed in
`rows/ExecCaseGeom.lean`) + a `blockA_stmt` — BUT the step-6b ledger found
`execBlockA`/`execBlockD` ALREADY exist, so `blockA_stmt` is a marshalling wrapper,
not a new proof.

**Payoff.** Queue item 2 (the whole ExecS dispatch/loop family) — the biggest
un-rowed family. Once `ExecCaseGeom` + `blockA_stmt`-wrapper land, each ExecS arm is
a row (like the EvalE binary family).

**Cost/risk.** Medium — depends on T1.2 (`Widen`) for the non-identity-φ exits.

---

# TIER 3 — post-campaign hardening (under the ratchet)

## T3.1 — DecodeTable build-CPU collapse (515 files, 80% of build CPU)

**Collapses.** The 515 DecodeTable files (import-aggregators + Part leaves) carry a
uniform 16M-heartbeat and dominate the measured 75.5-min world rebuild
(build-speed-campaign memory + completion-plan Tier-0 note). This is the single
biggest ITERATION-RATE lever, but it does not close a proof — hence T3.

**Design sketch.** The completion plan already scopes this: "the 512 generated
DecodeTable files' uniform 16M-heartbeat constant" — the experiment is to replace the
per-file decide-heavy decode with a reflected lookup (fast-reflection law: reflect on
first-order data, one decide). Candidate: a single `decodeTableData` array + one
`decode_of_table` metatheorem, so the 515 files become 1 data file + 1 lemma.

**Payoff.** Iteration rate for ALL remaining work; but ONLY worth a slot mid-campaign
IF the measurement shows a rebuild-speed win that pays back (completion-plan's own
gate). Otherwise post-campaign.

**Cost/risk.** High effort, measurement-gated. Do NOT speculatively.

## T3.2 — Legacy site-battery / snprintf re-seat (grandfather shrink)

**Collapses.** ~120 grandfathered site-battery + Snprintf files (`by decide` density
700+ in the top files: StrcmpSites 714, SnprintfSpec17 580, StrcpySites 541, …).
These are the pre-abstraction idiom the discipline gate now forbids for NEW files.

**Design sketch.** Re-seat on `#derive_case`/`segToTriple`/`bridgeOfSeg`/`FrameMeta`
per the completion-plan's non-blocking list (re-seat strlen byte-tail + the four hand
prefix-runs; `interpContSeg_of` on `restoreRetChain_run`). Each re-seat retires
grandfathered files.

**Payoff.** Grandfather shrink (correctness-neutral); build CPU; future-edit
maintainability. Post-campaign hygiene per the plan.

**Cost/risk.** Low-risk, high-volume. Fan-out-able (COW-clone workflow). Not campaign
priority.

## T3.3 — `keys_evalBlocks` subset lemma (task #31, drops per-seg key decides to zero)

**Collapses.** The 2 extra `decide`s per `bridgeOfSeg` row for
`hKeysOut`/`hRaOut` (the `keys-decides-per-seg` observation, already harvested to
task #31). One structural-induction subset lemma
(`keys (evalBlocks bs L).regs ⊆ keysG L ++ wrChain bs`) makes them derivable.

**Payoff.** Every current + future `bridgeOfSeg` row (×19 today, growing). Small per
row, but permanent. Could be T2 if bridge rows dominate the remaining queue (item 1
env_define bridges use it).

**Cost/risk.** Low. A single fold lemma. Promote to T1.5-adjacent if the env_define
bridge front (queue item 1) is next.

---

# THE TOWER — how these compose (abstractions on abstractions)

The design goal is one-line instantiation. The composition:

```
                         ImageGeom (T1.1)  ─┐
                                            ├─►  TermShared  ─┐
   Widen (T1.2) ──► *SimD / *D lemmas ──────┘                │
                                                             ├─►  termSimClosed
   Contract-framed (T2.3) ──► TermCallees  ──────────────────┤     (queue item 9)
                                                             │       = @EvalE.rec table
   TermGuards (str cells, badClosure, topAbrupt, overflow) ──┘
        ▲
        │ str-cell rows need ── chain_facts fallback (T1.5) + gholds_lookup_ld
        │ ExecS rows      need ── EvalCaseGeom/blockA_stmt (T2.4) which needs Widen (T1.2)
        │
   genrow (T1.3) EMITS every row into the three bundles from ONE rows.tsv schema
   route-generator (T2.2) EMITS the error premise struct into all 3 mirrors
   parametric-trichotomy (T2.1) EMITS the 6 *Tri for hdivFam/htri
```

Named compositions (the "abstractions on abstractions"):

1. **`ImageGeom` ∘ `ArmPostGeom` → `<Op>Resid` alias → `genrow` binary shape.**
   T1.1 makes the geometry a field; `genrow` (T1.3) then emits a binary row as
   `(armPC, tag, slotDef)` — the whole 200-line geometry list becomes a TSV triple.
2. **`Widen` (T1.2) → `*SimD` (abbrev) → `genrow` leaf/rec shape → `EvalCaseGeom`
   (T2.4) → ExecS rows.** One widener feeds the `*D` relanders, which feed the row
   templates, which feed the case-geom entry bridges — the ExecS family (queue item
   2) collapses to rows once this chain lands.
3. **`Contract-framed` (T2.3) → `TermCallees` → `callSeg` splices (queue items
   1/6/7).** A pre-framed contract per callee makes every splice a plain `callSeg`;
   `TermCallees` threads them once.
4. **Bundle-of-premises (T2.2) → single `@Rel.rec` application.** The error list AND
   the term list both become `structure`-threaded, so queue item 8's leaf-adds are
   one field, and item 9's capstone is positional.

The convention that ties it together (prompt's "unified `Post`-structure
convention feeding a generic destructurer feeding row generators feeding the
recursor table"): **every Post/Entry/Resid is a named-field `structure … : Prop`**
(CLAUDE.md law 6 / gate R6/R7, already enforced). `genrow` reads the structure's
field list from the TSV; `Widen`/`ImageGeom` are the shared fields; the destructurer
is the structure's projection (no `.2.2.2`). This is already the LAW — the tower just
makes the generators and bundles CONSUME it uniformly instead of per-family.

---

# PROPOSED EXECUTION ORDER (interleaved with the discharge queue)

The queue (`interp-sim-completion-plan.md`): 1 env_define bridges, 2 ExecS
dispatch/loop, 3 Call residuals, 4 hBinary str cells, 5 hVar, 6 entry seams, 7
hCallClosure, 8 error amendment, 9 assembly+M6.

**Build BEFORE any queue front (they pay for themselves on the very next item):**
- **T1.4 bundle DEFS** (`TermShared`/`TermCallees`/`TermGuards` structures, empty of
  witnesses) — so every subsequent row targets the final shape. Half a day.
- **T1.1 `ImageGeom` finish** + fan out `<Op>Resid := ArmPostGeom` to the 8
  remaining ops — collapses geometry before ExecS/str rows re-list it. Feeds T1.4's
  `geom` field.
- **T1.2 `Widen`** — REQUIRED by queue item 2 (ExecS non-identity-φ exits are
  BLOCKED without it) and item 3.

**Then interleave:**
- **T1.5 chain_facts fallback + gholds_lookup_ld** BEFORE queue item 4 (str cells
  hit the arith-guard SIGABRT) and item 2 (if/while conditions).
- **T2.4 `EvalCaseGeom`/`blockA_stmt`-wrapper** BEFORE queue item 2 (it IS the ExecS
  row enabler); depends on T1.2.
- **T1.3 `genrow`** BEFORE queue items 2/3/4 emit their rows (whenever ≥2 new row
  families are imminent — the "factor before the third" law).
- **T2.3 Contract-framed** per-callee, JUST-IN-TIME as queue items 1/6/7 reach each
  callee (not speculative).
- **T2.2 route-struct** BEFORE queue item 8 (the 3-rule amendment) — makes the
  leaf-adds one field, not 3 mirrors.
- **T2.1 parametric-trichotomy** WITH queue item 8 (same amendment re-derives the 6
  *Tri).
- **T3.3 `keys_evalBlocks`** early if queue item 1 (env_define bridges, ×19
  bridgeOfSeg) is next — it zeroes their per-seg key decides.

**Post-campaign, under the ratchet:** T3.1 (DecodeTable, measurement-gated — only
mid-campaign if the rebuild-win pays back), T3.2 (legacy re-seat, fan-out).

**Capstone:** queue item 9 = instantiate T1.4 with the landed rows — a positional
`@EvalE.rec`/`@ExecS.rec` application, `#print axioms`, into check_all.
