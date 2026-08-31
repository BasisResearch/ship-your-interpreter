# Residual-unification survey + interface design (step 6)

Goal (from `interp-sim-completion-plan.md` §6): normalize every term-side case
theorem's **heterogeneous named residuals** into a uniform interface so the
`@EvalE.rec` assembly (`TermSimAssembly.term_sim_of_cases` /
`TermSimClose.execSeq_sim_of_cases`) becomes a **table** — one thin
`<case>_row : <UnifiedResid…> → <the exact minor-premise shape>` adapter per
premise, most of them pure table rows (like `gen_m5_error_routing.py`).

This doc is (1) the exhaustive premise↔case↔hypothesis table, (2) the unified
interface design (Lean signatures), (3) the generator plan, (4) the estimate +
refactor list. Read-only survey; nothing landed.

---

## 0. The structural gap (the crux the whole design turns on)

The 50 minor premises of `term_sim_of_cases` are stated in **motive shape**
(`TermSimAssembly.lean`):

| relation | motive `m_R` | = |
|---|---|---|
| `EvalE` | `mEvalE` | `EvalRecCommon.EvalIH` (`Triple (EvalEntry…) (EvalExitD…)`), ∀-closed over layout ghosts |
| `ExecS` | `mExecS` | `ExecBlock.ExecIH` (`Triple (ExecEntry…) (ExecExitD…)`) |
| `EvalArgs`/`Call`/`ExecInit`/`ForLoop`/`ForCond`/`ExecStep`/`ExecSeq` | `m…` | `Triple (SegEntry…@decodedPC) (SegExit…@decodedPC)` |

**PROBED (`/tmp/probe2.lean`, green):** `mEvalE st d env e st' v h = EvalIH …`
by `rfl`. So (a) the sub-derivation IHs the recursor hands a case ARE already in
the case theorem's input shape — **no input adapter needed**; (b) each premise's
*conclusion* is `EvalIH …`/`ExecIH …`/`Seg…` for THIS node.

But the landed case theorems do **not** conclude `EvalIH` directly. Their goal
`Eval<Op>SimGoal` is `Triple (fun c => ∃ ment, ArmEntryK … ∧ <front conjuncts> ∧
(∀ c', TwoSubReturn… → <Op>Resid…) ∧ <g-bridge>) (EvalExitD…)` — a Triple whose
**entry** is `ArmEntryK`-∃ (the post-dispatch arm state), not `EvalEntry` (the
`eval_expr` fn entry). The missing link between `EvalEntry` (what `EvalIH`
promises) and `ArmEntryK` (what the case theorem consumes) is exactly
`blockA_k` (`EvalSimCommon.lean`): prologue + jump-table dispatch →
`ArmEntryK @armPC`. **PROBED green:** `blockA_k`'s entry precondition is an
`EvalEntry`-shaped prologue struct.

So a term-side `<case>_row` adapter has THREE mechanical jobs, all identical
across the binary/unary/leaf families:

1. **input**: take the bundle's `EvalIH`-conclusion goal for THIS node
   (`∀ g N A SL φf φc sp r sret aEnv aExpr m0, Triple (EvalEntry…) (EvalExitD…)`).
   Intro the ghosts + the `EvalEntry` precondition `c`.
2. **synthesize**: run `blockA_k` from `EvalEntry` (needs the case's kind-tag /
   slot / callee-loaded / `hexprSurv` — all **geometry** facts) to reach the
   `ArmEntryK`-∃ entry the case theorem wants.
3. **apply**: feed the case theorem (`evalDivSim` …) with the sub-IHs
   (`rfl`-passed) + the case's **residual bundle** (`<Op>Resid` ∀-closed over
   `c'`) + the semantic guards (`b≠0`, overflow). Chain the `Steps`, land
   `EvalExitD`.

Steps 1–2 are IDENTICAL up to a **row of constants** (armPC, tag, callee,
slot-def, `<Op>Resid`). Step 3 differs only by the guard set. THIS is why the
adapters are table rows, and why the unified bundle must carry exactly the
`blockA_k` geometry inputs + the `<Op>Resid` geometry + the guards.

---

## 1. THE SURVEY TABLE

Legend for **hyp classes** (the 7 residual classes the interface must cover):
`G`=M6-layout geometry (align/RAM/window/disjointness/StackOK — all the
`blockA_k` inputs, `ArmEntryK`/`<Op>Resid`/`*Extras` fields, `hexprSurv`,
`hMcallPop`/`fullpop`); `C`=callee contract (Malloc/Realloc/SC/HT, `value_*`
specs, `env_get`/`env_define`); `S`=step-contract loop body oracle
(`ExecWhileStep`/`ForLoop`/`EvalArgsStep`/block `hstep`); `H`=caller-linkage
`hsite`/entry-existential; `R`=repr-bridge (`ValueRepr`/`ExprRepr` readback,
`EqNeReprReadback`); `I`=IH-shaped (`EvalIH`/`ExecIH`/`mExecSeq` sub-premise —
free, `rfl`); `O`=genuinely-open / semantic guard (`b≠0`, overflow,
`store.size`-stability, depth crux).

### 1a. `EvalE` premises (motive_1, 15)

| premise | discharging thm (file:line) | hypotheses (goal binders) | classes |
|---|---|---|---|
| `hInt` | `evalIntSim` (EvalIntSim4:245) | `EvalEntry`→`EvalExitD` via jump-table+`value_int`; leaf | G, C |
| `hStr` | `evalStrSim` (EvalStrSim:628) | leaf + CString geometry | G, C, R |
| `hBool` | `evalBoolSim` (EvalBoolSim:651) | leaf + payload `lw` | G, C |
| `hNull` | `evalNullSim` (EvalNullSim:353) | leaf | G, C |
| `hVar` | `evalVarSim` (EvalVarSim:1571) | `EvalVarEntry`; **`env_get_found` hyp** (`hreach` scan) | G, C, **O** |
| `hAssign` | *(gap)* — native-store; env_define-blocked | needs `set?`/env_define contract | G, C, O |
| `hBinary` | per-op: `evalAddSim`/`evalSubSim`/`evalLtSim`/`evalLeSim`/`evalGtSim`/`evalGeSim`/`evalMulSim`/`evalDivSim`/`evalModSim`/`evalEqNeSim` | `ArmEntryK`-∃ + `BinExtras` + `<Op>Resid`(∀c') + `g`-bridge; sub-IHs `EvalIH×2`; `store.size` stability | G, R, I, **O** |
| `hOrTrue` | `evalOrTrueSim` (EvalOrSim:1017) | logical short-circuit; 1 sub-IH | G, I |
| `hOrFalse` | `evalOrFalseSim` (EvalLogical4:1185) | 2 sub-IH | G, I |
| `hAndFalse` | `evalAndSim` (EvalAndSim:1341) | 1 sub-IH | G, I |
| `hAndTrue` | `evalAndTrueSim` (EvalLogical3:1151) | 2 sub-IH | G, I |
| `hNeg` | `evalNegSim` (EvalNegSim3:189) | `EvalEntry`+`NegExtras`+`hMcallPop`; 1 sub-IH | G, I |
| `hNot` | `evalNotSim` (EvalNotSim:1095) | `EvalEntry`+`NotExtras`; 1 sub-IH | G, I |
| `hCall` | `evalCallSim` (EvalCall:91) | 3 sub-motives (`EvalIH`,`mEvalArgs`,`mCall`) | G, I |
| `hFn` | `evalFnSim` (EvalFn:86) | `allocClosure` native store | G, C |

The 10 `hBinary` op-sub-theorems are the **canonical table family**: their goals
(`Eval{Add,Sub,Lt,Le,Gt,Ge,Mul,Div,Mod}SimGoal`, `evalEqNeSim`) are byte-identical
in shape modulo the row `(armPC, opTok, slotDef, <Op>Resid, guards, callee-seam)`.
Confirmed: `AddResid`≡`SubResid` field-names IDENTICAL; `GtResid` differs only
`vint`→`vbool`; token + `tableStk` offset differ by constant. div/mod/mul/eqne
add a callee-seam (`__divdi3`/`value_equal`) but keep the same outer shape.

### 1b. `EvalArgs` (2), `Call` (4)

| premise | discharging thm | hyps | classes |
|---|---|---|---|
| `hArgsNil` | `evalArgsNil` (CallEntry:305) | `SegEntry`→`SegExit` leaf | G |
| `hArgsCons` | `evalArgsCons` (EvalArgs:248) | 1 `EvalIH` + 1 `mEvalArgs` sub | G, I, **S** (loop back-edge via `evalArgsStepOf`, LoopSteps:221) |
| `hCallClosure` | *(crux gap)* `callClosureSim` (EvalCallClosure:166) partial | arity+depth+`allocFrame`+env_define-fold+body-`ExecSeq`@d+1 | G, C, S, **O** (depth crux) |
| `hCallPrint` | `callPrint` (EvalCallPrint:181) | native output-append | G, C |
| `hCallPrintln` | `callPrintln` (EvalCallPrint:216) | native output-append | G, C |
| `hCallAssertOk` | `callAssertOk` (EvalCallNative:180) | native no-op | G |

### 1c. `ExecS` (16), `ExecInit` (2), `ForLoop` (4), `ForCond` (2), `ExecStep` (2), `ExecSeq` (3)

| premise | discharging thm (file:line) | hyps | classes |
|---|---|---|---|
| `hSExpr` | `execExprSim` (ExecExprRet:172) | `ExecEntry`→`ExecExitD`; 1 `EvalIH` sub | G, I |
| `hSVarInit` | `execVarDeclSim` (ExecVarDecl:116) | `define` native store; 1 sub | G, C, I |
| `hSVarNull` | `execVarDeclNullSim` (ExecVarNull:110) | `define null` | G, C |
| `hSBlock` | `execBlockSim` (ExecBlock2:293) | `allocFrame` + inner `mExecSeq` sub | G, C, I |
| `hSIfTrue` | `execIfTrueSim` (ExecIf2:105) | cond `EvalIH` + branch `ExecIH` | G, I |
| `hSIfFalse` | `execIfFalseSim` (ExecIf2:197) | 2 sub | G, I |
| `hSIfNone` | `execIfNoneSim` (ExecIf:104) | 1 sub | G, I |
| `hSWhileFalse` | `execWhileFalseSim` (ExecWhile:102) | 1 `EvalIH` sub | G, I |
| `hSWhileBreak`/`hSWhileRet`/`hSWhileLoop` | `execWhileSim`/`execWhileLoopSim` (ExecWhile2:195/129) | back-edge loop | G, I, **S** |
| `hSForStart` | `execForStartSim` (ExecForStart:92) | `allocFrame`+`mExecInit`+`mForLoop` | G, C, I |
| `hSRet` | `execRetSim` (ExecRet:132) | 1 sub | G, I |
| `hSRetNull`/`hSBrk`/`hSCont` | `execRetNullSim`/`execBrkSim`/`execContSim` | leaf status | G |
| `hInitNone`/`hInitSome` | *(scaffold, `SegEntry→SegExit`)* | init sub | G, I, S |
| `hFlCondFalse`/`hFlBodyBreak`/`hFlBodyRet`/`hFlLoop` | `execForLoopSim` (ExecFor:216) + scaffold | for back-edge | G, I, **S** |
| `hFcNone`/`hFcSome` | *(scaffold)* | for-cond | G, I |
| `hEsNone`/`hEsSome` | *(scaffold)* | step | G, I |
| `hSeqNil` | `execSeqNil` (TermSimAssembly ref) | `SegEntry→SegExit` leaf | G |
| `hSeqConsNormal`/`hSeqConsAbrupt` | `execSeqLoop` | seq back-edge; `ExecIH`+`mExecSeq` sub | G, I, **S** |

**Program-entry** premise (not in the 50): `termSimClosed.hEntryHalts` — the M6
`interp_run` prologue → statement-loop `mExecSeq` → clean `Halts c out 0`
bridge. Classes: G (Loaded↔SegEntry unification) + the whole-program `mExecSeq`
(I). This is the ONE bespoke top-level adapter, already isolated as a named hyp.

**Summary of class distribution over the 50 premises + entry:** every premise
carries **G** (layout geometry — universal); **I** appears in all 33 recursive
premises (free, `rfl`); **C** in 11 (leaf-callee + native-store + env cases);
**S** in 8 (loop back-edges); **R** in 3 (str/binary/eqne repr readback);
**O** (genuinely-open) in 5: `hVar`(`env_get_found`), `hAssign`(env_define),
`hBinary`(store.size + overflow/nonzero guards), `hCallClosure`(depth crux),
plus loop-`S` termination measures.

---

## 2. THE UNIFIED INTERFACE

Precedent: `ErrShared` (`rows/ErrorRouting.lean`) is the model — ONE record of
shared L7/L8 facts, threaded into every `route_*` row, with only `hsite`
per-premise. `DivResid`/`EqResid` are the model for the per-case geometry slot.
The design mirrors this: **one shared bundle + per-shape geometry slot + the
open oracles**, with each case getting a thin `<case>_row` adapter.

### 2.1 `TermShared` — the shared layout/ghost bundle (the `ErrShared` analogue)

Everything universal across all EvalE/ExecS cases: the layout ghosts and the
whole-program geometry that `blockA_k`/`ArmEntryK` need identically. Threaded
once, like `ErrShared.SC`/`HT`.

```lean
structure TermShared where
  g gpre gouter : (R : Register) → Option (RegisterType R)
  N : NativeAddrs
  A : Arena
  SL : StackLayout
  φf φc : Addr → Nat
  -- whole-program geometry (the `blockA_k`/`ArmEntryK` disjointness constants):
  -- StackLayout↔code↔arena↔jumptable↔tohost disjointness, RAM bounds, alignment.
  geom : ImageGeom N A SL           -- packages every `decide`-provable G constant
```

`ImageGeom` bundles the ~30 disjointness/alignment/RAM facts that appear
verbatim in every `ArmEntryK`/`<Op>Resid`/`*Extras`/`EvalEntry` (they are ALL
functions of `(N,A,SL)` + `decide`, independent of the case). This is the single
biggest dedup: today each `<Op>Resid` re-lists `SLlo`/`SLwin`/`sphiRam`/`sp8`/
`exprAl`/`exprLo`/`exprHi`/`exprWin`/`sretAl`/…/`codeStk`/`viStk`/`tableStk` etc.

### 2.2 `EvalCaseGeom` — the per-EvalE-node geometry oracle (the `blockA_k` inputs)

The residual `blockA_k` needs to synthesize `ArmEntryK` from `EvalEntry`, plus
the case-specific `hexprSurv`/`hMcallPop`. Parameterized by the op ROW.

```lean
structure OpRow where                 -- pure data, one per binary/unary/leaf case
  armPC   : BitVec 64
  tag     : Nat
  callee  : Mem → Prop                -- calleeLoaded predicate
  slotDef : Mem → Prop                -- <Case>SlotPinned
  -- (div/mod/mul/eqne also carry a callee-seam field; see §2.4)

structure EvalCaseGeom (S : TermShared) (row : OpRow)
    (st : SpecSt) (sp r sret aEnv aExpr : BitVec 64) (e : Expr) (m0 : Mem) : Prop where
  kind      : read32 m0 aExpr.toNat = some row.tag
  slot      : row.slotDef m0
  calleeOk  : row.callee m0
  calleeSurv: ∀ mem a8 dd, S.SL.lo ≤ a8 → a8+8 ≤ sp.toNat →
                row.callee mem → row.callee (writeMap8 mem a8 dd)
  exprSurv  : ∀ m', (∀ a, ¬(S.SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
                ExprRepr m' aExpr.toNat e
  mcallPop  : ∀ mcall, (∀ a, ¬(S.SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
                ∀ a, ∃ b, mcall[a]? = some b      -- the `hMcallPop`/`fullpop`
```

This IS the union of `NegExtras`/`BinExtras`/`hMcallPop` + `blockA_k`'s six
side-inputs. `<Op>Resid` (the ∀c' post-dispatch slot) is `EvalCaseGeom`'s twin
at the *post*-`TwoSubReturn` config; the two collapse into one geometry oracle
because both are `decide`/`ImageGeom`-derived. **The refactor**: express each
`<Op>Resid` as `fun c' => ArmPostGeom S row … c'` so `<Op>Resid = ArmPostGeom`
(one shared structure, per-row `opTok`/`slot`/`vint`-vs-`vbool`).

### 2.3 The `<case>_row` adapter shape (what the generator emits)

```lean
theorem eval<Op>_row (S : TermShared) (row := <Op>OpRow)
    (hGeom  : ∀ st sp r sret aEnv aExpr m0, EvalCaseGeom S row st sp r sret aEnv aExpr … m0)
    (hguard : <Op>Guards)            -- b≠0, overflow, store.size-stability (see §2.5)
    : ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt)
        (lv rv v : Value) (a a_1 a_2) ,
        mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_1 →
        mEvalE st d env (.binary <op> l r) st'' v (EvalE.binary …) := by
  intro …; intro ihl ihr; intro g N A SL φf φc sp r sret aEnv aExpr m0; intro c hEntry
  -- 1. blockA_k : EvalEntry → ArmEntryK   (from hGeom + S.geom, all `decide`)
  -- 2. eval<Op>Sim  … ihl ihr (hGeom-post as <Op>Resid via ArmPostGeom) hguard
  -- 3. chain Steps ; land EvalExitD
```

Because `mEvalE ≡ EvalIH` by `rfl` (probed), `ihl ihr` pass straight through as
the two `EvalIH` sub-derivations `evalAddSim`/`evalDivSim` demand. The body is
`blockA_k ≫ eval<Op>Sim ≫ blockD_v_rec` — **identical across all 10 binary ops**
modulo `(row, guard set, callee-seam)`. → `gen_m4_term_row.py`, one row/op.

### 2.4 Callee-contract bundle (the `C`/`S` classes)

For the leaf/native/loop cases the callee seam replaces the `<Op>Resid` slot:

```lean
structure TermCallees (S : TermShared) where           -- the `ErrShared.SC/HT` analogue
  valueInt   : ∀ …, value_int_spec_full …              -- leaf value_* specs
  valueBool  : …
  valueEqual : ∀ …, value_equal_spec_full …            -- eq/ne seam (LANDED)
  divdi3     : ∀ …, divdi3_spec …                       -- div/mod/mul libgcc seams
  envGet     : ∀ …, env_get_found …                     -- var (env_get HIT-tail, LANDED)
  -- OPEN (step 5, biggest gap):
  envDefine  : ∀ …, env_define_spec …                   -- assign/varInit/closure-fold
  malloc     : MallocContract …                          -- named-hyp, NOT axiom
  realloc    : ReallocOps …
```

`TermCallees` is threaded once (like `ErrShared`); each leaf/native `<case>_row`
projects the field it needs. `valueEqual`/`envGet`/`divdi3` are already landed;
`envDefine`/`malloc`/`realloc` are the step-5 residues, so these three are the
only genuinely-open `C` fields.

### 2.5 The open-guard bundle (`O`)

The genuinely-open per-case semantic residues, kept as an explicit named record
(they do NOT collapse to geometry):

```lean
structure TermGuards where
  binNonZero : ∀ b, div/mod b ≠ 0                        -- value-path (b=0 is M5)
  binNoOvf   : ∀ a b, ¬(a = -2^63 ∧ b = -1)              -- div/mul overflow
  storeSize  : ∀ …, st'.store.frames.size = st''.store.frames.size ∧ (closures)
  depthCrux  : d < maxCallDepth                          -- Call.closure
  -- loop measures (S): one termination measure per loop SHAPE (not per site)
  whileMeasure forMeasure argsMeasure seqMeasure : …     -- feed loopFromBody
```

`storeSize` is a `φ`-monotonicity fact that a general depth-indexed lemma would
discharge (noted in every binary goal); `binNonZero`/`binNoOvf` are the
value-path guards already carried in `EvalDivSimGoal`.

---

## 3. GENERATOR PLAN

Two generators, both `ErrorRouting`-shaped (data table → uniform emission):

1. **`gen_m4_term_row.py`** (model `gen_m5_error_routing.py` + existing
   `gen_m4_case.py`): reads `scripts/m4_term_rows.tsv` (one row per premise:
   `premise, thm, kind, armPC, tag, slotDef, callee, residStruct, guards, subIHs`).
   Emits `Vsa/Sim/rows/TermRouting.lean` with one `eval<Op>_row`/`exec<S>_row`
   per premise, body = `blockA_k ≫ <thm> ≫ blockD_v_rec` marshalling. The 10
   binary ops + the 5 leaf + the ~13 simple ExecS/leaf premises are PURE ROWS.

2. **`ImageGeom`/`ArmPostGeom` one-shot** (hand-written once, then reused): the
   shared `decide`-bundle; `<Op>Resid := ArmPostGeom S row` is a `def`-alias
   refactor per row-file (mechanical).

The capstone `term_sim_of_cases`/`execSeq_sim_of_cases` application is then
supplied by the generated rows positionally — exactly as `errFamily_of_sites`
consumes the 42 `route_*`. `termSimClosed` gets `TermShared`+`TermCallees`+
`TermGuards` as its three bundle args + `hEntryHalts`.

---

## 4. ESTIMATE + REFACTOR LIST

**Adapter split (of 50 premises + entry = 51):**

- **Pure table rows (~38):** all 15 EvalE except `hAssign` (14) — the 10 binary
  ops + 4 non-binary leaf/logical/unary; `hArgsNil`/`hArgsCons`; the 4 native
  `Call` (print/println/assert) minus closure; the ~13 simple ExecS
  (`hSExpr`…`hSRetNull`/`hSBrk`/`hSCont`, if-family, whileFalse); `hSeqNil`.
  These emit from a TSV row with the `blockA_k ≫ thm ≫ epilogue` body.
- **Bespoke (~13):** `hEntryHalts` (program-entry, 1); `hCallClosure` (depth
  crux + env_define-fold, 1); `hAssign`/`hSVarInit`/`hSVarNull`/`hSBlock`/
  `hSForStart` (native-store / env_define / allocFrame seams, 5); the loop
  back-edges `hArgsCons`-loop / `execSeqLoop` / `execWhileLoopSim` /
  `execForLoopSim` / for-scaffold `hFl*`/`hFc*`/`hEs*`/`hInit*` (`loopFromBody`
  shape, ~6 distinct SHAPES not sites). Loop rows are "bespoke per shape, row
  per site".

**Case theorems whose hypothesis lists DON'T fit the unified classes (need a
small refactor before the adapter is a pure row):**

1. **All 10 binary `Eval<Op>SimGoal`** — take `gouter gpre g` as THREE separate
   ghost frames + inline the `<Op>Resid` as a `∀ c', TwoSubReturn… → <Op>Resid`
   conjunct INSIDE the Triple entry, not as a hypothesis. *Change:* factor the
   entry's `∃ ment, ArmEntryK ∧ … ∧ (∀c', …<Op>Resid)` into
   `blockA_k`'s output + `ArmPostGeom` so the row supplies only geometry. (No
   proof change — a `def`-alias `<Op>Resid := ArmPostGeom` + reassociate the
   entry conjunction.)
2. **`evalNegSim`/`evalNotSim`** — carry `NegExtras`/`NotExtras`+`hMcallPop` as
   distinct structures. *Change:* rename-alias `NegExtras`→`EvalCaseGeom`
   fields (they are a subset) so the unary/binary rows share one geometry oracle.
3. **`evalVarSim`** — carries `env_get_found` as a naked hyp, not via a callee
   record. *Change:* route it through `TermCallees.envGet`.
4. **`evalEqNeSim`** (in-flight, do-not-edit) — its `EqResid`/`EqFrontData`
   already follows the DivResid template; only needs the `ArmPostGeom` alias to
   match. No structural change; wait for the sibling agent to land the reseat.
5. **`ExecS`/`ExecSeq`/loop cases** — their `ExecIH`/`SegEntry→SegExit` motive
   entries are NOT yet unified with `ExecCaseGeom` (the ExecS twin of
   `EvalCaseGeom`). *Change:* define `ExecCaseGeom` mirroring §2.2 and a
   `blockA_stmt` analogue of `blockA_k` (the `exec_stmt` dispatch prologue,
   `ExecDispatch.lean`); today each ExecS case re-derives its own entry.

**Recommended implementation order:**

1. Land `ImageGeom` + `ArmPostGeom` + the `<Op>Resid := ArmPostGeom` def-aliases
   (mechanical, no proof change) — this collapses the 10 binary geometry lists.
2. Write `EvalCaseGeom` + `eval<Op>_row` for ONE op (add) by hand; verify it
   discharges `hBinary` at `.add` through `term_sim_of_cases`.
3. `gen_m4_term_row.py` + `m4_term_rows.tsv`; fan out the other 9 binary ops +
   the 5 leaf + simple ExecS rows (COW-clone workflow, `lake env lean` verify).
4. `TermCallees`/`TermGuards` bundles; wire the leaf/native rows.
5. Bespoke: `hEntryHalts`, then the loop shapes via `loopFromBody`, then the
   env_define-gated cases (blocked on step 5's `env_define`/`realloc` contract).
6. Assemble `termSimClosed` from `TermShared`+`TermCallees`+`TermGuards`+entry;
   `#print axioms`; add to check_all.

Steps 1–3 close ~38 of 51 premises as pure rows; the remaining 13 are the known
semantic gaps (steps 4–5 of the completion plan), now each pinned to exactly one
bundle field.

---

## 5. IMPLEMENTATION LEDGER (steps 1-3, executed 2026-08-30)

State verified against CURRENT source (post store-size `nf nc` refactor, commit
b606376). Row bodies compiled with `lake env lean <file>` (isolated), axiom-clean
(`{propext, Classical.choice, Quot.sound}`); scratch-probes green.

### LANDED (green + axiom-clean)

- **`Vsa/Sim/rows/ArmPostGeom.lean`** (step 1). `ArmPostGeom` = the shared
  post-`TwoSubReturn` binary residual, parameterised by `(opTok : Nat)`,
  `(slotDef : Mem → Prop)`. Four thin adapters, ~1s elab:
  `armPostGeom_of_addResid`/`addResid_of_armPostGeom` (`AddResid ↔ ArmPostGeom 11
  AddSlotPinned`) and the `sub` pair (`12 SubSlotPinned`). MEASURED: `AddResid`
  and `SubResid` are byte-identical modulo exactly `opTok` (11 vs 12) and `slot`
  (`AddSlotPinned` vs `SubSlotPinned`) — the survey's §2.2 `<Op>Resid = ArmPostGeom`
  generalization is SOUND for the shared tail. (`ImageGeom` was already landed thin
  in `TermImageGeom.lean` at commit b0bccdc; left as-is.)

- **`Vsa/Sim/rows/TermRouting.lean`** (steps 2-3) + **`scripts/gen_m4_term_row.py`**
  + **`scripts/m4_term_rows.tsv`**. Generator (model `gen_m5_error_routing.py`)
  emits three row shapes from the TSV; regenerated output compiles green (~1s):
  - `eval_int_row` (leaf_direct) — fills `hInt` via `evalIntSimD` directly.
  - `eval_null_row`, `eval_bool_row` (leaf_bridge) — fill `hNull`/`hBool` by
    bridging `EvalEntry → EvalNullEntry`/`EvalBoolEntry` (record built from the 32
    shared `EvalEntry` projections + a 5-conjunct callee-geometry residual), then
    `evalNullSimD`/`evalBoolSimD`.
  - `eval_neg_row` (rec_unary) — fills `hNeg` via the already-motive-shaped
    `evalNegSim`, supplying `NegExtras` + `hMcallPop` keyed to the operand pointer
    extracted from the entry `ExprRepr`.

- **Pilot verification.** `/tmp/probe_fill.lean`: all four rows fill their EXACT
  `TermCaseBundle.TermCases` field slots (`hInt`/`hNull`/`hBool`/`hNeg`) via record
  update — type-checks the row types against the bundle premise types. Green.
  Wired into `Vsa.lean` (imports after `TermCaseBundle`) and `scripts/check_all.sh`
  THEOREMS (8 new capstones).

### DESIGN DEVIATIONS (honest, from real premise shapes)

1. **`eval_add_row` as the pilot is BLOCKED, not just mechanical.** The survey's
   step-2 pilot (`eval_add_row` composing `blockA_k ≫ evalAddSim ≫ blockD_v_rec`)
   presumes an `EvalEntry (.binary .add) → ArmEntryK@0x800034e8` bridge exists to
   prepend to `evalAddSim` (which starts from the `ArmEntryK`-∃ entry — `blockA_k`
   is factored OUT of it, unlike `evalNegSim` which INCLUDES `blockA_k`). No such
   binary-arm bridge is landed (`EvalBinSim4` stops at slot lemmas). Building it is
   ~200 lines of real machine-proof (reconstruct the EX_BINARY dispatch entry facts
   + `BinExtras` + `AddResid`-via-`ArmPostGeom` + the two-IH plumbing), NOT a table
   row. So the recursive PILOT here is **`eval_neg_row`** (neg's `evalNegSim` is
   already motive-shaped) — a working recursive-row demonstration — and add is on
   the blocked list.

2. **`hBinary` is a SINGLE ∀-op premise, not one-row-per-op.** `execSeq_sim_of_cases`'s
   `hBinary` (and `TermCases.hBinary`) quantifies over arbitrary `op : BinOp`,
   `lv rv v : Value` with `binOpSem st''.store op lv rv = some v`. The 10 landed
   `eval<Op>Sim` each cover only ONE op restricted to `.int`/`.str` operands (e.g.
   `evalAddSim`: `op=.add, lv=.int a, rv=.int b`). Filling `hBinary` needs a
   DISPATCHER that case-splits `op` × value-kinds and routes each arm — AND several
   kind combinations are NOT covered by the int-restricted sims (str concatenation
   for `.add`, str comparisons for `.lt/.le/.gt/.ge`). So the 10 binary rows the
   survey counts toward the ~38 do NOT individually fill a premise slot; they are
   inputs to one composite `hBinary` dispatcher that remains to be built (and whose
   str-operand arms are genuine gaps).

3. **Leaf entries are per-leaf structures, not `EvalEntry`.** Only `hInt` uses
   `EvalEntry` directly. `hNull`/`hBool`/`hStr`/`hVar` route through
   `EvalNullEntry`/`EvalBoolEntry`/`EvalStrEntry`/`EvalVarEntry`, each carrying
   extra callee-code/slot facts (and, for `var`, the `env_get_found` open oracle).
   Handled by the leaf_bridge shape (a per-leaf `<Leaf>Extras` residual) — confirms
   the survey's `EvalCaseGeom`-twin design, but the bridge is a real (small) record,
   not a def-alias.

### DEFERRED / BLOCKED (not emitted; each pinned to its gap)

- **eq/ne family** — per brief, the sibling agent owns it; not touched.
- **`hStr`** — needs CString `ExprRepr`/`ValueRepr` readback in the entry bridge
  (`R`-class); leaf_bridge extension, deferred.
- **`hVar`** — `evalVarSim`/`EvalVarEntry` bundle `env_get_found` (a Triple hyp,
  `O`-class open oracle); row is a conditional leaf_bridge, deferred to step-5.
- **`hAssign`, `hSVarInit`, `hSVarNull`, `hSBlock`, `hSForStart`** — native-store /
  env_define / allocFrame seams (env_define-gated per brief); deferred.
- **`hBinary`** — blocked on the ∀-op dispatcher + str-operand arms (deviation 2)
  and the binary-arm `blockA_k` bridge (deviation 1).
- **`hNot`, `hOrTrue`, `hOrFalse`, `hAndFalse`, `hAndTrue`** — TRACTABLE (their
  `eval*Sim` are already motive-shaped like `evalNegSim`, with `<Op>Extras`
  [+`aEnv3` Steps-residual for the two-eval cases] + `hMcallPop`). Same rec-row
  recipe as `eval_neg_row`; not emitted this pass only for time (add to the TSV as
  `rec_unary`/`rec_logical` shapes next).
- **`hCall`, `hFn`, `hCallClosure`, `hArgs*`, native `Call`** — call subsystem;
  deferred.
- **All `ExecS`/`ExecSeq`/`ExecInit`/`ForLoop`/`ForCond`/`ExecStep` premises** —
  need `ExecCaseGeom` + a `blockA_stmt` analogue of `blockA_k` (survey §4 refactor
  5); the exec dispatch prologue is not yet factored into a reusable entry bridge.
  Deferred to a follow-on ExecRouting pass.

### Count

Rows landed filling real premise slots: **4** (hInt, hNull, hBool, hNeg), all
green + axiom-clean + slot-verified. Tractable-next (documented recipe, ~5): hNot,
hOrTrue, hOrFalse, hAndFalse, hAndTrue. The survey's "~38 pure rows" over-counts:
the 10 binary rows collapse to ONE dispatcher premise (blocked), and every ExecS
row needs the un-built `blockA_stmt`. Realistic pure-row EvalE frontier now =
{int,null,bool,neg,not,orTrue,orFalse,andFalse,andTrue} = 9, of which 4 landed.

---

## APPENDIX — BINARY-ARM ENTRY BRIDGE `blockA_binaryArm` (LANDED 2026-08-30)

Deviation-1 ("`eval_add_row` BLOCKED on the missing `EvalEntry (.binary) →
ArmEntryK@0x800034e8` bridge") is now **UNBLOCKED**.  New files (both green,
axiom-clean = `[propext, Classical.choice, Quot.sound]` only; ≤1.3s/file elab):

* **`Vsa/Sim/rows/BinArmBridge.lean`** — `blockA_binaryArm` (the bridge) +
  `BinArmExtras` (its `NegExtras`-analogue residual bundle).
* **`Vsa/Sim/rows/BinArmBridgeProbe.lean`** — `binArm_add_entry_connects` (the
  composition probe).

### What the bridge proves

```
blockA_binaryArm :
  Triple (EvalEntry g … st d env (.binary op el er) sp r sret aEnv aExpr m0)
         (fun c => ∃ gpre aEnvReg v8 v9 v18 v19 ment,
            ArmEntryK g … 0x800034e8 UnaryArmCallee (.binary op el er) … ment c
            ∧ BinExtras … ∧ <x11/x13/x19 + gpre frame + operand reads
                             + ExprRepr el/er + hMentPop + MemExtends m0 ment>)
```

i.e. **exactly the `blockB_binary` entry** (`EvalBinSim.lean:262`), which is the
entry every `eval<Op>Sim` starts from (`blockA_k` factored out).  ONE proof,
**operator-INDEPENDENT** (parameterised over `op : BinOp` — the operator token is
not read until `0x8000351c`, after both recursive calls).  Body = `evalNegSim`'s
block-A pattern transposed to the binary node (tag `k = 6`, arm `0x800034e8`,
`e := .binary op el er`, `calleeLoaded := UnaryArmCallee`): run `blockA_k` →
repackage its `ArmEntryK` with the binary-arm extras.  `gpre := c1.σ.regs.get?`
(frame `rfl`); `x11`/`x8`/`x18` off the widened `ArmEntryK`; the two operand
pointers + `ExprRepr` peeled from `ExprRepr.binary` (offsets 16/24).

### `BinArmExtras` — the supplied residual (all M6-Layout / `EvalCaseGeom`-widening
facts, stated over the ENTRY `m0`, threaded like `NegExtras`):
slot-6 pin `KindSlotPinned 6 0x800034e8`; node/operand geometry (BinExtras
mirror); `pay_l`/`pay_r` (the two operand-ptr reads); `expr_survives` +
`lexpr_surv`/`rexpr_surv` (AST survival closures); `frame_pop` (the `[sp-1120,sp)`
population, `hMcallPop`-style); `tableStk` strengthened to slot 6 (`+28≤SL.lo`);
plus **three genuinely-residual register/memory facts** blockA_k does NOT expose:
- `gx19_pres : ∃w, g x19 = some w` — `s3` ghost presence (EvalEntry.spill_defined
  covers only s0/s1/s2; `blockA_k`'s frame ties `c1.regs x19 = g x19`).
- `x13_pres` — `a3` machine-liveness at the arm (a caller-save temp NOT covered by
  `blockA_k`'s callee-saved frame; the dispatch span never writes a3).  The ONE
  register a `blockA_k` widening (tracking `x13`) would internalise.
- `mem_ext` — `MemExtends m0 ment` presence-monotonicity closure (the prologue
  spills are inserts; `EvalExitD`-presence widening).

### Composition probe (`binArm_add_entry_connects`)

`blockA_binaryArm ≫ blockB_binary` at `.add`/int operands:
`Triple (EvalEntry (.binary .add el er)) (∃ gpre v8 v9 v18, TwoSubReturn …)`.
The bridge's ∃-ghosts unpack straight into `blockB_binary`'s ∀-parameters — the
seam is `rfl`-tight (only the two `EvalIH` sub-derivations + the left-value
survival closure thread through).  **The `ArmEntryK`-∃ entry the case theorems
consume is now PRODUCED from the `hBinary` recursor premise's `EvalEntry`.**

### What `hBinary` STILL needs (precise)

1. **The op×kind DISPATCHER (deviation-2).** `hBinary` quantifies over arbitrary
   `op : BinOp` + `lv rv v` with `binOpSem st''.store op lv rv = some v`
   (`Semantics.lean:258`).  The bridge+`blockB_binary`+`blockC_<op>` chain covers
   ONE `(op, kind)` cell each; a top dispatcher must case-split `op` × operand
   value-kinds and route each cell.  This is a `.binary`-arm analogue of the leaf
   kind-dispatch, NOT yet built.  Per bridge, each cell's entry is now uniform.
2. **The row-level residuals PER cell** (thread THROUGH the bridge unchanged): the
   op-specific `∀c' TwoSubReturn → <Op>Resid` post-dispatch slot (the `ArmPostGeom`
   twin) + the outer `g`-bridge conjuncts + the guard set (`b≠0`/overflow for
   div/mod/mul, `store.size`-stability).  The bridge deliberately does NOT produce
   `<Op>Resid`/the g-bridge — they are consumed by `blockC_<op>`/`blockD_v_rec`
   downstream, so they compose after, exactly as `evalAddSim` does today.
3. **STR-OPERAND arms are genuine gaps** (from `binOpSem`): `.add` str
   concatenation (`str++`/`display`), and `.lt/.le/.gt/.ge` STR comparisons
   (`a < b` on `String`).  The 10 landed `eval<Op>Sim` are all `.int`-restricted
   (`eq/ne` cover all kinds via `value_equal_spec_full`, already landed).  So the
   str cells of `add`/`lt`/`le`/`gt`/`ge` need NEW block-C tails (the strcmp /
   string-concat callee seams) — the bridge+entry is shared, the block-C is not.

Net: the bridge removes the SINGLE structural blocker (entry linkage) common to
all 10 ops.  Remaining `hBinary` work is (a) one op×kind dispatcher shell, (b) the
existing per-cell `blockC_<op>` + row residuals composed after the bridge (add/sub/
lt/le/gt/ge/mul/div/mod/eqne int cells all have their block-C landed), (c) the 5
str cells' new block-C tails.

### LEDGER — `hBinary` DISPATCHER LANDED (2026-08-30)

Deviation-1/2 of the appendix are now CLOSED.  New files (all green, axiom-clean =
`[propext, Classical.choice, Quot.sound]`; elab: `BinDispatchRow` 3.5s, probe 1.2s):

* **`Vsa/Sim/rows/BinDispatchRow.lean`** (GENERATED by
  `scripts/gen_bin_dispatch_row.py`) — 11 per-op row lemmas `binRow_<op>` (each =
  `blockA_binaryArm ≫ eval<Op>Sim(D)`, from the `EvalEntry (.binary op el er)`
  recursor entry straight to `EvalExitD`) + the dispatcher shell **`eval_binary_row`**.
* **`Vsa/Sim/rows/BinDispatchProbe.lean`** — `binary_row_fills_hBinary`: the
  decisive slot-verify (`eval_binary_row` applied to its 18 residual slots, ascribed
  to the VERBATIM `hBinary` premise type — type-checks, so the shell fills the slot).

**Generated vs hand.**  The 9 int-op rows (add/sub/mul/div/mod/lt/le/gt/ge) are
SYNTACTICALLY UNIFORM modulo the 5-tuple `(op token, value form, <Op>Resid struct,
sim name, guards)` — emitted from the generator's `INT_ROWS` table.  eq/ne resisted
Lean-level uniformity (they use `evalEqSimD`/`evalNeSimD`, whose precondition is a
DIFFERENT shape: a SEPARATE `hResid`/`hVlSurv` rather than the inline
`AddResid`/g-bridge conjuncts) — emitted from their own template.  The shell's
op × operand-kind case tree is not table-uniform (`binOpSem`'s success condition
differs per op: int ops need `.int a, .int b`; div/mod add `b ≠ 0` guards; cmps need
ints; eq/ne any kind; add/cmps have str cells) — hand-templated.

**`hBinary` closed MODULO exactly these slots** (all named, none hidden):
- 9 int-op providers `hIAdd…hIGe : BinIntCellResid <op> <Resid> …` (∃-commits the
  operand nodes `aLOp aROp`, the left word `Wl`, store-size stability, `BinArmExtras`,
  and the post-dispatch `∀c' TwoSubReturn → <Op>Resid` + g-bridge slot) — the
  `evalDivRow`-style row residual an M6 `EvalCaseGeom` widening supplies;
- `hIDiv` additionally takes the no-overflow premise `¬(a = -2^63 ∧ b = -1)`
  (`binOpSem .div` supplies only `b ≠ 0`; the div sim demands ¬overflow — the machine
  `__divdi3` path differs);
- 2 eq/ne providers `hEq`/`hNe : BinEqCellResid …` (∃-commits `aLOp aROp w19` + the
  left-value survival closure + the `EqResid` front residual);
- **5 STR-cell residual slots** `hStrAddL`/`hStrAddR`/`hStrLt`/`hStrLe`/`hStrGt`/`hStrGe`
  — genuine gaps (`binOpSem` succeeds on strings, NO sim exists), each a whole-node
  `EvalIH` the shell routes to unchanged;
- 1 div-overflow slot `hDivOv` (whole-node `EvalIH` at `INT64_MIN / -1`).

Everything else is discharged inside the shell by `binOpSem`-inversion (`cases op`
then `match lv, rv`; each non-succeeding kind pair falls to `none = some v`
contradiction; each succeeding cell routes to its `binRow_<op>`).  The bridge's
existential ghosts (`gpre`/`aEnvReg`/`v8..v19`/`ment`) unpack `rfl`-tight into each
`eval<Op>Sim(D)` — the seam re-derives nothing.

INFEASIBLE-WITHOUT-RESIDUAL (honest): the 5 str cells need the string
concat/`strcmp` block-C tails (no sim exists yet); store-size stability across the
right sub-derivation is a genuine spec-level residual (no monotonicity lemma); div
overflow is a genuine machine-path residual.  All three are surfaced as typed
slots, not `sorry`.

---

## 6. LEDGER APPENDIX — logical/not/str rows (executed 2026-08-30)

The five "tractable-next" rows from §5 are LANDED, plus `hStr` (deferred there,
re-examined and found to be a pure leaf_bridge). `TermRouting.lean` now has
**10 rows**; all compiled isolated (`lake env lean`, ~1.0s file elab), axiom-clean
(`{propext, Classical.choice, Quot.sound}`), and slot-probed (record-update fill
of the exact `TermCases` field, all 6 new slots in one probe, 3.9s green).

### Rows landed

- **`eval_not_row`** (`hNot` → `evalNotSim`) — new `rec_not` shape: `eval_neg_row`
  verbatim except the operand value is an arbitrary `vsub : Value` (spec-level in
  the residual `NotResid esub vsub`) and the produced value is `.bool (!vsub.truthy)`.
  Pure table row + small template variant; `NotSimExtras` takes no `st` (unlike
  `NegExtras`).
- **`eval_orTrue_row`**, **`eval_andFalse_row`** (`hOrTrue`/`hAndFalse` →
  `evalOrTrueSim`/`evalAndSim`) — new `rec_logical1` shape (one-IH short-circuit):
  like rec_unary but the extracted pointer is the LEFT operand (logical node payload
  offset 16), and the residual additionally carries the `aEnv3` x13-survival
  Steps-residual the logical sims take. Since `aEnv3` is a per-entry-config ghost,
  the residual is quantified over the entry `c` and ∃-quantifies `aEnv3` (the row
  obtains the witness and passes it to the sim).
- **`eval_orFalse_row`**, **`eval_andTrue_row`** (`hOrFalse`/`hAndTrue` →
  `evalOrFalseSim`/`evalAndTrueSim`) — new `rec_logical2` shape (two-IH): as
  rec_logical1 plus the RIGHT operand pointer (offset 24, second `ExprRepr`
  extraction from the same `logical` constructor) and the second IH threaded to the
  sim; the `<Op>Extras` take the mid/post spec states `st' st''` and both values.
- **`eval_str_row`** (`hStr` → `evalStrSimD`) — plain **leaf_bridge**, NOT the
  feared R-class CString-readback bridge. MEASURED against current `EvalStrEntry`
  (EvalStrSim.lean:550): it is exactly `EvalEntry`'s 32 shared projections + 7
  extra conjuncts (`str_stack_disjoint`/`str_sret_disjoint`/`sret_vstrcode_disjoint`/
  `vstrcode_stack_disjoint`/`value_str_code`/`str_slot`/`table_stack_disjoint`).
  The two `str_*` fields are ∀-quantified over the payload pointer
  (`∀ p, read64 c.σ.mem (aExpr+8) = some p → …`), so the bridge never reads the
  CString — the residual provider supplies the geometry hypothetically. Template
  change: leaf_bridge dicts gained `vbinds` (value binders, e.g. `(s : String)`)
  and `extra_ghosts` (extra resid ∀-ghosts; str threads `aExpr`); null/bool
  regenerate byte-identical.

### Template extensions (gen_m4_term_row.py)

Three new shapes (`rec_not`, `rec_logical1`, `rec_logical2`) + the generalized
`leaf_bridge` (dict-driven value binders/ghosts). New shared text constants
`MCALLPOP` (M6 populated-memory residual) and `X13RESID` (the ∃`aEnv3` Steps
residual). Header now imports `EvalLogical4` (covers all four logical sims +
`EvalNotSim` transitively) and opens `Steps`.

### Count update

Rows landed filling real premise slots: **10** (hInt, hNull, hBool, hStr, hNeg,
hNot, hOrTrue, hAndFalse, hOrFalse, hAndTrue) — the full realistic pure-row EvalE
frontier from §5 (9) plus hStr. Remaining EvalE premises are all genuinely gated:
hVar (env_get_found oracle), hAssign (env_define), hBinary (∀-op dispatcher +
str arms), call subsystem, and the ExecS/loop family (blockA_stmt).

---

## LEDGER — step-6b: the `ExecS` statement-leaf rows (LANDED)

**The real gap was BUNDLE-ONLY, not a new machine proof and not a `blockA_stmt`
build.** The survey's §5 note ("all ExecS/loop premises need `ExecCaseGeom`/
`blockA_stmt`") was pessimistic: `execBlockA` (prologue+dispatch, UNCONDITIONAL)
+ `execBlockD` (epilogue) ALREADY landed (`ExecBrkCont.lean`), and the register-
only leaf sims `execBrkSim`/`execContSim` already compose them into a full
`Triple (ExecEntry ∧ sailOutput=out0) (ExecExit …)` unconditionally (modulo the
jump-table slot pin + its stack-disjointness — the same geometry the EvalE leaves
carry as `EvalEntry` fields). So NO `ExecEntry→execBlockA` bridge was missing.

The ONLY gap between the landed sim and the recursor's `hSBrk`/`hSCont` premise
(which, via `TermSimAssembly.mExecS = ExecBlock.ExecIH` by `rfl`, is
`∀ ghosts, Triple (ExecEntry …) (ExecExitD …)`) is the exact statement-side twin
of the `EvalLeafD` gap:

1. **entry `out0`** — drop the sim's `∧ sailOutput = out0` conjunct by taking
   `out0 := c.σ.sailOutput` (`rfl`). Pure marshalling.
2. **exit `ExecExit → ExecExitD`** — add `MemExtends m0 mem` + the
   `[SL.lo,SL.hi)`-store-survival clause. Re-supplied as the honest exit-quantified
   widener `ExecLeafWiden` (the `LeafWiden` twin), true of every register-only leaf
   (delta = the prologue `writeMap8` spills, presence-preserving; store `= st`,
   footprint-disjoint from `[SL.lo,SL.hi)`).

### Deliverables

- **`Vsa/Sim/rows/ExecCaseGeom.lean`** (the bundle + bridge, hand-written once):
  - `ExecLeafWiden` — the two `ExecExitD` upgrade clauses as an exit-quantified
    widener (`LeafWiden` analog).
  - `execExitD_of_execExit` — `ExecExit ∧ ExecLeafWiden → ExecExitD` at identity φ
    (`evalExitD_of_evalExit` twin).
  - `ExecCaseGeom g N A SL φf φc st status k armPC sp r aRet m0` — the per-leaf
    recursor-supplied residual = `StmtSlotPinned k armPC m0` ∧ its stack-disjoint
    disjunct ∧ `ExecLeafWiden`. (The `ArmPostGeom` twin: one bundle, per-row
    `(k, armPC, status)`.)
  - `execBrkSimD`/`execContSimD` — the register-only leaves re-landed at
    `ExecExitD` (compose the landed `execBrkSim`/`execContSim` with the bridge;
    do NOT re-prove the run).
- **`scripts/exec_rows.tsv` + `scripts/gen_exec_row.py`** → **`Vsa/Sim/rows/ExecRouting.lean`**
  (GENERATED): `exec_brk_row`/`exec_cont_row`, each routing the real
  `hSBrk`/`hSCont` premise onto the `*D` lemma with a `<Key>Resid` = the
  `ExecCaseGeom` bundle ∀-closed over the ghosts.
- `Vsa.lean` imports both new files; `scripts/check_all.sh` THEOREMS extended with
  `execExitD_of_execExit`, `execBrkSimD`, `execContSimD`, `exec_brk_row`,
  `exec_cont_row`.

### Verification

Pilot `exec_brk_row` slot-verified against the REAL `hSBrk` premise of
`execSeq_sim_of_cases` (record-update/`show ExecIH` probe, `/tmp/exec_brk_probe.lean`,
green); `exec_cont_row` likewise. All five new declarations axiom-clean
(`[propext, Classical.choice, Quot.sound]` only). Each file elaborates <1s isolated
(well under the 120s budget; deps cached). No `sorry`/`axiom`/`native_decide`/
`bv_decide`; landed statements unchanged (bundle/adapter/rows only).

### Rows emitted vs candidates (honest per-row)

- **EMITTED (2)**: `hSBrk`, `hSCont` — register-only leaves; sims fully
  unconditional modulo geometry; `ExecLeafWiden` (identity-φ, unchanged store,
  spill-only delta) applies verbatim.
- **BLOCKED — NOT emitted (per-row reasons)**:
  - `hSRetNull` (`execRetNullSim`) — carries an OPEN `hGlue` residual (arm setup +
    `beqz`-TAKEN `value_null` bridge → `SubExecReturnR`) AND writes the retslot
    `[aRet,aRet+24)`, a `memFrame` disjunct the current `ExecLeafWiden` does not
    cover. Needs a retslot-aware widener + `hGlue` closed. (Store `= st`, so the
    φ side is identity — only the retslot-window widener + glue are missing.)
  - `hSVarNull` (`execVarDeclNullSim`) — OPEN `hGlue` (env_define is NOT a landed
    Triple; M3 verified only its prologue) AND the exit store CHANGES to
    `st.store.define env x null` (non-identity φ), so the identity-φ leaf widener
    does not apply. Needs the recursive-shaped `ExecExitD` reland + env_define.
  - `hSExpr` (`execExprSim`), `hSRet` (`execRetSim`) — recursive (a sub-`EvalIH`),
    exit store `= st'.store` (sub-eval mutated, non-identity φ); these are
    `armExec_rec`/`SubExecReturn` territory, not a leaf widener. `hSRet` adds the
    retslot write on top.
  - All dispatch/loop cases (`hSBlock`/`hSIf*`/`hSWhile*`/`hSForStart`/for-loop
    scaffold/`hSeqConsNormal`/`hSeqConsAbrupt`) — recursive with sub-`ExecIH`/
    `mExecSeq` premises + allocFrame/env geometry; out of scope for the leaf-row
    family.

**Net: 2 statement-leaf rows landed** (brk/cont), each an EXPONENTIATING template
instance — the `ExecCaseGeom` bundle + `execExitD_of_execExit` bridge + the
`gen_exec_row.py` `leaf_reg` shape mean any future register-only statement leaf is
one TSV line. The statement side now has the `blockA_k`/`ArmPostGeom`/`*SimD`/
`gen_*_row` equivalents the EvalE side had; the remaining ExecS premises are all
genuinely gated (open `hGlue`/env_define/non-identity-φ/recursive), not
shape-gap-blocked.
