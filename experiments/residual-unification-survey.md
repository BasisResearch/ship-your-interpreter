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
