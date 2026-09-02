# Cluster design — env-seam (13 fields)

**Fields.** hArgsCons, hArgsNil, hCall, hCallAssertOk, hCallClosure, hCallPrint,
hCallPrintln, hInitStore, hSBlock, hSForStart, hSVarInit, hSVarNull, hVar.

Each touches the environment/store machinery (env_new, env_define, env_get,
env_set, exec_stmt-on-body). Distinguished by needing callee-contract glue (X6)
and/or the loop-knot IH (X4). NOT a single statement shape.

## Sub-partition

| Sub | Fields | Blocker |
|-----|--------|---------|
| **ES-var** (3) | hVar, hSVarInit, hSVarNull | X6 env_get_found / env_define splice |
| **ES-call-native** (4) | hCall*, — routed here: hCallPrint/Println/AssertOk feed via io | X6 native seams (see io doc) + hCall arm |
| **ES-call-crux** (1) | hCallClosure | X7 depth crux — whole-premise by design |
| **ES-args** (2) | hArgsNil, hArgsCons | X5 seq/args span code-grounding + loopFromBody |
| **ES-loop-body** (2) | hSBlock, hSForStart | X4 self-referential loop IH |
| **ES-prologue** (1) | hInitStore | X8 interp_init store repr (not an entry need) |

## (a) Amended / new statement shapes

The env-seam fields are mostly correctly-stated-but-unsupplied (X6/X4/X5) — the
CONTENT is a callee contract or the loop knot, not a falsity. The amendments
here are (1) the `entry` carry where a slot/geometry conjunct is asserted free,
(2) restating the callee-glue premises as named-field structures.

### ES-var: env_get / env_define glue as named contracts

```lean
/-- hVar: the env_get_found caller-linkage. `VarLeafResid` currently carries the
    oracle as a bare ∀-premise; restate with the LANDED contract as a field. -/
structure VarArmResid (st : SpecSt) (x : String) (v : Value) : Prop where
  entry    : EvalEntry …                       -- carry (geometry precondition)
  found    : EnvGetFound st x v                 -- TermCallees.envGet contract (LANDED)
  bridge   : EvalVarCallBridge st x v           -- eval-var-arm → env_get jal seam (MISSING)
  exit     : EvalExitD … (.var x) v
```

`env_get_found_uncond''` is LANDED (memory: EnvGetSpec6); the residual is
EXACTLY the `bridge` field (the arm→callee jal linkage). Same shape for
hSVarInit/hSVarNull with `EnvDefineSplice` (TermCallees.envDefine, the
composition is LANDED per envdefine-composition memory; the residual is the
Shape-A straight-line bridges).

### ES-args: the args loop as loopFromBody (X5)

```lean
/-- hArgsCons: per-iteration body oracle + fall-through. NOT a falsity — needs
    the `SegEntry` code-grounding (X5, mEvalArgs table entry missing). -/
structure ArgsConsResid (st : SpecSt) (d : Nat) (env : Addr) : Prop where
  bodyStep : EvalArgsBodyStep st d env         -- one iteration (loopFromBody obligation)
  ground   : SeqSpanGround evalArgsLoopPC       -- CODE linkage (X5; SeqSpanGround landed for seq)
```

The B6 obstruction (code-free `SegEntry`) is the exact blocker: `mEvalArgs`
needs a `SeqSpanGround`-style code pin. `SeqSpanGround` LANDED for seq; the args
twin is the missing table entry.

### ES-loop-body / ES-call-crux: NOT amendable (X4/X7)

hSBlock/hSForStart (`hstep`/`hForIH`) and hCallClosure are self-referential
oracles supplied by the CAPSTONE recursor, not by any bridge. Their statement
shape is correct-as-oracle; they are threaded per-derivation
(`armResidGap_of_stages` shape). NO statement amendment — flag as
recursor-threaded.

## (b) Invariants / bridges to mine

- **ES-args**: relational multi-seam (the round-3 open risk: `hCall`/`hSVarInit`
  need a real per-event alignment key, not tag-histogram). Mine the args loop:
  probe the loop head + the args-count reg + the store-frames size; align spec
  `evalArgs` steps by event index. Grounds `EvalArgsBodyStep` + the measure.
- **ES-var**: relational value-repr — `gprGet a0 = reprOf(env_get result)`. This
  is the untested "value-repr conjunct" class (round-3 open risk): the spec
  driver must emit the actual `Value` and its repr, machine probe dumps the
  boxed pointer + reads back the payload. Pilot this on hVar FIRST as the
  value-repr technique acceptance test.
- **ES-loop-body/crux**: LLM-heavy (recursion depth/budget relations). The crux
  depth ladder was refound by the falsity-#13 depth trace — re-run at depth 2-3
  to seed the `hCallClosure` stackBudget relation (already the ITEM-ZERO budget
  layer, StackNeed.lean, LANDED). Mining CONFIRMS, doesn't discover.

## (c) Supplier DAG

```
env_get_found_uncond'' (EnvGetSpec6)   ── LANDED
env_define composition                 ── LANDED (envdefine-composition)
env_new / value_null                   ── LANDED
EvalVarCallBridge (arm→env_get jal)     ── MISSING (ES-var residual)
EnvDefineSplice straight-line bridges   ── MISSING (Shape-A: strlenPre/mallocPre/…)
SeqSpanGround (args twin, mEvalArgs)    ── MISSING (X5 table entry)
loopFromBody / SegEntry code pin        ── LANDED (loopFromBody); args table entry MISSING
StackNeed budget layer (crux)           ── LANDED (B0); budgeted entry re-index B1 in flight
Capstone recursor IHs (hSBlock/ForStart) ── the assembly itself (X4)
InterpInitStoreRepr (hInitStore)        ── MISSING (X8, interp_init decode)
```

## (d) Proving-task decomposition (bounded, ≤1 session each)

1. **T-ES-var-bridge** (×1): `EvalVarCallBridge` = the eval-var-arm → env_get jal
   seam (5-block slice, corpus hVar). Then discharge `VarArmResid` via LANDED
   `env_get_found`. Template: `bridgeOfSeg` + EnvGetSpec6.
2. **T-ES-vardecl** (×1): `EnvDefineSplice` bridges for hSVarInit/hSVarNull.
   Template: envdefine-composition Shape-A (strlenPre landed as precedent).
3. **T-ES-args** (×1): `mEvalArgs` SeqSpanGround table entry + `ArgsConsResid`
   body via loopFromBody; hArgsNil = seg-identity. Template: `SeqSpanGround`
   (seq) + `loopFromBody`.
4. **T-ES-call-arm** (×1): hCall `CallArmSpec` arm + widen (non-crux path).
   Template: `callSeg`/`CallResid`.
5. **T-ES-crux** (×1, HARD, sibling-owned): hCallClosure depth crux via
   StackNeed budget. Template: falsity-#13 budget layer.
6. **T-ES-loopbody** (recursor-threaded, NOT bounded here): hSBlock/hSForStart
   supplied at capstone assembly. Flag only.
7. **T-ES-initstore** (×1): hInitStore = `InterpInitStoreRepr` off-path decode.
   Template: X8 interp_init span.
8. **T-ES-native-print** (routed to io doc): hCallPrint/Println/AssertOk.

Bounded tasks (this cluster, excluding io-routed + recursor-threaded):
**≈6** (var-bridge, vardecl, args, call-arm, crux, initstore).
