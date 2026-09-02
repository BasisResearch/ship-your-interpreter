# SUPPLIER-BATCH — per-field, per-branch SMT-validated invariant sets

Date: 2026-09-02. Tool: `scripts/autoprove.py --batch supplier` (z3 4.15.4, whole run <2s). Generated from the JSON coverage; per-field rows are
the tool's per-branch verdicts, NOT a claim that any whole field closes.

## What autoprove now does per supplier field (PART 1 integration)

Each field's residual is sliced into BRANCHES; autoprove hands an SMT verdict per branch:

- **FRAME-Z3-CLOSED** — `ExecLeafMemPin` (`pres`=MemExtends, `agree`=window-frame) encoded
  via the `wlogM`-extracted write-log; Z3: agree UNSAT ∧ pres UNSAT ∧ ctrl-window SAT.
- **SURVIVAL-IH-VALIDATED** — the recursive `StoreRepr` survival, run INLINE: Houdini
  selects the IH, then the structural induction on the `frames` vector is base/step-
  DECOMPOSED and Z3-validated: `base P(nil)`=UNSAT, `step (∀p,P)→P(node)`=UNSAT under the
  IH, wall(no-IH)=SAT (non-vacuous). IH = `storeRepr_agreeP@parent-frame(IH)` +
  `{valueRepr_agreeP@valhdr, frameRepr_agreeP@nameptr, cstring_agreeP@{name,valstr}+tails}`.
  This is a **Z3-SUFFICIENCY-CERTIFIED IH**, not a Lean proof (base+step both UNSAT under it).
- **COMPOSITION-DEFER** — the arm's `Triple`/`*Geom`/sub-`ExecIH`/native-seg: ∀-closed
  machine-step content, out of solver scope → landed marshalling (`segToTriple`,
  `bridgeOfSeg`, `callSeg`, `FrameMeta`, `WidenMeta`). ALWAYS present; no whole field closes here.
- **NOVEL** — Houdini vocabulary insufficient → LLM request/response protocol. (none fired.)

## Coverage: 14/24 FRAME-Z3-CLOSED · 14/24 SURVIVAL-IH-VALIDATED · 0 NOVEL · 10/24 no-frame

## Per-field per-branch table

| field | FRAME | SURVIVAL-IH | COMPOSITION-DEFER residual (→ landed marshalling) |
|---|---|---|---|
| `hSExpr` | Z3-CLOSED | VALIDATED (base+step UNSAT) | ExecExprGeom Triple + StoreRepr survival |
| `hSRet` | Z3-CLOSED | VALIDATED (base+step UNSAT) | ExecRetGeom Triple + StoreRepr survival |
| `hSBlock` | Z3-CLOSED | VALIDATED (base+step UNSAT) | SeqSegIH (recursive) + StoreRepr survival |
| `hArgsNil` | — | — (no frame slice) | Triple PC-hop |
| `hArgsCons` | — | — (no frame slice) | EvalArgsStep + Triple |
| `hVar` | Z3-CLOSED | VALIDATED (base+step UNSAT) | VarPostCall Triple + LeafWiden + StoreRepr survival |
| `hAssign` | Z3-CLOSED | VALIDATED (base+step UNSAT) | AssignArmSpec arm oracle + StoreRepr survival |
| `hInitStore` | — | — (no frame slice) | Steps ; SegEntry |
| `hCall` | — | — (no frame slice) | composite call splice |
| `hSVarNull` | Z3-CLOSED | VALIDATED (base+step UNSAT) | value_null+env_define + StoreRepr (Store.define grows frames) |
| `hSVarInit` | Z3-CLOSED | VALIDATED (base+step UNSAT) | VarInit arm Triple + StoreRepr survival |
| `hSIfNone` | Z3-CLOSED | VALIDATED (base+step UNSAT) | IfGeom Triple + StoreRepr survival |
| `hSIfTrue` | Z3-CLOSED | VALIDATED (base+step UNSAT) | sub-ExecIH + StoreRepr survival |
| `hSIfFalse` | Z3-CLOSED | VALIDATED (base+step UNSAT) | sub-ExecIH + StoreRepr survival |
| `hSWhileFalse` | Z3-CLOSED | VALIDATED (base+step UNSAT) | WhileGeom Triple + StoreRepr survival |
| `hSWhileBreak` | Z3-CLOSED | VALIDATED (base+step UNSAT) | loop-break span + StoreRepr survival |
| `hSForStart` | Z3-CLOSED | VALIDATED (base+step UNSAT) | loop scaffold seg + StoreRepr survival |
| `hSRetNull` | Z3-CLOSED | VALIDATED (base+step UNSAT) | value_null bridge + StoreRepr survival |
| `hSeqNil` | — | — (no frame slice) | Triple PC-hop |
| `hSeqConsNormal` | — | — (no frame slice) | Triple + head ExecIH |
| `hSeqConsAbrupt` | — | — (no frame slice) | Triple + head ExecIH |
| `hCallPrint` | — | — (no frame slice) | ∀-closed native seg |
| `hCallPrintln` | — | — (no frame slice) | ∀-closed native seg |
| `hCallAssertOk` | — | — (no frame slice) | ∀-closed native seg |

## Validated INVARIANT SET per field (the honest claim)

We claim the validated **invariant set**, NOT that the field closes. For the 14
frame-reachable fields:

- **FRAME invariant** (Z3-UNSAT): `MemExtends (pres) + window-agree [SL.lo,sp) (agree)` — over the arm's `wlogM`-extracted spill stores.
- **SURVIVAL IH** (Z3-sufficiency-certified, base+step UNSAT): `storeRepr_agreeP@{valhdr,nameptr,name*,valstr*,tails} + parent-frame(IH)`.

For the 10 no-frame fields: NO straight-line write-log slice (pure PC-hop / recursive
call-splice / ∀-closed native seg), so neither branch encodes; the whole arm is a
COMPOSITION-DEFER to landed marshalling.

## Honest per-field residual

Every field — frame-reachable or not — keeps a COMPOSITION-DEFER residual: the arm
`Triple` that composes the frame slice + survival IH + the machine-step span into the
landed spec is ∀-closed over machine semantics and is OUT of the bounded-SMT fragment.
The two SMT-validated branches (frame + survival-IH) are DESIGN-TIME certificates that
the load-bearing invariants hold + are sufficient; they do NOT discharge the Lean
obligation. Specific extra residuals:

- `hSVarNull`: GROWS frames (`Store.define`) → survival certifies the KEPT frames, but the
  NEW binding needs a `φf'` from the widener (`WidenMeta`), not pure survival.
- `hVar`/`hAssign`: eval-arm spill OFFSETS differ from brk/cont's; the brkCont write-log is
  a faithful frame-slice STAND-IN (window reasoning is offset-agnostic).
- `hSIfTrue`/`hSIfFalse`/`hSBlock`/`hSWhile*`/`hSForStart`: additionally carry a recursive
  sub-`ExecIH`/`SeqSegIH`/loop-scaffold seg (composition-defer).
- the 10 no-frame fields: whole arm defers (no encodable slice).

## Reproduction

- `scripts/autoprove.py --batch supplier` — this table.
- `scripts/autoprove.py --survival` — the standalone base/step certificate.
- `scripts/autoprove.py --field hStr --no-transcribe` — the recursive branch through autoprove
  (Houdini rediscovers `cstring_agreeP` + base/step-validates `storeRepr_agreeP`).
