import Vsa.Sim.ExecExprRet
import Vsa.Sim.ExecRet
import Vsa.Sim.rows.ExecCaseGeom
import Vsa.Sim.TermSimClose
import Vsa.Sim.rows.EvalChildArmExpr
import Vsa.Sim.rows.EvalChildArmRet

/-!
# Layer 4 — M4 RECURSIVE `ExecS` cases re-landed at `ExecExitD` (`hSExpr`/`hSRet`)

The recursive statement-side twin of `rows/ExecCaseGeom.lean` (which handles the
register-only leaves `brk`/`cont`).  The recursive statement cases
(`ExecS.expr`, `ExecS.ret`) run a sub-`eval_expr` derivation, so their exit store
is `st'.store` (the sub-eval mutated memory) at a NON-identity `φ`, and — for
`ret` — the arm writes the caller retslot `[aRet, aRet+24)`.  The identity-φ
`ExecLeafWiden` therefore does not apply; this file supplies the recursive-shaped
widener(s) and routes `hSExpr`/`hSRet` onto `execExprSim`/`execRetSim`.

## The two gaps between the landed sim and the `mExecS` motive

`execExprSim` (`ExecExprRet.lean`) proves
`Triple (ExecEntry (.expr e) ∧ sailOutput = out0) (ExecExit … st' .normal …)`
and `execRetSim` (`ExecRet.lean`) proves
`Triple (ExecEntry (.ret (some e)) ∧ sailOutput = out0) (ExecExit … st' (.ret v) …)`,
each conditional on the jump-table geometry + the recursion glue `hGlue`.  The
recursor's minor premise `hSExpr`/`hSRet` is (via `TermSimAssembly.mExecS =
ExecBlock.ExecIH` by definitional unfolding, and `mEvalE = EvalRecCommon.EvalIH`)

    ∀ ghosts, Triple (ExecEntry …) (ExecExitD … st.store.frames.size
                                              st.store.closures.size st' status …)

so the gaps are exactly as for the leaves, but recursive:

1. **entry `out0`** — drop `∧ sailOutput = out0` by `out0 := c.σ.sailOutput`
   (`rfl`).  Pure marshalling — identical to `execBrkSimD`/`execContSimD`.
2. **exit `ExecExit → ExecExitD`** — add `MemExtends m0 c.σ.mem` and the
   `[SL.lo,SL.hi)`-store-survival clause AT A NON-IDENTITY `φ` (the sub-eval
   allocated/extended the store maps).  Unlike `ExecLeafWiden` (identity φ,
   unchanged store), the recursive widener `ExecRecWiden` carries its own
   `∃ φf' φc', PhiExtends …` witnesses in the survival clause.  This is the
   statement-frame analog of `EvalExitD`'s survival clause / `SubExecReturn`'s
   survival clause (both carry `∃ φf' φc'`), re-supplied as the honest
   exit-quantified widener the recursive-case minor premise provides.

`ExecRecWiden` is TRUE of every recursive statement exit: `execExprSim`/
`execRetSim` internally re-represent `st'.store` at extended maps with a
survival clause (via `SubExecReturn`/`SubExecReturnR` and `execBlockD`), so the
widener is the honest re-supply of what the packaged `ExecExit` forgets.  The
`ret`-arm retslot write `[aRet, aRet+24)` is disjoint from the arena where
`st'.store` lives, so it is transparent to the survival clause (which quantifies
over ALL `m'` agreeing outside `[SL.lo, SL.hi)`); NO retslot-specific carve is
needed in the widener — the retslot-awareness lives entirely inside the survival
witness the residual supplies.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `ExecRecWiden` — the recursive `ExecExitD` upgrade clauses, exit-quantified

The two `ExecExitD` clauses `ExecExit` forgets, as a widener over the exit config,
at a NON-identity `φ` (the sub-eval extended the store maps).  For any config `c`
satisfying the sim's `ExecExit` (the widener is applied ONLY to the sim's own
exit), it yields `MemExtends m0 c.σ.mem` and the `[SL.lo,SL.hi)`-survival of
`st'.store` at some extended pair `φf'/φc'`.  This is the recursive analog of
`ExecLeafWiden` (the identity-φ leaf widener): the survival clause here binds its
own `∃ φf' φc'`, matching the `ExecExitD.store`/`SubEvalReturn` shape.

**Re-landed (T1.2)** as a THIN ALIAS of the parametric `Widen` (`WidenMeta.lean`)
at the `ExecExit` family and the canonical `stackFoot SL` footprint; the bridge is
`execExitD_of_widen`. -/

/-! ## `ExecExprGeom` — the `hSExpr` recursor-supplied residual bundle

Everything `execExprSim` needs BEYOND the sub-`EvalIH` (which the recursor hands
the case for free, `rfl`-passed): the `execBlockA` jump-table slot pin + its
stack-disjointness, the recursion glue `hGlue`, and the recursive widener.  This
is the `ExecCaseGeom` twin for the recursive `expr` case: one bundle threaded
once, ∀-closed over the ghosts in the row. -/

/-! ## `ExecRetGeom` — the `hSRet` recursor-supplied residual bundle

The `ExecExprGeom` twin for the recursive, retslot-writing `ret` case.  Carries
`execRetSim`'s FULL residual list — the jump-table slot pin + disjointness, the
retslot geometry (`aRet` an 8-aligned 24-byte RAM slot above HTIF, disjoint from
stack/arena/code — the `sd` store-region checks), the recursion glue `hGlue`
(producing `SubExecReturnR`, i.e. `SubExecReturn` + the 24-byte buffer
readability), and the recursive widener at status `.ret v`.  The retslot write
`[aRet, aRet+24)` is transparent to `ExecRecWiden`'s survival clause (the store
lives in the arena, disjoint from the retslot); the retslot-awareness is entirely
in the residual `hGlue`/widener the recursor supplies. -/

/-! ## `hSRetNull` — the null return, a leaf on the helper-call layer

`ret;` has no child: the arm takes the `beqz` into the `value_null` bridge,
rejoins the retslot copy, and runs the status-3 epilogue.  Its residual is
the whole leaf simulation at the widened exit; `rows/Field_hSRetNullClosed`
supplies it from `HelperCall` (the bridge), `retSlotResume` (the copy and
epilogue) and `armState_of_entry_kind` (the prologue). -/

/-! ## `hSVarNull` — the null declaration on the helper-call layer

`var x;` takes the `beqz` into the `value_null` bridge and rejoins the
declaration tail (`ld a1,8(s0)`, the copy, `jal env_define`, the normal exit).
Its residual is the whole leaf simulation at the widened exit;
`rows/Field_hSVarNullClosed` supplies it from `HelperCall` and the named
`env_define` contract. -/

end Vsa.Sim

/-! ## The `mExecS`-motive case rows (the recursor-premise adapters)

`exec_expr_row`/`exec_ret_row` marshal the `*D` lemma into the exact minor-premise
slot of `execSeq_sim_of_cases` (`TermSimClose.lean`).  As for the brk/cont rows
(`rows/ExecRouting.lean`), the premise is `ExecIH …` by definitional unfolding
(`TermSimAssembly.mExecS = ExecBlock.ExecIH`), and — for these recursive cases —
the sub-derivation IH the recursor hands the case (`mEvalE st d env e st' v a`) is
`EvalRecCommon.EvalIH st d env e st' v` by the SAME unfolding
(`TermSimAssembly.mEvalE = EvalRecCommon.EvalIH`), so it passes straight through
to the `*D` lemma's `hIH` by `rfl` — no adapter.  The per-case `ExecExprGeom`/
`ExecRetGeom` bundle (∀-closed over the ghosts) carries the geometry + glue +
widener. -/
namespace Vsa.Sim.Rows

open Vsa.Sim

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.Rows
