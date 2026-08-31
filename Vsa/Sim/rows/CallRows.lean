import Vsa.Sim.EvalCall
import Vsa.Sim.EvalFn
import Vsa.Sim.EvalCallPrint
import Vsa.Sim.EvalCallNative
import Vsa.Sim.rows.LoopSteps
import Vsa.Sim.TermCaseBundle
import Vsa.Sim.WidenMeta

/-!
# `CallRows` — the call-subsystem case rows (step-6c, HAND-WRITTEN)

Adapters filling the `@EvalE.rec` (`term_sim_of_cases`/`execSeq_sim_of_cases`)
call-subsystem minor premises with their landed simulation lemmas:

| premise | motive shape | landed sim | gap this file bridges |
|---|---|---|---|
| `hArgsNil` | `mEvalArgs` (`SegEntry@loop → SegExit@cont`) | `evalArgsNil` | ENTRY-PC hop `loop→cont` (empty-list `blez`), surfaced as `ArgsNilPrefix` |
| `hArgsCons` | `mEvalArgs` | `evalArgsCons` | the `hstep`/`hnil` loop residuals (tail sub-motive is unused — the sim recurses over the FULL list) |
| `hCallPrint` | `mCall` (`SegEntry@dispatch → SegExit@join`) | `callPrint` | `NativePrintSpec` residual, ∀-closed over ghosts |
| `hCallPrintln` | `mCall` | `callPrintln` | `NativePrintlnSpec` residual |
| `hCallAssertOk` | `mCall` | `callAssertOk` | `NativeAssertOkSpec` residual |
| `hCall` | `mEvalE` (`EvalEntry → EvalExitD`) | `evalCallSim` | `EvalExit → EvalExitD` rec-widener + `CallArmSpec` (consumes the 3 sub-derivations) |
| `hFn` | `mEvalE` | `evalFnSim` | rec-widener (non-identity φc) + `FnArmSpec` |

Each row's genuine gap is a NAMED typed residual field (never `sorry`).
`hCallClosure` is OUT OF SCOPE (depth-crux, env_define-gated).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.Scaffold

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## `EvalRecWiden` — the recursive `EvalExit → EvalExitD` widener

The `ExecRecWiden` twin for the `EvalE` side.  `evalCallSim`/`evalFnSim` conclude
at `EvalExit` (the packaged exit config existential); the `mEvalE` motive
(`EvalIH`) demands `EvalExitD`, i.e. `EvalExit` PLUS `MemExtends m0 (exit mem)`
PLUS the `[SL.lo,SL.hi)`-survival of the exit store at some EXTENDED φ-pair.
Unlike `LeafWiden` (identity φ, `PhiExtends.refl`), the recursive/allocating exit
carries its own `∃ φf' φc'` (the call frame / closure array grew), matching
`EvalExitD`'s existential shape.

**Re-landed (T1.2)** as a THIN ALIAS of the parametric `Widen` (`WidenMeta.lean`)
at the `EvalExit` family and the canonical `stackFoot SL` footprint; the bridge is
`evalExitD_of_widen`. -/
abbrev EvalRecWiden
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : Vsa.While.St) (v : Value) (sp r sret : BitVec 64) (m0 : Mem) : Prop :=
  Widen (EvalExit g N A SL φf φc nf nc st' v sp r sret m0)
    N A φf φc nf nc st' m0 (stackFoot SL)

/-- **The recursive eval widening.** `EvalExit … c ∧ EvalRecWiden …` gives
`EvalExitD … c` — the `mEvalE` motive shape.  A THIN COROLLARY of the parametric
family bridge `evalExitD_of_widen` (`WidenMeta.lean`). -/
theorem evalExitD_of_evalExit_rec
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {nf nc : Nat}
    {st' : Vsa.While.St} {v : Value} {sp r sret : BitVec 64} {m0 : Mem} {c : Config}
    (hExit : EvalExit g N A SL φf φc nf nc st' v sp r sret m0 c)
    (hW : EvalRecWiden g N A SL φf φc nf nc st' v sp r sret m0) :
    EvalExitD g N A SL φf φc nf nc st' v sp r sret m0 c :=
  evalExitD_of_widen hExit hW

/-! ## `hCall` — the composite `EX_CALL` arm re-landed at `EvalExitD`

`evalCallSim` consumes the callee `EvalIH` + the `EvalArgs`/`Call` SPEC
derivations (the recursor hands `a`/`a_1`/`a_2` directly) + the composite
`CallArmSpec` residual.  The mid sub-motives (`mEvalArgs`/`mCall`) are NOT
consumed by `evalCallSim` — they are consumed INSIDE `CallArmSpec`'s eventual
discharge (via `evalArgsLoop` / the native/closure dispatch).  So the row
threads them into the residual bundle unchanged. -/

/-- The `hCall` residual bundle: the composite `CallArmSpec` arm run + the
recursive `EvalExit → EvalExitD` widener, ∀-closed over the ghosts. -/
def CallResid (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr)
    (f : Expr) (args : List Expr) (fval : Value) (vs : List Value) (v : Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    Vsa.Sim.CallArmSpec g N A SL φf φc st st' st'' st''' d env f args fval vs v
      sp r sret aEnv aExpr m0 ∧
    Vsa.Sim.EvalRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size
      st''' v sp r sret m0

/-- **`evalCallSimD`** — `EvalE.call` re-landed at `EvalExitD` (the `EvalIH`
shape).  Composes `evalCallSim`'s `EvalExit` with the recursive widener. -/
theorem evalCallSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr)
    (f : Expr) (args : List Expr) (fval : Value) (vs : List Value) (v : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hIH_f : EvalIH st d env f st' fval)
    (hArgs : EvalArgs st' d env args st'' vs)
    (hCall : Call st'' d fval vs st''' v)
    (hEval : EvalE st d env (.call f args) st''' v)
    (hArm : Vsa.Sim.CallArmSpec g N A SL φf φc st st' st'' st''' d env f args fval vs v
      sp r sret aEnv aExpr m0)
    (hW : Vsa.Sim.EvalRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size
      st''' v sp r sret m0) :
    Triple
      (EvalEntry g N A SL φf φc st d env (.call f args) sp r sret aEnv aExpr m0)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st''' v sp r sret m0) := by
  intro c hEntry
  obtain ⟨c', hs, hExit⟩ :=
    evalCallSim g N A SL φf φc st st' st'' st''' d env f args fval vs v
      sp r sret aEnv aExpr m0 hIH_f hArgs hCall hEval hArm c hEntry
  exact ⟨c', hs, evalExitD_of_evalExit_rec hExit hW⟩

/-! ## `hFn` — the `EX_FN` closure-alloc arm re-landed at `EvalExitD` -/

/-- The `hFn` residual bundle: the `FnArmSpec` arm run + the recursive widener,
∀-closed over the ghosts.  φc is genuinely non-identity here (the closures array
grows by one), so `EvalRecWiden` (not `LeafWiden`) is required. -/
def FnResid (st : SpecSt) (d : Nat) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (store' : Store) (a : Addr) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    Vsa.Sim.FnArmSpec g N A SL φf φc st d env name params body store' a
      sp r sret aEnv aExpr m0 ∧
    Vsa.Sim.EvalRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size
      ⟨store', st.out⟩ (.closure a) sp r sret m0

/-- **`evalFnSimD`** — `EvalE.fn` re-landed at `EvalExitD`. -/
theorem evalFnSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (store' : Store) (a : Addr)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hAlloc : st.store.allocClosure ⟨env, name, params, body⟩ = (store', a))
    (hEval : EvalE st d env (.fn name params body) ⟨store', st.out⟩ (.closure a))
    (hArm : Vsa.Sim.FnArmSpec g N A SL φf φc st d env name params body store' a
      sp r sret aEnv aExpr m0)
    (hW : Vsa.Sim.EvalRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size
      ⟨store', st.out⟩ (.closure a) sp r sret m0) :
    Triple
      (EvalEntry g N A SL φf φc st d env (.fn name params body) sp r sret aEnv aExpr m0)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨store', st.out⟩ (.closure a) sp r sret m0) := by
  intro c hEntry
  obtain ⟨c', hs, hExit⟩ :=
    evalFnSim g N A SL φf φc st d env name params body store' a
      sp r sret aEnv aExpr m0 hAlloc hEval hArm c hEntry
  exact ⟨c', hs, evalExitD_of_evalExit_rec hExit hW⟩

end Vsa.Sim

/-! ## The `mCall`/`mEvalArgs`/`mEvalE` case rows -/

namespace Vsa.Sim.Rows

open Vsa.Sim
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

/-! ### `hArgsNil` -/

/-- The nil-args residual: the empty-list ENTRY-PC hop (`evalArgsLoopPC →
evalArgsContPC`, the `blez a5` empty-list fall-through) as a prefix `Triple`,
∀-closed over the ghosts.  `evalArgsNil` itself is the zero-step identity at
`evalArgsContPC`; the only gap to the `mEvalArgs` motive (entry at
`evalArgsLoopPC`) is this fall-through hop. -/
def ArgsNilResid (st : SpecSt) (d : Nat) (_env : Addr) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft evalArgsLoopPC m0)
      (SegEntry g N A SL φf φc st d dLeft aLeft evalArgsContPC m0)

/-- Route `hArgsNil` → `evalArgsNil`, prepending the empty-list `loop→cont` hop. -/
theorem eval_argsNil_row (hR : ∀ st d env, ArgsNilResid st d env) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      mEvalArgs st d env [] st [] (EvalArgs.nil st d env) := by
  intro st d env
  show ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft evalArgsLoopPC m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st evalArgsContPC m0)
  intro g N A SL φf φc dLeft aLeft m0
  intro c hc
  obtain ⟨c₁, hs₁, hcont⟩ := hR st d env g N A SL φf φc dLeft aLeft m0 c hc
  obtain ⟨c₂, hs₂, hexit⟩ :=
    Vsa.Sim.evalArgsNil g N A SL φf φc st d env dLeft aLeft m0
      (EvalArgs.nil st d env) c₁ hcont
  exact ⟨c₂, hs₁.trans hs₂, hexit⟩

/-! ### `hArgsCons` -/

/-- The cons-args residual: the per-iteration body oracle (`hstep`, an
`EvalArgsStep`) + the fall-through (`hnil`), the two residuals `evalArgsCons`
takes, ∀-closed over the ghosts.  The tail sub-motive `mEvalArgs` is NOT used —
`evalArgsCons` recurses over the FULL list internally via `evalArgsLoop`. -/
def ArgsConsResid (_st : SpecSt) (d : Nat) (env : Addr) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (dLeft aLeft : Nat) (_m0 : Mem),
    (∀ (φf φc : Addr → Nat) (st0 : SpecSt) (e : Expr) (es : List Expr)
        (st' stFin : SpecSt) (v : Value) (mm : Mem),
        EvalArgsStep g N A SL φf φc st0 d env e es dLeft aLeft evalArgsLoopPC mm st' stFin v) ∧
    (∀ (φf φc : Addr → Nat) (st0 : SpecSt) (mm : Mem),
        Triple
          (SegEntry g N A SL φf φc st0 d dLeft aLeft evalArgsLoopPC mm)
          (SegExit g N A SL φf φc st0.store.frames.size st0.store.closures.size st0
            evalArgsContPC mm))

/-- Route `hArgsCons` → `evalArgsCons`.  The head `EvalIH` (`mEvalE … a`) and the
tail `mEvalArgs` (`… a_1`) the recursor hands are consumed only via the `hstep`
body oracle inside `evalArgsCons` (it recurses over the whole list), so they pass
through unused here. -/
theorem eval_argsCons_row (hR : ∀ st d env, ArgsConsResid st d env) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' st'' : SpecSt) (v : Value) (vs : List Value)
      (a : EvalE st d env e st' v) (a_1 : EvalArgs st' d env es st'' vs),
      mEvalE st d env e st' v a →
      mEvalArgs st' d env es st'' vs a_1 →
      mEvalArgs st d env (e :: es) st'' (v :: vs) (EvalArgs.cons st d env e es st' st'' v vs a a_1) := by
  intro st d env e es st' st'' v vs hE hArgs _ihE _ihArgs
  show ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft evalArgsLoopPC m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st'' evalArgsContPC m0)
  intro g N A SL φf φc dLeft aLeft m0
  obtain ⟨hstep, hnil⟩ := hR st d env g N A SL dLeft aLeft m0
  exact Vsa.Sim.evalArgsCons g N A SL d env dLeft aLeft evalArgsLoopPC evalArgsContPC
    (fun φf φc st0 e es st' stFin v mm => hstep φf φc st0 e es st' stFin v mm)
    (fun φf φc st0 mm => hnil φf φc st0 mm)
    φf φc st st'' e es v vs m0 (EvalArgs.cons st d env e es st' st'' v vs hE hArgs)

/-! ### `hCallPrint` / `hCallPrintln` / `hCallAssertOk` (native `mCall` rows) -/

/-- The print residual: `NativePrintSpec`, ∀-closed over the ghosts. -/
def CallPrintResid (st : SpecSt) (d : Nat) (vs : List Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Vsa.Sim.NativePrintSpec g N A SL φf φc st d dLeft aLeft m0 vs

/-- Route `hCallPrint` → `callPrint`. -/
theorem eval_callPrint_row (hR : ∀ st d vs, CallPrintResid st d vs) :
    ∀ (st : SpecSt) (d : Nat) (vs : List Value),
      mCall st d (Value.native NativeFn.print) vs
        { store := st.store, out := st.out +++ printArgs st.store vs } Value.null
        (Call.print st d vs) := by
  intro st d vs
  show ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨st.store, st.out +++ printArgs st.store vs⟩ callJoinPC m0)
  intro g N A SL φf φc dLeft aLeft m0
  exact Vsa.Sim.callPrint g N A SL φf φc st d dLeft aLeft m0 vs
    (Call.print st d vs) (hR st d vs g N A SL φf φc dLeft aLeft m0)

/-- The println residual: `NativePrintlnSpec`, ∀-closed over the ghosts. -/
def CallPrintlnResid (st : SpecSt) (d : Nat) (vs : List Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Vsa.Sim.NativePrintlnSpec g N A SL φf φc st d dLeft aLeft m0 vs

/-- Route `hCallPrintln` → `callPrintln`. -/
theorem eval_callPrintln_row (hR : ∀ st d vs, CallPrintlnResid st d vs) :
    ∀ (st : SpecSt) (d : Nat) (vs : List Value),
      mCall st d (Value.native NativeFn.println) vs
        { store := st.store, out := st.out +++ printArgs st.store vs +++ "\n" } Value.null
        (Call.println st d vs) := by
  intro st d vs
  show ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨st.store, st.out +++ printArgs st.store vs +++ "\n"⟩ callJoinPC m0)
  intro g N A SL φf φc dLeft aLeft m0
  exact Vsa.Sim.callPrintln g N A SL φf φc st d dLeft aLeft m0 vs
    (Call.println st d vs) (hR st d vs g N A SL φf φc dLeft aLeft m0)

/-- The assert-ok residual: `NativeAssertOkSpec`, ∀-closed over the ghosts.
The truthy/arity guards `vs = [v] ∨ vs = [v,mv]` and `v.truthy = true` are
supplied per-invocation (they come from the `Call.assertOk` constructor args). -/
def CallAssertOkResid (st : SpecSt) (d : Nat) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Vsa.Sim.NativeAssertOkSpec g N A SL φf φc st d dLeft aLeft m0

/-- Route `hCallAssertOk` → `callAssertOk`. -/
theorem eval_callAssertOk_row (hR : ∀ st d, CallAssertOkResid st d) :
    ∀ (st : SpecSt) (d : Nat) (vs : List Value) (v m : Value)
      (a : vs = [v] ∨ vs = [v, m]) (a_1 : v.truthy = true),
      mCall st d (Value.native NativeFn.assert) vs st Value.null
        (Call.assertOk st d vs v m a a_1) := by
  intro st d vs v m hvs htruthy
  show ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st callJoinPC m0)
  intro g N A SL φf φc dLeft aLeft m0
  exact Vsa.Sim.callAssertOk g N A SL φf φc st d dLeft aLeft m0 vs v m
    hvs htruthy (Call.assertOk st d vs v m hvs htruthy)
    (hR st d g N A SL φf φc dLeft aLeft m0)

/-! ### `hCall` (composite `EvalIH` row) -/

/-- Route `hCall` → `evalCallSimD`.  The callee `EvalIH` (`mEvalE … a`) passes to
`hIH_f` by `rfl`; the `EvalArgs`/`Call` SPEC derivations (`a_1`/`a_2`) thread
directly; the mid sub-motives (`mEvalArgs … ih1`/`mCall … ih2`) are consumed
inside `CallArmSpec`, so they pass through unused. -/
theorem eval_call_row
    (hR : ∀ st st' st'' st''' d env f args fval vs v,
      CallResid st st' st'' st''' d env f args fval vs v) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' st''' : SpecSt) (fv : Value) (vs : List Value) (v : Value)
      (a : EvalE st d env f st' fv) (a_1 : EvalArgs st' d env args st'' vs)
      (a_2 : Call st'' d fv vs st''' v),
      mEvalE st d env f st' fv a →
      mEvalArgs st' d env args st'' vs a_1 →
      mCall st'' d fv vs st''' v a_2 →
      mEvalE st d env (f.call args) st''' v
        (EvalE.call st d env f args st' st'' st''' fv vs v a a_1 a_2) := by
  intro st d env f args st' st'' st''' fv vs v hEf hEargs hCall ihf _iharg _ihcall
  show Vsa.Sim.EvalIH st d env (f.call args) st''' v
  intro g N A SL φf φc sp r sret aEnv aExpr m0
  obtain ⟨hArm, hW⟩ := hR st st' st'' st''' d env f args fv vs v
    g N A SL φf φc sp r sret aEnv aExpr m0
  exact Vsa.Sim.evalCallSimD g N A SL φf φc st st' st'' st''' d env f args fv vs v
    sp r sret aEnv aExpr m0 ihf hEargs hCall
    (EvalE.call st d env f args st' st'' st''' fv vs v hEf hEargs hCall) hArm hW

/-! ### `hFn` (closure-alloc `EvalIH` row) -/

/-- Route `hFn` → `evalFnSimD`. -/
theorem eval_fn_row
    (hR : ∀ st d env name params body store' a,
      FnResid st d env name params body store' a) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (name : Option String)
      (params : List String) (body : List Stmt) (store' : Store) (a : Addr)
      (a_1 : st.store.allocClosure { env := env, name := name, params := params, body := body } = (store', a)),
      mEvalE st d env (Expr.fn name params body) { store := store', out := st.out }
        (Value.closure a) (EvalE.fn st d env name params body store' a a_1) := by
  intro st d env name params body store' a hAlloc
  show Vsa.Sim.EvalIH st d env (.fn name params body) ⟨store', st.out⟩ (.closure a)
  intro g N A SL φf φc sp r sret aEnv aExpr m0
  obtain ⟨hArm, hW⟩ := hR st d env name params body store' a
    g N A SL φf φc sp r sret aEnv aExpr m0
  exact Vsa.Sim.evalFnSimD g N A SL φf φc st d env name params body store' a
    sp r sret aEnv aExpr m0 hAlloc
    (EvalE.fn st d env name params body store' a hAlloc) hArm hW

end Vsa.Sim.Rows
