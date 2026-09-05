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
| `hArgsNil` | `mEvalArgs` (`SegEntry@0x31d8 → SegExit@0x3254`) | `evalArgsNil` | exact loaded empty-list branch; unconditional |
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
    (f : Expr) (args : List Expr) (fval : Value) (vs : List Value) (v : Value)
    (hEf : EvalE st d env f st' fval)
    (hBound : args.length ≤ maxArgs)
    (hArgs : EvalArgs st' d env args st'' vs)
    (hCall : Call st'' d fval vs st''' v) : Prop :=
  TermSimAssembly.mEvalE st d env f st' fval hEf →
  TermSimAssembly.mEvalArgs st' d env args st'' vs hArgs →
  TermSimAssembly.mCall st'' d fval vs st''' v hCall →
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

/-- Close the exact nil row from the real taken branch. -/
theorem eval_argsNil_row :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      mEvalArgs st d env [] st [] (EvalArgs.nil st d env) := by
  intro st d env
  intro esPrefix vsPrefix hlen g N A SL φf φc dLeft aLeft m0
  exact evalArgsNilPrefix g N A SL φf φc st d env esPrefix vsPrefix hlen
    dLeft aLeft m0 (EvalArgs.nil st d env)

/-! ### `hArgsCons` -/

/-- The exact cons-args residual.  Its conclusion is the generalized prefix
motive, so the tail IH resumes at the actual loop cursor. -/
def ArgsConsResid (st : SpecSt) (d : Nat) (env : Addr)
    (e : Expr) (es : List Expr) (st' st'' : SpecSt)
    (v : Value) (vs : List Value)
    (hE : EvalE st d env e st' v)
    (hArgs : EvalArgs st' d env es st'' vs) : Prop :=
  mEvalE st d env e st' v hE →
  mEvalArgs st' d env es st'' vs hArgs →
  mEvalArgs st d env (e :: es) st'' (v :: vs)
    (EvalArgs.cons st d env e es st' st'' v vs hE hArgs)

/-- Route the exact cons residual to the indexed `mEvalArgs` motive. -/
theorem eval_argsCons_row
    (hR : ∀ st d env e es st' st'' v vs hE hArgs,
      ArgsConsResid st d env e es st' st'' v vs hE hArgs) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' st'' : SpecSt) (v : Value) (vs : List Value)
      (a : EvalE st d env e st' v) (a_1 : EvalArgs st' d env es st'' vs),
      mEvalE st d env e st' v a →
      mEvalArgs st' d env es st'' vs a_1 →
      mEvalArgs st d env (e :: es) st'' (v :: vs) (EvalArgs.cons st d env e es st' st'' v vs a a_1) := by
  intro st d env e es st' st'' v vs hE hArgs ihE ihArgs
  exact hR st d env e es st' st'' v vs hE hArgs ihE ihArgs

/-! ### `hCallPrint` / `hCallPrintln` / `hCallAssertOk` (native `mCall` rows) -/

/-- The print residual at the indexed native-call ABI. -/
def CallPrintResid (st : SpecSt) (d : Nat) (vs : List Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem),
    Triple
      (CallEntryI g N A SL φf φc st d (.native .print) vs
        dLeft aLeft sp sret m0)
      (CallExitI g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨st.store, st.out +++ printArgs st.store vs⟩ .null sret m0)

/-- Route `hCallPrint` → `callPrint`. -/
theorem eval_callPrint_row (hR : ∀ st d vs, CallPrintResid st d vs) :
    ∀ (st : SpecSt) (d : Nat) (vs : List Value),
      mCall st d (Value.native NativeFn.print) vs
        { store := st.store, out := st.out +++ printArgs st.store vs } Value.null
        (Call.print st d vs) := by
  intro st d vs
  intro g N A SL φf φc dLeft aLeft sp sret m0 _hImg
  exact hR st d vs g N A SL φf φc dLeft aLeft sp sret m0

/-- The println residual at the indexed native-call ABI. -/
def CallPrintlnResid (st : SpecSt) (d : Nat) (vs : List Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem),
    Triple
      (CallEntryI g N A SL φf φc st d (.native .println) vs
        dLeft aLeft sp sret m0)
      (CallExitI g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨st.store, st.out +++ printArgs st.store vs +++ "\n"⟩ .null sret m0)

/-- Route `hCallPrintln` → `callPrintln`. -/
theorem eval_callPrintln_row (hR : ∀ st d vs, CallPrintlnResid st d vs) :
    ∀ (st : SpecSt) (d : Nat) (vs : List Value),
      mCall st d (Value.native NativeFn.println) vs
        { store := st.store, out := st.out +++ printArgs st.store vs +++ "\n" } Value.null
        (Call.println st d vs) := by
  intro st d vs
  intro g N A SL φf φc dLeft aLeft sp sret m0 _hImg
  exact hR st d vs g N A SL φf φc dLeft aLeft sp sret m0

/-- The assert-ok residual at the indexed native-call ABI.  The constructor's
arity and truthiness proofs select this path. -/
def CallAssertOkResid (st : SpecSt) (d : Nat) (vs : List Value)
    (v m : Value) (hvs : vs = [v] ∨ vs = [v, m]) (htruthy : v.truthy = true) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem),
    Triple
      (CallEntryI g N A SL φf φc st d (.native .assert) vs
        dLeft aLeft sp sret m0)
      (CallExitI g N A SL φf φc st.store.frames.size st.store.closures.size
        st .null sret m0)

/-- Route `hCallAssertOk` → `callAssertOk`. -/
theorem eval_callAssertOk_row
    (hR : ∀ st d vs v m hvs htruthy,
      CallAssertOkResid st d vs v m hvs htruthy) :
    ∀ (st : SpecSt) (d : Nat) (vs : List Value) (v m : Value)
      (a : vs = [v] ∨ vs = [v, m]) (a_1 : v.truthy = true),
      mCall st d (Value.native NativeFn.assert) vs st Value.null
        (Call.assertOk st d vs v m a a_1) := by
  intro st d vs v m hvs htruthy
  intro g N A SL φf φc dLeft aLeft sp sret m0 _hImg
  exact hR st d vs v m hvs htruthy g N A SL φf φc dLeft aLeft sp sret m0

/-! ### `hCallClosure` -/

/-- The closure-call residual, indexed by the exact semantic constructor and
its body-sequence induction hypothesis.  Unlike the former bare `mCall` shape,
the entry names the staged closure and argument vector and the exit names the
returned value. -/
def CallClosureResid
    (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
    (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status) (v : Value)
    (_hClosure : st.store.closures[a]? = some cd)
    (_hArity : vs.length = cd.params.length)
    (_hDepth : d < maxCallDepth)
    (_hAlloc : st.store.allocFrame (some cd.env) = (store', frame))
    (hBody : ExecSeq
      { store := List.foldl (fun s x => match x with
          | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out }
      (d + 1) frame cd.body st' status)
    (_hResult : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v) : Prop :=
  mExecSeq
      { store := List.foldl (fun s x => match x with
          | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out }
      (d + 1) frame cd.body st' status hBody →
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem),
    EntryImage callDispatchPC g m0 →
    Triple
      (CallEntryI g N A SL φf φc st d (.closure a) vs
        dLeft aLeft sp sret m0)
      (CallExitI g N A SL φf φc st.store.frames.size st.store.closures.size
        st' v sret m0)

/-- Route the exact closure constructor to the indexed call motive. -/
theorem eval_callClosure_indexed_row
    (hR : ∀ st d a cd vs store' frame st' status v
      hClosure hArity hDepth hAlloc hBody hResult,
      CallClosureResid st d a cd vs store' frame st' status v
        hClosure hArity hDepth hAlloc hBody hResult) :
    ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData)
      (vs : List Value) (store' : Store) (frame : Addr) (st' : SpecSt)
      (status : Status) (v : Value)
      (hClosure : st.store.closures[a]? = some cd)
      (hArity : vs.length = cd.params.length)
      (hDepth : d < maxCallDepth)
      (hAlloc : st.store.allocFrame (some cd.env) = (store', frame))
      (hBody : ExecSeq
        { store := List.foldl (fun s x => match x with
            | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out }
        (d + 1) frame cd.body st' status)
      (hResult : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v),
      mExecSeq
          { store := List.foldl (fun s x => match x with
              | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out }
          (d + 1) frame cd.body st' status hBody →
      mCall st d (.closure a) vs st' v
        (Call.closure st d a cd vs store' frame st' status v
          hClosure hArity hDepth hAlloc hBody hResult) := by
  intro st d a cd vs store' frame st' status v hClosure hArity hDepth hAlloc
    hBody hResult hBodyIH
  exact hR st d a cd vs store' frame st' status v hClosure hArity hDepth hAlloc
    hBody hResult hBodyIH

/-! ### `hCall` (composite `EvalIH` row) -/

/-- Route `hCall` → `evalCallSimD`.  The residual is indexed by all three
semantic derivations and consumes all three recursive motives. -/
theorem eval_call_row
    (hR : ∀ st st' st'' st''' d env f args fval vs v hEf hBound hArgs hCall,
      CallResid st st' st'' st''' d env f args fval vs v hEf hBound hArgs hCall) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' st''' : SpecSt) (fv : Value) (vs : List Value) (v : Value)
      (a : EvalE st d env f st' fv) (hargs : args.length ≤ maxArgs)
      (a_1 : EvalArgs st' d env args st'' vs) (a_2 : Call st'' d fv vs st''' v),
      mEvalE st d env f st' fv a →
      mEvalArgs st' d env args st'' vs a_1 →
      mCall st'' d fv vs st''' v a_2 →
      mEvalE st d env (f.call args) st''' v
        (EvalE.call st d env f args st' st'' st''' fv vs v a hargs a_1 a_2) := by
  intro st d env f args st' st'' st''' fv vs v hEf hargs hEargs hCall ihf iharg ihcall
  show Vsa.Sim.EvalIH st d env (f.call args) st''' v
  intro g N A SL φf φc sp r sret aEnv aExpr m0
  obtain ⟨hArm, hW⟩ := hR st st' st'' st''' d env f args fv vs v
    hEf hargs hEargs hCall ihf iharg ihcall
    g N A SL φf φc sp r sret aEnv aExpr m0
  exact Vsa.Sim.evalCallSimD g N A SL φf φc st st' st'' st''' d env f args fv vs v
    sp r sret aEnv aExpr m0 ihf hEargs hCall
    (EvalE.call st d env f args st' st'' st''' fv vs v hEf hargs hEargs hCall) hArm hW

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
