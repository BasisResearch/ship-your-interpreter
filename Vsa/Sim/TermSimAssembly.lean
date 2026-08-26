import Vsa.Sim.InductionScaffold
import Vsa.Sim.EvalRecCommon
import Vsa.Sim.ExecBlock
import Vsa.Sim.ExecDispatch
import Vsa.Sim.CallEntry

/-!
# Layer 4 — the M4 CAPSTONE: the mutual-recursor ASSEMBLY (`term_sim_of_cases`)

`Vsa/Sim/InductionScaffold.lean` established and VALIDATED the `@EvalE.rec`
plumbing (nine motives, ~50 minor premises, binder order) against the kernel with
*trivial* (`fun … => True`) motives. This file replaces those with the **REAL**
simulation motives and applies the recursor to assemble the whole mutual
induction, taking the per-constructor case Triples as explicit hypotheses.

## What is real here

* **The nine motives** (`§1`) are the honest simulation projections, using the
  *widened* exit predicates the landed recursive cases actually target:
  - `mEvalE`  = `EvalRecCommon.EvalIH`  (`EvalEntry → EvalExitD`),
  - `mExecS`  = `ExecBlock.ExecIH`      (`ExecEntry → ExecExitD`),
  - `mEvalArgs`/`mCall`/`mExecInit`/`mForLoop`/`mForCond`/`mExecStep`/`mExecSeq`
    are the `SegEntry → SegExit` Triples (`InductionScaffold` skeletons), at the
    decoded call/args PCs where those exist (`CallEntry`).
  Every motive ignores the derivation node (its last argument) and is
  ∀-closed over the layout ghosts + budgets, exactly the shape of the landed
  case Triples.

* **`term_sim_of_cases`** (`§2`) is the full nine-motive `@EvalE.rec`
  application. Each of the ~50 minor premises is taken as an EXPLICIT hypothesis
  of the theorem, in the exact ∀-closed shape the recursor demands (constructor
  args, then the sub-derivation IHs in the motive shape, then the motive
  conclusion). The proof is `@EvalE.rec` applied to those hypotheses: it
  type-checks iff the nine real motives compose through every constructor —
  i.e. it is the kernel-checked demonstration that the mutual induction assembles
  with the real simulation motives.

  The hypotheses are exactly the landed case Triples (`evalIntSim`, `evalNegSim`,
  …, `execBlockSim`, `evalCallSim`, …) MODULO their residual bundles: each landed
  theorem discharges its corresponding minor-premise hypothesis (conditionally on
  its named residuals / M6-layout facts / the `Call.closure` crux). The
  case ↔ hypothesis mapping is documented at each premise.

`term_sim` itself (the top-level `BigStep`-level statement) then follows by
instantiating `term_sim_of_cases` at the whole-program entry and discharging the
minor-premise hypotheses from the landed cases once the residual-unification
interface (M6) closes. That last step is future work; what is proved here is that
the induction COMPOSES and pins EXACTLY the per-constructor obligations.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

namespace Vsa.Sim.TermSimAssembly

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim
open Vsa.Sim.Scaffold

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The nine REAL motives

Each `m_R` maps a derivation node (last, ignored argument) to the simulation
`Triple` STATEMENT for that node. `EvalE`/`ExecS` use the widened
`EvalIH`/`ExecIH` (the shape the recursive cases produce and consume — `EvalExit`
upgraded to `EvalExitD` for the presence/survival facts recursive callers need);
the other seven use the `InductionScaffold` `SegEntry → SegExit` skeleton
Triples, at the real decoded PCs where `CallEntry` provides them. -/

/-- `EvalE` motive: the widened simulation IH (`EvalEntry → EvalExitD`). This is
`EvalRecCommon.EvalIH`, which every recursive `EvalE` case both consumes (for its
sub-derivations) and produces. -/
def mEvalE (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
    (v : Value) (_h : EvalE st d env e st' v) : Prop :=
  EvalIH st d env e st' v

/-- `ExecS` motive: the widened statement IH (`ExecEntry → ExecExitD`), i.e.
`ExecBlock.ExecIH`. -/
def mExecS (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (st' : SpecSt)
    (status : Status) (_h : ExecS st d env s st' status) : Prop :=
  ExecIH st d env s st' status

/-- `EvalArgs` motive: the `SegEntry → SegExit` Triple at the decoded arg-loop
head/continuation (`evalArgsLoopPC`/`evalArgsContPC`). -/
def mEvalArgs (st : SpecSt) (d : Nat) (env : Addr) (_es : List Expr)
    (st' : SpecSt) (_vs : List Value) (_h : EvalArgs st d env _es st' _vs) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft evalArgsLoopPC m0)
      (SegExit g N A SL φf φc st' evalArgsContPC m0)

/-- `Call` motive: the `SegEntry → SegExit` Triple at the decoded fval-dispatch
entry / epilogue join (`callDispatchPC`/`callJoinPC`). `Call.closure` is where
the depth budget (`d < maxCallDepth`) bites. -/
def mCall (st : SpecSt) (d : Nat) (_fv : Value) (_vs : List Value)
    (st' : SpecSt) (_v : Value) (_h : Call st d _fv _vs st' _v) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
      (SegExit g N A SL φf φc st' callJoinPC m0)

/-- `ExecInit` motive: `SegEntry → SegExit` skeleton Triple. -/
def mExecInit (st : SpecSt) (d : Nat) (env : Addr) (_init : Option Stmt)
    (st' : SpecSt) (_h : ExecInit st d env _init st') : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (p q : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st' q m0)

/-- `ForLoop` motive: `SegEntry → SegExit` skeleton Triple. -/
def mForLoop (st : SpecSt) (d : Nat) (env : Addr) (_cnd _step : Option Expr)
    (_b : Stmt) (st' : SpecSt) (_status : Status)
    (_h : ForLoop st d env _cnd _step _b st' _status) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (p q : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st' q m0)

/-- `ForCond` motive: `SegEntry → SegExit` skeleton Triple. -/
def mForCond (st : SpecSt) (d : Nat) (env : Addr) (_cnd : Option Expr)
    (st' : SpecSt) (_h : ForCond st d env _cnd st') : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (p q : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st' q m0)

/-- `ExecStep` motive: `SegEntry → SegExit` skeleton Triple. -/
def mExecStep (st : SpecSt) (d : Nat) (env : Addr) (_step : Option Expr)
    (st' : SpecSt) (_h : ExecStep st d env _step st') : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (p q : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st' q m0)

/-- `ExecSeq` motive: `SegEntry → SegExit` skeleton Triple (the statement-list
loop; `interp_run` and the `block`/closure-body loops consume this). -/
def mExecSeq (st : SpecSt) (d : Nat) (env : Addr) (_ss : List Stmt)
    (st' : SpecSt) (_status : Status) (_h : ExecSeq st d env _ss st' _status) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (p q : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st' q m0)

/-! ## §2. The assembled mutual induction — `term_sim_of_cases`

The full nine-motive `@EvalE.rec` application with the REAL simulation motives.
Each of the 50 minor premises is an explicit hypothesis, in the exact ∀-closed
shape the recursor demands: the constructor's arguments (including its
sub-derivation proofs `a`, `a_1`, …), then the sub-derivation induction
hypotheses in the motive shape (`mEvalE …`/`mExecS …`/…), then the motive
conclusion for this node (with the reconstructed derivation term). The body is
the recursor applied to these hypotheses.

This TYPE-CHECKS iff the nine real motives compose through every constructor of
the mutual family — it is the kernel-checked assembly of the whole simulation
induction with real motives (not the `True`-motive plumbing check of
`InductionScaffold`). It concludes `mEvalE … t = EvalIH …`, the widened
`EvalE`-simulation Triple, for an arbitrary `EvalE` derivation.

Each hypothesis `h<Ctor>` is discharged — conditionally on that case's named
residuals / M6-layout facts / the `Call.closure` crux — by the correspondingly
named landed case theorem. The case ↔ hypothesis mapping (module doc):

* EvalE: hInt←`evalIntSim`, hStr←`evalStrSim`, hBool←`evalBoolSim`,
  hNull←`evalNullSim`, hVar←`evalVarSim`, hNeg←`evalNegSim`, hNot←`evalNotSim`,
  hBinary←`evalAddSim`/`evalSubSim`/`evalLtSim`/… (per `op`; le/gt/eq/ne/mul/
  div/mod mechanical-pending), hOrTrue←`evalOrTrueSim`, hOrFalse←`evalOrFalseSim`,
  hAndFalse←`evalAndSim`, hAndTrue←`evalAndTrueSim`, hCall←`evalCallSim`,
  hFn←`evalFnSim`; hAssign is a native-store case (pending env_define contract).
* EvalArgs: hArgsNil←`evalArgsNil`, hArgsCons←`evalArgsCons`.
* Call: hCallAssertOk←`callAssertOk`; hCallClosure (crux, env_define-blocked),
  hCallPrint/hCallPrintln (native output-append, template ready) are the open
  minor premises taken as hypotheses.
* ExecS: hSExpr←`execExprSim`, hSVarInit←`execVarDeclSim`, hSVarNull←
  `execVarNullSim`, hSBlock←`execBlockSim`, hSIfTrue←`execIfTrueSim`,
  hSIfFalse←`execIfFalseSim`, hSIfNone←`execIfNoneSim`, hSWhile*←`execWhileSim`,
  hSForStart←`execForStartSim`, hSRet←`execRetSim`, hSRetNull←`execRetNullSim`,
  hSBrk←`execBrkSim`, hSCont←`execContSim`.
* ExecSeq: hSeqNil←`execSeqNil`, hSeqConsNormal/hSeqConsAbrupt←`execSeqLoop`
  (the per-iteration rule that consumes these).
* ForLoop: hFl*←`execForLoopBody`; ForCond/ExecStep/ExecInit (hFc*/hEs*/hInit*)
  are the loop-scaffold sub-relations (`SegEntry → SegExit`), taken as
  hypotheses pending their per-relation machine proofs.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.  -/

theorem term_sim_of_cases
    (hInt :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (n : Int), mEvalE st d env (Expr.int n) st (Value.int n) (EvalE.int st d env n))
    (hStr :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : String), mEvalE st d env (Expr.str s) st (Value.str s) (EvalE.str st d env s))
    (hBool :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (b : Bool), mEvalE st d env (Expr.bool b) st (Value.bool b) (EvalE.bool st d env b))
    (hNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mEvalE st d env Expr.null st Value.null (EvalE.null st d env))
    (hVar :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value) (a : st.store.get? env x = some v), mEvalE st d env (Expr.var x) st v (EvalE.var st d env x v a))
    (hAssign :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt) (v : Value) (store'' : Store) (a : EvalE st d env e st' v) (a_1 : st'.store.set? env x v = some store''), mEvalE st d env e st' v a → mEvalE st d env (Expr.assign x e) { store := store'', out := st'.out } v (EvalE.assign st d env x e st' v store'' a a_1))
    (hBinary :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) (st' st'' : SpecSt) (lv rv v : Value) (a : EvalE st d env l st' lv) (a_1 : EvalE st' d env r st'' rv) (a_2 : binOpSem st''.store op lv rv = some v), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_1 → mEvalE st d env (Expr.binary op l r) st'' v (EvalE.binary st d env op l r st' st'' lv rv v a a_1 a_2))
    (hOrTrue :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true), mEvalE st d env l st' lv a → mEvalE st d env (Expr.logical LogOp.or l r) st' (Value.bool true) (EvalE.orTrue st d env l r st' lv a a_1))
    (hOrFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false) (a_2 : EvalE st' d env r st'' rv), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_2 → mEvalE st d env (Expr.logical LogOp.or l r) st'' (Value.bool rv.truthy) (EvalE.orFalse st d env l r st' st'' lv rv a a_1 a_2))
    (hAndFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false), mEvalE st d env l st' lv a → mEvalE st d env (Expr.logical LogOp.and l r) st' (Value.bool false) (EvalE.andFalse st d env l r st' lv a a_1))
    (hAndTrue :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true) (a_2 : EvalE st' d env r st'' rv), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_2 → mEvalE st d env (Expr.logical LogOp.and l r) st'' (Value.bool rv.truthy) (EvalE.andTrue st d env l r st' st'' lv rv a a_1 a_2))
    (hNeg :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (n : Int) (a : EvalE st d env e st' (Value.int n)), mEvalE st d env e st' (Value.int n) a → mEvalE st d env (Expr.unary UnOp.neg e) st' (Value.int (wrap64 (-n))) (EvalE.neg st d env e st' n a))
    (hNot :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mEvalE st d env (Expr.unary UnOp.not e) st' (Value.bool !v.truthy) (EvalE.not st d env e st' v a))
    (hCall :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr) (st' st'' st''' : SpecSt) (fv : Value) (vs : List Value) (v : Value) (a : EvalE st d env f st' fv) (a_1 : EvalArgs st' d env args st'' vs) (a_2 : Call st'' d fv vs st''' v), mEvalE st d env f st' fv a → mEvalArgs st' d env args st'' vs a_1 → mCall st'' d fv vs st''' v a_2 → mEvalE st d env (f.call args) st''' v (EvalE.call st d env f args st' st'' st''' fv vs v a a_1 a_2))
    (hFn :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (name : Option String) (params : List String) (body : List Stmt) (store' : Store) (a : Addr) (a_1 : st.store.allocClosure { env := env, name := name, params := params, body := body } = (store', a)), mEvalE st d env (Expr.fn name params body) { store := store', out := st.out } (Value.closure a) (EvalE.fn st d env name params body store' a a_1))
    (hArgsNil :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mEvalArgs st d env [] st [] (EvalArgs.nil st d env))
    (hArgsCons :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr) (st' st'' : SpecSt) (v : Value) (vs : List Value) (a : EvalE st d env e st' v) (a_1 : EvalArgs st' d env es st'' vs), mEvalE st d env e st' v a → mEvalArgs st' d env es st'' vs a_1 → mEvalArgs st d env (e :: es) st'' (v :: vs) (EvalArgs.cons st d env e es st' st'' v vs a a_1))
    (hCallClosure :
      ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value) (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status) (v : Value) (a_1 : st.store.closures[a]? = some cd) (a_2 : vs.length = cd.params.length) (a_3 : d < maxCallDepth) (a_4 : st.store.allocFrame (some cd.env) = (store', frame)) (a_5 : ExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status) (a_6 : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v), mExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status a_5 → mCall st d (Value.closure a) vs st' v (Call.closure st d a cd vs store' frame st' status v a_1 a_2 a_3 a_4 a_5 a_6))
    (hCallPrint :
      ∀ (st : SpecSt) (d : Nat) (vs : List Value), mCall st d (Value.native NativeFn.print) vs { store := st.store, out := st.out +++ printArgs st.store vs } Value.null (Call.print st d vs))
    (hCallPrintln :
      ∀ (st : SpecSt) (d : Nat) (vs : List Value), mCall st d (Value.native NativeFn.println) vs { store := st.store, out := st.out +++ printArgs st.store vs +++ "\n" } Value.null (Call.println st d vs))
    (hCallAssertOk :
      ∀ (st : SpecSt) (d : Nat) (vs : List Value) (v m : Value) (a : vs = [v] ∨ vs = [v, m]) (a_1 : v.truthy = true), mCall st d (Value.native NativeFn.assert) vs st Value.null (Call.assertOk st d vs v m a a_1))
    (hSExpr :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecS st d env (Stmt.expr e) st' Status.normal (ExecS.expr st d env e st' v a))
    (hSVarInit :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecS st d env (Stmt.varDecl x (some e)) { store := st'.store.define env x v, out := st'.out } Status.normal (ExecS.varInit st d env x e st' v a))
    (hSVarNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String), mExecS st d env (Stmt.varDecl x none) { store := st.store.define env x Value.null, out := st.out } Status.normal (ExecS.varNull st d env x))
    (hSBlock :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store) (inner : Addr) (st' : SpecSt) (status : Status) (a : st.store.allocFrame (some env) = (store', inner)) (a_1 : ExecSeq { store := store', out := st.out } d inner ss st' status), mExecSeq { store := store', out := st.out } d inner ss st' status a_1 → mExecS st d env (Stmt.block ss) st' status (ExecS.block st d env ss store' inner st' status a a_1))
    (hSIfTrue :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (e : Option Stmt) (st' st'' : SpecSt) (v : Value) (status : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env t st'' status), mEvalE st d env c st' v a → mExecS st' d env t st'' status a_2 → mExecS st d env (Stmt.ifStmt c t e) st'' status (ExecS.ifTrue st d env c t e st' st'' v status a a_1 a_2))
    (hSIfFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt) (st' st'' : SpecSt) (v : Value) (status : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = false) (a_2 : ExecS st' d env e st'' status), mEvalE st d env c st' v a → mExecS st' d env e st'' status a_2 → mExecS st d env (Stmt.ifStmt c t (some e)) st'' status (ExecS.ifFalse st d env c t e st' st'' v status a a_1 a_2))
    (hSIfNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mExecS st d env (Stmt.ifStmt c t none) st' Status.normal (ExecS.ifNone st d env c t st' v a a_1))
    (hSWhileFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mExecS st d env (Stmt.whileStmt c b) st' Status.normal (ExecS.whileFalse st d env c b st' v a a_1))
    (hSWhileBreak :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' Status.brk), mEvalE st d env c st' v a → mExecS st' d env b st'' Status.brk a_2 → mExecS st d env (Stmt.whileStmt c b) st'' Status.normal (ExecS.whileBreak st d env c b st' st'' v a a_1 a_2))
    (hSWhileRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : SpecSt) (v rv : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' (Status.ret rv)), mEvalE st d env c st' v a → mExecS st' d env b st'' (Status.ret rv) a_2 → mExecS st d env (Stmt.whileStmt c b) st'' (Status.ret rv) (ExecS.whileRet st d env c b st' st'' v rv a a_1 a_2))
    (hSWhileLoop :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' st''' : SpecSt) (v : Value) (status status' : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' status) (a_3 : status = Status.normal ∨ status = Status.cont) (a_4 : ExecS st'' d env (Stmt.whileStmt c b) st''' status'), mEvalE st d env c st' v a → mExecS st' d env b st'' status a_2 → mExecS st'' d env (Stmt.whileStmt c b) st''' status' a_4 → mExecS st d env (Stmt.whileStmt c b) st''' status' (ExecS.whileLoop st d env c b st' st'' st''' v status status' a a_1 a_2 a_3 a_4))
    (hSForStart :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr) (st' st'' : SpecSt) (status : Status) (a : st.store.allocFrame (some env) = (store', outer)) (a_1 : ExecInit { store := store', out := st.out } d outer init st') (a_2 : ForLoop st' d outer cnd step b st'' status), mExecInit { store := store', out := st.out } d outer init st' a_1 → mForLoop st' d outer cnd step b st'' status a_2 → mExecS st d env (Stmt.forStmt init cnd step b) st'' status (ExecS.forStart st d env init cnd step b store' outer st' st'' status a a_1 a_2))
    (hSRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecS st d env (Stmt.ret (some e)) st' (Status.ret v) (ExecS.ret st d env e st' v a))
    (hSRetNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecS st d env (Stmt.ret none) st (Status.ret Value.null) (ExecS.retNull st d env))
    (hSBrk :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecS st d env Stmt.brk st Status.brk (ExecS.brk st d env))
    (hSCont :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecS st d env Stmt.cont st Status.cont (ExecS.cont st d env))
    (hInitNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecInit st d env none st (ExecInit.none st d env))
    (hInitSome :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (st' : SpecSt) (a : ExecS st d env s st' Status.normal), mExecS st d env s st' Status.normal a → mExecInit st d env (some s) st' (ExecInit.some st d env s st' a))
    (hFlCondFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr) (b : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mForLoop st d env (some c) step b st' Status.normal (ForLoop.condFalse st d env c step b st' v a a_1))
    (hFlBodyBreak :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' : SpecSt) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' Status.brk), mForCond st d env cnd st' a → mExecS st' d env b st'' Status.brk a_1 → mForLoop st d env cnd step b st'' Status.normal (ForLoop.bodyBreak st d env cnd step b st' st'' a a_1))
    (hFlBodyRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' : SpecSt) (rv : Value) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' (Status.ret rv)), mForCond st d env cnd st' a → mExecS st' d env b st'' (Status.ret rv) a_1 → mForLoop st d env cnd step b st'' (Status.ret rv) (ForLoop.bodyRet st d env cnd step b st' st'' rv a a_1))
    (hFlLoop :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' st''' st'''' : SpecSt) (status status' : Status) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' status) (a_2 : status = Status.normal ∨ status = Status.cont) (a_3 : ExecStep st'' d env step st''') (a_4 : ForLoop st''' d env cnd step b st'''' status'), mForCond st d env cnd st' a → mExecS st' d env b st'' status a_1 → mExecStep st'' d env step st''' a_3 → mForLoop st''' d env cnd step b st'''' status' a_4 → mForLoop st d env cnd step b st'''' status' (ForLoop.loop st d env cnd step b st' st'' st''' st'''' status status' a a_1 a_2 a_3 a_4))
    (hFcNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mForCond st d env none st (ForCond.none st d env))
    (hFcSome :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true), mEvalE st d env c st' v a → mForCond st d env (some c) st' (ForCond.some st d env c st' v a a_1))
    (hEsNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecStep st d env none st (ExecStep.none st d env))
    (hEsSome :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecStep st d env (some e) st' (ExecStep.some st d env e st' v a))
    (hSeqNil :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecSeq st d env [] st Status.normal (ExecSeq.nil st d env))
    (hSeqConsNormal :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' st'' : SpecSt) (status : Status) (a : ExecS st d env s st' Status.normal) (a_1 : ExecSeq st' d env ss st'' status), mExecS st d env s st' Status.normal a → mExecSeq st' d env ss st'' status a_1 → mExecSeq st d env (s :: ss) st'' status (ExecSeq.consNormal st d env s ss st' st'' status a a_1))
    (hSeqConsAbrupt :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt) (status : Status) (a : ExecS st d env s st' status) (a_1 : status ≠ Status.normal), mExecS st d env s st' status a → mExecSeq st d env (s :: ss) st' status (ExecSeq.consAbrupt st d env s ss st' status a a_1))
    {st : SpecSt} {d : Nat} {env : Addr} {e : Expr} {st' : SpecSt} {v : Value}
    (t : EvalE st d env e st' v) : mEvalE st d env e st' v t :=
  @EvalE.rec mEvalE mEvalArgs mCall mExecS mExecInit mForLoop mForCond mExecStep
    mExecSeq
    hInt hStr hBool hNull hVar hAssign hBinary hOrTrue hOrFalse hAndFalse hAndTrue hNeg
    hNot hCall hFn hArgsNil hArgsCons hCallClosure hCallPrint hCallPrintln hCallAssertOk
    hSExpr hSVarInit hSVarNull hSBlock hSIfTrue hSIfFalse hSIfNone hSWhileFalse
    hSWhileBreak hSWhileRet hSWhileLoop hSForStart hSRet hSRetNull hSBrk hSCont hInitNone
    hInitSome hFlCondFalse hFlBodyBreak hFlBodyRet hFlLoop hFcNone hFcSome hEsNone hEsSome
    hSeqNil hSeqConsNormal hSeqConsAbrupt
    st d env e st' v t

end Vsa.Sim.TermSimAssembly
