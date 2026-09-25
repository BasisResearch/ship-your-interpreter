import Vsa.While.Cost
import Vsa.While.Programs

/-!
# A fuel-bounded evaluator for the cost relations

`Vsa/While/Cost.lean` defines nine mutually inductive cost relations
(`EvalECost`, …, `ExecSeqCost`). This file gives a fuel-bounded,
kernel-reducible evaluator mirroring them rule for rule, so that facts about
the cost of a concrete program (e.g. the capacity premise
`∀ st' n, ExecSeqCost initSt 0 0 p st' .normal n → 2 * n + 8256 ≤ K`) are
discharged by kernel computation.

* `Res α` is the three-valued result: `done a`, `stuck` (no rule applies:
  division by zero, an unbound variable, calling a non-function, an arity
  mismatch, depth `≥ maxCallDepth`, an escaping `break`, …) and `fuel`.
* The nine evaluators are the fields of one `Oracle`; `Oracle.next` performs
  one unfolding of every rule, calling the previous oracle on premises, and
  `oracle f` iterates it `f` times from the all-`fuel` oracle. Every premise
  that is a function in the relations (`binOpSem`, `Store.get?`, `set?`,
  `allocClosure`, `allocFrame`, `define`, `defineCost`, `binOpCost`,
  `bindParamsCost`, `printArgs`, `Value.truthy`) is called verbatim.
* `oracle_le`: fuel monotonicity (`done`/`stuck` are stable under more fuel).
* `evalE_complete` … `execSeq_complete`: every derivation is found at some
  fuel (mutual structural recursion on the derivation).
* Consumers: `execSeqCost_eq_of_eval`, `execSeqCost_none_of_stuck`, and the
  Bool-checked forms `execSeqCost_eq_of_normalCost` /
  `execSeqCost_capacity_of_normalCost` for `decide +kernel`.
* Validation: the test programs of `Vsa/While/Programs.lean` evaluated by the
  kernel (the loop programs take several seconds each: every block iteration
  allocates a frame, and the kernel reads the frame array as a list).
-/

namespace Vsa.While

/-! ## Three-valued results -/

/-- Result of a fuel-bounded evaluation. -/
inductive Res (α : Type) where
  | done (a : α)
  | stuck
  | fuel
  deriving Repr

namespace Res

/-- Sequencing: `stuck` and `fuel` propagate. -/
def bind {α β : Type} : Res α → (α → Res β) → Res β
  | .done a, k => k a
  | .stuck, _ => .stuck
  | .fuel, _ => .fuel

/-- A partial premise function: `none` means no rule applies. -/
def ofOption {α : Type} : Option α → Res α
  | some a => .done a
  | none => .stuck

/-- Information order: `fuel` is below everything, other results only below
themselves. -/
def Le {α : Type} (r r' : Res α) : Prop := r = .fuel ∨ r = r'

theorem Le.refl {α : Type} (r : Res α) : Le r r := Or.inr rfl

theorem Le.fuel {α : Type} (r : Res α) : Le .fuel r := Or.inl rfl

theorem Le.trans {α : Type} {r r' r'' : Res α} (h : Le r r') (h' : Le r' r'') :
    Le r r'' := by
  rcases h with rfl | rfl
  · exact Le.fuel _
  · exact h'

theorem Le.bind {α β : Type} {r r' : Res α} {k k' : α → Res β} (h : Le r r')
    (hk : ∀ a, Le (k a) (k' a)) : Le (r.bind k) (r'.bind k') := by
  rcases h with rfl | rfl
  · exact Le.fuel _
  · cases r with
    | done a => exact hk a
    | stuck => exact Le.refl _
    | fuel => exact Le.fuel _

theorem Le.ite {α : Type} {c : Prop} [Decidable c] {a a' b b' : Res α} (ha : Le a a')
    (hb : Le b b') : Le (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using ha
  · simpa only [h, ↓reduceIte] using hb

/-- `done` is stable upward. -/
theorem Le.done_of {α : Type} {r r' : Res α} {a : α} (h : Le r r') (hr : r = .done a) :
    r' = .done a := by
  subst hr
  rcases h with h | h
  · cases h
  · exact h.symm

/-- `stuck` is stable upward. -/
theorem Le.stuck_of {α : Type} {r r' : Res α} (h : Le r r') (hr : r = .stuck) :
    r' = .stuck := by
  subst hr
  rcases h with h | h
  · cases h
  · exact h.symm

/-- `true` iff the result is `stuck`. -/
def isStuck {α : Type} : Res α → Bool
  | .stuck => true
  | _ => false

theorem eq_stuck_of_isStuck {α : Type} {r : Res α} (h : r.isStuck = true) : r = .stuck := by
  cases r with
  | done _ => cases h
  | stuck => rfl
  | fuel => cases h

end Res

/-- Dispatch on a statement status. -/
def onStatus {β : Type} (s : Status) (normal brk cont : β) (ret : Value → β) : β :=
  match s with
  | .normal => normal
  | .brk => brk
  | .cont => cont
  | .ret v => ret v

theorem Res.Le.onStatus {α : Type} {s : Status} {n n' b b' c c' : Res α}
    {r r' : Value → Res α} (hn : Le n n') (hb : Le b b') (hc : Le c c')
    (hr : ∀ v, Le (r v) (r' v)) :
    Le (Vsa.While.onStatus s n b c r) (Vsa.While.onStatus s n' b' c' r') := by
  cases s with
  | normal => exact hn
  | brk => exact hb
  | cont => exact hc
  | ret v => exact hr v

/-! ## Result payloads -/

/-- Payload of `EvalECost`/`CallCost`: final state, value, cost. -/
structure EOut where
  st : St
  v : Value
  n : Nat

/-- Payload of `EvalArgsCost`. -/
structure AOut where
  st : St
  vs : List Value
  n : Nat

/-- Payload of `ExecSCost`/`ForLoopCost`/`ExecSeqCost`. -/
structure SOut where
  st : St
  status : Status
  n : Nat

/-- Payload of the `for`-condition evaluator: `ok` is the condition's
truthiness (`true` for an absent condition). `ForCondCost` corresponds to
`ok = true`; `ForLoopCost.condFalse` to `ok = false`. -/
structure COut where
  st : St
  ok : Bool
  n : Nat

/-- Payload of `ExecInitCost`/`ExecStepCost`. -/
structure UOut where
  st : St
  n : Nat

/-! ## Rule helpers -/

/-- The value a finished closure body returns (`CallCost.closure`'s
`status = .normal ∧ v = .null ∨ status = .ret v`). -/
def callResult : Status → Option Value
  | .normal => some .null
  | .ret v => some v
  | .brk => none
  | .cont => none

/-- The asserted value of `CallCost.assertOk` (`vs = [v] ∨ vs = [v, m]`). -/
def assertArg : List Value → Option Value
  | [v] => some v
  | [v, _] => some v
  | _ => none

/-- The operand of `EvalECost.neg`. -/
def Value.asInt : Value → Option Int
  | .int n => some n
  | _ => none

/-! ## The oracle: one field per relation -/

/-- One evaluator per cost relation. -/
structure Oracle where
  e : St → Nat → Addr → Expr → Res EOut
  args : St → Nat → Addr → List Expr → Res AOut
  call : St → Nat → Value → List Value → Res EOut
  s : St → Nat → Addr → Stmt → Res SOut
  init : St → Nat → Addr → Option Stmt → Res UOut
  loop : St → Nat → Addr → Option Expr → Option Expr → Stmt → Res SOut
  cond : St → Nat → Addr → Option Expr → Res COut
  step : St → Nat → Addr → Option Expr → Res UOut
  seq : St → Nat → Addr → List Stmt → Res SOut

namespace Oracle

/-- `EvalECost` rules, premises answered by `o`. -/
def stepE (o : Oracle) (st : St) (d : Nat) (env : Addr) : Expr → Res EOut
  | .int n => .done ⟨st, .int n, 0⟩
  | .str s => .done ⟨st, .str s, 0⟩
  | .bool b => .done ⟨st, .bool b, 0⟩
  | .null => .done ⟨st, .null, 0⟩
  | .var x => (Res.ofOption (st.store.get? env x)).bind fun v => .done ⟨st, v, 0⟩
  | .assign x e => (o.e st d env e).bind fun r =>
      (Res.ofOption (r.st.store.set? env x r.v)).bind fun store'' =>
        .done ⟨⟨store'', r.st.out⟩, r.v, r.n⟩
  | .binary op l r => (o.e st d env l).bind fun rl => (o.e rl.st d env r).bind fun rr =>
      (Res.ofOption (binOpSem rr.st.store op rl.v rr.v)).bind fun v =>
        .done ⟨rr.st, v, rl.n + rr.n + binOpCost rr.st.store op rl.v rr.v⟩
  | .logical .or l r => (o.e st d env l).bind fun rl =>
      if rl.v.truthy then .done ⟨rl.st, .bool true, rl.n⟩
      else (o.e rl.st d env r).bind fun rr => .done ⟨rr.st, .bool rr.v.truthy, rl.n + rr.n⟩
  | .logical .and l r => (o.e st d env l).bind fun rl =>
      if rl.v.truthy then
        (o.e rl.st d env r).bind fun rr => .done ⟨rr.st, .bool rr.v.truthy, rl.n + rr.n⟩
      else .done ⟨rl.st, .bool false, rl.n⟩
  | .unary .neg e => (o.e st d env e).bind fun r =>
      (Res.ofOption r.v.asInt).bind fun n => .done ⟨r.st, .int (wrap64 (-n)), r.n⟩
  | .unary .not e => (o.e st d env e).bind fun r => .done ⟨r.st, .bool (!r.v.truthy), r.n⟩
  | .call f args => (o.e st d env f).bind fun rf =>
      if args.length ≤ maxArgs then
        (o.args rf.st d env args).bind fun ra => (o.call ra.st d rf.v ra.vs).bind fun rc =>
          .done ⟨rc.st, rc.v, rf.n + ra.n + rc.n⟩
      else .stuck
  | .fn name params body =>
      .done ⟨⟨(st.store.allocClosure ⟨env, name, params, body⟩).1, st.out⟩,
        .closure (st.store.allocClosure ⟨env, name, params, body⟩).2, closureBytes⟩

/-- `EvalArgsCost` rules. -/
def stepArgs (o : Oracle) (st : St) (d : Nat) (env : Addr) : List Expr → Res AOut
  | [] => .done ⟨st, [], 0⟩
  | e :: es => (o.e st d env e).bind fun r => (o.args r.st d env es).bind fun rs =>
      .done ⟨rs.st, r.v :: rs.vs, r.n + rs.n⟩

/-- `CallCost` rules. -/
def stepCall (o : Oracle) (st : St) (d : Nat) : Value → List Value → Res EOut
  | .closure a, vs => (Res.ofOption st.store.closures[a]?).bind fun cd =>
      if vs.length = cd.params.length ∧ d < maxCallDepth then
        (o.seq ⟨(cd.params.zip vs).foldl
            (fun s (x, v) => s.define (st.store.allocFrame (some cd.env)).2 x v)
            (st.store.allocFrame (some cd.env)).1, st.out⟩
          (d + 1) (st.store.allocFrame (some cd.env)).2 cd.body).bind fun rb =>
        (Res.ofOption (callResult rb.status)).bind fun v =>
          .done ⟨rb.st, v, envBytes + bindParamsCost (st.store.allocFrame (some cd.env)).1
            (st.store.allocFrame (some cd.env)).2 (cd.params.zip vs) + rb.n⟩
      else .stuck
  | .native .print, vs => .done ⟨⟨st.store, st.out ++ printArgs st.store vs⟩, .null, 0⟩
  | .native .println, vs =>
      .done ⟨⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩, .null, 0⟩
  | .native .assert, vs => (Res.ofOption (assertArg vs)).bind fun v =>
      if v.truthy then .done ⟨st, .null, 0⟩ else .stuck
  | .null, _ => .stuck
  | .bool _, _ => .stuck
  | .int _, _ => .stuck
  | .str _, _ => .stuck

/-- `ExecSCost` rules. -/
def stepS (o : Oracle) (st : St) (d : Nat) (env : Addr) : Stmt → Res SOut
  | .expr e => (o.e st d env e).bind fun r => .done ⟨r.st, .normal, r.n⟩
  | .varDecl x (some e) => (o.e st d env e).bind fun r =>
      .done ⟨⟨r.st.store.define env x r.v, r.st.out⟩, .normal, r.n + defineCost r.st.store env x⟩
  | .varDecl x none =>
      .done ⟨⟨st.store.define env x .null, st.out⟩, .normal, defineCost st.store env x⟩
  | .block ss =>
      (o.seq ⟨(st.store.allocFrame (some env)).1, st.out⟩ d
          (st.store.allocFrame (some env)).2 ss).bind fun r =>
        .done ⟨r.st, r.status, envBytes + r.n⟩
  | .ifStmt c t (some e) => (o.e st d env c).bind fun rc =>
      if rc.v.truthy then
        (o.s rc.st d env t).bind fun rt => .done ⟨rt.st, rt.status, rc.n + rt.n⟩
      else (o.s rc.st d env e).bind fun re => .done ⟨re.st, re.status, rc.n + re.n⟩
  | .ifStmt c t none => (o.e st d env c).bind fun rc =>
      if rc.v.truthy then
        (o.s rc.st d env t).bind fun rt => .done ⟨rt.st, rt.status, rc.n + rt.n⟩
      else .done ⟨rc.st, .normal, rc.n⟩
  | .whileStmt c b => (o.e st d env c).bind fun rc =>
      if rc.v.truthy then
        (o.s rc.st d env b).bind fun rb =>
          onStatus rb.status
            ((o.s rb.st d env (.whileStmt c b)).bind fun rr =>
              .done ⟨rr.st, rr.status, rc.n + rb.n + rr.n⟩)
            (.done ⟨rb.st, .normal, rc.n + rb.n⟩)
            ((o.s rb.st d env (.whileStmt c b)).bind fun rr =>
              .done ⟨rr.st, rr.status, rc.n + rb.n + rr.n⟩)
            (fun rv => .done ⟨rb.st, .ret rv, rc.n + rb.n⟩)
      else .done ⟨rc.st, .normal, rc.n⟩
  | .forStmt init cnd step b =>
      (o.init ⟨(st.store.allocFrame (some env)).1, st.out⟩ d
          (st.store.allocFrame (some env)).2 init).bind fun ri =>
        (o.loop ri.st d (st.store.allocFrame (some env)).2 cnd step b).bind fun rl =>
          .done ⟨rl.st, rl.status, envBytes + ri.n + rl.n⟩
  | .ret (some e) => (o.e st d env e).bind fun r => .done ⟨r.st, .ret r.v, r.n⟩
  | .ret none => .done ⟨st, .ret .null, 0⟩
  | .brk => .done ⟨st, .brk, 0⟩
  | .cont => .done ⟨st, .cont, 0⟩

/-- `ExecInitCost` rules (the init's status is discarded). -/
def stepInit (o : Oracle) (st : St) (d : Nat) (env : Addr) : Option Stmt → Res UOut
  | none => .done ⟨st, 0⟩
  | some s => (o.s st d env s).bind fun r => .done ⟨r.st, r.n⟩

/-- `ForLoopCost` rules: the condition flag selects `condFalse`; otherwise
the body status selects `bodyBreak`/`bodyRet`/`loop`. -/
def stepLoop (o : Oracle) (st : St) (d : Nat) (env : Addr) (cnd step : Option Expr)
    (b : Stmt) : Res SOut :=
  (o.cond st d env cnd).bind fun rc =>
    if rc.ok then
      (o.s rc.st d env b).bind fun rb =>
        onStatus rb.status
          ((o.step rb.st d env step).bind fun rs =>
            (o.loop rs.st d env cnd step b).bind fun rl =>
              .done ⟨rl.st, rl.status, rc.n + rb.n + rs.n + rl.n⟩)
          (.done ⟨rb.st, .normal, rc.n + rb.n⟩)
          ((o.step rb.st d env step).bind fun rs =>
            (o.loop rs.st d env cnd step b).bind fun rl =>
              .done ⟨rl.st, rl.status, rc.n + rb.n + rs.n + rl.n⟩)
          (fun rv => .done ⟨rb.st, .ret rv, rc.n + rb.n⟩)
    else .done ⟨rc.st, .normal, rc.n⟩

/-- The `for` condition with its truthiness (`ForCondCost` / `condFalse`). -/
def stepCond (o : Oracle) (st : St) (d : Nat) (env : Addr) : Option Expr → Res COut
  | none => .done ⟨st, true, 0⟩
  | some c => (o.e st d env c).bind fun r => .done ⟨r.st, r.v.truthy, r.n⟩

/-- `ExecStepCost` rules. -/
def stepStep (o : Oracle) (st : St) (d : Nat) (env : Addr) : Option Expr → Res UOut
  | none => .done ⟨st, 0⟩
  | some e => (o.e st d env e).bind fun r => .done ⟨r.st, r.n⟩

/-- `ExecSeqCost` rules. -/
def stepSeq (o : Oracle) (st : St) (d : Nat) (env : Addr) : List Stmt → Res SOut
  | [] => .done ⟨st, .normal, 0⟩
  | s :: ss => (o.s st d env s).bind fun r1 =>
      onStatus r1.status
        ((o.seq r1.st d env ss).bind fun r2 => .done ⟨r2.st, r2.status, r1.n + r2.n⟩)
        (.done r1) (.done r1) (fun _ => .done r1)

/-- One unfolding of all nine relations. -/
def next (o : Oracle) : Oracle where
  e := o.stepE
  args := o.stepArgs
  call := o.stepCall
  s := o.stepS
  init := o.stepInit
  loop := o.stepLoop
  cond := o.stepCond
  step := o.stepStep
  seq := o.stepSeq

/-- The oracle that has no fuel. -/
def bot : Oracle where
  e _ _ _ _ := .fuel
  args _ _ _ _ := .fuel
  call _ _ _ _ := .fuel
  s _ _ _ _ := .fuel
  init _ _ _ _ := .fuel
  loop _ _ _ _ _ _ := .fuel
  cond _ _ _ _ := .fuel
  step _ _ _ _ := .fuel
  seq _ _ _ _ := .fuel

end Oracle

/-- The evaluator at fuel `f`: `f` unfoldings of every rule. -/
def oracle : Nat → Oracle
  | 0 => .bot
  | f + 1 => (oracle f).next

theorem oracle_succ (f : Nat) : oracle (f + 1) = (oracle f).next := rfl

/-! ## The nine evaluators -/

def evalE (f : Nat) : St → Nat → Addr → Expr → Res EOut := (oracle f).e
def evalArgs (f : Nat) : St → Nat → Addr → List Expr → Res AOut := (oracle f).args
def callEval (f : Nat) : St → Nat → Value → List Value → Res EOut := (oracle f).call
def execSEval (f : Nat) : St → Nat → Addr → Stmt → Res SOut := (oracle f).s
def execInitEval (f : Nat) : St → Nat → Addr → Option Stmt → Res UOut := (oracle f).init
def forLoopEval (f : Nat) :
    St → Nat → Addr → Option Expr → Option Expr → Stmt → Res SOut := (oracle f).loop
def forCondEval (f : Nat) : St → Nat → Addr → Option Expr → Res COut := (oracle f).cond
def execStepEval (f : Nat) : St → Nat → Addr → Option Expr → Res UOut := (oracle f).step
def execSeqEval (f : Nat) : St → Nat → Addr → List Stmt → Res SOut := (oracle f).seq

/-! ## Fuel monotonicity -/

/-- Pointwise information order on oracles. -/
structure Oracle.Le (o o' : Oracle) : Prop where
  e : ∀ st d env x, Res.Le (o.e st d env x) (o'.e st d env x)
  args : ∀ st d env x, Res.Le (o.args st d env x) (o'.args st d env x)
  call : ∀ st d fv vs, Res.Le (o.call st d fv vs) (o'.call st d fv vs)
  s : ∀ st d env x, Res.Le (o.s st d env x) (o'.s st d env x)
  init : ∀ st d env x, Res.Le (o.init st d env x) (o'.init st d env x)
  loop : ∀ st d env cnd step b,
    Res.Le (o.loop st d env cnd step b) (o'.loop st d env cnd step b)
  cond : ∀ st d env x, Res.Le (o.cond st d env x) (o'.cond st d env x)
  step : ∀ st d env x, Res.Le (o.step st d env x) (o'.step st d env x)
  seq : ∀ st d env x, Res.Le (o.seq st d env x) (o'.seq st d env x)

/-- Closes `Res.Le (B o) (B o')` for a rule body `B` built from `bind`, `if`,
`onStatus` and oracle calls, given `o.Le o'` in context. -/
syntax "res_mono" : tactic
macro_rules
  | `(tactic| res_mono) => `(tactic| repeat' (first
      | exact Res.Le.refl _
      | intro _
      | apply Res.Le.bind
      | apply Res.Le.ite
      | apply Res.Le.onStatus
      | (apply Oracle.Le.e; assumption)
      | (apply Oracle.Le.args; assumption)
      | (apply Oracle.Le.call; assumption)
      | (apply Oracle.Le.s; assumption)
      | (apply Oracle.Le.init; assumption)
      | (apply Oracle.Le.loop; assumption)
      | (apply Oracle.Le.cond; assumption)
      | (apply Oracle.Le.step; assumption)
      | (apply Oracle.Le.seq; assumption)))

/-- One unfolding is monotone in the premise oracle. -/
theorem Oracle.Le.next {o o' : Oracle} (h : o.Le o') : o.next.Le o'.next where
  e st d env x := by
    show Res.Le (o.stepE st d env x) (o'.stepE st d env x)
    cases x <;> (try cases ‹LogOp›) <;> (try cases ‹UnOp›) <;>
      simp only [Oracle.stepE] <;> res_mono
  args st d env x := by
    show Res.Le (o.stepArgs st d env x) (o'.stepArgs st d env x)
    cases x <;> simp only [Oracle.stepArgs] <;> res_mono
  call st d fv vs := by
    show Res.Le (o.stepCall st d fv vs) (o'.stepCall st d fv vs)
    cases fv <;> (try cases ‹NativeFn›) <;> simp only [Oracle.stepCall] <;> res_mono
  s st d env x := by
    show Res.Le (o.stepS st d env x) (o'.stepS st d env x)
    cases x with
    | varDecl x init => cases init <;> simp only [Oracle.stepS] <;> res_mono
    | ifStmt c t e => cases e <;> simp only [Oracle.stepS] <;> res_mono
    | ret e => cases e <;> simp only [Oracle.stepS] <;> res_mono
    | _ => simp only [Oracle.stepS] <;> res_mono
  init st d env x := by
    show Res.Le (o.stepInit st d env x) (o'.stepInit st d env x)
    cases x <;> simp only [Oracle.stepInit] <;> res_mono
  loop st d env cnd step b := by
    show Res.Le (o.stepLoop st d env cnd step b) (o'.stepLoop st d env cnd step b)
    simp only [Oracle.stepLoop]; res_mono
  cond st d env x := by
    show Res.Le (o.stepCond st d env x) (o'.stepCond st d env x)
    cases x <;> simp only [Oracle.stepCond] <;> res_mono
  step st d env x := by
    show Res.Le (o.stepStep st d env x) (o'.stepStep st d env x)
    cases x <;> simp only [Oracle.stepStep] <;> res_mono
  seq st d env x := by
    show Res.Le (o.stepSeq st d env x) (o'.stepSeq st d env x)
    cases x <;> simp only [Oracle.stepSeq] <;> res_mono

theorem Oracle.Le.bot (o : Oracle) : Oracle.bot.Le o where
  e _ _ _ _ := Res.Le.fuel _
  args _ _ _ _ := Res.Le.fuel _
  call _ _ _ _ := Res.Le.fuel _
  s _ _ _ _ := Res.Le.fuel _
  init _ _ _ _ := Res.Le.fuel _
  loop _ _ _ _ _ _ := Res.Le.fuel _
  cond _ _ _ _ := Res.Le.fuel _
  step _ _ _ _ := Res.Le.fuel _
  seq _ _ _ _ := Res.Le.fuel _

/-- **Fuel monotonicity** of all nine evaluators at once. -/
theorem oracle_le : ∀ {f f' : Nat}, f ≤ f' → (oracle f).Le (oracle f')
  | 0, _, _ => Oracle.Le.bot _
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, h => (oracle_le (Nat.le_of_succ_le_succ h)).next

/-- Fuel monotonicity of the statement-sequence evaluator: a `done` result
persists at every larger fuel. -/
theorem execSeqEval_done_mono {f f' : Nat} (hf : f ≤ f') {st d env ss} {r : SOut}
    (h : execSeqEval f st d env ss = .done r) : execSeqEval f' st d env ss = .done r :=
  ((oracle_le hf).seq st d env ss).done_of h

/-- Fuel monotonicity of the statement-sequence evaluator: a `stuck` result
persists at every larger fuel. -/
theorem execSeqEval_stuck_mono {f f' : Nat} (hf : f ≤ f') {st d env ss}
    (h : execSeqEval f st d env ss = .stuck) : execSeqEval f' st d env ss = .stuck :=
  ((oracle_le hf).seq st d env ss).stuck_of h

/-- Fuel monotonicity of the expression evaluator. -/
theorem evalE_mono {f f' : Nat} (hf : f ≤ f') (st d env e) :
    Res.Le (evalE f st d env e) (evalE f' st d env e) :=
  (oracle_le hf).e st d env e

/-! ## Completeness -/

/-- `g` eventually (at some fuel) returns `done a`. -/
def Reaches {α : Type} (g : Nat → Res α) (a : α) : Prop := ∃ f, g f = .done a

section lift
variable {f F : Nat}

theorem lift_e {st d env x a} (hf : f ≤ F) (h : (oracle f).e st d env x = .done a) :
    (oracle F).e st d env x = .done a := ((oracle_le hf).e st d env x).done_of h
theorem lift_args {st d env x a} (hf : f ≤ F) (h : (oracle f).args st d env x = .done a) :
    (oracle F).args st d env x = .done a := ((oracle_le hf).args st d env x).done_of h
theorem lift_call {st d fv vs a} (hf : f ≤ F) (h : (oracle f).call st d fv vs = .done a) :
    (oracle F).call st d fv vs = .done a := ((oracle_le hf).call st d fv vs).done_of h
theorem lift_s {st d env x a} (hf : f ≤ F) (h : (oracle f).s st d env x = .done a) :
    (oracle F).s st d env x = .done a := ((oracle_le hf).s st d env x).done_of h
theorem lift_init {st d env x a} (hf : f ≤ F) (h : (oracle f).init st d env x = .done a) :
    (oracle F).init st d env x = .done a := ((oracle_le hf).init st d env x).done_of h
theorem lift_loop {st d env cnd step b a} (hf : f ≤ F) (h : (oracle f).loop st d env cnd step b = .done a) :
    (oracle F).loop st d env cnd step b = .done a :=
  ((oracle_le hf).loop st d env cnd step b).done_of h
theorem lift_cond {st d env x a} (hf : f ≤ F) (h : (oracle f).cond st d env x = .done a) :
    (oracle F).cond st d env x = .done a := ((oracle_le hf).cond st d env x).done_of h
theorem lift_step {st d env x a} (hf : f ≤ F) (h : (oracle f).step st d env x = .done a) :
    (oracle F).step st d env x = .done a := ((oracle_le hf).step st d env x).done_of h
theorem lift_seq {st d env x a} (hf : f ≤ F) (h : (oracle f).seq st d env x = .done a) :
    (oracle F).seq st d env x = .done a := ((oracle_le hf).seq st d env x).done_of h

end lift

/-- Unfold one fuel level and the rule bodies, then reduce the binds. -/
syntax "reach_simp" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| reach_simp $[[$ls,*]]?) => do
    let ls := (ls.map (·.getElems)).getD #[]
    `(tactic| simp only [oracle_succ, Oracle.next, Oracle.stepE, Oracle.stepArgs,
        Oracle.stepCall, Oracle.stepS, Oracle.stepInit, Oracle.stepLoop, Oracle.stepCond,
        Oracle.stepStep, Oracle.stepSeq, Res.bind, Res.ofOption, onStatus, callResult,
        assertArg, Value.asInt, Bool.false_eq_true, ↓reduceIte, $ls,*])

mutual

theorem evalE_complete {st d env e st' v n} (h : EvalECost st d env e st' v n) :
    Reaches (fun f => (oracle f).e st d env e) ⟨st', v, n⟩ :=
  match h with
  | .int .. => by exact ⟨1, rfl⟩
  | .str .. => by exact ⟨1, rfl⟩
  | .bool .. => by exact ⟨1, rfl⟩
  | .null .. => by exact ⟨1, rfl⟩
  | .var _ _ _ _ _ hv => by exact ⟨1, by reach_simp [hv]⟩
  | .assign _ _ _ _ _ _ _ _ _ he hs => by
    obtain ⟨f1, h1⟩ := evalE_complete he
    exact ⟨f1 + 1, by reach_simp [lift_e (Nat.le_refl _) h1, hs]⟩
  | .binary _ _ _ _ _ _ _ _ _ _ _ _ _ hl hr hop => by
    obtain ⟨f1, h1⟩ := evalE_complete hl
    obtain ⟨f2, h2⟩ := evalE_complete hr
    exact ⟨f1 + f2 + 1, by
      reach_simp [lift_e (Nat.le_add_right f1 f2) h1, lift_e (Nat.le_add_left f2 f1) h2, hop]⟩
  | .orTrue _ _ _ _ _ _ _ _ hl ht => by
    obtain ⟨f1, h1⟩ := evalE_complete hl
    exact ⟨f1 + 1, by reach_simp [lift_e (Nat.le_refl _) h1, ht]⟩
  | .orFalse _ _ _ _ _ _ _ _ _ _ _ hl hf hr => by
    obtain ⟨f1, h1⟩ := evalE_complete hl
    obtain ⟨f2, h2⟩ := evalE_complete hr
    exact ⟨f1 + f2 + 1, by
      reach_simp [lift_e (Nat.le_add_right f1 f2) h1, lift_e (Nat.le_add_left f2 f1) h2, hf]⟩
  | .andFalse _ _ _ _ _ _ _ _ hl hf => by
    obtain ⟨f1, h1⟩ := evalE_complete hl
    exact ⟨f1 + 1, by reach_simp [lift_e (Nat.le_refl _) h1, hf]⟩
  | .andTrue _ _ _ _ _ _ _ _ _ _ _ hl ht hr => by
    obtain ⟨f1, h1⟩ := evalE_complete hl
    obtain ⟨f2, h2⟩ := evalE_complete hr
    exact ⟨f1 + f2 + 1, by
      reach_simp [lift_e (Nat.le_add_right f1 f2) h1, lift_e (Nat.le_add_left f2 f1) h2, ht]⟩
  | .neg _ _ _ _ _ _ _ he => by
    obtain ⟨f1, h1⟩ := evalE_complete he
    exact ⟨f1 + 1, by reach_simp [lift_e (Nat.le_refl _) h1]⟩
  | .not _ _ _ _ _ _ _ he => by
    obtain ⟨f1, h1⟩ := evalE_complete he
    exact ⟨f1 + 1, by reach_simp [lift_e (Nat.le_refl _) h1]⟩
  | .call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf hlen ha hc => by
    obtain ⟨f1, h1⟩ := evalE_complete hf
    obtain ⟨f2, h2⟩ := evalArgs_complete ha
    obtain ⟨f3, h3⟩ := call_complete hc
    exact ⟨f1 + f2 + f3 + 1, by
      reach_simp [lift_e (F := f1 + f2 + f3) (by omega) h1, lift_args (F := f1 + f2 + f3) (by omega) h2,
        lift_call (F := f1 + f2 + f3) (by omega) h3, hlen]⟩
  | .fn _ _ _ _ _ _ _ _ hc => by exact ⟨1, by reach_simp [hc]⟩

  termination_by structural h

theorem evalArgs_complete {st d env es st' vs n} (h : EvalArgsCost st d env es st' vs n) :
    Reaches (fun f => (oracle f).args st d env es) ⟨st', vs, n⟩ :=
  match h with
  | .nil .. => by exact ⟨1, rfl⟩
  | .cons _ _ _ _ _ _ _ _ _ _ _ he hes => by
    obtain ⟨f1, h1⟩ := evalE_complete he
    obtain ⟨f2, h2⟩ := evalArgs_complete hes
    exact ⟨f1 + f2 + 1, by
      reach_simp [lift_e (Nat.le_add_right f1 f2) h1, lift_args (Nat.le_add_left f2 f1) h2]⟩

  termination_by structural h

theorem call_complete {st d fv vs st' v n} (h : CallCost st d fv vs st' v n) :
    Reaches (fun f => (oracle f).call st d fv vs) ⟨st', v, n⟩ :=
  match h with
  | .closure _ _ _ _ _ _ _ _ _ _ _ hcd hlen hd hfr hb hstat => by
    obtain ⟨f1, h1⟩ := execSeq_complete hb
    refine ⟨f1 + 1, ?_⟩
    reach_simp [hcd, hfr, hlen, hd, eq_self_iff_true, and_self, lift_seq (Nat.le_refl _) h1]
    rcases hstat with ⟨rfl, rfl⟩ | rfl <;> rfl
  | .print .. => by exact ⟨1, rfl⟩
  | .println .. => by exact ⟨1, rfl⟩
  | .assertOk _ _ _ _ _ hvs ht => by
    refine ⟨1, ?_⟩
    rcases hvs with rfl | rfl <;> reach_simp [ht]

  termination_by structural h

theorem execS_complete {st d env s st' status n} (h : ExecSCost st d env s st' status n) :
    Reaches (fun f => (oracle f).s st d env s) ⟨st', status, n⟩ :=
  match h with
  | .expr _ _ _ _ _ _ _ he => by
    obtain ⟨f1, h1⟩ := evalE_complete he
    exact ⟨f1 + 1, by reach_simp [lift_e (Nat.le_refl _) h1]⟩
  | .varInit _ _ _ _ _ _ _ _ he => by
    obtain ⟨f1, h1⟩ := evalE_complete he
    exact ⟨f1 + 1, by reach_simp [lift_e (Nat.le_refl _) h1]⟩
  | .varNull .. => by exact ⟨1, rfl⟩
  | .block _ _ _ _ _ _ _ _ _ hfr hb => by
    obtain ⟨f1, h1⟩ := execSeq_complete hb
    exact ⟨f1 + 1, by reach_simp [hfr, lift_seq (Nat.le_refl _) h1]⟩
  | .ifTrue _ _ _ _ _ e _ _ _ _ _ _ hc ht hs => by
    obtain ⟨f1, h1⟩ := evalE_complete hc
    obtain ⟨f2, h2⟩ := execS_complete hs
    refine ⟨f1 + f2 + 1, ?_⟩
    cases e <;>
      reach_simp [lift_e (Nat.le_add_right f1 f2) h1, lift_s (Nat.le_add_left f2 f1) h2, ht]
  | .ifFalse _ _ _ _ _ _ _ _ _ _ _ _ hc hf hs => by
    obtain ⟨f1, h1⟩ := evalE_complete hc
    obtain ⟨f2, h2⟩ := execS_complete hs
    exact ⟨f1 + f2 + 1, by
      reach_simp [lift_e (Nat.le_add_right f1 f2) h1, lift_s (Nat.le_add_left f2 f1) h2, hf]⟩
  | .ifNone _ _ _ _ _ _ _ _ hc hf => by
    obtain ⟨f1, h1⟩ := evalE_complete hc
    exact ⟨f1 + 1, by reach_simp [lift_e (Nat.le_refl _) h1, hf]⟩
  | .whileFalse _ _ _ _ _ _ _ _ hc hf => by
    obtain ⟨f1, h1⟩ := evalE_complete hc
    exact ⟨f1 + 1, by reach_simp [lift_e (Nat.le_refl _) h1, hf]⟩
  | .whileBreak _ _ _ _ _ _ _ _ _ _ hc ht hb => by
    obtain ⟨f1, h1⟩ := evalE_complete hc
    obtain ⟨f2, h2⟩ := execS_complete hb
    exact ⟨f1 + f2 + 1, by
      reach_simp [lift_e (Nat.le_add_right f1 f2) h1, lift_s (Nat.le_add_left f2 f1) h2, ht]⟩
  | .whileRet _ _ _ _ _ _ _ _ _ _ _ hc ht hb => by
    obtain ⟨f1, h1⟩ := evalE_complete hc
    obtain ⟨f2, h2⟩ := execS_complete hb
    exact ⟨f1 + f2 + 1, by
      reach_simp [lift_e (Nat.le_add_right f1 f2) h1, lift_s (Nat.le_add_left f2 f1) h2, ht]⟩
  | .whileLoop _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc ht hb hst hr => by
    obtain ⟨f1, h1⟩ := evalE_complete hc
    obtain ⟨f2, h2⟩ := execS_complete hb
    obtain ⟨f3, h3⟩ := execS_complete hr
    refine ⟨f1 + f2 + f3 + 1, ?_⟩
    rcases hst with rfl | rfl <;>
      reach_simp [lift_e (F := f1 + f2 + f3) (by omega) h1, lift_s (F := f1 + f2 + f3) (by omega) h2,
        lift_s (F := f1 + f2 + f3) (by omega) h3, ht]
  | .forStart _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfr hi hl => by
    obtain ⟨f1, h1⟩ := execInit_complete hi
    obtain ⟨f2, h2⟩ := forLoop_complete hl
    exact ⟨f1 + f2 + 1, by
      reach_simp [hfr, lift_init (Nat.le_add_right f1 f2) h1,
        lift_loop (Nat.le_add_left f2 f1) h2]⟩
  | .ret _ _ _ _ _ _ _ he => by
    obtain ⟨f1, h1⟩ := evalE_complete he
    exact ⟨f1 + 1, by reach_simp [lift_e (Nat.le_refl _) h1]⟩
  | .retNull .. => by exact ⟨1, rfl⟩
  | .brk .. => by exact ⟨1, rfl⟩
  | .cont .. => by exact ⟨1, rfl⟩

  termination_by structural h

theorem execInit_complete {st d env init st' n} (h : ExecInitCost st d env init st' n) :
    Reaches (fun f => (oracle f).init st d env init) ⟨st', n⟩ :=
  match h with
  | .none .. => by exact ⟨1, rfl⟩
  | .some _ _ _ _ _ _ _ hs => by
    obtain ⟨f1, h1⟩ := execS_complete hs
    exact ⟨f1 + 1, by reach_simp [lift_s (Nat.le_refl _) h1]⟩

  termination_by structural h

theorem forLoop_complete {st d env cnd step b st' status n}
    (h : ForLoopCost st d env cnd step b st' status n) :
    Reaches (fun f => (oracle f).loop st d env cnd step b) ⟨st', status, n⟩ :=
  match h with
  | .condFalse _ _ _ _ _ _ _ _ _ hc hf => by
    obtain ⟨f1, h1⟩ := evalE_complete hc
    exact ⟨f1 + 2, by reach_simp [lift_e (Nat.le_refl _) h1, hf]⟩
  | .bodyBreak _ _ _ _ _ _ _ _ _ _ hc hb => by
    obtain ⟨f1, h1⟩ := forCond_complete hc
    obtain ⟨f2, h2⟩ := execS_complete hb
    exact ⟨f1 + f2 + 1, by
      reach_simp [lift_cond (Nat.le_add_right f1 f2) h1, lift_s (Nat.le_add_left f2 f1) h2]⟩
  | .bodyRet _ _ _ _ _ _ _ _ _ _ _ hc hb => by
    obtain ⟨f1, h1⟩ := forCond_complete hc
    obtain ⟨f2, h2⟩ := execS_complete hb
    exact ⟨f1 + f2 + 1, by
      reach_simp [lift_cond (Nat.le_add_right f1 f2) h1, lift_s (Nat.le_add_left f2 f1) h2]⟩
  | .loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hb hst hs hr => by
    obtain ⟨f1, h1⟩ := forCond_complete hc
    obtain ⟨f2, h2⟩ := execS_complete hb
    obtain ⟨f3, h3⟩ := execStep_complete hs
    obtain ⟨f4, h4⟩ := forLoop_complete hr
    refine ⟨f1 + f2 + f3 + f4 + 1, ?_⟩
    rcases hst with rfl | rfl <;>
      reach_simp [lift_cond (F := f1 + f2 + f3 + f4) (by omega) h1,
        lift_s (F := f1 + f2 + f3 + f4) (by omega) h2,
        lift_step (F := f1 + f2 + f3 + f4) (by omega) h3,
        lift_loop (F := f1 + f2 + f3 + f4) (by omega) h4]

  termination_by structural h

theorem forCond_complete {st d env cnd st' n} (h : ForCondCost st d env cnd st' n) :
    Reaches (fun f => (oracle f).cond st d env cnd) ⟨st', true, n⟩ :=
  match h with
  | .none .. => by exact ⟨1, rfl⟩
  | .some _ _ _ _ _ _ _ hc ht => by
    obtain ⟨f1, h1⟩ := evalE_complete hc
    exact ⟨f1 + 1, by reach_simp [lift_e (Nat.le_refl _) h1, ht]⟩

  termination_by structural h

theorem execStep_complete {st d env step st' n} (h : ExecStepCost st d env step st' n) :
    Reaches (fun f => (oracle f).step st d env step) ⟨st', n⟩ :=
  match h with
  | .none .. => by exact ⟨1, rfl⟩
  | .some _ _ _ _ _ _ _ he => by
    obtain ⟨f1, h1⟩ := evalE_complete he
    exact ⟨f1 + 1, by reach_simp [lift_e (Nat.le_refl _) h1]⟩

  termination_by structural h

theorem execSeq_complete {st d env ss st' status n} (h : ExecSeqCost st d env ss st' status n) :
    Reaches (fun f => (oracle f).seq st d env ss) ⟨st', status, n⟩ :=
  match h with
  | .nil .. => by exact ⟨1, rfl⟩
  | .consNormal _ _ _ _ _ _ _ _ _ _ hs hss => by
    obtain ⟨f1, h1⟩ := execS_complete hs
    obtain ⟨f2, h2⟩ := execSeq_complete hss
    exact ⟨f1 + f2 + 1, by
      reach_simp [lift_s (Nat.le_add_right f1 f2) h1, lift_seq (Nat.le_add_left f2 f1) h2]⟩
  | .consAbrupt _ _ _ _ _ _ status _ hs hne => by
    obtain ⟨f1, h1⟩ := execS_complete hs
    refine ⟨f1 + 1, ?_⟩
    cases status with
    | normal => exact absurd rfl hne
    | _ => reach_simp [lift_s (Nat.le_refl _) h1]

  termination_by structural h
end

/-! ## Consumers -/

/-- Any derivation from `st` agrees with a `done` result of the evaluator. -/
theorem execSeqCost_eq_of_eval {f : Nat} {st d env} {p : List Stmt} {r0 : SOut}
    {st' : St} {status : Status} {n : Nat}
    (h : execSeqEval f st d env p = .done r0) (hd : ExecSeqCost st d env p st' status n) :
    (⟨st', status, n⟩ : SOut) = r0 := by
  obtain ⟨f1, h1⟩ := execSeq_complete hd
  have e1 := lift_seq (Nat.le_add_right f1 f) h1
  have e0 := lift_seq (F := f1 + f) (Nat.le_add_left f f1) h
  rw [e1] at e0
  exact Res.done.inj e0

/-- Cost projection of `execSeqCost_eq_of_eval`. -/
theorem execSeqCost_n_eq_of_eval {f : Nat} {st d env} {p : List Stmt} {r0 : SOut}
    {st' : St} {status : Status} {n : Nat}
    (h : execSeqEval f st d env p = .done r0) (hd : ExecSeqCost st d env p st' status n) :
    n = r0.n := by
  rw [← execSeqCost_eq_of_eval h hd]

/-- A `stuck` evaluation rules out every derivation. -/
theorem execSeqCost_none_of_stuck {f : Nat} {st d env} {p : List Stmt}
    (h : execSeqEval f st d env p = .stuck) (st' : St) (status : Status) (n : Nat) :
    ¬ ExecSeqCost st d env p st' status n := by
  intro hd
  obtain ⟨f1, h1⟩ := execSeq_complete hd
  have e1 := lift_seq (Nat.le_add_right f1 f) h1
  have e0 := execSeqEval_stuck_mono (f' := f1 + f) (Nat.le_add_left f f1) h
  unfold execSeqEval at e0
  rw [e1] at e0
  cases e0

/-- The cost of a `done`-and-`normal` result (Bool-checkable by the kernel). -/
def Res.normalCost? : Res SOut → Option Nat
  | .done r => if r.status = .normal then some r.n else none
  | _ => none

theorem Res.eq_done_of_normalCost {r : Res SOut} {n0 : Nat} (h : r.normalCost? = some n0) :
    ∃ st0, r = .done ⟨st0, .normal, n0⟩ := by
  cases r with
  | done r =>
    obtain ⟨st0, status, n⟩ := r
    simp only [Res.normalCost?] at h
    by_cases hs : status = .normal
    · subst hs; simp only [↓reduceIte, Option.some.injEq] at h; subst h; exact ⟨st0, rfl⟩
    · simp only [hs, ↓reduceIte, reduceCtorEq] at h
  | stuck => cases h
  | fuel => cases h

/-- Kernel-checkable form: if the evaluator's normal cost is `n0`, every
normal derivation costs exactly `n0`. -/
theorem execSeqCost_eq_of_normalCost {f : Nat} {st d env} {p : List Stmt} {n0 : Nat}
    (h : (execSeqEval f st d env p).normalCost? = some n0) {st' : St} {n : Nat}
    (hd : ExecSeqCost st d env p st' .normal n) : n = n0 := by
  obtain ⟨st0, h0⟩ := Res.eq_done_of_normalCost h
  exact execSeqCost_n_eq_of_eval h0 hd

/-- The capacity premise shape of `DlHeap.InitialAllocatorAt.capacity`,
discharged from one evaluator run. -/
theorem execSeqCost_capacity_of_normalCost {f : Nat} {p : Program} {n0 K : Nat}
    (h : (execSeqEval f initSt 0 0 p).normalCost? = some n0) (hK : 2 * n0 + 8256 ≤ K) :
    ∀ st' n, ExecSeqCost initSt 0 0 p st' .normal n → 2 * n + 8256 ≤ K := by
  intro st' n hd
  rw [execSeqCost_eq_of_normalCost h hd]
  exact hK

/-- Kernel-checkable form of `execSeqCost_none_of_stuck`. -/
theorem execSeqCost_none_of_isStuck {f : Nat} {st d env} {p : List Stmt}
    (h : (execSeqEval f st d env p).isStuck = true) (st' : St) (status : Status) (n : Nat) :
    ¬ ExecSeqCost st d env p st' status n :=
  execSeqCost_none_of_stuck (Res.eq_stuck_of_isStuck h) st' status n

/-! ## Validation on the test programs

Costs computed by the kernel. The printed output of each run agrees with
`Vsa/While/Validation.lean`. -/

section Validation
open Programs

/-- `tests/while.wl`, the script embedded in the ELF. -/
theorem whileWl_normalCost : (execSeqEval 1000 initSt 0 0 whileWl).normalCost? = some 6992 := by
  decide +kernel

/-- Every normal derivation of the embedded script costs exactly 6992. -/
theorem whileWl_cost_eq {st' : St} {n : Nat} (hd : ExecSeqCost initSt 0 0 whileWl st' .normal n) :
    n = 6992 :=
  execSeqCost_eq_of_normalCost whileWl_normalCost hd

example : (execSeqEval 1000 initSt 0 0 arithmeticWl).normalCost? = some 0 := by decide +kernel
example : (execSeqEval 1000 initSt 0 0 forWl).normalCost? = some 6384 := by decide +kernel
example : (execSeqEval 1000 initSt 0 0 functionsWl).normalCost? = some 5296 := by decide +kernel
example : (execSeqEval 1000 initSt 0 0 scopeWl).normalCost? = some 1648 := by decide +kernel
example : (execSeqEval 1000 initSt 0 0 stringsWl).normalCost? = some 208 := by decide +kernel

/-- Division by zero has no derivation. -/
theorem divZero_underivable (st' : St) (status : Status) (n : Nat) :
    ¬ ExecSeqCost initSt 0 0 [.expr (.binary .div (.int 1) (.int 0))] st' status n :=
  execSeqCost_none_of_isStuck (f := 10) (by decide +kernel) st' status n

end Validation

end Vsa.While
