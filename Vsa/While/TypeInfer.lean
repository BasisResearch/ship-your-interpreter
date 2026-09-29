import Vsa.While.TypeSearch

/-!
# Type inference and the WHILE type checker

`infer p` finds a typing environment for `p` whenever one exists:

* `infer_sound`: a result types `p`;
* `infer_complete`: if any `Δ` types `p`, `infer p` succeeds;
* `whileTyped p = true ↔ ∃ Δ, WellTyped Δ p` (`whileTyped_iff`), so
  `Typable p` is decidable.

`infer` runs the complete search of `Vsa/While/TypeSearch.lean` and confirms its
result with the verified checker (`typeCheck_iff`). When there is no typing,
the unverified diagnostic solver `Diag.solve` produces the error message; it
never decides acceptance.
-/

namespace Vsa.While.Types

open Vsa.While

/-! ## Diagnostics

A unification solver over types with variables (`TyV`) that tracks scoping,
loop and return context and reports the first failure in words. `+` and the
comparisons wait until an operand's type is known and otherwise default to
integers. It is only used for error messages. -/

namespace Diag


/-- Types with unification variables. -/
inductive TyV where
  | var (n : Nat)
  | int
  | bool
  | str
  | null
  | native (f : NativeFn)
  | fn (ps : List TyV) (r : TyV)
  deriving Repr, Inhabited

namespace TyV

/-- A ground type as a `TyV`. -/
def ofTy : Ty → TyV
  | .int => .int
  | .bool => .bool
  | .str => .str
  | .null => .null
  | .native f => .native f
  | .fn ps r => .fn (ps.attach.map fun ⟨p, _⟩ => ofTy p) (ofTy r)

end TyV

/-- A substitution: variable bindings. -/
abbrev Subst := List (Nat × TyV)

/-- Follow variable bindings at the head of a type. -/
def walk (σ : Subst) : Nat → TyV → TyV
  | 0, t => t
  | fuel + 1, .var n =>
    match σ.lookup n with
    | some t => walk σ fuel t
    | none => .var n
  | _, t => t

/-- Fully apply a substitution, turning unresolved variables into `int`. -/
def ground (σ : Subst) : Nat → TyV → Ty
  | 0, _ => .int
  | fuel + 1, t =>
    match walk σ (σ.length + 1) t with
    | .var _ => .int
    | .int => .int
    | .bool => .bool
    | .str => .str
    | .null => .null
    | .native f => .native f
    | .fn ps r => .fn (ps.map (ground σ fuel)) (ground σ fuel r)

/-- Does variable `n` occur in `t` under `σ`? -/
def occurs (σ : Subst) (n : Nat) : Nat → TyV → Bool
  | 0, _ => true
  | fuel + 1, t =>
    match walk σ (σ.length + 1) t with
    | .var m => n == m
    | .fn ps r => ps.any (occurs σ n fuel) || occurs σ n fuel r
    | _ => false

/-- Render a type for messages. -/
def TyV.render (σ : Subst) : Nat → TyV → String
  | 0, _ => "…"
  | fuel + 1, t =>
    match walk σ (σ.length + 1) t with
    | .var n => s!"?{n}"
    | .int => "int"
    | .bool => "bool"
    | .str => "str"
    | .null => "null"
    | .native .print => "print"
    | .native .println => "println"
    | .native .assert => "assert"
    | .fn ps r =>
      "fn(" ++ ", ".intercalate (ps.map (TyV.render σ fuel)) ++ ") -> " ++ TyV.render σ fuel r

/-- Render a ground type. -/
def Ty.render : Ty → String
  | .int => "int"
  | .bool => "bool"
  | .str => "str"
  | .null => "null"
  | .native .print => "print"
  | .native .println => "println"
  | .native .assert => "assert"
  | .fn ps r => "fn(" ++ ", ".intercalate (ps.attach.map fun ⟨p, _⟩ => Ty.render p) ++
      ") -> " ++ Ty.render r

/-- Unification; `none` on a clash. -/
def unify (σ : Subst) : Nat → TyV → TyV → Option Subst
  | 0, _, _ => none
  | fuel + 1, a, b =>
    match walk σ (σ.length + 1) a, walk σ (σ.length + 1) b with
    | .var n, .var m => if n == m then some σ else some ((n, .var m) :: σ)
    | .var n, t => if occurs σ n (fuel + 1) t then none else some ((n, t) :: σ)
    | t, .var n => if occurs σ n (fuel + 1) t then none else some ((n, t) :: σ)
    | .int, .int => some σ
    | .bool, .bool => some σ
    | .str, .str => some σ
    | .null, .null => some σ
    | .native f, .native g => if f == g then some σ else none
    | .fn ps r, .fn qs u =>
      if ps.length == qs.length then
        (ps.zip qs).foldl (fun acc (p, q) => acc.bind fun σ' => unify σ' fuel p q)
          (unify σ fuel r u)
      else none
    | _, _ => none

/-- Waiting constraints of overloaded operators and unknown callees. -/
inductive Pending where
  /-- `a + b : c` -/
  | add (a b c : TyV) (ctx : String)
  /-- `a < b` and the other comparisons -/
  | cmp (a b : TyV) (ctx : String)
  /-- a call of a callee of type `f` on arguments `ts` with result `r` -/
  | call (f : TyV) (ts : List TyV) (r : TyV) (ctx : String)

/-- Inference state. -/
structure InferSt where
  σ : Subst := []
  next : Nat := 0
  names : List (String × TyV) :=
    [("print", .native .print), ("println", .native .println), ("assert", .native .assert)]
  pending : List Pending := []

abbrev InferM := StateT InferSt (Except String)

/-- Unification fuel. -/
def fuel : Nat := 100000

def fresh : InferM TyV := do
  let s ← get
  set { s with next := s.next + 1 }
  pure (.var s.next)

/-- The type variable of a program name. -/
def nameTy (x : String) : InferM TyV := do
  match (← get).names.lookup x with
  | some t => pure t
  | none =>
    let t ← fresh
    modify fun s => { s with names := (x, t) :: s.names }
    pure t

def render (t : TyV) : InferM String := do
  pure (t.render (← get).σ 50)

def unifyM (a b : TyV) (ctx : String) : InferM Unit := do
  let s ← get
  match unify s.σ fuel a b with
  | some σ => set { s with σ := σ }
  | none => throw s!"type mismatch in {ctx}: {← render a} vs {← render b}"

def whnfM (t : TyV) : InferM TyV := do
  let s ← get
  pure (walk s.σ (s.σ.length + 1) t)

/-- Resolve a call whose callee type is known. `false` when it must wait. -/
def resolveCall (f : TyV) (ts : List TyV) (r : TyV) (ctx : String) (dflt : Bool) :
    InferM Bool := do
  match ← whnfM f with
  | .native .print | .native .println => unifyM r .null ctx; pure true
  | .native .assert =>
    if ts.length == 1 || ts.length == 2 then unifyM r .null ctx; pure true
    else throw s!"assert takes 1 or 2 arguments in {ctx}"
  | .fn ps u =>
    if ps.length != ts.length then
      throw s!"call with {ts.length} arguments to a function of {ps.length} parameters in {ctx}"
    unifyM (.fn ps u) (.fn ts r) ctx; pure true
  | .var _ =>
    if dflt then unifyM f (.fn ts r) ctx; pure true else pure false
  | t => throw s!"calling a non-function ({← render t}) in {ctx}"

/-- Try to resolve one waiting constraint; with `dflt`, apply the default. -/
def step (c : Pending) (dflt : Bool) : InferM Bool := do
  match c with
  | .add a b r ctx =>
    let a' ← whnfM a
    let b' ← whnfM b
    match a', b' with
    | .str, _ | _, .str => unifyM r .str ctx; pure true
    | .int, .int => unifyM r .int ctx; pure true
    | .var _, .var _ | .int, .var _ | .var _, .int =>
      if dflt then
        unifyM a .int ctx; unifyM b .int ctx; unifyM r .int ctx; pure true
      else pure false
    | _, _ => throw s!"`+` needs integers or a string in {ctx}: {← render a} + {← render b}"
  | .cmp a b ctx =>
    let a' ← whnfM a
    let b' ← whnfM b
    match a', b' with
    | .str, _ | _, .str => unifyM a .str ctx; unifyM b .str ctx; pure true
    | .int, _ | _, .int => unifyM a .int ctx; unifyM b .int ctx; pure true
    | .var _, .var _ =>
      if dflt then unifyM a .int ctx; unifyM b .int ctx; pure true else pure false
    | _, _ =>
      throw s!"comparison needs two integers or two strings in {ctx}: {← render a}, {← render b}"
  | .call f ts r ctx => resolveCall f ts r ctx dflt

/-- Resolve waiting constraints until none is left. -/
def solvePending : Nat → InferM Unit
  | 0 => throw "constraint solving did not terminate"
  | n + 1 => do
    let cs := (← get).pending
    if cs.isEmpty then return
    modify fun s => { s with pending := [] }
    let mut rest : List Pending := []
    let mut progress := false
    for c in cs do
      if ← step c false then progress := true else rest := rest ++ [c]
    match progress, rest with
    | _, [] => pure ()
    | true, _ => modify fun s => { s with pending := rest ++ s.pending }
    | false, c :: cs =>
      discard <| step c true
      modify fun s => { s with pending := cs ++ s.pending }
    solvePending n

/-- Does a statement list contain a `return` outside nested function literals? -/
def hasRet (ss : List Stmt) : Bool := hasRetSyn ss
where
  hasRetSyn : List Stmt → Bool
    | [] => false
    | s :: ss => hasRetS s || hasRetSyn ss
  hasRetS : Stmt → Bool
    | .ret _ => true
    | .block ss => hasRetSyn ss
    | .ifStmt _ t (some e) => hasRetS t || hasRetS e
    | .ifStmt _ t none => hasRetS t
    | .whileStmt _ b => hasRetS b
    | .forStmt (some i) _ _ b => hasRetS i || hasRetS b
    | .forStmt none _ _ b => hasRetS b
    | _ => false

/-- The operator's source spelling. -/
def BinOp.sym : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="

/-- Context of the statements being inferred. -/
structure Ctx where
  /-- names bound here -/
  S : List String
  /-- return type of the enclosing function, `none` at the top level -/
  R : Option TyV
  /-- inside a loop -/
  L : Bool
  /-- enclosing function, for messages -/
  where_ : String

mutual

def inferE (c : Ctx) : Expr → InferM TyV
  | .int _ => pure .int
  | .str _ => pure .str
  | .bool _ => pure .bool
  | .null => pure .null
  | .var x => do
    unless x ∈ c.S do throw s!"undefined variable `{x}` in {c.where_}"
    nameTy x
  | .assign x e => do
    unless x ∈ c.S do throw s!"assignment to undefined variable `{x}` in {c.where_}"
    let t ← inferE c e
    let tx ← nameTy x
    unifyM t tx s!"assignment to `{x}` in {c.where_}"
    pure tx
  | .binary op l r => do
    let tl ← inferE c l
    let tr ← inferE c r
    let ctx := s!"`{BinOp.sym op}` in {c.where_}"
    match op with
    | .add =>
      let t ← fresh
      modify fun s => { s with pending := s.pending ++ [.add tl tr t ctx] }
      pure t
    | .sub | .mul | .div | .mod =>
      unifyM tl .int ctx; unifyM tr .int ctx; pure .int
    | .eq | .ne => pure .bool
    | .lt | .le | .gt | .ge =>
      modify fun s => { s with pending := s.pending ++ [.cmp tl tr ctx] }
      pure .bool
  | .logical _ l r => do
    discard <| inferE c l
    discard <| inferE c r
    pure .bool
  | .unary .neg e => do
    let t ← inferE c e
    unifyM t .int s!"negation in {c.where_}"
    pure .int
  | .unary .not e => do
    discard <| inferE c e
    pure .bool
  | .call f args => do
    if args.length > maxArgs then throw s!"more than {maxArgs} arguments in {c.where_}"
    let tf ← inferE c f
    let ts ← inferArgs c args
    let r ← fresh
    let ctx := s!"a call in {c.where_}"
    unless ← resolveCall tf ts r ctx false do
      modify fun s => { s with pending := s.pending ++ [.call tf ts r ctx] }
    pure r
  | .fn name params body => do
    let ps ← params.mapM nameTy
    let r ← fresh
    let c' : Ctx := { S := params ++ c.S, R := some r, L := false,
                      where_ := s!"function `{name.getD "<anonymous>"}`" }
    discard <| inferSeq c' body
    unless hasRet body && mustExitSeqB body do
      unifyM r .null s!"{c'.where_}, whose body can finish without `return` (so it returns null)"
    pure (.fn ps r)

def inferArgs (c : Ctx) : List Expr → InferM (List TyV)
  | [] => pure []
  | e :: es => do
    let t ← inferE c e
    let ts ← inferArgs c es
    pure (t :: ts)

/-- Infer a statement; returns the names bound afterwards. -/
def inferS (c : Ctx) : Stmt → InferM (List String)
  | .expr e => do discard <| inferE c e; pure c.S
  | .varDecl x none => do
    unifyM (← nameTy x) .null s!"`var {x};` in {c.where_}"
    pure (x :: c.S)
  | .varDecl x (some e) => do
    -- a function literal may refer to itself
    let c' := match e with
      | .fn .. => { c with S := x :: c.S }
      | _ => c
    let t ← inferE c' e
    unifyM t (← nameTy x) s!"declaration of `{x}` in {c.where_}"
    pure (x :: c.S)
  | .block ss => do discard <| inferSeq c ss; pure c.S
  | .ifStmt cnd t e => do
    discard <| inferE c cnd
    discard <| inferS c t
    match e with
    | some e => discard <| inferS c e
    | none => pure ()
    pure c.S
  | .whileStmt cnd b => do
    discard <| inferE c cnd
    discard <| inferS { c with L := true } b
    pure c.S
  | .forStmt init cnd step b => do
    let S₁ ← match init with
      | some i => inferS c i
      | none => pure c.S
    let c₁ := { c with S := S₁ }
    if let some e := cnd then discard <| inferE c₁ e
    if let some e := step then discard <| inferE c₁ e
    discard <| inferS { c₁ with L := true } b
    pure c.S
  | .ret e => do
    let some r := c.R | throw "`return` outside a function"
    let t ← match e with
      | some e => inferE c e
      | none => pure .null
    unifyM t r s!"return value in {c.where_}"
    pure c.S
  | .brk => do
    unless c.L do throw s!"`break` outside a loop in {c.where_}"
    pure c.S
  | .cont => do
    unless c.L do throw s!"`continue` outside a loop in {c.where_}"
    pure c.S

def inferSeq (c : Ctx) : List Stmt → InferM (List String)
  | [] => pure c.S
  | s :: ss => do
    let S₁ ← inferS c s
    inferSeq { c with S := S₁ } ss

end

/-- The diagnostic solver's name table. -/
def solve (p : Program) : Except String (List (String × Ty)) := do
  let go : InferM (List (String × Ty)) := do
    discard <| inferSeq { S := builtinNames, R := none, L := false, where_ := "the program" } p
    solvePending 10000
    let s ← get
    pure ((s.names.filter fun (x, _) => x ∉ builtinNames).reverse.map fun (x, t) =>
      (x, ground s.σ 1000 t))
  (·.1) <$> go.run {}

/-- The first problem the diagnostic solver finds. -/
def message (p : Program) : String :=
  match solve p with
  | .error e => e
  | .ok _ => "no typing environment exists"

end Diag

/-! ## Inference -/

/-- **Type inference.** -/
def infer (p : Program) : Except String TyEnv :=
  match searchProg p with
  | some s => if typeCheck (envOfSubst s.σ) p then .ok (envOfSubst s.σ) else .error (Diag.message p)
  | none => .error (Diag.message p)

/-- **Inference is sound.** -/
theorem infer_sound {p : Program} {Δ : TyEnv} (h : infer p = .ok Δ) : WellTyped Δ p := by
  unfold infer at h
  split at h
  · split at h
    · rename_i hc; cases h; exact typeCheck_iff.mp hc
    · cases h
  · cases h

/-- **Inference is complete.** -/
theorem infer_complete {p : Program} {Δ : TyEnv} (h : WellTyped Δ p) :
    ∃ Δ', infer p = .ok Δ' := by
  obtain ⟨s, hs⟩ := search_complete h
  have hc := typeCheck_iff.mpr (search_sound h hs)
  exact ⟨envOfSubst s.σ, by simp [infer, hs, hc]⟩

/-- A program is typable when some typing environment types it. -/
def Typable (p : Program) : Prop := ∃ Δ, WellTyped Δ p

/-- **The WHILE type checker.** -/
def whileTyped (p : Program) : Bool :=
  match infer p with
  | .ok _ => true
  | .error _ => false

/-- **The type checker decides typability.** -/
theorem whileTyped_iff {p : Program} : whileTyped p = true ↔ Typable p := by
  constructor
  · intro h
    unfold whileTyped at h
    split at h
    · rename_i Δ hΔ; exact ⟨Δ, infer_sound hΔ⟩
    · cases h
  · rintro ⟨Δ, h⟩
    obtain ⟨Δ', hΔ'⟩ := infer_complete h
    simp [whileTyped, hΔ']

instance (p : Program) : Decidable (Typable p) := decidable_of_iff _ whileTyped_iff

/-- The names a program declares, in order of first declaration. -/
def programNames (p : Program) : List String :=
  (go p).foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []
where
  go : List Stmt → List String
    | [] => []
    | s :: ss => goS s ++ go ss
  goS : Stmt → List String
    | .expr e => goE e
    | .varDecl x none => [x]
    | .varDecl x (some e) => x :: goE e
    | .block ss => go ss
    | .ifStmt c t (some e) => goE c ++ goS t ++ goS e
    | .ifStmt c t none => goE c ++ goS t
    | .whileStmt c b => goE c ++ goS b
    | .forStmt (some i) _ _ b => goS i ++ goS b
    | .forStmt none _ _ b => goS b
    | .ret (some e) => goE e
    | _ => []
  goE : Expr → List String
    | .assign _ e => goE e
    | .binary _ l r => goE l ++ goE r
    | .logical _ l r => goE l ++ goE r
    | .unary _ e => goE e
    | .call f args => goE f ++ goArgs args
    | .fn _ params body => params ++ go body
    | _ => []
  goArgs : List Expr → List String
    | [] => []
    | e :: es => goE e ++ goArgs es

end Vsa.While.Types
