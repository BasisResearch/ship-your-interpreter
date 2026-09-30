import Vsa.Compiler.StuckStmt

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

omit hR in
theorem EStuck.of_has {n : Nat} {st : St} {d : Nat} {env : Addr} {e : Expr} (h : HasE st d env e) :
    EStuck code T n st d env e :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hne => absurd h hne

omit hR in
theorem SStuck.of_has {n : Nat} {st : St} {d : Nat} {env : Addr} {s : Stmt} (h : HasS st d env s) :
    SStuck code T n st d env s :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hne => absurd h hne

theorem noC {n : Nat} (IHn : ∀ m < n, StuckAt code T m) (st : St) (d : Nat) (fv : Value) (vs : List Value) :
    CStuck code T n st d fv vs := by
  cases fv with
  | closure a => exact fClosure hR (fun m hm => (IHn m hm).q)
  | native f =>
    cases f with
    | print => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne => absurd ⟨_, _, .print _ _ _⟩ hne
    | println => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne => absurd ⟨_, _, .println _ _ _⟩ hne
    | assert => exact fAssert hR
  | null => exact fNotCallable hR (fun _ h => by cases h) (fun _ h => by cases h)
  | bool _ => exact fNotCallable hR (fun _ h => by cases h) (fun _ h => by cases h)
  | int _ => exact fNotCallable hR (fun _ h => by cases h) (fun _ h => by cases h)
  | str _ => exact fNotCallable hR (fun _ h => by cases h) (fun _ h => by cases h)

mutual

theorem noE (n : Nat) (IHn : ∀ m < n, StuckAt code T m) :
    ∀ (e : Expr) (st : St) (d : Nat) (env : Addr), EStuck code T n st d env e
  | .int _, _, _, _ => EStuck.of_has ⟨_, _, .int _ _ _ _⟩
  | .str _, _, _, _ => EStuck.of_has ⟨_, _, .str _ _ _ _⟩
  | .bool _, _, _, _ => EStuck.of_has ⟨_, _, .bool _ _ _ _⟩
  | .null, _, _, _ => EStuck.of_has ⟨_, _, .null _ _ _⟩
  | .fn _ _ _, _, _, _ => EStuck.of_has ⟨_, _, .fn _ _ _ _ _ _ _ _ rfl⟩
  | .var x, _, _, _ => fVar hR x
  | .assign _ e, _, d, env => fAssign hR (fun st => noE n IHn e st d env)
  | .binary _ l r, _, d, env => fBinary hR (fun st => noE n IHn l st d env) (fun st => noE n IHn r st d env)
  | .logical _ l r, _, d, env => fLogical hR (fun st => noE n IHn l st d env) (fun st => noE n IHn r st d env)
  | .unary .neg e, _, d, env => fNeg hR (fun st => noE n IHn e st d env)
  | .unary .not e, _, d, env => fNot hR (fun st => noE n IHn e st d env)
  | .call f args, _, d, env =>
    fCall hR (fun st => noE n IHn f st d env) (fun st => noA n IHn args st d env) (fun st => noC hR IHn st d)

theorem noA (n : Nat) (IHn : ∀ m < n, StuckAt code T m) :
    ∀ (es : List Expr) (st : St) (d : Nat) (env : Addr), AStuck code T n st d env es
  | [], _, _, _ => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne => absurd ⟨_, _, .nil _ _ _⟩ hne
  | e :: es, _, d, env => fArgs hR (fun st => noE n IHn e st d env) (fun st => noA n IHn es st d env)

theorem noS (n : Nat) (IHn : ∀ m < n, StuckAt code T m) :
    ∀ (s : Stmt) (st : St) (d : Nat) (env : Addr), SStuck code T n st d env s
  | .expr e, st, d, env => fExprS (noE n IHn e st d env)
  | .varDecl _ (some e), st, d, env => fVarInit (noE n IHn e st d env)
  | .varDecl _ none, _, _, _ => SStuck.of_has ⟨_, _, .varNull _ _ _ _⟩
  | .block ss, _, d, _ => fBlockS hR (fun st env => noQ n IHn ss st d env)
  | .ifStmt c t none, _, d, env =>
    fIfNone hR (fun st => noE n IHn c st d env) (fun st => noS n IHn t st d env)
  | .ifStmt c t (some e), _, d, env =>
    fIfSome hR (fun st => noE n IHn c st d env) (fun st => noS n IHn t st d env) (fun st => noS n IHn e st d env)
  | .whileStmt c b, _, d, env =>
    fWhile hR (fun st => noE n IHn c st d env) (fun st => noS n IHn b st d env)
      (fun m hm st => (IHn m hm).s st d env _)
  | .forStmt init cnd step b, _, d, _ =>
    fFor hR (noInit n IHn init d) (fun st env => fFL hR (noCnd n IHn cnd d env) (fun st => noS n IHn b st d env)
      (noCnd n IHn step d env) (fun m hm st => (IHn m hm).fl st d env cnd step b))
  | .ret (some e), st, d, env => fRet (noE n IHn e st d env)
  | .ret none, _, _, _ => SStuck.of_has ⟨_, _, .retNull _ _ _⟩
  | .brk, _, _, _ => SStuck.of_has ⟨_, _, .brk _ _ _⟩
  | .cont, _, _, _ => SStuck.of_has ⟨_, _, .cont _ _ _⟩

theorem noInit (n : Nat) (IHn : ∀ m < n, StuckAt code T m) :
    ∀ (init : Option Stmt) (d : Nat), ∀ s, init = some s → ∀ st env, SStuck code T n st d env s
  | none, _ => fun _ h => by cases h
  | some s, d => fun _ h st env => by cases h; exact noS n IHn s st d env

theorem noCnd (n : Nat) (IHn : ∀ m < n, StuckAt code T m) :
    ∀ (c : Option Expr) (d : Nat) (env : Addr), ∀ e, c = some e → ∀ st, EStuck code T n st d env e
  | none, _, _ => fun _ h => by cases h
  | some e, d, env => fun _ h st => by cases h; exact noE n IHn e st d env

theorem noQ (n : Nat) (IHn : ∀ m < n, StuckAt code T m) :
    ∀ (ss : List Stmt) (st : St) (d : Nat) (env : Addr), QStuck code T n st d env ss
  | [], _, _, _ => fNil
  | s :: ss, _, d, env => fCons hR (fun st => noS n IHn s st d env) (fun st => noQ n IHn ss st d env)

end

theorem stuck_all : ∀ n, StuckAt code T n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    exact {
      e := fun st d env e => noE hR n IHn e st d env
      a := fun st d env es => noA hR n IHn es st d env
      c := noC hR IHn
      s := fun st d env s => noS hR n IHn s st d env
      q := fun st d env ss => noQ hR n IHn ss st d env
      fl := fun st d env cnd step b => fFL hR (noCnd hR n IHn cnd d env) (fun st => noS hR n IHn b st d env)
        (noCnd hR n IHn step d env) (fun m hm st => (IHn m hm).fl st d env cnd step b) }

end

end Vsa.Compiler
