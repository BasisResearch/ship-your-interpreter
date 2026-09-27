import Vsa.While.Semantics

/-!
# Abstract domains for WHILE values

`AbsDom A` is the interface every value domain implements: a join
semi-lattice with `⊑` (`le`), `⊔` (`join`), `⊤`, a widening `∇`, a
concretisation `Gam : A → Value → Prop`, and the transfer functions the
generic abstract interpreter (`Vsa/AbsInt/Interp.lean`) consults. Each
operation carries its soundness law against the concrete semantics
(`binOpSem`, `wrap64`, `Value.truthy`) of `Vsa/While/Semantics.lean`.

Domains need no bottom element: unreachable program points are
represented at the state level (`AState.bot`).

Runtime-error verdicts are reported as `Kind`s. `binFailKind` classifies a
`binOpSem = none` failure as a division by zero or a type error.
-/

namespace Vsa.AbsInt

open Vsa.While

/-- Classes of runtime error the analysis reports. -/
inductive Kind where
  /-- `env_get`/`env_set` miss. -/
  | unbound
  /-- operator applied to values of the wrong kind. -/
  | type
  /-- `/` or `%` by zero. -/
  | divZero
  /-- a call that fails: not callable, arity, depth, argument buffer,
  closure-body escape. -/
  | call
  /-- `assert` with a falsy argument or wrong arity. -/
  | assert
  /-- a top-level `return`/`break`/`continue`. -/
  | abrupt
  deriving DecidableEq, Repr

/-- Union of alarm lists without duplicates. -/
def Kind.union (l m : List Kind) : List Kind :=
  l.foldr (fun k acc => if k ∈ acc then acc else k :: acc) m

instance : Union (List Kind) := ⟨Kind.union⟩

theorem Kind.mem_union {k : Kind} {l m : List Kind} : k ∈ l ∪ m ↔ k ∈ l ∨ k ∈ m := by
  show k ∈ Kind.union l m ↔ _
  induction l with
  | nil => simp [Kind.union]
  | cons j l ih =>
    simp only [Kind.union, List.foldr_cons] at ih ⊢
    split
    · rename_i h
      rw [ih]
      constructor
      · rintro (h' | h')
        · exact Or.inl (List.mem_cons_of_mem j h')
        · exact Or.inr h'
      · rintro (h' | h')
        · rcases List.mem_cons.mp h' with rfl | h'
          · exact ih.mp h
          · exact Or.inl h'
        · exact Or.inr h'
    · rw [List.mem_cons, ih, List.mem_cons]
      exact or_assoc.symm

/-- All kinds except `abrupt` (what an unanalysed closure body may raise). -/
def Kind.inCall : List Kind := [.unbound, .type, .divZero, .call, .assert]

/-- The kind of a `binOpSem … = none` failure. -/
def binFailKind : BinOp → Value → Value → Kind
  | .div, .int _, .int 0 => .divZero
  | .mod, .int _, .int 0 => .divZero
  | _, _, _ => .type

/-- A value domain with its concretisation and sound transfer functions. -/
class AbsDom (A : Type) where
  top : A
  le : A → A → Bool
  join : A → A → A
  widen : A → A → A
  Gam : A → Value → Prop
  /-- Abstraction of one concrete value (literals, natives, `null`). -/
  ofValue : Value → A
  /-- Abstraction of every closure value. -/
  closure : A
  binop : BinOp → A → A → A
  neg : A → A
  /-- May a value of `a` be truthy / falsy? -/
  mayT : A → Bool
  mayF : A → Bool
  /-- Kinds of failure `binOpSem op` may raise on `a`, `b`. -/
  binErr : BinOp → A → A → List Kind
  /-- May unary `-` fail (non-integer operand)? -/
  negErr : A → Bool
  /-- `some f`: every value of `a` is the native `f`. -/
  asNative : A → Option NativeFn
  /-- Refine the left operand `a` knowing `(l op r).truthy = t` for `r ∈ b`. -/
  refine : BinOp → Bool → A → A → A
  /-- `true` only for an empty abstract value. -/
  isBot : A → Bool
  le_sound : ∀ {a b v}, le a b = true → Gam a v → Gam b v
  join_l : ∀ {a b v}, Gam a v → Gam (join a b) v
  join_r : ∀ {a b v}, Gam b v → Gam (join a b) v
  widen_l : ∀ {a b v}, Gam a v → Gam (widen a b) v
  widen_r : ∀ {a b v}, Gam b v → Gam (widen a b) v
  top_sound : ∀ {v}, Gam top v
  ofValue_sound : ∀ v, Gam (ofValue v) v
  closure_sound : ∀ a, Gam closure (.closure a)
  binop_sound : ∀ {s op l r v a b}, binOpSem s op l r = some v →
    Gam a l → Gam b r → Gam (binop op a b) v
  neg_sound : ∀ {a n}, Gam a (.int n) → Gam (neg a) (.int (wrap64 (-n)))
  mayT_sound : ∀ {a v}, Gam a v → v.truthy = true → mayT a = true
  mayF_sound : ∀ {a v}, Gam a v → v.truthy = false → mayF a = true
  binErr_sound : ∀ {s op l r a b}, binOpSem s op l r = none →
    Gam a l → Gam b r → binFailKind op l r ∈ binErr op a b
  negErr_sound : ∀ {a v}, Gam a v → (∀ n, v ≠ .int n) → negErr a = true
  asNative_sound : ∀ {a v f}, Gam a v → asNative a = some f → v = .native f
  refine_sound : ∀ {s op t l r w a b}, Gam a l → Gam b r →
    binOpSem s op l r = some w → w.truthy = t → Gam (refine op t a b) l
  isBot_sound : ∀ {a v}, isBot a = true → ¬ Gam a v

namespace AbsDom

variable {A : Type} [AbsDom A]

/-- Abstraction of `.bool b` for the truth values `b` that may occur. -/
def boolOf (canT canF : Bool) : A :=
  if canT then
    if canF then join (ofValue (.bool true)) (ofValue (.bool false))
    else ofValue (.bool true)
  else ofValue (.bool false)

theorem boolOf_sound {canT canF : Bool} {b : Bool}
    (hT : b = true → canT = true) (hF : b = false → canF = true) :
    Gam (boolOf (A := A) canT canF) (.bool b) := by
  unfold boolOf
  cases b
  · have := hF rfl
    subst this
    split
    · exact join_r (ofValue_sound _)
    · exact ofValue_sound _
  · have := hT rfl
    subst this
    simp only [↓reduceIte]
    split
    · exact join_l (ofValue_sound _)
    · exact ofValue_sound _

/-- Abstraction of the truthiness bit of a value of `a`. -/
def truthOf (a : A) : A := boolOf (mayT a) (mayF a)

theorem truthOf_sound {a : A} {v : Value} (h : Gam a v) :
    Gam (truthOf a) (.bool v.truthy) :=
  boolOf_sound (fun hv => mayT_sound h hv) (fun hv => mayF_sound h hv)

/-- Abstraction of the negated truthiness bit (`!v.truthy`). -/
def notOf (a : A) : A := boolOf (mayF a) (mayT a)

theorem notOf_sound {a : A} {v : Value} (h : Gam a v) :
    Gam (notOf a) (.bool (!v.truthy)) :=
  boolOf_sound (fun hv => mayF_sound h (by simpa using hv))
    (fun hv => mayT_sound h (by simpa using hv))

end AbsDom

end Vsa.AbsInt
