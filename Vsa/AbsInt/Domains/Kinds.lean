import Vsa.AbsInt.Domain

/-!
# The value-kind domain

A finite set of value kinds: `null`, `bool`, `int`, `str`, `closure`, and
each of the three natives. It proves the absence of type errors, call
errors on natives, and unbound variables (with the state layer); it cannot
exclude division by zero.
-/

namespace Vsa.AbsInt

open Vsa.While

/-- A set of value kinds. -/
structure KSet where
  null : Bool := false
  bool : Bool := false
  int : Bool := false
  str : Bool := false
  clo : Bool := false
  prn : Bool := false
  pln : Bool := false
  ast : Bool := false
  deriving DecidableEq, Repr

namespace KSet

/-- Every kind. -/
def all : KSet := ⟨true, true, true, true, true, true, true, true⟩

/-- Membership of a value. -/
def Mem (a : KSet) : Value → Prop
  | .null => a.null = true
  | .bool _ => a.bool = true
  | .int _ => a.int = true
  | .str _ => a.str = true
  | .closure _ => a.clo = true
  | .native .print => a.prn = true
  | .native .println => a.pln = true
  | .native .assert => a.ast = true

/-- The kind of one value. -/
def of : Value → KSet
  | .null => { null := true }
  | .bool _ => { bool := true }
  | .int _ => { int := true }
  | .str _ => { str := true }
  | .closure _ => { clo := true }
  | .native .print => { prn := true }
  | .native .println => { pln := true }
  | .native .assert => { ast := true }

def join (a b : KSet) : KSet :=
  ⟨a.null || b.null, a.bool || b.bool, a.int || b.int, a.str || b.str,
    a.clo || b.clo, a.prn || b.prn, a.pln || b.pln, a.ast || b.ast⟩

def le (a b : KSet) : Bool :=
  (!a.null || b.null) && (!a.bool || b.bool) && (!a.int || b.int) &&
    (!a.str || b.str) && (!a.clo || b.clo) && (!a.prn || b.prn) &&
    (!a.pln || b.pln) && (!a.ast || b.ast)

/-- Some kind other than `int`. -/
def nonInt (a : KSet) : Bool :=
  a.null || a.bool || a.str || a.clo || a.prn || a.pln || a.ast

/-- Some kind other than `str`. -/
def nonStr (a : KSet) : Bool :=
  a.null || a.bool || a.int || a.clo || a.prn || a.pln || a.ast

/-- Some kind other than `int` and `str`. -/
def nsi (a : KSet) : Bool :=
  a.null || a.bool || a.clo || a.prn || a.pln || a.ast

def binop : BinOp → KSet → KSet → KSet
  | .add, a, b => { str := a.str || b.str, int := a.int && b.int }
  | .sub, _, _ | .mul, _, _ | .div, _, _ | .mod, _, _ => { int := true }
  | _, _, _ => { bool := true }

/-- Only integers, or only strings, on both sides. -/
def cmpSafe (a b : KSet) : Bool :=
  (!a.nonInt && !b.nonInt) || (!a.nonStr && !b.nonStr)

def binErr : BinOp → KSet → KSet → List Kind
  | .add, a, b => if a.nonStr && b.nonStr && (a.nsi || b.nsi) then [.type] else []
  | .sub, a, b | .mul, a, b => if a.nonInt || b.nonInt then [.type] else []
  | .div, a, b | .mod, a, b =>
    (if a.nonInt || b.nonInt then [.type] else []) ++
      (if a.int && b.int then [.divZero] else [])
  | .eq, _, _ | .ne, _, _ => []
  | _, a, b => if cmpSafe a b then [] else [.type]

def mayT (a : KSet) : Bool := a.bool || a.int || a.str || a.clo || a.prn || a.pln || a.ast

def mayF (a : KSet) : Bool := a.null || a.bool || a.int

def asNative (a : KSet) : Option NativeFn :=
  if a = { prn := true } then some .print
  else if a = { pln := true } then some .println
  else if a = { ast := true } then some .assert
  else none

theorem mem_of (v : Value) : Mem (of v) v := by
  cases v with
  | native f => cases f <;> rfl
  | _ => rfl

theorem mem_join_l {a b : KSet} {v : Value} (h : Mem a v) : Mem (join a b) v := by
  cases v with
  | native f => cases f <;> simp_all [Mem, join]
  | _ => simp_all [Mem, join]

theorem mem_join_r {a b : KSet} {v : Value} (h : Mem b v) : Mem (join a b) v := by
  cases v with
  | native f => cases f <;> simp_all [Mem, join]
  | _ => simp_all [Mem, join]

theorem mem_le {a b : KSet} {v : Value} (hle : le a b = true) (h : Mem a v) : Mem b v := by
  simp only [le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    at hle
  cases v with
  | native f => cases f <;> simp_all [Mem]
  | _ => simp_all [Mem]

theorem binop_sound {s : Store} {op : BinOp} {l r v : Value} {a b : KSet}
    (h : binOpSem s op l r = some v) (hl : Mem a l) (hr : Mem b r) :
    Mem (binop op a b) v := by
  cases op <;> cases l <;> cases r <;> simp [binOpSem] at h <;>
    (try split at h) <;> (try simp at h) <;> (try subst h) <;>
    (try simp_all [Mem, binop]) <;> (obtain ⟨_, rfl⟩ := h; trivial)

theorem binErr_sound {s : Store} {op : BinOp} {l r : Value} {a b : KSet}
    (h : binOpSem s op l r = none) (hl : Mem a l) (hr : Mem b r) :
    binFailKind op l r ∈ binErr op a b := by
  rcases l with _ | _ | _ | _ | _ | (_ | _ | _) <;>
    rcases r with _ | _ | _ | _ | _ | (_ | _ | _) <;>
    cases op <;> simp [binOpSem] at h <;>
    simp_all [binErr, binFailKind, Mem, nonInt, nonStr, nsi, cmpSafe]

theorem mayT_sound {a : KSet} {v : Value} (h : Mem a v) (ht : v.truthy = true) :
    mayT a = true := by
  cases v with
  | native f => cases f <;> simp_all [Mem, mayT]
  | _ => simp_all [Mem, mayT, Value.truthy]

theorem mayF_sound {a : KSet} {v : Value} (h : Mem a v) (ht : v.truthy = false) :
    mayF a = true := by
  cases v with
  | native f => cases f <;> simp_all [Mem, mayF, Value.truthy]
  | _ => simp_all [Mem, mayF, Value.truthy]

theorem asNative_sound {a : KSet} {v : Value} {f : NativeFn} (h : Mem a v)
    (hn : asNative a = some f) : v = .native f := by
  unfold asNative at hn
  split at hn
  · rename_i ha; subst ha; cases hn
    cases v with
    | native g => cases g <;> simp_all [Mem]
    | _ => simp_all [Mem]
  split at hn
  · rename_i _ ha; subst ha; cases hn
    cases v with
    | native g => cases g <;> simp_all [Mem]
    | _ => simp_all [Mem]
  split at hn
  · rename_i _ _ ha; subst ha; cases hn
    cases v with
    | native g => cases g <;> simp_all [Mem]
    | _ => simp_all [Mem]
  cases hn

end KSet

instance : AbsDom KSet where
  top := KSet.all
  le := KSet.le
  join := KSet.join
  widen := KSet.join
  Gam := KSet.Mem
  ofValue := KSet.of
  closure := { clo := true }
  binop := KSet.binop
  neg _ := { int := true }
  mayT := KSet.mayT
  mayF := KSet.mayF
  binErr := KSet.binErr
  negErr a := a.nonInt
  asNative := KSet.asNative
  refine _ _ a _ := a
  isBot a := a = {}
  le_sound := KSet.mem_le
  join_l := KSet.mem_join_l
  join_r := KSet.mem_join_r
  widen_l := KSet.mem_join_l
  widen_r := KSet.mem_join_r
  top_sound := by
    intro v
    cases v with
    | native f => cases f <;> rfl
    | _ => rfl
  ofValue_sound := KSet.mem_of
  closure_sound _ := rfl
  binop_sound := KSet.binop_sound
  neg_sound _ := rfl
  mayT_sound := KSet.mayT_sound
  mayF_sound := KSet.mayF_sound
  binErr_sound := KSet.binErr_sound
  negErr_sound := by
    intro a v h hv
    cases v with
    | int n => exact absurd rfl (hv n)
    | native f => cases f <;> simp_all [KSet.Mem, KSet.nonInt]
    | _ => simp_all [KSet.Mem, KSet.nonInt]
  asNative_sound := KSet.asNative_sound
  refine_sound h _ _ _ := h
  isBot_sound := by
    intro a v ha hv
    simp only [decide_eq_true_eq] at ha
    subst ha
    cases v with
    | native f => cases f <;> simp [KSet.Mem] at hv
    | _ => simp [KSet.Mem] at hv

end Vsa.AbsInt
