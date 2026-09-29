import Vsa.AbsInt.Domain

/-!
# The sign domain

A set of integer signs (`neg`, `zero`, `pos`) plus a flag for non-integer
values. Arithmetic is 64-bit wrapped, so a sum or product of nonzero
operands may take any sign; the domain tracks the cases that survive
wrapping (zero operands). It decides truthiness of integers and excludes
division by zero when the divisor cannot be zero.
-/

namespace Vsa.AbsInt

open Vsa.While

/-- Sets of signs, plus non-integer values. -/
structure Sign where
  neg : Bool := false
  zero : Bool := false
  pos : Bool := false
  other : Bool := false
  deriving DecidableEq, Repr

namespace Sign

/-- The sign of `n` is in `a`. -/
def hasInt (a : Sign) (n : Int) : Bool :=
  if n < 0 then a.neg else if n = 0 then a.zero else a.pos

def Gam (a : Sign) : Value → Prop
  | .int n => hasInt a n = true
  | _ => a.other = true

def all : Sign := ⟨true, true, true, true⟩
def allInt : Sign := { neg := true, zero := true, pos := true }
def zeroS : Sign := { zero := true }

def le (a b : Sign) : Bool :=
  (!a.neg || b.neg) && (!a.zero || b.zero) && (!a.pos || b.pos) && (!a.other || b.other)

def join (a b : Sign) : Sign :=
  ⟨a.neg || b.neg, a.zero || b.zero, a.pos || b.pos, a.other || b.other⟩

def of : Value → Sign
  | .int n => if n < 0 then { neg := true } else if n = 0 then zeroS else { pos := true }
  | _ => { other := true }

def ints (a : Sign) : Bool := a.neg || a.zero || a.pos

/-- Every integer of `a` is zero. -/
def zeroOnly (a : Sign) : Bool := !a.neg && !a.pos

theorem eq_zero {a : Sign} {n : Int} (hz : zeroOnly a = true) (h : hasInt a n = true) :
    n = 0 := by
  simp only [zeroOnly, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hz
  unfold hasInt at h
  split at h
  · simp_all
  · split at h
    · assumption
    · simp_all

theorem ints_of {a : Sign} {n : Int} (h : hasInt a n = true) : ints a = true := by
  unfold hasInt at h
  unfold ints
  split at h <;> (try split at h) <;> simp_all

/-- The integer part of an arithmetic result. -/
def arith (ok zero : Bool) : Sign :=
  if ok then (if zero then zeroS else allInt) else {}

def binop (op : BinOp) (a b : Sign) : Sign :=
  match op with
  | .add => { arith (ints a && ints b) (zeroOnly a && zeroOnly b) with
      other := a.other || b.other }
  | .sub => arith (ints a && ints b) (zeroOnly a && zeroOnly b)
  | .mul => arith (ints a && ints b) (zeroOnly a || zeroOnly b)
  | .div | .mod => arith (ints a && ints b) (zeroOnly a)
  | _ => { other := true }

def negS (a : Sign) : Sign := arith (ints a) (zeroOnly a)

def mayT (a : Sign) : Bool := a.neg || a.pos || a.other
def mayF (a : Sign) : Bool := a.zero || a.other

def binErr (op : BinOp) (a b : Sign) : List Kind :=
  match op with
  | .eq | .ne => []
  | .div | .mod =>
    (if a.other || b.other then [.type] else []) ∪
      (if ints a && b.zero then [.divZero] else [])
  | _ => if a.other || b.other then [.type] else []

theorem gam_allInt (n : Int) : hasInt allInt n = true := by
  unfold hasInt allInt
  split <;> (try split) <;> rfl

theorem gam_arith {ok zero : Bool} {n : Int} (hok : ok = true) (hz : zero = true → n = 0) :
    hasInt (arith ok zero) n = true := by
  subst hok
  unfold arith
  cases zero
  · exact gam_allInt n
  · rw [hz rfl]
    rfl

theorem gam_arith_with {ok zero o : Bool} {n : Int} (hok : ok = true)
    (hz : zero = true → n = 0) : hasInt { arith ok zero with other := o } n = true := by
  have := gam_arith (n := n) hok hz
  unfold hasInt at this ⊢
  exact this

theorem gam_le {a b : Sign} {v : Value} (hle : le a b = true) (h : Gam a v) : Gam b v := by
  simp only [le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hle
  cases v with
  | int n =>
    simp only [Gam, hasInt] at h ⊢
    split at h <;> (try split at h) <;> simp_all
  | _ => simp_all [Gam]

theorem gam_join_l {a b : Sign} {v : Value} (h : Gam a v) : Gam (join a b) v := by
  cases v with
  | int n =>
    simp only [Gam, hasInt, join] at h ⊢
    split at h <;> (try split at h) <;> simp_all
  | _ => simp_all [Gam, join]

theorem gam_join_r {a b : Sign} {v : Value} (h : Gam b v) : Gam (join a b) v := by
  cases v with
  | int n =>
    simp only [Gam, hasInt, join] at h ⊢
    split at h <;> (try split at h) <;> simp_all
  | _ => simp_all [Gam, join]

theorem gam_of (v : Value) : Gam (of v) v := by
  cases v with
  | int n =>
    simp only [Gam, of, hasInt]
    by_cases h1 : n < 0
    · simp [h1]
    · by_cases h2 : n = 0
      · simp [h2, zeroS]
      · simp [h1, h2]
  | _ => rfl

theorem gam_binop {s : Store} {op : BinOp} {l r v : Value} {a b : Sign}
    (h : binOpSem s op l r = some v) (hl : Gam a l) (hr : Gam b r) :
    Gam (binop op a b) v := by
  rcases l with _ | _ | n | _ | _ | _ <;> rcases r with _ | _ | m | _ | _ | _ <;>
    cases op <;> simp [binOpSem] at h <;> simp only [Gam] at hl hr
  all_goals first
    | (subst h; simp [Gam, binop, hl, hr]; done)
    | (subst h
       exact gam_arith_with (by simp [ints_of hl, ints_of hr])
         (fun hz => by
           simp only [Bool.and_eq_true] at hz
           rw [eq_zero hz.1 hl, eq_zero hz.2 hr]; decide))
    | (subst h
       exact gam_arith (by simp [ints_of hl, ints_of hr])
         (fun hz => by
           simp only [Bool.and_eq_true] at hz
           rw [eq_zero hz.1 hl, eq_zero hz.2 hr]; decide))
    | (subst h
       exact gam_arith (by simp [ints_of hl, ints_of hr])
         (fun hz => by
           simp only [Bool.or_eq_true] at hz
           rcases hz with hz | hz
           · rw [eq_zero hz hl, Int.zero_mul]; decide
           · rw [eq_zero hz hr, Int.mul_zero]; decide))
    | (obtain ⟨_, rfl⟩ := h
       exact gam_arith (by simp [ints_of hl, ints_of hr])
         (fun hz => by rw [eq_zero hz hl, Int.zero_tdiv]; decide))
    | (obtain ⟨_, rfl⟩ := h
       exact gam_arith (by simp [ints_of hl, ints_of hr])
         (fun hz => by rw [eq_zero hz hl, Int.zero_tmod]; decide))

theorem gam_neg {a : Sign} {n : Int} (h : Gam a (.int n)) :
    Gam (negS a) (.int (wrap64 (-n))) :=
  gam_arith (ints_of h) (fun hz => by rw [eq_zero (n := n) hz h]; decide)

theorem mayT_sound {a : Sign} {v : Value} (h : Gam a v) (ht : v.truthy = true) :
    mayT a = true := by
  cases v with
  | int n =>
    simp only [Gam, hasInt] at h
    simp only [Value.truthy, bne_iff_ne, ne_eq] at ht
    simp only [mayT]
    split at h <;> (try split at h) <;> simp_all
  | _ => simp_all [Gam, mayT]

theorem mayF_sound {a : Sign} {v : Value} (h : Gam a v) (ht : v.truthy = false) :
    mayF a = true := by
  cases v with
  | int n =>
    simp only [Value.truthy, bne_eq_false_iff_eq] at ht
    subst ht
    simp_all [Gam, hasInt, mayF]
  | _ => simp_all [Gam, mayF]

theorem binErr_sound {s : Store} {op : BinOp} {l r : Value} {a b : Sign}
    (h : binOpSem s op l r = none) (hl : Gam a l) (hr : Gam b r) :
    binFailKind op l r ∈ binErr op a b := by
  rcases l with _ | _ | n | _ | _ | _ <;> rcases r with _ | _ | m | _ | _ | _ <;>
    cases op <;> simp [binOpSem] at h <;> simp only [Gam] at hl hr <;>
    simp_all [binErr, binFailKind, Kind.mem_union]
  all_goals (subst h; simp_all [hasInt, ints_of hl])

end Sign

instance : AbsDom Sign where
  top := Sign.all
  le := Sign.le
  join := Sign.join
  widen := Sign.join
  Gam := Sign.Gam
  ofValue := Sign.of
  closure := { other := true }
  binop := Sign.binop
  neg := Sign.negS
  mayT := Sign.mayT
  mayF := Sign.mayF
  binErr := Sign.binErr
  negErr a := a.other
  asNative _ := none
  refine _ _ a _ := a
  isBot a := a == {}
  le_sound := Sign.gam_le
  join_l := Sign.gam_join_l
  join_r := Sign.gam_join_r
  widen_l := Sign.gam_join_l
  widen_r := Sign.gam_join_r
  top_sound := by
    intro v
    cases v with
    | int n => exact Sign.gam_allInt n
    | _ => rfl
  ofValue_sound := Sign.gam_of
  closure_sound _ := rfl
  binop_sound := Sign.gam_binop
  neg_sound := Sign.gam_neg
  mayT_sound := Sign.mayT_sound
  mayF_sound := Sign.mayF_sound
  binErr_sound := Sign.binErr_sound
  negErr_sound := by
    intro a v h hv
    cases v with
    | int n => exact absurd rfl (hv n)
    | _ => exact h
  asNative_sound := by
    intro a v f _ hn
    cases hn
  refine_sound h _ _ _ := h
  isBot_sound := by
    intro a v ha h
    simp only [beq_iff_eq] at ha
    subst ha
    cases v with
    | int n => simp [Sign.Gam, Sign.hasInt] at h
    | _ => simp [Sign.Gam] at h

end Vsa.AbsInt
