import Vsa.AbsInt.Domain

/-!
# The constant domain

The flat lattice over values: `bot`, one value, or `top`. Operators on two
known values compute `binOpSem` exactly, except string concatenation with a
closure, whose rendering depends on the store. Equality tests refine a
variable to the constant it is compared with. The lattice has finite height,
so widening is join.
-/

namespace Vsa.AbsInt

open Vsa.While

/-- Constants. -/
inductive Const where
  | bot
  | val (v : Value)
  | top
  deriving DecidableEq, Repr

namespace Const

def Gam : Const → Value → Prop
  | bot, _ => False
  | val v, w => w = v
  | top, _ => True

def le : Const → Const → Bool
  | bot, _ => true
  | _, top => true
  | val v, val w => v == w
  | _, _ => false

def join : Const → Const → Const
  | bot, a => a
  | a, bot => a
  | val v, val w => if v = w then val v else top
  | _, _ => top

def isClosure : Value → Bool
  | .closure _ => true
  | _ => false

/-- The empty store, for operators that do not consult it. -/
def store0 : Store := ⟨#[], #[]⟩

/-- `binOpSem` does not consult the store unless a closure is rendered. -/
theorem binOpSem_store {s s' : Store} {op : BinOp} {l r : Value}
    (hl : isClosure l = false) (hr : isClosure r = false) :
    binOpSem s op l r = binOpSem s' op l r := by
  rcases l with _ | _ | _ | _ | _ | (_ | _ | _) <;>
    rcases r with _ | _ | _ | _ | _ | (_ | _ | _) <;>
    simp_all [isClosure] <;> cases op <;> rfl

/-- Whether `binOpSem` fails does not depend on the store. -/
theorem binOpSem_none_store {s s' : Store} {op : BinOp} {l r : Value}
    (h : binOpSem s op l r = none) : binOpSem s' op l r = none := by
  rcases l with _ | _ | _ | _ | _ | (_ | _ | _) <;>
    rcases r with _ | _ | _ | _ | _ | (_ | _ | _) <;>
    cases op <;> simp_all [binOpSem]

def binop (op : BinOp) : Const → Const → Const
  | bot, _ => bot
  | _, bot => bot
  | val l, val r =>
    if isClosure l || isClosure r then top
    else match binOpSem store0 op l r with
      | some v => val v
      | none => bot
  | _, _ => top

def neg : Const → Const
  | val (.int n) => val (.int (wrap64 (-n)))
  | val _ => bot
  | c => c

def mayT : Const → Bool
  | bot => false
  | val v => v.truthy
  | top => true

def mayF : Const → Bool
  | bot => false
  | val v => !v.truthy
  | top => true

def binErr (op : BinOp) : Const → Const → List Kind
  | bot, _ => []
  | _, bot => []
  | val l, val r =>
    match binOpSem store0 op l r with
    | none => [binFailKind op l r]
    | some _ => []
  | _, _ => [.type, .divZero]

def negErr : Const → Bool
  | val (.int _) => false
  | bot => false
  | _ => true

def asNative : Const → Option NativeFn
  | val (.native f) => some f
  | _ => none

/-- `x == r` true (or `x != r` false) makes `x` the constant `r`. -/
def refine : BinOp → Bool → Const → Const → Const
  | .eq, true, a, val r => if Gam' a r then val r else bot
  | .ne, false, a, val r => if Gam' a r then val r else bot
  | _, _, a, _ => a
where
  /-- Decidable membership. -/
  Gam' : Const → Value → Bool
    | bot, _ => false
    | val v, w => w == v
    | top, _ => true

theorem gam'_iff {a : Const} {v : Value} : refine.Gam' a v = true ↔ Gam a v := by
  cases a <;> simp [refine.Gam', Gam]

theorem value_equal_eq {l r : Value} (h : l.equal r = true) : l = r := by
  rcases l with _ | _ | _ | _ | _ | (_ | _ | _) <;>
    rcases r with _ | _ | _ | _ | _ | (_ | _ | _) <;>
    simp_all [Value.equal]

theorem gam_join_l {a b : Const} {v : Value} (h : Gam a v) : Gam (join a b) v := by
  cases a with
  | bot => exact h.elim
  | top => cases b <;> trivial
  | val x =>
    cases b with
    | bot => exact h
    | top => trivial
    | val y =>
      simp only [join]
      by_cases hxy : x = y
      · simp only [hxy, ↓reduceIte]; simp only [Gam] at h ⊢; rw [h, hxy]
      · simp only [hxy, ↓reduceIte]; trivial

theorem gam_join_r {a b : Const} {v : Value} (h : Gam b v) : Gam (join a b) v := by
  cases b with
  | bot => exact h.elim
  | top => cases a <;> trivial
  | val y =>
    cases a with
    | bot => exact h
    | top => trivial
    | val x =>
      simp only [join]
      by_cases hxy : x = y
      · simp only [hxy, ↓reduceIte]; exact h
      · simp only [hxy, ↓reduceIte]; trivial

end Const

instance : AbsDom Const where
  top := .top
  le := Const.le
  join := Const.join
  widen := Const.join
  Gam := Const.Gam
  ofValue := .val
  closure := .top
  binop := Const.binop
  neg := Const.neg
  mayT := Const.mayT
  mayF := Const.mayF
  binErr := Const.binErr
  negErr := Const.negErr
  asNative := Const.asNative
  refine := Const.refine
  isBot a := a == .bot
  le_sound := by
    intro a b v hle h
    cases a <;> cases b <;> simp_all [Const.le, Const.Gam]
  join_l := Const.gam_join_l
  join_r := Const.gam_join_r
  widen_l := Const.gam_join_l
  widen_r := Const.gam_join_r
  top_sound := trivial
  ofValue_sound _ := rfl
  closure_sound _ := trivial
  binop_sound := by
    intro s op l r v a b h hl hr
    cases a <;> cases b <;> simp only [Const.Gam] at hl hr <;>
      first | exact hl.elim | exact hr.elim | trivial | skip
    subst hl hr
    simp only [Const.binop]
    split
    · trivial
    · rename_i hc
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
      rw [Const.binOpSem_store (s' := s) hc.1 hc.2, h]
      rfl
  neg_sound := by
    intro a n h
    cases a with
    | bot => exact h.elim
    | top => trivial
    | val w => cases h; rfl
  mayT_sound := by
    intro a v h ht
    cases a <;> simp_all [Const.Gam, Const.mayT]
  mayF_sound := by
    intro a v h ht
    cases a <;> simp_all [Const.Gam, Const.mayF]
  binErr_sound := by
    intro s op l r a b h hl hr
    cases a <;> cases b <;> simp only [Const.Gam] at hl hr <;>
      first | exact hl.elim | exact hr.elim | exact binFailKind_mem | skip
    subst hl hr
    simp [Const.binErr, Const.binOpSem_none_store (s' := Const.store0) h]
  negErr_sound := by
    intro a v h hv
    cases a with
    | bot => exact h.elim
    | top => rfl
    | val w =>
      cases h
      cases v with
      | int n => exact absurd rfl (hv n)
      | _ => rfl
  asNative_sound := by
    intro a v f h hn
    cases a with
    | val w =>
      cases h
      cases v <;> simp_all [Const.asNative]
    | _ => simp [Const.asNative] at hn
  refine_sound := by
    intro s op t l r w a b hl hr hw ht
    cases op <;> cases t <;> cases b <;> simp only [Const.refine] <;> try exact hl
    · -- `x == r` is true
      simp only [Const.Gam] at hr
      subst hr
      rcases l with _ | _ | _ | _ | _ | (_ | _ | _) <;> simp [binOpSem] at hw <;> subst hw <;>
        (have := Const.value_equal_eq ht; subst this;
         simp [Const.gam'_iff.2 hl, Const.Gam])
    · -- `x != r` is false
      simp only [Const.Gam] at hr
      subst hr
      rcases l with _ | _ | _ | _ | _ | (_ | _ | _) <;> simp [binOpSem] at hw <;> subst hw <;>
        (simp [Value.truthy] at ht; have := Const.value_equal_eq ht; subst this;
         simp [Const.gam'_iff.2 hl, Const.Gam])
  isBot_sound := by
    intro a v ha h
    cases a <;> simp_all [Const.Gam]

end Vsa.AbsInt
