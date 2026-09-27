import Vsa.AbsInt.Domains.Const
import Vsa.AbsInt.Domains.Interval

/-!
# Products of domains and their reduction

`A × B` is the domain whose concretisation is the intersection of the two
components'. A `Reduce A B` instance exchanges information between the
components after each transfer function; the default instance does
nothing. `Const × Itv` is reduced: an integer constant pins the interval,
a singleton interval pins the constant, and a contradiction empties both.
-/

namespace Vsa.AbsInt

open Vsa.While AbsDom

/-- A sound reduction of a product value. -/
class Reduce (A B : Type) [AbsDom A] [AbsDom B] where
  reduce : A × B → A × B
  reduce_sound : ∀ {p : A × B} {v : Value}, Gam p.1 v → Gam p.2 v →
    Gam (reduce p).1 v ∧ Gam (reduce p).2 v

/-- No reduction. -/
instance (priority := low) Reduce.none {A B : Type} [AbsDom A] [AbsDom B] : Reduce A B :=
  ⟨id, fun h1 h2 => ⟨h1, h2⟩⟩

section

variable {A B : Type} [AbsDom A] [AbsDom B] [Reduce A B]

/-- Pair two component values and reduce. -/
def pr (a : A) (b : B) : A × B := Reduce.reduce (a, b)

theorem gam_pr {a : A} {b : B} {v : Value} (ha : Gam a v) (hb : Gam b v) :
    Gam (pr a b).1 v ∧ Gam (pr a b).2 v :=
  Reduce.reduce_sound (p := (a, b)) ha hb

instance : AbsDom (A × B) where
  top := (top, top)
  le a b := le a.1 b.1 && le a.2 b.2
  join a b := (join a.1 b.1, join a.2 b.2)
  widen a b := (widen a.1 b.1, widen a.2 b.2)
  Gam a v := Gam a.1 v ∧ Gam a.2 v
  ofValue v := pr (ofValue v) (ofValue v)
  closure := (closure, closure)
  binop op a b := pr (binop op a.1 b.1) (binop op a.2 b.2)
  neg a := pr (neg a.1) (neg a.2)
  mayT a := mayT a.1 && mayT a.2
  mayF a := mayF a.1 && mayF a.2
  binErr op a b := (binErr op a.1 b.1).filter (· ∈ binErr op a.2 b.2)
  negErr a := negErr a.1 && negErr a.2
  asNative a := (asNative a.1).orElse fun _ => asNative a.2
  refine op t a b := pr (refine op t a.1 b.1) (refine op t a.2 b.2)
  isBot a := isBot a.1 || isBot a.2
  le_sound {a b v} hle h := by
    simp only [Bool.and_eq_true] at hle
    exact ⟨le_sound hle.1 h.1, le_sound hle.2 h.2⟩
  join_l h := ⟨join_l h.1, join_l h.2⟩
  join_r h := ⟨join_r h.1, join_r h.2⟩
  widen_l h := ⟨widen_l h.1, widen_l h.2⟩
  widen_r h := ⟨widen_r h.1, widen_r h.2⟩
  top_sound := ⟨top_sound, top_sound⟩
  ofValue_sound v := gam_pr (ofValue_sound v) (ofValue_sound v)
  closure_sound a := ⟨closure_sound a, closure_sound a⟩
  binop_sound h hl hr := gam_pr (binop_sound h hl.1 hr.1) (binop_sound h hl.2 hr.2)
  neg_sound h := gam_pr (neg_sound h.1) (neg_sound h.2)
  mayT_sound h ht := by simp [mayT_sound h.1 ht, mayT_sound h.2 ht]
  mayF_sound h ht := by simp [mayF_sound h.1 ht, mayF_sound h.2 ht]
  binErr_sound h hl hr := by
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨binErr_sound h hl.1 hr.1, binErr_sound h hl.2 hr.2⟩
  negErr_sound h hv := by simp [negErr_sound h.1 hv, negErr_sound h.2 hv]
  asNative_sound {a v f} h hn := by
    cases h1 : asNative a.1 with
    | some g =>
      rw [h1] at hn
      cases hn
      exact asNative_sound h.1 h1
    | none =>
      rw [h1] at hn
      exact asNative_sound h.2 hn
  refine_sound hl hr hw ht :=
    gam_pr (refine_sound hl.1 hr.1 hw ht) (refine_sound hl.2 hr.2 hw ht)
  isBot_sound {a v} ha h := by
    simp only [Bool.or_eq_true] at ha
    rcases ha with ha | ha
    · exact isBot_sound ha h.1
    · exact isBot_sound ha h.2

end

/-! ## Constants with intervals -/

/-- Decidable interval membership. -/
def Itv.memB : Itv → Int → Bool
  | .bot, _ => false
  | .range lo hi, n => Itv.loLe lo (some n) && Itv.hiLe (some n) hi
  | .top, _ => true

theorem Itv.memB_of {i : Itv} {n : Int} (h : Itv.Gam i (.int n)) : Itv.memB i n = true := by
  cases i with
  | bot => exact h.elim
  | top => rfl
  | range lo hi =>
    obtain ⟨h1, h2⟩ := h
    cases lo <;> cases hi <;> simp_all [Itv.memB, Itv.loLe, Itv.hiLe, Itv.InLo, Itv.InHi]

/-- Reduce a constant with an interval. -/
def reduceCI : Const × Itv → Const × Itv
  | (.val (.int n), i) =>
    if Itv.memB i n then (.val (.int n), .range (some n) (some n)) else (.bot, .bot)
  | (.val _, .range _ _) => (.bot, .bot)
  | (.top, i) =>
    match Itv.single i with
    | some n => (.val (.int n), i)
    | none => (.top, i)
  | p => p

instance : Reduce Const Itv where
  reduce := reduceCI
  reduce_sound {p v} h1 h2 := by
    obtain ⟨c, i⟩ := p
    cases c with
    | bot => exact h1.elim
    | val w =>
      simp only [AbsDom.Gam, Const.Gam] at h1
      subst h1
      cases v with
      | int n =>
        simp only [reduceCI, Itv.memB_of h2, ↓reduceIte]
        exact ⟨rfl, by simp [AbsDom.Gam, Itv.Gam, Itv.InLo, Itv.InHi]⟩
      | _ =>
        cases i with
        | range lo hi => exact (by simpa [AbsDom.Gam, Itv.Gam] using h2)
        | _ => exact ⟨rfl, h2⟩
    | top =>
      simp only [reduceCI]
      split
      · rename_i n hs
        cases v with
        | int m =>
          have := Itv.single_eq hs h2
          subst this
          exact ⟨rfl, h2⟩
        | _ =>
          cases i with
          | range lo hi => exact (by simpa [AbsDom.Gam, Itv.Gam] using h2)
          | _ => simp [Itv.single] at hs
      · exact ⟨trivial, h2⟩

end Vsa.AbsInt
