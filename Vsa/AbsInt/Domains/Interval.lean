import Vsa.AbsInt.Domain

/-!
# The interval domain

`range lo hi` is the set of integers between the bounds (`none` is
unbounded); `top` is every value. Arithmetic results are 64-bit wrapped
(`wrap64`): a result interval inside `[-2^63, 2^63)` is exact, otherwise it
widens to the whole 64-bit range. Multiplication, division and remainder are
exact on singletons. Widening drops unstable bounds. Comparisons against an
interval refine the compared variable.
-/

namespace Vsa.AbsInt

open Vsa.While

/-- Integer intervals. -/
inductive Itv where
  | bot
  | range (lo hi : Option Int)
  | top
  deriving DecidableEq, Repr

namespace Itv

/-- Lower-bound membership. -/
def InLo : Option Int → Int → Prop
  | none, _ => True
  | some l, n => l ≤ n

/-- Upper-bound membership. -/
def InHi : Option Int → Int → Prop
  | none, _ => True
  | some h, n => n ≤ h

def Gam : Itv → Value → Prop
  | bot, _ => False
  | range lo hi, .int n => InLo lo n ∧ InHi hi n
  | range _ _, _ => False
  | top, _ => True

/-- `a` is a weaker lower bound than `b`. -/
def loLe : Option Int → Option Int → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => decide (a ≤ b)

/-- `a` is a stronger upper bound than `b`. -/
def hiLe : Option Int → Option Int → Bool
  | _, none => true
  | none, some _ => false
  | some a, some b => decide (a ≤ b)

theorem inLo_of_loLe {a b : Option Int} {n : Int} (h : loLe a b = true) (hb : InLo b n) :
    InLo a n := by
  cases a <;> cases b <;> simp_all [loLe, InLo] <;> omega

theorem inHi_of_hiLe {a b : Option Int} {n : Int} (h : hiLe a b = true) (ha : InHi a n) :
    InHi b n := by
  cases a <;> cases b <;> simp_all [hiLe, InHi] <;> omega

def le : Itv → Itv → Bool
  | bot, _ => true
  | _, top => true
  | range l1 h1, range l2 h2 => loLe l2 l1 && hiLe h1 h2
  | _, _ => false

def minLo : Option Int → Option Int → Option Int
  | some a, some b => some (min a b)
  | _, _ => none

def maxHi : Option Int → Option Int → Option Int
  | some a, some b => some (max a b)
  | _, _ => none

def join : Itv → Itv → Itv
  | bot, a => a
  | a, bot => a
  | range l1 h1, range l2 h2 => range (minLo l1 l2) (maxHi h1 h2)
  | _, _ => top

def widen : Itv → Itv → Itv
  | bot, a => a
  | a, bot => a
  | range l1 h1, range l2 h2 =>
    range (if loLe l1 l2 then l1 else none) (if hiLe h2 h1 then h1 else none)
  | _, _ => top

/-- The 64-bit range. -/
def full : Itv := range (some (-2^63)) (some (2^63 - 1))

/-- The interval of `wrap64 z` for `z` between the bounds. -/
def wrapR (lo hi : Option Int) : Itv :=
  match lo, hi with
  | some l, some h => if -2^63 ≤ l ∧ h ≤ 2^63 - 1 then range lo hi else full
  | _, _ => full

theorem gam_full (z : Int) : Gam full (.int (wrap64 z)) := by
  have := wrap64_range z
  simp only [full, Gam, InLo, InHi]
  omega

theorem gam_wrapR {lo hi : Option Int} {z : Int} (hl : InLo lo z) (hh : InHi hi z) :
    Gam (wrapR lo hi) (.int (wrap64 z)) := by
  unfold wrapR
  cases lo with
  | none => exact gam_full z
  | some l =>
    cases hi with
    | none => exact gam_full z
    | some h =>
      simp only
      split
      · rename_i hr
        simp only [InLo, InHi] at hl hh
        rw [wrap64_eq_self ⟨by omega, by omega⟩]
        exact ⟨hl, hh⟩
      · exact gam_full z

def addB : Option Int → Option Int → Option Int
  | some a, some b => some (a + b)
  | _, _ => none

def subB : Option Int → Option Int → Option Int
  | some a, some b => some (a - b)
  | _, _ => none

/-- The single value of a singleton interval. -/
def single : Itv → Option Int
  | range (some a) (some b) => if a = b then some a else none
  | _ => none

theorem single_eq {a : Itv} {x n : Int} (hs : single a = some x) (h : Gam a (.int n)) :
    n = x := by
  unfold single at hs
  split at hs
  · rename_i l hh
    split at hs
    · cases hs
      simp only [Gam, InLo, InHi] at h
      omega
    · cases hs
  · cases hs

/-- Whether a comparison or equality operator. -/
def isBool : BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

def binop (op : BinOp) (a b : Itv) : Itv :=
  match a, b with
  | bot, _ => bot
  | _, bot => bot
  | range l1 h1, range l2 h2 =>
    match op with
    | .add => wrapR (addB l1 l2) (addB h1 h2)
    | .sub => wrapR (subB l1 h2) (subB h1 l2)
    | .mul =>
      match single a, single b with
      | some x, some y => wrapR (some (x * y)) (some (x * y))
      | _, _ => full
    | .div =>
      match single a, single b with
      | some x, some y => wrapR (some (x.tdiv y)) (some (x.tdiv y))
      | _, _ => full
    | .mod =>
      match single a, single b with
      | some x, some y => wrapR (some (x.tmod y)) (some (x.tmod y))
      | _, _ => full
    | _ => top
  | _, _ => if isBool op || op == .add then top else full

def neg : Itv → Itv
  | bot => bot
  | range lo hi => wrapR (subB (some 0) hi) (subB (some 0) lo)
  | top => full

def mem0 : Itv → Bool
  | bot => false
  | range lo hi => loLe lo (some 0) && hiLe (some 0) hi
  | top => true

def mayT : Itv → Bool
  | bot => false
  | range lo hi => !(lo == some 0 && hi == some 0)
  | top => true

def binErr (op : BinOp) : Itv → Itv → List Kind
  | bot, _ => []
  | _, bot => []
  | range _ _, range l2 h2 =>
    match op with
    | .div | .mod => if mem0 (range l2 h2) then [.divZero] else []
    | _ => []
  | _, _ => [.type, .divZero]

/-- An interval, emptied when its bounds cross. -/
def mk (lo hi : Option Int) : Itv :=
  match lo, hi with
  | some a, some b => if b < a then bot else range lo hi
  | _, _ => range lo hi

theorem gam_mk {lo hi : Option Int} {n : Int} (hl : InLo lo n) (hh : InHi hi n) :
    Gam (mk lo hi) (.int n) := by
  cases lo with
  | none => exact ⟨hl, hh⟩
  | some a =>
    cases hi with
    | none => exact ⟨hl, hh⟩
    | some b =>
      simp only [InLo, InHi] at hl hh
      have hab : ¬ b < a := by omega
      simp only [mk, hab, ↓reduceIte]
      exact ⟨hl, hh⟩

def maxLo : Option Int → Option Int → Option Int
  | none, b => b
  | a, none => a
  | some a, some b => some (max a b)

def minHi : Option Int → Option Int → Option Int
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

theorem inLo_maxLo {a b : Option Int} {n : Int} (ha : InLo a n) (hb : InLo b n) :
    InLo (maxLo a b) n := by
  cases a <;> cases b <;> simp_all [maxLo, InLo] <;> omega

theorem inHi_minHi {a b : Option Int} {n : Int} (ha : InHi a n) (hb : InHi b n) :
    InHi (minHi a b) n := by
  cases a <;> cases b <;> simp_all [minHi, InHi] <;> omega

/-- Bounds of an interval (`top` is unbounded). -/
def lo : Itv → Option Int
  | range l _ => l
  | _ => none

def hi : Itv → Option Int
  | range _ h => h
  | _ => none

/-- Refine `x ∈ a` knowing `(x op r).truthy = t` for an integer `r ∈ [l2, h2]`. -/
def refineR (op : BinOp) (t : Bool) (a : Itv) (l2 h2 : Option Int) : Itv :=
  match op, t with
  | .lt, true => mk a.lo (minHi a.hi (subB h2 (some 1)))
  | .lt, false => mk (maxLo a.lo l2) a.hi
  | .le, true => mk a.lo (minHi a.hi h2)
  | .le, false => mk (maxLo a.lo (addB l2 (some 1))) a.hi
  | .gt, true => mk (maxLo a.lo (addB l2 (some 1))) a.hi
  | .gt, false => mk a.lo (minHi a.hi h2)
  | .ge, true => mk (maxLo a.lo l2) a.hi
  | .ge, false => mk a.lo (minHi a.hi (subB h2 (some 1)))
  | .eq, true => mk (maxLo a.lo l2) (minHi a.hi h2)
  | .ne, false => mk (maxLo a.lo l2) (minHi a.hi h2)
  | _, _ => a

def refine (op : BinOp) (t : Bool) (a b : Itv) : Itv :=
  match a, b with
  | bot, _ => bot
  | a, range l2 h2 => refineR op t a l2 h2
  | a, _ => a

def isBot : Itv → Bool
  | bot => true
  | range (some a) (some b) => decide (b < a)
  | _ => false

/-! ## Soundness -/

theorem gam_le {a b : Itv} {v : Value} (hle : le a b = true) (h : Gam a v) : Gam b v := by
  cases a with
  | bot => exact h.elim
  | top => cases b <;> simp_all [le]
  | range l1 h1 =>
    cases b with
    | bot => simp [le] at hle
    | top => trivial
    | range l2 h2 =>
      simp only [le, Bool.and_eq_true] at hle
      rcases v with _ | _ | n | _ | _ | _ <;> simp only [Gam] at h ⊢
      exact ⟨inLo_of_loLe hle.1 h.1, inHi_of_hiLe hle.2 h.2⟩

theorem inLo_minLo_l {a b : Option Int} {n : Int} (h : InLo a n) : InLo (minLo a b) n := by
  cases a <;> cases b <;> simp_all [minLo, InLo] <;> omega

theorem inLo_minLo_r {a b : Option Int} {n : Int} (h : InLo b n) : InLo (minLo a b) n := by
  cases a <;> cases b <;> simp_all [minLo, InLo] <;> omega

theorem inHi_maxHi_l {a b : Option Int} {n : Int} (h : InHi a n) : InHi (maxHi a b) n := by
  cases a <;> cases b <;> simp_all [maxHi, InHi] <;> omega

theorem inHi_maxHi_r {a b : Option Int} {n : Int} (h : InHi b n) : InHi (maxHi a b) n := by
  cases a <;> cases b <;> simp_all [maxHi, InHi] <;> omega

theorem gam_join_l {a b : Itv} {v : Value} (h : Gam a v) : Gam (join a b) v := by
  cases a with
  | bot => exact h.elim
  | top => cases b <;> trivial
  | range l1 h1 =>
    cases b with
    | bot => exact h
    | top => trivial
    | range l2 h2 =>
      rcases v with _ | _ | n | _ | _ | _ <;> simp only [Gam] at h ⊢
      exact ⟨inLo_minLo_l h.1, inHi_maxHi_l h.2⟩

theorem gam_join_r {a b : Itv} {v : Value} (h : Gam b v) : Gam (join a b) v := by
  cases b with
  | bot => exact h.elim
  | top => cases a <;> trivial
  | range l2 h2 =>
    cases a with
    | bot => exact h
    | top => trivial
    | range l1 h1 =>
      rcases v with _ | _ | n | _ | _ | _ <;> simp only [Gam] at h ⊢
      exact ⟨inLo_minLo_r h.1, inHi_maxHi_r h.2⟩

theorem gam_widen_l {a b : Itv} {v : Value} (h : Gam a v) : Gam (widen a b) v := by
  cases a with
  | bot => exact h.elim
  | top => cases b <;> trivial
  | range l1 h1 =>
    cases b with
    | bot => exact h
    | top => trivial
    | range l2 h2 =>
      rcases v with _ | _ | n | _ | _ | _ <;> simp only [Gam] at h ⊢
      refine ⟨?_, ?_⟩
      · split
        · exact h.1
        · trivial
      · split
        · exact h.2
        · trivial

theorem gam_widen_r {a b : Itv} {v : Value} (h : Gam b v) : Gam (widen a b) v := by
  cases b with
  | bot => exact h.elim
  | top => cases a <;> trivial
  | range l2 h2 =>
    cases a with
    | bot => exact h
    | top => trivial
    | range l1 h1 =>
      rcases v with _ | _ | n | _ | _ | _ <;> simp only [Gam] at h ⊢
      refine ⟨?_, ?_⟩
      · split
        · rename_i hle
          exact inLo_of_loLe hle h.1
        · trivial
      · split
        · rename_i hle
          exact inHi_of_hiLe hle h.2
        · trivial

theorem inLo_addB {a b : Option Int} {n m : Int} (ha : InLo a n) (hb : InLo b m) :
    InLo (addB a b) (n + m) := by
  cases a <;> cases b <;> simp_all [addB, InLo] <;> omega

theorem inHi_addB {a b : Option Int} {n m : Int} (ha : InHi a n) (hb : InHi b m) :
    InHi (addB a b) (n + m) := by
  cases a <;> cases b <;> simp_all [addB, InHi] <;> omega

theorem inLo_subB {a b : Option Int} {n m : Int} (ha : InLo a n) (hb : InHi b m) :
    InLo (subB a b) (n - m) := by
  cases a <;> cases b <;> simp_all [subB, InLo, InHi] <;> omega

theorem inHi_subB {a b : Option Int} {n m : Int} (ha : InHi a n) (hb : InLo b m) :
    InHi (subB a b) (n - m) := by
  cases a <;> cases b <;> simp_all [subB, InLo, InHi] <;> omega

theorem gam_single {z : Int} : InLo (some z) z ∧ InHi (some z) z := by
  simp [InLo, InHi]

/-- Arithmetic other than `+` always yields a wrapped integer. -/
theorem gam_full_arith {s : Store} {op : BinOp} {l r v : Value}
    (hop : (isBool op || op == .add) = false) (h : binOpSem s op l r = some v) :
    Gam full v := by
  cases op <;> simp [isBool] at hop <;>
    rcases l with _ | _ | _ | _ | _ | _ <;> rcases r with _ | _ | _ | _ | _ | _ <;>
    simp [binOpSem] at h
  all_goals first
    | (subst h; exact gam_full _)
    | (obtain ⟨_, rfl⟩ := h; exact gam_full _)

theorem gam_binop {s : Store} {op : BinOp} {l r v : Value} {a b : Itv}
    (h : binOpSem s op l r = some v) (hl : Gam a l) (hr : Gam b r) :
    Gam (binop op a b) v := by
  cases a with
  | bot => exact hl.elim
  | top =>
    cases b with
    | bot => exact hr.elim
    | _ =>
      simp only [binop]
      split
      · trivial
      · exact gam_full_arith (Bool.eq_false_iff.mpr ‹_›) h
  | range l1 h1 =>
    cases b with
    | bot => exact hr.elim
    | top =>
      simp only [binop]
      split
      · trivial
      · exact gam_full_arith (Bool.eq_false_iff.mpr ‹_›) h
    | range l2 h2 =>
      rcases l with _ | _ | n | _ | _ | _ <;> simp only [Gam] at hl
      rcases r with _ | _ | m | _ | _ | _ <;> simp only [Gam] at hr
      cases op <;> simp only [binop] <;> simp only [binOpSem] at h <;>
        try (cases h; trivial)
      · cases h; exact gam_wrapR (inLo_addB hl.1 hr.1) (inHi_addB hl.2 hr.2)
      · cases h; exact gam_wrapR (inLo_subB hl.1 hr.2) (inHi_subB hl.2 hr.1)
      · cases h
        split
        · rename_i x y hx hy
          have e1 : n = x := single_eq hx hl
          have e2 : m = y := single_eq hy hr
          subst e1 e2
          exact gam_wrapR gam_single.1 gam_single.2
        · exact gam_full _
      · split at h
        · cases h
        · cases h
          split
          · rename_i x y hx hy
            have e1 : n = x := single_eq hx hl
            have e2 : m = y := single_eq hy hr
            subst e1 e2
            exact gam_wrapR gam_single.1 gam_single.2
          · exact gam_full _
      · split at h
        · cases h
        · cases h
          split
          · rename_i x y hx hy
            have e1 : n = x := single_eq hx hl
            have e2 : m = y := single_eq hy hr
            subst e1 e2
            exact gam_wrapR gam_single.1 gam_single.2
          · exact gam_full _

theorem gam_neg {a : Itv} {n : Int} (h : Gam a (.int n)) : Gam (neg a) (.int (wrap64 (-n))) := by
  cases a with
  | bot => exact h.elim
  | top => exact gam_full _
  | range lo hi =>
    have h' : InLo lo n ∧ InHi hi n := h
    exact gam_wrapR (lo := subB (some 0) hi) (hi := subB (some 0) lo) (z := -n)
      (by cases hi <;> simp_all [subB, InLo, InHi] <;> omega)
      (by cases lo <;> simp_all [subB, InLo, InHi] <;> omega)

theorem mayT_sound {a : Itv} {v : Value} (h : Gam a v) (ht : v.truthy = true) :
    mayT a = true := by
  cases a with
  | bot => exact h.elim
  | top => rfl
  | range lo hi =>
    rcases v with _ | _ | n | _ | _ | _ <;> simp only [Gam] at h
    simp only [Value.truthy, bne_iff_ne, ne_eq] at ht
    cases lo <;> cases hi <;> simp_all [mayT, InLo, InHi]
    omega

theorem mem0_sound {a : Itv} {v : Value} (h : Gam a v) (ht : v.truthy = false) :
    mem0 a = true := by
  cases a with
  | bot => exact h.elim
  | top => rfl
  | range lo hi =>
    rcases v with _ | _ | n | _ | _ | _ <;> simp only [Gam] at h
    simp only [Value.truthy, bne_eq_false_iff_eq] at ht
    subst ht
    simp only [mem0, Bool.and_eq_true]
    cases lo <;> cases hi <;> simp_all [loLe, hiLe, InLo, InHi]

theorem binErr_sound {s : Store} {op : BinOp} {l r : Value} {a b : Itv}
    (h : binOpSem s op l r = none) (hl : Gam a l) (hr : Gam b r) :
    binFailKind op l r ∈ binErr op a b := by
  cases a with
  | bot => exact hl.elim
  | top => cases b with
    | bot => exact hr.elim
    | _ => exact binFailKind_mem
  | range l1 h1 =>
    cases b with
    | bot => exact hr.elim
    | top => exact binFailKind_mem
    | range l2 h2 =>
      rcases l with _ | _ | n | _ | _ | _ <;> simp only [Gam] at hl
      rcases r with _ | _ | m | _ | _ | _ <;> simp only [Gam] at hr
      cases op <;> simp [binOpSem] at h <;> subst h <;> simp only [binErr] <;>
        rw [if_pos (mem0_sound (a := range l2 h2) (v := .int 0) hr rfl)] <;> simp [binFailKind]

theorem inLo_lo {a : Itv} {n : Int} (h : Gam a (.int n)) : InLo a.lo n := by
  cases a with
  | bot => exact h.elim
  | top => trivial
  | range lo hi => exact h.1

theorem inHi_hi {a : Itv} {n : Int} (h : Gam a (.int n)) : InHi a.hi n := by
  cases a with
  | bot => exact h.elim
  | top => trivial
  | range lo hi => exact h.2

theorem refine_sound {s : Store} {op : BinOp} {t : Bool} {l r w : Value} {a b : Itv}
    (hl : Gam a l) (hr : Gam b r) (hw : binOpSem s op l r = some w) (ht : w.truthy = t) :
    Gam (refine op t a b) l := by
  cases a with
  | bot => exact hl.elim
  | _ =>
    cases b with
    | bot => exact hr.elim
    | top => exact hl
    | range l2 h2 =>
      simp only [refine]
      rcases r with _ | _ | m | _ | _ | _ <;> simp only [Gam] at hr
      cases op <;> cases t <;> simp only [refineR] <;> try exact hl
      all_goals
        rcases l with _ | _ | n | _ | _ | _ <;> simp [binOpSem] at hw <;> subst hw <;>
          simp [Value.truthy, Value.equal] at ht <;>
          exact gam_mk
            (by first
              | exact inLo_lo hl
              | exact inLo_maxLo (inLo_lo hl) (by
                  cases l2 <;> simp_all [addB, InLo, InHi] <;> omega))
            (by first
              | exact inHi_hi hl
              | exact inHi_minHi (inHi_hi hl) (by
                  cases h2 <;> simp_all [subB, InLo, InHi] <;> omega))

end Itv

instance : AbsDom Itv where
  top := .top
  le := Itv.le
  join := Itv.join
  widen := Itv.widen
  Gam := Itv.Gam
  ofValue
    | .int n => .range (some n) (some n)
    | _ => .top
  closure := .top
  binop := Itv.binop
  neg := Itv.neg
  mayT := Itv.mayT
  mayF := Itv.mem0
  binErr := Itv.binErr
  negErr
    | .top => true
    | _ => false
  asNative _ := none
  refine := Itv.refine
  isBot := Itv.isBot
  le_sound := Itv.gam_le
  join_l := Itv.gam_join_l
  join_r := Itv.gam_join_r
  widen_l := Itv.gam_widen_l
  widen_r := Itv.gam_widen_r
  top_sound := trivial
  ofValue_sound := by
    intro v
    cases v with
    | int n => exact Itv.gam_single
    | _ => trivial
  closure_sound _ := trivial
  binop_sound := Itv.gam_binop
  neg_sound := Itv.gam_neg
  mayT_sound := Itv.mayT_sound
  mayF_sound := Itv.mem0_sound
  binErr_sound := Itv.binErr_sound
  negErr_sound := by
    intro a v h hv
    cases a with
    | bot => exact h.elim
    | top => rfl
    | range lo hi =>
      rcases v with _ | _ | n | _ | _ | _ <;> simp only [Itv.Gam] at h
      exact absurd rfl (hv n)
  asNative_sound := by
    intro a v f _ hn
    cases hn
  refine_sound := Itv.refine_sound
  isBot_sound := by
    intro a v ha h
    cases a with
    | bot => exact h
    | top => simp [Itv.isBot] at ha
    | range lo hi =>
      rcases v with _ | _ | n | _ | _ | _ <;> simp only [Itv.Gam] at h
      cases lo <;> cases hi <;> simp_all [Itv.isBot, Itv.InLo, Itv.InHi]
      omega

end Vsa.AbsInt
