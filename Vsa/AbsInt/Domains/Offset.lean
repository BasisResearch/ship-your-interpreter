import Vsa.AbsInt.Domains.Interval

namespace Vsa.AbsInt

open Vsa.While AbsOps AbsDom

abbrev OffV := Itv × Option Int

namespace Off

def offLe : Option Int → Option Int → Bool
  | _, none => true
  | none, some _ => false
  | some x, some y => decide (y ≤ x)

def offMin : Option Int → Option Int → Option Int
  | some x, some y => some (min x y)
  | _, _ => none

def offWiden : Option Int → Option Int → Option Int
  | some x, some y => if x ≤ y then some x else none
  | _, _ => none

def noWrap (i : Itv) (c : Int) : Bool :=
  match i with
  | .range (some lo) (some hi) => decide (-2^63 ≤ lo + c ∧ hi + c ≤ 2^63 - 1)
  | _ => false

def offBin (op : BinOp) (a b : OffV) : Option Int :=
  match op with
  | .add =>
    match a.2, Itv.single b.1, b.2, Itv.single a.1 with
    | some x, some c, _, _ => if noWrap a.1 c then some (x + c) else none
    | _, _, some y, some c => if noWrap b.1 c then some (y + c) else none
    | _, _, _, _ => none
  | .sub =>
    match a.2, Itv.single b.1 with
    | some x, some c => if noWrap a.1 (-c) then some (x - c) else none
    | _, _ => none
  | _ => none

end Off

instance offOps : AbsOps OffV where
  top := (.top, none)
  le a b := Itv.le a.1 b.1 && Off.offLe a.2 b.2
  join a b := (Itv.join a.1 b.1, Off.offMin a.2 b.2)
  widen a b := (Itv.widen a.1 b.1, Off.offWiden a.2 b.2)
  ofValue v := (AbsOps.ofValue v, none)
  closure := (.top, none)
  binop op a b := (Itv.binop op a.1 b.1, Off.offBin op a b)
  neg a := (Itv.neg a.1, none)
  mayT a := Itv.mayT a.1
  mayF a := Itv.mem0 a.1
  binErr op a b := Itv.binErr op a.1 b.1
  negErr a := AbsOps.negErr a.1
  asNative _ := none
  refine op t a b := (Itv.refine op t a.1 b.1, a.2)
  isBot a := Itv.isBot a.1

namespace Off

def OK (b : Int) : Option Int → Value → Prop
  | none, _ => True
  | some k, .int n => k ≤ n - b
  | some _, _ => False

theorem ok_le {b : Int} {o p : Option Int} {v : Value} (hle : offLe o p = true)
    (h : OK b o v) : OK b p v := by
  cases p with
  | none => trivial
  | some y =>
    cases o with
    | none => simp [offLe] at hle
    | some x =>
      simp only [offLe, decide_eq_true_eq] at hle
      rcases v with _ | _ | n | _ | _ | _ <;> simp_all [OK]
      omega

theorem ok_min_l {b : Int} {o p : Option Int} {v : Value} (h : OK b o v) :
    OK b (offMin o p) v := by
  cases o <;> cases p <;> simp only [offMin] <;> try trivial
  rcases v with _ | _ | n | _ | _ | _ <;> simp_all [OK]
  omega

theorem ok_min_r {b : Int} {o p : Option Int} {v : Value} (h : OK b p v) :
    OK b (offMin o p) v := by
  cases o <;> cases p <;> simp only [offMin] <;> try trivial
  rcases v with _ | _ | n | _ | _ | _ <;> simp_all [OK]
  omega

theorem ok_widen_l {b : Int} {o p : Option Int} {v : Value} (h : OK b o v) :
    OK b (offWiden o p) v := by
  cases o <;> cases p <;> simp only [offWiden] <;> try trivial
  split
  · exact h
  · trivial

theorem ok_widen_r {b : Int} {o p : Option Int} {v : Value} (h : OK b p v) :
    OK b (offWiden o p) v := by
  cases o <;> cases p <;> simp only [offWiden] <;> try trivial
  split
  · rcases v with _ | _ | n | _ | _ | _ <;> simp_all [OK]
    omega
  · trivial

theorem noWrap_eq {i : Itv} {c n : Int} (hw : noWrap i c = true) (h : Itv.Gam i (.int n)) :
    wrap64 (n + c) = n + c := by
  unfold noWrap at hw
  split at hw
  · rename_i lo hi
    simp only [decide_eq_true_eq] at hw
    obtain ⟨h1, h2⟩ := h
    simp only [Itv.InLo, Itv.InHi] at h1 h2
    exact wrap64_eq_self ⟨by omega, by omega⟩
  · cases hw

theorem noWrap_int {i : Itv} {c : Int} {v : Value} (hw : noWrap i c = true) (h : Itv.Gam i v) :
    ∃ n, v = .int n := by
  unfold noWrap at hw
  split at hw
  · rcases v with _ | _ | n | _ | _ | _ <;> simp_all [Itv.Gam]
  · cases hw

theorem single_int {i : Itv} {c : Int} {v : Value} (hs : Itv.single i = some c)
    (h : Itv.Gam i v) : v = .int c := by
  unfold Itv.single at hs
  split at hs
  · rename_i lo hi
    split at hs
    · cases hs
      rcases v with _ | _ | n | _ | _ | _ <;> simp_all [Itv.Gam, Itv.InLo, Itv.InHi]
      omega
    · cases hs
  · cases hs

theorem ok_add_l {b : Int} {s : Store} {l r v : Value} {x y : OffV} {k c : Int}
    (h : binOpSem s .add l r = some v) (hl : Itv.Gam x.1 l ∧ OK b x.2 l)
    (hr : Itv.Gam y.1 r) (hk : x.2 = some k) (hc : Itv.single y.1 = some c)
    (hw : noWrap x.1 c = true) : OK b (some (k + c)) v := by
  obtain ⟨n, rfl⟩ := noWrap_int hw hl.1
  have hrc := single_int hc hr
  subst hrc
  simp only [binOpSem, Option.some.injEq] at h
  subst h
  rw [noWrap_eq hw hl.1]
  have := hl.2
  rw [hk] at this
  simp only [OK] at this ⊢
  omega

theorem ok_add_r {b : Int} {s : Store} {l r v : Value} {x y : OffV} {k c : Int}
    (h : binOpSem s .add l r = some v) (hl : Itv.Gam x.1 l)
    (hr : Itv.Gam y.1 r ∧ OK b y.2 r) (hk : y.2 = some k) (hc : Itv.single x.1 = some c)
    (hw : noWrap y.1 c = true) : OK b (some (k + c)) v := by
  obtain ⟨m, rfl⟩ := noWrap_int hw hr.1
  have hlc := single_int hc hl
  subst hlc
  simp only [binOpSem, Option.some.injEq] at h
  subst h
  rw [Int.add_comm c m, noWrap_eq hw hr.1]
  have := hr.2
  rw [hk] at this
  simp only [OK] at this ⊢
  omega

theorem ok_sub {b : Int} {s : Store} {l r v : Value} {x y : OffV} {k c : Int}
    (h : binOpSem s .sub l r = some v) (hl : Itv.Gam x.1 l ∧ OK b x.2 l)
    (hr : Itv.Gam y.1 r) (hk : x.2 = some k) (hc : Itv.single y.1 = some c)
    (hw : noWrap x.1 (-c) = true) : OK b (some (k - c)) v := by
  obtain ⟨n, rfl⟩ := noWrap_int hw hl.1
  have hrc := single_int hc hr
  subst hrc
  simp only [binOpSem, Option.some.injEq] at h
  subst h
  have e := noWrap_eq hw hl.1
  rw [← Int.sub_eq_add_neg] at e
  rw [e]
  have := hl.2
  rw [hk] at this
  simp only [OK] at this ⊢
  omega

theorem ok_bin {b : Int} {s : Store} {op : BinOp} {l r v : Value} {x y : OffV}
    (h : binOpSem s op l r = some v) (hl : Itv.Gam x.1 l ∧ OK b x.2 l)
    (hr : Itv.Gam y.1 r ∧ OK b y.2 r) : OK b (offBin op x y) v := by
  cases op <;> simp only [offBin] <;> try trivial
  · cases hk : x.2 <;> cases hc : Itv.single y.1 <;> cases hk2 : y.2 <;>
      cases hc2 : Itv.single x.1 <;> simp only <;> (try trivial) <;>
      (split <;> rename_i hw <;> first
        | trivial
        | exact ok_add_l h hl hr.1 hk hc hw
        | exact ok_add_r h hl.1 hr hk2 hc2 hw)
  · cases hk : x.2 <;> cases hc : Itv.single y.1 <;> simp only <;> (try trivial)
    split
    · rename_i hw
      exact ok_sub h hl hr.1 hk hc hw
    · trivial

end Off

def offDom (b : Int) : AbsDom OffV where
  toAbsOps := offOps
  Gam a v := Itv.Gam a.1 v ∧ Off.OK b a.2 v
  le_sound {a c v} hle h := by
    change (Itv.le a.1 c.1 && Off.offLe a.2 c.2) = true at hle
    simp only [Bool.and_eq_true] at hle
    exact ⟨Itv.gam_le hle.1 h.1, Off.ok_le hle.2 h.2⟩
  join_l h := ⟨Itv.gam_join_l h.1, Off.ok_min_l h.2⟩
  join_r h := ⟨Itv.gam_join_r h.1, Off.ok_min_r h.2⟩
  widen_l h := ⟨Itv.gam_widen_l h.1, Off.ok_widen_l h.2⟩
  widen_r h := ⟨Itv.gam_widen_r h.1, Off.ok_widen_r h.2⟩
  top_sound := ⟨trivial, trivial⟩
  ofValue_sound v := ⟨AbsDom.ofValue_sound (A := Itv) v, trivial⟩
  closure_sound _ := ⟨trivial, trivial⟩
  binop_sound h hl hr := ⟨Itv.gam_binop h hl.1 hr.1, Off.ok_bin h hl hr⟩
  neg_sound h := ⟨Itv.gam_neg h.1, trivial⟩
  mayT_sound h ht := Itv.mayT_sound h.1 ht
  mayF_sound h ht := Itv.mem0_sound h.1 ht
  binErr_sound h hl hr := Itv.binErr_sound h hl.1 hr.1
  negErr_sound h hv := AbsDom.negErr_sound (A := Itv) h.1 hv
  asNative_sound _ hn := by cases hn
  refine_sound hl hr hw ht := ⟨Itv.refine_sound hl.1 hr.1 hw ht, hl.2⟩
  isBot_sound ha h := AbsDom.isBot_sound (A := Itv) ha h.1

end Vsa.AbsInt
