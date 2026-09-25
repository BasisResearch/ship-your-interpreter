import Vsa.Sim.Boot.View
import Vsa.RuntimeRepr

/-!
# Checkers for strings, values and the initial store

A *partial* view `v` of a memory `m` (`PartialView m v`) agrees with `m`
wherever `v` returns a byte. The checkers here only succeed on bytes `v`
returns, so a check over a view that masks a region out (`maskView`) also
proves the fact for every memory agreeing with `m` outside that region: the
same check gives `StoreRepr` at the entry and `store_survives` through
`interp_run`'s prologue footprint.

* `cstrv`: a NUL-terminated ASCII string (`CStr`, `CString`).
* `valueCheck`: a non-closure `Value` (`ValueRepr`).
* `frameCheck`: an `Env` with no parent (`FrameRepr`).
* `storeRepr_initSt`: the initial store from its one frame.
-/

namespace Vsa.Sim.Boot

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

/-- `v` agrees with `m` wherever it returns a byte. -/
def PartialView (m : Mem) (v : Nat → Option (BitVec 8)) : Prop :=
  ∀ k b, v k = some b → m[k]? = some b

theorem ViewOf.partial {m : Mem} {v : Nat → Option (BitVec 8)} (h : ViewOf m v) :
    PartialView m v := fun k b hk => (h k).trans hk

/-- `v` with the bytes satisfying `out` removed. -/
def maskView (out : Nat → Bool) (v : Nat → Option (BitVec 8)) (k : Nat) : Option (BitVec 8) :=
  if out k then none else v k

/-- A mask of a view is a partial view of every memory agreeing outside the mask. -/
theorem maskView_partial {m m' : Mem} {v : Nat → Option (BitVec 8)} {out : Nat → Bool}
    (h : ViewOf m v) (hag : ∀ k, out k = false → m[k]? = m'[k]?) :
    PartialView m' (maskView out v) := by
  intro k b hk
  unfold maskView at hk
  cases ho : out k
  · rw [ho] at hk
    simp only [Bool.false_eq_true, ↓reduceIte] at hk
    rw [← hag k ho, h k, hk]
  · rw [ho] at hk
    cases hk

theorem PartialView.readLE {m : Mem} {v : Nat → Option (BitVec 8)} (h : PartialView m v)
    {a n x : Nat} (hr : readLEv v a n = some x) : Vsa.MemRepr.readLE m a n = some x := by
  induction n generalizing a x with
  | zero => exact hr
  | succ n ih =>
    simp only [readLEv] at hr
    cases hb : v a with
    | none => rw [hb] at hr; cases hr
    | some b =>
      rw [hb] at hr
      cases hrest : readLEv v (a + 1) n with
      | none => rw [hrest] at hr; cases hr
      | some rest =>
        rw [hrest] at hr
        simp only [Vsa.MemRepr.readLE, h a b hb, ih hrest]
        exact hr

/-! ## Strings -/

/-- The NUL-terminated ASCII string at `a`, within `fuel` bytes. -/
def cstrv (v : Nat → Option (BitVec 8)) (a : Nat) : Nat → Option (List Char)
  | 0 => none
  | fuel + 1 =>
    match v a with
    | some b =>
      if b = 0 then some []
      else if b.toNat < 128 then (cstrv v (a + 1) fuel).map (Char.ofNat b.toNat :: ·)
      else none
    | none => none

theorem cstrv_sound {m : Mem} {v : Nat → Option (BitVec 8)} (h : PartialView m v) :
    ∀ {fuel a cs}, cstrv v a fuel = some cs → CStr m a cs := by
  intro fuel
  induction fuel with
  | zero => intro a cs hc; cases hc
  | succ fuel ih =>
    intro a cs hc
    simp only [cstrv] at hc
    cases hb : v a with
    | none => rw [hb] at hc; cases hc
    | some b =>
      rw [hb] at hc
      simp only at hc
      by_cases h0 : b = 0
      · rw [if_pos h0] at hc
        cases hc
        exact .nil (by rw [h a b hb, h0])
      · rw [if_neg h0] at hc
        by_cases h128 : b.toNat < 128
        · rw [if_pos h128] at hc
          cases hr : cstrv v (a + 1) fuel with
          | none => rw [hr] at hc; cases hc
          | some rest =>
            rw [hr] at hc
            cases hc
            exact .cons (h a b hb) h0 h128 (ih hr)
        · rw [if_neg h128] at hc; cases hc

/-- String check: the string at `a` is `s` (fuel 4096 covers every script string). -/
def cstrIs (v : Nat → Option (BitVec 8)) (a : Nat) (s : String) : Bool :=
  (cstrv v a 4096).map String.ofList == some s

theorem cstrIs_sound {m : Mem} {v : Nat → Option (BitVec 8)} (h : PartialView m v)
    {a : Nat} {s : String} (hc : cstrIs v a s = true) : CString m a s := by
  unfold cstrIs at hc
  cases hr : cstrv v a 4096 with
  | none => rw [hr] at hc; cases hc
  | some cs =>
    rw [hr] at hc
    simp only [Option.map_some, beq_iff_eq, Option.some.injEq] at hc
    exact ⟨cs, cstrv_sound h hr, hc.symm⟩

/-! ## Values -/

/-- A non-closure value at `a` (closures need the closure map; the initial
store has none). -/
def valueCheck (v : Nat → Option (BitVec 8)) (N : NativeAddrs) (a : Nat) : Value → Bool
  | .null => readLEv v a 4 == some 0
  | .bool b => readLEv v a 4 == some 1 && readLEv v (a + 8) 4 == some (cond b 1 0)
  | .int n => readLEv v a 4 == some 2 &&
      (readLEv v (a + 8) 8).map (fun w => (BitVec.ofNat 64 w).toInt) == some n
  | .str s => readLEv v a 4 == some 3 &&
      (match readLEv v (a + 8) 8 with
       | some p => p != 0 && cstrIs v p s
       | none => false)
  | .closure _ => false
  | .native f => readLEv v a 4 == some 5 &&
      (match readLEv v (a + 8) 8 with
       | some p => cstrIs v p (nativeName f)
       | none => false) &&
      readLEv v (a + 16) 8 == some (N.addr f)

theorem valueCheck_sound {m : Mem} {v : Nat → Option (BitVec 8)} (h : PartialView m v)
    {N : NativeAddrs} (φc : Addr → Nat) {a : Nat} {val : Value}
    (hc : valueCheck v N a val = true) : ValueRepr m N φc a val := by
  cases val with
  | null =>
    simp only [valueCheck, beq_iff_eq] at hc
    exact h.readLE hc
  | bool b =>
    simp only [valueCheck, Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨h.readLE hc.1, h.readLE hc.2⟩
  | int n =>
    simp only [valueCheck, Bool.and_eq_true, beq_iff_eq] at hc
    refine ⟨h.readLE hc.1, ?_⟩
    cases hr : readLEv v (a + 8) 8 with
    | none => rw [hr] at hc; cases hc.2
    | some w =>
      rw [hr] at hc
      simp only [readI64, read64, h.readLE hr, Option.map_some]
      exact hc.2
  | str s =>
    simp only [valueCheck, Bool.and_eq_true, beq_iff_eq] at hc
    refine ⟨h.readLE hc.1, ?_⟩
    cases hr : readLEv v (a + 8) 8 with
    | none => rw [hr] at hc; cases hc.2
    | some p =>
      rw [hr] at hc
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      exact ⟨p, h.readLE hr, hc.2.1, cstrIs_sound h hc.2.2⟩
  | closure _ => cases hc
  | native f =>
    simp only [valueCheck, Bool.and_eq_true, beq_iff_eq] at hc
    refine ⟨h.readLE hc.1.1, ?_, h.readLE hc.2⟩
    have h2 := hc.1.2
    cases hr : readLEv v (a + 8) 8 with
    | none => rw [hr] at h2; cases h2
    | some p =>
      rw [hr] at h2
      exact ⟨p, h.readLE hr, cstrIs_sound h h2⟩

/-! ## Frames -/

/-- Bindings `i … ` of a frame: name pointers from `pn`, values from `pv`. -/
def bindingsCheck (v : Nat → Option (BitVec 8)) (N : NativeAddrs) (pn pv : Nat) :
    Nat → List (String × Value) → Bool
  | _, [] => true
  | i, (x, val) :: rest =>
    (match readLEv v (pn + 8 * i) 8 with
     | some q => cstrIs v q x
     | none => false) &&
    valueCheck v N (pv + 24 * i) val && bindingsCheck v N pn pv (i + 1) rest

theorem bindingsCheck_sound {m : Mem} {v : Nat → Option (BitVec 8)} (h : PartialView m v)
    {N : NativeAddrs} (φc : Addr → Nat) {pn pv : Nat} :
    ∀ {vars : List (String × Value)} {i : Nat}, bindingsCheck v N pn pv i vars = true →
      ∀ j, (hj : j < vars.length) →
        (∃ q, read64 m (pn + 8 * (i + j)) = some q ∧ CString m q (vars[j].1)) ∧
        ValueRepr m N φc (pv + 24 * (i + j)) (vars[j].2) := by
  intro vars
  induction vars with
  | nil => intro i _ j hj; cases hj
  | cons b rest ih =>
    intro i hc j hj
    obtain ⟨x, val⟩ := b
    simp only [bindingsCheck, Bool.and_eq_true] at hc
    obtain ⟨⟨hn, hv⟩, hr⟩ := hc
    cases j with
    | zero =>
      refine ⟨?_, by simpa using valueCheck_sound h φc hv⟩
      cases hq : readLEv v (pn + 8 * i) 8 with
      | none => rw [hq] at hn; cases hn
      | some q =>
        rw [hq] at hn
        exact ⟨q, by simpa [read64] using h.readLE hq, by simpa using cstrIs_sound h hn⟩
    | succ j =>
      have := ih hr j (by simp at hj; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

/-- A parentless `Env` at `e` holding `f`'s bindings. -/
def frameCheck (v : Nat → Option (BitVec 8)) (N : NativeAddrs) (e : Nat) (f : Vsa.While.Frame) : Bool :=
  f.parent.isNone &&
  readLEv v e 4 == some f.vars.length &&
  (match readLEv v (e + 4) 4 with
   | some cap => decide (f.vars.length ≤ cap)
   | none => false) &&
  (match readLEv v (e + 8) 8, readLEv v (e + 16) 8 with
   | some pn, some pv => bindingsCheck v N pn pv 0 f.vars
   | _, _ => false) &&
  readLEv v (e + 24) 8 == some 0

theorem frameCheck_sound {m : Mem} {v : Nat → Option (BitVec 8)} (h : PartialView m v)
    {N : NativeAddrs} (φf φc : Addr → Nat) {e : Nat} {f : Vsa.While.Frame}
    (hc : frameCheck v N e f = true) : FrameRepr m N φf φc e f := by
  obtain ⟨parent, vars⟩ := f
  simp only [frameCheck, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hc
  obtain ⟨⟨⟨⟨hp, hcount⟩, hcap⟩, harr⟩, hpar⟩ := hc
  subst hp
  refine ⟨h.readLE hcount, ?_, ?_, h.readLE hpar⟩
  · cases hr : readLEv v (e + 4) 4 with
    | none => rw [hr] at hcap; cases hcap
    | some cap =>
      rw [hr] at hcap
      exact ⟨cap, h.readLE hr, of_decide_eq_true hcap⟩
  · cases hn : readLEv v (e + 8) 8 with
    | none => rw [hn] at harr; cases harr
    | some pn =>
      cases hv : readLEv v (e + 16) 8 with
      | none => rw [hn, hv] at harr; cases harr
      | some pv =>
        rw [hn, hv] at harr
        refine ⟨pn, pv, h.readLE hn, h.readLE hv, fun i hi => ?_⟩
        simpa using bindingsCheck_sound h φc harr i hi

/-! ## The initial store -/

/-- The global frame `interp_init` builds. -/
def initFrame : Vsa.While.Frame := initSt.store.frames[0]

/-- The initial store is its one frame, placed in the arena. -/
theorem storeRepr_initSt {m : Mem} {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat}
    (hf : FrameRepr m N φf φc (φf 0) initFrame)
    (ha : A.contains (φf 0) 32 ∧ φf 0 % 8 = 0) : StoreRepr m N A φf φc initSt.store where
  frames := by
    intro fa hfa
    have : fa = 0 := by change fa < 1 at hfa; omega
    subst this
    exact hf
  closures := by intro ca hca; change ca < 0 at hca; omega
  φf_inj := by intro a b ha hb _; change a < 1 at ha; change b < 1 at hb; omega
  φc_inj := by intro a b ha _ _; change a < 0 at ha; omega
  frames_arena := by
    intro fa hfa
    have : fa = 0 := by change fa < 1 at hfa; omega
    subst this
    exact ha
  closures_arena := by intro ca hca; change ca < 0 at hca; omega

end Vsa.Sim.Boot
