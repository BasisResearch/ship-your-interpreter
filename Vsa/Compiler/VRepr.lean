import Vsa.Compiler.RTDisplay

/-!
# Values as machine words

`VRepr H m h v t p`: the word pair `(t, p)` represents the value `v`, where `H`
maps semantic closures to their objects, `m` is the memory, and `h` bounds the
object heap (strings lie below it). `CloOK` says every closure of the store has
an object with its print and concatenation renderings. From these, `display`
and `catstr` print and render exactly `Value.display` and `Value.catDisplay`
(`dispW_of_repr`, `catW_of_repr`).
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

/-- 64-bit integers. -/
def I64 (n : Int) : Prop := -2 ^ 63 ≤ n ∧ n < 2 ^ 63

/-- The machine id of a native. -/
def natId : NativeFn → BitVec 64
  | .print => 0
  | .println => 1
  | .assert => 2

/-- Where the semantic closures' objects are. -/
abbrev CloMap := List Nat

/-- Word pair `(t, p)` represents `v`. -/
def VRepr (H : CloMap) (m : Mem) (h : Nat) : Value → BitVec 64 → BitVec 64 → Prop
  | .null, t, p => t = 0 ∧ p = 0
  | .bool b, t, p => t = 1 ∧ p = (if b then 1 else 0)
  | .int n, t, p => t = 2 ∧ p = BitVec.ofInt 64 n ∧ I64 n
  | .str s, t, p => t = 3 ∧ StrBelow m h p.toNat s.toList
  | .closure a, t, p => t = 4 ∧ H[a]? = some p.toNat
  | .native f, t, p => t = 5 ∧ p = natId f

/-- How a closure prints. -/
def dispName : Option String → String
  | some n => s!"<fn {n}>"
  | none => "<fn>"

/-- How a closure renders when concatenated. -/
def catName : Option String → String
  | some n => fnCatRender n
  | none => "<fn>"

/-- The object of a closure named `name` at `p`, whose print and concatenation
renderings are the string objects at `d` and `c` below `h`. -/
structure CloObj (m : Mem) (h p : Nat) (name : Option String) (d c : Nat) : Prop where
  lo : tohostAddr + 16 ≤ p
  hi : p + 32 ≤ 2 ^ 32
  al : p % 8 = 0
  disp : rdW m (p + 16) = BitVec.ofNat 64 d
  dispStr : StrBelow m h d (dispName name).toList
  cat : rdW m (p + 24) = BitVec.ofNat 64 c
  catStr : StrBelow m h c (catName name).toList

/-- Every closure of the store has its object. -/
structure CloOK (H : CloMap) (s : Store) (m : Mem) (h : Nat) : Prop where
  len : H.length = s.closures.size
  obj : ∀ (a : Nat) (cd : ClosureData) (p : Nat), s.closures[a]? = some cd → H[a]? = some p →
    ∃ d c, CloObj m h p cd.name d c

theorem dispW_of_repr {H : CloMap} {s : Store} {m : Mem} {h : Nat} {v : Value} {t p : BitVec 64}
    (hv : VRepr H m h v t p) (hc : CloOK H s m h) : DispW m t p (v.display s).toList := by
  cases v with
  | null => obtain ⟨rfl, rfl⟩ := hv; simp [DispW, Value.display]
  | bool b => obtain ⟨rfl, rfl⟩ := hv; cases b <;> simp [DispW, Value.display]
  | int n =>
    obtain ⟨rfl, rfl, h1, h2⟩ := hv
    simp only [DispW, Value.display, toInt_ofInt_small n h1 h2, if_true]
  | str s0 => obtain ⟨rfl, hs⟩ := hv; simp [DispW, Value.display]; exact hs.str
  | closure a =>
    obtain ⟨rfl, ha⟩ := hv
    have hlt : a < s.closures.size := by
      have := (List.getElem?_eq_some_iff.mp ha).1; rw [← hc.len]; exact this
    obtain ⟨cd, hcd⟩ : ∃ cd, s.closures[a]? = some cd := ⟨_, Array.getElem?_eq_getElem hlt⟩
    obtain ⟨d, c, ho⟩ := hc.obj a cd _ hcd ha
    simp only [DispW, show (4 : BitVec 64) ≠ 2 by decide, show (4 : BitVec 64) ≠ 3 by decide,
      if_false, if_true, Value.display, hcd]
    refine ⟨d, ho.disp, ?_, ho.lo, ho.hi⟩
    have := ho.dispStr.str
    cases hn : cd.name with
    | none => simp only [hn, dispName] at this; exact this
    | some n => simp only [hn, dispName] at this; exact this
  | native f => obtain ⟨rfl, rfl⟩ := hv; cases f <;> simp [DispW, Value.display, natId, natDisp]

theorem catW_of_repr {H : CloMap} {s : Store} {m : Mem} {h : Nat} {v : Value} {t p : BitVec 64}
    (hv : VRepr H m h v t p) (hc : CloOK H s m h) : CatW m h t p (v.catDisplay s).toList := by
  cases v with
  | null => obtain ⟨rfl, rfl⟩ := hv; simp [CatW, Value.catDisplay, Value.display]
  | bool b => obtain ⟨rfl, rfl⟩ := hv; cases b <;> simp [CatW, Value.catDisplay, Value.display]
  | int n =>
    obtain ⟨rfl, rfl, h1, h2⟩ := hv
    simp only [CatW, Value.catDisplay, Value.display, toInt_ofInt_small n h1 h2]
    simp
  | str s0 => obtain ⟨rfl, hs⟩ := hv; simp [CatW, Value.catDisplay, Value.display]; exact hs
  | closure a =>
    obtain ⟨rfl, ha⟩ := hv
    have hlt : a < s.closures.size := by
      have := (List.getElem?_eq_some_iff.mp ha).1; rw [← hc.len]; exact this
    obtain ⟨cd, hcd⟩ : ∃ cd, s.closures[a]? = some cd := ⟨_, Array.getElem?_eq_getElem hlt⟩
    obtain ⟨d, c, ho⟩ := hc.obj a cd _ hcd ha
    simp only [CatW, show (4 : BitVec 64) ≠ 2 by decide, show (4 : BitVec 64) ≠ 3 by decide,
      if_false, if_true, Value.catDisplay, hcd]
    refine ⟨c, ho.cat, ?_, ho.lo, ho.hi⟩
    have := ho.catStr
    cases hn : cd.name with
    | none => simp only [hn, catName] at this; exact this
    | some n => simp only [hn, catName] at this; exact this
  | native f => obtain ⟨rfl, rfl⟩ := hv; cases f <;> simp [CatW, Value.catDisplay]

/-- The value `v` is in `(a0, a1)`. -/
def InA (H : CloMap) (m : Mem) (h : Nat) (L : GRegs) (v : Value) : Prop :=
  ∃ t p, Has L a0 t ∧ Has L a1 p ∧ VRepr H m h v t p

theorem VRepr.tag_int {H : CloMap} {m : Mem} {h : Nat} {v : Value} {t p : BitVec 64}
    (hv : VRepr H m h v t p) : t = 2 ↔ ∃ n, v = .int n := by
  cases v <;> simp only [VRepr] at hv <;> (obtain ⟨rfl, _⟩ := hv) <;> simp <;> decide

end Vsa.Compiler
