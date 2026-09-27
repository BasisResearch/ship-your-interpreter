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
  lo : objBase ≤ p
  hi : p + 32 ≤ h
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
    (hv : VRepr H m h v t p) (hc : CloOK H s m h) (hh : h ≤ objEnd) :
    DispW m t p (v.display s).toList := by
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
    have ho1 := ho.lo; have ho2 := ho.hi
    have hob : objBase = 0x90000000 := rfl
    have hoe : objEnd = 0xE0000000 := rfl
    have ht : tohostAddr = 0x8001ad00 := rfl
    refine ⟨d, ho.disp, ?_, by omega, by omega⟩
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
    refine ⟨c, ho.cat, ?_, ho.lo, ho.hi, ho.al⟩
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

theorem VRepr.tag_str {H : CloMap} {m : Mem} {h : Nat} {v : Value} {t p : BitVec 64}
    (hv : VRepr H m h v t p) : t = 3 → ∃ s, v = .str s := by
  cases v <;> simp only [VRepr] at hv <;> (obtain ⟨rfl, _⟩ := hv) <;> simp <;> decide

/-- The tag of a value. -/
def tagOf : Value → BitVec 64
  | .null => 0 | .bool _ => 1 | .int _ => 2 | .str _ => 3 | .closure _ => 4 | .native _ => 5

theorem VRepr.tag {H : CloMap} {m : Mem} {h : Nat} {v : Value} {t p : BitVec 64}
    (hv : VRepr H m h v t p) : t = tagOf v := by
  cases v <;> simp only [VRepr] at hv <;> exact hv.1

theorem equal_tag {l r : Value} (h : l.equal r = true) : tagOf l = tagOf r := by
  cases l <;> cases r <;> simp_all [Value.equal, tagOf]

/-- Closure objects are at distinct addresses. -/
def CloInj (H : CloMap) : Prop := ∀ (a b p : Nat), H[a]? = some p → H[b]? = some p → a = b

theorem ofInt_inj {a b : Int} (ha : I64 a) (hb : I64 b) (h : BitVec.ofInt 64 a = BitVec.ofInt 64 b) :
    a = b := by
  have := congrArg BitVec.toInt h
  rwa [toInt_ofInt_small a ha.1 ha.2, toInt_ofInt_small b hb.1 hb.2] at this

theorem natId_inj {f g : NativeFn} (h : natId f = natId g) : f = g := by
  cases f <;> cases g <;> simp_all [natId] <;> revert h <;> decide

/-- For equal tags other than strings, payload equality is value equality. -/
theorem payload_eq_iff {H : CloMap} {m : Mem} {h : Nat} {l r : Value} {t p1 p2 : BitVec 64}
    (hinj : CloInj H) (hl : VRepr H m h l t p1) (hr : VRepr H m h r t p2) (h3 : t ≠ 3) :
    p1 = p2 ↔ l.equal r = true := by
  cases l <;> cases r <;> simp only [VRepr] at hl hr <;>
    (obtain ⟨rfl, hl⟩ := hl) <;> (obtain ⟨ht, hr⟩ := hr) <;> simp only [Value.equal] <;>
    first | (exact absurd ht (by decide)) | skip
  · subst hl hr; simp
  · rename_i a b; subst hl hr; cases a <;> cases b <;> simp <;> decide
  · rename_i a b; obtain ⟨rfl, ha⟩ := hl; obtain ⟨rfl, hb⟩ := hr
    constructor
    · intro e; simp [ofInt_inj ha hb e]
    · intro e; simp at e; rw [e]
  · exact absurd rfl h3
  · rename_i a b
    constructor
    · intro e; subst e; have := hinj a b _ hl hr; simp [this]
    · intro e
      have e' : a = b := by simpa using e
      subst e'
      rw [hl] at hr
      exact BitVec.eq_of_toNat_eq (Option.some.inj hr)
  · rename_i f g; subst hl hr
    constructor
    · intro e; simp [natId_inj e]
    · intro e; simp at e; rw [e]

/-- `m'` agrees with `m` on the object heap below `h`. -/
def ObjAgree (m m' : Mem) (h : Nat) : Prop :=
  ∀ a, a % 8 = 0 → objBase ≤ a → a + 8 ≤ h → rdW m' a = rdW m a

theorem StrBelow.mono {m m' : Mem} {h h' q : Nat} {cs : List Char} (hs : StrBelow m h q cs)
    (hag : ObjAgree m m' h) (hh : h ≤ h') : StrBelow m' h' q cs :=
  ⟨hs.str.transport (fun a h1 h2 h3 => hag a h3 (by have := hs.lo; omega) (by have := hs.hi; omega)),
    hs.lo, by have := hs.hi; omega⟩

theorem CatW.mono {m m' : Mem} {h h' : Nat} {t p : BitVec 64} {cs : List Char} (hc : CatW m h t p cs)
    (hag : ObjAgree m m' h) (hh : h ≤ h') : CatW m' h' t p cs := by
  unfold CatW at hc ⊢
  split
  · next h3 => rw [if_pos h3] at hc; exact hc.mono hag hh
  · next h3 =>
    rw [if_neg h3] at hc
    split
    · next h2 => rw [if_pos h2] at hc; exact hc
    · next h2 =>
      rw [if_neg h2] at hc
      split
      · next h4 =>
        rw [if_pos h4] at hc
        obtain ⟨d, hd, hs, hp1, hp2, hp3⟩ := hc
        exact ⟨d, by rw [hag _ (by omega) (by omega) (by omega)]; exact hd, hs.mono hag hh, hp1, by omega, hp3⟩
      · next h4 => rw [if_neg h4] at hc; exact hc

theorem VRepr.mono {H : CloMap} {m m' : Mem} {h h' : Nat} {v : Value} {t p : BitVec 64}
    (hv : VRepr H m h v t p) (hag : ObjAgree m m' h) (hh : h ≤ h') : VRepr H m' h' v t p := by
  cases v <;> simp only [VRepr] at hv ⊢
  all_goals first | exact hv | exact ⟨hv.1, hv.2.mono hag hh⟩

end Vsa.Compiler
