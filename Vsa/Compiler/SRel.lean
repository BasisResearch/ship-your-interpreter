import Vsa.Compiler.CodeGen

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

def lookupVar (fr : Frame) (x : String) : Option Value := (fr.vars.find? (·.1 == x)).map (·.2)

abbrev FrMap := List (Nat × List String)

def frSize (L : List String) : Nat := 8 + 16 * L.length

structure FrameAt (H : CloMap) (m : Mem) (h : Nat) (f : Nat) (L : List String) (par : Nat)
    (fr : Frame) : Prop where
  parent : rdW m f = BitVec.ofNat 64 par
  bound : ∀ i x v, L[i]? = some x → lookupVar fr x = some v →
    VRepr H m h v (rdW m (f + 8 + 16 * i)) (rdW m (f + 16 + 16 * i))
  unbound : ∀ i x, L[i]? = some x → lookupVar fr x = none → rdW m (f + 8 + 16 * i) = 6
  names : ∀ x, (lookupVar fr x).isSome → x ∈ L

def parAddr (F : FrMap) (fr : Frame) : Nat :=
  match fr.parent with
  | some b => (F[b]?.map Prod.fst).getD 0
  | none => 0

inductive ChainL (F : FrMap) (s : Store) : Addr → List (List String) → Prop where
  | top {a : Addr} {fr : Frame} {f : Nat} {L : List String} :
    s.frames[a]? = some fr → fr.parent = none → F[a]? = some (f, L) → ChainL F s a [L]
  | cons {a b : Addr} {fr : Frame} {f : Nat} {L L' : List String} {g : List (List String)} :
    s.frames[a]? = some fr → fr.parent = some b → F[a]? = some (f, L) →
    ChainL F s b (L' :: g) → ChainL F s a (L :: L' :: g)

def ParentsLt (s : Store) : Prop :=
  ∀ (a : Nat) (fr : Frame) (b : Nat), s.frames[a]? = some fr → fr.parent = some b → b < a

theorem lookup_step {s : Store} {g : Nat} {a : Addr} {x : String} {fr : Frame}
    (h : s.frames[a]? = some fr) : s.lookup (g + 1) a x =
      match lookupVar fr x with
      | some v => some v
      | none => match fr.parent with
        | some b => s.lookup g b x
        | none => none := by
  cases hf : fr.vars.find? (·.1 == x) with
  | none =>
    cases hq : fr.parent with
    | none => simp [Store.lookup, h, hf, hq, lookupVar]
    | some b => simp [Store.lookup, h, hf, hq, lookupVar]
  | some q => obtain ⟨y, w⟩ := q; simp [Store.lookup, h, hf, lookupVar]

theorem lookup_gas {s : Store} (hp : ParentsLt s) (x : String) :
    ∀ (a g : Nat), a < g → s.lookup g a x = s.lookup (a + 1) a x := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
  intro g hg
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  cases hfr : s.frames[a]? with
  | none => simp [Store.lookup, hfr]
  | some fr =>
    rw [lookup_step hfr, lookup_step hfr]
    cases lookupVar fr x with
    | some v => rfl
    | none =>
      cases hb : fr.parent with
      | none => rfl
      | some b =>
        have hba := hp a fr b hfr hb
        simp only
        rw [ih b hba g' (by omega), ih b hba a hba]

theorem get?_eq {s : Store} (hp : ParentsLt s) {a : Addr} (ha : a < s.frames.size) (x : String) :
    s.get? a x = s.lookup (a + 1) a x := lookup_gas hp x a _ ha

structure StoreRel (F : FrMap) (H : CloMap) (s : Store) (m : Mem) (hF h : Nat) : Prop where
  len : F.length = s.frames.size
  frame : ∀ (a : Nat) (fr : Frame) (f : Nat) (L : List String), s.frames[a]? = some fr →
    F[a]? = some (f, L) → FrameAt H m h f L (parAddr F fr) fr
  region : ∀ (a f : Nat) (L : List String), F[a]? = some (f, L) →
    frameBase ≤ f ∧ f + frSize L ≤ hF ∧ f % 8 = 0 ∧ L.length ≤ 120
  nodup : ∀ (a f : Nat) (L : List String), F[a]? = some (f, L) → L.Nodup
  disjoint : ∀ (a b fa fb : Nat) (La Lb : List String), a < b → F[a]? = some (fa, La) →
    F[b]? = some (fb, Lb) → fa + frSize La ≤ fb
  parents : ParentsLt s
  clo : CloOK H s m h
  inj : CloInj H
  top : hF ≤ frameEnd
  lo : frameBase ≤ hF

end Vsa.Compiler
