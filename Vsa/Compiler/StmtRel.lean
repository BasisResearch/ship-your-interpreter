import Vsa.Compiler.ExprSim
import Vsa.Compiler.PrintInt

/-!
# Frame parents are stable

Store operations only ever append frames or rewrite a frame's variables, so the
parent of an existing frame never changes (`SameParents`). A block allocates its
frame with the enclosing environment as parent; stability lets the block's exit
recover the enclosing chain (`Chain.tail`).
-/

namespace Vsa.Compiler

open Vsa.While Vsa.Sim

/-- `s'` extends `s` without changing any existing frame's parent. -/
def SameParents (s s' : Store) : Prop :=
  s.frames.size ≤ s'.frames.size ∧
    ∀ j, j < s.frames.size → (s'.frames[j]?).map Frame.parent = (s.frames[j]?).map Frame.parent

theorem SameParents.refl (s : Store) : SameParents s s := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem SameParents.trans {s1 s2 s3 : Store} (h1 : SameParents s1 s2) (h2 : SameParents s2 s3) :
    SameParents s1 s3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun j hj => (h2.2 j (Nat.lt_of_lt_of_le hj h1.1)).trans (h1.2 j hj)⟩

theorem sameParents_modify (s : Store) (a : Nat) (g : Frame → Frame) (hg : ∀ f, (g f).parent = f.parent) :
    SameParents s { s with frames := s.frames.modify a g } := by
  refine ⟨by simp, fun j _ => ?_⟩
  rw [Array.getElem?_modify]
  by_cases h : a = j
  · subst h; cases s.frames[a]? <;> simp [hg]
  · simp [h]

theorem sameParents_set {s s' : Store} {x : String} {v : Value} :
    ∀ (gas : Nat) (a : Addr), s.set gas a x v = some s' → SameParents s s'
  | 0, _, h => by simp [Store.set] at h
  | gas + 1, a, h => by
    simp only [Store.set] at h
    cases hf : s.frames[a]? with
    | none => simp [hf] at h
    | some f =>
      simp only [hf, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · cases h; exact sameParents_modify _ _ _ (fun _ => rfl)
      · split at h
        · exact sameParents_set gas _ h
        · cases h

theorem sameParents_define (s : Store) (a : Addr) (x : String) (v : Value) :
    SameParents s (s.define a x v) :=
  sameParents_modify _ _ _ (fun _ => rfl)

theorem sameParents_alloc (s : Store) (p : Option Addr) :
    SameParents s (s.allocFrame p).1 := by
  refine ⟨by simp [Store.allocFrame], fun j hj => ?_⟩
  simp [Store.allocFrame, Array.getElem?_push, Nat.ne_of_lt hj]

theorem EvalE.sameParents : ∀ (e : Expr), Simple e → ∀ {st : St} {d : Nat} {env : Addr} {st' : St}
    {v : Value}, EvalE st d env e st' v → SameParents st.store st'.store
  | .int _, _, _, _, _, _, _, h => by cases h; exact .refl _
  | .bool _, _, _, _, _, _, _, h => by cases h; exact .refl _
  | .var _, _, _, _, _, _, _, h => by cases h; exact .refl _
  | .assign _ e, hs, _, _, _, _, _, h => by
    cases h with | assign _ _ _ _ _ _ _ _ he hset =>
    exact (EvalE.sameParents e hs he).trans (sameParents_set _ _ hset)
  | .binary _ l r, hs, _, _, _, _, _, h => by
    cases h with | binary _ _ _ _ _ _ _ _ _ _ _ hl hr _ =>
    exact (EvalE.sameParents l hs.1 hl).trans (EvalE.sameParents r hs.2 hr)
  | .unary .neg e, hs, _, _, _, _, _, h => by
    cases h with | neg _ _ _ _ _ _ he => exact EvalE.sameParents e hs he
  | .unary .not e, hs, _, _, _, _, _, h => by
    cases h with | not _ _ _ _ _ _ he => exact EvalE.sameParents e hs he
  | .str _, h, _, _, _, _, _, _ => h.elim
  | .null, h, _, _, _, _, _, _ => h.elim
  | .logical _ _ _, h, _, _, _, _, _, _ => h.elim
  | .call _ _, h, _, _, _, _, _, _ => h.elim
  | .fn _ _ _, h, _, _, _, _, _, _ => h.elim

/-- A chain whose head frame has parent `p` continues at `p`. -/
theorem Chain.tail {s : Store} {m : Mem} {e p : Addr} {f : List (String × Nat)} {g : Scope}
    (h : Chain s m e (f :: g)) (hg : g ≠ []) (hp : (s.frames[e]?).map Frame.parent = some (some p)) :
    Chain s m p g := by
  match g, h with
  | [], _ => exact absurd rfl hg
  | g0 :: gs, h =>
    obtain ⟨fr, p', hfr, hpar, -, -, hc⟩ := h
    rw [hfr] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    rw [hpar] at hp; cases hp
    exact hc

/-- A block's frame keeps its parent. -/
theorem parent_of_alloc (s : Store) (env : Addr) :
    ((s.allocFrame (some env)).1.frames[(s.allocFrame (some env)).2]?).map Frame.parent
      = some (some env) := by
  simp [Store.allocFrame]

theorem SameParents.parent {s s' : Store} (h : SameParents s s') {j : Nat} {q : Option Addr}
    (hq : (s.frames[j]?).map Frame.parent = some q) : (s'.frames[j]?).map Frame.parent = some q := by
  have hj : j < s.frames.size := by
    cases hs : s.frames[j]? with
    | none => rw [hs] at hq; cases hq
    | some _ => exact (Array.getElem?_eq_some_iff.mp hs).1
  rw [h.2 j hj, hq]

end Vsa.Compiler
