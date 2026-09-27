import Vsa.Compiler.Frag
import Vsa.Compiler.Subset

/-!
# The store relation

`Chain s m env Γ` relates the semantics' frame chain starting at `env` to the
compiler's scope `Γ` and the memory `m`: the frame at each chain position binds
exactly the names of the corresponding scope (plus the natives in the global
frame), each to the integer held in its static slot. The lemmas give the
semantic effect of lookup, assignment, declaration and frame allocation.
-/

namespace Vsa.Compiler

open Vsa.While Vsa.Sim

/-- The integer held in variable slot `i`. -/
def slotV (m : Mem) (i : Nat) : Int := (rdW m (varAddr i)).toInt

/-- The global frame's initial bindings. -/
def nativeVars : List (String × Value) :=
  [("print", .native .print), ("println", .native .println), ("assert", .native .assert)]

/-- A frame binds the scope's names to their slot values (and, in the global
frame, the natives). -/
def FrameOK (fr : Frame) (f : List (String × Nat)) (m : Mem) (global : Bool) : Prop :=
  ∀ x, fr.vars.find? (·.1 == x) =
    match f.lookup x with
    | some i => some (x, .int (slotV m i))
    | none => if global then nativeVars.find? (·.1 == x) else none

/-- The frame chain from `env` realizes the scope `Γ` in memory `m`. -/
def Chain (s : Store) (m : Mem) : Addr → Scope → Prop
  | _, [] => False
  | env, [f] => env = 0 ∧ ∃ fr, s.frames[0]? = some fr ∧ fr.parent = none ∧ FrameOK fr f m true
  | env, f :: g :: gs => ∃ fr p, s.frames[env]? = some fr ∧ fr.parent = some p ∧ p < env ∧
      FrameOK fr f m false ∧ Chain s m p (g :: gs)

/-- The slot numbers of a scope. -/
def Scope.slots (Γ : Scope) : List Nat := (Γ.flatMap id).map Prod.snd

/-- Scope names, for the subset predicate. -/
def Scope.names (Γ : Scope) : NScope := Γ.map (·.map Prod.fst)

/-! ## Lookup -/

theorem Chain.env_lt {s : Store} {m : Mem} : ∀ {env : Addr} {Γ : Scope},
    Chain s m env Γ → env < s.frames.size
  | env, [], h => h.elim
  | env, [f], h => by
    obtain ⟨rfl, fr, hfr, -⟩ := h
    exact (Array.getElem?_eq_some_iff.mp hfr).1
  | env, f :: g :: gs, h => by
    obtain ⟨fr, p, hfr, -⟩ := h
    exact (Array.getElem?_eq_some_iff.mp hfr).1

theorem find?_of_FrameOK_some {fr : Frame} {f : List (String × Nat)} {m : Mem} {b : Bool}
    (h : FrameOK fr f m b) {x : String} {i : Nat} (hx : f.lookup x = some i) :
    fr.vars.find? (·.1 == x) = some (x, .int (slotV m i)) := by
  rw [h x, hx]

theorem find?_of_FrameOK_none {fr : Frame} {f : List (String × Nat)} {m : Mem}
    (h : FrameOK fr f m false) {x : String} (hx : f.lookup x = none) :
    fr.vars.find? (·.1 == x) = none := by
  rw [h x, hx]; rfl

theorem Chain.lookup {s : Store} {m : Mem} {x : String} {i : Nat} : ∀ {env : Addr} {Γ : Scope}
    (gas : Nat), Chain s m env Γ → env < gas → Γ.resolve x = some i →
    s.lookup gas env x = some (.int (slotV m i))
  | env, [], _, h, _, _ => h.elim
  | env, [f], gas + 1, h, _, hr => by
    obtain ⟨rfl, fr, hfr, -, hok⟩ := h
    simp only [Scope.resolve] at hr
    cases hf : f.lookup x with
    | none => rw [hf] at hr; cases hr
    | some j =>
      rw [hf] at hr; cases hr
      simp [Store.lookup, hfr, find?_of_FrameOK_some hok hf]
  | env, f :: g :: gs, gas + 1, h, hg, hr => by
    obtain ⟨fr, p, hfr, hp, hlt, hok, hc⟩ := h
    simp only [Scope.resolve] at hr
    cases hf : f.lookup x with
    | some j =>
      rw [hf] at hr; cases hr
      simp [Store.lookup, hfr, find?_of_FrameOK_some hok hf]
    | none =>
      rw [hf] at hr
      simp only [Store.lookup, hfr, find?_of_FrameOK_none hok hf, hp, Option.bind_eq_bind,
        Option.bind_some]
      exact Chain.lookup gas hc (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ hg)) hr

theorem Chain.get? {s : Store} {m : Mem} {env : Addr} {Γ : Scope} {x : String} {i : Nat}
    (h : Chain s m env Γ) (hr : Γ.resolve x = some i) :
    s.get? env x = some (.int (slotV m i)) :=
  h.lookup s.frames.size h.env_lt hr

/-! ## Memory transport -/

theorem lookup_mem {x : String} {i : Nat} : ∀ {f : List (String × Nat)}, f.lookup x = some i → (x, i) ∈ f
  | [], h => by simp at h
  | (y, j) :: f, h => by
    simp only [List.lookup_cons] at h
    split at h
    · next heq => cases h; simp at heq; subst heq; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem FrameOK.transport {fr : Frame} {f : List (String × Nat)} {m m' : Mem} {b : Bool}
    (h : FrameOK fr f m b) (hm : ∀ p ∈ f, slotV m' p.2 = slotV m p.2) : FrameOK fr f m' b := by
  intro x
  rw [h x]
  cases hf : f.lookup x with
  | none => rfl
  | some i =>
    simp [hm _ (lookup_mem hf)]

theorem Chain.transport {s : Store} {m m' : Mem} : ∀ {env : Addr} {Γ : Scope},
    Chain s m env Γ → (∀ i ∈ Γ.slots, slotV m' i = slotV m i) → Chain s m' env Γ
  | env, [], h, _ => h.elim
  | env, [f], h, hm => by
    obtain ⟨rfl, fr, hfr, hp, hok⟩ := h
    refine ⟨rfl, fr, hfr, hp, hok.transport fun p hp => hm _ ?_⟩
    simp [Scope.slots]; exact ⟨p.1, hp⟩
  | env, f :: g :: gs, h, hm => by
    obtain ⟨fr, p, hfr, hpp, hlt, hok, hc⟩ := h
    refine ⟨fr, p, hfr, hpp, hlt, hok.transport fun q hq => hm _ ?_, hc.transport fun i hi => hm i ?_⟩
    · simp [Scope.slots]; exact .inl ⟨q.1, hq⟩
    · simp only [Scope.slots, List.flatMap_cons, List.map_append, List.mem_append] at hi ⊢
      exact .inr hi

/-- Writes outside the variable-slot region leave slot values unchanged. -/
theorem slotV_write_low (m : Mem) (a : Nat) (w : BitVec 64) (i : Nat) (ha : a + 8 ≤ varBase) :
    slotV (applyW m (a, 8, w)) i = slotV m i := by
  unfold slotV
  rw [rdW_write_other _ _ _ _ (by unfold varAddr; omega)]

theorem slotV_write_self (m : Mem) (i : Nat) (v : Int) (hv : InRange v) :
    slotV (applyW m (varAddr i, 8, BitVec.ofInt 64 v)) i = v := by
  unfold slotV
  rw [rdW_write, BitVec.toInt_ofInt]
  obtain ⟨h1, h2⟩ := hv
  apply Int.bmod_eq_of_le <;> simp <;> omega

theorem slotV_write_other (m : Mem) (i j : Nat) (w : BitVec 64) (h : j ≠ i) :
    slotV (applyW m (varAddr i, 8, w)) j = slotV m j := by
  unfold slotV
  rw [rdW_write_other _ _ _ _ (by unfold varAddr; omega)]

/-! ## Store changes outside the chain -/

theorem Chain.frames_congr {s s' : Store} {m : Mem} : ∀ {env : Addr} {Γ : Scope},
    Chain s m env Γ → (∀ j, j ≤ env → s'.frames[j]? = s.frames[j]?) → Chain s' m env Γ
  | env, [], h, _ => h.elim
  | env, [f], h, hs => by
    obtain ⟨rfl, fr, hfr, hp, hok⟩ := h
    exact ⟨rfl, fr, by rw [hs 0 (Nat.le_refl _), hfr], hp, hok⟩
  | env, f :: g :: gs, h, hs => by
    obtain ⟨fr, p, hfr, hpp, hlt, hok, hc⟩ := h
    exact ⟨fr, p, by rw [hs env (Nat.le_refl _), hfr], hpp, hlt, hok,
      hc.frames_congr fun j hj => hs j (Nat.le_trans hj (Nat.le_of_lt hlt))⟩

/-! ## Assignment -/

theorem any_of_find? {l : List (String × Value)} {x : String} {q : String × Value}
    (h : l.find? (·.1 == x) = some q) : l.any (·.1 == x) = true := by
  rw [List.any_eq_true]
  exact ⟨q, List.mem_of_find?_eq_some h, by have := List.find?_some h; simpa using this⟩

theorem not_any_of_find? {l : List (String × Value)} {x : String}
    (h : l.find? (·.1 == x) = none) : l.any (·.1 == x) = false := by
  rw [List.find?_eq_none] at h
  simpa using h

/-- Rebinding `x` in a frame's variable list. -/
def rebind (x : String) (v : Value) (vars : List (String × Value)) : List (String × Value) :=
  vars.map fun p => if p.1 == x then (x, v) else p

theorem find?_rebind (x y : String) (v : Value) (vars : List (String × Value)) :
    (rebind x v vars).find? (·.1 == y) =
      if y = x then (vars.find? (·.1 == y)).map (fun _ => (x, v)) else vars.find? (·.1 == y) := by
  unfold rebind
  rw [List.find?_map]
  have hc : ((·.1 == y) ∘ fun p : String × Value => if p.1 == x then (x, v) else p) = (·.1 == y) := by
    funext p; simp only [Function.comp]; split <;> simp_all
  rw [hc]
  cases hq : vars.find? (·.1 == y) with
  | none => simp
  | some q =>
    have := List.find?_some hq
    simp only [Option.map_some]
    by_cases hyx : y = x
    · subst hyx; simp_all
    · simp only [hyx, if_false]
      have hq1 : q.1 = y := by simpa using this
      have : (q.fst == x) = false := by rw [hq1]; simpa using hyx
      simp [this]

theorem nodup_snd_inj {f : List (String × Nat)} (hnd : (f.map Prod.snd).Nodup) {a b : String}
    {j : Nat} (ha : (a, j) ∈ f) (hb : (b, j) ∈ f) : a = b := by
  induction f with
  | nil => simp at ha
  | cons q f ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
    · rw [← ha] at hb; cases hb; rfl
    · exact absurd ⟨_, hb, by rw [← ha]⟩ hnd.1
    · exact absurd ⟨_, ha, by rw [← hb]⟩ hnd.1
    · exact ih hnd.2 ha hb

theorem FrameOK.rebind {fr : Frame} {f : List (String × Nat)} {m m' : Mem} {b : Bool}
    {x : String} {i : Nat} {v : Int} (h : FrameOK fr f m b) (hx : f.lookup x = some i)
    (hnd : (f.map Prod.snd).Nodup) (hv : slotV m' i = v)
    (ho : ∀ p ∈ f, p.2 ≠ i → slotV m' p.2 = slotV m p.2) :
    FrameOK { fr with vars := rebind x (.int v) fr.vars } f m' b := by
  intro y
  simp only
  rw [find?_rebind]
  by_cases hyx : y = x
  · subst hyx; rw [if_pos rfl, h y, hx]; simp [hv]
  · rw [if_neg hyx, h y]
    cases hf : f.lookup y with
    | none => rfl
    | some j =>
      have hj := lookup_mem hf
      have hne : j ≠ i := by
        intro e; subst e
        have hi := lookup_mem hx
        exact hyx (nodup_snd_inj hnd hj hi)
      simp [ho _ hj hne]

theorem slots_cons (f : List (String × Nat)) (Γ : Scope) :
    Scope.slots (f :: Γ) = f.map Prod.snd ++ Scope.slots Γ := by
  simp [Scope.slots]

theorem getElem?_modify_self' {α} (xs : Array α) (i : Nat) (g : α → α) {a : α}
    (h : xs[i]? = some a) : (xs.modify i g)[i]? = some (g a) := by
  rw [Array.getElem?_modify]; simp [h]

theorem getElem?_modify_ne' {α} (xs : Array α) (i j : Nat) (g : α → α) (h : i ≠ j) :
    (xs.modify i g)[j]? = xs[j]? := by
  rw [Array.getElem?_modify]; simp [h]

theorem resolve_mem {x : String} {i : Nat} : ∀ {Γ : Scope}, Γ.resolve x = some i → i ∈ Γ.slots
  | [], h => by simp [Scope.resolve] at h
  | f :: g, h => by
    rw [slots_cons]
    simp only [Scope.resolve] at h
    cases hf : f.lookup x with
    | some j => rw [hf] at h; cases h; exact List.mem_append_left _ (List.mem_map_of_mem (lookup_mem hf))
    | none => rw [hf] at h; exact List.mem_append_right _ (resolve_mem h)

theorem Chain.set {s : Store} {m m' : Mem} {x : String} {i : Nat} {v : Int} :
    ∀ {env : Addr} {Γ : Scope} (gas : Nat), Chain s m env Γ → env < gas →
    Γ.resolve x = some i → Γ.slots.Nodup → slotV m' i = v →
    (∀ j ∈ Γ.slots, j ≠ i → slotV m' j = slotV m j) →
    ∃ s', s.set gas env x (.int v) = some s' ∧ Chain s' m' env Γ ∧
      s'.frames.size = s.frames.size ∧ (∀ j, env < j → s'.frames[j]? = s.frames[j]?)
  | env, [], _, h, _, _, _, _, _ => h.elim
  | env, f :: g, gas + 1, h, hg, hr, hnd, hv, ho => by
    rw [slots_cons] at hnd ho
    have hndf := (List.nodup_append.mp hnd).1
    simp only [Scope.resolve] at hr
    cases hf : f.lookup x with
    | some j =>
      rw [hf] at hr; cases hr
      have hi := List.mem_map_of_mem (f := Prod.snd) (lookup_mem hf)
      have hgi : ∀ k ∈ Scope.slots g, k ≠ i := by
        intro k hk e; subst e
        exact (List.nodup_append.mp hnd).2.2 _ hi _ hk rfl
      have hof : ∀ p ∈ f, p.2 ≠ i → slotV m' p.2 = slotV m p.2 :=
        fun p hp hne => ho _ (List.mem_append_left _ (List.mem_map_of_mem hp)) hne
      let upd : Frame → Frame := fun fr => { fr with vars := rebind x (.int v) fr.vars }
      let s' : Store := { s with frames := s.frames.modify env upd }
      match g, h with
      | [], h =>
        obtain ⟨rfl, fr, hfr, hpar, hok⟩ := h
        have hfind := find?_of_FrameOK_some hok hf
        refine ⟨s', ?_, ⟨rfl, upd fr, getElem?_modify_self' _ 0 upd hfr, hpar,
          hok.rebind hf hndf hv hof⟩, by simp [s'], fun j hj => ?_⟩
        · rw [Store.set]
          simp only [hfr, Option.bind_eq_bind, Option.bind_some, any_of_find? hfind, ite_true]
          rfl
        · exact getElem?_modify_ne' _ _ _ _ (Nat.ne_of_lt hj)
      | g0 :: gs, h =>
        obtain ⟨fr, p, hfr, hpar, hlt, hok, hc⟩ := h
        have hfind := find?_of_FrameOK_some hok hf
        refine ⟨s', ?_, ⟨upd fr, p, getElem?_modify_self' _ env upd hfr, hpar, hlt,
          hok.rebind hf hndf hv hof, ?_⟩, by simp [s'], fun j hj => ?_⟩
        · rw [Store.set]
          simp only [hfr, Option.bind_eq_bind, Option.bind_some, any_of_find? hfind, ite_true]
          rfl
        · refine (hc.frames_congr fun j hj => getElem?_modify_ne' _ _ _ _
            (Nat.ne_of_gt (Nat.lt_of_le_of_lt hj hlt))).transport ?_
          intro k hk
          exact ho k (List.mem_append_right _ hk) (hgi k hk)
        · exact getElem?_modify_ne' _ _ _ _ (Nat.ne_of_lt hj)
    | none =>
      rw [hf] at hr
      match g, h with
      | [], _ => simp [Scope.resolve] at hr
      | g0 :: gs, h =>
        obtain ⟨fr, p, hfr, hpar, hlt, hok, hc⟩ := h
        have hfind := find?_of_FrameOK_none hok hf
        obtain ⟨s', hset, hc', hsz, hhi⟩ := Chain.set gas hc (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ hg)) hr
          (List.nodup_append.mp hnd).2.1 hv (fun k hk hne => ho k (List.mem_append_right _ hk) hne)
        refine ⟨s', ?_, ⟨fr, p, by rw [hhi env hlt, hfr], hpar, hlt, ?_, hc'⟩, hsz,
          fun j hj => hhi j (Nat.lt_trans hlt hj)⟩
        · simp [Store.set, hfr, not_any_of_find? hfind, hpar, hset]
        · refine hok.transport fun q hq => ho _ (List.mem_append_left _ (List.mem_map_of_mem hq)) ?_
          intro e
          have hi : i ∈ Scope.slots (g0 :: gs) := resolve_mem hr
          exact (List.nodup_append.mp hnd).2.2 _ (List.mem_map_of_mem hq) _ hi e

end Vsa.Compiler
