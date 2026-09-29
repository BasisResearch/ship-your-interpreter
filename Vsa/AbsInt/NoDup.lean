import Vsa.AbsInt.Chain

/-!
# Binding lists without duplicate names

`env_define` appends a name only when the frame does not bind it, and
`env_set` rewrites values in place, so no frame ever binds a name twice
(`FramesNoDup`). Execution preserves this (`nodup_exec` and siblings). With
it, a frame described by an abstract scope has at most as many bindings as
the scope has names (`vars_length_le`), which bounds the cost of growing
its binding arrays.
-/

namespace Vsa.AbsInt

open Vsa.While AbsOps AbsDom

/-- No frame binds a name twice. -/
def FramesNoDup (s : Store) : Prop :=
  ∀ (a : Addr) (f : Frame), s.frames[a]? = some f → (f.vars.map Prod.fst).Nodup

theorem keys_setVars (vars : List (String × Value)) (x : String) (v : Value) :
    (setVars vars x v).map Prod.fst = vars.map Prod.fst := by
  induction vars with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    rw [setVars_cons]
    by_cases hk : k = x
    · subst hk; simp [ih]
    · simp [hk, ih]

theorem not_mem_keys_of_not_any {vars : List (String × Value)} {x : String}
    (h : vars.any (·.1 == x) = false) : x ∉ vars.map Prod.fst := by
  intro hm
  obtain ⟨⟨k, w⟩, hk, rfl⟩ := List.mem_map.mp hm
  have : vars.any (·.1 == k) = true := List.any_eq_true.mpr ⟨(k, w), hk, by simp⟩
  rw [this] at h
  cases h

theorem nodup_defineVars {vars : List (String × Value)} {x : String} {v : Value}
    (h : (vars.map Prod.fst).Nodup) : ((defineVars vars x v).map Prod.fst).Nodup := by
  unfold defineVars
  cases hany : vars.any (·.1 == x)
  · simp only [Bool.false_eq_true, ↓reduceIte, List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    intro e
    subst e
    exact not_mem_keys_of_not_any hany ha
  · simp only [↓reduceIte, keys_setVars]
    exact h

theorem FramesNoDup.define {s : Store} {a : Addr} {x : String} {v : Value}
    (h : FramesNoDup s) : FramesNoDup (s.define a x v) := by
  intro i f hf
  rw [define_frames] at hf
  split at hf
  · subst_vars
    cases hs : s.frames[i]? with
    | none => rw [hs] at hf; cases hf
    | some g =>
      rw [hs] at hf
      cases hf
      exact nodup_defineVars (h i g hs)
  · exact h i f hf

theorem FramesNoDup.set {s s' : Store} {a : Addr} {x : String} {v : Value} :
    ∀ {g : Nat}, s.set g a x v = some s' → FramesNoDup s → FramesNoDup s'
  | 0, hs, _ => by simp [Store.set] at hs
  | g + 1, hs, h => by
    rw [set_succ] at hs
    cases hf : s.frames[a]? with
    | none => rw [hf] at hs; cases hs
    | some f =>
      rw [hf] at hs
      simp only at hs
      split at hs
      · cases hs
        intro i f' hf'
        simp only [Array.getElem?_modify] at hf'
        split at hf'
        · subst_vars
          rw [hf] at hf'
          cases hf'
          simp only [keys_setVars]
          exact h _ f hf
        · exact h i f' hf'
      · split at hs
        · exact FramesNoDup.set (a := _) hs h
        · cases hs

theorem FramesNoDup.allocFrame {s s' : Store} {p : Option Addr} {a : Addr}
    (halloc : s.allocFrame p = (s', a)) (h : FramesNoDup s) : FramesNoDup s' := by
  simp only [Store.allocFrame, Prod.mk.injEq] at halloc
  obtain ⟨rfl, rfl⟩ := halloc
  intro i f hf
  simp only [Array.getElem?_push] at hf
  split at hf
  · cases hf; simp
  · exact h i f hf

theorem FramesNoDup.frames_eq {s s' : Store} (hfr : s'.frames = s.frames)
    (h : FramesNoDup s) : FramesNoDup s' := by
  intro i f hf
  rw [hfr] at hf
  exact h i f hf

theorem FramesNoDup.foldDefine {frame : Addr} :
    ∀ {xs : List (String × Value)} {s : Store}, FramesNoDup s →
      FramesNoDup (xs.foldl (fun s (x, v) => s.define frame x v) s)
  | [], _, h => h
  | (x, v) :: rest, s, h =>
    FramesNoDup.foldDefine (xs := rest) (s := s.define frame x v) (FramesNoDup.define h)

theorem initSt_nodup : FramesNoDup initSt.store := by
  intro i f hf
  simp only [initSt] at hf
  rcases i with _ | i
  · cases hf; decide
  · simp at hf

theorem FramesNoDup.allocClosure {s s' : Store} {c : ClosureData} {a : Addr}
    (halloc : s.allocClosure c = (s', a)) (h : FramesNoDup s) : FramesNoDup s' := by
  simp only [Store.allocClosure, Prod.mk.injEq] at halloc
  obtain ⟨rfl, rfl⟩ := halloc
  exact h

/-- The preservation motive. -/
abbrev NDM (st st' : St) : Prop := FramesNoDup st.store → FramesNoDup st'.store

set_option hygiene false in
/-- One application of a semantics recursor with the preservation motive. -/
local macro "nodup_rec" r:ident h:term : tactic => `(tactic| (
  refine $r
    (motive_1 := fun st _ _ _ st' _ _ => NDM st st')
    (motive_2 := fun st _ _ _ st' _ _ => NDM st st')
    (motive_3 := fun st _ _ _ st' _ _ => NDM st st')
    (motive_4 := fun st _ _ _ st' _ _ => NDM st st')
    (motive_5 := fun st _ _ _ st' _ => NDM st st')
    (motive_6 := fun st _ _ _ _ _ st' _ _ => NDM st st')
    (motive_7 := fun st _ _ _ st' _ => NDM st st')
    (motive_8 := fun st _ _ _ st' _ => NDM st st')
    (motive_9 := fun st _ _ _ st' _ _ => NDM st st')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ $h
  all_goals intros
  all_goals simp only [NDM] at *
  all_goals intros
  all_goals first
    | assumption
    | (apply FramesNoDup.define; solve_by_elim)
    | (apply FramesNoDup.set (by assumption); solve_by_elim)
    | (apply FramesNoDup.allocClosure (by assumption); assumption)
    | solve_by_elim (maxDepth := 6) [FramesNoDup.allocFrame, FramesNoDup.foldDefine,
        FramesNoDup.frames_eq, FramesNoDup.define]))

theorem nodup_eval {st st' : St} {d : Nat} {env : Addr} {e : Expr} {v : Value}
    (h : EvalE st d env e st' v) : NDM st st' := by nodup_rec EvalE.rec h

theorem nodup_exec {st st' : St} {d : Nat} {env : Addr} {s : Stmt} {status : Status}
    (h : ExecS st d env s st' status) : NDM st st' := by nodup_rec ExecS.rec h

theorem nodup_seq {st st' : St} {d : Nat} {env : Addr} {ss : List Stmt} {status : Status}
    (h : ExecSeq st d env ss st' status) : NDM st st' := by nodup_rec ExecSeq.rec h

theorem nodup_init {st st' : St} {d : Nat} {env : Addr} {i : Option Stmt}
    (h : ExecInit st d env i st') : NDM st st' := by nodup_rec ExecInit.rec h

theorem nodup_for {st st' : St} {d : Nat} {env : Addr} {cnd step : Option Expr} {b : Stmt}
    {status : Status} (h : ForLoop st d env cnd step b st' status) : NDM st st' := by
  nodup_rec ForLoop.rec h

theorem nodup_cond {st st' : St} {d : Nat} {env : Addr} {cnd : Option Expr}
    (h : ForCond st d env cnd st') : NDM st st' := by nodup_rec ForCond.rec h

theorem nodup_step {st st' : St} {d : Nat} {env : Addr} {step : Option Expr}
    (h : ExecStep st d env step st') : NDM st st' := by nodup_rec ExecStep.rec h

/-! ## Binding counts from abstract scopes -/

variable {A : Type} [AbsDom A]

/-- A frame described by a scope binds only names of the scope. -/
theorem vars_length_le {S : Scope A} {vars : List (String × Value)}
    (hS : ScopeOK S vars) (hnd : (vars.map Prod.fst).Nodup) :
    vars.length ≤ (dedup (keys S)).length := by
  have hsub : vars.map Prod.fst ⊆ dedup (keys S) := by
    intro x hx
    rw [mem_dedup]
    by_cases hk : x ∈ keys S
    · exact hk
    exfalso
    have hg := get_eq_none_of_not_mem hk
    have hb := hS x
    rw [hg] at hb
    simp only [BindOK] at hb
    obtain ⟨⟨k, w⟩, hkw, rfl⟩ := List.mem_map.mp hx
    have : (vfind vars k).isSome = true := by
      apply vfind_isSome_of_any
      exact List.any_eq_true.mpr ⟨(k, w), hkw, by simp⟩
    rw [hb] at this
    cases this
  have := List.Nodup.length_le_of_subset hnd hsub
  rw [List.length_map] at this
  exact this

end Vsa.AbsInt
