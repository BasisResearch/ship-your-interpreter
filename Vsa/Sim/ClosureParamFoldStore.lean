import Vsa.Sim.rows.CallCruxMarshal
import Vsa.Sim.StoreSetFootprint
import Vsa.While.Cost

namespace Vsa.Sim.ClosureParam

open Vsa Vsa.While

/-- Defining a valid scope leaves at least one binding and adds at most one slot. -/
theorem define_count (store : Store) (target : Addr) (valid : target < store.frames.size)
    (param : String) (value : Value) :
    0 < ((store.define target param value).frames[target]'(by simpa [Store.define] using valid)).vars.length ∧
    ((store.define target param value).frames[target]'(by simpa [Store.define] using valid)).vars.length ≤
      store.frames[target].vars.length + 1 := by
  simp only [Store.define, Array.getElem_modify, if_pos]
  split
  · rename_i hit
    simp only [List.length_map]
    have nonempty : store.frames[target].vars ≠ [] := by
      intro empty
      simp only [empty, List.any_nil, Bool.false_eq_true] at hit
    exact ⟨List.length_pos_iff.mpr nonempty, by omega⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- The exact source prefix advances by the parameter and argument at the same index. -/
theorem fold_next (store : Store) (cd : ClosureData) (values : List Value) (target index : Nat)
    (arity : values.length = cd.params.length) (hi : index < values.length) :
    foldStore store cd values target (index + 1) =
      (foldStore store cd values target index).define target
        (cd.params[index]'(by omega)) values[index] := by
  rw [foldStore_succ store cd values target index (by simp only [List.length_zip]; omega)]
  simp only [List.getElem_zip]

/-- Every prefix has the original frame and closure counts. -/
theorem fold_sizes (store : Store) (cd : ClosureData) (values : List Value) (target index : Nat) :
    (foldStore store cd values target index).frames.size = store.frames.size ∧
    (foldStore store cd values target index).closures.size = store.closures.size :=
  foldDefine_size _ _ _

/-- Source binding uniqueness is preserved over every parameter prefix. -/
theorem fold_unique (store : Store) (cd : ClosureData) (values : List Value) (target index : Nat)
    (unique : StoreUnique store) : StoreUnique (foldStore store cd values target index) := by
  unfold foldStore
  generalize (cd.params.zip values).take index = pairs
  induction pairs generalizing store with
  | nil => exact unique
  | cons pair rest ih =>
    exact ih (store.define target pair.1 pair.2) (unique.define store target pair.1 pair.2)

/-- A fresh scope has at most one binding per processed argument and is nonempty thereafter. -/
theorem fold_count (store : Store) (cd : ClosureData) (values : List Value) (target index : Nat)
    (arity : values.length = cd.params.length) (bound : index ≤ values.length)
    (valid : target < store.frames.size) (empty : store.frames[target].vars.length = 0) :
    ((foldStore store cd values target index).frames[target]'(by
      rw [(fold_sizes store cd values target index).1]; exact valid)).vars.length ≤ index ∧
    (0 < index → 0 < ((foldStore store cd values target index).frames[target]'(by
      rw [(fold_sizes store cd values target index).1]; exact valid)).vars.length) := by
  induction index with
  | zero => simpa only [foldStore, List.take_zero, List.foldl_nil, empty] using
      (show 0 ≤ 0 ∧ (0 < 0 → 0 < 0) from ⟨by omega, fun h => h⟩)
  | succ index ih =>
    have previous := ih (by omega)
    have next := define_count (foldStore store cd values target index) target
      (by rw [(fold_sizes store cd values target index).1]; exact valid)
      (cd.params[index]'(by omega)) (values[index]'(by omega))
    simp only [fold_next store cd values target index arity (by omega)]
    exact ⟨by omega, fun _ => next.1⟩

end Vsa.Sim.ClosureParam
