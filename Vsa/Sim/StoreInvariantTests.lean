import Vsa.Sim.StoreInvariant

open Vsa Vsa.While

namespace Vsa.Sim.StoreInvariantTests

private def chainStore : Store :=
  { frames :=
      #[{ parent := none, vars := [("x", .int 7)] },
        { parent := some 0, vars := [("y", .int 9)] }]
    closures := #[] }

private def chainStoreSet : Store :=
  { frames :=
      #[{ parent := none, vars := [("x", .int 11)] },
        { parent := some 0, vars := [("y", .int 9)] }]
    closures := #[] }

private theorem chainStore_inv : StoreInvariant chainStore := by
  constructor
  · intro fa hfa
    have hcases : fa = 0 ∨ fa = 1 := by
      simp [chainStore] at hfa
      omega
    rcases hcases with rfl | rfl <;> simp [chainStore, FrameNamesUnique]
  · intro fa hfa parent hparent
    have hcases : fa = 0 ∨ fa = 1 := by
      simp [chainStore] at hfa
      omega
    rcases hcases with rfl | rfl
    · simp [chainStore] at hparent
    · simpa [chainStore] using hparent.symm

example : StoreInvariant chainStore := chainStore_inv

example : chainStore.get? 1 "x" = some (.int 7) := by rfl

example : LookupChain chainStore "x" chainStore.frames.size 1 (.int 7) :=
  (get?_eq_some_iff_chain chainStore 1 "x" (.int 7)).mp (by rfl)

example : chainStore.set? 1 "x" (.int 11) = some chainStoreSet := by rfl

example : SetChain chainStore "x" (.int 11) chainStore.frames.size 1 chainStoreSet :=
  (set?_eq_some_iff_chain chainStore 1 "x" (.int 11) chainStoreSet).mp (by rfl)

example : StoreInvariant chainStoreSet := by
  exact chainStore_inv.set? (s' := chainStoreSet) (a := 1) (x := "x")
    (newValue := .int 11) (by rfl)

example : VarStoreBridge initSt.store 0 "print" (.native .print) :=
  ReachableStore.init.varBridge (by rfl)

example : AssignStoreBridge initSt.store
    (initSt.store.define 0 "print" (.int 11)) 0 "print" (.int 11) :=
  ReachableStore.init.assignBridge (by rfl)

private def parentStore0 : Store := (initSt.store.allocFrame (some 0)).1
private def parentStore1 : Store := parentStore0.define 0 "x" (.int 7)
private def parentStore : Store := parentStore1.define 1 "y" (.int 9)

private theorem parentStore_reachable : ReachableStore parentStore := by
  have h0 : ReachableStore initSt.store := ReachableStore.init
  have h1 : ReachableStore parentStore0 := by
    apply ReachableStore.step h0
    apply StoreStep.allocFrame
    intro p hp
    cases hp
    simp [initSt]
  have h2 : ReachableStore parentStore1 :=
    ReachableStore.step h1 (StoreStep.define parentStore0 0 "x" (.int 7))
  exact ReachableStore.step h2 (StoreStep.define parentStore1 1 "y" (.int 9))

example : VarStoreBridge parentStore 1 "x" (.int 7) :=
  parentStore_reachable.varBridge (by rfl)

example : AssignStoreBridge parentStore
    (parentStore.define 0 "x" (.int 11)) 1 "x" (.int 11) :=
  parentStore_reachable.assignBridge (by rfl)

example :
    [("x", Value.int 7), ("y", Value.int 9)].map
      (replaceBindingValue "x" (.int 11)) =
    [("x", Value.int 11), ("y", Value.int 9)] := by
  rfl

#print axioms firstMatch_iff_find?
#print axioms lookup_eq_some_iff_chain
#print axioms get?_terminal_first
#print axioms set_eq_some_iff_chain
#print axioms set?_terminal_first
#print axioms set?_single_update
#print axioms FirstMatch.single_update
#print axioms StoreInvariant.set?
#print axioms storeInvariant_initSt
#print axioms ReachableStore.invariant
#print axioms ReachableStore.varBridge
#print axioms ReachableStore.assignBridge

end Vsa.Sim.StoreInvariantTests
