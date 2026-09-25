import Vsa.Densify.GenA

/-!
# `Resp` for the `currentlyEnabled` mutual block

`PlatformConfig.lean`'s `mutual` block (`check_stateen_bit`, `currentlyEnabled`,
`get_hstateen`, `get_sstateen`, `get_xLPE`, `is_hstateen_accessible`,
`is_sstateen_accessible`, `is_zfinx_enabled_by_stateen`,
`virtual_memory_supported`) recurses by a measure, so `unfold` cannot close it
by itself. Each member's functional induction principle (`*.induct`) carries
the same nine motives; every case is one unfolding plus `resp_auto`, with the
recursive calls closed by the induction hypotheses.
-/

namespace Vsa.Densify.RecMutual

open Sail ConcurrencyInterfaceV1 LeanRV64DExecutable LeanRV64DExecutable.Functions
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Densify.Gen

/-- One case of the block's induction: unfold the head and discharge. -/
macro "mutual_case" : tactic => `(tactic| (
  intros
  first
    | rw [check_stateen_bit.eq_def] | rw [currentlyEnabled.eq_def] | rw [get_hstateen.eq_def]
    | rw [get_sstateen.eq_def] | rw [get_xLPE.eq_def] | rw [is_hstateen_accessible.eq_def]
    | rw [is_sstateen_accessible.eq_def] | rw [is_zfinx_enabled_by_stateen.eq_def]
    | rw [virtual_memory_supported.eq_def]
  resp_auto))

theorem check_stateen_bit_resp : ∀ (a0 : _) (a1 : _) (a2 : _), Resp (@check_stateen_bit a0 a1 a2) := by
  apply check_stateen_bit.induct (motive1 := fun p b n => Resp (check_stateen_bit p b n))
    (motive2 := fun i => Resp (get_hstateen i)) (motive3 := fun x => Resp (is_hstateen_accessible x))
    (motive4 := fun e => Resp (currentlyEnabled e)) (motive5 := fun x => Resp (virtual_memory_supported x))
    (motive6 := fun p => Resp (get_xLPE p)) (motive7 := fun x => Resp (is_zfinx_enabled_by_stateen x))
    (motive8 := fun i => Resp (get_sstateen i)) (motive9 := fun x => Resp (is_sstateen_accessible x))
    <;> mutual_case

theorem currentlyEnabled_resp : ∀ (a0 : _), Resp (@currentlyEnabled a0) := by
  apply currentlyEnabled.induct (motive1 := fun p b n => Resp (check_stateen_bit p b n))
    (motive2 := fun i => Resp (get_hstateen i)) (motive3 := fun x => Resp (is_hstateen_accessible x))
    (motive4 := fun e => Resp (currentlyEnabled e)) (motive5 := fun x => Resp (virtual_memory_supported x))
    (motive6 := fun p => Resp (get_xLPE p)) (motive7 := fun x => Resp (is_zfinx_enabled_by_stateen x))
    (motive8 := fun i => Resp (get_sstateen i)) (motive9 := fun x => Resp (is_sstateen_accessible x))
    <;> mutual_case

theorem get_hstateen_resp : ∀ (a0 : _), Resp (@get_hstateen a0) := by
  apply get_hstateen.induct (motive1 := fun p b n => Resp (check_stateen_bit p b n))
    (motive2 := fun i => Resp (get_hstateen i)) (motive3 := fun x => Resp (is_hstateen_accessible x))
    (motive4 := fun e => Resp (currentlyEnabled e)) (motive5 := fun x => Resp (virtual_memory_supported x))
    (motive6 := fun p => Resp (get_xLPE p)) (motive7 := fun x => Resp (is_zfinx_enabled_by_stateen x))
    (motive8 := fun i => Resp (get_sstateen i)) (motive9 := fun x => Resp (is_sstateen_accessible x))
    <;> mutual_case

theorem get_sstateen_resp : ∀ (a0 : _), Resp (@get_sstateen a0) := by
  apply get_sstateen.induct (motive1 := fun p b n => Resp (check_stateen_bit p b n))
    (motive2 := fun i => Resp (get_hstateen i)) (motive3 := fun x => Resp (is_hstateen_accessible x))
    (motive4 := fun e => Resp (currentlyEnabled e)) (motive5 := fun x => Resp (virtual_memory_supported x))
    (motive6 := fun p => Resp (get_xLPE p)) (motive7 := fun x => Resp (is_zfinx_enabled_by_stateen x))
    (motive8 := fun i => Resp (get_sstateen i)) (motive9 := fun x => Resp (is_sstateen_accessible x))
    <;> mutual_case

theorem get_xLPE_resp : ∀ (a0 : _), Resp (@get_xLPE a0) := by
  apply get_xLPE.induct (motive1 := fun p b n => Resp (check_stateen_bit p b n))
    (motive2 := fun i => Resp (get_hstateen i)) (motive3 := fun x => Resp (is_hstateen_accessible x))
    (motive4 := fun e => Resp (currentlyEnabled e)) (motive5 := fun x => Resp (virtual_memory_supported x))
    (motive6 := fun p => Resp (get_xLPE p)) (motive7 := fun x => Resp (is_zfinx_enabled_by_stateen x))
    (motive8 := fun i => Resp (get_sstateen i)) (motive9 := fun x => Resp (is_sstateen_accessible x))
    <;> mutual_case

theorem is_hstateen_accessible_resp : ∀ (a0 : _), Resp (@is_hstateen_accessible a0) := by
  apply is_hstateen_accessible.induct (motive1 := fun p b n => Resp (check_stateen_bit p b n))
    (motive2 := fun i => Resp (get_hstateen i)) (motive3 := fun x => Resp (is_hstateen_accessible x))
    (motive4 := fun e => Resp (currentlyEnabled e)) (motive5 := fun x => Resp (virtual_memory_supported x))
    (motive6 := fun p => Resp (get_xLPE p)) (motive7 := fun x => Resp (is_zfinx_enabled_by_stateen x))
    (motive8 := fun i => Resp (get_sstateen i)) (motive9 := fun x => Resp (is_sstateen_accessible x))
    <;> mutual_case

theorem is_sstateen_accessible_resp : ∀ (a0 : _), Resp (@is_sstateen_accessible a0) := by
  apply is_sstateen_accessible.induct (motive1 := fun p b n => Resp (check_stateen_bit p b n))
    (motive2 := fun i => Resp (get_hstateen i)) (motive3 := fun x => Resp (is_hstateen_accessible x))
    (motive4 := fun e => Resp (currentlyEnabled e)) (motive5 := fun x => Resp (virtual_memory_supported x))
    (motive6 := fun p => Resp (get_xLPE p)) (motive7 := fun x => Resp (is_zfinx_enabled_by_stateen x))
    (motive8 := fun i => Resp (get_sstateen i)) (motive9 := fun x => Resp (is_sstateen_accessible x))
    <;> mutual_case

theorem is_zfinx_enabled_by_stateen_resp : ∀ (a0 : _), Resp (@is_zfinx_enabled_by_stateen a0) := by
  apply is_zfinx_enabled_by_stateen.induct (motive1 := fun p b n => Resp (check_stateen_bit p b n))
    (motive2 := fun i => Resp (get_hstateen i)) (motive3 := fun x => Resp (is_hstateen_accessible x))
    (motive4 := fun e => Resp (currentlyEnabled e)) (motive5 := fun x => Resp (virtual_memory_supported x))
    (motive6 := fun p => Resp (get_xLPE p)) (motive7 := fun x => Resp (is_zfinx_enabled_by_stateen x))
    (motive8 := fun i => Resp (get_sstateen i)) (motive9 := fun x => Resp (is_sstateen_accessible x))
    <;> mutual_case

theorem virtual_memory_supported_resp : ∀ (a0 : _), Resp (@virtual_memory_supported a0) := by
  apply virtual_memory_supported.induct (motive1 := fun p b n => Resp (check_stateen_bit p b n))
    (motive2 := fun i => Resp (get_hstateen i)) (motive3 := fun x => Resp (is_hstateen_accessible x))
    (motive4 := fun e => Resp (currentlyEnabled e)) (motive5 := fun x => Resp (virtual_memory_supported x))
    (motive6 := fun p => Resp (get_xLPE p)) (motive7 := fun x => Resp (is_zfinx_enabled_by_stateen x))
    (motive8 := fun i => Resp (get_sstateen i)) (motive9 := fun x => Resp (is_sstateen_accessible x))
    <;> mutual_case

end Vsa.Densify.RecMutual
