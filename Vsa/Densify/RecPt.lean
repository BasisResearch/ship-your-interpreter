import Vsa.Densify.GenB

/-!
# `Resp` for the page-table walk

`pt_walk` (`Vmem.lean`) recurses on the level; `pt_walk.induct` supplies the
induction hypothesis for the recursive call, and the body is one unfolding
plus `resp_auto`.
-/

namespace Vsa.Densify.RecPt

open Sail ConcurrencyInterfaceV1 LeanRV64DExecutable LeanRV64DExecutable.Functions
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Densify.Gen Vsa.Densify.RecMutual

theorem pt_walk_resp : ∀ (a0 : _) (a1 : _) (a2 : _) (a3 : _) (a4 : _) (a5 : _) (a6 : _) (a7 : _)
    (a8 : _) (a9 : _), Resp (@pt_walk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) := by
  intro sv_width vpn access priv mxr do_sum pt_base level global ext_ptw
  refine pt_walk.induct sv_width vpn access priv mxr do_sum ext_ptw
    (motive := fun pt_base level global =>
      Resp (pt_walk sv_width vpn access priv mxr do_sum pt_base level global ext_ptw))
    ?_ pt_base level global
  intro pt_base level global ih
  rw [pt_walk.eq_def]
  resp_auto [read_pte_resp, pte_is_invalid_resp, check_PTE_permission_resp,
    page_based_mem_type_forwards_resp, currentlyEnabled_resp]
  all_goals exact ih _ ‹_›

end Vsa.Densify.RecPt
