import Vsa.Sim.EntryGroundKit
import Vsa.Sim.MemRegionOwned

namespace Vsa.Sim
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Preserve evaluator ground from the actual owned AST and static support. -/
theorem EvalGround.transport_owned
    {m m' : Mem} {P : Nat → Prop} {SL : StackLayout} {A : Arena}
    {sp dst : BitVec 64} {node : Nat} {e : Expr}
    (h : EvalGround m SL A sp dst node e)
    (ast : ExprReprWithin m P node e) (agreement : AgreeP P m m')
    (support : EvalCallSupport m' SL A sp) (presence : MemExtends m m') :
    EvalGround m' SL A sp dst node e := by
  obtain ⟨_, _, _, _, _, table⟩ := support.pins m' (fun _ _ => rfl)
  refine
    { h with
      eval_call := support
      table := table
      stack_bytes := h.stack_bytes_extend presence
      ast := ⟨?_⟩ }
  obtain ⟨lo, hi, region⟩ := h.ast.region
  exact ⟨lo, hi, { region with nodes := ast.transport_region agreement region.nodes }⟩

#print axioms EvalGround.transport_owned
end Vsa.Sim
