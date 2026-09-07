import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BlockTactics

namespace Vsa.Sim

/-- Structure fields introduce the metadata wrapper seen in dispatch data. -/
structure MetadataWrappedFacts (σ : Vsa.Machine.MState) (L : GRegs)
    (lds : List (List (BitVec 8))) : Prop where
  facts : ChainFacts σ.mem σ.mem L lds chainFactsDemo

/-- The chain walker accepts a metadata-wrapped field goal. -/
theorem metadata_chain_facts (σ : Vsa.Machine.MState) (L : GRegs)
    (lds : List (List (BitVec 8))) (h : Code.Eval_exprLoaded σ.mem) :
    MetadataWrappedFacts σ L lds := by
  refine ⟨?_⟩
  chain_facts h with "Vsa.Sim.Code.eval_expr_at_"

/-- The block walker accepts the same wrapped chain container. -/
theorem metadata_block_facts (σ : Vsa.Machine.MState) (L : GRegs)
    (lds : List (List (BitVec 8))) (h : Code.Eval_exprLoaded σ.mem) :
    MetadataWrappedFacts σ L lds := by
  refine ⟨?_⟩
  block_facts h with "Vsa.Sim.Code.eval_expr_at_"

#print axioms metadata_chain_facts
#print axioms metadata_block_facts
end Vsa.Sim
