import Vsa.Sim.SeqSuffixGround
import Vsa.Sim.MemRegionOwned

namespace Vsa.Sim
open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Preserve statement ground from owned AST reads and reached static support. -/
theorem ExecGround.transport_owned
    {m m' : Mem} {P : Nat → Prop} {SL : StackLayout} {A : Arena}
    {sp ret : BitVec 64} {node : Nat} {s : Stmt}
    (h : ExecGround m SL A sp ret node s)
    (ast : StmtReprWithin m P node s) (agreement : AgreeP P m m')
    (table : StmtTablePins m') (support : EvalCallSupport m' SL A sp)
    (presence : MemExtends m m') : ExecGround m' SL A sp ret node s := by
  refine
    { h with
      table := table
      eval_call := support
      stack_bytes := by
        intro k hlo hhi
        obtain ⟨b, hb⟩ := h.stack_bytes k hlo hhi
        exact presence k b hb
      ast := ⟨by
        obtain ⟨lo, hi, region⟩ := h.ast.region
        exact ⟨lo, hi, { region with nodes := ast.transport_region agreement region.nodes }⟩⟩ }

/-- The selected child supplies static framing; shared agreement preserves the AST. -/
theorem SeqStmtGround.transport_owned_execExit
    {m : Mem} {P : Nat → Prop} {SL : StackLayout} {A : Arena}
    {sp ret r : BitVec 64} {d node : Nat} {s : Stmt}
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {phiF phiC : Addr → Nat} {nf nc : Nat} {st : Vsa.While.St} {status : Status}
    {cfg : Config} (h : SeqStmtGround m SL A sp ret d node s)
    (ast : StmtReprWithin m P node s) (agreement : AgreeP P m cfg.σ.mem)
    (exit : ExecExit g N A SL phiF phiC nf nc st status sp r ret m cfg)
    (presence : MemExtends m cfg.σ.mem) :
    SeqStmtGround cfg.σ.mem SL A sp ret d node s := by
  have table : StmtTablePins cfg.σ.mem := h.ground.table.transport (by
    intro k hlo hhi
    have offStack : ¬ (SL.lo ≤ k ∧ k < sp.toNat) := by
      rcases h.ground.table_stack with ht | ht <;> omega
    have offArena : ¬ (A.lo ≤ k ∧ k < A.hi) := by
      rcases h.ground.arena_table with ht | ht <;> omega
    have offRet : ¬ (ret.toNat ≤ k ∧ k < ret.toNat + 24) := by
      rcases h.ground.aret_table_disjoint with ht | ht <;> omega
    exact ((exit.memFrame k offStack offArena).resolve_left offRet).symm)
  have support := h.ground.eval_call.transport_frame (sp' := sp)
    h.stackBudget.2.1 h.ground.aret.inSL exit.memFrame
  exact
    { h with
      stmt := (ast.transport agreement).erase
      ground := h.ground.transport_owned ast agreement table support presence }

#print axioms ExecGround.transport_owned
#print axioms SeqStmtGround.transport_owned_execExit
end Vsa.Sim
