import Vsa.Sim.SeqSuffixOwned

namespace Vsa.Sim
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Sequence dispatch stores preserve each child's static image and hereditary ground. -/
theorem SeqStmtGround.transport_stack
    {m m' : Mem} {SL : StackLayout} {A : Arena} {sp aRet : BitVec 64}
    {d a : Nat} {s : Stmt} (h : SeqStmtGround m SL A sp aRet d a s)
    (presence : MemExtends m m')
    (frame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m[k]? = m'[k]?) :
    SeqStmtGround m' SL A sp aRet d a s := by
  have regions : ∀ lo hi, StmtRegionSpec m SL A aRet.toNat a s lo hi →
      ∀ k, lo ≤ k → k < hi → m[k]? = m'[k]? := by
    intro lo hi region k hlo hhi
    exact frame k (by have := region.stack_disjoint; omega)
  refine
    { stmt := ?_
      ground := h.ground.transport_via ?_ regions
        (fun k hk => (frame k (h.ground.eval_call.outsideStack hk)).symm)
        (by
          intro k hlo hhi
          obtain ⟨b, hb⟩ := h.ground.stack_bytes k hlo hhi
          exact presence k b hb)
      stackBudget := h.stackBudget, bodies := h.bodies }
  · obtain ⟨lo, hi, region⟩ := h.ground.ast.region
    exact ((stmtReprWithin_of_region h.stmt region.nodes).transport
      (fun k hk => regions lo hi region k hk.1 hk.2)).erase
  · intro k hlo hhi
    apply frame k
    apply h.ground.eval_call.outsideStack
    change 0x80000000 ≤ k ∧ k < 0x8001acf0
    change 0x80019fb8 ≤ k at hlo
    change k < 0x80019fb8 + 36 at hhi
    omega

/-- The whole owned suffix survives a dispatch's stack-only writes. -/
theorem SeqSuffixOwned.transport_stack
    {m m' : Mem} {shared : Nat → Prop} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {d a : Nat} {ss : List Stmt}
    (h : SeqSuffixOwned m shared SL A sp aRet d a ss)
    (presence : MemExtends m m')
    (frame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m[k]? = m'[k]?)
    (agreement : AgreeP shared m m') : SeqSuffixOwned m' shared SL A sp aRet d a ss := by
  obtain ⟨reads, ground⟩ := h
  refine ⟨reads.transport agreement, ?_⟩
  have pointers := reads.pointers
  clear reads
  induction ground with
  | nil => exact .nil
  | cons read ground _ ih =>
    cases pointers with
    | cons cell tail =>
      exact .cons ((read64_agreeP agreement cell.covered).symm.trans read)
        (ground.transport_stack presence frame) (ih tail)

#print axioms SeqStmtGround.transport_stack
#print axioms SeqSuffixOwned.transport_stack

end Vsa.Sim
