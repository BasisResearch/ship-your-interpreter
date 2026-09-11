import Vsa.Sim.EntryGroundKit

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

namespace Vsa.Sim

/-- Retain enclosing expression ground through the actual child memory frame. -/
theorem EvalGround.transport_frame
    {m m' : Mem} {SL : StackLayout} {A : Arena} {sp dst : BitVec 64}
    {node : Nat} {e : Expr} {cut result : Nat}
    (h : EvalGround m SL A sp dst node e)
    (hcut : cut ≤ SL.hi) (hresult : SL.lo ≤ result ∧ result + 24 ≤ SL.hi)
    (presence : MemExtends m m')
    (frame : ∀ k, ¬ (SL.lo ≤ k ∧ k < cut) → ¬ (A.lo ≤ k ∧ k < A.hi) →
      (result ≤ k ∧ k < result + 24) ∨ m'[k]? = m[k]?) :
    EvalGround m' SL A sp dst node e := by
  have agree (k : Nat) (hs : ¬ (SL.lo ≤ k ∧ k < SL.hi))
      (ha : ¬ (A.lo ≤ k ∧ k < A.hi)) : m[k]? = m'[k]? := by
    rcases frame k (by omega) ha with slot | same
    · exact False.elim (hs (by omega))
    · exact same.symm
  refine h.transport_via ?_ ?_
    (h.eval_call.transport_frame hcut hresult frame) (h.stack_bytes_extend presence)
  · intro k hlo hhi
    exact agree k (by
      have := h.eval_call.table_stack
      omega) (by
      have := h.eval_call.arena_table
      omega)
  · intro lo hi region k hlo hhi
    exact agree k (by
      have := region.stack_disjoint
      omega) (by
      have := region.arena_disjoint
      omega)

#print axioms EvalGround.transport_frame

end Vsa.Sim
