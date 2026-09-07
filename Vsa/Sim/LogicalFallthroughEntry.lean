import Vsa.Sim.LogicalShortEntry
import Vsa.Sim.EvalLogical4
import Vsa.While.StoreBodiesBoundPreservation

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc Vsa.Sim.Code

namespace Vsa.Sim

/-- The actual left derivation supplies the right call's store-body bound;
the represented right child supplies its geometry and read preservation. -/
theorem EvalEntry.logicalFallthroughExtras
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {op : LogOp} {st st' : Vsa.While.St} (st'' : Vsa.While.St)
    {d env : Nat} {el er : Expr} {vl : Value} (vr : Value)
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Config}
    (h : EvalEntry g N A SL phiF phiC st d env (.logical op el er)
      sp r sret aEnv aExpr m0 c)
    (hEl : EvalE st d env el st' vl) :
    ∃ aLeft aRight, LogicalFallthroughExtras op N A SL st' st'' el er vl vr
      sp sret aExpr aLeft aRight m0 := by
  obtain ⟨aLeft, hs⟩ := h.logicalShortExtras vl
  have hr : ExprRepr m0 aExpr.toNat (.logical op el er) := h.mem ▸ h.expr
  obtain ⟨p, hp, hchild⟩ : ∃ p, read64 m0 (aExpr.toNat + 24) = some p ∧
      ExprRepr m0 p er := by
    cases hr with
    | logical _ _ _ _ hp hc => exact ⟨_, hp, hc⟩
  have hg : EvalGround m0 SL A sp sret aExpr.toNat (.logical op el er) :=
    h.mem ▸ h.ground
  obtain ⟨lo, hi, spec⟩ := hg.ast.region
  have hn := exprIn_node spec.nodes
  have hright := exprIn_logical_right spec.nodes p hp
  have hop := exprIn_node hright
  have helo := hn.lo_le
  have hehi := hn.hi_ge
  have holo := hop.lo_le
  have hohi := hop.hi_ge
  have hlo := spec.lo_ram
  have hhi := spec.hi_ram
  have hwin := spec.win
  have hsp := hs.sp_SLhi
  have hpword : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨aLeft, BitVec.ofNat 64 p,
    { toLogicalShortExtras := hs
      right_survives := ?_
      pay_right := by simpa only [hpword] using hp
      expr32 := by omega
      expr32_stk := ?_
      rop_lo := by rw [hpword]; omega
      rop_hi := by rw [hpword]; omega
      rop_win := by rw [hpword]; omega
      rop_stk := ?_
      arena_vi := by have := hg.eval_call.arena_vi; omega
      arena_table := hg.eval_call.arena_table
      expr_A32 := ?_
      store_bodiesR := StoreBodiesBound.afterEvalE hEl
        (Expr.bodiesBound_logical h.expr_bodies).1 h.store_bodies }⟩
  · intro m' ha
    rw [hpword]
    apply ((exprReprWithin_of_region hchild hright).transport ?_).erase
    intro k hk
    change lo ≤ k ∧ k < hi at hk
    apply ha k
    · intro hstack
      rcases spec.stack_disjoint with hd | hd <;> omega
    · intro harena
      rcases spec.arena_disjoint with hd | hd <;> omega
  · rcases spec.stack_disjoint with hd | hd <;> omega
  · rw [hpword]
    rcases spec.stack_disjoint with hd | hd <;> omega
  · rcases spec.arena_disjoint with hd | hd <;> omega

#print axioms EvalEntry.logicalFallthroughExtras
end Vsa.Sim
