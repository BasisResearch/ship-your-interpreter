import Vsa.Sim.EvalOrSim

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc Vsa.Sim.Code

namespace Vsa.Sim

/-- Short-circuit entry geometry follows from the represented child and
the retained helper-code support. -/
theorem EvalEntry.logicalShortExtras
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {op : LogOp} {st : Vsa.While.St} {d env : Nat} {el er : Expr} (vl : Value)
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Config}
    (h : EvalEntry g N A SL phiF phiC st d env (.logical op el er)
      sp r sret aEnv aExpr m0 c) :
    ∃ aLeft, LogicalShortExtras op N A SL el er vl sp sret aExpr aLeft m0 := by
  have hr : ExprRepr m0 aExpr.toNat (.logical op el er) := h.mem ▸ h.expr
  obtain ⟨p, hp, hchild⟩ : ∃ p, read64 m0 (aExpr.toNat + 16) = some p ∧
      ExprRepr m0 p el := by
    cases hr with
    | logical _ _ hp hc _ _ => exact ⟨_, hp, hc⟩
  have hg : EvalGround m0 SL A sp sret aExpr.toNat (.logical op el er) :=
    h.mem ▸ h.ground
  obtain ⟨lo, hi, spec⟩ := hg.ast.region
  have hn := exprIn_node spec.nodes
  have hleft := exprIn_logical_left spec.nodes p hp
  have hop := exprIn_node hleft
  have helo := hn.lo_le
  have hehi := hn.hi_ge
  have holo := hop.lo_le
  have hohi := hop.hi_ge
  have hlo := spec.lo_ram
  have hhi := spec.hi_ram
  have hwin := spec.win
  have hsp := h.stackBudget
  have hneed := Expr.stackNeed_ge el
  have hmax := Nat.le_max_left el.stackNeed er.stackNeed
  change SL.lo + ((evalFrame + max el.stackNeed er.stackNeed) +
    (maxCallDepth - d) * perCallBudget + 1088) ≤ sp.toNat ∧
    sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 at hsp
  simp only [evalFrame] at hsp hneed
  have hpword : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hagree (m' : Mem)
      (ha : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → m0[k]? = m'[k]?) :
      ∀ k, lo ≤ k ∧ k < hi → m0[k]? = m'[k]? := by
    intro k hk
    apply ha k
    intro hs
    rcases spec.stack_disjoint with hd | hd <;> omega
  obtain ⟨_, hint, htruthy, hslot, hnbs, _⟩ := hg.eval_call.pins m0 (fun _ _ => rfl)
  refine ⟨BitVec.ofNat 64 p,
    { slot7 := hg.table.slot7
      expr_survives := fun m' ha =>
        ((exprReprWithin_of_region hr spec.nodes).transport (hagree m' ha)).erase
      left_survives := ?_
      pay := by simpa only [hpword] using hp
      expr24 := by omega
      expr24_stk := ?_
      op_lo := by rw [hpword]; omega
      op_hi := by rw [hpword]; omega
      op_win := by rw [hpword]; omega
      op_stk := ?_
      sp_headroom := by omega
      sp_SLhi := hsp.2.1
      sp16 := hsp.2.2
      SLhi_ram := h.stack_ram.2
      code_stk := h.code_stack_disjoint
      vicode_stk := h.vicode_stack_disjoint
      table_stk := by have := h.table_stack_disjoint; omega
      arena_stk := hg.arena_stack
      arena_code := hg.arena_code
      expr_win8 := by omega
      expr_A := ?_
      expr_sub := ?_
      sret_inSL := hg.sret_inSL
      truthy_loaded := htruthy
      bool_loaded := hnbs.bool_code
      int_loaded := hint
      intslot := hslot
      truthy_stk := by have := hg.eval_call.vi_stack; omega
      boolcode_stk := by have := hg.eval_call.vi_stack; omega
      sret_boolcode := by have := h.sret_vicode_disjoint; omega
      truthy_arena := by have := hg.eval_call.arena_vi; omega
      bool_arena := by have := hg.eval_call.arena_vi; omega }⟩
  · intro m' ha
    rw [hpword]
    exact ((exprReprWithin_of_region hchild hleft).transport (hagree m' ha)).erase
  · rcases spec.stack_disjoint with hd | hd <;> omega
  · rw [hpword]
    rcases spec.stack_disjoint with hd | hd <;> omega
  · rcases spec.arena_disjoint with hd | hd <;> omega
  · rcases spec.stack_disjoint with hd | hd <;> omega

#print axioms EvalEntry.logicalShortExtras
end Vsa.Sim
