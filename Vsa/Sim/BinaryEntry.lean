import Vsa.Sim.rows.BinArmBridge

open LeanRV64DExecutable Vsa Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

/-- The represented children and entry ground supply the binary arm bundle. -/
theorem EvalEntry.binaryExtras
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {op : BinOp} {st : Vsa.While.St} {d env : Nat} {el er : Expr}
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Vsa.Machine.Config}
    (h : EvalEntry g N A SL phiF phiC st d env (.binary op el er)
      sp r sret aEnv aExpr m0 c) :
    ∃ aLeft aRight,
      BinArmExtras g N A SL op el er sp r sret aExpr aLeft aRight m0 := by
  have hr : ExprRepr m0 aExpr.toNat (.binary op el er) := h.mem ▸ h.expr
  obtain ⟨lp, rp, hpl, hl, hpr, hrp⟩ : ∃ lp rp,
      read64 m0 (aExpr.toNat + 16) = some lp ∧ ExprRepr m0 lp el ∧
      read64 m0 (aExpr.toNat + 24) = some rp ∧ ExprRepr m0 rp er := by
    cases hr with
    | binary _ _ hpL hL hpR hR => exact ⟨_, _, hpL, hL, hpR, hR⟩
  have hg : EvalGround m0 SL A sp sret aExpr.toNat (.binary op el er) :=
    h.mem ▸ h.ground
  obtain ⟨lo, hi, spec⟩ := hg.ast.region
  have hlin := exprIn_binary_left spec.nodes lp hpl
  have hrin := exprIn_binary_right spec.nodes rp hpr
  have hn := exprIn_node spec.nodes
  have hln := exprIn_node hlin
  have hrn := exprIn_node hrin
  have hlo := spec.lo_ram
  have hhi := spec.hi_ram
  have hwin := spec.win
  have hnlo := hn.lo_le
  have hnhi := hn.hi_ge
  have hllo := hln.lo_le
  have hlhi := hln.hi_ge
  have hrlo := hrn.lo_le
  have hrhi := hrn.hi_ge
  have hsp := h.stackBudget
  have hneed := Expr.stackNeed_ge el
  change SL.lo + ((evalFrame + max el.stackNeed er.stackNeed) +
    (maxCallDepth - d) * perCallBudget + 1088) ≤ sp.toNat ∧
    sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 at hsp
  simp only [evalFrame] at hsp hneed
  have hlword : (BitVec.ofNat 64 lp).toNat = lp := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hrword : (BitVec.ofNat 64 rp).toNat = rp := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hOutsideStack : ∀ k, regionP lo hi k → ¬ (SL.lo ≤ k ∧ k < SL.hi) := by
    intro k hk hs
    change lo ≤ k ∧ k < hi at hk
    rcases spec.stack_disjoint with hd | hd <;> omega
  have hOutsideArena : ∀ k, regionP lo hi k → ¬ (A.lo ≤ k ∧ k < A.hi) := by
    intro k hk ha
    change lo ≤ k ∧ k < hi at hk
    rcases spec.arena_disjoint with hd | hd <;> omega
  refine ⟨BitVec.ofNat 64 lp, BitVec.ofNat 64 rp, ?_⟩
  refine
    { slot6 := hg.table.slot6
      expr_survives := ?_
      pay_l := by simpa only [hlword] using hpl
      pay_r := by simpa only [hrword] using hpr
      expr32_stk := ?_
      lop_ram := by rw [hlword]; exact ⟨by omega, by omega⟩
      lop_win := by rw [hlword]; omega
      lop_stk := ?_
      lexpr_surv := ?_
      rop_ram := by rw [hrword]; exact ⟨by omega, by omega⟩
      rop_win := by rw [hrword]; omega
      rop_stk := ?_
      rop_stkfull := ?_
      rop_arena := ?_
      rexpr_surv := ?_
      node_hi := by omega
      node_stk := ?_
      node_arena := ?_
      sproom := by omega
      spSLhi := hsp.2.1
      sp16 := hsp.2.2
      SLhiRam := h.stack_ram.2
      codeStk := h.code_stack_disjoint
      viStk := h.vicode_stack_disjoint
      tableStk := by have := h.table_stack_disjoint; omega
      arenaStk := hg.arena_stack
      arenaCode := hg.arena_code
      arenaVi := hg.arena_vi
      arenaTable := hg.eval_call.arena_table
      sret_inSL := hg.sret_inSL
      gx19_pres := ?_ }
  · intro m' ha
    apply ((exprReprWithin_of_region hr spec.nodes).transport ?_).erase
    intro k hk
    exact ha k (fun hs => hOutsideStack k hk ⟨hs.1, by omega⟩)
  · rcases spec.stack_disjoint with hd | hd <;> omega
  · rw [hlword]
    rcases spec.stack_disjoint with hd | hd <;> omega
  · intro m' ha
    rw [hlword]
    exact ((exprReprWithin_of_region hl hlin).transport
      (fun k hk => ha k (hOutsideStack k hk))).erase
  · rw [hrword]
    rcases spec.stack_disjoint with hd | hd <;> omega
  · rw [hrword]
    rcases spec.stack_disjoint with hd | hd <;> omega
  · rw [hrword]
    rcases spec.arena_disjoint with hd | hd <;> omega
  · intro m' ha
    rw [hrword]
    exact ((exprReprWithin_of_region hrp hrin).transport
      (fun k hk => ha k (hOutsideStack k hk) (hOutsideArena k hk))).erase
  · rcases spec.stack_disjoint with hd | hd <;> omega
  · rcases spec.arena_disjoint with hd | hd <;> omega
  · obtain ⟨v19, _, _, h19, _, _⟩ := h.envset_defined
    exact ⟨v19, (h.frame Register.x19 (by decide)).symm.trans h19⟩

#print axioms EvalEntry.binaryExtras

end Vsa.Sim
