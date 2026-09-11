import Vsa.Sim.CallArgsStart
import Vsa.Sim.ArmEntryRetained

namespace Vsa.Sim.CallCallee

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The actual call-arm dispatch supplies the callee input and outer caller frame. -/
structure ArmReady (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop) (credits : Nat)
    (st : Vsa.While.St) (d env : Nat) (e : Expr) (args : List Expr)
    (sp ret dst node interp child v8 v9 v18 : BitVec 64) (m0 : Mem) (arm : Config) : Prop where
  input : Input SL A phiF st d env e node (sp - 1088#64) interp child arm
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits st.store arm.σ.mem
  ast : ExprReprWithin arm.σ.mem shared node.toNat (.call e args)
  gp : arm.σ.regs.get? Register.x3 = some gpv
  window : BinaryPrefix.Window SL (sp - 1088#64)
  retained : ArmEntryRetained g N A SL phiF phiC st env 0x800031b0#64 (fun _ => True)
    (.call e args) sp ret dst node interp v8 v9 v18 arm.σ.sailOutput m0 arm.σ.mem arm

/-- Dispatch an owned call expression and derive the callee's entry facts from its AST. -/
theorem dispatch
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {credits : Nat}
    {st : Vsa.While.St} {d env : Nat} {e : Expr} {args : List Expr}
    {sp ret dst node interp : BitVec 64} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (h : EvalAllocatorEntry g N M phiF phiC alloc exts shared credits
      st d env (.call e args) sp ret dst interp node m0 before) :
    ∃ arm child v8 v9 v18, Steps before arm ∧
      ArmReady g N M phiF phiC alloc exts shared credits st d env e args
        sp ret dst node interp child v8 v9 v18 m0 arm := by
  have entry := h.entry
  have ast0 : ExprReprWithin m0 shared node.toNat (.call e args) := entry.mem ▸ h.ast
  have ground0 : EvalGround m0 SL A sp dst node.toNat (.call e args) := entry.mem ▸ entry.ground
  have kind : read32 m0 node.toNat = some 9 := by cases ast0.erase with | call hk => exact hk
  have spHi := entry.stackOK.2.1
  have offShared : ∀ k, shared k → ¬ (SL.lo ≤ k ∧ k < SL.hi) :=
    fun _ hk => (h.allocator.runtime L).shared_off_stack hk
  obtain ⟨arm, steps, out0, ment, v8, v9, v18, retained⟩ :=
    armEntry_retained g N A SL phiF phiC st d env (.call e args) 9 0x800031b0#64
      (fun _ => True) sp ret dst interp node m0 (by decide) (by decide) kind ground0.table.slot9
      trivial (fun _ _ _ _ _ _ => trivial)
      (fun mem same => (ast0.transport (fun k hk => same k (by have := offShared k hk; omega))).erase)
      (by decide) (by have := entry.table_stack_disjoint; simp only [jumpTableBase]; omega) before entry
  have p := ArmEntryK.destruct g N A SL phiF phiC st 0x800031b0#64 (fun _ => True)
    (.call e args) sp ret dst node interp v8 v9 v18 out0 m0 ment arm retained.arm
  have memory := p.mem
  subst ment
  have frame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = arm.σ.mem[k]? := by
    intro k hk
    rw [entry.mem]
    exact (p.memFrame k (by omega)).symm
  have current := h.allocator.after_stack L frame
  have ast := h.ast.transport (fun k hk => frame k (offShared k hk))
  have ground := ground0.transport_offstack entry.table_stack_disjoint spHi
    (by
      intro k hlo hhi
      obtain ⟨b, hb⟩ := ground0.stack_bytes k hlo hhi
      exact retained.presence k b hb) p.memFrame
  obtain ⟨q, childRead⟩ : ∃ q, read64 arm.σ.mem (node.toNat + 8) = some q := by
    cases ast.erase with | call _ hf => exact ⟨_, hf⟩
  obtain ⟨lo, hi, region⟩ := ground.ast.region
  have nodeBounds := exprIn_node region.nodes
  have childBounds := exprIn_node (exprIn_call_callee region.nodes q childRead)
  have qsmall : q < 2^64 := by have := childBounds.hi_ge; have := region.hi_ram; omega
  have qnat : (BitVec.ofNat 64 q).toNat = q := Nat.mod_eq_of_lt qsmall
  have lowered : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := p.spRoom; have := sp.isLt; omega
  have resultAddr : ((sp - 1088#64) + 96#64).toNat = sp.toNat - 1088 + 96 := by
    rw [BitVec.toNat_add, lowered]
    change (sp.toNat - 1088 + 96) % 2^64 = _
    exact Nat.mod_eq_of_lt (by have := p.spRoom; have := sp.isLt; omega)
  have stackLo : SL.lo ≤ (sp - 1088#64).toNat := by rw [lowered]; have := entry.stackOK.1; omega
  have budget : StackOK SL (sp - 1088#64)
      (e.stackNeed + (maxCallDepth - d) * perCallBudget + 1088) := by
    apply entry.stackBudget.child (by decide)
    change (e.stackNeed + (maxCallDepth - d) * perCallBudget + 1088) + 1088 ≤
      (1088 + max e.stackNeed (Expr.stackNeedList args)) + (maxCallDepth - d) * perCallBudget + 1088
    have bound := Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.le_max_left e.stackNeed (Expr.stackNeedList args))
        ((maxCallDepth - d) * perCallBudget)) (1088 + 1088)
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using bound
  have childGround := ground.child_params
    (fun lo hi hin => exprIn_call_callee hin q childRead) entry.table_stack_disjoint spHi
    (sp' := sp - 1088#64) (subsret := (sp - 1088#64) + 96#64)
    (by rw [lowered]; omega) (by rw [resultAddr]; rw [lowered] at stackLo; omega)
    (by rw [resultAddr]; have := p.spRoom; omega)
  have savedFrame (R : Register) (hr : AbiPreservedNoise R)
      (h8 : (Register.x8 == R) = false) (h9 : (Register.x9 == R) = false)
      (h18 : (Register.x18 == R) = false) (h2 : (Register.x2 == R) = false) :
      arm.σ.regs.get? R = before.σ.regs.get? R :=
    (p.frame R hr h8 h9 h18 h2).trans (entry.frame R hr).symm
  obtain ⟨r19, r20, r21, h19, h20, h21⟩ := entry.envset_defined
  have outEq := p.out.symm
  refine ⟨arm, BitVec.ofNat 64 q, v8, v9, v18, steps,
    { input :=
        { geometry :=
            { nodeLo := p.exprLo
              nodeHi := by have := nodeBounds.hi_ge; have := region.hi_ram; omega
              nodeHtif := Or.inr (by have := p.exprWin; omega)
              stackLo := by have := entry.stack_ram.1; omega
              stackHi := by rw [lowered]; have := p.spHi; have := p.spRoom; omega
              stackHtif := by rw [lowered]; exact Nat.le_sub_of_add_le p.spWin
              stackAlign := by rw [lowered]; have := p.spAlign; have := p.spRoom; omega }
          good := p.good, tick := p.tick, pc := p.pc
          regs := ⟨p.a2, p.spReg, retained.environment, trivial⟩
          interpReg := p.a1, childRead := by rw [qnat]; exact childRead
          ground := { ground := by rw [qnat]; exact childGround
                      budget := budget, bodies := (Expr.bodiesBound_call entry.expr_bodies).1 }
          stackRam := entry.stack_ram, stackWin := entry.stack_win
          envValid := entry.env_valid, storeBodies := entry.store_bodies
          present8 := by rw [p.node]; rfl
          present9 := by rw [p.s1]; rfl
          present18 := by rw [p.env]; rfl
          present19 := by rw [savedFrame .x19 (by decide) (by decide) (by decide) (by decide) (by decide), h19]; rfl
          present20 := by rw [savedFrame .x20 (by decide) (by decide) (by decide) (by decide) (by decide), h20]; rfl
          present21 := by rw [savedFrame .x21 (by decide) (by decide) (by decide) (by decide) (by decide), h21]; rfl
          out := by change String.join arm.σ.sailOutput.toList = st.out; rw [p.out]; exact p.outStr }
      allocator := current, ast := ast
      gp := (savedFrame .x3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.gp
      window := { lo := stackLo, hi := by rw [lowered]; have := p.spRoom; omega }
      retained := by rw [outEq] at retained; exact retained }⟩

end Vsa.Sim.CallCallee
