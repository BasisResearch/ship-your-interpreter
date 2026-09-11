import Vsa.Sim.BinaryAllocatorHead
import Vsa.Sim.BinaryEntry
import Vsa.Sim.BinaryArmFrame

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- The complete operand run retains the actual arm ghost and its outer-frame relation. -/
structure BinaryAllocatorOperands
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (nf nc : Nat) (shared : Nat → Prop) (reserve : Nat)
    (middle final : Vsa.While.St) (vl vr : Value)
    (sp ret dst node : BitVec 64) (m0 : Mem) (after : Config) : Prop where
  selected : ∃ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
    ReturnedWith (fun _ => BinaryArmFrame g gpre sp node v8 v9 v18 v19)
      (BinaryAllocatorHeadReturn gpre N M phiF phiC nf nc shared reserve
        middle final vl vr sp ret dst v8 v9 v18 m0) after

/-- Dispatch a binary expression and retain both owned child results at fixed native addresses. -/
theorem evalBinaryAllocatorOperands_at
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st middle final : Vsa.While.St} {d env : Nat} {op : BinOp} {el er : Expr}
    {vl vr : Value} {costL costR maxRequest reserve : Nat}
    {sp ret dst node interp : BitVec 64} {m0 : Mem}
    (L : AllocLedger A SL gpv headroom maxReq M) (request : maxRequest ≤ maxReq)
    (leftSem : EvalE st d env el middle vl)
    (bounded : StoreClosuresBounded st.store)
    (leftIH : EvalAllocatorAt N st d env el middle vl costL maxRequest)
    (rightIH : EvalAllocatorAt N middle d env er final vr costR maxRequest) :
    Triple (EvalAllocatorEntry g N M phiF phiC alloc exts shared
      (costL + (costR + reserve)) st d env (.binary op el er) sp ret dst interp node m0)
      (BinaryAllocatorOperands g N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve middle final vl vr sp ret dst node m0) := by
  intro before h
  obtain ⟨left, right, extras⟩ := h.entry.binaryExtras
  have middleBodies := StoreBodiesBound.afterEvalE leftSem
    (Expr.bodiesBound_binary h.entry.expr_bodies).1 h.entry.store_bodies
  obtain ⟨arm, stepsA, gpre, envReg, v8, v9, v18, v19, ment, hArm, geometry, recursion,
    _interp, environment, saved19, frame, _g8, _g18, ghostNode, ghostInterp, ghost19,
    leftRead, _leftRepr, rightRead, _rightRepr, presence, ground,
    leftBudget, leftBodies, storeBodies, rightBudget, rightBodies, _middleBodies⟩ :=
    blockA_binaryArm_budgeted g N A SL phiF phiC st middle d env op el er
      sp ret dst interp node left right m0 extras middleBodies before h.entry
  have p := ArmEntryK.destruct g N A SL phiF phiC st 0x800034e8#64 UnaryArmCallee
    (.binary op el er) sp ret dst node interp v8 v9 v18 arm.σ.sailOutput m0 ment arm hArm
  have memory := p.mem
  subst ment
  have ready : BinaryArmReady g gpre N A SL phiF phiC st d env op el er
      sp ret dst node interp left right envReg v8 v9 v18 v19 arm.σ.sailOutput m0 arm :=
    { arm := hArm, geometry := geometry, recursion := recursion
      environment := environment, saved19 := saved19, frame := frame
      ghostNode := ghostNode, ghostInterp := ghostInterp, ghost19 := ghost19
      leftRead := leftRead, rightRead := rightRead, presence := presence, ground := ground
      leftBudget := leftBudget, rightBudget := rightBudget
      leftBodies := leftBodies, rightBodies := rightBodies, storeBodies := storeBodies }
  have agreement : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = arm.σ.mem[k]? := by
    intro k hk
    rw [h.entry.mem]
    exact (p.memFrame k (by have := geometry.spSLhi; omega)).symm
  have allocator := h.allocator.after_stack L agreement
  have ast := h.ast.transport (fun k hk => agreement k ((h.allocator.runtime L).shared_off_stack hk))
  have gp : arm.σ.regs.get? Register.x3 = some gpv :=
    (p.frame .x3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((h.entry.frame .x3 (by decide)).symm.trans h.gp)
  obtain ⟨after, stepsB, result⟩ := ready.run_allocator_at L request allocator ast gp
    leftSem bounded leftIH rightIH
  exact ⟨after, stepsA.trans stepsB,
    { selected := ⟨gpre, v8, v9, v18, v19, BinaryArmFrame.of_entry hArm frame ghost19, result⟩ }⟩

/-- Dispatch a binary expression, execute both children, and retain their owned results. -/
theorem evalBinaryAllocatorOperands
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st middle final : Vsa.While.St} {d env : Nat} {op : BinOp} {el er : Expr}
    {vl vr : Value} {costL costR maxRequest reserve : Nat}
    {sp ret dst node interp : BitVec 64} {m0 : Mem}
    (L : AllocLedger A SL gpv headroom maxReq M) (request : maxRequest ≤ maxReq)
    (leftSem : EvalE st d env el middle vl)
    (bounded : StoreClosuresBounded st.store)
    (leftIH : EvalAllocatorIH st d env el middle vl costL maxRequest)
    (rightIH : EvalAllocatorIH middle d env er final vr costR maxRequest) :
    Triple (EvalAllocatorEntry g N M phiF phiC alloc exts shared
      (costL + (costR + reserve)) st d env (.binary op el er) sp ret dst interp node m0)
      (BinaryAllocatorOperands g N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve middle final vl vr sp ret dst node m0) :=
  evalBinaryAllocatorOperands_at L request leftSem bounded (leftIH.at N) (rightIH.at N)

#print axioms evalBinaryAllocatorOperands_at
#print axioms evalBinaryAllocatorOperands

end Vsa.Sim
