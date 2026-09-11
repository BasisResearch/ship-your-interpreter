import Vsa.Sim.CallCalleePrefix
import Vsa.Sim.CallExprGround
import Vsa.Sim.AllocatorAt
import Vsa.Sim.MemPresence
import Vsa.Sim.Code.FixedImage_Eval_expr

namespace Vsa.Sim.CallCallee

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Source and machine inputs at the call arm before callee evaluation. -/
structure Input (SL : StackLayout) (A : Arena) (phiF : Addr → Nat)
    (st : Vsa.While.St) (d env : Nat) (e : Expr)
    (node sp interp child : BitVec 64) (before : Config) : Prop where
  geometry : BinaryPrefix.Geometry node sp
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some 0x800031b0#64
  regs : GHolds before.σ (callArmCalleeEvalL node sp (BitVec.ofNat 64 (phiF env)))
  interpReg : before.σ.regs.get? Register.x11 = some interp
  childRead : read64 before.σ.mem (node.toNat + 8) = some child.toNat
  ground : CallExprGround before.σ.mem SL A sp (sp + 96#64) d child.toNat e
  stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stackWin : tohostAddr + 16 ≤ SL.lo
  envValid : EnvValid st env
  storeBodies : StoreBodiesBound st.store perCallBudget
  present8 : (before.σ.regs.get? Register.x8).isSome = true
  present9 : (before.σ.regs.get? Register.x9).isSome = true
  present18 : (before.σ.regs.get? Register.x18).isSome = true
  present19 : (before.σ.regs.get? Register.x19).isSome = true
  present20 : (before.σ.regs.get? Register.x20).isSome = true
  present21 : (before.σ.regs.get? Register.x21).isSome = true
  out : OutRepr before.σ st

/-- The actual call entry retains its dispatch, shared bytes, and allocator. -/
structure OwnedPost (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop) (credits : Nat)
    (st : Vsa.While.St) (d env : Nat) (e : Expr)
    (node sp interp child : BitVec 64) (before called : Config) : Prop where
  entry : EvalAllocatorEntry called.σ.regs.get? N M phiF phiC alloc exts shared credits
    st d env e sp 0x800031c0#64 (sp + 96#64) interp child called.σ.mem called
  dispatch : Post node sp interp (BitVec.ofNat 64 (phiF env)) child before called
  agreement : AgreeP shared before.σ.mem called.σ.mem
  presence : MemExtends before.σ.mem called.σ.mem

/-- Build the owned child entry from the reflected callee prefix. -/
theorem Input.prepare
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {credits : Nat}
    {st : Vsa.While.St} {d env : Nat} {e : Expr}
    {node sp interp child : BitVec 64} {before : Config}
    (I : Input SL A phiF st d env e node sp interp child before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits st.store before.σ.mem)
    (ast : ExprReprWithin before.σ.mem shared child.toNat e)
    (gp : before.σ.regs.get? Register.x3 = some gpv) :
    ∃ called, Steps before called ∧
      OwnedPost N M phiF phiC alloc exts shared credits st d env e node sp interp child before called := by
  have support := I.ground.ground.eval_call
  obtain ⟨called, steps, post⟩ := run node sp interp (BitVec.ofNat 64 (phiF env)) child before
    I.geometry I.good I.tick I.pc I.regs I.interpReg support.image.text.Eval_exprLoaded I.childRead
  have resultAddr : (sp + 96#64).toNat = sp.toNat + 96 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := I.geometry.stackHi; change sp.toNat + 96 < 2^64; omega)]
    rfl
  have spLo : SL.lo ≤ sp.toNat := by have := I.ground.budget; exact Nat.le_trans (Nat.le_add_right _ _) this.1
  have retBounds := I.ground.ground.sret_inSL
  have spHi := I.ground.budget.2.1
  have frame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = called.σ.mem[k]? := by
    intro k hk
    apply post.outside k
    rw [resultAddr] at retBounds
    omega
  have presence : MemExtends before.σ.mem called.σ.mem := by
    rw [post.memory]
    exact memExtends_writeLog _ _
  have sharedFrame : AgreeP shared before.σ.mem called.σ.mem := fun k hk => frame k ((allocator.runtime L).shared_off_stack hk)
  have current := allocator.after_stack L frame
  have ground := I.ground.transport_stack presence frame
  have ast' := ast.transport sharedFrame
  obtain ⟨lo, hi, region⟩ := ground.ground.ast.region
  have childBounds := exprIn_node region.nodes
  have childLo := childBounds.lo_le
  have childHi := childBounds.hi_ge
  have support' := ground.ground.eval_call
  obtain ⟨code, valueInt, _, intSlot, nbs, _⟩ := support'.pins called.σ.mem (fun _ _ => rfl)
  obtain ⟨a0, a1, a2, a3, spReg, _⟩ := post.args
  have defined (R : Register) (hr : AbiPreserved R = true)
      (h : (before.σ.regs.get? R).isSome = true) : ∃ v, called.σ.regs.get? R = some v := by
    rw [post.frame R hr]
    exact Option.isSome_iff_exists.mp h
  have small : StackOK SL sp (1088 + 1088) := ground.budget.mono (by
    have := Expr.stackNeed_ge e
    change 1088 ≤ e.stackNeed at this
    omega)
  refine ⟨called, steps,
    { entry :=
        { entry :=
            { good := post.good, tick := post.tick, pc := post.pc
              a0 := a0, a1 := a1, a2 := a2, ra := post.ra, ra_align := by decide
              spReg := spReg, stackOK := small, stackBudget := ground.budget
              expr_bodies := ground.bodies, store_bodies := I.storeBodies
              minstret := post.minstret, mem := rfl, code := code, expr := ast'.erase
              store := current.repr, env_valid := I.envValid
              store_survives := ?_
              out := by simpa [OutRepr, output, post.output] using I.out
              frame := fun _ _ => rfl
              code_stack_disjoint := by have := support'.code_stack; omega
              expr_stack_disjoint := by have := region.stack_disjoint; omega
              expr_ram := by have := region.lo_ram; have := region.hi_ram; exact ⟨by omega, by omega⟩
              expr_win := by have := region.win; omega
              sret_align := by rw [resultAddr, Nat.add_mod, I.geometry.stackAlign]
              sret_ram := by rw [resultAddr] at retBounds ⊢; have := I.stackRam; exact ⟨by omega, by omega⟩
              sret_win := by rw [resultAddr]; have := I.stackWin; omega
              sret_vicode_disjoint := by have := support'.vi_stack; omega
              sret_stack_disjoint := by rw [resultAddr]; right; omega
              sret_evalcode_disjoint := by have := support'.code_stack; omega
              vicode_stack_disjoint := by have := support'.vi_stack; omega
              stack_ram := I.stackRam, stack_win := I.stackWin
              value_int_code := valueInt, int_slot := intSlot
              table_stack_disjoint := by have := support'.table_stack; exact Or.imp id (fun h => Nat.le_trans spHi h) this
              nbs_pins := nbs, ground := ground.ground
              spill_defined := ⟨defined .x8 (by decide) I.present8,
                defined .x9 (by decide) I.present9, defined .x18 (by decide) I.present18⟩
              envset_defined := ?_, envReg := a3, x13_defined := ⟨_, a3⟩
              sret_words := ground.ground.valueWordsTotal retBounds.1 retBounds.2 }
          allocator := current, ast := ast', gp := (post.frame .x3 (by decide)).trans gp }
      dispatch := post, agreement := sharedFrame, presence := presence }⟩
  · intro mem hm
    apply ((current.runtime L).after_stack _).repr
    intro k hk
    exact hm k hk (by have := ground.ground.sret_inSL; omega)
  · obtain ⟨v19, h19⟩ := defined .x19 (by decide) I.present19
    obtain ⟨v20, h20⟩ := defined .x20 (by decide) I.present20
    obtain ⟨v21, h21⟩ := defined .x21 (by decide) I.present21
    exact ⟨v19, v20, v21, h19, h20, h21⟩

end Vsa.Sim.CallCallee
