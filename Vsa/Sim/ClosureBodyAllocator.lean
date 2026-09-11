import Vsa.Sim.HelperCallNull
import Vsa.Sim.AstReadGeometry
import Vsa.Sim.ClosureBodyDispatch
import Vsa.Sim.ClosureBodyNull
import Vsa.Sim.ExecSeqAllocatorAt
import Vsa.Sim.SeqSuffixStack
import Vsa.Sim.Code.FixedImage_Eval_expr
import Vsa.Sim.Code.FixedImage_Value_null

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open RuntimeOwnership

/-- The bound closure body at its return-slot initializer. -/
structure ClosureBodyInput (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF : Addr → Nat) (shared : Nat → Prop) (st : Vsa.While.St) (d env : Nat)
    (ss : List Stmt) (sp closure body base interp : BitVec 64) (before : Config) : Prop where
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some 0x80003324#64
  minstret : ∃ w, before.σ.regs.get? Register.minstret = some w
  spReg : before.σ.regs.get? Register.x2 = some sp
  closureReg : before.σ.regs.get? Register.x21 = some closure
  interpReg : before.σ.regs.get? Register.x18 = some interp
  envReg : before.σ.regs.get? Register.x19 = some (BitVec.ofNat 64 (phiF env))
  bodyRead : read64 before.σ.mem (closure.toNat + 32) = some body.toNat
  bodyCovered : Covers shared (closure.toNat + 32) 8
  baseRead : read64 before.σ.mem (body.toNat + 8) = some base.toNat
  countRead : read32 before.σ.mem (body.toNat + 16) = some ss.length
  countBound : ss.length < 2^31
  suffix : SeqSuffixOwned before.σ.mem shared SL A sp (sp + 144#64) d base.toNat ss
  resources : ExecSeqClosureResources A SL shared body before.σ.regs.get?
  support : EvalCallSupport before.σ.mem SL A sp
  envValid : EnvValid st env
  storeBodies : StoreBodiesBound st.store perCallBudget
  out : OutRepr before.σ st
  stackOK : StackOK SL sp (176 + 1088)
  stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stackWin : tohostAddr + 16 ≤ SL.lo
  bufferHi : sp.toNat + 168 ≤ SL.hi

/-- The reached owned sequence and exact caller frame after body setup. -/
structure ClosureBodyPost (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (st : Vsa.While.St) (d env : Nat)
    (ss : List Stmt) (sp : BitVec 64) (before after : Config) : Prop where
  entry : ExecSeqAllocatorEntry .closureBody before.σ.regs.get? N M phiF phiC alloc exts shared
    credits st d env ss sp (sp + 144#64) after.σ.mem after
  value : ValueRepr after.σ.mem N phiC (sp + 144#64).toNat .null
  outside : ∀ k, ¬ ((sp + 144#64).toNat ≤ k ∧ k < (sp + 144#64).toNat + 24) →
    before.σ.mem[k]? = after.σ.mem[k]?
  stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = after.σ.mem[k]?
  highStack : ExecSeqStackFrame .closureBody A SL sp (sp + 144#64) before.σ.mem after.σ.mem
  agreement : AgreeP shared before.σ.mem after.σ.mem
  presence : MemExtends before.σ.mem after.σ.mem
  frame : ∀ R, AbiExceptS0 R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Initialize the body result and enter the owned sequence on either count branch. -/
theorem closureBodyAllocator_run
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {d env : Nat}
    {ss : List Stmt} {sp closure body base interp : BitVec 64} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (I : ClosureBodyInput N A SL phiF shared st d env ss sp closure body base interp before)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits st.store before.σ.mem)
    (gp : before.σ.regs.get? Register.x3 = some gpv) :
    ∃ after, Steps before after ∧
      ClosureBodyPost N M phiF phiC alloc exts shared credits st d env ss sp before after := by
  have spLo := I.stackOK.1
  have spAlign := I.stackOK.2.2
  have ram := I.stackRam
  have high := I.bufferHi
  have win := I.stackWin
  have bufNat : (sp + 144#64).toNat = sp.toNat + 144 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change sp.toNat + 144 < 2^64; omega)]
    rfl
  have region : NullRegion (sp + 144#64) := by
    have codeOff := I.support.image.stack_disjoint
      (lo := 0x800027ec) (hi := 0x800027f8) (by decide) (by decide)
    constructor
    · rw [bufNat]; omega
    · rw [bufNat]; omega
    · rw [bufNat]; omega
    · rw [bufNat]; omega
    · rw [bufNat]; omega
  obtain ⟨initialized, nullSteps, initializedPost⟩ := closureBodyNull_run before sp N phiC
    I.good I.tick I.pc I.spReg I.minstret I.support.image.text.Eval_exprLoaded
    I.support.image.text.Value_nullLoaded region
  have stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
      before.σ.mem[k]? = initialized.σ.mem[k]? := by
    intro k hk
    apply initializedPost.outside k
    rw [bufNat]
    omega
  have agreement : AgreeP shared before.σ.mem initialized.σ.mem :=
    fun k hk => stackFrame k ((allocator.runtime L).shared_off_stack hk)
  have allocator' := allocator.after_stack L stackFrame
  have suffix := I.suffix.transport_stack initializedPost.presence stackFrame agreement
  have support : EvalCallSupport initialized.σ.mem SL A sp :=
    I.support.transport_stack (fun k hk => (stackFrame k hk).symm)
  have keepNull (R : Register) (abi : AbiPreserved R = true) :
      initialized.σ.regs.get? R = before.σ.regs.get? R := by
    apply initializedPost.frame R (notWrittenV_of_abiPreserved R abi)
    · exact wrChain_ne_abi (by decide : WrChainAvoidAbi callClosureValueNullCallSeg) abi
    · exact abiPreserved_ne abi (by decide)
  have domain := SharedReadDomain.of_immutable allocator'.heap.immutable
  have bodyGeometry := AstReadGeometry.of_domain domain I.bodyCovered (by decide)
  have countGeometry := AstReadGeometry.of_domain domain I.resources.countCovered (by decide)
  have baseRead := (read64_agreeP agreement I.resources.baseCovered).symm.trans I.baseRead
  have countRead := (read32_agreeP agreement I.resources.countCovered).symm.trans I.countRead
  have pre : ClosureBodyDispatch.Pre closure body ss.length (decide (0 < ss.length)) initialized :=
    { good := initializedPost.good, tick := initializedPost.tick, pc := initializedPost.pc
      minstret := initializedPost.minstret
      closureReg := (keepNull .x21 (by decide)).trans I.closureReg
      geometry :=
        { closureLo := bodyGeometry.ram_lo, closureHi := bodyGeometry.ram_hi
          closureHtif := bodyGeometry.htif.imp id (fun h => by omega)
          bodyLo := countGeometry.ram_lo, bodyHi := countGeometry.ram_hi
          bodyHtif := countGeometry.htif.imp id (fun h => by omega) }
      bodyRead := (read64_agreeP agreement I.bodyCovered).symm.trans I.bodyRead
      countRead := countRead, countBound := I.countBound, branch := rfl
      code := support.image.text.Eval_exprLoaded }
  obtain ⟨after, dispatchSteps, post⟩ := ClosureBodyDispatch.run pre
  have keep (R : Register) (abi : AbiExceptS0 R = true) :
      after.σ.regs.get? R = before.σ.regs.get? R :=
    (post.frame R abi).trans (keepNull R (Bool.and_eq_true_iff.mp abi).1)
  have spReg := (keep .x2 (by decide)).trans I.spReg
  have envReg := (keep .x19 (by decide)).trans I.envReg
  have interpReg := (keep .x18 (by decide)).trans I.interpReg
  have reached : SeqSuffixOwned after.σ.mem shared SL A sp (sp + 144#64) d base.toNat ss := by
    rw [post.memory]; exact suffix
  have allocatorAfter : RuntimeAllocatorState M N phiF phiC alloc exts shared credits st.store
      after.σ.mem := by rw [post.memory]; exact allocator'
  have survives : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → after.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A phiF phiC st.store :=
    fun _ hm => ((allocatorAfter.runtime L).after_stack hm).repr
  have ready : ss ≠ [] → ExecSeqLoopReady .closureBody N A SL phiF phiC st d env ss
      sp (sp + 144#64) after := by
    intro nonempty
    refine
      { env_valid := I.envValid
        code := by rw [post.memory]; exact pre.code
        cursor := ⟨body, base, 0, ss.length, post.bodyReg, post.indexReg, envReg, spReg, rfl,
          by rw [post.memory]; exact baseRead, by rw [post.memory]; exact countRead,
          by omega, I.countBound, ?_⟩
        head_ground := ?_
        store_survives := survives, stack_ram := I.stackRam, stack_win := I.stackWin }
    · simpa only [Nat.mul_zero, Nat.add_zero] using reached.reads.erase
    · cases ss with
      | nil => exact False.elim (nonempty rfl)
      | cons s rest =>
        obtain ⟨p, cell, ground⟩ := reached.head
        have bound : p < 2^64 := read64_lt_eg4 _ _ _ cell.read
        have pn : (BitVec.ofNat 64 p).toNat = p := Nat.mod_eq_of_lt bound
        refine ⟨BitVec.ofNat 64 p, ?_, ?_, ⟨interp, interpReg, envReg, rfl⟩, ?_,
          I.stackOK, ground.stackBudget, ground.bodies, I.storeBodies⟩
        · refine ⟨body, base, 0, post.bodyReg, post.indexReg, ?_, ?_⟩
          · rw [post.memory]; exact baseRead
          · simpa only [Nat.mul_zero, Nat.add_zero, pn] using cell.read
        · rw [pn]; exact ground.stmt
        · rw [pn]; exact ground.ground
  refine ⟨after, nullSteps.trans dispatchSteps,
    { entry :=
        { entry :=
            { good := post.good, tick := post.tick, pc := ?_, minstret := post.minstret
              store := allocatorAfter.repr, store_survives := survives
              out := by simpa [OutRepr, output, post.output, initializedPost.output] using I.out
              mem := rfl, ready := ready, empty_status := fun _ => trivial
              frame := fun R hR => keep R (by
                simp only [AbiExceptS0, hR.1.1, Bool.true_and]
                simpa using hR.2) }
          allocator := allocatorAfter
          suffix := fun _ => ⟨base.toNat, ?_, reached⟩
          closureResources := fun _ _ => ⟨body, post.bodyReg, ?_⟩
          interpResources := by intro impossible; cases impossible
          blockResources := by intro impossible; cases impossible
          gp := (keep .x3 (by decide)).trans gp }
      value := by rw [post.memory]; exact initializedPost.value
      outside := by rw [post.memory]; exact initializedPost.outside
      stackFrame := by rw [post.memory]; exact stackFrame
      highStack := by
        intro k hlo _
        rw [post.memory]
        apply (initializedPost.outside k ?_).symm
        rw [bufNat]
        omega
      agreement := by rw [post.memory]; exact agreement
      presence := by rw [post.memory]; exact initializedPost.presence
      frame := keep }⟩
  · cases ss with
    | nil => exact post.pc
    | cons s rest => exact post.pc
  · have hbase : read64 after.σ.mem (body.toNat + 8) = some base.toNat := by
      rw [post.memory]; exact baseRead
    simpa only [Nat.mul_zero, Nat.add_zero] using
      ExecSeqArrayAt.closureBody post.bodyReg (index := 0) post.indexReg hbase
  · refine { I.resources with spill9 := ?_, spill20 := ?_, spill21 := ?_ }
    · obtain ⟨v, hv⟩ := I.resources.spill9
      exact ⟨v, (keep .x9 (by decide)).trans hv⟩
    · obtain ⟨v, hv⟩ := I.resources.spill20
      exact ⟨v, (keep .x20 (by decide)).trans hv⟩
    · obtain ⟨v, hv⟩ := I.resources.spill21
      exact ⟨v, (keep .x21 (by decide)).trans hv⟩

#print axioms closureBodyAllocator_run

end Vsa.Sim
