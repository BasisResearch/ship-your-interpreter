import Vsa.Sim.CallArgOwned

namespace Vsa.Sim.CallArgStage

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The evaluated argument and current store share the child's selected allocator maps. -/
structure Evaluated (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (nf nc : Nat) (shared : Nat → Prop) (reserve : Nat)
    (st : Vsa.While.St) (value : Value) (sp env : BitVec 64) (index count : Nat) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x80003224#64
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  spReg : after.σ.regs.get? Register.x2 = some sp
  selected : ∃ resultF resultC,
    ReturnRepr N A phiF phiC resultF resultC nf nc st.store [((sp + 64#64).toNat, value)]
      (AllocatorResult M N shared reserve st.store [((sp + 64#64).toNat, value)] before.σ.mem)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem
  gp : after.σ.regs.get? Register.x3 = some gpv
  support : EvalCallSupport after.σ.mem SL A sp
  saved : Saved after.σ.mem sp env index count
  words : ValueWordsTotal after.σ.mem (sp + 64#64).toNat
  presence : MemExtends before.σ.mem after.σ.mem
  frame : ∀ R, AbiPreservedNoise R → after.σ.regs.get? R = before.σ.regs.get? R
  memoryFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat + 32) → ¬ (A.lo ≤ k ∧ k < A.hi) →
    ¬ ((sp + 64#64).toNat ≤ k ∧ k < (sp + 64#64).toNat + 24) →
      before.σ.mem[k]? = after.σ.mem[k]?
  out : OutRepr after.σ st

/-- Execute the actual argument staging and recursive child, retaining the owned result. -/
theorem Input.evaluate
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {cost request reserve : Nat}
    {st final : Vsa.While.St} {d env : Nat} {e : Expr} {value : Value}
    {node sp interp base child : BitVec 64} {index count : Nat} {before : Config}
    (I : Input SL A phiF st d env e node sp interp base child index count before)
    (L : AllocLedger A SL gpv headroom maxReq M) (requestBound : request ≤ maxReq)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (cost + reserve) st.store before.σ.mem)
    (ast : ExprReprWithin before.σ.mem shared child.toNat e)
    (gp : before.σ.regs.get? Register.x3 = some gpv)
    (ih : EvalAllocatorAt N st d env e final value cost request) :
    ∃ after, Steps before after ∧ Evaluated N M phiF phiC st.store.frames.size st.store.closures.size
      shared reserve final value sp (BitVec.ofNat 64 (phiF env)) index count before after := by
  obtain ⟨called, prefixSteps, prepared⟩ := I.prepare L allocator ast gp
  obtain ⟨after, childSteps, returned⟩ := ih.run called.σ.regs.get? A SL gpv headroom maxReq M L
    requestBound phiF phiC alloc exts shared reserve sp 0x80003224#64 (sp + 64#64) interp child
    called.σ.mem called prepared.entry
  obtain ⟨exit, presence, words, _⟩ := returned.returned.exit
  obtain ⟨resultF, resultC, repr⟩ := returned.returned.repr.selected
  have resultAddr : (sp + 64#64).toNat = sp.toNat + 64 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := I.geometry.caller.stackHi; change sp.toNat + 64 < 2^64; omega)]
    rfl
  have spLo : SL.lo ≤ sp.toNat := Nat.le_trans (Nat.le_add_right _ _) I.ground.budget.1
  have spHi := I.ground.budget.2.1
  have retBounds := I.ground.ground.sret_inSL
  have abi : ∀ R, AbiPreservedNoise R → AbiPreserved R = true := by intro R; cases R <;> decide
  have kept : AgreeP (fun k => sp.toNat ≤ k ∧ k < sp.toNat + 32) called.σ.mem after.σ.mem := by
    intro k hk
    symm
    apply (exit.memFrame k (by omega) (by have := L.arena_stack; rw [resultAddr] at retBounds; omega)).resolve_left
    rw [resultAddr]
    omega
  refine ⟨after, prefixSteps.trans childSteps,
    { good := exit.good, tick := exit.tick, pc := exit.pc, minstret := exit.minstret
      spReg := exit.spReg
      selected := ⟨resultF, resultC, repr.withOwnership
        (repr.owned.rebase (fun _ hk => hk) prepared.agreement)⟩
      gp := returned.gp
      support := prepared.entry.entry.ground.eval_call.transport_frame spHi retBounds exit.memFrame
      saved := prepared.dispatch.saved.transport kept, words := words
      presence := prepared.presence.trans presence
      frame := fun R hr => (exit.frame R hr).trans (prepared.dispatch.frame R (abi R hr))
      memoryFrame := ?_, out := exit.out }⟩
  intro k hs ha hr
  exact (prepared.dispatch.outside k (by omega)).trans
    ((exit.memFrame k (by omega) ha).resolve_left hr).symm

end Vsa.Sim.CallArgStage
