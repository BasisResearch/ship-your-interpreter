import Vsa.Sim.ClosureCallPrefix
import Vsa.Sim.ClosureScopeAllocator
import Vsa.Sim.ClosureParamFoldEntry

namespace Vsa.Sim.ClosureCallPrefix

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Physical caller resources consumed by the existing scope allocator. -/
structure ScopeResources (A : Arena) (SL : StackLayout) (phiF : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (sp interp parent gpv savedS6 : BitVec 64)
    (before : Config) : Prop where
  envValid : EnvValid st env
  parentAddr : parent = BitVec.ofNat 64 (phiF env)
  stack : StackOK SL sp 1088
  stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stackWin : tohostAddr + 16 ≤ SL.lo
  stackBytes : StackBytesPresent before.σ.mem SL
  stackHi : sp.toNat + 1056 ≤ SL.hi
  interpLo : SL.lo ≤ interp.toNat + 8
  interpHi : interp.toNat + 12 ≤ SL.hi
  support : EvalCallSupport before.σ.mem SL A sp
  gp : before.σ.regs.get? Register.x3 = some gpv
  s6 : before.σ.regs.get? Register.x22 = some savedS6

/-- Ownership and allocator entry at the same reached env_new call. -/
structure ScopeReady (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (st : Vsa.While.St) (env : Addr)
    (sp parent savedS6 : BitVec 64) (before called : Config) : Prop where
  entry : EnvNewEntryState called.σ.regs.get? N A SL phiF phiC st env sp parent
    0x800032c0#64 called.σ.mem before.σ.sailOutput called
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits st.store called.σ.mem
  support : EvalCallSupport called.σ.mem SL A sp
  gp : called.σ.regs.get? Register.x3 = some gpv
  s6 : called.σ.regs.get? Register.x22 = some savedS6
  agreement : AgreeP shared before.σ.mem called.σ.mem
  presence : MemExtends before.σ.mem called.σ.mem
  stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = called.σ.mem[k]?
  arguments : ∀ k, sp.toNat + 240 ≤ k → k < sp.toNat + 1008 → before.σ.mem[k]? = called.σ.mem[k]?

/-- Dispatch writes preserve the owned runtime and every evaluated argument slot. -/
theorem Post.scope_ready
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {env : Addr}
    {sp call object fn interp parent saved5 saved3 savedS6 : BitVec 64}
    {count depth : Nat} {before called : Config}
    (h : Post sp call object fn interp parent saved5 saved3 count depth before called)
    (G : Geometry sp call object fn interp)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits st.store before.σ.mem)
    (R : ScopeResources A SL phiF st env sp interp parent gpv savedS6 before) :
    ScopeReady N M phiF phiC alloc exts shared credits st env sp parent savedS6 before called := by
  have stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = called.σ.mem[k]? := by
    intro k hk
    apply h.outside k
    unfold footprint
    have := R.stack.1; have := R.stackHi; have := R.interpLo; have := R.interpHi
    omega
  have reached := allocator.after_stack L stackFrame
  have support : EvalCallSupport called.σ.mem SL A sp :=
    R.support.transport_stack (fun k hk => (stackFrame k hk).symm)
  have presence : MemExtends before.σ.mem called.σ.mem := by
    rw [h.memory]
    exact memExtends_writeLog _ _
  refine
    { entry :=
        { good := h.good, tick := h.tick, pc := h.pc
          a0 := ?_, ra := h.ra, ra_align := by decide, sp := ?_
          minstret := h.minstret, mem := rfl, out := h.output, frame := fun _ _ => rfl
          facts :=
            { text := support.image.text, store := reached.repr
              store_survives := fun _ hm => (reached.after_stack L hm).repr
              env_valid := R.envValid, env_addr := R.parentAddr, stack := R.stack
              stack_ram := R.stackRam, stack_win := R.stackWin
              stack_bytes := ?_
              arena_stack := L.arena_stack.imp id (fun ha => by have := R.stackHi; omega) } }
      allocator := reached, support := support
      gp := (h.frame .x3 (by decide) (by decide) (by decide)).trans R.gp
      s6 := (h.frame .x22 (by decide) (by decide) (by decide)).trans R.s6
      agreement := fun k hk => stackFrame k ((allocator.runtime L).shared_off_stack hk)
      presence := presence, stackFrame := stackFrame, arguments := ?_ }
  · exact gholds_lookup _ h.regs (show lookupG 10 _ = some parent from rfl)
  · exact gholds_lookup _ h.regs (show lookupG 2 _ = some sp from rfl)
  · intro k lo hi
    obtain ⟨b, hb⟩ := R.stackBytes k lo hi
    exact presence k b hb
  · intro k lo hi
    apply h.outside k
    unfold footprint
    have := G.interpAbove
    omega

/-- The reached call allocates the fresh scope and selects binding or the empty bypass. -/
theorem ScopeReady.allocate
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {env : Addr}
    {sp call object fn interp parent saved5 saved3 savedS6 : BitVec 64}
    {count depth : Nat} {before called : Config}
    (ready : ScopeReady N M phiF phiC alloc exts shared (credits + 1) st env sp parent savedS6 before called)
    (post : Post sp call object fn interp parent saved5 saved3 count depth before called)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (stackHi : sp.toNat + 1032 ≤ SL.hi) (countBound : count < 2^31) :
    ∃ after p, Steps called after ∧
      ClosureScopePost called.σ.regs.get? N M phiF phiC alloc exts shared credits st env
        sp p savedS6 count (decide (0 < count)) called.σ.mem before.σ.sailOutput after := by
  apply closureScopeAllocator_run L ready.entry ready.allocator ready.support ready.gp
    (savedS6 := savedS6)
  · exact ⟨call, gholds_lookup _ post.regs (show lookupG 8 _ = some call from rfl)⟩
  · exact ready.s6
  · exact stackHi
  · exact post.countRead
  · exact countBound
  · rfl

/-- Dispatch and scope allocation share the actual binding/bypass endpoint. -/
structure AllocatedCallAt (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (st : Vsa.While.St) (env : Addr)
    (sp call object fn interp parent saved5 saved3 savedS6 : BitVec 64)
    (count depth : Nat) (before called : Config) (p : BitVec 64) (after : Config) : Prop where
  dispatch : Post sp call object fn interp parent saved5 saved3 count depth before called
  ready : ScopeReady N M phiF phiC alloc exts shared (credits + 1) st env
    sp parent savedS6 before called
  scopePost : ClosureScopePost called.σ.regs.get? N M phiF phiC alloc exts shared credits st env
    sp p savedS6 count (decide (0 < count)) called.σ.mem before.σ.sailOutput after
  run : Steps before after

/-- Execute dispatch and scope creation, including the zero-parameter bypass. -/
theorem Pre.allocate
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {env : Addr}
    {sp call object fn interp parent a3 saved5 saved3 savedS6 : BitVec 64}
    {count depth : Nat} {before : Config}
    (pre : Pre sp call object fn interp parent a3 saved5 saved3 count depth before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (credits + 1) st.store before.σ.mem)
    (R : ScopeResources A SL phiF st env sp interp parent gpv savedS6 before) :
    ∃ called p after, AllocatedCallAt N M phiF phiC alloc exts shared credits st env
      sp call object fn interp parent saved5 saved3 savedS6 count depth before called p after := by
  obtain ⟨called, dispatchSteps, dispatch⟩ := run pre
  have ready := dispatch.scope_ready pre.geometry L allocator R
  obtain ⟨after, p, allocationSteps, scopePost⟩ := ready.allocate dispatch L
    (by have := R.stackHi; omega) (by have := pre.reads.countBound; omega)
  exact ⟨called, p, after,
    { dispatch := dispatch, ready := ready, scopePost := scopePost
      run := dispatchSteps.trans allocationSteps }⟩

/-- An empty call reaches the existing body initializer directly. -/
theorem AllocatedCallAt.empty_pc
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {env : Addr}
    {sp call object fn interp parent saved5 saved3 savedS6 p : BitVec 64}
    {depth : Nat} {before called after : Config}
    (h : AllocatedCallAt N M phiF phiC alloc exts shared credits st env
      sp call object fn interp parent saved5 saved3 savedS6 0 depth before called p after) :
    after.σ.regs.get? Register.PC = some 0x80003324#64 := h.scopePost.pc

end Vsa.Sim.ClosureCallPrefix
