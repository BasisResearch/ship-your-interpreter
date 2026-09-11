import Vsa.Sim.ClosureParamFoldData
import Vsa.Sim.ClosureParamDefineOwned
import Vsa.Sim.ClosureParamOwnedResume

namespace Vsa.Sim.ClosureParam

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Dispatch the actual binding call using the current scope's bindings and capacity. -/
theorem OwnedPost.define_next_owned
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {value : Value} {param : String}
    {sp cursor index scope closure name : BitVec 64} {before called : Config} {target : Addr}
    (h : OwnedPost N M phiF phiC alloc exts shared (credits + 3) st.store value param
      sp cursor index scope closure name before called)
    (L : AllocLedger A SL gpv headroom maxReq M) (placement : BindingArena A SL)
    (valid : target < st.store.frames.size) (scopeAddr : scope.toNat = phiF target)
    (stack : StackOK SL sp 1088)
    (stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (stackWin : tohostAddr + 16 ≤ SL.lo) (bufferHi : sp.toNat + 88 ≤ SL.hi)
    (support : EvalCallSupport before.σ.mem SL A sp)
    (present : EnvDefineSavedPresent (fun R => called.σ.regs.get? R))
    (unique : FrameUnique st.store.frames[target])
    (bounded : ValueClosuresBounded st.store.closures.size value)
    (emptyCapacity : st.store.frames[target].vars.length = 0 →
      read32 called.σ.mem (phiF target + 4) = some 0)
    (nameRequest : param.length + 1 ≤ maxReq)
    (growRequest : 48 * st.store.frames[target].vars.length ≤ maxReq) :
    ∃ after, Steps called after ∧
      EnvDefineOwnedReturn (fun R => called.σ.regs.get? R) N M phiF phiC shared credits st target param value
        sp 0x80003314#64 called.σ.mem called.σ.sailOutput after := by
  classical
  by_cases empty : st.store.frames[target].vars.length = 0
  · exact h.define_empty_owned L placement valid scopeAddr stack stackRam stackWin bufferHi
      support present (emptyCapacity empty) nameRequest bounded
  by_cases hit : ∃ i, ∃ hi : i < st.store.frames[target].vars.length,
      st.store.frames[target].vars[i].1 = param
  · have reduced : OwnedPost N M phiF phiC alloc exts shared credits st.store value param
        sp cursor index scope closure name before called :=
      { h with allocator := h.allocator.credit_mono (by omega) }
    exact reduced.define_hit_owned L valid scopeAddr stack stackRam stackWin bufferHi support
      present unique bounded hit
  · exact h.define_miss_owned L placement valid scopeAddr stack stackRam stackWin bufferHi
      support present bounded (by omega) (by
        intro i hi eq
        exact hit ⟨i, hi, eq⟩) nameRequest growRequest

/-- One binding and its actual fold branch retain the next iteration's complete data. -/
structure FoldReturnAt
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (N : NativeAddrs) (phiF phiC : Addr → Nat)
    (entryShared : Nat → Prop) (credits : Nat) (store : Store)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop)
    (sp cursor scope closure names savedS6 : BitVec 64) (params : List String) (values : List Value)
    (index : Nat) (more : Bool) (before returned after : Config) : Prop where
  result : AllocatorResultAt M N entryShared credits store [] before.σ.mem
    phiF phiC alloc exts shared after.σ.mem
  data : FoldData after.σ.mem N phiC shared sp closure names params values
  resume : ClosureParamResume.Post sp savedS6 index values.length more returned after
  cursor : after.σ.regs.get? Register.x8 = some (cursor + 24#64)
  scope : after.σ.regs.get? Register.x19 = some scope
  closure : after.σ.regs.get? Register.x21 = some closure
  gp : after.σ.regs.get? Register.x3 = some gpv
  frame : ∀ R, ClosureEnvNewResume.keep R = true →
    after.σ.regs.get? R = before.σ.regs.get? R
  output : after.σ.sailOutput = before.σ.sailOutput
  presence : MemExtends before.σ.mem after.σ.mem
  memoryFrame : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < SL.hi) →
    before.σ.mem[k]? = after.σ.mem[k]?
  support : EvalCallSupport after.σ.mem SL A sp
  savedRead : read64 after.σ.mem (sp.toNat + 1024) = some savedS6.toNat
  arguments : ∀ k, sp.toNat + 240 ≤ k → k < sp.toNat + 1008 →
    before.σ.mem[k]? = after.σ.mem[k]?
  highStack : ∀ k, sp.toNat + 1032 ≤ k → k < SL.hi →
    before.σ.mem[k]? = after.σ.mem[k]?
  saved7Frame : ∀ k, sp.toNat + 1016 ≤ k → k < sp.toNat + 1024 →
    before.σ.mem[k]? = after.σ.mem[k]?

/-- Join the staged call, owned helper return, and reflected branch at one selected runtime. -/
theorem OwnedPost.resume_fold
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {value : Value} {param : String}
    {sp cursor scope closure names name savedS6 : BitVec 64}
    {before called returned : Config} {target index : Nat} {params : List String} {values : List Value}
    (h : OwnedPost N M phiF phiC alloc exts shared (credits + 3) st.store value param
      sp cursor (BitVec.ofNat 64 (8 * index)) scope closure name before called)
    (data : FoldData before.σ.mem N phiC shared sp closure names params values)
    (exit : EnvDefineOwnedReturn (fun R => called.σ.regs.get? R) N M phiF phiC shared credits
      st target param value sp 0x80003314#64 called.σ.mem called.σ.sailOutput returned)
    (geometry : ClosureEnvNewResume.Geometry sp)
    (stackLo : SL.lo ≤ sp.toNat) (stackHi : sp.toNat + 1032 ≤ SL.hi)
    (arenaStack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo)
    (bound : before.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 (8 * values.length)))
    (savedRead : read64 before.σ.mem (sp.toNat + 1024) = some savedS6.toNat)
    (indexLt : index < values.length)
    (support : EvalCallSupport before.σ.mem SL A sp) :
    ∃ after alloc' exts' shared', Steps returned after ∧
      FoldReturnAt M N phiF phiC shared credits (st.store.define target param value)
        alloc' exts' shared' sp cursor scope closure names savedS6 params values
        index (decide (index + 1 < values.length)) before returned after := by
  have stagedHigh : ∀ k, sp.toNat + 88 ≤ k → before.σ.mem[k]? = called.σ.mem[k]? := by
    intro k hk
    exact h.call.outside k (by unfold footprint; omega)
  have savedCalled : read64 called.σ.mem (sp.toNat + 1024) = some savedS6.toNat :=
    ((read64_agreeP (P := fun k => sp.toNat + 88 ≤ k)
      (fun k hk => stagedHigh k hk) (fun _ hk => by omega)).symm.trans savedRead)
  have calledSupport : EvalCallSupport called.σ.mem SL A sp :=
    support.transport_stack (fun k hk => (h.stackFrame k hk).symm)
  have indexRead : read64 called.σ.mem sp.toNat = some (8 * index) := by
    have saved := h.call.savedIndex
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 8 * index < 2^64 by
      have := data.bound; omega)] using saved
  obtain ⟨after, steps, resumed⟩ := ClosureParamResume.run_owned exit geometry stackLo stackHi
    arenaStack ((h.call.frame .x22 (by decide) (by decide) (by decide)).trans bound)
    indexRead savedCalled indexLt (by have := data.bound; omega) rfl calledSupport
  obtain ⟨alloc', exts', shared', result⟩ := resumed.result.selected
  have helperHigh : ∀ k, sp.toNat + 88 ≤ k → k < SL.hi →
      called.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hlo hhi
    rw [resumed.memory]
    symm
    apply exit.exit.mem_frame k
    · omega
    · omega
  have arguments : ∀ k, sp.toNat + 240 ≤ k → k < sp.toNat + 1008 →
      before.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hlo hhi
    exact (stagedHigh k (by omega)).trans (helperHigh k (by omega) (by omega))
  have agreement : AgreeP shared before.σ.mem after.σ.mem :=
    fun k hk => (h.agreement k hk).trans (result.agreement k hk)
  have supportAfter : EvalCallSupport after.σ.mem SL A sp := by
    rw [resumed.memory]
    exact calledSupport.transport (fun k hk => exit.exit.mem_frame k
      (calledSupport.outsideArena hk) (by have := calledSupport.outsideStack hk; omega))
  have frame : ∀ R, ClosureEnvNewResume.keep R = true →
      after.σ.regs.get? R = before.σ.regs.get? R := by
    intro R kept
    simp only [ClosureEnvNewResume.keep, Bool.and_eq_true] at kept
    have abi : AbiPreserved R = true := by
      exact kept.1.1.1
    have resumeKeep : ClosureParamResume.keep R = true := by
      simp only [ClosureParamResume.keep, abi, kept.2, Bool.and_self]
    have writes : ∀ n ∈ wrChain callClosureFoldStageSeg, (gprReg n == R) = false := by
      intro n hn
      have avoid : ∀ n ∈ wrChain callClosureFoldStageSeg,
          gprReg n = Register.x8 ∨ AbiPreserved (gprReg n) = false := by decide
      rcases avoid n hn with eq | scratch
      · rw [eq]
        apply beq_eq_false_iff_ne.mpr
        intro same
        subst R
        exact Bool.noConfusion kept.1.1.2
      · exact abiPreserved_ne abi scratch
    exact (resumed.frame R resumeKeep).trans ((exit.exit.frame R abi).trans
      (h.call.frame R (noise_ne_abi abi) writes (abiPreserved_ne abi (by decide))))
  refine ⟨after, alloc', exts', shared', steps,
    { result := { result with agreement := agreement }
      data := data.transport agreement result.includes arguments
      resume := resumed.toPost, cursor := ?_, scope := ?_, closure := ?_
      gp := resumed.gp, frame := frame
      output := resumed.output.trans (exit.exit.out.trans h.call.output)
      presence := by rw [resumed.memory]; exact h.presence.trans exit.exit.mem_extends
      memoryFrame := by
        intro k ha hs
        rw [resumed.memory]
        exact (h.stackFrame k hs).trans (exit.exit.mem_frame k ha (by omega)).symm
      support := supportAfter, savedRead := ?_, arguments := arguments
      highStack := fun k hlo hhi =>
        (stagedHigh k (by omega)).trans (helperHigh k (by omega) hhi)
      saved7Frame := fun k hlo hhi =>
        (stagedHigh k (by omega)).trans (helperHigh k (by omega) (by omega)) }⟩
  · exact (resumed.frame .x8 (by decide)).trans ((exit.exit.frame .x8 (by decide)).trans
      (show gprGet called.σ 8 = some (cursor + 24#64) from gholds_lookup _ h.call.regs (by rfl)))
  · exact (resumed.frame .x19 (by decide)).trans ((exit.exit.frame .x19 (by decide)).trans
      (show gprGet called.σ 19 = some scope from gholds_lookup _ h.call.regs (by rfl)))
  · exact (resumed.frame .x21 (by decide)).trans ((exit.exit.frame .x21 (by decide)).trans
      (show gprGet called.σ 21 = some closure from gholds_lookup _ h.call.regs (by rfl)))
  · exact (read64_agreeP (P := fun k => sp.toNat + 1024 ≤ k ∧ k < sp.toNat + 1032)
      (fun k hk => (stagedHigh k (by omega)).trans (helperHigh k (by omega) (by omega)))
      (fun _ hk => by omega)).symm.trans savedRead

end Vsa.Sim.ClosureParam
