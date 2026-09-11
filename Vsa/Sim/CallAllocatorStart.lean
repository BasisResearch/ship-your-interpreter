import Vsa.Sim.CallCalleeEntry

namespace Vsa.Sim.CallCallee

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The original evaluator frame and owned callee result at the argument boundary. -/
structure Started (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop) (cost reserve : Nat)
    (st final : Vsa.While.St) (d env : Nat) (e : Expr) (args : List Expr) (value : Value)
    (sp ret dst node interp saved7 : BitVec 64) (m0 : Mem) (empty : Bool) (after : Config) : Prop where
  path : ∃ arm child v8 v9 v18,
    ReturnedWith
      (fun _ => ArmReady g N M phiF phiC alloc exts shared (cost + reserve) st d env e args
        sp ret dst node interp child v8 v9 v18 m0 arm)
      (CallArgsSetup.Started N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve final value node (sp - 1088#64) saved7 (BitVec.ofNat 64 (phiF env))
        args.length empty arm) after
  repr : EvalReturnData N A SL phiF phiC st.store.frames.size st.store.closures.size final value
    ((sp - 1088#64) + 96#64).toNat
    (AllocatorResult M N shared reserve final.store [(((sp - 1088#64) + 96#64).toNat, value)] m0) after

/-- Execute prologue, dispatch, callee evaluation, and both argument-count setup routes. -/
theorem start
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {cost request reserve : Nat}
    {st final : Vsa.While.St} {d env : Nat} {e : Expr} {args : List Expr} {value : Value}
    {sp ret dst node interp saved7 : BitVec 64} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (requestBound : request ≤ maxReq)
    (h : EvalAllocatorEntry g N M phiF phiC alloc exts shared (cost + reserve)
      st d env (.call e args) sp ret dst interp node m0 before)
    (saved7Reg : before.σ.regs.get? Register.x23 = some saved7) (countBound : args.length ≤ 32)
    (ih : EvalAllocatorAt N st d env e final value cost request) :
    ∃ after empty, Steps before after ∧ Started g N M phiF phiC alloc exts shared cost reserve
      st final d env e args value sp ret dst node interp saved7 m0 empty after := by
  obtain ⟨arm, child, v8, v9, v18, dispatchSteps, ready⟩ := dispatch L h
  have p := ArmEntryK.destruct g N A SL phiF phiC st 0x800031b0#64 (fun _ => True)
    (.call e args) sp ret dst node interp v8 v9 v18 arm.σ.sailOutput m0 arm.σ.mem arm ready.retained.arm
  have saved : arm.σ.regs.get? Register.x23 = some saved7 :=
    (p.frame .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((h.entry.frame .x23 (by decide)).symm.trans saved7Reg)
  obtain ⟨after, empty, argumentSteps, arguments⟩ := ready.input.start_arguments L requestBound
    ready.allocator ready.ast ready.gp p.node saved ready.window countBound ih
  obtain ⟨resultF, resultC, repr⟩ := arguments.selected
  have original : AgreeP shared m0 arm.σ.mem := by
    intro k hk
    have off := (h.allocator.runtime L).shared_off_stack hk
    exact (p.memFrame k (by have := h.entry.stackOK.2.1; omega)).symm
  exact ⟨after, empty, dispatchSteps.trans argumentSteps,
    { path := ⟨arm, child, v8, v9, v18, ready, arguments⟩
      repr := ⟨resultF, resultC, repr.withOwnership (repr.owned.rebase (fun _ hk => hk) original)⟩ }⟩

end Vsa.Sim.CallCallee
