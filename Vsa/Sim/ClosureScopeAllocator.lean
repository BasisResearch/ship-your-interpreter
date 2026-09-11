import Vsa.Sim.EnvNewAllocator
import Vsa.Sim.ClosureEnvNewResume
import Vsa.Sim.Code.FixedImage_Eval_expr
import Vsa.Sim.InterpEntry

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The allocated closure scope at parameter binding or body initialization. -/
structure ClosureScopePost
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (st : Vsa.While.St) (env : Addr)
    (sp p savedS6 : BitVec 64) (count : Nat) (hasParams : Bool)
    (m : Mem) (out : Array String) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (ClosureEnvNewResume.exitPC hasParams)
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  regs : GHolds after.σ (ClosureEnvNewResume.selected sp p savedS6 count hasParams)
  fresh : EnvNewFresh N A SL phiF phiC st env p
    (pushFrameMap phiF st.store.frames.size p.toNat) after.σ.mem
  allocator : RuntimeAllocatorState M N (pushFrameMap phiF st.store.frames.size p.toNat) phiC
    (alloc.insert (.frame st.store.frames.size) p.toNat 32) ((p.toNat, 32) :: exts)
    shared credits (st.store.allocFrame (some env)).1 after.σ.mem
  agreement : AgreeP shared m after.σ.mem
  support : EvalCallSupport after.σ.mem SL A sp
  gp : after.σ.regs.get? Register.x3 = some gpv
  output : after.σ.sailOutput = out
  countRead : read64 after.σ.mem sp.toNat = some count
  capacity : read32 after.σ.mem (p.toNat + 4) = some 0
  savedS6 : hasParams = true → read64 after.σ.mem (sp.toNat + 1024) = some savedS6.toNat
  memoryFrame : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) →
    ¬ (SL.lo ≤ k ∧ k < sp.toNat) →
    ¬ (sp.toNat + 1024 ≤ k ∧ k < sp.toNat + 1032) → after.σ.mem[k]? = m[k]?
  presence : MemExtends m after.σ.mem
  frame : ∀ R, ClosureEnvNewResume.keep R = true → after.σ.regs.get? R = g R

/-- Allocate the scope once, reload argc, and execute the selected return route. -/
theorem closureScopeAllocator_run
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {env : Addr}
    {sp aEnv savedS6 : BitVec 64} {count : Nat} {hasParams : Bool}
    {m : Mem} {out : Array String} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (entry : EnvNewEntryState g N A SL phiF phiC st env sp aEnv 0x800032c0#64 m out before)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (credits + 1) st.store m)
    (support : EvalCallSupport m SL A sp)
    (gp : before.σ.regs.get? Register.x3 = some gpv)
    (spill : ∃ v, before.σ.regs.get? Register.x8 = some v)
    (s6 : before.σ.regs.get? Register.x22 = some savedS6)
    (stackHi : sp.toNat + 1032 ≤ SL.hi)
    (countRead : read64 m sp.toNat = some count)
    (countBound : count < 2^31) (branch : decide (0 < count) = hasParams) :
    ∃ after p, Steps before after ∧
      ClosureScopePost g N M phiF phiC alloc exts shared credits st env
        sp p savedS6 count hasParams m out after := by
  obtain ⟨returned, p, allocSteps, H⟩ := envNewAllocator_run L entry allocator gp spill
  have stackLo := entry.facts.stack.1
  have stackAlign := entry.facts.stack.2.2
  have stackRam := entry.facts.stack_ram
  have stackWin := entry.facts.stack_win
  have geometry : ClosureEnvNewResume.Geometry sp :=
    { lo := by omega, hi := by omega, htif := by omega, align := by omega }
  have countAgreement : AgreeP (fun k => sp.toNat ≤ k ∧ k < sp.toNat + 8)
      returned.σ.mem m := by
    intro k hk
    apply H.exit.mem_frame k
    · have := L.arena_stack; omega
    · omega
  have returnedCount : read64 returned.σ.mem sp.toNat = some count :=
    (read64_agreeP countAgreement (fun _ hk => by omega)).trans countRead
  have returnedSupport : EvalCallSupport returned.σ.mem SL A sp :=
    support.transport (fun k hk => H.exit.mem_frame k (support.outsideArena hk) (by
      have := support.outsideStack hk
      omega))
  have pre : ClosureEnvNewResume.Pre sp p savedS6 count hasParams returned :=
    { good := H.exit.good, tick := H.exit.tick, pc := H.exit.pc
      minstret := H.exit.minstret
      regs := ⟨H.exit.sp, H.result,
        (H.exit.frame .x22 (by decide)).trans
          ((entry.frame .x22 (by decide)).symm.trans s6), trivial⟩
      geometry := geometry, countRead := returnedCount, countBound := countBound
      branch := branch
      code := returnedSupport.image.text.Eval_exprLoaded }
  obtain ⟨after, resumeSteps, R⟩ := ClosureEnvNewResume.run pre
  have outside : ∀ k, ¬ (sp.toNat + 1024 ≤ k ∧ k < sp.toNat + 1032) →
      returned.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    rw [R.memory]
    symm
    apply writeLog_out
    cases hasParams
    · trivial
    · change (k < sp.toNat + 1024 ∨ sp.toNat + 1024 + 8 ≤ k) ∧ True
      exact ⟨by omega, trivial⟩
  have stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
      returned.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    apply outside k
    omega
  have allocatorAfter := H.allocator.after_stack L stackFrame
  have agreement : AgreeP shared returned.σ.mem after.σ.mem :=
    fun k hk => stackFrame k ((H.allocator.runtime L).shared_off_stack hk)
  refine ⟨after, p, allocSteps.trans resumeSteps,
    { good := R.good, tick := R.tick, pc := R.pc, minstret := R.minstret
      regs := R.regs
      fresh := { H.fresh with
        store := allocatorAfter.repr
        survives := fun _ hm => ((allocatorAfter.runtime L).after_stack hm).repr }
      allocator := allocatorAfter, agreement := fun k hk => (H.agreement k hk).trans (agreement k hk)
      support := returnedSupport.transport_stack (fun k hk => (stackFrame k hk).symm)
      gp := (R.frame .x3 (by decide)).trans H.gp
      output := R.output.trans H.exit.out
      countRead := ?_, capacity := ?_, savedS6 := ?_
      memoryFrame := fun k ha hs hf => (outside k hf).symm.trans (H.exit.mem_frame k ha hs)
      presence := H.exit.mem_extends.trans (by rw [R.memory]; exact memExtends_writeLog _ _)
      frame := fun reg kept => (R.frame reg kept).trans (H.exit.frame reg (by
        simp only [ClosureEnvNewResume.keep, Bool.and_eq_true] at kept
        exact kept.1.1.1)) }⟩
  · have agree : AgreeP (fun k => sp.toNat ≤ k ∧ k < sp.toNat + 8)
        returned.σ.mem after.σ.mem := fun k hk => outside k (by omega)
    exact (read64_agreeP agree (fun _ hk => by omega)).symm.trans returnedCount
  · have arena := H.fresh.arena
    have agreement : AgreeP (fun k => A.lo ≤ k ∧ k < A.hi) returned.σ.mem after.σ.mem := by
      intro k hk
      exact stackFrame k (by have := L.arena_stack; omega)
    have read := read32_agreeP agreement (a := p.toNat + 4) (by
      intro k hk
      rcases arena with ⟨lo, hi⟩
      omega)
    exact read.symm.trans H.capacity
  · intro nonempty
    rw [R.memory, nonempty]
    exact read64_of_writeLog_at returned.σ.mem [(sp.toNat + 1024, 8, savedS6)] 0 _ _ rfl
      (by simp [OutLRange])

#print axioms closureScopeAllocator_run

end Vsa.Sim
