import Vsa.Sim.ClosureReturnRun

namespace Vsa.Sim.ClosureCallPrefix

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The reached body status selects and executes the complete physical return route. -/
theorem BodyRunAt.run_return
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {shared : Nat → Prop} {reserve : Nat}
    {st final : Vsa.While.St} {env : Nat} {cd : ClosureData} {values : List Value} {status : Status}
    {sp call object fn interp parent saved5 saved3 saved7 p sret : BitVec 64} {depth : Nat}
    {before called head exited : Config}
    (h : BodyRunAt N M phiF phiC shared reserve st final env cd values status
      sp call object fn interp parent saved5 saved3 depth before called head p exited)
    (G : Geometry sp call object fn interp) (depthBound : depth < 1000)
    (stackHi : sp.toNat + 1056 ≤ SL.hi) (interpHi : interp.toNat + 12 ≤ SL.hi)
    (saved7Read : read64 before.σ.mem (sp.toNat + 1016) = some saved7.toNat)
    (sretReg : before.σ.regs.get? Register.x9 = some sret)
    (support : EvalCallSupport before.σ.mem SL A sp)
    (joinGeometry : ClosureReturnJoin.Geometry sp sret)
    (retOffSpills : sret.toNat + 24 ≤ sp.toNat + 1016 ∨ sp.toNat + 1056 ≤ sret.toNat)
    (nullRegion : NullRegion sret) :
    ∃ returns after, Steps before after ∧
      ClosureReturn.Post N phiC sp sret interp saved5 saved3 saved7 depth returns exited after ∧
      (if returns then ∃ v, status = .ret v else status = .normal) := by
  have reads := h.return_reads G depthBound stackHi interpHi saved7Read
  have reachedSupport : EvalCallSupport exited.σ.mem SL A sp :=
    support.transport (fun k hk => (h.memoryFrame k (support.outsideArena hk) (support.outsideStack hk)).symm)
  have geometry : ClosureReturnDepth.Geometry interp :=
    { lo := by have := G.stackLo; have := G.interpAbove; omega
      hi := G.interpHi
      htif := by have := G.stackHtif; have := G.interpAbove; omega
      align := G.interpAlign }
  have resultReg := h.s1.trans sretReg
  rcases h.exit.supported with normal | ⟨value, ret⟩
  · have input : ClosureReturn.Pre sp sret interp saved5 saved3 saved7 depth false exited :=
      { depthEntry :=
          { good := h.exit.good, tick := h.exit.tick
            pc := by simpa only [normal, execSeqExitPC, ClosureReturnDepth.entryPC, if_false] using h.exit.pc
            minstret := h.exit.minstret, regs := ⟨h.interpReg, resultReg, trivial⟩
            geometry := geometry, depthRead := reads.depthRead, bound := depthBound
            code := reachedSupport.image.text.Eval_exprLoaded }
        spReg := h.spReg, reads := reads, joinGeometry := joinGeometry, interpAbove := G.interpAbove
        retOffSpills := retOffSpills, nullRegion := nullRegion, nullCode := reachedSupport.image.text.Value_nullLoaded }
    obtain ⟨after, steps, result⟩ := ClosureReturn.run input N phiC
    exact ⟨false, after, h.run.trans steps, result, normal⟩
  · have statusReg : exited.σ.regs.get? Register.x10 = some 3#64 := by
      simpa only [ret, ExecSeqStatusABI, StatusCode] using h.exit.status_abi
    have input : ClosureReturn.Pre sp sret interp saved5 saved3 saved7 depth true exited :=
      { depthEntry :=
          { good := h.exit.good, tick := h.exit.tick
            pc := by simpa only [ret, execSeqExitPC, ClosureReturnDepth.entryPC, if_true] using h.exit.pc
            minstret := h.exit.minstret, regs := ⟨h.interpReg, resultReg, statusReg, trivial⟩
            geometry := geometry, depthRead := reads.depthRead, bound := depthBound
            code := reachedSupport.image.text.Eval_exprLoaded }
        spReg := h.spReg, reads := reads, joinGeometry := joinGeometry, interpAbove := G.interpAbove
        retOffSpills := retOffSpills, nullRegion := nullRegion, nullCode := reachedSupport.image.text.Value_nullLoaded }
    obtain ⟨after, steps, result⟩ := ClosureReturn.run input N phiC
    exact ⟨true, after, h.run.trans steps, result, value, ret⟩

end Vsa.Sim.ClosureCallPrefix
