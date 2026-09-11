import Vsa.Sim.ClosureCallEpilogue

namespace Vsa.Sim.ClosureCallPrefix

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Return the closure's selected value and allocator through the actual final epilogue. -/
theorem BodyRunAt.finish
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {shared : Nat → Prop} {reserve : Nat}
    {st final : Vsa.While.St} {env : Nat} {cd : ClosureData} {values : List Value}
    {status : Status} {value : Value}
    {sp call object fn interp parent saved5 saved3 saved7 p sret ret v8 v9 v18 : BitVec 64}
    {depth : Nat} {m0 : Mem} {before called head exited : Config}
    (h : BodyRunAt N M phiF phiC shared reserve st final env cd values status
      (sp - 1088#64) call object fn interp parent saved5 saved3 depth before called head p exited)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (G : Geometry (sp - 1088#64) call object fn interp)
    (caller : CallerFrame g A SL sp ret sret interp v8 v9 v18 saved5 saved3 saved7 depth m0 before)
    (windows : ClosureReturn.StackWindows SL interp sret) (region : NullRegion sret)
    (agreement : AgreeP shared m0 before.σ.mem)
    (meaning : status = .normal ∧ value = .null ∨ status = .ret value) :
    ∃ after, Steps before after ∧
      EvalAllocatorReturn g N M phiF phiC st.store.frames.size st.store.closures.size shared reserve
        final value sp ret sret m0 after := by
  have lowered : (sp - 1088#64).toNat = sp.toNat - 1088 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact caller.stackSize)
  have joinGeometry : ClosureReturnJoin.Geometry (sp - 1088#64) sret :=
    { stackLo := G.stackLo, stackHi := G.stackHi, stackHtif := G.stackHtif
      retLo := region.lo, retHi := region.hi, retHtif := region.win, retAlign := region.align }
  obtain ⟨returns, joined, returnSteps, post, route⟩ := h.run_return (saved7 := saved7) (sret := sret) G caller.depthBound
    (by rw [lowered]; have := caller.stackSize; have := caller.stackHi; omega)
    windows.interpHi (by rw [lowered, show sp.toNat - 1088 + 1016 = sp.toNat - 72 by
      have := caller.stackSize; omega]; exact caller.s7Read)
    caller.resultReg caller.support joinGeometry
    (by rw [lowered]; have := caller.stackSize; have := caller.retOutside; omega) region
  have statusEq : status = if returns then .ret value else .normal := by
    cases returns
    · exact route
    · rcases meaning with ⟨normal, _⟩ | ret
      · obtain ⟨v, hv⟩ := route
        rw [normal] at hv; cases hv
      · exact ret
  have valueEq : (if returns then value else .null) = value := by
    cases returns
    · rcases meaning with ⟨_, null⟩ | ret
      · exact null.symm
      · rw [route] at ret; cases ret
    · rfl
  obtain ⟨resultF, resultC, bodyRepr⟩ := h.selected
  have result := post.owned L windows (value := value)
    (by simpa only [statusEq] using bodyRepr) (G.stackAddr 144 (by decide))
  simp only [valueEq] at result
  have framesBound : st.store.frames.size ≤
      (closureBoundStore (st.store.allocFrame (some env)).1 cd values st.store.frames.size).frames.size := by
    unfold closureBoundStore
    rw [(foldDefine_size (cd.params.zip values) st.store.frames.size (st.store.allocFrame (some env)).1).1]
    simp [Store.allocFrame]
  have closuresBound : st.store.closures.size ≤
      (closureBoundStore (st.store.allocFrame (some env)).1 cd values st.store.frames.size).closures.size := by
    unfold closureBoundStore
    rw [(foldDefine_size (cd.params.zip values) st.store.frames.size (st.store.allocFrame (some env)).1).2]
    exact Nat.le_refl _
  have returned : ReturnRepr N A phiF phiC resultF resultC st.store.frames.size st.store.closures.size
      final.store [(sret.toNat, value)]
      (AllocatorResult M N shared reserve final.store [(sret.toNat, value)] m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) joined.σ.mem :=
    { result with
      frames := (pushFrameMap_extends phiF st.store.frames.size p.toNat).trans
        (PhiExtends.mono framesBound result.frames)
      closures := PhiExtends.mono closuresBound result.closures
      owned := result.owned.rebase (fun _ hv => hv) agreement }
  have epi := h.epilogue post caller windows returned
  obtain ⟨after, epilogueSteps, finished⟩ := blockD_v_return g N A SL phiF phiC resultF resultC
    st.store.frames.size st.store.closures.size final value sp ret sret v8 v9 v18
    joined.σ.sailOutput m0 (AllocatorResult M N shared reserve final.store [(sret.toNat, value)] m0)
    returned.frames returned.closures joined epi
  have ghostGp : g Register.x3 = some gpv :=
    (caller.frame .x3 (by decide) (by decide) (by decide) (by decide)).symm.trans
      ((h.frame .x3 (by decide)).symm.trans h.gp)
  exact ⟨after, returnSteps.trans epilogueSteps,
    { returned := finished, gp := (finished.exit.1.frame .x3 (by decide)).trans ghostGp }⟩

end Vsa.Sim.ClosureCallPrefix
