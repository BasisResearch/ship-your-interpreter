import Vsa.Sim.ClosureCallBind
import Vsa.Sim.ClosureScopeBody
import Vsa.Sim.ClosureBodyRun

namespace Vsa.Sim.ClosureCallPrefix

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership ClosureParam

def bodyKeep (R : Register) : Bool :=
  AbiPreserved R && !(R == .x8) && !(R == .x19) && !(R == .x21) && !(R == .x23)

/-- One selected allocator and the body input reached by the same call execution. -/
structure BodyReadyAt (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (entryShared : Nat → Prop) (credits : Nat)
    (st : Vsa.While.St) (d env : Nat) (ss : List Stmt)
    (sp fn body base interp : BitVec 64) (before after : Config)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop) : Prop where
  input : ClosureBodyInput N A SL phiF shared st d env ss sp fn body base interp after
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits st.store after.σ.mem
  gp : after.σ.regs.get? Register.x3 = some gpv
  s1 : after.σ.regs.get? Register.x9 = before.σ.regs.get? Register.x9
  s4 : after.σ.regs.get? Register.x20 = before.σ.regs.get? Register.x20
  frame : ∀ R, bodyKeep R = true → after.σ.regs.get? R = before.σ.regs.get? R
  includes : ∀ k, entryShared k → shared k
  agreement : AgreeP entryShared before.σ.mem after.σ.mem
  presence : MemExtends before.σ.mem after.σ.mem
  memoryFrame : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < SL.hi) →
    before.σ.mem[k]? = after.σ.mem[k]?

/-- Dispatch and all bindings reach the body while retaining the saved caller stack. -/
structure BodyCallAt (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (shared : Nat → Prop) (credits : Nat)
    (st : Vsa.While.St) (env d : Nat) (cd : ClosureData) (values : List Value)
    (sp call object fn interp parent saved5 saved3 body base : BitVec 64) (depth : Nat)
    (before called : Config) (p : BitVec 64) (after : Config) : Prop where
  dispatch : Post sp call object fn interp parent saved5 saved3 values.length depth before called
  selected : ∃ alloc exts shared', BodyReadyAt N M
    (pushFrameMap phiF st.store.frames.size p.toNat) phiC shared credits
    ⟨closureBoundStore (st.store.allocFrame (some env)).1 cd values st.store.frames.size,
      Vsa.Machine.output before.σ⟩ d st.store.frames.size cd.body
    sp fn body base interp before after alloc exts shared'
  highStack : ∀ k, sp.toNat + 1032 ≤ k → k < SL.hi → called.σ.mem[k]? = after.σ.mem[k]?
  saved7Frame : ∀ k, sp.toNat + 1016 ≤ k → k < sp.toNat + 1024 →
    before.σ.mem[k]? = after.σ.mem[k]?
  run : Steps before after

/-- Execute dispatch, fresh scope allocation, and either complete parameter-count branch. -/
theorem Pre.prepare_body
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {env d : Addr}
    {sp call object fn interp parent a3 saved5 saved3 savedS6 names body base : BitVec 64}
    {cd : ClosureData} {values : List Value} {depth : Nat} {before : Config}
    (pre : Pre sp call object fn interp parent a3 saved5 saved3 values.length depth before)
    (L : AllocLedger A SL gpv headroom maxReq M) (placement : BindingArena A SL)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared
      (3 * values.length + credits + 1) st.store before.σ.mem)
    (R : ScopeResources A SL phiF st env sp interp parent gpv savedS6 before)
    (data : FoldData before.σ.mem N phiC shared sp fn names cd.params values)
    (bodyData : FoldBodyData N A SL shared st.store d cd.body sp fn body base interp before)
    (stack : StackOK SL sp (176 + 1088))
    (unique : StoreUnique st.store)
    (bounded : ∀ i (hi : i < values.length), ValueClosuresBounded st.store.closures.size values[i])
    (nameRequest : ∀ param ∈ cd.params, param.length + 1 ≤ maxReq)
    (growRequest : 48 * values.length ≤ maxReq)
    (present : EnvDefineSavedPresent before.σ.regs.get?) :
    ∃ called p after, BodyCallAt N M phiF phiC shared credits st env d cd values
      sp call object fn interp parent saved5 saved3 body base depth before called p after := by
  obtain ⟨called, p, scope, allocated⟩ := pre.allocate L allocator R
  have stackLo : SL.lo ≤ sp.toNat := by have := R.stack.1; omega
  have stackHi : sp.toNat + 1032 ≤ SL.hi := by have := R.stackHi; omega
  have closureReg : called.σ.regs.get? Register.x21 = some fn :=
    gholds_lookup _ allocated.dispatch.regs (show lookupG 21 _ = some fn from rfl)
  have scopeData := allocated.scopePost.body_data
    (allocated.ready.body_data allocated.dispatch bodyData) stackLo stackHi closureReg
  have scopeHigh := allocated.scopePost.high_stack L stackLo
  have scopeAgreement : AgreeP shared before.σ.mem scope.σ.mem :=
    fun k hk => (allocated.ready.agreement k hk).trans (allocated.scopePost.agreement k hk)
  have scopeMemory : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < SL.hi) →
      before.σ.mem[k]? = scope.σ.mem[k]? := by
    intro k ha hs
    exact (allocated.ready.stackFrame k hs).trans
      (allocated.scopePost.memoryFrame k ha (by omega) (by omega)).symm
  have scopePresence := allocated.ready.presence.trans allocated.scopePost.presence
  have keptAbi : ∀ R, bodyKeep R = true → AbiPreserved R = true := by
    intro reg; cases reg <;> decide
  have keptScope : ∀ R, bodyKeep R = true → R ≠ Register.x22 → ClosureEnvNewResume.keep R = true := by
    intro reg; cases reg <;> decide
  have keptDispatch : ∀ R, bodyKeep R = true →
      ∀ n ∈ wrChain callClosureDispatchStageSeg, (gprReg n == R) = false := by
    intro reg; cases reg <;> decide
  have scopeFrame : ∀ R, bodyKeep R = true → R ≠ Register.x22 →
      scope.σ.regs.get? R = before.σ.regs.get? R := by
    intro reg kept non22
    exact (allocated.scopePost.frame reg (keptScope reg kept non22)).trans
      (allocated.dispatch.frame reg (noise_ne_abi (keptAbi reg kept)) (keptDispatch reg kept)
        (abiPreserved_ne (keptAbi reg kept) (by decide)))
  have scopeSaved7 : ∀ k, sp.toNat + 1016 ≤ k → k < sp.toNat + 1024 →
      before.σ.mem[k]? = scope.σ.mem[k]? := by
    intro k hlo hhi
    have dispatchFrame := allocated.dispatch.outside k (by
      unfold footprint; have := pre.geometry.interpAbove; omega)
    exact dispatchFrame.trans (allocated.scopePost.memoryFrame k
      (by have := L.arena_stack; omega) (by omega) (by omega)).symm
  by_cases zero : values = []
  · subst values
    have h := allocated.scopePost
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.lt_irrefl, decide_false] at h
    refine ⟨called, p, scope,
      { dispatch := allocated.dispatch, highStack := scopeHigh, saved7Frame := scopeSaved7
        run := allocated.run
        selected := ⟨alloc.insert (.frame st.store.frames.size) p.toNat 32,
          (p.toNat, 32) :: exts, shared, ?_⟩ }⟩
    refine
      { input := ?_, allocator := ?_, gp := h.gp
        s1 := (h.frame .x9 (by decide)).trans (allocated.dispatch.frame .x9 (by decide) (by decide) (by decide))
        s4 := (h.frame .x20 (by decide)).trans (allocated.dispatch.frame .x20 (by decide) (by decide) (by decide))
        frame := ?_
        includes := fun _ hk => hk
        agreement := scopeAgreement, presence := scopePresence, memoryFrame := scopeMemory }
    · simpa only [closureBoundStore, List.zip_nil_right, List.foldl_nil] using
        h.empty_body_input scopeData closureReg stack R.stackRam R.stackWin (by omega)
    · simpa only [closureBoundStore, List.zip_nil_right, List.foldl_nil] using h.allocator
    · intro reg kept
      by_cases is22 : reg = Register.x22
      · subst reg
        exact (show scope.σ.regs.get? Register.x22 = some savedS6 from
          gholds_lookup _ h.regs (show lookupG 22 _ = some savedS6 from rfl)).trans R.s6.symm
      · exact scopeFrame reg kept is22
  · have positive : 0 < values.length := List.length_pos_iff.mpr zero
    have scopePost := allocated.scopePost
    rw [show decide (0 < values.length) = true by simp [positive]] at scopePost
    have calledData := data.transport allocated.ready.agreement (fun _ hk => hk) allocated.ready.arguments
    obtain ⟨after, steps, result⟩ := scopePost.bind_params calledData L placement
      R.stack R.stackRam R.stackWin stackHi positive unique bounded nameRequest growRequest
      closureReg (allocated.dispatch.saved_present present)
    obtain ⟨alloc', exts', shared', bound⟩ := result.selected
    have context : FoldContext SL maxReq (pushFrameMap phiF st.store.frames.size p.toNat)
        (st.store.allocFrame (some env)).1 cd values st.store.frames.size sp p :=
      { arity := data.arity, bound := data.bound
        valid := by simp [Store.allocFrame], empty := by simp [Store.allocFrame]
        unique := unique.allocFrame st.store (some env)
        scopeAddr := (pushFrameMap_fresh phiF st.store.frames.size p.toNat).symm
        stack := R.stack, stackRam := R.stackRam, stackWin := R.stackWin, stackHi := stackHi
        names := nameRequest, growth := growRequest
        bounded := by simpa only [Store.allocFrame] using bounded }
    have full : foldStore (st.store.allocFrame (some env)).1 cd values st.store.frames.size values.length =
        closureBoundStore (st.store.allocFrame (some env)).1 cd values st.store.frames.size := by
      have length : (cd.params.zip values).length = values.length := by
        simp only [List.length_zip, ← data.arity, Nat.min_self]
      simpa only [length] using foldStore_full (st.store.allocFrame (some env)).1 cd values st.store.frames.size
    have output : Vsa.Machine.output scope.σ = Vsa.Machine.output before.σ := by
      simp only [Vsa.Machine.output, scopePost.output]
    refine ⟨called, p, after,
      { dispatch := allocated.dispatch, run := allocated.run.trans steps
        highStack := fun k hlo hhi => (scopeHigh k hlo hhi).trans (bound.highStack k hlo hhi)
        saved7Frame := fun k hlo hhi => (scopeSaved7 k hlo hhi).trans (bound.saved7Frame k hlo hhi)
        selected := ⟨alloc', exts', shared', ?_⟩ }⟩
    exact
      { input := by simpa only [full, output] using bound.body_input context scopeData stack
        allocator := by simpa only [Nat.sub_self, Nat.mul_zero, Nat.zero_add, full] using bound.allocator
        gp := bound.gp
        s1 := (bound.frame .x9 (by decide)).trans ((scopePost.frame .x9 (by decide)).trans
          (allocated.dispatch.frame .x9 (by decide) (by decide) (by decide)))
        s4 := (bound.frame .x20 (by decide)).trans ((scopePost.frame .x20 (by decide)).trans
          (allocated.dispatch.frame .x20 (by decide) (by decide) (by decide)))
        frame := by
          intro reg kept
          by_cases is22 : reg = Register.x22
          · subst reg
            have s6 : after.σ.regs.get? Register.x22 = some savedS6 := by
              simpa only [Nat.lt_irrefl, if_false] using bound.s6
            exact s6.trans R.s6.symm
          · exact (bound.frame reg (keptScope reg kept is22)).trans (scopeFrame reg kept is22)
        includes := bound.includes
        agreement := fun k hk => (scopeAgreement k hk).trans (bound.agreement k hk)
        presence := scopePresence.trans bound.presence
        memoryFrame := fun k ha hs => (scopeMemory k ha hs).trans (bound.memoryFrame k ha hs) }

end Vsa.Sim.ClosureCallPrefix
