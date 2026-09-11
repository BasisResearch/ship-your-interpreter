import Vsa.Sim.ClosureCallReturn
import Vsa.Sim.RuntimeOwnershipCopy

namespace Vsa.Sim.ClosureReturn

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Both mutable return windows belong to the caller's stack layout. -/
structure StackWindows (SL : StackLayout) (interp sret : BitVec 64) : Prop where
  interpLo : SL.lo ≤ interp.toNat + 8
  interpHi : interp.toNat + 12 ≤ SL.hi
  retLo : SL.lo ≤ sret.toNat
  retHi : sret.toNat + 24 ≤ SL.hi

/-- Return writes preserve the selected heap and move its owned result to the caller slot. -/
theorem Post.owned
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {entryF entryC resultF resultC nullC : Addr → Nat} {nf nc reserve : Nat}
    {entryShared : Nat → Prop} {store : Store} {value : Value} {m0 : Mem}
    {sp sret interp saved5 saved3 saved7 : BitVec 64} {depth : Nat} {returns : Bool} {before after : Config}
    (h : Post N nullC sp sret interp saved5 saved3 saved7 depth returns before after)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (windows : StackWindows SL interp sret)
    (repr : ReturnRepr N A entryF entryC resultF resultC nf nc store
      (statusResults (sp + 144#64).toNat (if returns then .ret value else .normal))
      (AllocatorResult M N entryShared reserve store
        (statusResults (sp + 144#64).toNat (if returns then .ret value else .normal)) m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) before.σ.mem)
    (buffer : (sp + 144#64).toNat = sp.toNat + 144) :
    ReturnRepr N A entryF entryC resultF resultC nf nc store
      [(sret.toNat, if returns then value else .null)]
      (AllocatorResult M N entryShared reserve store [(sret.toNat, if returns then value else .null)] m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem := by
  obtain ⟨alloc, exts, shared, data⟩ := repr.owned.selected
  have stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    apply h.outside k
    · have := windows.interpLo; have := windows.interpHi; omega
    · have := windows.retLo; have := windows.retHi; omega
  have agreement : AgreeP shared before.σ.mem after.σ.mem :=
    fun k hk => stackFrame k ((data.allocator.runtime L).shared_off_stack hk)
  have owned : ValueOwned after.σ.mem shared sret.toNat (if returns then value else .null) := by
    cases returns
    · trivial
    · have source := data.values (sp + 144#64).toNat value (by simp [statusResults])
      rw [buffer] at source
      exact source.copy_total (h.copied rfl) agreement
  have valueRepr : ValueRepr after.σ.mem N resultC sret.toNat (if returns then value else .null) := by
    cases returns
    · exact h.normalValue rfl
    · have source := repr.values (sp + 144#64).toNat value (by simp [statusResults])
      have sourceOwned := data.values (sp + 144#64).toNat value (by simp [statusResults])
      rw [buffer] at source sourceOwned
      exact valueRepr_copy_total_exact (h.copied rfl) (sourceOwned.covered agreement) source
  have result : AllocatorResultAt M N entryShared reserve store
      [(sret.toNat, if returns then value else .null)] m0 resultF resultC alloc exts shared after.σ.mem :=
    { allocator := data.allocator.after_stack L stackFrame, includes := data.includes
      agreement := fun k hk => (data.agreement k hk).trans (agreement k (data.includes k hk))
      values := by
        intro a v hv
        have same := List.mem_singleton.mp hv
        cases same
        exact owned }
  apply result.coherent L repr.frames repr.closures
  intro a v hv
  have same := List.mem_singleton.mp hv
  cases same
  exact valueRepr

end Vsa.Sim.ClosureReturn
