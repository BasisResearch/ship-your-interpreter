import Vsa.Sim.AllocatorResult
import Vsa.Sim.CoherentReturnFrame
import Vsa.Sim.RuntimeOwnershipShared

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine

namespace Vsa.Sim
open RuntimeOwnership

/-- Compose actual child returns, retaining both operands at the second child's maps.
The caller supplies the preserved left slots and the semantic bound on left closures.
The second child's allocator result supplies shared-payload preservation. -/
theorem AllocatorResultAt.bind_return
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {N : NativeAddrs}
    {entryF entryC middleF middleC resultF resultC : Addr → Nat} {nf nc : Nat}
    {entryShared middleShared : Nat → Prop} {firstCredits reserve : Nat}
    {middleStore store : Store} {left right : List (Nat × Value)}
    {alloc : Allocations} {exts : List Extent} {m0 : Mem} {before after : Config}
    {FirstOwned : (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    {firstWrites : Nat → Prop}
    (data : AllocatorResultAt M N entryShared firstCredits middleStore left m0
      middleF middleC alloc exts middleShared before.σ.mem)
    (first : ReturnRepr N A entryF entryC middleF middleC nf nc
      middleStore left FirstOwned firstWrites before.σ.mem)
    (second : ReturnRepr N A middleF middleC resultF resultC
      middleStore.frames.size middleStore.closures.size store right
      (AllocatorResult M N middleShared reserve store right before.σ.mem)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem)
    (hsizeF : nf ≤ middleStore.frames.size) (hsizeC : nc ≤ middleStore.closures.size)
    (hbound : ∀ a v, (a, v) ∈ left → ValueClosuresBounded middleStore.closures.size v)
    (steps : Steps before after)
    (headers : ∀ a v, (a, v) ∈ left → ∀ k, valHeader a k →
      before.σ.mem[k]? = after.σ.mem[k]?) :
    ReturnRepr N A entryF entryC resultF resultC nf nc store (left ++ right)
      (AllocatorResult M N entryShared reserve store (left ++ right) m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem := by
  obtain ⟨resultAlloc, resultExts, resultShared, returned⟩ := second.owned.selected
  let preserved : Nat → Prop := fun k =>
    middleShared k ∨ ∃ a v, (a, v) ∈ left ∧ valHeader a k
  have agreement : AgreeP preserved before.σ.mem after.σ.mem := by
    intro k hk
    rcases hk with shared | ⟨a, v, member, header⟩
    · exact returned.agreement k shared
    · exact headers a v member k header
  have framed : FramedSteps
      { regs := fun _ => False, mem := preserved, output := False } before after :=
    { steps := steps
      frame :=
        { regs := ⟨fun _ h => False.elim h⟩
          mem := fun k hk => (agreement k hk).symm
          output := fun h => False.elim h } }
  have hheaders : ∀ a v, (a, v) ∈ left → ∀ k, valHeader a k → preserved k :=
    fun a v ha k hk => Or.inr ⟨a, v, ha, hk⟩
  have composed := first.bind second hsizeF hsizeC hbound framed hheaders
    (fun a v ha => (data.values a v ha).covered (fun _ hk => Or.inl hk))
  apply composed.withOwnership
  exact ⟨resultAlloc, resultExts, resultShared,
    { allocator := returned.allocator
      includes := fun k hk => returned.includes k (data.includes k hk)
      values := fun a v hav => by
        rcases List.mem_append.mp hav with hl | hr
        · exact ((data.values a v hl).transport agreement (hheaders a v hl)
            (fun _ hk => Or.inl hk)).mono returned.includes
        · exact returned.values a v hr
      agreement := fun k hk => (data.agreement k hk).trans
        (returned.agreement k (data.includes k hk)) }⟩

#print axioms AllocatorResultAt.bind_return

end Vsa.Sim
