import Vsa.Sim.BinaryPrefixOwnership
import Vsa.Sim.AllocatorResultBind
import Vsa.Sim.EvalReturn

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine

namespace Vsa.Sim.BinaryPrefix
open RuntimeOwnership

/-- Compose the argument respill and actual right return at its selected maps.
The right child supplies the ordinary call frame; its owned result supplies
the stronger shared-payload agreement needed by the left operand. -/
theorem bind_operands
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {N : NativeAddrs}
    {entryF entryC middleF middleC : Addr → Nat} {nf nc : Nat}
    {entryShared middleShared : Nat → Prop} {firstCredits reserve : Nat}
    {middleStore : Store} {st : Vsa.While.St} {vl vr : Value}
    {alloc : Allocations} {exts : List Extent} {m0 : Mem}
    {before called after : Config} {node sp interp right env kind payload : BitVec 64}
    {br be bk bp : List (BitVec 8)}
    {FirstOwned : (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    {firstWrites : Nat → Prop}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (data : AllocatorResultAt M N entryShared firstCredits middleStore
      [((sp + 120#64).toNat, vl)] m0 middleF middleC alloc exts middleShared before.σ.mem)
    (first : ReturnRepr N A entryF entryC middleF middleC nf nc middleStore
      [((sp + 120#64).toNat, vl)] FirstOwned firstWrites before.σ.mem)
    (segment : SelectedFramedSegResult secondSeg (secondInput node sp interp)
      [br, be, bk, bp] 0x800034fc#64 (secondFoot sp) secondKeep
      [(12, right), (13, env), (16, kind), (10, sp + 144#64), (11, interp),
       (19, payload), (2, sp), (8, node), (18, interp)] before called)
    (returned : EvalReturnData N A SL middleF middleC
      middleStore.frames.size middleStore.closures.size st vr (sp + 144#64).toNat
      (AllocatorResult M N middleShared reserve st.store
        [((sp + 144#64).toNat, vr)] called.σ.mem) after)
    (steps : Steps called after)
    (frame : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (A.lo ≤ k ∧ k < A.hi) →
      ((sp + 144#64).toNat ≤ k ∧ k < (sp + 144#64).toNat + 24) ∨
        after.σ.mem[k]? = called.σ.mem[k]?)
    (w : Window SL sp) (hsp : sp.toNat + 1056 ≤ 0x100000000)
    (hsizeF : nf ≤ middleStore.frames.size) (hsizeC : nc ≤ middleStore.closures.size)
    (hbound : ValueClosuresBounded middleStore.closures.size vl) :
    ∃ resultF resultC,
      ReturnRepr N A entryF entryC resultF resultC nf nc st.store
        [((sp + 120#64).toNat, vl), ((sp + 144#64).toNat, vr)]
        (AllocatorResult M N entryShared reserve st.store
          [((sp + 120#64).toNat, vl), ((sp + 144#64).toNat, vr)] m0)
        (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem := by
  have carried := allocator_prefix L data.allocator segment (fun _ hk => w.second hk)
  obtain ⟨resultF, resultC, result⟩ := returned.selected
  have rebased := result.withOwnership
    (result.owned.rebase (fun _ h => h) carried.agreement)
  have addNat (off : Nat) (hoff : off ≤ 1056) :
      (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hleft := addNat 120 (by decide)
  have hright := addNat 144 (by decide)
  have headers : ∀ a v, (a, v) ∈ [((sp + 120#64).toNat, vl)] →
      ∀ k, valHeader a k → before.σ.mem[k]? = after.σ.mem[k]? := by
    intro a v member k hk
    have pair := List.mem_singleton.mp member
    have ha : a = (sp + 120#64).toNat := congrArg Prod.fst pair
    change a ≤ k ∧ k < a + 24 at hk
    rw [ha, hleft] at hk
    have samePrefix := segment.outside k (by unfold secondFoot; omega)
    have sameChild := frame k (by omega) (by
      have := w.lo
      have := w.hi
      rcases L.arena_stack with outside | outside <;> omega)
    rw [hright] at sameChild
    rcases sameChild with slot | same
    · omega
    · exact samePrefix.trans same.symm
  exact ⟨resultF, resultC, data.bind_return first rebased hsizeF hsizeC
    (by
      intro a v member
      have pair := List.mem_singleton.mp member
      have hv : v = vl := congrArg Prod.snd pair
      exact hv.symm ▸ hbound)
    (segment.steps.trans steps) headers⟩

#print axioms bind_operands

end Vsa.Sim.BinaryPrefix
