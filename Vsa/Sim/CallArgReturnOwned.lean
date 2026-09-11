import Vsa.Sim.CallArgReturn
import Vsa.Sim.BinaryPrefixOwnership
import Vsa.Sim.AllocatorResult

namespace Vsa.Sim.CallArgReturn

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Move the returned argument into its slot while retaining the callee and prior arguments. -/
theorem Post.owned
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {entryF entryC resultF resultC : Addr → Nat} {nf nc reserve : Nat} {entryShared : Nat → Prop}
    {store : Store} {value : Value} {prior : List (Nat × Value)} {m0 : Mem}
    {node base sp env : BitVec 64} {index count : Nat} {more : Bool} {before after : Config}
    (h : Post sp env index count more before after)
    (G : CallArgStage.Geometry node base sp index count)
    (L : AllocLedger A SL gpv headroom maxReq M) (window : BinaryPrefix.Window SL sp)
    (priorOff : ∀ a v, (a, v) ∈ prior → a + 24 ≤ slot sp index ∨ slot sp index + 24 ≤ a)
    (repr : ReturnRepr N A entryF entryC resultF resultC nf nc store
      (prior ++ [((sp + 64#64).toNat, value)])
      (AllocatorResult M N entryShared reserve store (prior ++ [((sp + 64#64).toNat, value)]) m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) before.σ.mem) :
    ReturnRepr N A entryF entryC resultF resultC nf nc store (prior ++ [(slot sp index, value)])
      (AllocatorResult M N entryShared reserve store (prior ++ [(slot sp index, value)]) m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem := by
  obtain ⟨alloc, exts, shared, data⟩ := repr.owned.selected
  have buffer : (sp + 64#64).toNat = sp.toNat + 64 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := G.caller.stackHi; change sp.toNat + 64 < 2^64; omega)]
    rfl
  have stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    apply h.outside k
    unfold slot
    have := window.lo; have := window.hi; have := G.indexBound; have := G.countBound
    omega
  have agreement : AgreeP shared before.σ.mem after.σ.mem :=
    fun k hk => stackFrame k ((data.allocator.runtime L).shared_off_stack hk)
  have oldAgreement (a : Nat) (v : Value) (hv : (a, v) ∈ prior) :
      AgreeP (fun k => shared k ∨ valHeader a k) before.σ.mem after.σ.mem := by
    intro k hk
    rcases hk with hs | hh
    · exact agreement k hs
    · apply h.outside k
      have := priorOff a v hv
      change a ≤ k ∧ k < a + 24 at hh
      omega
  have sourceOwned := data.values _ _ (List.mem_append_right prior (List.mem_singleton_self _))
  have sourceRepr := repr.values _ _ (List.mem_append_right prior (List.mem_singleton_self _))
  rw [buffer] at sourceOwned sourceRepr
  have result : AllocatorResultAt M N entryShared reserve store (prior ++ [(slot sp index, value)]) m0
      resultF resultC alloc exts shared after.σ.mem :=
    { allocator := data.allocator.after_stack L stackFrame, includes := data.includes
      agreement := fun k hk => (data.agreement k hk).trans (agreement k (data.includes k hk))
      values := by
        intro a v hv
        rcases List.mem_append.mp hv with hp | hn
        · exact (data.values a v (List.mem_append_left _ hp)).transport (oldAgreement a v hp)
            (fun _ hk => Or.inr hk) (fun _ hk => Or.inl hk)
        · cases List.mem_singleton.mp hn
          exact sourceOwned.copy_total h.copied agreement }
  apply result.coherent L repr.frames repr.closures
  intro a v hv
  rcases List.mem_append.mp hv with hp | hn
  · have owned := data.values a v (List.mem_append_left _ hp)
    exact valueRepr_agreeP (oldAgreement a v hp) (fun _ hk => Or.inr hk)
      (owned.covered (fun _ hk => Or.inl hk)) (repr.values a v (List.mem_append_left _ hp))
  · cases List.mem_singleton.mp hn
    exact valueRepr_copy_total_exact h.copied (sourceOwned.covered agreement) sourceRepr

end Vsa.Sim.CallArgReturn
