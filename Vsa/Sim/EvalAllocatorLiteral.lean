import Vsa.Sim.AllocatorIH
import Vsa.Sim.EvalLeafD
import Vsa.Sim.IHClauseGeneric

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- A literal's actual writes lie inside the whole caller stack. -/
theorem LeafMemPin.agree_off_stack
    {SL : StackLayout} {sp dst : BitVec 64} {m0 m : Mem}
    (pin : LeafMemPin SL sp dst m0 m) (high : sp.toNat ≤ SL.hi)
    (slot : SL.lo ≤ dst.toNat ∧ dst.toNat + 24 ≤ SL.hi) :
    ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m0[k]? = m[k]? := by
  intro k hk
  exact (pin.agree k (by omega) (by omega)).symm

/-- Retain allocator ownership at a pinned literal's actual return and entry maps. -/
theorem EvalExitPinned.allocatorReturn
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {credits : Nat}
    {st : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    {sp ret dst interp node : BitVec 64} {m0 : Mem} {before after : Config}
    (exit : EvalExitPinned g N A SL phiF phiC st v sp ret dst m0 after)
    (entry : EvalAllocatorEntry g N M phiF phiC alloc exts shared credits
      st d env e sp ret dst interp node m0 before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (bounded : ValueClosuresBounded 0 v)
    (owned : ValueOwned after.σ.mem shared dst.toNat v) :
    EvalAllocatorReturn g N M phiF phiC st.store.frames.size st.store.closures.size
      shared credits st v sp ret dst m0 after := by
  obtain ⟨ordinary, pin⟩ := exit
  have frame := pin.agree_off_stack entry.entry.stackOK.2.1 entry.entry.ground.sret_inSL
  have agreement : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
      before.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    rw [entry.entry.mem]
    exact frame k hk
  have data : AllocatorResultAt M N shared credits st.store [(dst.toNat, v)] m0
      phiF phiC alloc exts shared after.σ.mem :=
    { allocator := entry.allocator.after_stack L agreement
      includes := fun _ hk => hk
      values := fun a w hw => by
        have eq := List.mem_singleton.mp hw
        cases eq
        exact owned
      agreement := fun k hk => frame k ((entry.allocator.runtime L).shared_off_stack hk) }
  obtain ⟨valueC, _, value⟩ := ordinary.result
  have value' : ValueRepr after.σ.mem N phiC dst.toNat v :=
    valueRepr_phic_mono bounded (by intro k hk; omega) value
  have coherent := data.coherent L (PhiExtends.refl phiF st.store.frames.size)
    (PhiExtends.refl phiC st.store.closures.size) (by
    intro a w hw
    have eq := List.mem_singleton.mp hw
    cases eq
    exact value')
  have widened := evalExitD_of_pinnedExit ⟨ordinary, pin⟩ (leafWidenP_of_entry entry.entry)
    (entry.entry.mem ▸ entry.entry.sret_words)
  exact
    { returned := widened.withReturnRepr coherent
      gp := (ordinary.frame .x3 (by decide)).trans
        ((entry.entry.frame .x3 (by decide)).symm.trans entry.gp) }

/-- Integer literals preserve all allocation credit. -/
theorem evalAllocatorIH_int (st : Vsa.While.St) (d env : Nat) (n : Int) :
    EvalAllocatorIH st d env (.int n) st (.int n) 0 0 where
  run := by
    intro g N A SL gpv headroom maxReq M L _request phiF phiC alloc exts shared reserve
      sp ret dst interp node m0 before entry
    obtain ⟨after, steps, result⟩ :=
      evalIntSimP g N A SL phiF phiC st d env n sp ret dst interp node m0 before entry.entry
    exact ⟨after, steps, by
      simpa only [Nat.zero_add] using
        EvalExitPinned.allocatorReturn result entry L (by trivial) (by trivial)⟩

/-- Null literals preserve all allocation credit. -/
theorem evalAllocatorIH_null (st : Vsa.While.St) (d env : Nat) :
    EvalAllocatorIH st d env .null st .null 0 0 where
  run := by
    intro g N A SL gpv headroom maxReq M L _request phiF phiC alloc exts shared reserve
      sp ret dst interp node m0 before entry
    obtain ⟨after, steps, result⟩ :=
      evalNullSimP g N A SL phiF phiC st d env sp ret dst interp node m0 before
        (evalNullEntry_of_entry entry.entry)
    exact ⟨after, steps, by
      simpa only [Nat.zero_add] using
        EvalExitPinned.allocatorReturn result entry L (by trivial) (by trivial)⟩

/-- Boolean literals preserve all allocation credit. -/
theorem evalAllocatorIH_bool (st : Vsa.While.St) (d env : Nat) (b : Bool) :
    EvalAllocatorIH st d env (.bool b) st (.bool b) 0 0 where
  run := by
    intro g N A SL gpv headroom maxReq M L _request phiF phiC alloc exts shared reserve
      sp ret dst interp node m0 before entry
    obtain ⟨after, steps, result⟩ :=
      evalBoolSimP g N A SL phiF phiC st d env b sp ret dst interp node m0 before
        (evalBoolEntry_of_entry entry.entry)
    exact ⟨after, steps, by
      simpa only [Nat.zero_add] using
        EvalExitPinned.allocatorReturn result entry L (by trivial) (by trivial)⟩

/-- String literals retain the shared AST payload at their actual returned pointer. -/
theorem evalAllocatorIH_str (st : Vsa.While.St) (d env : Nat) (s : String) :
    EvalAllocatorIH st d env (.str s) st (.str s) 0 0 where
  run := by
    intro g N A SL gpv headroom maxReq M L _request phiF phiC alloc exts shared reserve
      sp ret dst interp node m0 before entry
    obtain ⟨after, steps, ordinary, pin⟩ :=
      evalStrSimP_exact g N A SL phiF phiC st d env s sp ret dst interp node m0 before
        (evalStrEntry_of_entry entry.entry)
    obtain ⟨valueC, _, value⟩ := ordinary.result
    obtain ⟨_kind, p, pointer, _nonzero, string⟩ := value
    have sourcePointer : read64 before.σ.mem (node.toNat + 8) = some p := by
      rw [entry.entry.mem]
      exact pin.pointer.symm.trans pointer
    have bytes : ∀ k, k ≤ s.length → shared (p + k) := by
      cases entry.ast with
      | str _ _ read _ payload =>
        have eq := Option.some.inj (read.symm.trans sourcePointer)
        obtain ⟨_, covered⟩ := payload
        simpa only [eq] using covered
    have owned : ValueOwned after.σ.mem shared dst.toNat (.str s) :=
      ⟨p, pointer, string, bytes⟩
    have result : EvalExitPinned g N A SL phiF phiC st (.str s) sp ret dst m0 after :=
      ⟨ordinary, pin.memory⟩
    exact ⟨after, steps, by
      simpa only [Nat.zero_add] using
        EvalExitPinned.allocatorReturn result entry L (by trivial) owned⟩

#print axioms LeafMemPin.agree_off_stack
#print axioms EvalExitPinned.allocatorReturn
#print axioms evalAllocatorIH_int
#print axioms evalAllocatorIH_null
#print axioms evalAllocatorIH_bool
#print axioms evalAllocatorIH_str

end Vsa.Sim
