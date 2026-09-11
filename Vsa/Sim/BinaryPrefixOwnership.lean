import Vsa.Sim.BinaryPrefixRun
import Vsa.Sim.RuntimeAllocatorState
import Vsa.Sim.InterpEntry

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine

namespace Vsa.Sim.BinaryPrefix
open RuntimeOwnership

/-- Both argument prefixes write within the caller's reserved stack. -/
structure Window (SL : StackLayout) (sp : BitVec 64) : Prop where
  lo : SL.lo ≤ sp.toNat
  hi : sp.toNat + 1056 ≤ SL.hi

theorem Window.first {SL : StackLayout} {sp : BitVec 64} (w : Window SL sp)
    {k : Nat} (hk : firstFoot sp k) : SL.lo ≤ k ∧ k < SL.hi := by
  have := w.lo
  have := w.hi
  unfold firstFoot at hk
  omega

theorem Window.second {SL : StackLayout} {sp : BitVec 64} (w : Window SL sp)
    {k : Nat} (hk : secondFoot sp k) : SL.lo ≤ k ∧ k < SL.hi := by
  exact w.first (Or.inr hk)

/-- The reached allocator and shared-byte agreement use the same segment endpoint. -/
structure AllocatorPrefix {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq)
    (N : NativeAddrs) (phiF phiC : Addr → Nat) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (credits : Nat) (store : Store)
    (before after : Config) : Prop where
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store after.σ.mem
  agreement : AgreeP shared before.σ.mem after.σ.mem

/-- Apply the existing stack-transport theorem to an actual reflected prefix. -/
theorem allocator_prefix
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {N : NativeAddrs}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {store : Store} {before after : Config}
    {bs : List BBlock} {regs selected : GRegs} {loads : List (List (BitVec 8))}
    {pc : BitVec 64} {foot : Nat → Prop} {keep : Register → Bool}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits
      store before.σ.mem)
    (run : SelectedFramedSegResult bs regs loads pc foot keep selected before after)
    (contained : ∀ k, foot k → SL.lo ≤ k ∧ k < SL.hi) :
    AllocatorPrefix M N phiF phiC alloc exts shared credits store before after := by
  have hm : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = after.σ.mem[k]? :=
    fun k hk => run.outside k (fun hf => hk (contained k hf))
  exact
    { allocator := allocator.after_stack L hm
      agreement := fun k hk => hm k ((allocator.runtime L).shared_off_stack hk) }

/-- Shared AST reads survive the same prefix as the allocator. -/
theorem AllocatorPrefix.ast
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {N : NativeAddrs}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {store : Store} {before after : Config}
    (h : AllocatorPrefix M N phiF phiC alloc exts shared credits store before after)
    {a : Nat} {e : Expr} (ast : ExprReprWithin before.σ.mem shared a e) :
    ExprReprWithin after.σ.mem shared a e :=
  ast.transport h.agreement

/-- The left child cannot overwrite either saved word in the caller's frame. -/
theorem FirstSaved.after_left
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat} {nf nc : Nat}
    {st : Vsa.While.St} {v : Value} {sp ret saved env : BitVec 64}
    {m : Mem} {after : Config}
    (h : FirstSaved m sp saved env)
    (exit : EvalExit g N A SL phiF phiC nf nc st v sp ret (sp + 120#64) m after)
    (w : Window SL sp) (hsp : sp.toNat + 1056 ≤ 0x100000000)
    (arenaStack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo) :
    FirstSaved after.σ.mem sp saved env := by
  have hdst : (sp + 120#64).toNat = sp.toNat + 120 := by
    rw [BitVec.toNat_add]
    change (sp.toNat + 120) % 2^64 = sp.toNat + 120
    exact Nat.mod_eq_of_lt (by omega)
  have agree : AgreeP (firstFoot sp) m after.σ.mem := by
    intro k hk
    have within := w.first hk
    have frame := exit.memFrame k (by unfold firstFoot at hk; omega)
      (by rcases arenaStack with ha | ha <;> omega)
    rw [hdst] at frame
    unfold firstFoot at hk
    rcases frame with slot | same
    · omega
    · exact same.symm
  have rd (a : Nat) (ha : ∀ k, k < 8 → firstFoot sp (a + k)) :
      read64 m a = read64 after.σ.mem a := read64_agreeP agree ha
  exact
    { saved := (rd (sp.toNat + 1048) (by
        intro k hk
        exact Or.inl ⟨by omega, by omega⟩)).symm.trans h.saved
      environment := (rd sp.toNat (by
        intro k hk
        exact Or.inr ⟨by omega, by omega⟩)).symm.trans h.environment }

#print axioms Window.first
#print axioms Window.second
#print axioms allocator_prefix
#print axioms AllocatorPrefix.ast
#print axioms FirstSaved.after_left

end Vsa.Sim.BinaryPrefix
