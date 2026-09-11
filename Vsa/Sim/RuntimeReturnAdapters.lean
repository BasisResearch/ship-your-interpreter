import Vsa.Sim.RuntimeIH

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine

namespace Vsa.Sim

/-- Select the same representation maps in every statement exit field. -/
theorem ExecExitD.withRuntimeRepr
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC resultF resultC : Addr → Nat} {nf nc : Nat} {shared : Nat → Prop}
    {st : Vsa.While.St} {status : Status} {sp ret aRet : BitVec 64} {m0 : Mem} {c : Config}
    (h : ExecExitD g N A SL phiF phiC nf nc st status sp ret aRet m0 c)
    (hr : ReturnRepr N A phiF phiC resultF resultC nf nc st.store
      (statusResults aRet.toNat status)
      (RuntimeResult N A SL shared st.store (statusResults aRet.toNat status) m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) c.σ.mem) :
    ExecRuntimeReturn g N A SL phiF phiC nf nc shared st status sp ret aRet m0 c := by
  obtain ⟨exit, presence, _⟩ := h
  have exit' : ExecExit g N A SL phiF phiC nf nc st status sp ret aRet m0 c :=
    { exit with
      store := ⟨resultF, resultC, hr.frames, hr.closures, hr.storeRepr⟩
      retval := fun v hv => ⟨resultC, hr.closures,
        hr.values _ v (by rw [hv]; exact List.mem_singleton_self _)⟩ }
  exact ⟨⟨exit', presence, resultF, resultC, hr.frames, hr.closures, hr.survives⟩,
    resultF, resultC, hr⟩

/-- The selected evaluator result preserves the caller's shared reads. -/
theorem EvalRuntimeReturn.shared_agree
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {nf nc : Nat} {shared : Nat → Prop} {st : Vsa.While.St} {v : Value}
    {sp ret dst : BitVec 64} {m0 : Mem} {c : Config}
    (h : EvalRuntimeReturn g N A SL phiF phiC nf nc shared st v sp ret dst m0 c) :
    AgreeP shared m0 c.σ.mem := by
  obtain ⟨_, _, repr⟩ := h.repr.selected
  exact repr.owned.shared_agree

#print axioms ExecExitD.withRuntimeRepr
#print axioms EvalRuntimeReturn.shared_agree

/-- The selected statement result preserves the caller's shared reads. -/
theorem ExecRuntimeReturn.shared_agree
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {nf nc : Nat} {shared : Nat → Prop} {st : Vsa.While.St} {status : Status}
    {sp ret aRet : BitVec 64} {m0 : Mem} {c : Config}
    (h : ExecRuntimeReturn g N A SL phiF phiC nf nc shared st status sp ret aRet m0 c) :
    AgreeP shared m0 c.σ.mem := by
  obtain ⟨_, _, repr⟩ := h.selected
  exact repr.owned.shared_agree

#print axioms ExecRuntimeReturn.shared_agree

end Vsa.Sim
