import Vsa.Sim.SeqClosureRetResume
import Vsa.MemReprWithin

namespace Vsa.Sim

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Code and loop words read from the actual child-return memory. -/
structure SeqClosureNormalReadback (m : Mem) (sp body : BitVec 64) (count : Nat) : Prop where
  code : Code.Eval_exprLoaded m
  savedBody : read64 m sp.toNat = some body.toNat
  bodyCount : read32 m (body.toNat + 16) = some count

/-- The child's frame preserves its saved body; owned sharing preserves the count. -/
theorem SeqClosureNormalReadback.of_exit
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat} {nf nc : Nat}
    {st : Vsa.While.St} {status : Status} {sp aRet body : BitVec 64} {ret : BitVec 64}
    {count : Nat} {m0 mCall : Mem} {shared : Nat → Prop} {cfg : Config}
    (h : SeqClosureRetCarrier g gExec A SL sp aRet m0 mCall)
    (child : ExecExitD gExec N A SL phiF phiC nf nc st status sp ret aRet mCall cfg)
    (support : EvalCallSupport mCall SL A sp)
    (savedBody : read64 mCall sp.toNat = some body.toNat)
    (savedOffRet : sp.toNat + 8 ≤ aRet.toNat)
    (bodyCount : read32 mCall (body.toNat + 16) = some count)
    (countCovered : Covers shared (body.toNat + 16) 4)
    (agreement : AgreeP shared mCall cfg.σ.mem) :
    SeqClosureNormalReadback cfg.σ.mem sp body count := by
  have returnedSupport : EvalCallSupport cfg.σ.mem SL A sp :=
    support.transport_frame h.spLe h.retInStack child.1.memFrame
  obtain ⟨code, _, _, _, _, _⟩ := returnedSupport.pins _ (fun _ _ => rfl)
  refine ⟨code, ?_, (read32_agreeP agreement countCovered).symm.trans bodyCount⟩
  have savedAgreement : AgreeP (fun k => sp.toNat ≤ k ∧ k < sp.toNat + 8)
      mCall cfg.σ.mem := by
    intro k hk
    have hA := h.childFrame.arenaBelow
    have hlo := h.childFrame.stackLo
    exact ((child.1.memFrame k (by omega) (by omega)).resolve_left (by omega)).symm
  rw [← read64_agreeP savedAgreement (fun k hk => ⟨by omega, by omega⟩)]
  exact savedBody

#print axioms SeqClosureNormalReadback.of_exit

end Vsa.Sim
