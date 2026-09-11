import Vsa.Sim.rows.EvalEqNeFront
import Vsa.Sim.ValueEqualPresent

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While

namespace Vsa.Sim

/-- Equality call data at the actual dispatch endpoint.
The helper supplies return presence; strings require no pointer alignment. -/
structure EqFrontPresent
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (fbase sret : BitVec 64) (vl vr : Value) (link jalPC : BitVec 64) (jImm : BitVec 21)
    (mA : Mem) (out0 : Array String) (cD : Config) : Prop where
  hmemD : cD.σ.mem = mA
  hG : GoodState cD.σ
  htick : cD.tick < 2
  hpc : cD.σ.regs.get? Register.PC = some jalPC
  hjalTgt : (jalPC + sign_extend (m := 64) jImm) = (0x8000285c#64 : BitVec 64)
  hlink : BitVec.addInt jalPC 4 = link
  hlinkAl : (BitVec.update (link + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
  hx10 : cD.σ.regs.get? Register.x10 = some (fbase + 0x40#64)
  hx11 : cD.σ.regs.get? Register.x11 = some (fbase + 0x20#64)
  hx2 : cD.σ.regs.get? Register.x2 = some fbase
  hx9 : cD.σ.regs.get? Register.x9 = some sret
  hout : cD.σ.sailOutput = out0
  jalSite : ∀ (σ : MState) (i u : Nat) (pc vminstret : BitVec 64),
    GoodState σ → σ.regs.get? Register.PC = some pc →
    σ.regs.get? Register.minstret = some vminstret →
    Vsa.Sim.Code.Eval_exprLoaded σ.mem → pc = jalPC → i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ pc vminstret jImm Register.x1 (BitVec.addInt pc 4))
  hVeLoaded : Vsa.Sim.Code.Value_equalLoaded mA
  hJT : JumpTable mA
  hEE : Vsa.Sim.Code.Eval_exprLoaded mA
  hStrc : Vsa.Sim.Code.StrcmpLoaded mA
  hMask : MaskPinned mA
  hRegA : VERegion (fbase + 0x40#64)
  hRegB : VERegion (fbase + 0x20#64)
  hReprA : ValueRepr mA N φc (fbase + 0x40#64).toNat vl
  hReprB : ValueRepr mA N φc (fbase + 0x20#64).toNat vr
  hIdentity : ValueEqualityIdentity N φc vl vr
  hraln4 : link.toNat % 4 = 0
  strings : ∀ sa sb, vl = .str sa → vr = .str sb →
    ValueEqualStringData (fbase + 0x40#64) (fbase + 0x20#64) fbase sa sb mA
  hsnapEval : ∀ R : Register, NotWrittenVEStr R → (Register.x1 == R) = false →
    (Register.x9 == R) = false → (Register.x19 == R) = false →
    cD.σ.regs.get? R = g R

/-- Execute the equality call and retain its actual memory and register frame. -/
theorem blockC_eqne_front_present
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (fbase sret : BitVec 64) (vl vr : Value) (link jalPC : BitVec 64) (jImm : BitVec 21)
    (mA : Mem) (out0 : Array String) (cD : Config)
    (hData : EqFrontPresent g N φc fbase sret vl vr link jalPC jImm mA out0 cD) :
    ∃ (cR : Config), Steps cD cR ∧
      VeReturn g fbase sret vl vr link out0 mA cR := by
  obtain ⟨cP, hStepsP, hx2P, hx9P, hframeP, hVePre⟩ :=
    eqnePreBridge (fun R => cD.σ.regs.get? R) N φc fbase sret vl vr mA out0
      jalPC link jImm hData.jalSite hData.hjalTgt hData.hlink hData.hlinkAl
      hData.hVeLoaded hData.hJT hData.hEE hData.hRegA hData.hRegB hData.hReprA hData.hReprB
      cD ⟨hData.hmemD, hData.hpc, hData.hx10, hData.hx11, hData.hx2, hData.hx9,
        (fun _ _ _ => rfl), hData.hout, hData.htick, hData.hG⟩
  obtain ⟨cV, hStepsV, hVePost⟩ :=
    value_equal_spec_present (fun R => cP.σ.regs.get? R) (fbase + 0x40#64) (fbase + 0x20#64)
      link fbase N φc vl vr mA out0 cP hData.hIdentity hVePre hx2P hData.hStrc hData.hMask
      hData.hraln4 hData.strings
  have hEvalCollapse : ∀ R : Register, NotWrittenVEStr R →
      (Register.x9 == R) = false → (Register.x19 == R) = false →
      (fun R => cP.σ.regs.get? R) R = g R := by
    intro R hR he9 he19
    exact (hframeP R hR hR.1).trans (hData.hsnapEval R hR hR.1 he9 he19)
  refine ⟨cV, (hStepsP.trans hStepsV), ?_⟩
  exact veReturnBridge (fun R => cP.σ.regs.get? R) g fbase sret vl vr link out0 mA cV
    hx9P hEvalCollapse hVePost.presence hVePost.post

#print axioms blockC_eqne_front_present

end Vsa.Sim
