import Vsa.Sim.EqBoxCall
import Vsa.Sim.EqBoxMemory
import Vsa.Sim.rows.EvalEqNeRowFootprint

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc
open Vsa.Machine Vsa.Sim.Code

namespace Vsa.Sim
namespace EqNeOp

def boolExitPC : EqNeOp → BitVec 64
  | .eq => 0x80003730#64
  | .ne => 0x80003780#64

def boolExitImm : EqNeOp → BitVec 21
  | .eq => 0x1ffcbc#21
  | .ne => 0x1ffc6c#21

/-- Equality boxing uses the ordinary outer epilogue frame. -/
theorem boolFrame_kept (R : Register) : AbiPreservedNoise R →
    (Register.x2 == R) = false → NotWrittenVEStr R := by
  cases R <;> decide

/-- The completed boolean box retains the actual cell writes and epilogue entry. -/
structure BoxedAt (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (final : Vsa.While.St) (value : Bool) (sp ret dst v8 v9 v18 : BitVec 64)
    (out : Array String) (m0 mEnt mpre : Mem) (before after : Config) : Prop where
  run : Steps before after
  pre : PreEpilogueVD g N A SL phiF phiC final (.bool value)
    sp ret dst v8 v9 v18 out m0 mpre after
  footprint : MemFootprint (eqneCellFoot sp.toNat dst.toNat) mEnt mpre

/-- Run the boolean box and restore path using the actual helper return. -/
theorem finishBox (op : EqNeOp)
    {g ghost : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {final : Vsa.While.St} {vl vr : Value} {sp ret dst v8 v9 v18 v19 : BitVec 64}
    {out : Array String} {m0 mEnt : Mem} {before : Config}
    (returned : VeReturn ghost (sp - 1088#64) dst vl vr op.returnPC out mEnt before)
    (box : EqNeBoxPre g N A SL phiF phiC final sp ret dst v8 v9 v18 v19 v19 out m0 mEnt)
    (collapse : ∀ R, AbiPreservedNoise R → (Register.x8 == R) = false →
      (Register.x9 == R) = false → (Register.x18 == R) = false →
      (Register.x2 == R) = false → (Register.x19 == R) = false → ghost R = g R) :
    ∃ after mpre tailF tailC,
      BoxedAt g N A SL tailF tailC final (op.result vl vr) sp ret dst v8 v9 v18
        out m0 mEnt mpre before after := by
  have lowered : (sp - 1088#64).toNat = sp.toNat - 1088 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact box.hsp1088)
  have outside : ∀ k, ¬ (sp.toNat - 1104 ≤ k ∧ k < sp.toNat - 1088) →
      before.σ.mem[k]? = mEnt[k]? := by
    intro k hk
    apply returned.hmemframe
    rw [lowered]
    omega
  have boxR := box.after_helper returned.hMemExt outside
  have pc : before.σ.regs.get? Register.PC = some op.returnPC := by
    have update : BitVec.update (op.returnPC + sign_extend (m := 64) (0x000#12)) 0 0#1 =
        op.returnPC := by cases op <;> decide
    exact update ▸ returned.hpc
  obtain ⟨called, call⟩ := op.boolCall (sp - 1088#64) dst
    (cond (vl.equal vr) 1#64 0#64) before returned.hG returned.htick pc
    returned.hx10 returned.hx9 returned.hsp boxR.hcodeEnt
  have boxC : EqNeBoxPre g N A SL phiF phiC final sp ret dst v8 v9 v18 v19 v19 out m0
      called.σ.mem := call.memory.symm ▸ boxR
  have frame : ∀ R, AbiPreservedNoise R → (Register.x8 == R) = false →
      (Register.x9 == R) = false → (Register.x18 == R) = false →
      (Register.x2 == R) = false → (Register.x19 == R) = false → called.σ.regs.get? R = g R := by
    intro R hR h8 h9 h18 h2 h19
    exact (call.frame R hR.1).trans ((returned.hframe R (boolFrame_kept R hR h2) h9 h19).trans
      (collapse R hR h8 h9 h18 h2 h19))
  have ldSite : LdS3Site op.boolLink := by
    cases op with
    | eq => exact site_8000372c_ee
    | ne => exact site_8000377c_ee
  have jumpSite : JExitSite op.boolExitPC op.boolExitImm := by
    cases op with
    | eq => exact site_80003730_ee
    | ne => exact site_80003780_ee
  obtain ⟨lo, hi, htif, aligned⟩ := eqne_ld_geom sp box.hsp1088 box.hspRam box.hspHtif box.hsp8
  obtain ⟨mpre, middleF, middleC, tailF, tailC, after, run, _, _, _, _, pre, footprint⟩ :=
    boolBoxEpilogue_footprint g N A SL phiF phiC phiF phiC phiF phiC
      final.store.frames.size final.store.closures.size final.store.frames.size final.store.closures.size
      final final sp ret dst v8 v9 v18 v19 v19
      (op.boolWord (cond (vl.equal vr) 1#64 0#64)) (op.result vl vr) out m0 called
      op.boolLink op.boolLink op.boolExitPC op.boolExitImm ldSite jumpSite
      rfl (by cases op <;> decide) (by cases op <;> decide)
      (by cases op <;> decide) (by cases op <;> decide) (eqne_ldPCeq sp box.hsp1088)
      call.good boxC.hVboolEnt call.pc call.result call.value call.link call.destination call.stack
      call.minstret call.tick (call.output.trans returned.hout) boxC.hcodeEnt boxC.hBoolRegion
      (by cases op <;> decide) (op.boolWord_result vl vr)
      (PhiExtends.refl phiF final.store.frames.size)
      (PhiExtends.refl phiC final.store.closures.size)
      (PhiExtends.refl phiF final.store.frames.size)
      (PhiExtends.refl phiC final.store.closures.size) boxC.houtStr boxC.hSurvSL0
      boxC.hs3Ent boxC.hslotRa0 boxC.hslotS00 boxC.hslotS10 boxC.hslotS20
      boxC.hgv8 boxC.hgv9 boxC.hgv18 boxC.hgv2 boxC.hgx19 rfl frame
      boxC.hMemExt0 boxC.hWordsEnt boxC.hmemframe0
      boxC.hsretEvalCode boxC.hsretStk boxC.hsretInSL boxC.hSLlo40 boxC.hSLlo32
      boxC.hsp1088 boxC.hspRam boxC.hspLo boxC.hspHtif boxC.hsp8 boxC.hraAl lo hi htif aligned
  refine ⟨after, mpre, tailF, tailC, call.run.trans run, pre, ⟨?_⟩⟩
  intro k hk
  have resultOutside : ¬ resultSlot dst.toNat k := by
    intro hr; exact hk (Or.inr hr)
  exact (footprint.agree k resultOutside).trans
    ((congrArg (fun memory : Mem => memory[k]?) call.memory).trans
      (outside k (by unfold eqneCellFoot at hk; omega)))

#print axioms boolFrame_kept
#print axioms finishBox

end EqNeOp
end Vsa.Sim
