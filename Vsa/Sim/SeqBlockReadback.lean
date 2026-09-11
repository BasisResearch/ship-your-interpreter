import Vsa.Sim.SeqBlockExit
import Vsa.Sim.SeqBlockNormal
import Vsa.Sim.Code.FixedImage_Exec_stmt

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Protected loop words at the reached block statement call. -/
structure SeqBlockNormalCarrier
    (g gExec : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (shared : Nat → Prop)
    (sp aRet block : BitVec 64) (index count : Nat) (m0 mCall : Mem) : Prop
    extends SeqBlockCaller g gExec A SL sp aRet m0 mCall where
  blockReg : gExec .x8 = some block
  geometry : SeqBlockNormal.Geometry sp block
  stackLo : SL.lo ≤ sp.toNat
  savedOffArena : sp.toNat + 16 ≤ A.lo ∨ A.hi ≤ sp.toNat + 8
  savedOffRet : sp.toNat + 16 ≤ aRet.toNat ∨ aRet.toNat + 24 ≤ sp.toNat + 8
  savedIndex : read64 mCall (sp.toNat + 8) = some index
  blockCount : read32 mCall (block.toNat + 16) = some count
  countCovered : Covers shared (block.toNat + 16) 4
  nextBound : index + 1 ≤ count
  countBound : count < 2^31

/-- The child's frame and owned sharing supply both normal-route reads. -/
theorem SeqBlockNormalCarrier.normalPre
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat} {nf nc : Nat}
    {final : Vsa.While.St} {shared : Nat → Prop} {sp aRet block : BitVec 64}
    {index count : Nat} {m0 mCall : Mem} {cfg : Config} {more : Bool}
    (h : SeqBlockNormalCarrier g gExec A SL shared sp aRet block index count m0 mCall)
    (support : EvalCallSupport mCall SL A sp)
    (child : ExecExitD gExec N A SL phiF phiC nf nc final .normal
      sp 0x800041c8#64 aRet mCall cfg)
    (agreement : AgreeP shared mCall cfg.σ.mem)
    (branch : decide (index + 1 < count) = more) :
    SeqBlockNormal.Pre sp block index count more cfg := by
  have image : EvalCallSupport cfg.σ.mem SL A sp :=
    support.transport_frame h.spLe h.retInStack child.1.memFrame
  have savedAgreement : AgreeP (fun k => sp.toNat + 8 ≤ k ∧ k < sp.toNat + 16)
      mCall cfg.σ.mem := by
    intro k hk
    have := h.stackLo
    have := h.savedOffArena
    have := h.savedOffRet
    exact ((child.1.memFrame k (by omega) (by omega)).resolve_left (by omega)).symm
  exact
    { good := child.1.good, tick := child.1.tick, pc := child.1.pc
      minstret := child.1.minstret
      registers := ⟨child.1.a0, child.1.spReg,
        (child.1.frame .x8 (by decide)).trans h.blockReg, trivial⟩
      geometry := h.geometry, nextBound := h.nextBound, countBound := h.countBound
      branch := branch
      savedIndex := (read64_agreeP savedAgreement (fun k hk => ⟨by omega, by omega⟩)).symm.trans
        h.savedIndex
      blockCount := (read32_agreeP agreement h.countCovered).symm.trans h.blockCount
      code := image.image.text.Exec_stmtLoaded }

#print axioms SeqBlockNormalCarrier.normalPre

end Vsa.Sim
