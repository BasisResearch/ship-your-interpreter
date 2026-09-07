import Vsa.Sim.ExecBlock
import Vsa.Sim.ExecWhileSites

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (Config Step Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Logic (Triple)

/-- Actual normal-exit head, with the selected store maps and saved parent
frame. Both a falsy condition and a breaking body establish this predicate. -/
structure WhileNormalExitTailPre
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φf' φc' : Addr → Nat) (nf nc : Nat)
    (st' : Vsa.While.St) (sp r aRet : BitVec 64) (m0 : Mem)
    (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? PC = some 0x80004090#64
  minstret : ∃ v, cfg.σ.regs.get? Register.minstret = some v
  spReg : cfg.σ.regs.get? x2 = some (sp - 176#64)
  code : Code.Exec_stmtLoaded cfg.σ.mem
  out : OutRepr cfg.σ st'
  frames : PhiExtends φf φf' nf
  closures : PhiExtends φc φc' nc
  storeSurvives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cfg.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store
  saved_ra : read64 cfg.σ.mem (sp.toNat - 8) = some r.toNat
  saved_s0 : ∃ v, read64 cfg.σ.mem (sp.toNat - 16) = some v.toNat ∧ g x8 = some v
  saved_s1 : ∃ v, read64 cfg.σ.mem (sp.toNat - 24) = some v.toNat ∧ g x9 = some v
  saved_s2 : ∃ v, read64 cfg.σ.mem (sp.toNat - 32) = some v.toNat ∧ g x18 = some v
  saved_s3 : ∃ v, read64 cfg.σ.mem (sp.toNat - 40) = some v.toNat ∧ g x19 = some v
  parentSp : g x2 = some sp
  frame : ∀ R, AbiPreservedNoise R →
    (x8 == R) = false → (x9 == R) = false →
    (x18 == R) = false → (x19 == R) = false →
    (x2 == R) = false → cfg.σ.regs.get? R = g R
  memExtends : MemExtends m0 cfg.σ.mem
  memFrame : ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
    ¬ (A.lo ≤ a ∧ a < A.hi) →
    (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ cfg.σ.mem[a]? = m0[a]?
  spRoom : 176 ≤ sp.toNat
  spHi : sp.toNat ≤ 0x100000000
  spLo : 0x80000000 ≤ sp.toNat
  spWin : tohostAddr + 16 + 176 ≤ sp.toNat
  spAlign : sp.toNat % 8 = 0
  retAlign : r.toNat % 4 = 0

/-- Set normal status and execute the existing shared epilogue. The widened
exit is attached to this run and retains the preselected store witnesses. -/
theorem execWhileNormalExitTail
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {φf φc φf' φc' : Addr → Nat} {nf nc : Nat}
    {st' : Vsa.While.St} {sp r aRet : BitVec 64} {m0 : Mem} :
    Triple
      (WhileNormalExitTailPre g N A SL φf φc φf' φc' nf nc st' sp r aRet m0)
      (ExecExitD g N A SL φf φc nf nc st' .normal sp r aRet m0) := by
  intro cfg h
  obtain ⟨vmi, hmi⟩ := h.minstret
  obtain ⟨σ1, i1, hs1', hi1, hg1, hm1, ho1⟩ :=
    site_80004090_es cfg.σ cfg.tick cfg.steps 0x80004090#64 vmi
      h.good h.pc hmi h.code rfl h.tick
  have hs1 : Step cfg ⟨σ1, i1, cfg.steps + 1⟩ := by cases cfg; exact hs1'
  have hpc1 : σ1.regs.get? PC = some 0x80004094#64 := by
    have := obs_alu_pc ho1
    simpa only [show BitVec.addInt (0x80004090#64) 4 = (0x80004094#64 : BitVec 64)
      from by decide] using this
  have ha01 : σ1.regs.get? x10 = some (StatusCode .normal) := by
    have := obs_alu_rd ho1 (by decide) (by decide) (by decide) (by decide) (by decide)
    simpa only [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) =
      StatusCode .normal from by decide] using this
  have hsp1 := obs_alu_other' ho1 x2 (by decide) h.spReg
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret ho1
  obtain ⟨σ2, i2, hs2, hi2, hg2, hm2, ho2⟩ :=
    site_80004094_es σ1 i1 (cfg.steps + 1) 0x80004094#64 vmi1
      hg1 hpc1 hmi1 (by rw [hm1]; exact h.code) rfl (by decide) hi1
  have hmTail : σ2.mem = cfg.σ.mem := hm2.trans hm1
  have hpc2 : σ2.regs.get? PC = some 0x8000409c#64 := by
    have := obs_jr_pc ho2
    simpa only [show (0x80004094#64 + sign_extend (m := 64) (0x000008#21)) =
      (0x8000409c#64 : BitVec 64) from by decide] using this
  have ha02 := obs_jr_other' ho2 x10 (by decide) ha01
  have hsp2 := obs_jr_other' ho2 x2 (by decide) hsp1
  obtain ⟨vmi2, hmi2⟩ := obs_jr_minstret ho2
  have htailFrame (R : Register) (hR : AbiPreservedNoise R) :
      σ2.regs.get? R = cfg.σ.regs.get? R := by
    have h10 : (x10 == R) = false := by
      rcases hx : (x10 == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hx
        have ha := hR.1
        rw [← hx] at ha
        exact absurd ha (by decide)
    obtain ⟨_, hPC, hNPC, hMI, hMII, hMC, hMT, hMIP⟩ := hR
    exact ((ho2.1 R hMC hMT hMIP).trans
      (get?_sigmaPost_jump_x0 _ _ _ _ R hMI hPC hNPC hMII)).trans
      ((ho1.1 R hMC hMT hMIP).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hMI hPC h10 hNPC hMII))
  have hout2 : OutRepr σ2 st' := by
    change String.join σ2.sailOutput.toList = st'.out
    rw [ho2.out, sailOutput_sigmaPost_jump_x0, ho1.out, sailOutput_sigmaPost_alu]
    exact h.out
  obtain ⟨v8, hr8, hg8⟩ := h.saved_s0
  obtain ⟨v9, hr9, hg9⟩ := h.saved_s1
  obtain ⟨v18, hr18, hg18⟩ := h.saved_s2
  obtain ⟨v19, hr19, hg19⟩ := h.saved_s3
  have hpre : PreExecEpilogue g N A SL φf' φc' st' .normal sp r aRet
      v8 v9 v18 v19 σ2.sailOutput cfg.σ.mem cfg.σ.mem
      ⟨σ2, i2, cfg.steps + 1 + 1⟩ := by
    refine ⟨hg2, hi2, hpc2, ha02, hsp2, ⟨vmi2, hmi2⟩, rfl, hout2,
      hmTail, h.code, h.storeSurvives _ (fun _ _ => rfl), ?_,
      h.saved_ra, hr8, hr9, hr18, hr19, hg8, hg9, hg18, hg19, h.parentSp,
      (fun _ _ => rfl), h.spRoom, h.spHi, h.spLo, h.spWin, h.spAlign, h.retAlign⟩
    intro R hR he8 he9 he18 he19 he2
    exact (htailFrame R hR).trans (h.frame R hR he8 he9 he18 he19 he2)
  obtain ⟨cD, hstepsD, hExit, hmD⟩ :=
    execBlockDQ g N A SL φf' φc' nf nc st' .normal sp r aRet
      v8 v9 v18 v19 σ2.sailOutput cfg.σ.mem
      (fun m => m = cfg.σ.mem) (by intro v hv; cases hv)
      ⟨σ2, i2, cfg.steps + 1 + 1⟩ ⟨cfg.σ.mem, hpre, rfl⟩
  refine ⟨cD, (Steps.single hs1).trans ((Steps.single hs2).trans hstepsD),
    ?_, ?_, φf', φc', h.frames, h.closures, ?_⟩
  · exact
      { good := hExit.good
        tick := hExit.tick
        pc := hExit.pc
        a0 := hExit.a0
        ra := hExit.ra
        spReg := hExit.spReg
        minstret := hExit.minstret
        store := ⟨φf', φc', h.frames, h.closures, by
          rw [hmD]; exact h.storeSurvives _ (fun _ _ => rfl)⟩
        out := hExit.out
        retval := by intro v hv; cases hv
        frame := hExit.frame
        memFrame := by rw [hmD]; exact h.memFrame }
  · rw [hmD]
    exact h.memExtends
  · rw [hmD]
    exact h.storeSurvives

#print axioms execWhileNormalExitTail

end Vsa.Sim
