import Vsa.Sim.ExecBrkCont
import Vsa.Sim.ExecBlock
import Vsa.Sim.ObsAvoid

/-!
# `ExecNormalExitTail` — the parametric `li a0,0; j 0x8000409c; epilogue` tail

Every `exec_stmt` arm that completes `.normal` ends with the same two
instructions at an arm-specific PC (`0x80004090` for `while`, `0x80004184` for
`expr`, `0x800042d4` for `if` without `else`, `0x80004118` for `varDecl`,
`0x800041e0` for `block`) followed by the shared epilogue.  `WhileNormalExitTail`
proved this tail at `0x80004090`; this file proves it ONCE over the `li` PC and
the `j` immediate, taking the two site lemmas as certificate fields.
-/

-- discipline: allow(R7-conj-tower-def) every `∃` here is a single saved-register witness inside a named-field structure (`NormalExitTailPre`, `EpilogueReady`), mirroring `PreExecEpilogue`'s ghost pins; no ∃/∧ tower is defined
namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Logic (Triple)
open Vsa.Sim.Code

/-- Actual normal-exit head at the arm's `li a0,0`, with the selected store
maps and the saved parent frame. -/
structure NormalExitTailPre (liPC : BitVec 64)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φf' φc' : Addr → Nat) (nf nc : Nat)
    (st' : Vsa.While.St) (sp r aRet : BitVec 64) (m0 : Mem)
    (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? PC = some liPC
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

/-- The generated `li a0,0` site at `liPC`. -/
def LiZeroSite (liPC : BitVec 64) : Prop :=
  ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
    GoodState σ → σ.regs.get? Register.PC = some liPC →
    σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ liPC vmi Register.x10
        ((0#64) + sign_extend (m := 64) (0x000#12)))

/-- The generated `j` site at `jPC` with immediate `jImm`. -/
def JumpSite (jPC : BitVec 64) (jImm : BitVec 21) : Prop :=
  ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
    GoodState σ → σ.regs.get? Register.PC = some jPC →
    σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem →
    (jPC + sign_extend (m := 64) jImm).toNat % 4 = 0 → i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ jPC vmi (jPC + sign_extend (m := 64) jImm))

/-- Agreement with a common base on a prefix is agreement between the two
extensions. -/
theorem PhiExtends.of_common {φ φ1 φ2 : Addr → Nat} {n : Nat}
    (h1 : PhiExtends φ φ1 n) (h2 : PhiExtends φ φ2 n) : PhiExtends φ1 φ2 n :=
  fun a ha => (h2 a ha).trans (h1 a ha).symm

/-- Actual state at the shared epilogue entry `0x8000409c`: the produced
status in `a0`, the selected store maps, the parent frame in its spill slots,
and (for `ret`) the represented return value under the selected closure map. -/
structure EpilogueReady
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φf' φc' : Addr → Nat) (nf nc : Nat)
    (st' : Vsa.While.St) (status : Status) (sp r aRet : BitVec 64) (m0 : Mem)
    (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? PC = some 0x8000409c#64
  a0 : cfg.σ.regs.get? x10 = some (StatusCode status)
  minstret : ∃ v, cfg.σ.regs.get? Register.minstret = some v
  spReg : cfg.σ.regs.get? x2 = some (sp - 176#64)
  code : Code.Exec_stmtLoaded cfg.σ.mem
  out : OutRepr cfg.σ st'
  frames : PhiExtends φf φf' nf
  closures : PhiExtends φc φc' nc
  storeSurvives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cfg.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store
  retval : ∀ v, status = .ret v →
    ∃ φc'', PhiExtends φc' φc'' nc ∧ ValueRepr cfg.σ.mem N φc'' aRet.toNat v
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

/-- Run the shared epilogue from any produced status.  The widened exit
retains the preselected store witnesses; the return value (if any) is
rebased to the entry closure map. -/
theorem epilogueTail
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {φf φc φf' φc' : Addr → Nat} {nf nc : Nat}
    {st' : Vsa.While.St} {status : Status} {sp r aRet : BitVec 64} {m0 : Mem} :
    Triple
      (EpilogueReady g N A SL φf φc φf' φc' nf nc st' status sp r aRet m0)
      (ExecExitD g N A SL φf φc nf nc st' status sp r aRet m0) := by
  intro cfg h
  obtain ⟨v8, hr8, hg8⟩ := h.saved_s0
  obtain ⟨v9, hr9, hg9⟩ := h.saved_s1
  obtain ⟨v18, hr18, hg18⟩ := h.saved_s2
  obtain ⟨v19, hr19, hg19⟩ := h.saved_s3
  have hpre : PreExecEpilogue g N A SL φf' φc' st' status sp r aRet
      v8 v9 v18 v19 cfg.σ.sailOutput cfg.σ.mem cfg.σ.mem cfg :=
    ⟨h.good, h.tick, h.pc, h.a0, h.spReg, h.minstret, rfl, h.out,
      rfl, h.code, h.storeSurvives _ (fun _ _ => rfl), h.frame,
      h.saved_ra, hr8, hr9, hr18, hr19, hg8, hg9, hg18, hg19, h.parentSp,
      (fun _ _ => rfl), h.spRoom, h.spHi, h.spLo, h.spWin, h.spAlign, h.retAlign⟩
  obtain ⟨cD, hstepsD, hExit, hmD⟩ :=
    execBlockDQR g N A SL φf' φc' nf nc st' status sp r aRet
      v8 v9 v18 v19 cfg.σ.sailOutput cfg.σ.mem
      (fun m => m = cfg.σ.mem)
      (fun v hv m hm => by subst hm; exact h.retval v hv)
      cfg ⟨cfg.σ.mem, hpre, rfl⟩
  refine ⟨cD, hstepsD, ?_, ?_, φf', φc', h.frames, h.closures, ?_⟩
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
        retval := fun v hv => by
          obtain ⟨φc'', hp, hrepr⟩ := h.retval v hv
          exact ⟨φc'', h.closures.trans hp, by rw [hmD]; exact hrepr⟩
        frame := hExit.frame
        memFrame := by rw [hmD]; exact h.memFrame }
  · rw [hmD]
    exact h.memExtends
  · rw [hmD]
    exact h.storeSurvives

#print axioms epilogueTail

/-- Set normal status, jump into the shared epilogue, and run it.  The widened
exit is attached to this run and retains the preselected store witnesses. -/
theorem normalExitTail (liPC : BitVec 64) (jImm : BitVec 21)
    (hli : LiZeroSite liPC) (hj : JumpSite (BitVec.addInt liPC 4) jImm)
    (htgt : BitVec.addInt liPC 4 + sign_extend (m := 64) jImm = 0x8000409c#64)
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {φf φc φf' φc' : Addr → Nat} {nf nc : Nat}
    {st' : Vsa.While.St} {sp r aRet : BitVec 64} {m0 : Mem} :
    Triple
      (NormalExitTailPre liPC g N A SL φf φc φf' φc' nf nc st' sp r aRet m0)
      (ExecExitD g N A SL φf φc nf nc st' .normal sp r aRet m0) := by
  intro cfg h
  obtain ⟨vmi, hmi⟩ := h.minstret
  obtain ⟨σ1, i1, hs1', hi1, hg1, hm1, ho1⟩ :=
    hli cfg.σ cfg.tick cfg.steps vmi h.good h.pc hmi h.code h.tick
  have hs1 : Step cfg ⟨σ1, i1, cfg.steps + 1⟩ := by cases cfg; exact hs1'
  have hpc1 : σ1.regs.get? PC = some (BitVec.addInt liPC 4) := obs_alu_pc ho1
  have ha01 : σ1.regs.get? x10 = some (StatusCode .normal) := by
    have := obs_alu_rd ho1 (by decide) (by decide) (by decide) (by decide) (by decide)
    simpa only [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) =
      StatusCode .normal from by decide] using this
  have hsp1 := obs_alu_other' ho1 x2 (by decide) h.spReg
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret ho1
  obtain ⟨σ2, i2, hs2, hi2, hg2, hm2, ho2⟩ :=
    hj σ1 i1 (cfg.steps + 1) vmi1 hg1 hpc1 hmi1 (by rw [hm1]; exact h.code)
      (by rw [htgt]; decide) hi1
  have hmTail : σ2.mem = cfg.σ.mem := hm2.trans hm1
  have hpc2 : σ2.regs.get? PC = some 0x8000409c#64 := by
    have := obs_jr_pc ho2
    rwa [htgt] at this
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
  have hm2 : (⟨σ2, i2, cfg.steps + 1 + 1⟩ : Config).σ.mem = cfg.σ.mem := hmTail
  have hready : EpilogueReady g N A SL φf φc φf' φc' nf nc st' .normal sp r aRet m0
      ⟨σ2, i2, cfg.steps + 1 + 1⟩ :=
    { good := hg2
      tick := hi2
      pc := hpc2
      a0 := ha02
      minstret := ⟨vmi2, hmi2⟩
      spReg := hsp2
      code := by rw [hm2]; exact h.code
      out := hout2
      frames := h.frames
      closures := h.closures
      storeSurvives := by rw [hm2]; exact h.storeSurvives
      retval := fun v hv => by cases hv
      saved_ra := by rw [hm2]; exact h.saved_ra
      saved_s0 := by rw [hm2]; exact h.saved_s0
      saved_s1 := by rw [hm2]; exact h.saved_s1
      saved_s2 := by rw [hm2]; exact h.saved_s2
      saved_s3 := by rw [hm2]; exact h.saved_s3
      parentSp := h.parentSp
      frame := fun R hR he8 he9 he18 he19 he2 =>
        (htailFrame R hR).trans (h.frame R hR he8 he9 he18 he19 he2)
      memExtends := by rw [hm2]; exact h.memExtends
      memFrame := by rw [hm2]; exact h.memFrame
      spRoom := h.spRoom
      spHi := h.spHi
      spLo := h.spLo
      spWin := h.spWin
      spAlign := h.spAlign
      retAlign := h.retAlign }
  obtain ⟨cD, hstepsD, hExit⟩ := epilogueTail _ hready
  exact ⟨cD, (Steps.single hs1).trans ((Steps.single hs2).trans hstepsD), hExit⟩

#print axioms normalExitTail

end Vsa.Sim
