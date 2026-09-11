import Vsa.Sim.SeqInterpHead
import Vsa.Sim.SeqInterpArgs
import Vsa.Sim.InitialNullRun

namespace Vsa.Sim.SeqInterpDispatch

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.Machine Vsa.Alloc Vsa.RuntimeRepr Vsa.While

/-- Read geometry and separation of saved words from the initialized result slot. -/
structure Geometry (sp cursor interp : BitVec 64) : Prop where
  head : SeqInterpHead.Geometry sp cursor
  args : SeqInterpArgs.Geometry sp interp
  result : NullRegion (sp + 88#64)
  savedOffRet : sp.toNat + 16 ≤ (sp + 88#64).toNat
  interpOffRet : interp.toNat + 8 ≤ (sp + 88#64).toNat ∨
    (sp + 88#64).toNat + 24 ≤ interp.toNat
  codeOffRet : (sp + 88#64).toNat + 24 ≤ 0x800043ec ∨
    0x80004588 ≤ (sp + 88#64).toNat

/-- The actual statement entry, including the initialized value and exact write frame. -/
structure Post (sp stmt interp env : BitVec 64) (N : NativeAddrs)
    (phiC : Addr → Nat) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x80003fe0#64
  ra : after.σ.regs.get? Register.x1 = some 0x80004478#64
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  args : GHolds after.σ [(10, interp), (11, stmt), (12, env), (13, sp + 88#64),
    (2, sp), (9, stmt)]
  value : ValueRepr after.σ.mem N phiC (sp + 88#64).toNat .null
  outside : ∀ k, ¬ ((sp + 88#64).toNat ≤ k ∧ k < (sp + 88#64).toNat + 24) →
    before.σ.mem[k]? = after.σ.mem[k]?
  presence : MemExtends before.σ.mem after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, SeqInterpHead.keep R = true →
    after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute loop-head dispatch, result initialization, and statement argument setup. -/
theorem run (sp cursor stmt interp env : BitVec 64) (N : NativeAddrs)
    (phiC : Addr → Nat) (before : Config) (G : Geometry sp cursor interp)
    (good : GoodState before.σ) (tick : before.tick < 2)
    (pc : before.σ.regs.get? Register.PC = some 0x8000448c#64)
    (minstret : ∃ w, before.σ.regs.get? Register.minstret = some w)
    (registers : GHolds before.σ (loopHeadDispatchL sp cursor))
    (code : Code.Interp_runLoaded before.σ.mem)
    (nullCode : Code.Value_nullLoaded before.σ.mem)
    (script : read64 before.σ.mem (sp.toNat + 8) = some 0)
    (statement : read64 before.σ.mem cursor.toNat = some stmt.toNat)
    (saved : read64 before.σ.mem sp.toNat = some interp.toNat)
    (environment : read64 before.σ.mem interp.toNat = some env.toNat) :
    ∃ after, Steps before after ∧ Post sp stmt interp env N phiC before after := by
  obtain ⟨head, headRun, H⟩ := SeqInterpHead.run sp cursor stmt before G.head
    good tick pc minstret registers code script statement
  obtain ⟨spReg, _, stmtReg, _⟩ := H.registers
  obtain ⟨initialized, I⟩ := interpValueNull_run head sp N phiC H.good H.pc spReg
    H.minstret H.tick (H.memory.symm ▸ code) (H.memory.symm ▸ nullCode) G.result
  have word (a : Nat) (offRet : a + 8 ≤ (sp + 88#64).toNat ∨
      (sp + 88#64).toNat + 24 ≤ a) :
      read64 initialized.σ.mem a = read64 before.σ.mem a := by
    have agreement : AgreeP (fun k => a ≤ k ∧ k < a + 8) head.σ.mem initialized.σ.mem := by
      intro k hk
      exact I.outside k (by omega)
    exact (read64_agreeP agreement (fun k hk => ⟨by omega, by omega⟩)).symm.trans
      (congrArg (fun m => read64 m a) H.memory)
  have code' : Code.Interp_runLoaded initialized.σ.mem := by
    apply loaded_interp_run_of_agree head.σ.mem initialized.σ.mem (H.memory.symm ▸ code)
    intro k hlo hhi
    exact I.outside k (by have := G.codeOffRet; omega)
  have regs : GHolds initialized.σ (loopHeadArgSetupL sp stmt) :=
    ⟨(I.frame Register.x2 (by decide) (by decide) (by decide)).trans spReg,
      (I.frame Register.x9 (by decide) (by decide) (by decide)).trans stmtReg, trivial⟩
  obtain ⟨after, argsRun, A⟩ := SeqInterpArgs.run sp stmt interp env initialized G.args
    I.good I.tick I.pc I.minstret regs code'
    ((word _ (Or.inl (by have := G.savedOffRet; omega))).trans saved)
    ((word _ G.interpOffRet).trans environment)
  refine ⟨after, headRun.trans (I.run.trans argsRun),
    { good := A.good, tick := A.tick, pc := A.pc, ra := A.ra, minstret := A.minstret
      args := A.args, value := A.memory.symm ▸ I.value, outside := ?_, presence := ?_
      output := A.output.trans (I.output.trans H.output), frame := ?_ }⟩
  · intro k hk
    exact (congrArg (fun m : Mem => m[k]?) H.memory).symm.trans
      ((I.outside k hk).trans (congrArg (fun m : Mem => m[k]?) A.memory.symm))
  · exact A.memory.symm ▸ H.memory ▸ I.mem_extends
  · intro R hR
    have abi : AbiPreserved R = true := by
      cases h : AbiPreserved R <;> simp_all [SeqInterpHead.keep]
    have notWritten : NotWrittenV R := by
      unfold NotWrittenV
      repeat' apply And.intro
      all_goals exact abiPreserved_ne abi (by decide)
    exact (A.frame R abi).trans ((I.frame R notWritten
      (abiPreserved_ne abi (by decide)) (abiPreserved_ne abi (by decide))).trans (H.frame R hR))

#print axioms run

end Vsa.Sim.SeqInterpDispatch
