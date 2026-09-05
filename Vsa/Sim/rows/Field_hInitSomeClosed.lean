import Vsa.Sim.rows.InitSomeChildEntry
import Vsa.Sim.rows.InitSomeReturnReady

/-! # Present-initializer row

Compose the concrete dispatch, recursive child, and return jump. The only
induction hypothesis is the actual initializer statement's `ExecIH`.
-/

open LeanRV64DExecutable Sail Vsa
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.TermSimAssembly

namespace Vsa.Sim.ScaffoldRows

/-- Discharge the present-initializer residual using its supplied child IH. -/
theorem field_hInitSome : ∀ (st : Vsa.While.St) (d env : Nat) (s : Stmt)
    (st' : Vsa.While.St) (status : Status) (hS : ExecS st d env s st' status),
    InitSomeResid st d env s st' status hS := by
  intro st d env s st' status hS hIH
  intro cnd step body g N A SL φf φc sp r aInterp aStmt aOuter aRet m0 ment
  intro cfg hReady
  obtain ⟨cfgStage, hsStage, hStage⟩ :=
    initSome_to_stage g N A SL φf φc st d env s cnd step body
      sp r aInterp aStmt aOuter aRet m0 ment cfg hReady
  obtain ⟨cfgCall, hsCall, ⟨hLanding⟩⟩ :=
    initSome_stage_to_bodyPost g N A SL φf φc st d env s cnd step body
      sp r aInterp aStmt aOuter aRet m0 ment cfgStage hStage
  have hEntry := initSomeChildEntry_of_landing hLanding
  obtain ⟨cfgRet, hsChild, hChild⟩ :=
    hIH (fun R => cfgCall.σ.regs.get? R) N A SL φf φc
      (sp - 176#64) (0x80004258#64) aInterp hLanding.p aOuter aRet
      ment cfgCall hEntry
  have hBodies := StoreBodiesBound.afterExecS hS hEntry.stmt_bodies
    hEntry.store_bodies
  obtain ⟨cfgDone, hsReturn, hDone⟩ :=
    initSomeReturnReady hLanding hChild hS hBodies
  exact ⟨cfgDone, ((hsStage.trans hsCall).trans hsChild).trans hsReturn, hDone⟩

end Vsa.Sim.ScaffoldRows

#print axioms Vsa.Sim.ScaffoldRows.field_hInitSome
