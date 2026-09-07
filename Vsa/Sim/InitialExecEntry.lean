import Vsa.Sim.InitialExecCall
import Vsa.Sim.Code.FixedImage_Exec_stmt

namespace Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Alloc

variable {inp : BitVec 64} {stmts count aStmt : Nat}
  {before dispatch initialized after : Config} {s : Stmt} {ss : List Stmt}
  {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
  {D : RuntimeOwnership.InitialOwnershipData}

/-- Compose the actual null-call and argument-setup frames for a retained register. -/
theorem OwnedInitialExecFacts.loop_register
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) {R : Register} {v : RegisterType R}
    (hv : NotWrittenV R) (h1 : (Register.x1 == R) = false)
    (h10 : (Register.x10 == R) = false)
    (hw : ∀ n ∈ wrChain loopHeadArgSetupSeg, (gprReg n == R) = false)
    (hr : dispatch.σ.regs.get? R = some v) : after.σ.regs.get? R = some v :=
  (H.frame R (nullFrame_noise hv) hw h1).trans
    ((H.nullReturn.call.frame R hv h1 h10).trans hr)

/-- The current fixed text image supplies the first statement callee's code. -/
theorem OwnedInitialExecFacts.code
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft) :
    Code.Exec_stmtLoaded after.σ.mem := by
  have hi := F.interp_local
  subst inp
  exact (H.preservation.text_image F.text_image).Exec_stmtLoaded

/-- Assemble the reached entry once hereditary ground and source stack bounds
are supplied. These three inputs remain internal closure obligations. -/
theorem OwnedInitialExecFacts.execEntry
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft)
    (hground : ExecGround after.σ.mem LayoutInstance.stackSL A 0x87fffc50#64
      0x87fffca8#64 (BitVec.ofNat 64 aStmt).toNat s)
    (hbudget : StackOK LayoutInstance.stackSL 0x87fffc50#64
      (s.stackNeed + maxCallDepth * perCallBudget + 1088))
    (hbodies : Stmt.bodiesBound perCallBudget s = true) :
    ExecEntry after.σ.regs.get? N A LayoutInstance.stackSL phiF phiC initSt 0 0 s
      0x87fffc50#64 0x80004478#64 inp (BitVec.ofNat 64 aStmt)
      (BitVec.ofNat 64 (phiF 0)) 0x87fffca8#64 after.σ.mem after := by
  have h8 : after.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 stmts) :=
    H.loop_register (by decide) (by decide) (by decide) (by decide)
      (gholds_lookup _ H.nullReturn.entered.keep
        (show lookupG 8 _ = some (BitVec.ofNat 64 stmts) from rfl))
  have h18 : after.σ.regs.get? Register.x18 =
      some (BitVec.ofNat 64 stmts + (BitVec.ofNat 64 count <<< 3)) :=
    H.loop_register (by decide) (by decide) (by decide) (by decide)
      (gholds_lookup _ H.nullReturn.entered.keep
        (show lookupG 18 _ = some (BitVec.ofNat 64 stmts + (BitVec.ofNat 64 count <<< 3)) from rfl))
  have h19 : after.σ.regs.get? Register.x19 = some (3#64 : BitVec 64) :=
    H.loop_register (by decide) (by decide) (by decide) (by decide)
      (gholds_lookup _ H.nullReturn.entered.keep (show lookupG 19 _ = some 3#64 from rfl))
  have h20 : after.σ.regs.get? Register.x20 = some (1#64 : BitVec 64) :=
    H.loop_register (by decide) (by decide) (by decide) (by decide)
      (gholds_lookup _ H.nullReturn.entered.keep (show lookupG 20 _ = some 1#64 from rfl))
  have h9 : after.σ.regs.get? Register.x9 = some (BitVec.ofNat 64 aStmt) :=
    gholds_lookup _ H.arguments (show lookupG 9 _ = some (BitVec.ofNat 64 aStmt) from rfl)
  exact
    { good := H.good
      tick := H.tick
      pc := H.pc
      a0 := gholds_lookup _ H.arguments (show lookupG 10 _ = some inp from rfl)
      a1 := gholds_lookup _ H.arguments (show lookupG 11 _ = some (BitVec.ofNat 64 aStmt) from rfl)
      a2 := gholds_lookup _ H.arguments (show lookupG 12 _ = some (BitVec.ofNat 64 (phiF 0)) from rfl)
      envPtr := rfl
      a3 := gholds_lookup _ H.arguments (show lookupG 13 _ = some 0x87fffca8#64 from rfl)
      ra := gholds_lookup _ H.arguments (show lookupG 1 _ = some 0x80004478#64 from rfl)
      ra_align := by decide
      spReg := gholds_lookup _ H.arguments (show lookupG 2 _ = some 0x87fffc50#64 from rfl)
      stackOK := by unfold StackOK; decide
      stackBudget := hbudget
      stmt_bodies := hbodies
      store_bodies := by
        intro a cd hcd
        simp [initSt] at hcd
      minstret := H.minstret
      mem := rfl
      code := H.code F
      stmt := H.stmt
      store := H.store
      env_valid := EnvValid.init
      store_survives := H.store_survives_stack
      out := H.out F
      frame := fun _ _ => rfl
      code_stack_disjoint := by decide
      stack_ram := by decide
      stack_win := by decide
      stmt_stack_disjoint := by
        have ht := H.tag.stack_disjoint (by decide)
        rcases ht with ht | ht
        · exact Or.inl ht
        · right; exact Nat.le_trans (by decide) ht
      stmt_ram := ⟨H.tag.ram_lo, H.tag.ram_hi⟩
      stmt_win := H.tag.htif
      spill_defined := ⟨⟨_, h8⟩, ⟨_, h9⟩, ⟨_, h18⟩, ⟨_, h19⟩⟩
      envset_defined := ⟨⟨_, h20⟩, ⟨_, H.preservation.return_latch⟩⟩
      ground := hground }

#print axioms OwnedInitialExecFacts.loop_register
#print axioms OwnedInitialExecFacts.code
#print axioms OwnedInitialExecFacts.execEntry
end Vsa.Sim
