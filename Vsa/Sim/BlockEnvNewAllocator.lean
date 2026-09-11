import Vsa.Sim.EnvNewAllocator
import Vsa.Sim.AllocatorEntry
import Vsa.Sim.rows.BlockArmEnvNew

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa Vsa.Machine Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open RuntimeOwnership Code

/-- The block's actual scope allocation retains its caller and owned store. -/
structure BlockEnvNewPost
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (st : Vsa.While.St) (d env : Nat)
    (ss : List Stmt) (sp r aInterp aStmt aEnv aRet p : BitVec 64)
    (m0 ment : Mem) (arm returned : Config) : Prop where
  caller : ArmState execArmBlock (.block ss) g N A SL phiF phiC st d env
    sp r aInterp aStmt aEnv aRet m0 ment arm
  helper : blockEnvNewCall.Return arm.σ.regs.get? p (sp - 176#64) aStmt aInterp aRet aEnv
    ment returned.σ.mem
    (fun k => (A.lo ≤ k ∧ k < A.hi) ∨ (SL.lo ≤ k ∧ k < (sp - 176#64).toNat))
    arm.σ.sailOutput returned
  fresh : EnvNewFresh N A SL phiF phiC st env p
    (pushFrameMap phiF st.store.frames.size p.toNat) returned.σ.mem
  allocator : RuntimeAllocatorState M N (pushFrameMap phiF st.store.frames.size p.toNat) phiC
    (alloc.insert (.frame st.store.frames.size) p.toNat 32) ((p.toNat, 32) :: exts)
    shared credits (st.store.allocFrame (some env)).1 returned.σ.mem
  agreement : AgreeP shared m0 returned.σ.mem
  ast : StmtReprWithin returned.σ.mem shared aStmt.toNat (.block ss)
  gp : returned.σ.regs.get? Register.x3 = some gpv

/-- Dispatch the block and allocate its scope from the caller's reserve. -/
theorem blockEnvNewAllocator_run
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {d env : Nat}
    {ss : List Stmt} {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (entry : ExecAllocatorEntry g N M phiF phiC alloc exts shared (credits + 1)
      st d env (.block ss) sp r aInterp aStmt aEnv aRet m0 before) :
    ∃ returned p ment arm, Steps before returned ∧
      BlockEnvNewPost g N M phiF phiC alloc exts shared credits st d env ss
        sp r aInterp aStmt aEnv aRet p m0 ment arm returned := by
  obtain ⟨cA, ment, hsA, hA⟩ := armState_of_entry_kind 2 execArmBlock (by decide) rfl (by decide)
    (fun _ _ h => by cases h with | block hk _ _ _ => exact hk) entry.entry
  have allocator0 : RuntimeAllocatorState M N phiF phiC alloc exts shared (credits + 1)
      st.store m0 := by rw [← entry.entry.mem]; exact entry.allocator
  have stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m0[k]? = ment[k]? := by
    intro k hk
    exact (hA.mem_frame k (by have := hA.spSL; omega)).symm
  have allocatorArm := allocator0.after_stack L stackFrame
  have sharedArm : AgreeP shared m0 ment := fun k hk =>
    stackFrame k ((allocator0.runtime L).shared_off_stack hk)
  have ghostGp : g Register.x3 = some gpv :=
    (entry.entry.frame .x3 (by decide)).symm.trans entry.gp
  have armGp : cA.σ.regs.get? Register.x3 = some gpv :=
    (hA.frame .x3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ghostGp
  obtain ⟨cP, hsP, hP⟩ := blockEnvNewCall.parked_of_armState blockEnvNewCall_cert hA []
    (by change ChainOK 0x8000418c#64 [2, 8, 9, 18, 19] blockEnvNewSeg; decide) rfl
    (by change KeysOK [10, 2, 8, 9, 18, 19]; decide)
    (by change ∀ n ∈ [10, 2, 8, 9, 18, 19], n ≠ 1; decide)
    (by show Exec_stmtLoaded (writeLog ment []); exact hA.code)
    (blockEnvNew_facts ment _ _ _ _ _ hA.code)
  have hreg : ∀ n w, lookupG n (blockEnvNewCall.out
      (EvalChildArm.regs (sp - 176#64) aStmt aInterp aRet aEnv) []).regs = some w →
      gprGet cP.σ n = some w := fun _ _ h => gholds_lookup _ hP.regs h
  have hsext : (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 := by decide
  have callEntry : EnvNewEntryState cP.σ.regs.get? N A SL phiF phiC st env
      (sp - 176#64) (aEnv + sign_extend (m := 64) (0#12)) blockEnvNewCall.retPC
      ment cA.σ.sailOutput cP :=
    { good := hP.good, tick := hP.tick, pc := hP.pc
      a0 := hreg 10 _ rfl, ra := hP.ra, ra_align := blockEnvNewCall_cert.ret_align
      sp := hreg 2 _ rfl, minstret := hP.minstret, mem := hP.mem, out := hP.out
      frame := fun _ _ => rfl
      facts :=
        { text := hA.ground.eval_call.image.text, store := hA.store
          store_survives := hA.store_survives, env_valid := hA.env_valid
          env_addr := by rw [hsext, BitVec.add_zero]; exact hA.env_addr
          stack := hA.frameFacts.espStack, stack_ram := hA.stack_ram
          stack_win := hA.stack_win, stack_bytes := hA.ground.stack_bytes
          arena_stack := hA.frameFacts.espArena } }
  obtain ⟨cR, p, hsR, result⟩ := envNewAllocator_run L callEntry allocatorArm
    ((hP.frame .x3 (by decide)).trans armGp) ⟨aStmt, hreg 8 _ rfl⟩
  have hRet : blockEnvNewCall.Return cA.σ.regs.get? p (sp - 176#64) aStmt aInterp aRet aEnv
      ment cR.σ.mem
      (fun k => (A.lo ≤ k ∧ k < A.hi) ∨ (SL.lo ≤ k ∧ k < (sp - 176#64).toNat))
      cA.σ.sailOutput cR :=
    { ready :=
        { good := result.exit.good, tick := result.exit.tick, pc := result.exit.pc
          a0 := result.result, ra := result.exit.ra, minstret := result.exit.minstret
          mem := rfl, out := result.exit.out, sp := result.exit.sp
          s0 := (result.exit.frame .x8 (by decide)).trans (hreg 8 _ rfl)
          s1 := (result.exit.frame .x9 (by decide)).trans (hreg 9 _ rfl)
          s2 := (result.exit.frame .x18 (by decide)).trans (hreg 18 _ rfl)
          s3 := (result.exit.frame .x19 (by decide)).trans (hreg 19 _ rfl)
          frame := fun R hR => (result.exit.frame R hR).trans (hP.frame R hR) }
      mem_frame := fun k hk => result.exit.mem_frame k
        (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h))
      mem_extends := result.exit.mem_extends }
  have agreement : AgreeP shared m0 cR.σ.mem :=
    fun k hk => (sharedArm k hk).trans (result.agreement k hk)
  refine ⟨cR, p, ment, cA, hsA.trans (hsP.trans hsR),
    { caller := hA, helper := hRet, fresh := result.fresh, allocator := result.allocator
      agreement := agreement, ast := ?_, gp := result.gp }⟩
  have ast : StmtReprWithin m0 shared aStmt.toNat (.block ss) := by
    rw [← entry.entry.mem]; exact entry.ast
  exact ast.transport agreement

#print axioms blockEnvNewAllocator_run

end Vsa.Sim
