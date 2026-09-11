import Vsa.Sim.BlockEnvNewAllocator
import Vsa.Sim.ExecSeqAllocatorEntry

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open RuntimeOwnership

/-- The owned sequence and enclosing statement share the reached block entry. -/
structure BlockAllocatorPost
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (st : Vsa.While.St) (d env : Nat)
    (ss : List Stmt) (sp r aRet p : BitVec 64) (m0 : Mem) (after : Config) : Prop where
  entry : ExecSeqAllocatorEntry .blockBody after.σ.regs.get? N M
    (pushFrameMap phiF st.store.frames.size p.toNat) phiC
    (alloc.insert (.frame st.store.frames.size) p.toNat 32) ((p.toNat, 32) :: exts)
    shared credits ⟨(st.store.allocFrame (some env)).1, st.out⟩ d st.store.frames.size ss
    (sp - 176#64) aRet after.σ.mem after
  parent : Rows.BlockArmFrame g after.σ.regs.get? A SL phiF phiC
    (pushFrameMap phiF st.store.frames.size p.toNat) phiC st
    (st.store.allocFrame (some env)).1 sp r aRet m0 after.σ.mem
  agreement : AgreeP shared m0 after.σ.mem

/-- Resume the actual scope allocation into the owned block sequence. -/
theorem BlockEnvNewPost.resume
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {d env : Nat}
    {ss : List Stmt} {sp r aInterp aStmt aEnv aRet p : BitVec 64}
    {m0 ment : Mem} {arm returned : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (h : BlockEnvNewPost g N M phiF phiC alloc exts shared credits st d env ss
      sp r aInterp aStmt aEnv aRet p m0 ment arm returned) :
    ∃ after, Steps returned after ∧
      BlockAllocatorPost g N M phiF phiC alloc exts shared credits st d env ss
        sp r aRet p m0 after := by
  obtain ⟨after, base, steps, resume⟩ := blockArm_resume h.caller h.helper h.fresh
  have ast : StmtReprWithin after.σ.mem shared aStmt.toNat (.block ss) := by
    rw [resume.memory]; exact h.ast
  have blockReg : after.σ.regs.get? Register.x8 = some aStmt :=
    (resume.kept .x8 (by decide)).trans h.caller.s0
  have gp : after.σ.regs.get? Register.x3 = some gpv :=
    (resume.kept .x3 (by decide)).trans
      ((h.helper.ready.frame .x3 (by decide)).symm.trans h.gp)
  have suffix : ss ≠ [] → ∃ a, ExecSeqArrayAt after.σ.mem after.σ.regs.get? .blockBody a ∧
      SeqSuffixOwned after.σ.mem shared SL A (sp - 176#64) aRet d a ss := by
    intro nonempty
    obtain ⟨block, cursorBase, index, count, cursor⟩ := (resume.entry.ready nonempty).cursor.block
    have blockEq : block = aStmt := Option.some.inj (cursor.blockReg.symm.trans blockReg)
    subst block
    have countEq : count = ss.length := Option.some.inj (cursor.countRead.symm.trans resume.countRead)
    have indexEq : index = 0 := by have := cursor.remaining; omega
    subst index
    have baseEq : cursorBase.toNat = base := Option.some.inj (cursor.baseRead.symm.trans resume.baseRead)
    have reads : StmtArrayReprWithin after.σ.mem shared base ss.length ss := by
      cases ast with
      | block _ _ hb _ hc _ ha =>
        have hb' := Option.some.inj (hb.symm.trans resume.baseRead)
        have hc' := Option.some.inj (hc.symm.trans resume.countRead)
        simpa only [hb', hc'] using ha
    refine ⟨base, ?_, ⟨reads, resume.suffix⟩⟩
    simpa only [Nat.mul_zero, Nat.add_zero, baseEq] using
      ExecSeqArrayAt.blockBody cursor.blockReg cursor.indexReg cursor.baseRead
  have resources : ExecSeqBlockResources.At A SL shared (sp - 176#64) aRet after.σ.regs.get? := by
    have esp := EvalChildArm.esp_toNat sp resume.parent.spRoom
    have stackLo := resume.parent.stackLo
    have stackHi := resume.parent.stackHi
    have retAbove := resume.parent.retAbove
    have offArena : (sp - 176#64).toNat + 16 ≤ A.lo ∨ A.hi ≤ (sp - 176#64).toNat + 8 := by
      have := L.arena_stack
      omega
    obtain ⟨v20, reg20⟩ := h.caller.envset.1
    obtain ⟨v21, reg21⟩ := h.caller.envset.2
    exact .intro aStmt blockReg (ExecSeqBlockResources.of_header ast offArena (by omega)
      (Or.inl (by omega))
      ⟨v20, (resume.kept .x20 (by decide)).trans reg20⟩
      ⟨v21, (resume.kept .x21 (by decide)).trans reg21⟩)
  exact ⟨after, steps,
    { entry :=
        { entry := resume.entry
          allocator := by rw [resume.memory]; exact h.allocator
          suffix := suffix, closureResources := by intro impossible; cases impossible
          interpResources := by intro impossible; cases impossible
          blockResources := fun _ _ => resources, gp := gp }
      parent := resume.parent
      agreement := by rw [resume.memory]; exact h.agreement }⟩

/-- Execute block dispatch, scope allocation, and sequence setup once. -/
theorem blockAllocatorEntry_run
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {d env : Nat}
    {ss : List Stmt} {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (entry : ExecAllocatorEntry g N M phiF phiC alloc exts shared (credits + 1)
      st d env (.block ss) sp r aInterp aStmt aEnv aRet m0 before) :
    ∃ after p, Steps before after ∧
      BlockAllocatorPost g N M phiF phiC alloc exts shared credits st d env ss sp r aRet p m0 after := by
  obtain ⟨returned, p, ment, arm, steps, result⟩ := blockEnvNewAllocator_run L entry
  obtain ⟨after, resume, post⟩ := result.resume L
  exact ⟨after, p, steps.trans resume, post⟩

#print axioms BlockEnvNewPost.resume
#print axioms blockAllocatorEntry_run

end Vsa.Sim
