import Vsa.Sim.EnvDefineScanHit

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

private theorem some_default {α : Type} (x : Option α) (fallback : α)
    (present : x.isSome = true) : some (x.getD fallback) = x := by
  cases x <;> simp_all

/-- The epilogue's exact saved words restore the caller's present registers. -/
theorem EnvDefineEpilogueExactPost.restored
    {g : (R : Register) → Option (RegisterType R)} {sp r : BitVec 64} {m : Mem} {after : Config}
    (h : EnvDefineEpilogueExactPost sp (envDefineSaved g r) m after)
    (present : EnvDefineSavedPresent g) :
    ∀ R, EnvDefineRestored R = true → after.σ.regs.get? R = g R := by
  intro R restored
  simp only [EnvDefineRestored, Bool.or_eq_true, beq_iff_eq] at restored
  rcases restored with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
  · rw [h.s0, envDefineSaved_ne g r (by decide)]; exact some_default _ _ present.s0
  · rw [h.s1, envDefineSaved_ne g r (by decide)]; exact some_default _ _ present.s1
  · rw [h.s2, envDefineSaved_ne g r (by decide)]; exact some_default _ _ present.s2
  · rw [h.s3, envDefineSaved_ne g r (by decide)]; exact some_default _ _ present.s3
  · rw [h.s4, envDefineSaved_ne g r (by decide)]; exact some_default _ _ present.s4
  · rw [h.s5, envDefineSaved_ne g r (by decide)]; exact some_default _ _ present.s5
  · rw [h.s6, envDefineSaved_ne g r (by decide)]; exact some_default _ _ present.s6

/-- The helper's ordinary return and owned allocator refer to the same defined store. -/
structure EnvDefineAllocatorReturn
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (st : Vsa.While.St) (env : Addr)
    (name : String) (v : Value) (sp r : BitVec 64) (m : Mem) (out : Array String)
    (after : Config) : Prop where
  exit : EnvDefineReturnState g N A SL phiF phiC st env name v sp r m out after
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits
    (st.store.define env name v) after.σ.mem
  agreement : AgreeP shared m after.σ.mem

/-- Finish the owned existing-name route from the actual prologue exit to the caller's return. -/
theorem EnvDefinePrologueAllocatorPost.return_hit
    {g : (R : Register) → Option (RegisterType R)}
    {esp aEnv aName pv r : BitVec 64} {m : Mem} {out : Array String}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St}
    {target : Addr} {valid : target < st.store.frames.size} {name : String} {v : Value} {before : Config}
    (h : EnvDefinePrologueAllocatorPost g esp aEnv aName pv r m out N M
      phiF phiC alloc exts shared credits st.store target valid name v before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (envAddr : aEnv.toNat = phiF target) (stack : StackOK SL esp 1088)
    (source : RetSlotGeom SL (esp - 64#64) pv)
    (present : EnvDefineSavedPresent g) (ghostSp : g Register.x2 = some esp)
    (retAlign : r.toNat % 4 = 0) (unique : FrameUnique st.store.frames[target])
    (bounded : ValueClosuresBounded st.store.closures.size v)
    (hasName : ∃ i, ∃ hi : i < st.store.frames[target].vars.length, st.store.frames[target].vars[i].1 = name) :
    ∃ after, Steps before after ∧
      EnvDefineAllocatorReturn g N M phiF phiC alloc exts shared credits
        st target name v esp r m out after := by
  have positive : 0 < st.store.frames[target].vars.length := by
    obtain ⟨i, hi, _⟩ := hasName; omega
  obtain ⟨scanned, pn, scanSteps, scan⟩ := h.scan L envAddr stack positive
  apply scan.scanned.resolve
  · intro i hi cmp hit
    have frameHi : (esp - 64#64).toNat + 64 ≤ SL.hi := by
      obtain ⟨lo, top, _⟩ := stack
      rw [sp_sub64_toNat esp (by omega)]; omega
    obtain ⟨after, dst, tailSteps, tail⟩ := scan.hit_return hit L envAddr source frameHi unique bounded
    have result := tail.result
    have returned := result.exit.returned
    have memoryFrame : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat) →
        after.σ.mem[k]? = m[k]? := by
      intro k arenaOff stackOff
      have dstArena := result.destination
      obtain ⟨dstLo, dstHi⟩ := dstArena
      have wholeStack := stack
      obtain ⟨lo, _, _⟩ := wholeStack
      exact (result.outside k (by unfold SetOutside; omega)).symm.trans
        (h.outside k (by omega)).symm
    have core : EnvDefineReturnCore g N A SL phiF phiC st target name v esp r m after :=
      { good := returned.good, tick := returned.tick
        pc := by rw [returned.pc, envDefineSaved_x1, Option.getD_some, bitvec_update_self r retAlign]
        ra := by rw [returned.ra, envDefineSaved_x1]; rfl
        sp := by rw [returned.spReg, BitVec.sub_add_cancel]
        minstret := returned.good.minstret, restored := returned.restored present
        store := result.allocator.repr
        store_survives := fun _ agreement => (result.allocator.after_stack L agreement).repr
        mem_frame := memoryFrame, mem_extends := h.presence.trans result.presence }
    have residuals : EnvDefineReturnResiduals g out after :=
      { out := tail.kept.out
        rest := by
          intro R abi notRestored notSp
          obtain ⟨keep, prologueKeep, notS0, notS1, notS6⟩ := envDefineRest_facts R abi notRestored notSp
          apply (tail.kept.keep R keep).trans
          change scanned.σ.regs.get? R = g R
          rw [hit.frame.abi R abi, envDefineScanGhost_ne _ _ _ notS0 notS1,
            envDefineScanBaseGhost_ne _ _ notS6]
          exact h.frame R prologueKeep
        a0 := ⟨cmp, (tail.kept.keep .x10 (by decide)).trans hit.resultReg⟩ }
    refine ⟨after, scanSteps.trans tailSteps,
      { exit := core.toReturn ghostSp residuals, allocator := result.allocator
        agreement := ?_ }⟩
    exact fun k hk => (h.agreement k hk).trans (result.exit.shared_agree k hk)
  · intro _ _ miss
    obtain ⟨i, hi, nameEq⟩ := hasName
    exact False.elim (miss.missing i hi nameEq)

#print axioms EnvDefineEpilogueExactPost.restored
#print axioms EnvDefinePrologueAllocatorPost.return_hit

end Vsa.Sim
