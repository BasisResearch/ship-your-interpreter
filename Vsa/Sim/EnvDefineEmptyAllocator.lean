import Vsa.Sim.EnvDefineEmptyDispatch
import Vsa.Sim.EnvDefineGrowAllocator
import Vsa.Sim.EnvDefinePrologueAllocator

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- An empty owned frame executes initial array allocation and reaches the append entry. -/
theorem EnvDefinePrologueAllocatorPost.empty_grow
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {valid : env < st.store.frames.size}
    {name : String} {v : Value} {esp aEnv aName pv r : BitVec 64} {m : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {exts : List Extent}
    {alloc : Allocations} {shared : Nat → Prop} {credits : Nat} {before : Config}
    (h : EnvDefinePrologueAllocatorPost g esp aEnv aName pv r m out N M
      phiF phiC alloc exts shared (credits + 2) st.store env valid name v before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (geometry : EnvDefineGrowGeometry A SL esp pv)
    (envAddr : aEnv.toNat = phiF env) (ghostSp : g Register.x2 = some esp)
    (retAlign : r.toNat % 4 = 0)
    (emptyCapacity : read32 before.σ.mem (phiF env + 4) = some 0) :
    ∃ after exts' cap' pn' pvals', Steps before after ∧
      EnvDefineAppendAllocatorPost g N A SL phiF phiC st env name v esp aEnv aName pv r m out M
        ((alloc.insert (.names env) pn' (8 * cap')).insert (.values env) pvals' (24 * cap'))
        exts' shared credits cap' after ∧ AgreeP shared m after.σ.mem := by
  obtain ⟨arrays, fields⟩ := (h.allocator.heap.store.frames env valid).arrays
  have capZero := Option.some.inj (fields.capRead.symm.trans emptyCapacity)
  have countZero : st.store.frames[env].vars.length = 0 := by
    have := fields.bound; omega
  have namesZero : arrays.names = 0 := by
    rcases fields.names with empty | live
    · exact empty.2
    · have := live.1; omega
  have valuesZero : arrays.values = 0 := by
    rcases fields.values with empty | live
    · exact empty.2
    · have := live.1; omega
  have namesRead : read64 before.σ.mem (phiF env + 8) = some 0 := by
    rw [← namesZero]; exact fields.namesRead
  have valuesRead : read64 before.σ.mem (phiF env + 16) = some 0 := by
    rw [← valuesZero]; exact fields.valuesRead
  obtain ⟨envArena, envAlign⟩ := h.allocator.repr.frames_arena env valid
  have envGeom : EnvRecordGeom aEnv := by
    have arenaRam := L.arena_ram
    have arenaHtif := L.arena_htif
    have image := h.support.image.arena
    change A.lo ≤ phiF env ∧ phiF env + 32 ≤ A.hi at envArena
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals rw [envAddr]
    · omega
    · omega
    · omega
    · exact envAlign
    · omega
  obtain ⟨grown, dispatchSteps, D⟩ := EnvDefineEmptyDispatch.run
    (names := 0#64)
    { good := h.good, tick := h.tick, pc := h.pc, minstret := h.good.minstret
      envReg := h.a0, countReg := by have hs := h.s3; rwa [countZero] at hs
      geometry := envGeom
      capacity := by rw [envAddr]; exact emptyCapacity
      namesRead := by rw [envAddr]; exact namesRead
      code := h.support.image.text.Env_defineLoaded }
  have F : EnvDefineMissFacts g N A SL phiF phiC st env name v esp aEnv aName pv r m
      exts before.σ.mem 0 :=
    { ra_align := retAlign, g_sp := ghostSp, env_lt := valid, env_addr := envAddr
      text := h.support.image.text, store := h.allocator.repr
      owned := ⟨alloc, shared, InitialReadableByte, InitialWriteByte SL, h.allocator.heap,
        (fun k lo hi => Or.inr ⟨lo, hi⟩), h.owned, h.nameOwned⟩
      word := h.word, cap_read := emptyCapacity
      names_align := h.allocator.arrays.namesAligned env valid
      vals_align := h.allocator.arrays.valuesAligned env valid
      miss := fun _ hi => by omega
      mem_agree := fun k _ off => (h.outside k (by have := geometry.stack.1; omega)).symm
      mem_extends := h.presence }
  have R : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M exts before.σ.mem valid grown := by
    have stackLo := geometry.stack.1
    have stackHi := geometry.stack.2.1
    have stackAlign := geometry.stack.2.2
    have headroomBound := L.headroom_le
    have sp64 := sp_sub64_toNat esp (by omega)
    refine
      { good := D.good, tick := D.tick, mem := D.memory, out := D.output.trans h.output
        minstret := D.minstret, sp := (D.frame _ (by decide)).trans h.sp
        gp := (D.frame _ (by decide)).trans h.gp
        s2 := (D.frame _ (by decide)).trans h.s2
        s3 := (D.frame _ (by decide)).trans h.s3
        s4 := (D.frame _ (by decide)).trans h.s4
        s5 := (D.frame _ (by decide)).trans h.s5
        rest := ?_, saved := h.saved.of_mem_eq D.memory
        stack := ?_, ainv := ?_ }
    · intro reg abi restored notSp
      obtain ⟨_, kept, _, _, notS6⟩ := envDefineRest_facts reg abi restored notSp
      exact (D.frame reg (KeepButS6.of abi notS6)).trans (h.frame reg kept)
    · refine ⟨?_, ?_, ?_⟩ <;> rw [sp64] <;> omega
    · exact h.allocator.ainv grown.σ ((D.frame _ (by decide)).trans h.gp) D.memory
  obtain ⟨after, exts', cap', pn', pvals', steps, post, sharedAgreement⟩ :=
    envDefineGrowAllocator_run g N A SL phiF phiC st env name v esp aEnv aName pv r m out M
      exts before.σ.mem alloc shared credits 0 0 0 grown geometry L F R
      h.allocator h.owned h.nameOwned h.support countZero namesRead valuesRead (by omega)
      (.init rfl D.pc D.capacityReg D.requestReg) D.namesReg
  exact ⟨after, exts', cap', pn', pvals', dispatchSteps.trans steps, post,
    fun k hk => (h.agreement k hk).trans (sharedAgreement k hk)⟩

#print axioms EnvDefinePrologueAllocatorPost.empty_grow

end Vsa.Sim
