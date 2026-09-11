import Vsa.Sim.ClosureParamFoldLoop
import Vsa.Sim.ClosureScopeAllocator

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership ClosureParam

/-- The actual fresh scope supplies the initial owned parameter-loop state. -/
theorem ClosureScopePost.fold_entry
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {reserve : Nat} {st : Vsa.While.St} {env : Addr}
    {sp p closure names savedS6 : BitVec 64} {cd : ClosureData} {values : List Value}
    {m : Mem} {out : Array String} {after : Config}
    (h : ClosureScopePost g N M phiF phiC alloc exts shared (3 * values.length + reserve)
      st env sp p savedS6 values.length true m out after)
    (data : FoldData m N phiC shared sp closure names cd.params values)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (stackLo : SL.lo ≤ sp.toNat) (stackHi : sp.toNat + 1032 ≤ SL.hi)
    (positive : 0 < values.length)
    (closureReg : g Register.x21 = some closure)
    (present : EnvDefineSavedPresent g) :
    FoldLoopAt M N (pushFrameMap phiF st.store.frames.size p.toNat) phiC shared reserve
      (st.store.allocFrame (some env)).1 cd values st.store.frames.size
      sp p closure names savedS6 after (alloc.insert (.frame st.store.frames.size) p.toNat 32)
      ((p.toNat, 32) :: exts) shared 0 after := by
  have dataAfter : FoldData after.σ.mem N phiC shared sp closure names cd.params values :=
    data.transport h.agreement (fun _ hk => hk) (by
      intro k hlo hhi
      symm
      apply h.memoryFrame k
      · have := L.arena_stack; omega
      · omega
      · omega)
  have spReg : after.σ.regs.get? Register.x2 = some sp := by
    show gprGet after.σ 2 = some sp
    exact gholds_lookup _ h.regs (by rfl)
  have scopeReg : after.σ.regs.get? Register.x19 = some p := by
    show gprGet after.σ 19 = some p
    exact gholds_lookup _ h.regs (by rfl)
  have cursor : after.σ.regs.get? Register.x8 = some (sp + 240#64) := by
    show gprGet after.σ 8 = some (sp + 240#64)
    exact gholds_lookup _ h.regs (by rfl)
  have indexReg : after.σ.regs.get? Register.x15 = some 0#64 := by
    show gprGet after.σ 15 = some 0#64
    exact gholds_lookup _ h.regs (by rfl)
  have s6 : after.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 values.length <<< 3) := by
    show gprGet after.σ 22 = some (BitVec.ofNat 64 values.length <<< 3)
    exact gholds_lookup _ h.regs (by rfl)
  have shifted : BitVec.ofNat 64 values.length <<< 3 = BitVec.ofNat 64 (8 * values.length) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (show values.length < 2^64 by have := data.bound; omega)]
    rw [Nat.mul_comm]
  have closureAfter := (h.frame .x21 (by decide)).trans closureReg
  have presentAfter : EnvDefineSavedPresent (fun R => after.σ.regs.get? R) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cursor]; rfl
    · rw [h.frame .x9 (by decide)]; exact present.s1
    · rw [h.frame .x18 (by decide)]; exact present.s2
    · rw [scopeReg]; rfl
    · rw [h.frame .x20 (by decide)]; exact present.s4
    · rw [closureAfter]; rfl
    · rw [s6]; rfl
  refine
    { allocator := by simpa only [Nat.sub_zero, foldStore, List.take_zero, List.foldl_nil] using h.allocator
      data := dataAfter, includes := fun _ hk => hk, agreement := fun _ _ => rfl
      presence := fun _ b hb => ⟨b, hb⟩, memoryFrame := fun _ _ _ => rfl
      highStack := fun _ _ _ => rfl
      saved7Frame := fun _ _ _ => rfl
      indexBound := Nat.zero_le _, good := h.good, tick := h.tick
      pc := by simpa only [if_pos positive, ClosureEnvNewResume.exitPC, if_true] using h.pc
      minstret := h.minstret, spReg := spReg, scopeReg := scopeReg, closureReg := closureAfter
      cursor := fun _ => ?_, indexReg := by simpa using indexReg
      s6 := by simpa only [if_pos positive, shifted] using s6
      savedRead := h.savedS6 rfl, gp := h.gp, present := presentAfter, support := h.support
      emptyCapacity := fun _ => by rw [pushFrameMap_fresh]; exact h.capacity
      output := rfl, frame := fun _ _ => rfl }
  simpa only [Nat.mul_zero, Nat.add_zero, BitVec.ofNat_add, BitVec.ofNat_toNat] using cursor

/-- Bind the nonempty parameter list from the actual allocated scope through body entry. -/
theorem ClosureScopePost.bind_params
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {reserve : Nat} {st : Vsa.While.St} {env : Addr}
    {sp p closure names savedS6 : BitVec 64} {cd : ClosureData} {values : List Value}
    {m : Mem} {out : Array String} {before : Config}
    (h : ClosureScopePost g N M phiF phiC alloc exts shared (3 * values.length + reserve)
      st env sp p savedS6 values.length true m out before)
    (data : FoldData m N phiC shared sp closure names cd.params values)
    (L : AllocLedger A SL gpv headroom maxReq M) (placement : BindingArena A SL)
    (stack : StackOK SL sp 1088)
    (stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (stackWin : tohostAddr + 16 ≤ SL.lo) (stackHi : sp.toNat + 1032 ≤ SL.hi)
    (positive : 0 < values.length) (unique : StoreUnique st.store)
    (bounded : ∀ i (hi : i < values.length), ValueClosuresBounded st.store.closures.size values[i])
    (nameRequest : ∀ param ∈ cd.params, param.length + 1 ≤ maxReq)
    (growRequest : 48 * values.length ≤ maxReq)
    (closureReg : g Register.x21 = some closure) (present : EnvDefineSavedPresent g) :
    ∃ after, Steps before after ∧
      FoldLoopState M N (pushFrameMap phiF st.store.frames.size p.toNat) phiC shared reserve
        (st.store.allocFrame (some env)).1 cd values st.store.frames.size
        sp p closure names savedS6 before values.length after := by
  have context : FoldContext SL maxReq (pushFrameMap phiF st.store.frames.size p.toNat)
      (st.store.allocFrame (some env)).1 cd values st.store.frames.size sp p :=
    { arity := data.arity, bound := data.bound
      valid := by simp [Store.allocFrame]
      empty := by simp [Store.allocFrame]
      unique := unique.allocFrame st.store (some env)
      scopeAddr := (pushFrameMap_fresh phiF st.store.frames.size p.toNat).symm
      stack := stack, stackRam := stackRam, stackWin := stackWin, stackHi := stackHi
      names := nameRequest, growth := growRequest
      bounded := by simpa only [Store.allocFrame] using bounded }
  have initial := h.fold_entry data L (by have := stack.1; omega) stackHi positive closureReg present
  exact fold_run context L placement before ⟨_, _, _, initial⟩

end Vsa.Sim
