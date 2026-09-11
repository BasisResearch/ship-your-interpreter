import Vsa.Sim.ClosureParamFoldStep
import Vsa.Sim.ClosureParamFoldStore

namespace Vsa.Sim.ClosureParam

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership Vsa.Logic

/-- Fixed source and stack facts for binding the closure's parameter list. -/
structure FoldContext (SL : StackLayout) (maxReq : Nat) (phiF : Addr → Nat)
    (store : Store) (cd : ClosureData) (values : List Value) (target : Addr)
    (sp scope : BitVec 64) : Prop where
  arity : values.length = cd.params.length
  bound : values.length ≤ 32
  valid : target < store.frames.size
  empty : store.frames[target].vars.length = 0
  unique : StoreUnique store
  scopeAddr : scope.toNat = phiF target
  stack : StackOK SL sp 1088
  stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stackWin : tohostAddr + 16 ≤ SL.lo
  stackHi : sp.toNat + 1032 ≤ SL.hi
  names : ∀ param ∈ cd.params, param.length + 1 ≤ maxReq
  growth : 48 * values.length ≤ maxReq
  bounded : ∀ i (hi : i < values.length), ValueClosuresBounded store.closures.size values[i]

/-- One selected runtime at the exact source prefix, including the final body entry. -/
structure FoldLoopAt
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (N : NativeAddrs) (phiF phiC : Addr → Nat)
    (entryShared : Nat → Prop) (reserve : Nat) (store : Store) (cd : ClosureData) (values : List Value)
    (target : Addr) (sp scope closure names savedS6 : BitVec 64) (origin : Config)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop) (index : Nat) (before : Config) : Prop where
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared
    (3 * (values.length - index) + reserve) (foldStore store cd values target index) before.σ.mem
  data : FoldData before.σ.mem N phiC shared sp closure names cd.params values
  includes : ∀ k, entryShared k → shared k
  agreement : AgreeP entryShared origin.σ.mem before.σ.mem
  presence : MemExtends origin.σ.mem before.σ.mem
  memoryFrame : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < SL.hi) →
    origin.σ.mem[k]? = before.σ.mem[k]?
  highStack : ∀ k, sp.toNat + 1032 ≤ k → k < SL.hi →
    origin.σ.mem[k]? = before.σ.mem[k]?
  saved7Frame : ∀ k, sp.toNat + 1016 ≤ k → k < sp.toNat + 1024 →
    origin.σ.mem[k]? = before.σ.mem[k]?
  indexBound : index ≤ values.length
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some (if index < values.length then 0x800032dc#64 else 0x80003324#64)
  minstret : ∃ w, before.σ.regs.get? Register.minstret = some w
  spReg : before.σ.regs.get? Register.x2 = some sp
  scopeReg : before.σ.regs.get? Register.x19 = some scope
  closureReg : before.σ.regs.get? Register.x21 = some closure
  cursor : index < values.length → before.σ.regs.get? Register.x8 =
    some (BitVec.ofNat 64 (sp.toNat + 240 + 24 * index))
  indexReg : before.σ.regs.get? Register.x15 = some (BitVec.ofNat 64 (8 * index))
  s6 : before.σ.regs.get? Register.x22 = some
    (if index < values.length then BitVec.ofNat 64 (8 * values.length) else savedS6)
  savedRead : read64 before.σ.mem (sp.toNat + 1024) = some savedS6.toNat
  gp : before.σ.regs.get? Register.x3 = some gpv
  present : EnvDefineSavedPresent (fun R => before.σ.regs.get? R)
  support : EvalCallSupport before.σ.mem SL A sp
  emptyCapacity : index = 0 → read32 before.σ.mem (phiF target + 4) = some 0
  output : before.σ.sailOutput = origin.σ.sailOutput
  frame : ∀ R, ClosureEnvNewResume.keep R = true →
    before.σ.regs.get? R = origin.σ.regs.get? R

variable {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
  {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
  {phiF phiC : Addr → Nat} {entryShared : Nat → Prop} {reserve : Nat}
  {store : Store} {cd : ClosureData} {values : List Value} {target : Addr}
  {sp scope closure names savedS6 : BitVec 64} {origin before : Config}

/-- Advance the source prefix and the actual owned loop state together. -/
theorem FoldLoopAt.step
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {index : Nat}
    (h : FoldLoopAt M N phiF phiC entryShared reserve store cd values target
      sp scope closure names savedS6 origin alloc exts shared index before)
    (context : FoldContext SL maxReq phiF store cd values target sp scope)
    (L : AllocLedger A SL gpv headroom maxReq M) (placement : BindingArena A SL)
    (hi : index < values.length) :
    ∃ after alloc' exts' shared', Steps before after ∧
      FoldLoopAt M N phiF phiC entryShared reserve store cd values target
        sp scope closure names savedS6 origin alloc' exts' shared' (index + 1) after := by
  have valid : target < (foldStore store cd values target index).frames.size := by
    rw [(fold_sizes store cd values target index).1]; exact context.valid
  have counts := fold_count store cd values target index context.arity h.indexBound context.valid context.empty
  have nextStore := fold_next store cd values target index context.arity hi
  have budget : 3 * (values.length - index) + reserve =
      (3 * (values.length - (index + 1)) + reserve) + 3 := by omega
  have input : FoldStepInput M N phiF phiC alloc exts shared
      (3 * (values.length - (index + 1)) + reserve)
      ⟨foldStore store cd values target index, Vsa.Machine.output origin.σ⟩ target
      sp scope closure names savedS6 cd.params values index before :=
    { allocator := by rw [← budget]; exact h.allocator
      data := h.data, indexLt := hi, good := h.good, tick := h.tick
      pc := by simpa only [if_pos hi] using h.pc
      minstret := h.minstret
      regs := ⟨h.spReg, h.cursor hi, h.indexReg, h.scopeReg, h.closureReg, trivial⟩
      bound := by simpa only [if_pos hi] using h.s6
      savedRead := h.savedRead, gp := h.gp, present := h.present, support := h.support
      stack := context.stack, stackRam := context.stackRam, stackWin := context.stackWin
      stackHi := context.stackHi, valid := valid, scopeAddr := context.scopeAddr
      unique := frameUnique_of_frameNamesUnique
        (fold_unique store cd values target index context.unique target valid)
      bounded := by
        intro i hi
        simpa only [(fold_sizes store cd values target index).2] using context.bounded i hi
      emptyCapacity := fun empty => h.emptyCapacity (by
        change (foldStore store cd values target index).frames[target].vars.length = 0 at empty
        by_cases zero : index = 0
        · exact zero
        · have := counts.2 (by omega)
          omega)
      nameRequest := context.names
      growRequest := by
        change 48 * (foldStore store cd values target index).frames[target].vars.length ≤ maxReq
        have := context.growth
        omega }
  obtain ⟨after, returned, alloc', exts', shared', steps, result⟩ := input.run L placement
  have spReg : after.σ.regs.get? Register.x2 = some sp := by
    show gprGet after.σ 2 = some sp
    exact gholds_lookup _ result.resume.regs (by rfl)
  have indexReg : after.σ.regs.get? Register.x15 = some (BitVec.ofNat 64 (8 * (index + 1))) := by
    show gprGet after.σ 15 = some (BitVec.ofNat 64 (8 * (index + 1)))
    exact gholds_lookup _ result.resume.regs (by rfl)
  have s6 : after.σ.regs.get? Register.x22 = some
      (if index + 1 < values.length then BitVec.ofNat 64 (8 * values.length) else savedS6) := by
    show gprGet after.σ 22 = _
    apply gholds_lookup _ result.resume.regs
    simp [ClosureParamResume.selected, lookupG]
  have cursorEq : BitVec.ofNat 64 (sp.toNat + 240 + 24 * index) + 24#64 =
      BitVec.ofNat 64 (sp.toNat + 240 + 24 * (index + 1)) := by
    rw [← BitVec.ofNat_add]
    congr 1
  have present : EnvDefineSavedPresent (fun R => after.σ.regs.get? R) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [result.cursor]; rfl
    · rw [result.frame .x9 (by decide)]; exact h.present.s1
    · rw [result.frame .x18 (by decide)]; exact h.present.s2
    · rw [result.scope]; rfl
    · rw [result.frame .x20 (by decide)]; exact h.present.s4
    · rw [result.closure]; rfl
    · rw [s6]; rfl
  refine ⟨after, alloc', exts', shared', steps,
    { allocator := ?_, data := result.data
      includes := fun k hk => result.result.includes k (h.includes k hk)
      agreement := fun k hk => (h.agreement k hk).trans (result.result.agreement k (h.includes k hk))
      presence := h.presence.trans result.presence
      memoryFrame := fun k ha hs => (h.memoryFrame k ha hs).trans (result.memoryFrame k ha hs)
      highStack := fun k hlo hhi => (h.highStack k hlo hhi).trans (result.highStack k hlo hhi)
      saved7Frame := fun k hlo hhi => (h.saved7Frame k hlo hhi).trans (result.saved7Frame k hlo hhi)
      indexBound := by omega, good := result.resume.good, tick := result.resume.tick
      pc := by simpa only [ClosureParamResume.exitPC, decide_eq_true_eq] using result.resume.pc
      minstret := result.resume.minstret, spReg := spReg
      scopeReg := result.scope, closureReg := result.closure
      cursor := fun _ => by rw [← cursorEq]; exact result.cursor
      indexReg := indexReg, s6 := s6, savedRead := result.savedRead, gp := result.gp
      present := present, support := result.support, emptyCapacity := fun impossible => by omega
      output := result.output.trans h.output
      frame := fun R kept => (result.frame R kept).trans (h.frame R kept) }⟩
  simpa only [nextStore] using result.result.allocator

/-- Existential allocation witnesses stay local to each reached prefix. -/
structure FoldLoopState
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (N : NativeAddrs) (phiF phiC : Addr → Nat)
    (entryShared : Nat → Prop) (reserve : Nat) (store : Store) (cd : ClosureData) (values : List Value)
    (target : Addr) (sp scope closure names savedS6 : BitVec 64) (origin : Config)
    (index : Nat) (before : Config) : Prop where
  selected : ∃ alloc exts shared, FoldLoopAt M N phiF phiC entryShared reserve store cd values target
    sp scope closure names savedS6 origin alloc exts shared index before

/-- Bind every source parameter through the checked machine iteration and reach body entry. -/
theorem fold_run
    (context : FoldContext SL maxReq phiF store cd values target sp scope)
    (L : AllocLedger A SL gpv headroom maxReq M) (placement : BindingArena A SL) :
    Triple
      (FoldLoopState M N phiF phiC entryShared reserve store cd values target
        sp scope closure names savedS6 origin 0)
      (FoldLoopState M N phiF phiC entryShared reserve store cd values target
        sp scope closure names savedS6 origin values.length) := by
  apply storeChainList
  intro index hi before initial
  obtain ⟨alloc, exts, shared, head⟩ := initial.selected
  obtain ⟨after, alloc', exts', shared', steps, next⟩ := head.step context L placement hi
  exact ⟨after, steps, ⟨alloc', exts', shared', next⟩⟩

end Vsa.Sim.ClosureParam
