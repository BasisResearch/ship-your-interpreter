import Vsa.Sim.EnvDefineNameLength
import Vsa.Sim.EnvDefineGrowAllocator
import Vsa.Sim.RuntimeAllocatorMalloc

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership TruthyCopy

/-- The name allocation retains the old store while reserving its fresh copy block. -/
structure EnvDefineNameAllocated
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (name : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (credits cap p : Nat)
    (before after : Config) : Prop where
  facts : EnvDefineMissFacts g N A SL phiF phiC st env name v esp aEnv aName pv r m
    exts after.σ.mem cap
  regs : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M
    ((p, name.length + 1) :: exts) after.σ.mem facts.env_lt after
  pc : after.σ.regs.get? Register.PC = some 0x80002b30#64
  copyReg : after.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p)
  sizeReg : after.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 (name.length + 1))
  block : MallocBlock A exts (name.length + 1) p
  allocator : RuntimeAllocatorState M N phiF phiC alloc ((p, name.length + 1) :: exts)
    shared credits st.store after.σ.mem
  baseHeap : HeapOwned A exts after.σ.mem phiF phiC alloc shared
    InitialReadableByte (InitialWriteByte SL) st.store
  owned : ValueOwned after.σ.mem shared pv.toNat v
  nameOwned : SharedCString after.σ.mem shared aName.toNat name
  support : EvalCallSupport after.σ.mem SL A esp
  agreement : AgreeP shared before.σ.mem after.σ.mem
  outside : ∀ k, ¬ M.privFoot k → ¬ (SL.lo ≤ k ∧ k < (esp - 64#64).toNat) →
    after.σ.mem[k]? = before.σ.mem[k]?
  presence : MemExtends before.σ.mem after.σ.mem
  frame : ∀ R, abiButS0 R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute strlen and malloc for an owned name, consuming one allocation credit. -/
theorem EnvDefineAppendAllocatorPost.allocateName
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {name : String} {v : Value}
    {esp aEnv aName pv r : BitVec 64} {m : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {credits cap : Nat} {before : Config}
    (h : EnvDefineAppendAllocatorPost g N A SL phiF phiC st env name v esp aEnv aName pv r m out M
      alloc exts shared (credits + 1) cap before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (geometry : EnvDefineGrowGeometry A SL esp pv) (request : name.length + 1 ≤ maxReq) :
    ∃ after p, Steps before after ∧
      EnvDefineNameAllocated g N A SL phiF phiC st env name v esp aEnv aName pv r m out M
        alloc exts shared credits cap p before after := by
  have F := h.head.facts
  have R := h.head.regs
  obtain ⟨called, prepared⟩ := envDefineNameMallocParked_of R.good h.head.pc R.s2 F.text R.tick
    h.allocator.geometry h.nameOwned
  let gm := fun reg => called.σ.regs.get? reg
  have sp : called.σ.regs.get? Register.x2 = some (esp - 64#64) :=
    (prepared.abi _ (by decide)).trans R.sp
  have gp : called.σ.regs.get? Register.x3 = some gpv :=
    (prepared.abi _ (by decide)).trans R.gp
  have parked : MallocParked A SL gpv headroom maxReq M gm exts (name.length + 1)
      (esp - 64#64) 0x80002b30#64 before.σ.mem out N phiF phiC alloc shared
      InitialReadableByte (InitialWriteByte SL) st.store credits called :=
    { entry := { good := prepared.good, tick := prepared.tick, pc := prepared.pc, a0 := prepared.a0
                 ra := prepared.ra, ra_align := by decide, sp := sp, stack := R.stack, gp := gp
                 frame := fun _ _ => rfl
                 ainv := AllocLedger.ainvAt_at_state h.allocator.ainv gp prepared.mem
                 mem := prepared.mem, out := prepared.out.trans R.out }
      code := by rw [prepared.mem, R.mem]; exact F.text
      resources :=
        { bounded := request, budget := h.allocator.budget
          reserve := by rw [prepared.mem]; exact h.allocator.reserve }
      owned := h.allocator.heap, store := h.allocator.repr
      writes_stack := fun _ lo hi => Or.inr ⟨lo, hi⟩ }
  obtain ⟨after, mallocSteps, p, X⟩ := mallocReturn_of_parked L gm exts (name.length + 1)
    (esp - 64#64) 0x80002b30#64 before.σ.mem out N phiF phiC alloc shared
    InitialReadableByte (InitialWriteByte SL) st.store credits request (by omega) called parked
  have runtime := X.runtime h.allocator request
  have frame : ∀ reg, abiButS0 reg = true → after.σ.regs.get? reg = before.σ.regs.get? reg :=
    fun reg keep => (X.exit.frame reg (abiButS0_abi keep)).trans (prepared.abi reg keep)
  have agreement : AgreeP shared before.σ.mem after.σ.mem :=
    fun k hk => X.agree k ((X.ownedOff.shared k hk).mono (by simp))
  have stackLo := geometry.stack.1
  have stackHi := geometry.stack.2.1
  have slotLo := geometry.slot_above
  have slotHi := geometry.slot_in_stack
  have ram := geometry.stack_ram
  have sp64 := sp_sub64_toNat esp (by omega)
  have slotAgreement : ∀ k, valHeader pv.toNat k → before.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    unfold valHeader at hk
    apply Eq.symm (X.exit.mem_frame k ?_ ?_)
    · intro privateByte
      have arena := L.priv_arena k privateByte
      have separate := L.arena_stack
      omega
    · rw [sp64]
      omega
  let P : Nat → Prop := fun k => before.σ.mem[k]? = after.σ.mem[k]?
  have memory : AgreeP P before.σ.mem after.σ.mem := fun _ hk => hk
  have value := h.owned.transport memory slotAgreement agreement
  have nameAfter := h.nameOwned.transport agreement
  have support : EvalCallSupport after.σ.mem SL A esp := by
    apply h.support.transport
    intro k hk
    apply X.exit.mem_frame k
    · intro privateByte
      exact h.support.outsideArena hk (L.priv_arena k privateByte)
    · intro window
      apply h.support.outsideStack hk
      rw [sp64] at window
      exact ⟨window.1, by omega⟩
  have word : ValueWordRepr after.σ.mem N phiC pv.toNat v :=
    ⟨valueRepr_agreeP memory slotAgreement (h.owned.covered agreement) F.word.repr,
      valueWordsTotal_transport F.word.words memory slotAgreement⟩
  have record := h.allocator.heap.store.frameFootprint
    (X.ownedOff.mono (fresh' := []) (by simp)).alloc
    (X.ownedOff.mono (fresh' := []) (by simp)).shared F.env_lt
  have capEq := (extent_covers record.header (by decide : 4 + 4 ≤ 32)).read32_eq X.agree
  have facts : EnvDefineMissFacts g N A SL phiF phiC st env name v esp aEnv aName pv r m
      exts after.σ.mem cap :=
    { F with text := support.image.text, store := X.store
             owned := ⟨alloc, shared, InitialReadableByte, InitialWriteByte SL, X.owned0,
               fun _ lo hi => Or.inr ⟨lo, hi⟩, value, nameAfter⟩
             word := word, cap_read := capEq.symm.trans F.cap_read
             names_align := runtime.arrays.namesAligned env F.env_lt
             vals_align := runtime.arrays.valuesAligned env F.env_lt
             mem_agree := by
               intro k outsideArena outsideStack
               rw [X.exit.mem_frame k (fun hp => outsideArena (L.priv_arena k hp)) (by
                 rw [sp64]; intro hk; exact outsideStack ⟨hk.1, by omega⟩)]
               exact F.mem_agree k outsideArena outsideStack
             mem_extends := F.mem_extends.trans X.exit.mem_extends }
  have saved := R.saved.of_interval_agree
    (fun k lo hi => by
      apply X.exit.mem_frame k
      · intro hp
        have arena := L.priv_arena k hp
        have image := geometry.arena_image
        omega
      · rw [sp64]
        have win := geometry.stack_win
        unfold tohostAddr at win
        omega)
    (fun k lo hi => by
      apply X.exit.mem_frame k
      · intro hp
        have arena := L.priv_arena k hp
        have separate := L.arena_stack
        rw [sp64] at lo hi
        omega
      · omega)
  have regs : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M
      ((p, name.length + 1) :: exts) after.σ.mem facts.env_lt after :=
    { good := X.exit.good, tick := X.exit.tick, mem := rfl, out := X.exit.out
      minstret := X.exit.good.minstret
      sp := X.exit.sp, gp := X.exit.gp
      s2 := (frame _ (by decide)).trans R.s2, s3 := (frame _ (by decide)).trans R.s3
      s4 := (frame _ (by decide)).trans R.s4, s5 := (frame _ (by decide)).trans R.s5
      rest := by
        intro reg abi restored notSp
        obtain ⟨_, _, notS0, _, _⟩ := envDefineRest_facts reg abi restored notSp
        have kept : abiButS0 reg = true := by simp [abiButS0, abi, Ne.symm notS0]
        exact (frame reg kept).trans (R.rest reg abi restored notSp)
      saved := saved, stack := R.stack
      ainv := AllocLedger.ainvAt_at_state X.ainv X.exit.gp rfl }
  exact ⟨after, p, prepared.steps.trans mallocSteps,
    { facts := facts, regs := regs, pc := X.exit.pc, copyReg := X.a0
      sizeReg := (X.exit.frame _ (by decide)).trans prepared.s0, block := X.block
      allocator := runtime, baseHeap := X.owned0, owned := value, nameOwned := nameAfter, support := support
      agreement := agreement, outside := X.exit.mem_frame, presence := X.exit.mem_extends
      frame := frame }⟩

#print axioms EnvDefineAppendAllocatorPost.allocateName

end Vsa.Sim
