import Vsa.Sim.EnvDefineScanMiss
import Vsa.Sim.EnvDefineGrowAllocator

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The exhausted scan retains the caller facts needed by either capacity arm. -/
structure EnvDefineCapacityCaller
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st : Vsa.While.St) (target : Addr) (name : String) (v : Value)
    (esp env namePtr src r pn : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (cap : Nat) (after : Config) : Prop where
  facts : EnvDefineMissFacts g N A SL phiF phiC st target name v esp env namePtr src r m
    exts after.σ.mem cap
  regs : EnvDefineMissRegs g A SL st target esp env namePtr src r out M exts after.σ.mem facts.env_lt after
  namesReg : after.σ.regs.get? Register.x22 = some pn

/-- Rebase the scan ghost on the original prologue's saved caller state. -/
theorem EnvDefineCapacityAllocatorPost.caller
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {target : Addr} {valid : target < st.store.frames.size} {name : String} {v : Value}
    {esp env namePtr src r pn : BitVec 64} {m : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {credits cap : Nat} {before after : Config}
    (h : EnvDefinePrologueAllocatorPost g esp env namePtr src r m out N M
      phiF phiC alloc exts shared credits st.store target valid name v before)
    (post : EnvDefineCapacityAllocatorPost (envDefineSaved g r)
      (envDefineScanBaseGhost (fun R => before.σ.regs.get? R) pn)
      env namePtr src (BitVec.ofNat 64 (st.store.frames[target]'valid).vars.length) pn (esp - 64#64)
      before.σ.mem out N M phiF phiC alloc exts shared credits st.store target valid name v cap after)
    (geometry : EnvDefineGrowGeometry A SL esp src)
    (envAddr : env.toNat = phiF target) (ghostSp : g Register.x2 = some esp)
    (retAlign : r.toNat % 4 = 0) :
    EnvDefineCapacityCaller g N A SL phiF phiC st target name v esp env namePtr src r pn m out M
      exts cap after := by
  have C := post.capacity
  have frame : ∀ R, AbiPreserved R = true → R ≠ Register.x8 → R ≠ Register.x9 → R ≠ Register.x22 →
      after.σ.regs.get? R = before.σ.regs.get? R := by
    intro R abi notS0 notS1 notS6
    rw [C.frame.abi R abi, envDefineScanGhost_ne _ _ _ notS0 notS1,
      envDefineScanBaseGhost_ne _ _ notS6]
  have F : EnvDefineMissFacts g N A SL phiF phiC st target name v esp env namePtr src r m
      exts after.σ.mem cap :=
    { ra_align := retAlign, g_sp := ghostSp, env_lt := valid, env_addr := envAddr
      text := post.support.image.text, store := post.allocator.repr
      owned := ⟨alloc, shared, InitialReadableByte, InitialWriteByte SL, post.allocator.heap,
        fun _ lo hi => Or.inr ⟨lo, hi⟩, post.owned, post.nameOwned⟩
      word := post.word
      cap_read := by rw [C.memory, ← envAddr]; exact C.capacityRead
      names_align := post.allocator.arrays.namesAligned target valid
      vals_align := post.allocator.arrays.valuesAligned target valid
      miss := post.missing
      mem_agree := fun k _ off => by
        rw [C.memory]
        exact (h.outside k (by have := geometry.stack.1; omega)).symm
      mem_extends := by rw [C.memory]; exact h.presence }
  have R : EnvDefineMissRegs g A SL st target esp env namePtr src r out M exts after.σ.mem valid after :=
    { good := C.good, tick := C.tick, mem := rfl, out := C.frame.out, minstret := C.good.minstret
      sp := (frame _ (by decide) (by decide) (by decide) (by decide)).trans h.sp
      gp := C.frame.gp
      s2 := (frame _ (by decide) (by decide) (by decide) (by decide)).trans h.s2
      s3 := (frame _ (by decide) (by decide) (by decide) (by decide)).trans h.s3
      s4 := (frame _ (by decide) (by decide) (by decide) (by decide)).trans h.s4
      s5 := (frame _ (by decide) (by decide) (by decide) (by decide)).trans h.s5
      rest := by
        intro reg abi restored notSp
        obtain ⟨_, kept, notS0, notS1, notS6⟩ := envDefineRest_facts reg abi restored notSp
        exact (frame reg abi notS0 notS1 notS6).trans (h.frame reg kept)
      saved := C.savedFrame, stack := C.frame.stack, ainv := C.frame.ainv }
  refine ⟨F, R, ?_⟩
  rw [C.frame.abi .x22 (by decide), envDefineScanGhost_ne _ _ _ (by decide) (by decide),
    envDefineScanBaseGhost_x22]

#print axioms EnvDefineCapacityAllocatorPost.caller

end Vsa.Sim
