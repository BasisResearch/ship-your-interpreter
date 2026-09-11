import Vsa.Sim.EnvDefinePrologueAllocator
import Vsa.Sim.EnvGetReflected.EnvGetOwnedNames
import Vsa.Sim.StrCmpSeam

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The finite scan keeps owned data at the same memory on both exit routes. -/
structure EnvDefineScanAllocatorPost
    (saved gm : (R : Register) → Option (RegisterType R))
    (env namePtr pv count pn sp : BitVec 64) (m : Mem) (out : Array String)
    (N : NativeAddrs) {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (store : Store)
    (target : Addr) (valid : target < store.frames.size) (name : String) (v : Value)
    (after : Config) : Prop where
  scanned : EnvDefineScanFramedResult M exts out saved gm env namePtr pv count pn sp
    store.frames[target] name m after
  memory : after.σ.mem = m
  namesRead : read64 after.σ.mem (phiF target + 8) = some pn.toNat
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store after.σ.mem
  word : ValueWordRepr after.σ.mem N phiC pv.toNat v
  owned : ValueOwned after.σ.mem shared pv.toNat v
  nameOwned : SharedCString after.σ.mem shared namePtr.toNat name
  support : EvalCallSupport after.σ.mem SL A sp

/-- Run the positive-count scan from the owned prologue, deriving comparison data from ownership. -/
theorem EnvDefinePrologueAllocatorPost.scan
    {g : (R : Register) → Option (RegisterType R)}
    {esp aEnv aName pv r : BitVec 64} {m : Mem} {out : Array String}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {store : Store}
    {target : Addr} {valid : target < store.frames.size} {name : String} {v : Value} {before : Config}
    (h : EnvDefinePrologueAllocatorPost g esp aEnv aName pv r m out N M
      phiF phiC alloc exts shared credits store target valid name v before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (envAddr : aEnv.toNat = phiF target) (stack : StackOK SL esp 1088)
    (positive : 0 < store.frames[target].vars.length) :
    ∃ after pn, Steps before after ∧
      EnvDefineScanAllocatorPost (envDefineSaved g r)
        (envDefineScanBaseGhost (fun R => before.σ.regs.get? R) pn)
        aEnv aName pv (BitVec.ofNat 64 store.frames[target].vars.length) pn (esp - 64#64)
        before.σ.mem out N M phiF phiC alloc exts shared credits store target valid name v after := by
  have frame := h.allocator.heap.store.frames target valid
  obtain ⟨arrays, fields⟩ := frame.arrays
  have pnNat : (BitVec.ofNat 64 arrays.names).toNat = arrays.names := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ fields.namesRead)]
  have names := frame.scanNames h.allocator.heap.ledger h.allocator.geometry
    L.arena_ram.1 L.arena_ram.2 (by have := L.arena_htif; omega) fields.namesRead
    (h.allocator.arrays.namesAligned target valid arrays.names fields.namesRead)
    h.nameOwned (FixedRodataLoaded.maskPinned h.support.image.rodata)
  obtain ⟨stackLo, stackHi, stackAlign⟩ := stack
  have spNat := sp_sub64_toNat esp (by omega : 64 ≤ esp.toNat)
  have headroomBound := L.headroom_le
  have stack' : StackOK SL (esp - 64#64) headroom := by
    refine ⟨?_, ?_, ?_⟩ <;> rw [spNat] <;> omega
  obtain ⟨envArena, envAlign⟩ := h.allocator.repr.frames_arena target valid
  obtain ⟨envLo, envHi⟩ := envArena
  have arenaRam := L.arena_ram
  have arenaHtif := L.arena_htif
  have geometry : EnvDefineScanInitGeom aEnv (BitVec.ofNat 64 arrays.names) before.σ.mem :=
    { read := by rw [envAddr, pnNat]; exact fields.namesRead
      lo := by omega, hi := by omega, htif := by right; omega, align := by omega }
  have countNat : (BitVec.ofNat 64 store.frames[target].vars.length).toNat =
      store.frames[target].vars.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countSigned; omega)]
  have stable : ∀ (a b : MState), a.regs.get? Register.x3 = b.regs.get? Register.x3 →
      (∀ k, a.mem[k]? = b.mem[k]?) → M.AInv a exts → M.AInv b exts :=
    fun a b gp memory => L.ainv_private exts a b gp (fun k _ => memory k)
  obtain ⟨after, steps, scanned⟩ := envDefineScanDispatchFramed M exts out
    (envDefineSaved g r) (fun R => before.σ.regs.get? R)
    aEnv aName pv (BitVec.ofNat 64 store.frames[target].vars.length)
    (BitVec.ofNat 64 arrays.names) (esp - 64#64) store.frames[target] name N phiF phiC before.σ.mem
    (by rw [envAddr]; exact h.allocator.repr.frames target valid)
    (by rw [pnNat]; exact names) countNat positive h.countSigned geometry stable before
    ⟨h.good, h.support.image.text.Env_defineLoaded, h.support.image.text.StrcmpLoaded,
      rfl, h.pc, h.a0, h.s4, h.s2, h.s5, h.s3, h.sp, h.tick, h.saved,
      ⟨stack', h.gp, fun _ _ => rfl, h.allocator.ainv before.σ h.gp rfl, h.output⟩⟩
  have memory : after.σ.mem = before.σ.mem :=
    scanned.resolve (fun _ _ _ hit => hit.memory) (fun _ _ miss => miss.memory)
  refine ⟨after, BitVec.ofNat 64 arrays.names, steps,
    { scanned := scanned, memory := memory, namesRead := ?_, allocator := ?_, word := ?_, owned := ?_
      nameOwned := ?_, support := ?_ }⟩ <;> rw [memory]
  · rw [pnNat]; exact fields.namesRead
  · exact h.allocator
  · exact h.word
  · exact h.owned
  · exact h.nameOwned
  · exact h.support.transport (fun _ _ => rfl)

#print axioms EnvDefinePrologueAllocatorPost.scan

end Vsa.Sim
