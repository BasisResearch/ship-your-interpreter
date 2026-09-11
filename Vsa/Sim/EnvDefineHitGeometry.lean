import Vsa.Sim.EnvDefineHitAllocator
import Vsa.Sim.ExecEntry
import Vsa.Sim.RuntimeOwnershipLookup
import Vsa.Sim.rows.EnvDefineContractUpdate

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The actual backing-array pointer and selected destination for one occupied binding. -/
structure EnvDefineHitGeometry (A : Arena) (phiF : Addr → Nat) (target idx : Nat)
    (env src vals dst : BitVec 64) (m : Mem) : Prop where
  values : read64 m (phiF target + 16) = some vals.toNat
  slot : dst.toNat = vals.toNat + 24 * idx
  geometry : EnvDefineUpdateGeom env src vals dst idx m
  arena : A.contains dst.toNat 24

/-- Owned array bounds supply every address used by the existing-name update. -/
theorem RuntimeAllocatorState.defineHitGeometry
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {store : Store} {m : Mem}
    {target idx : Nat} {env src sp : BitVec 64}
    (h : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store m)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (valid : target < store.frames.size) (hi : idx < store.frames[target].vars.length)
    (envAddr : env.toNat = phiF target) (source : RetSlotGeom SL sp src) :
    ∃ vals dst, EnvDefineHitGeometry A phiF target idx env src vals dst m := by
  obtain ⟨arrays, fields⟩ := (h.heap.store.frames target valid).arrays
  have range := fields.values.slot_in_arena h.heap.ledger (Nat.lt_of_lt_of_le hi fields.bound)
  obtain ⟨dstLo, dstHi⟩ := range
  have valuesNat : (BitVec.ofNat 64 arrays.values).toNat = arrays.values := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ fields.valuesRead)]
  have ram := L.arena_ram
  have htif := L.arena_htif
  have strideLt : 24 * idx < 2^64 := by omega
  have dstNat : (BitVec.ofNat 64 arrays.values + BitVec.ofNat 64 (24 * idx)).toNat =
      arrays.values + 24 * idx := by
    rw [BitVec.toNat_add, valuesNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt strideLt,
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨envArena, envAlign⟩ := h.repr.frames_arena target valid
  obtain ⟨envLo, envHi⟩ := envArena
  have valuesAlign := h.arrays.valuesAligned target valid arrays.values fields.valuesRead
  refine ⟨BitVec.ofNat 64 arrays.values,
    BitVec.ofNat 64 arrays.values + BitVec.ofNat 64 (24 * idx),
    { values := by rw [valuesNat]; exact fields.valuesRead
      slot := by rw [dstNat, valuesNat]
      arena := by rw [dstNat]; exact ⟨dstLo, dstHi⟩
      geometry :=
        { valsRead := by rw [envAddr, valuesNat]; exact fields.valuesRead
          envLo := by omega, envHi := by omega, envHtif := by right; omega
          envAlign := by omega
          srcLo := source.ram.1, srcHi := source.ram.2
          srcHtif := Or.inr (by have := source.win; omega), srcAlign := source.align
          dstEq := by rw [dstNat, valuesNat]
          idx3 := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
            omega
          idx24 := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
            omega
          strideCalc := by
            apply BitVec.eq_of_toNat_eq
            rw [update_a4_stride (BitVec.ofNat 64 idx) idx
              (by rw [BitVec.toNat_ofNat]; omega) strideLt]
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt strideLt]
          addrCalc := rfl
          dstLo := by rw [dstNat]; omega, dstHi := by rw [dstNat]; omega
          dstHtif := by rw [dstNat]; omega, dstAlign := by rw [dstNat]; omega } }⟩

#print axioms RuntimeAllocatorState.defineHitGeometry

end Vsa.Sim
