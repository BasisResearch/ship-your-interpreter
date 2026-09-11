import Vsa.Sim.EnvGetReflected.EnvGetFrameParent
import Vsa.Sim.StoreInvariant

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- Read-only lookup data at the memory reached after the prologue.
Entry ownership and the source store invariant supply this record. -/
structure LookupData (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Vsa.While.Addr → Nat) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (s : Vsa.While.Store)
    (query : String) (name : BitVec 64) (m : Mem) : Prop where
  owned : StoreOwned m phiF phiC alloc shared s
  repr : StoreRepr m N A phiF phiC s
  arrays : StoreArraysReady m phiF s
  ledger : Ledger A exts alloc
  geometry : SharedReadGeom shared SL
  arenaLo : 0x80000000 ≤ A.lo
  arenaHi : A.hi ≤ 0x100000000
  arenaHtif : tohostAddr + 8 ≤ A.lo
  queryString : SharedCString m shared name.toNat query
  mask : MaskPinned m
  parents : StoreParents s

section Data

variable {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {name : BitVec 64} {m : Mem}
    (D : LookupData N A SL phiF phiC alloc exts shared s query name m)

include D in
theorem LookupData.framePointer {fa : Vsa.While.Addr} (hfa : fa < s.frames.size) :
    (BitVec.ofNat 64 (phiF fa)).toNat = phiF fa := by
  have hbound := (D.repr.frames_arena fa hfa).1
  change A.lo ≤ phiF fa ∧ phiF fa + 32 ≤ A.hi at hbound
  have hhi := D.arenaHi
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

include D in
/-- Reconstruct any represented frame at the actual read-only loop memory. -/
theorem LookupData.frame_state
    {fa : Vsa.While.Addr} {f : Vsa.While.Frame} {out ra sp : BitVec 64} {c : Config}
    (hframe : s.frames[fa]? = some f)
    (hregs : FrameRegisters (BitVec.ofNat 64 (phiF fa)) name out ra sp c)
    (hmem : c.σ.mem = m) :
    ∃ pn, FrameState (BitVec.ofNat 64 (phiF fa)) name out pn ra sp f query N phiF phiC c := by
  obtain ⟨hfa, helem⟩ := Array.getElem?_eq_some_iff.mp hframe
  obtain ⟨pn, hs⟩ := owned_frame_state hregs
    (by rw [hmem]; exact D.owned) (by rw [hmem]; exact D.repr)
    (by rw [hmem]; exact D.arrays) D.ledger D.geometry D.arenaLo D.arenaHi D.arenaHtif
    (by rw [hmem]; exact D.queryString) (by rw [hmem]; exact D.mask)
    hfa (D.framePointer hfa)
  exact ⟨pn, by simpa only [helem] using hs⟩

end Data

/-- Decode a represented frame pointer within the allocated prefix.
The store representation supplies uniqueness on that prefix. -/
noncomputable def lookupFrameIndex (s : Vsa.While.Store)
    (phiF : Vsa.While.Addr → Nat) (pointer : Nat) : Nat := by
  classical
  exact if h : ∃ fa, fa < s.frames.size ∧ phiF fa = pointer then h.choose else 0

section Measure

variable {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {name : BitVec 64} {m : Mem}
    (D : LookupData N A SL phiF phiC alloc exts shared s query name m)

include D in
theorem LookupData.frameIndex {fa : Vsa.While.Addr} (hfa : fa < s.frames.size) :
    lookupFrameIndex s phiF (phiF fa) = fa := by
  classical
  have hex : ∃ a, a < s.frames.size ∧ phiF a = phiF fa := ⟨fa, hfa, rfl⟩
  rw [lookupFrameIndex, dif_pos hex]
  exact D.repr.φf_inj _ fa hex.choose_spec.1 hfa hex.choose_spec.2

/-- At the count head the rank is the frame index plus one; exits have rank zero. -/
noncomputable def lookupMeasure (s : Vsa.While.Store)
    (phiF : Vsa.While.Addr → Nat) (c : Config) : Nat :=
  if c.σ.regs.get? Register.PC = some 0x80002c40#64 then
    lookupFrameIndex s phiF ((c.σ.regs.get? Register.x20).getD 0).toNat + 1
  else 0

include D in
theorem LookupData.measure_head {fa : Vsa.While.Addr} {c : Config}
    (hfa : fa < s.frames.size)
    (hpc : c.σ.regs.get? Register.PC = some 0x80002c40#64)
    (henv : c.σ.regs.get? Register.x20 = some (BitVec.ofNat 64 (phiF fa))) :
    lookupMeasure s phiF c = fa + 1 := by
  rw [lookupMeasure, if_pos hpc, henv, Option.getD_some,
    D.framePointer hfa, D.frameIndex hfa]

theorem lookupMeasure_exit {s : Vsa.While.Store} {phiF : Vsa.While.Addr → Nat}
    {pc : BitVec 64} {c : Config}
    (hpc : c.σ.regs.get? Register.PC = some pc) (hne : pc ≠ 0x80002c40#64) :
    lookupMeasure s phiF c = 0 := by
  simp only [lookupMeasure, hpc]
  exact if_neg (fun h => hne (Option.some.inj h))

end Measure

#print axioms LookupData.framePointer
#print axioms LookupData.frame_state
#print axioms LookupData.frameIndex
#print axioms LookupData.measure_head
#print axioms lookupMeasure_exit

end Vsa.Sim.EnvGetReflected
