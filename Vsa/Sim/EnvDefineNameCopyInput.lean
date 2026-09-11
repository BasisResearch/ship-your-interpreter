import Vsa.Sim.EnvDefineNameCopyEntry
import Vsa.Sim.MemcpyCopyEntry
import Vsa.Sim.Code.FixedImage_Memcpy
import Vsa.Sim.rows.StrcpyContractInhab

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The allocated name call supplies the byte-copy execution precondition. -/
theorem EnvDefineNameCopyReady.copyInput
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {name : String} {v : Value}
    {esp aEnv aName pv r : BitVec 64} {m : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {credits cap p : Nat} {origin before : Config}
    (h : EnvDefineNameCopyReady g N A SL phiF phiC st env name v esp aEnv aName pv r m out M
      alloc exts shared credits cap p origin before)
    (L : AllocLedger A SL gpv headroom maxReq M) :
    ∃ bs, StrBytes before.σ.mem aName name.length bs ∧
      MemcpyCopy.Input (BitVec.ofNat 64 p) aName 0x80002b44#64 (name.length+1) bs
        before.σ.mem before := by
  obtain ⟨len, bs, length, source⟩ := cstring_bytes before.σ.mem aName name h.nameOwned.repr
  subst len
  have ptrNat := h.block.toNat L.arena_hi
  have arena := h.block.arena
  have arenaLow := L.arena_htif
  have arenaHigh := L.arena_hi
  have regions : MemcpyCopy.Regions (BitVec.ofNat 64 p) aName (name.length+1) := by
    obtain ⟨lo, hi⟩ := arena
    exact { dst_lo := by rw [ptrNat]; unfold tohostAddr at arenaLow; omega
            dst_hi := by rw [ptrNat]; omega, dst_win := by rw [ptrNat]; omega
            src_lo := h.sourceGeometry.lo
            src_hi := by have := h.sourceGeometry.hi; omega
            src_win := by have := h.sourceGeometry.htif; omega
            disjoint := by simpa only [ptrNat] using h.disjoint
            code_disjoint := by rw [ptrNat]; unfold tohostAddr at arenaLow; omega }
  refine ⟨bs, source,
    { good := h.regs.good, loaded := h.facts.text.MemcpyLoaded, tick := h.regs.tick
      a0 := h.copyReg, ra := h.returnReg, regions := regions, bound := Nat.zero_le _
      pc := h.pc, a1 := h.sourceReg, a2 := h.lengthReg, positive := by omega
      meminv := { copied := by intro k hk; omega, outside := by intro _ _; rfl
                  src_intact := ?_ } }⟩
  intro k _ bound
  by_cases char : k < name.length
  · exact (source.chars k char).1
  · have equal : k = name.length := by omega
    subst k
    exact source.nul

/-- Read back the complete copied name, including its terminator. -/
theorem MemcpyCopy.Returned.nameString
    {dst src r : BitVec 64} {name : String} {bs : Nat → BitVec 8} {m0 : Mem}
    {after : Config} (h : MemcpyCopy.Returned dst src r (name.length+1) bs m0 after)
    (nameRepr : CString m0 src.toNat name) (source : StrBytes m0 src name.length bs) :
    CString after.σ.mem dst.toNat name := by
  apply cstring_shift_copy nameRepr
  intro k bound
  rw [h.meminv.copied k (by omega)]
  by_cases char : k < name.length
  · exact (source.chars k char).1.symm
  · have equal : k = name.length := by omega
    subst k
    exact source.nul.symm

#print axioms EnvDefineNameCopyReady.copyInput
#print axioms MemcpyCopy.Returned.nameString

end Vsa.Sim
