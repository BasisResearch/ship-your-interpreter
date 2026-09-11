import Vsa.Sim.CallArgumentValues
import Vsa.Sim.ClosureCallPrefix

namespace Vsa.Sim.CallCallee

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Owned closure and function fields supply the dispatch's heap and AST windows. -/
theorem ClosureDataAt.geometry
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {entryF entryC resultF resultC : Addr → Nat}
    {nf nc : Nat} {alloc : Allocations} {exts : List Extent} {entryShared shared : Nat → Prop}
    {credits : Nat} {store : Store} {ca : Addr} {cd : ClosureData} {values : List Value}
    {sp node interp : BitVec 64} {fn names body : Nat} {m0 m : Mem}
    (h : ClosureDataAt N M entryF entryC resultF resultC nf nc alloc exts entryShared shared
      credits store ca cd values sp fn names body m0 m)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (source : store.closures[ca]? = some cd) (caller : BinaryPrefix.Geometry node sp)
    (window : BinaryPrefix.Window SL sp)
    (interpAbove : sp.toNat + 1056 ≤ interp.toNat) (interpHi : interp.toNat + 12 ≤ SL.hi)
    (ram : SL.hi ≤ 0x100000000) (interpAlign : interp.toNat % 4 = 0) :
    ClosureCallPrefix.Geometry sp node (BitVec.ofNat 64 (resultC ca)) (BitVec.ofNat 64 fn) interp := by
  have valid := (Array.getElem?_eq_some_iff.mp source).1
  have objectBounds := h.allocator.repr.closures_arena ca valid
  obtain ⟨⟨objectLo, objectHi⟩, objectAlign⟩ := objectBounds
  have objectNat : (BitVec.ofNat 64 (resultC ca)).toNat = resultC ca :=
    Nat.mod_eq_of_lt (by have := L.arena_ram.2; omega)
  have fnNat : (BitVec.ofNat 64 fn).toNat = fn := Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ h.object.nodeRead)
  have fnGeom := AstReadGeometry.of_covered h.allocator.heap.immutable h.object.node.countCovered (by decide)
  have fnOff := fnGeom.stack_disjoint (by have := window.lo; have := window.hi; omega)
  refine
    { stackLo := caller.stackLo, stackHi := caller.stackHi, stackHtif := caller.stackHtif
      stackAlign := caller.stackAlign
      callLo := by have := caller.nodeLo; omega
      callHi := by have := caller.nodeHi; omega
      callHtif := by have := caller.nodeHtif; omega
      objectLo := ?_, objectHi := ?_, objectHtif := ?_, objectOff := ?_, objectInterp := ?_
      fnLo := by rw [fnNat]; exact fnGeom.ram_lo
      fnHi := by rw [fnNat]; exact fnGeom.ram_hi
      fnHtif := by rw [fnNat]; have := fnGeom.htif; omega
      fnOff := by rw [fnNat]; have := window.lo; have := window.hi; omega
      interpAbove := interpAbove, interpHi := by omega, interpAlign := interpAlign }
  · rw [objectNat]; have := L.arena_ram.1; omega
  · rw [objectNat]; have := L.arena_ram.2; omega
  · rw [objectNat]; right; have := L.arena_htif; omega
  · rw [objectNat]; have := L.arena_stack; have := window.lo; have := window.hi; omega
  · rw [objectNat]; have := L.arena_stack; have := window.lo; omega

end Vsa.Sim.CallCallee
