import Vsa.Sim.SeqBlockLoopStep

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Shared pointer-cell bounds identify the owned suffix with the block index. -/
theorem ExecSeqAllocatorEntry.blockSuffix
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet block base : BitVec 64} {index count : Nat} {m0 : Mem} {before : Config}
    (entry : ExecSeqAllocatorEntry .blockBody g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (cursor : ExecSeqBlockCursor before.σ.mem phiF env (s :: ss)
      sp aRet block base index count before.σ.regs.get?) :
    SeqSuffixOwned before.σ.mem shared SL A sp aRet d (base.toNat + 8 * index) (s :: ss) := by
  obtain ⟨a, selected, suffix⟩ := entry.suffix (by simp)
  cases selected with
  | @blockBody block' base' index' blockReg indexReg baseRead =>
    have hb : block' = block := Option.some.inj (blockReg.symm.trans cursor.blockReg)
    subst block'
    have hbase : base' = base := BitVec.eq_of_toNat_eq
      (Option.some.inj (baseRead.symm.trans cursor.baseRead))
    subst base'
    obtain ⟨_, cell, _⟩ := suffix.head
    have geometry := AstReadGeometry.of_covered entry.allocator.heap.immutable cell.covered (by decide)
    have upper : base.toNat + 8 * index' + 8 ≤ 0x100000000 := geometry.ram_hi
    have originalBound : index < 2^64 := by
      have := cursor.remaining
      have := cursor.countBound
      omega
    have selectedBound : index' < 2^64 := by omega
    have indices := congrArg BitVec.toNat (Option.some.inj (indexReg.symm.trans cursor.indexReg))
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt selectedBound,
      Nat.mod_eq_of_lt originalBound] at indices
    subst index'
    exact suffix

namespace SeqBlockDispatch

/-- Derive dispatch and normal-route geometry from the owned header and cursor. -/
theorem LoopInput.of_resources
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet block base : BitVec 64} {index count : Nat} {m0 : Mem} {before : Config}
    (entry : ExecSeqAllocatorEntry .blockBody g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (cursor : ExecSeqBlockCursor before.σ.mem phiF env (s :: ss)
      sp aRet block base index count before.σ.regs.get?)
    (resources : ExecSeqBlockResources A SL shared sp aRet block before.σ.regs.get?) :
    ∃ interp, LoopInput N A SL phiF shared st d env s ss
      block base sp aRet interp index count before := by
  have ready := entry.entry.ready (by simp)
  obtain ⟨p, head⟩ := ready.head_ground.facts
  obtain ⟨interp, interpReg, _, _⟩ := head.call
  have suffix := entry.blockSuffix cursor
  obtain ⟨_, cell, _⟩ := suffix.head
  have domain := SharedReadDomain.of_immutable entry.allocator.heap.immutable
  have baseGeom := AstReadGeometry.of_domain domain resources.baseCovered (by decide)
  have countGeom := AstReadGeometry.of_domain domain resources.countCovered (by decide)
  have cellGeom := AstReadGeometry.of_domain domain cell.covered (by decide)
  have stackOK := head.stackOK
  have stackRam := ready.stack_ram
  have stackWin := ready.stack_win
  have stackHi := resources.stackHi
  have codeOff := head.ground.eval_call.image.stack_disjoint
    (lo := 0x80003fe0) (hi := 0x800043ec) (by decide) (by decide)
  refine ⟨interp,
    { geometry :=
        { blockLo := baseGeom.ram_lo, blockHi := baseGeom.ram_hi
          blockHtif := baseGeom.htif.imp id (fun h => by omega)
          cellLo := cellGeom.ram_lo, cellHi := cellGeom.ram_hi
          cellHtif := cellGeom.htif.imp id (fun h => by omega)
          stackLo := by have := stackOK.1; omega
          stackHi := by omega
          stackHtif := by have := stackOK.1; omega
          stackAlign := by have := stackOK.2.2; omega
          codeOff := by have := stackOK.1; omega }
      registers := ⟨cursor.blockReg, cursor.indexReg, cursor.spReg, interpReg,
        cursor.envReg, cursor.retReg, trivial⟩
      baseRead := cursor.baseRead, suffix := suffix
      stackWrite := by have := stackOK.1; omega
      stackOK := stackOK, storeBodies := head.storeBodies
      spill20 := resources.spill20, spill21 := resources.spill21
      baseCovered := resources.baseCovered, blockCount := cursor.countRead
      countCovered := resources.countCovered
      remaining := by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using cursor.remaining
      countBound := cursor.countBound, savedOffArena := resources.savedOffArena
      savedOffRet := resources.savedOffRet
      normalGeometry :=
        { stackLo := by have := stackOK.1; omega
          stackHi := by omega
          stackHtif := Or.inr (by have := stackOK.1; omega)
          countLo := countGeom.ram_lo, countHi := countGeom.ram_hi
          countHtif := countGeom.htif.imp id (fun h => by omega) } }⟩

/-- Select every block loop input from the actual owned sequence entry. -/
theorem LoopInput.of_entry
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St}
    {s : Stmt} {ss : List Stmt} {sp aRet : BitVec 64} {m0 : Mem} {before : Config}
    (entry : ExecSeqAllocatorEntry .blockBody g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before) :
    ∃ block base interp index count,
      LoopInput N A SL phiF shared st d env s ss block base sp aRet interp index count before := by
  obtain ⟨block, base, index, count, cursor⟩ := (entry.entry.ready (by simp)).cursor.block
  obtain ⟨stored, storedReg, resources⟩ := entry.blockResources rfl (by simp)
  have same : stored = block := Option.some.inj (storedReg.symm.trans cursor.blockReg)
  subst stored
  obtain ⟨interp, input⟩ := LoopInput.of_resources entry cursor resources
  exact ⟨block, base, interp, index, count, input⟩

#print axioms LoopInput.of_resources
#print axioms LoopInput.of_entry

end SeqBlockDispatch

#print axioms ExecSeqAllocatorEntry.blockSuffix

end Vsa.Sim
