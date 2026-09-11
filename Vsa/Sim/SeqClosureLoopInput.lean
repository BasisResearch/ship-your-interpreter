import Vsa.Sim.SeqClosureAllocatorStep

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Shared pointer-cell bounds identify the owned suffix with the actual cursor. -/
theorem ExecSeqAllocatorEntry.closureSuffix
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet body base : BitVec 64} {index count : Nat} {m0 : Mem} {before : Config}
    (entry : ExecSeqAllocatorEntry .closureBody g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (cursor : ExecSeqClosureCursor before.σ.mem phiF env (s :: ss)
      sp aRet body base index count before.σ.regs.get?) :
    SeqSuffixOwned before.σ.mem shared SL A sp aRet d (base.toNat + 8 * index) (s :: ss) := by
  obtain ⟨a, selected, suffix⟩ := entry.suffix (by simp)
  cases selected with
  | @closureBody body' base' index' bodyReg indexReg baseRead =>
    have hb : body' = body := Option.some.inj (bodyReg.symm.trans cursor.bodyReg)
    subst body'
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

namespace SeqClosureDispatch

/-- Derive dispatch inputs from the cursor and retained closure resources. -/
theorem LoopInput.of_resources
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet body base : BitVec 64} {index count : Nat} {m0 : Mem} {before : Config}
    (entry : ExecSeqAllocatorEntry .closureBody g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (cursor : ExecSeqClosureCursor before.σ.mem phiF env (s :: ss)
      sp aRet body base index count before.σ.regs.get?)
    (resources : ExecSeqClosureResources A SL shared body before.σ.regs.get?) :
    ∃ interp, LoopInput N A SL phiF shared st d env s ss
      body base sp aRet interp index count before := by
  have ready := entry.entry.ready (by simp)
  obtain ⟨p, head⟩ := ready.head_ground.facts
  obtain ⟨interp, interpReg, _, _⟩ := head.call
  have suffix := entry.closureSuffix cursor
  obtain ⟨_, cell, _⟩ := suffix.head
  have domain := SharedReadDomain.of_immutable entry.allocator.heap.immutable
  have baseGeom := AstReadGeometry.of_domain domain resources.baseCovered (by decide)
  have cellGeom := AstReadGeometry.of_domain domain cell.covered (by decide)
  have stackOK := head.stackOK
  have stackRam := ready.stack_ram
  have ret : aRet.toNat = sp.toNat + 144 := by
    rw [cursor.retSlot, BitVec.toNat_add]
    change (sp.toNat + 144) % 2^64 = sp.toNat + 144
    exact Nat.mod_eq_of_lt (by have := stackOK.2.1; omega)
  have retStack := head.ground.aret.inSL
  have stackWin := ready.stack_win
  have codeOff := head.ground.eval_call.image.stack_disjoint
    (lo := 0x80003164) (hi := 0x80003fe0) (by decide) (by decide)
  refine ⟨interp,
    { geometry :=
        { bodyLo := baseGeom.ram_lo, bodyHi := baseGeom.ram_hi
          bodyHtif := by
            have h : body.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ body.toNat + 8 :=
              baseGeom.htif
            exact h.imp id (fun h => by omega)
          cellLo := cellGeom.ram_lo, cellHi := cellGeom.ram_hi
          cellHtif := cellGeom.htif.imp id (fun h => by omega)
          stackLo := by have := stackOK.1; omega
          stackHi := by omega
          stackHtif := by have := stackOK.1; omega
          stackAlign := by have := stackOK.2.2; omega
          codeOff := by have := stackOK.1; omega }
      registers := ⟨cursor.bodyReg, cursor.indexReg, cursor.spReg, interpReg, cursor.envReg, trivial⟩
      baseRead := cursor.baseRead, suffix := suffix, retSlot := cursor.retSlot
      stackWrite := by have := stackOK.1; omega
      stackOK := stackOK, storeBodies := head.storeBodies
      spill9 := resources.spill9, spill20 := resources.spill20, spill21 := resources.spill21
      baseCovered := resources.baseCovered
      bodyCount := cursor.countRead
      countCovered := resources.countCovered
      remaining := by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using cursor.remaining
      countBound := cursor.countBound, arenaBelow := resources.arenaBelow
      bodyLo := resources.bodyLo, bodyHi := resources.bodyHi
      bodyWin := resources.bodyWin, bodyAlign := resources.bodyAlign }⟩


/-- Derive dispatch and continuation inputs from the actual cursor and owned header.
The closure caller supplies body alignment, its HTIF side, and saved registers. -/
theorem LoopInput.of_cursor
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss all : List Stmt}
    {sp aRet body base : BitVec 64} {index count : Nat} {m0 : Mem} {before : Config}
    (entry : ExecSeqAllocatorEntry .closureBody g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (cursor : ExecSeqClosureCursor before.σ.mem phiF env (s :: ss)
      sp aRet body base index count before.σ.regs.get?)
    (header : StmtReprWithin before.σ.mem shared body.toNat (.block all))
    (bodyWin : tohostAddr + 8 ≤ body.toNat + 16) (bodyAlign : body.toNat % 4 = 0)
    (arenaBelow : A.hi ≤ SL.lo)
    (spill9 : ∃ v, before.σ.regs.get? Register.x9 = some v)
    (spill20 : ∃ v, before.σ.regs.get? Register.x20 = some v)
    (spill21 : ∃ v, before.σ.regs.get? Register.x21 = some v) :
    ∃ interp, LoopInput N A SL phiF shared st d env s ss
      body base sp aRet interp index count before := by
  have domain := SharedReadDomain.of_immutable entry.allocator.heap.immutable
  exact LoopInput.of_resources entry cursor
    (ExecSeqClosureResources.of_header domain header arenaBelow bodyWin bodyAlign
      spill9 spill20 spill21)

/-- Select every loop input from the owned nonempty sequence entry. -/
theorem LoopInput.of_entry
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St}
    {s : Stmt} {ss : List Stmt} {sp aRet : BitVec 64} {m0 : Mem} {before : Config}
    (entry : ExecSeqAllocatorEntry .closureBody g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before) :
    ∃ body base interp index count,
      LoopInput N A SL phiF shared st d env s ss body base sp aRet interp index count before := by
  obtain ⟨body, base, index, count, cursor⟩ := (entry.entry.ready (by simp)).cursor.closure
  obtain ⟨stored, storedReg, resources⟩ := entry.closureResources rfl (by simp)
  have same : stored = body := Option.some.inj (storedReg.symm.trans cursor.bodyReg)
  subst stored
  obtain ⟨interp, input⟩ := LoopInput.of_resources entry cursor resources
  exact ⟨body, base, interp, index, count, input⟩

#print axioms LoopInput.of_resources
#print axioms LoopInput.of_cursor
#print axioms LoopInput.of_entry

end SeqClosureDispatch

#print axioms ExecSeqAllocatorEntry.closureSuffix

end Vsa.Sim
