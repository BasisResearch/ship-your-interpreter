import Vsa.Sim.SeqInterpLoopStep

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The owned suffix is located at the interpreter's actual cursor register. -/
theorem ExecSeqAllocatorEntry.interpSuffix
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet cursor finish : BitVec 64} {m0 : Mem} {before : Config}
    (entry : ExecSeqAllocatorEntry .interpRun g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (C : ExecSeqInterpCursor before.σ.mem (s :: ss) sp aRet cursor finish before.σ.regs.get?) :
    SeqSuffixOwned before.σ.mem shared SL A sp aRet d cursor.toNat (s :: ss) := by
  obtain ⟨a, selected, suffix⟩ := entry.suffix (by simp)
  cases selected with
  | @interpRun actual actualReg =>
    have same : actual = cursor := Option.some.inj (actualReg.symm.trans C.cursorReg)
    subst actual
    exact suffix

namespace SeqInterpDispatch

/-- Derive every loop input from the represented cursor and retained interpreter. -/
theorem LoopInput.of_resources
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet cursor finish interp : BitVec 64} {m0 : Mem} {before : Config}
    (entry : ExecSeqAllocatorEntry .interpRun g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (C : ExecSeqInterpCursor before.σ.mem (s :: ss) sp aRet cursor finish before.σ.regs.get?)
    (saved : read64 before.σ.mem sp.toNat = some interp.toNat)
    (R : ExecSeqInterpResources A SL sp aRet interp before.σ.regs.get?) :
    LoopInput A SL phiF shared st d env s ss sp aRet cursor finish interp before := by
  have ready := entry.entry.ready (by simp)
  obtain ⟨p, head⟩ := ready.head_ground.facts
  obtain ⟨actual, actualSaved, environment, _⟩ := head.call
  have same : actual = interp := BitVec.eq_of_toNat_eq
    (Option.some.inj (actualSaved.symm.trans saved))
  subst actual
  have suffix := entry.interpSuffix C
  obtain ⟨_, cell, _⟩ := suffix.head
  have domain := SharedReadDomain.of_immutable entry.allocator.heap.immutable
  have cellGeom := AstReadGeometry.of_domain domain cell.covered (by decide)
  have stack := head.stackOK
  have ram := ready.stack_ram
  have win := ready.stack_win
  have retStack := head.ground.aret.inSL
  have ret : (sp + 88#64).toNat = sp.toNat + 88 := by
    rw [BitVec.toNat_add]
    change (sp.toNat + 88) % 2^64 = sp.toNat + 88
    exact Nat.mod_eq_of_lt (by have := stack.2.1; omega)
  have retBounds : SL.lo ≤ sp.toNat + 88 ∧ sp.toNat + 112 ≤ SL.hi := by
    rw [C.retSlot, ret] at retStack
    exact retStack
  have spLo := stack.1
  have spAlign := stack.2.2
  have interpAbove := R.interpAbove
  have htifAddr : tohostAddr = 0x8001ad00 := rfl
  exact
    { geometry :=
        { head :=
            { stackLo := by omega, stackHi := by omega, stackHtif := Or.inr (by omega)
              cursorLo := cellGeom.ram_lo, cursorHi := cellGeom.ram_hi
              cursorHtif := cellGeom.htif.imp id (fun h => by omega) }
          args :=
            { stackLo := by omega, stackHi := by omega, stackHtif := Or.inr (by omega)
              interpLo := by omega, interpHi := R.interpHi, interpHtif := Or.inr (by omega) }
          result :=
            { align := by rw [ret]; omega
              lo := by rw [ret]; omega
              hi := by rw [ret]; omega
              win := by rw [ret]; omega
              code_disjoint := Or.inr (by rw [ret]; omega) }
          savedOffRet := by rw [ret]; omega
          interpOffRet := by rw [← C.retSlot]; exact R.interpOffRet
          codeOffRet := Or.inr (by rw [ret]; omega) }
      registers := ⟨C.spReg, C.cursorReg, C.finishReg, R.breakReg, R.continueReg, trivial⟩
      script := C.script, saved := saved, environment := environment, suffix := suffix
      retSlot := C.retSlot, retWrite := head.ground.aret.inSL, stackOK := stack
      storeBodies := head.storeBodies, spill21 := R.spill21
      remaining := by simpa only [List.length_cons, Nat.add_comm] using C.remaining
      arenaBelow := R.arenaBelow, interpAbove := R.interpAbove }

/-- Select dispatch and continuation inputs directly from the owned entry. -/
theorem LoopInput.of_entry
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet : BitVec 64} {m0 : Mem} {before : Config}
    (entry : ExecSeqAllocatorEntry .interpRun g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before) :
    ∃ cursor finish interp,
      LoopInput A SL phiF shared st d env s ss sp aRet cursor finish interp before := by
  obtain ⟨cursor, finish, C⟩ := (entry.entry.ready (by simp)).cursor.interp
  obtain ⟨interp, saved, resources⟩ := entry.interpResources rfl (by simp)
  exact ⟨cursor, finish, interp, LoopInput.of_resources entry C saved resources⟩

#print axioms LoopInput.of_resources
#print axioms LoopInput.of_entry

end SeqInterpDispatch

#print axioms ExecSeqAllocatorEntry.interpSuffix

end Vsa.Sim
