import Vsa.Sim.SeqBlockDispatch
import Vsa.Sim.SeqSuffixStack
import Vsa.Sim.ExecSeqAllocatorEntry
import Vsa.Sim.AllocatorEntry
import Vsa.Sim.AstReadGeometry
import Vsa.Sim.Code.FixedImage_Exec_stmt
import Vsa.Sim.MemPresence

namespace Vsa.Sim.SeqBlockDispatch

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Owned cursor and register inputs for the block's statement dispatch. -/
structure Input (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF : Addr → Nat) (shared : Nat → Prop) (st : Vsa.While.St) (d env : Nat)
    (s : Stmt) (ss : List Stmt) (block base sp aRet interp : BitVec 64)
    (index : Nat) (before : Config) : Prop where
  geometry : Geometry block base sp index
  registers : GHolds before.σ (input block sp interp (BitVec.ofNat 64 (phiF env)) aRet index)
  baseRead : read64 before.σ.mem (block.toNat + 8) = some base.toNat
  suffix : SeqSuffixOwned before.σ.mem shared SL A sp aRet d (base.toNat + 8 * index) (s :: ss)
  stackWrite : SL.lo ≤ sp.toNat + 8 ∧ sp.toNat + 16 ≤ SL.hi
  stackOK : StackOK SL sp (176 + 1088)
  storeBodies : StoreBodiesBound st.store perCallBudget
  spill20 : ∃ v, before.σ.regs.get? Register.x20 = some v
  spill21 : ∃ v, before.σ.regs.get? Register.x21 = some v

/-- The actual child entry retains the owned suffix and saved index. -/
structure OwnedPost
    (N : NativeAddrs) {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (st : Vsa.While.St) (d env : Nat)
    (s : Stmt) (ss : List Stmt) (block base sp aRet interp stmt : BitVec 64)
    (index : Nat) (before after : Config) : Prop where
  entry : ExecAllocatorEntry after.σ.regs.get? N M phiF phiC alloc exts shared credits
    st d env s sp 0x800041c8#64 interp stmt (BitVec.ofNat 64 (phiF env)) aRet after.σ.mem after
  dispatch : Post block sp interp (BitVec.ofNat 64 (phiF env)) aRet stmt index before after
  suffix : SeqSuffixOwned after.σ.mem shared SL A sp aRet d (base.toNat + 8 * index) (s :: ss)
  agreement : AgreeP shared before.σ.mem after.σ.mem
  frame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = after.σ.mem[k]?
  presence : MemExtends before.σ.mem after.σ.mem

/-- Execute dispatch and construct the statement contract at its reached state. -/
theorem owned
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {block base sp aRet interp : BitVec 64} {index : Nat} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (entry : ExecSeqAllocatorEntry .blockBody g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (I : Input N A SL phiF shared st d env s ss block base sp aRet interp index before) :
    ∃ after stmt, Steps before after ∧
      OwnedPost N M phiF phiC alloc exts shared credits st d env s ss
        block base sp aRet interp stmt index before after := by
  obtain ⟨p, cell, ground⟩ := I.suffix.head
  have tagBefore := (SharedReadDomain.of_immutable entry.allocator.heap.immutable).stmt_field
    cell.target (.word32 0) (by simp [stmtReadFields])
  have small : p < 2^64 := by
    have bound : p + 4 ≤ 0x100000000 := tagBefore.ram_hi
    omega
  have pn : (BitVec.ofNat 64 p).toNat = p := Nat.mod_eq_of_lt small
  have ready := entry.entry.ready (by simp)
  obtain ⟨after, steps, post⟩ := run block sp interp (BitVec.ofNat 64 (phiF env)) aRet base
    (BitVec.ofNat 64 p) index before I.geometry entry.entry.good entry.entry.tick entry.entry.pc
    entry.entry.minstret I.registers ready.code I.baseRead (by rw [pn]; exact cell.read)
  have frame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    rw [post.memory]
    apply (writeLog_out before.σ.mem [(sp.toNat + 8, 8, BitVec.ofNat 64 index)] k ?_).symm
    simp only [OutL, and_true]
    have := I.stackWrite
    omega
  have presence : MemExtends before.σ.mem after.σ.mem := by
    rw [post.memory]
    exact memExtends_writeLog _ _
  have agreement : AgreeP shared before.σ.mem after.σ.mem :=
    fun k hk => frame k ((entry.allocator.runtime L).shared_off_stack hk)
  have allocator := entry.allocator.after_stack L frame
  have ast := cell.target.transport agreement
  have ground' := ground.transport_stack presence frame
  have tag := (SharedReadDomain.of_immutable allocator.heap.immutable).stmt_field
    ast (.word32 0) (by simp [stmtReadFields])
  have image := ground'.ground.eval_call.image
  have codeOff := image.stack_disjoint (lo := execStmtEntry) (hi := execStmtEnd)
    (by decide) (by decide)
  have spLo : SL.lo ≤ sp.toNat := by have := I.stackOK.1; omega
  obtain ⟨a0, a1, a2, a3, spReg, blockReg, indexReg, interpReg, retReg, envReg, _⟩ := post.args
  refine ⟨after, BitVec.ofNat 64 p, steps,
    { entry :=
        { entry :=
            { good := post.good, tick := post.tick, pc := post.pc
              a0 := a0, a1 := a1, a2 := a2, envPtr := rfl, a3 := a3
              ra := post.ra, ra_align := by decide, spReg := spReg
              stackOK := I.stackOK, stackBudget := ground'.stackBudget
              stmt_bodies := ground'.bodies, store_bodies := I.storeBodies
              minstret := post.minstret, mem := rfl, code := image.text.Exec_stmtLoaded
              stmt := by rw [pn]; exact ground'.stmt
              store := allocator.repr, env_valid := ready.env_valid
              store_survives := fun _ hm => ((allocator.runtime L).after_stack hm).repr
              out := by simpa [OutRepr, output, post.output] using entry.entry.out
              frame := fun _ _ => rfl
              code_stack_disjoint := by have := I.stackWrite; omega
              stack_ram := ready.stack_ram, stack_win := ready.stack_win
              stmt_stack_disjoint := by
                have ht := tag.stack_disjoint (by have := I.stackWrite; omega)
                change p + 4 ≤ SL.lo ∨ SL.hi ≤ p at ht
                rw [pn]
                have := I.stackWrite
                omega
              stmt_ram := by rw [pn]; exact ⟨tag.ram_lo, tag.ram_hi⟩
              stmt_win := by rw [pn]; exact tag.htif
              spill_defined := ⟨⟨_, blockReg⟩, ⟨_, interpReg⟩, ⟨_, retReg⟩, ⟨_, envReg⟩⟩
              envset_defined := ⟨?_, ?_⟩
              ground := by rw [pn]; exact ground'.ground }
          allocator := allocator
          ast := by rw [pn]; exact ast
          gp := (post.frame .x3 (by decide)).trans entry.gp }
      dispatch := post
      suffix := I.suffix.transport_stack presence frame agreement
      agreement := agreement, frame := frame, presence := presence }⟩
  · obtain ⟨v, hv⟩ := I.spill20
    exact ⟨v, (post.frame .x20 (by decide)).trans hv⟩
  · obtain ⟨v, hv⟩ := I.spill21
    exact ⟨v, (post.frame .x21 (by decide)).trans hv⟩

#print axioms owned

end Vsa.Sim.SeqBlockDispatch
