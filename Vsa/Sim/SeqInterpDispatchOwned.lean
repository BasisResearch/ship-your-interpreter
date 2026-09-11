import Vsa.Sim.SeqInterpDispatch
import Vsa.Sim.SeqSuffixStack
import Vsa.Sim.ExecSeqAllocatorEntry
import Vsa.Sim.AllocatorEntry
import Vsa.Sim.AstReadGeometry
import Vsa.Sim.Code.FixedImage_Exec_stmt
import Vsa.Sim.Code.FixedImage_Value_null
import Vsa.Sim.EnvGetSpec3

namespace Vsa.Sim.SeqInterpDispatch

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Actual loop registers, saved arguments, and owned statement suffix. -/
structure Input (A : Arena) (SL : StackLayout) (phiF : Addr → Nat)
    (shared : Nat → Prop) (st : Vsa.While.St) (d env : Nat) (s : Stmt) (ss : List Stmt)
    (sp aRet cursor finish interp : BitVec 64) (before : Config) : Prop where
  geometry : Geometry sp cursor interp
  registers : GHolds before.σ [(2, sp), (8, cursor), (18, finish), (19, 3#64), (20, 1#64)]
  script : read64 before.σ.mem (sp.toNat + 8) = some 0
  saved : read64 before.σ.mem sp.toNat = some interp.toNat
  environment : read64 before.σ.mem interp.toNat = some (phiF env)
  suffix : SeqSuffixOwned before.σ.mem shared SL A sp aRet d cursor.toNat (s :: ss)
  retSlot : aRet = sp + 88#64
  retWrite : SL.lo ≤ aRet.toNat ∧ aRet.toNat + 24 ≤ SL.hi
  stackOK : StackOK SL sp (176 + 1088)
  storeBodies : StoreBodiesBound st.store perCallBudget
  spill21 : ∃ v, before.σ.regs.get? Register.x21 = some v

/-- The reached statement entry and suffix share the actual dispatch write frame. -/
structure OwnedPost
    (N : NativeAddrs) {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (st : Vsa.While.St) (d env : Nat)
    (s : Stmt) (ss : List Stmt) (sp aRet cursor interp stmt : BitVec 64)
    (before after : Config) : Prop where
  entry : ExecAllocatorEntry after.σ.regs.get? N M phiF phiC alloc exts shared credits
    st d env s sp 0x80004478#64 interp stmt (BitVec.ofNat 64 (phiF env)) aRet after.σ.mem after
  dispatch : Post sp stmt interp (BitVec.ofNat 64 (phiF env)) N phiC before after
  suffix : SeqSuffixOwned after.σ.mem shared SL A sp aRet d cursor.toNat (s :: ss)
  agreement : AgreeP shared before.σ.mem after.σ.mem
  frame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = after.σ.mem[k]?
  presence : MemExtends before.σ.mem after.σ.mem

/-- Build the owned statement entry from the actual loop-head execution. -/
theorem owned
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet cursor finish interp : BitVec 64} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (entry : ExecSeqAllocatorEntry .interpRun g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (I : Input A SL phiF shared st d env s ss sp aRet cursor finish interp before) :
    ∃ after stmt, Steps before after ∧
      OwnedPost N M phiF phiC alloc exts shared credits st d env s ss
        sp aRet cursor interp stmt before after := by
  obtain ⟨p, cell, ground⟩ := I.suffix.head
  have tagBefore := (SharedReadDomain.of_immutable entry.allocator.heap.immutable).stmt_field
    cell.target (.word32 0) (by simp [stmtReadFields])
  have small : p < 2^64 := by
    have bound : p + 4 ≤ 0x100000000 := tagBefore.ram_hi
    omega
  have pn : (BitVec.ofNat 64 p).toNat = p := Nat.mod_eq_of_lt small
  have en : (BitVec.ofNat 64 (phiF env)).toNat = phiF env :=
    Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ I.environment)
  have ready := entry.entry.ready (by simp)
  obtain ⟨spBefore, cursorBefore, finishBefore, breakBefore, continueBefore, _⟩ := I.registers
  obtain ⟨after, steps, post⟩ := run sp cursor (BitVec.ofNat 64 p) interp
    (BitVec.ofNat 64 (phiF env)) N phiC before I.geometry entry.entry.good entry.entry.tick
    entry.entry.pc entry.entry.minstret ⟨spBefore, cursorBefore, trivial⟩ ready.code
    ground.ground.eval_call.image.text.Value_nullLoaded I.script
    (by rw [pn]; exact cell.read) I.saved (by rw [en]; exact I.environment)
  have frame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    apply post.outside k
    have bounds := I.retWrite
    rw [I.retSlot] at bounds
    omega
  have agreement : AgreeP shared before.σ.mem after.σ.mem :=
    fun k hk => frame k ((entry.allocator.runtime L).shared_off_stack hk)
  have allocator := entry.allocator.after_stack L frame
  have ast := cell.target.transport agreement
  have ground' := ground.transport_stack post.presence frame
  have domain := SharedReadDomain.of_immutable allocator.heap.immutable
  have tag := domain.stmt_field ast (.word32 0) (by simp [stmtReadFields])
  have image := ground'.ground.eval_call.image
  have stackBounds := ready.stack_ram
  have codeOff := image.stack_disjoint (lo := execStmtEntry) (hi := execStmtEnd)
    (by decide) (by decide)
  have stackLo := I.stackOK.1
  have stackHi := I.stackOK.2.1
  obtain ⟨a0, a1, a2, a3, spReg, stmtReg, _⟩ := post.args
  refine ⟨after, BitVec.ofNat 64 p, steps,
    { entry :=
        { entry :=
            { good := post.good, tick := post.tick, pc := post.pc
              a0 := a0, a1 := a1, a2 := a2, envPtr := rfl
              a3 := by rw [I.retSlot]; exact a3
              ra := post.ra, ra_align := by decide, spReg := spReg
              stackOK := I.stackOK, stackBudget := ground'.stackBudget
              stmt_bodies := ground'.bodies, store_bodies := I.storeBodies
              minstret := post.minstret, mem := rfl, code := image.text.Exec_stmtLoaded
              stmt := by rw [pn]; exact ground'.stmt
              store := allocator.repr, env_valid := ready.env_valid
              store_survives := fun _ hm => ((allocator.runtime L).after_stack hm).repr
              out := by simpa [OutRepr, output, post.output] using entry.entry.out
              frame := fun _ _ => rfl
              code_stack_disjoint := by omega
              stack_ram := stackBounds, stack_win := ready.stack_win
              stmt_stack_disjoint := by
                have ht := tag.stack_disjoint (by omega)
                change p + 4 ≤ SL.lo ∨ SL.hi ≤ p at ht
                rw [pn]
                omega
              stmt_ram := by rw [pn]; exact ⟨tag.ram_lo, tag.ram_hi⟩
              stmt_win := by rw [pn]; exact tag.htif
              spill_defined := ⟨⟨cursor, (post.frame .x8 (by decide)).trans cursorBefore⟩,
                ⟨_, stmtReg⟩, ⟨finish, (post.frame .x18 (by decide)).trans finishBefore⟩,
                ⟨3#64, (post.frame .x19 (by decide)).trans breakBefore⟩⟩
              envset_defined := ⟨⟨1#64, (post.frame .x20 (by decide)).trans continueBefore⟩, ?_⟩
              ground := by rw [pn]; exact ground'.ground }
          allocator := allocator, ast := by rw [pn]; exact ast
          gp := (post.frame .x3 (by decide)).trans entry.gp }
      dispatch := post, suffix := I.suffix.transport_stack post.presence frame agreement
      agreement := agreement, frame := frame, presence := post.presence }⟩
  obtain ⟨v, hv⟩ := I.spill21
  exact ⟨v, (post.frame .x21 (by decide)).trans hv⟩

#print axioms owned

end Vsa.Sim.SeqInterpDispatch
