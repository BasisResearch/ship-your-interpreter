import Vsa.Sim.ExecSimCommon
import Vsa.Sim.RuntimeAllocatorState
import Vsa.Sim.SeqSuffixOwned
import Vsa.Sim.AstReadGeometryCore
import Vsa.Sim.ExecSeqInterpResources
import Vsa.Sim.ExecSeqBlockResources

namespace Vsa.Sim

open LeanRV64DExecutable Vsa.Machine Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open RuntimeOwnership

/-- The array address selected by each physical sequence cursor. -/
inductive ExecSeqArrayAt (m : Mem)
    (regs : (R : Register) → Option (RegisterType R)) : ExecSeqCopy → Nat → Prop where
  | interpRun {cursor : BitVec 64} : regs .x8 = some cursor →
      ExecSeqArrayAt m regs .interpRun cursor.toNat
  | closureBody {body base : BitVec 64} {index : Nat} :
      regs .x16 = some body → regs .x8 = some (BitVec.ofNat 64 index) →
      read64 m (body.toNat + 8) = some base.toNat →
      ExecSeqArrayAt m regs .closureBody (base.toNat + 8 * index)
  | blockBody {block base : BitVec 64} {index : Nat} :
      regs .x8 = some block → regs .x16 = some (BitVec.ofNat 64 index) →
      read64 m (block.toNat + 8) = some base.toNat →
      ExecSeqArrayAt m regs .blockBody (base.toNat + 8 * index)

/-- Header coverage and caller registers retained around the closure loop.
The closure caller supplies them initially; the actual child frame and shared
footprint preserve them at each back edge. -/
structure ExecSeqClosureResources (A : Arena) (SL : StackLayout)
    (shared : Nat → Prop) (body : BitVec 64)
    (regs : (R : Register) → Option (RegisterType R)) : Prop where
  baseCovered : Covers shared (body.toNat + 8) 8
  countCovered : Covers shared (body.toNat + 16) 4
  arenaBelow : A.hi ≤ SL.lo
  bodyLo : 0x80000000 ≤ body.toNat
  bodyHi : body.toNat + 20 ≤ 0x100000000
  bodyWin : tohostAddr + 8 ≤ body.toNat + 16
  bodyAlign : body.toNat % 4 = 0
  spill9 : ∃ v, regs .x9 = some v
  spill20 : ∃ v, regs .x20 = some v
  spill21 : ∃ v, regs .x21 = some v

/-- The caller's owned block header supplies the closure read resources. -/
theorem ExecSeqClosureResources.of_header
    {A : Arena} {SL : StackLayout} {shared : Nat → Prop} {body : BitVec 64}
    {regs : (R : Register) → Option (RegisterType R)} {m : Mem} {ss : List Vsa.While.Stmt}
    (domain : SharedReadDomain SL shared)
    (header : StmtReprWithin m shared body.toNat (.block ss))
    (arenaBelow : A.hi ≤ SL.lo) (bodyWin : tohostAddr + 8 ≤ body.toNat + 16)
    (bodyAlign : body.toNat % 4 = 0)
    (spill9 : ∃ v, regs .x9 = some v) (spill20 : ∃ v, regs .x20 = some v)
    (spill21 : ∃ v, regs .x21 = some v) :
    ExecSeqClosureResources A SL shared body regs :=
  { baseCovered := header.fieldCovers (.word64 8) (by simp [stmtReadFields])
    countCovered := header.fieldCovers (.word32 16) (by simp [stmtReadFields])
    arenaBelow := arenaBelow
    bodyLo := (domain.stmt_field header (.word32 0) (by simp [stmtReadFields])).ram_lo
    bodyHi := (domain.stmt_field header (.word32 16) (by simp [stmtReadFields])).ram_hi
    bodyWin := bodyWin, bodyAlign := bodyAlign
    spill9 := spill9, spill20 := spill20, spill21 := spill21 }

/-- A sequence entry retains the allocator and every remaining child at its cursor. -/
structure ExecSeqAllocatorEntry
    (copy : ExecSeqCopy) (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop) (credits : Nat)
    (st : Vsa.While.St) (d env : Nat) (ss : List Stmt)
    (sp aRet : BitVec 64) (m0 : Mem) (c : Config) : Prop where
  entry : ExecSeqEntryI copy g N A SL phiF phiC st d env ss sp aRet m0 c
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits st.store c.σ.mem
  suffix : ss ≠ [] → ∃ a, ExecSeqArrayAt c.σ.mem c.σ.regs.get? copy a ∧
    SeqSuffixOwned c.σ.mem shared SL A sp aRet d a ss
  closureResources : copy = .closureBody → ss ≠ [] → ∃ body,
    c.σ.regs.get? Register.x16 = some body ∧
      ExecSeqClosureResources A SL shared body c.σ.regs.get?
  interpResources : copy = .interpRun → ss ≠ [] →
    ExecSeqInterpResources.At A SL sp aRet c.σ.mem c.σ.regs.get?
  blockResources : copy = .blockBody → ss ≠ [] →
    ExecSeqBlockResources.At A SL shared sp aRet c.σ.regs.get?
  gp : c.σ.regs.get? Register.x3 = some gpv

#print axioms ExecSeqClosureResources.of_header

end Vsa.Sim
