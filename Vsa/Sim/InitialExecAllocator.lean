import Vsa.Sim.InitialExecRuntime
import Vsa.Sim.ExecAllocatorAt

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Alloc
open RuntimeOwnership

/-- Initial-prefix execution followed by a statement return at its actual entry ghosts.
The statement's memory frame is relative to `entered`, after the setup writes. -/
structure InitialExecAllocatorRun (N : NativeAddrs) {A : Arena} {headroom maxReq : Nat}
    (M : MallocContract A LayoutInstance.stackSL
      (BitVec.ofNat 64 LayoutInstance.gpEntry) headroom maxReq)
    (phiF phiC : Addr → Nat) (shared : Nat → Prop) (reserve : Nat)
    (final : Vsa.While.St) (status : Status) (before entered returned : Config) : Prop where
  run : Steps before returned
  result : ExecAllocatorReturn entered.σ.regs.get? N M phiF phiC initSt.store.frames.size
    initSt.store.closures.size shared reserve final status
    0x87fffc50#64 0x80004478#64 0x87fffca8#64 entered.σ.mem returned

variable {inp : BitVec 64} {stmts count aStmt : Nat}
  {before dispatch initialized after : Config} {s : Stmt} {ss : List Stmt}
  {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
  {D : InitialOwnershipData} {aLeft headroom maxReq credits : Nat}
  {M : MallocContract A LayoutInstance.stackSL
    (BitVec.ofNat 64 LayoutInstance.gpEntry) headroom maxReq}

/-- The actual setup and null call preserve the initialized allocator global pointer. -/
theorem OwnedInitialExecFacts.allocator_gp
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) :
    after.σ.regs.get? Register.x3 = some (BitVec.ofNat 64 LayoutInstance.gpEntry) :=
  H.loop_register (by decide) (by decide) (by decide) (by decide)
    (gholds_lookup _ H.nullReturn.entered.keep
      (show lookupG 3 _ = some (BitVec.ofNat 64 LayoutInstance.gpEntry) from rfl))

/-- Assemble the first allocator entry at the reached statement JAL.
The initial ledger must supply allocator consistency, physical capacity, and placement;
the source representation must supply hereditary ground, stack and body bounds,
and shared read geometry. The executed prefix transports allocator metadata. -/
theorem OwnedInitialExecFacts.execAllocatorEntry
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D)
    (F : LayoutInstance.InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft)
    (L : AllocLedger A LayoutInstance.stackSL
      (BitVec.ofNat 64 LayoutInstance.gpEntry) headroom maxReq M)
    (ainv : AInvAt M (BitVec.ofNat 64 LayoutInstance.gpEntry) before.σ.mem D.exts)
    (capacity : ResourceBudget A maxReq D.exts credits)
    (placement : AllocationReserve A before.σ.mem D.exts maxReq credits)
    (ground : ExecGround after.σ.mem LayoutInstance.stackSL A 0x87fffc50#64
      0x87fffca8#64 (BitVec.ofNat 64 aStmt).toNat s)
    (stack : StackOK LayoutInstance.stackSL 0x87fffc50#64
      (s.stackNeed + maxCallDepth * perCallBudget + 1088))
    (bodies : Stmt.bodiesBound perCallBudget s = true)
    (geometry : SharedReadGeom D.shared LayoutInstance.stackSL) :
    ExecAllocatorEntry after.σ.regs.get? N M phiF phiC D.allocations D.exts D.shared
      credits initSt 0 0 s 0x87fffc50#64 0x80004478#64 inp (BitVec.ofNat 64 aStmt)
      (BitVec.ofNat 64 (phiF 0)) 0x87fffca8#64 after.σ.mem after := by
  have entry := H.execRuntimeEntry F ground stack bodies geometry
  have prefixFrame : ∀ k,
      ¬ (LayoutInstance.stackSL.lo ≤ k ∧ k < LayoutInstance.stackSL.hi) →
      before.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    apply H.preservation.outside_prefix k
    rw [F.interp_local]
    change ¬ ((0x87fffc50 ≤ k ∧ k < 0x87fffd00) ∨
      (0x87fffe20 ≤ k ∧ k < 0x87fffe90))
    change ¬ (0x87800000 ≤ k ∧ k < 0x88000000) at hk
    omega
  have preserved : AInvAt M (BitVec.ofNat 64 LayoutInstance.gpEntry) after.σ.mem D.exts :=
    L.ainvAt_transport_offStack (Nat.le_refl LayoutInstance.stackSL.hi) ainv prefixFrame
  have placed : AllocationReserve A after.σ.mem D.exts maxReq credits :=
    placement.after_stack prefixFrame (by
      intro k hk
      change ¬ (0x87800000 ≤ 0x8001ad20 + k ∧ 0x8001ad20 + k < 0x88000000)
      omega) L.arena_stack
  exact
    { entry := entry.entry, ast := entry.ast, gp := H.allocator_gp
      allocator :=
        { heap := H.heap, repr := H.store, arrays := H.arrays, geometry := geometry
          parents := storeInvariant_initSt.parents, ainv := preserved, budget := capacity
          reserve := placed } }

/-- Consume the first allocator entry with the exact statement supplier.
The supplier, initial allocator ledger, consistency, capacity, placement, and source resource
facts remain premises; this does not construct them from Loaded. -/
theorem OwnedInitialExecFacts.run_allocator
    {final : Vsa.While.St} {status : Status} {cost request reserve : Nat}
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D)
    (F : LayoutInstance.InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft)
    (L : AllocLedger A LayoutInstance.stackSL
      (BitVec.ofNat 64 LayoutInstance.gpEntry) headroom maxReq M)
    (ainv : AInvAt M (BitVec.ofNat 64 LayoutInstance.gpEntry) before.σ.mem D.exts)
    (capacity : ResourceBudget A maxReq D.exts (cost + reserve))
    (placement : AllocationReserve A before.σ.mem D.exts maxReq (cost + reserve))
    (ground : ExecGround after.σ.mem LayoutInstance.stackSL A 0x87fffc50#64
      0x87fffca8#64 (BitVec.ofNat 64 aStmt).toNat s)
    (stack : StackOK LayoutInstance.stackSL 0x87fffc50#64
      (s.stackNeed + maxCallDepth * perCallBudget + 1088))
    (bodies : Stmt.bodiesBound perCallBudget s = true)
    (geometry : SharedReadGeom D.shared LayoutInstance.stackSL)
    (supplier : ExecAllocatorAt N initSt 0 0 s final status cost request)
    (requestBound : request ≤ maxReq) :
    ∃ returned, InitialExecAllocatorRun N M phiF phiC D.shared reserve final status
      before after returned := by
  obtain ⟨returned, steps, result⟩ := supplier.run after.σ.regs.get? A LayoutInstance.stackSL
    (BitVec.ofNat 64 LayoutInstance.gpEntry) headroom maxReq M L requestBound
    phiF phiC D.allocations D.exts D.shared reserve 0x87fffc50#64 0x80004478#64
    inp (BitVec.ofNat 64 aStmt) (BitVec.ofNat 64 (phiF 0)) 0x87fffca8#64
    after.σ.mem after (H.execAllocatorEntry F L ainv capacity placement ground stack bodies geometry)
  exact ⟨returned, H.run.trans steps, result⟩

#print axioms OwnedInitialExecFacts.allocator_gp
#print axioms OwnedInitialExecFacts.execAllocatorEntry
#print axioms OwnedInitialExecFacts.run_allocator

end Vsa.Sim
