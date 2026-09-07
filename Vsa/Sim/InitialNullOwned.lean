import Vsa.Sim.InitialNullRun
import Vsa.Sim.Code.FixedImage_Value_null

namespace Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Alloc

/-- Null-slot writes remain within the already tracked interpreter prefix. -/
theorem InitialNullFacts.preservation
    {before middle after : Config} {inp : BitVec 64} {N : NativeAddrs}
    {phiC : Addr → Nat} (P : ReadyLandingFacts inp before middle)
    (H : InitialNullFacts middle after N phiC) :
    ReadyLandingFacts inp before after := by
  refine
    { outside_prefix := ?_
      output := ?_
      run_code := ?_
      htif_payload := (H.frame Register.htif_payload_writes
        (by decide) (by decide) (by decide)).trans P.htif_payload
      mem_extends := P.mem_extends.trans H.mem_extends
      return_latch := (H.frame Register.x21
        (by decide) (by decide) (by decide)).trans P.return_latch }
  · intro k hk
    apply (P.outside_prefix k hk).trans
    apply H.outside k
    intro hw
    apply hk
    left
    change 0x87fffc50 ≤ k ∧ k < 0x87fffd00
    omega
  · unfold Vsa.Machine.output
    rw [H.output]
    exact P.output
  · apply loaded_interp_run_of_agree middle.σ.mem after.σ.mem P.run_code
    intro k hlo hhi
    exact H.outside k (by omega)

/-- The actual result-slot call preserves an arbitrary fixed read domain. -/
theorem InitialNullFacts.shared_agree
    {before after : Config} {N : NativeAddrs} {phiC : Addr → Nat}
    {shared : Nat → Prop} (H : InitialNullFacts before after N phiC)
    (D : SharedReadDomain LayoutInstance.stackSL shared) :
    AgreeP shared before.σ.mem after.σ.mem := by
  apply D.agree_stack
  intro k hk
  apply H.outside k
  intro hw
  apply hk
  change 0x87800000 ≤ k ∧ k < 0x88000000
  omega

/-- Reached initialization retains its dispatch witness and the actual call frame. -/
structure OwnedInitialNullFacts (inp : BitVec 64) (stmts count aStmt : Nat)
    (before dispatch after : Config) (s : Stmt) (ss : List Stmt)
    (N : NativeAddrs) (A : Arena) (phiF phiC : Addr → Nat)
    (D : RuntimeOwnership.InitialOwnershipData) : Prop extends
    ReadySegFacts inp before before after 0x80004460#64,
    ReadyRuntimeFacts after stmts count (s :: ss) N A phiF phiC D where
  entered : OwnedInitialDispatchFacts inp stmts count aStmt before dispatch s ss
    N A phiF phiC D
  call : InitialNullFacts dispatch after N phiC

/-- The live initial boundary executes dispatch, initializes the result, and returns. -/
theorem readyInitialNull_owned
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {s : Stmt} {ss : List Stmt} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A phiF phiC aLeft)
    (hp : ProgramRepr c.σ.mem stmts count (s :: ss)) :
    ∃ dispatch after aStmt D,
      OwnedInitialNullFacts inp stmts count aStmt c dispatch after s ss N A phiF phiC D := by
  obtain ⟨dispatch, aStmt, D, H⟩ := readyInitialDispatch_owned F hp
  have ht : Code.FixedTextLoaded dispatch.σ.mem := by
    have hinp : inp = 0x87fffe10#64 := F.interp_local
    subst inp
    exact H.preservation.text_image F.text_image
  obtain ⟨after, C⟩ := initialValueNull_run dispatch N phiC H.good H.pc H.sp
    H.minstret H.tick H.preservation.run_code ht.Value_nullLoaded
  have P := C.preservation H.preservation
  exact ⟨dispatch, after, aStmt, D,
    ⟨H.run.trans C.run, C.pc, C.good, C.tick, C.minstret, P⟩,
    P.runtime_owned F hp H.initial, H, C⟩

#print axioms InitialNullFacts.preservation
#print axioms InitialNullFacts.shared_agree
#print axioms readyInitialNull_owned
end Vsa.Sim

namespace Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Alloc

variable {inp : BitVec 64} {stmts count aStmt : Nat} {before dispatch after : Config}
  {s : Stmt} {ss : List Stmt} {N : NativeAddrs} {A : Arena}
  {phiF phiC : Addr → Nat} {D : RuntimeOwnership.InitialOwnershipData}

/-- Result initialization preserves the interpreter's four saved argument words. -/
theorem OwnedInitialNullFacts.saved
    (H : OwnedInitialNullFacts inp stmts count aStmt before dispatch after s ss N A phiF phiC D) :
    InterpSpillReads after.σ.mem inp (BitVec.ofNat 64 stmts) (BitVec.ofNat 64 count) 0#64 :=
  H.entered.saved.transport (fun k hk => H.call.outside k (by omega))

/-- The selected statement remains in s1 after the helper returns. -/
theorem OwnedInitialNullFacts.statement
    (H : OwnedInitialNullFacts inp stmts count aStmt before dispatch after s ss N A phiF phiC D) :
    after.σ.regs.get? Register.x9 = some (BitVec.ofNat 64 aStmt) :=
  (H.call.frame Register.x9 (by decide) (by decide) (by decide)).trans H.entered.statement

/-- The helper retains the concrete interpreter stack pointer. -/
theorem OwnedInitialNullFacts.sp
    (H : OwnedInitialNullFacts inp stmts count aStmt before dispatch after s ss N A phiF phiC D) :
    after.σ.regs.get? Register.x2 = some (0x87fffc50#64 : BitVec 64) :=
  (H.call.frame Register.x2 (by decide) (by decide) (by decide)).trans H.entered.sp

/-- The selected AST pointer and its exact fields survive the result-slot writes. -/
theorem OwnedInitialNullFacts.access
    (H : OwnedInitialNullFacts inp stmts count aStmt before dispatch after s ss N A phiF phiC D) :
    StmtReadAccess after.σ.mem LayoutInstance.stackSL D.shared stmts aStmt s := by
  have hag : AgreeP D.shared dispatch.σ.mem after.σ.mem :=
    H.call.shared_agree (.of_immutable H.entered.heap.immutable)
  have R := H.entered.access
  exact ⟨⟨(R.pointer.covered.read64_eq hag).symm.trans R.pointer.read,
    R.pointer.covered, R.pointer.target.transport hag⟩, R.slotGeometry, R.fields⟩

#print axioms OwnedInitialNullFacts.saved
#print axioms OwnedInitialNullFacts.statement
#print axioms OwnedInitialNullFacts.sp
#print axioms OwnedInitialNullFacts.access
end Vsa.Sim
