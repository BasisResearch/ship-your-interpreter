import Vsa.Sim.TruthyCopy
import Vsa.Sim.rows.InitSomeReturnReady
import Vsa.Sim.ExecRetEpilogue

/-!
# `StmtChildArm` — the parametric in-frame call of a child statement

An `exec_stmt` loop arm calls `exec_stmt` recursively on a child statement
through a four-instruction prefix (`ld a1,off(s0); mv a3,s2; mv a2,s3;
mv a0,s1`) and a `jal` in the same 176-byte frame.  This file states that
call once over a descriptor: `dispatch_of_armState` lands the child's
`ExecEntry` with the parent `Carrier`; `exitKit_of_exit` recovers the parent
at the child's widened `ExecExitD`; `ExitKit.toRouteReady` hands the status
in `a0` to a reflected route (`TruthyCopy.route_of_ready`); the normal-exit
and return-propagation heads after a route are `normalExitPre_of_route` and
`retExit_of_route`.
-/

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) every `∃` here is the fixed StepObs site post
-- shape (`Cert.jal_site`), a saved-register witness inside a named-field structure, or
-- the reached-config existential of a run; all are consumed through named fields.

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

local notation "SpecSt" => Vsa.While.St

/-! ## The parent frame at an in-frame point

The facts a parent `exec_stmt` frame carries at any in-frame point after a
child returned: the ghost register image `gC`, and the memory-indexed AST,
code, store-survival, and saved-register facts at the current memory `mR`
with the current maps and source state.  Both child kits project it; routes,
copies, and the loop re-entry consume it. -/

/-- An in-frame `exec_stmt` arm that runs one child statement through
`jal exec_stmt` at the lowered frame `esp = sp - 176`. -/
structure StmtChildArm where
  /-- Arm entry PC; the prefix starts here. -/
  armPC : BitVec 64
  /-- The reflected prefix from `armPC` up to (excluding) the `jal`. -/
  seg : List BBlock
  /-- PC of `jal exec_stmt`. -/
  jalPC : BitVec 64
  /-- Decoded 21-bit `jal` immediate. -/
  jalImm : BitVec 21
  /-- The child pointer field offset inside the statement node. -/
  childOff : Nat

namespace StmtChildArm

/-- The load data of the prefix: the child pointer word. -/
def lds (D : StmtChildArm) (m : Mem) (aStmt : BitVec 64) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m (aStmt.toNat + D.childOff)]

/-- The reflected outcome of the prefix. -/
def out (D : StmtChildArm) (esp aStmt aInterp aRet aEnv : BitVec 64) (m : Mem) :
    SegEvalState :=
  evalBlocks D.seg
    (SegEvalState.init (EvalChildArm.regs esp aStmt aInterp aRet aEnv) (D.lds m aStmt))

/-! ## The decidable certificate -/

/-! ## The semantic certificate -/

/-! ## The prefix run -/

/-! ## The carrier -/

/-! ## The child exit -/

end StmtChildArm

/-! ## After a route -/

/-! ## The parent frame at an expression child's exit -/

/-! ## Memory bookkeeping across an iteration -/

/-- Memory change tolerated by the loop's exit: presence is preserved, and
outside the stack window and the arena only the retslot may differ. -/
def LoopFrame (SL : StackLayout) (A : Arena) (sp aRet : BitVec 64) (m m' : Mem) : Prop :=
  MemExtends m m' ∧
  ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ m'[a]? = m[a]?

namespace LoopFrame

theorem trans {SL : StackLayout} {A : Arena} {sp aRet : BitVec 64} {m m' m'' : Mem}
    (h1 : LoopFrame SL A sp aRet m m') (h2 : LoopFrame SL A sp aRet m' m'') :
    LoopFrame SL A sp aRet m m'' := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  intro a hstk hA
  rcases h2.2 a hstk hA with hr | heq
  · exact Or.inl hr
  · rcases h1.2 a hstk hA with hr' | heq'
    · exact Or.inl hr'
    · exact Or.inr (heq.trans heq')

end LoopFrame

end Vsa.Sim
