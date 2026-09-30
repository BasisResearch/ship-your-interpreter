import Vsa.Sim.EvalChildArm
import Vsa.Sim.PinW
import Vsa.Sim.BridgeSegFramed

/-!
# `TruthyCopy` — the parametric condition-copy and `value_truthy` seam

After a condition child returns, the `while`, `if`, and `for` arms all copy the
24-byte result from the sub-result slot to `esp+16`, call `value_truthy`, and
branch on its answer.  `WhileGeomSuppliers` closed this seam for `while` with
`0x80004050`-specific files.  This file states it ONCE over a descriptor
`TruthyCopy` attached to an `EvalChildArm`:

* `TruthyCopy.Cert D T` — decided facts (the reflected copy's fold, its
  write log as three `sd`s, the `jal value_truthy` site);
* `copyReady_of_exitKit` — from the child's exit kit, park at `value_truthy`;
* `truthyReturn_of_copyReady` — the helper returns with the truthiness bit;
* `route_of_truthyReturn` — run any reflected branch route from that return;
* `normalExitPre_of_route` — a route that ends at a `li a0,0` is a
  `NormalExitTailPre`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) the `∃` here are the fixed StepObs site post
-- (`Cert.jal_site`), reached-config existentials of runs, and saved-register witnesses
-- inside named-field structures; all consumed through named fields.

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

local notation "SpecSt" => Vsa.While.St

/-! ## The descriptor -/

/-- The copy-and-`value_truthy` seam of one condition arm. -/
structure TruthyCopy where
  /-- The reflected copy: three `ld` from the sub-result slot, `addi a0,sp,16`,
  three `sd` to `esp+16`; starts at the child's return PC. -/
  copySeg : List BBlock
  /-- PC of `jal value_truthy`. -/
  jalPC : BitVec 64
  /-- Decoded 21-bit `jal` immediate. -/
  jalImm : BitVec 21

namespace TruthyCopy

/-- The three total loads of the copy, from the arm's sub-result slot. -/
def lds (D : EvalChildArm) (m : Mem) (esp : BitVec 64) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m (esp.toNat + D.sretOff),
   EvalChildArm.wordLds8 m (esp.toNat + D.sretOff + 8),
   EvalChildArm.wordLds8 m (esp.toNat + D.sretOff + 16)]

/-- The reflected outcome of the copy. -/
def out (D : EvalChildArm) (T : TruthyCopy) (esp s0 s1 s2 s3 : BitVec 64) (m : Mem) :
    SegEvalState :=
  evalBlocks T.copySeg (SegEvalState.init (EvalChildArm.regs esp s0 s1 s2 s3) (lds D m esp))

/-! ## Byte-level facts about the copy -/

/-! ## Parked at `value_truthy` -/

/-! ## The helper's return -/

/-! ## A reflected branch route from the return -/

/-! ## A normal completion after a route -/

end TruthyCopy
end Vsa.Sim
