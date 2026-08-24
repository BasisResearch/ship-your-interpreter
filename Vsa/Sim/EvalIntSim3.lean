import Vsa.Sim.EvalIntSim2
import Vsa.Sim.EvalIntPilot
import Vsa.Sim.ReprSurvival
import Vsa.Sim.EvalSimCommon

/-!
# Layer 4 — M4 gate assembly: `EvalIntSimGoal` (part 3: blocks C, D, assembly)

Continues `EvalIntSim2.lean` (`blockA_ee` → `ArmEntry` at `0x80003408`):

* **Block C** (`blockC_ee`): the `EX_INT` arm + the `value_int` call.
  `ArmEntry` → `ld a1,8(a2)` (payload → `x11`) → `jal value_int` → the callee
  (via `value_int_spec`) → `j 0x800033ec`. Reaches `PreEpilogue`: PC at the
  shared epilogue `0x800033ec`, the sret buffer holding `ValueRepr (.int n)`, the
  four spill slots and `s1`/`sp`/`ra` intact, `eval_expr` still loaded, output
  invariant.

* **Block D** (`blockD_ee`): the shared epilogue.
  `PreEpilogue` → `ld ra,1080(sp); ld s0,1072(sp); ld s2,1056(sp); mv a0,s1;
  ld s1,1064(sp); addi sp,sp,1088; ret`. Restores `sp`, returns `a0 = sret`,
  PC → `r`.

* **`evalIntSimGoal_proof`**: `blockA_ee ≫ C ≫ D`, discharging every `EvalExit`
  field.

## Output threading (the retrofit payoff)

The `sailOutput`-invariance now flows end-to-end: `ArmEntry.out` (from `blockA_ee`),
`value_int_spec`'s `int_post` output field (through the callee), and the epilogue
`stepObs_*` `.out` chains. No `EX_INT` step touches the HTIF console, so
`c'.σ.sailOutput = c.σ.sailOutput` and `EvalExit.out` follows from `EvalEntry.out`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Address arithmetic for the epilogue restores (`(sp-1088)+off` slots) -/

theorem restore_addr (sp : BitVec 64) (off : BitVec 12) (k : Nat)
    (hoff : (sign_extend (m := 64) off : BitVec 64).toNat = 1088 - k)
    (hk : k ≤ 1088) (hsp : 1088 ≤ sp.toNat) :
    ((sp - 1088#64) + sign_extend (m := 64) off).toNat = sp.toNat - k :=
  spill_addr sp off k hoff hk hsp

/-! ## `PreEpilogue` — the machine state at the shared epilogue `0x800033ec`

After block C: `value_int` has filled the sret buffer with `ValueRepr (.int n)`,
`s1 = sret`, `sp = sp-1088`, `ra = r` (all preserved by `value_int`'s `NotWrittenV`
frame). The four spilled callee-saved slots `[sp-8], [sp-16], [sp-24], [sp-32]`
still hold their entry values (disjoint from the sret write). `eval_expr` loaded.
Output invariant (`= out0`). -/
def PreEpilogue
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (n : Int)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (m0 mpre : Mem) (c : Config) : Prop :=
  -- The `.int`-specialized instance of the shared, value-agnostic `PreEpilogueV`
  -- (`EvalSimCommon.lean`): the sret buffer holds `ValueRepr … (.int n)`. The
  -- null/bool/str/var leaf cases reuse `PreEpilogueV` directly at their own value.
  PreEpilogueV g N A SL φf φc st (.int n) sp r sret v8 v9 v18 out0 m0 mpre c

end Vsa.Sim
