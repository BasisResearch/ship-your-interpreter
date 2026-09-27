import Vsa.Sim.EvalIntSim3
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 gate: blocks C, D, and the `EvalIntSimGoal` assembly

Completes the `EvalE.int` simulation Triple begun in `EvalIntSim2.lean`
(`blockA_ee`) and `EvalIntSim3.lean` (`spill_roundtrip_ee`, `PreEpilogue`):

* **`blockC_ee`** (`ArmEntry → PreEpilogue`): the `EX_INT` arm — `ld a1,8(a2)`
  (payload → `x11`), `jal value_int` (the callee via `value_int_spec`, with the
  callee ghost `fun R => σ2.regs.get? R`), and `j 0x800033ec` to the shared
  epilogue. The sret buffer holds `ValueRepr (.int n)`; the four spill slots,
  `s1`/`sp`, `eval_expr`, the store, and the output all survive the callee.

* **`blockD_ee`** (`PreEpilogue → EvalExit`): the shared epilogue — four `ld`
  restores (via `spill_roundtrip_ee`), `mv a0,s1`, `addi sp,sp,1088`, `ret`.
  Restores `ra`/`s0`/`s1`/`s2`/`sp`, returns `a0 = sret`, `PC → r`.

* **`evalIntSim`** (`EvalIntSimGoal`): `blockA_ee ≫ blockC_ee ≫ blockD_ee`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

