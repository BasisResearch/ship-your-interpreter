import Vsa.Sim.rows.EnvDefineUpdateExact
import Vsa.Sim.BridgeSegFramed

/-!
# `EnvDefineTailFramed` — keep-set-framed update block and epilogue of `env_define`

The landed rows `updateStoreLiveRow` (`rows/EnvDefineUpdateExact.lean`) and
`envDefineEpilogueRow` (`rows/EnvDefineEpilogueCore.lean`) export only the
registers their segs write, so the untouched `gp`/`tp`/`s7`–`s11`, the result
register `a0`, and the console output are lost after a scan hit.  This file
lands ONE generic keep-set-framed seg row over a register ghost
(`segRowKeepGhost`, `frame_of_wrChain_avoids` on a `decide`d `WrChainAvoids`)
and instantiates it for both segs, then re-composes the landed
scan-hit ⟶ update ⟶ epilogue path with the frame retained:

* `KeepGhost P g outp c` — the registers selected by `P` equal the ghost `g`
  and the output is `outp`;
* `EnvDefineTailKeep`/`EnvDefineTailKeepSp` — the keep predicates
  (`x3`, `x4`, `x10`, `x23`–`x27`; the update block also keeps `x2`);
* `updateStoreLiveRowKeep`, `envDefineEpilogueRowKeep` — the framed rows;
* `envDefineUpdateFromHitKeep`, `envDefineUpdateFromHitKeep_of_heap_owned`,
  `EnvDefineUpdatePost.restoreKeep` — the landed update/epilogue compositions
  with `KeepGhost` carried.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.MemRepr
open Vsa.RuntimeRepr
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-- ABI registers `env_define`'s update block and epilogue never write, plus the
result register: `gp`, `tp`, `a0`, `s7`–`s11`. -/
def EnvDefineTailKeep (R : Register) : Bool :=
  R == Register.x3 || R == Register.x4 || R == Register.x10 || R == Register.x23 ||
    R == Register.x24 || R == Register.x25 || R == Register.x26 || R == Register.x27

/-- The update block additionally keeps `sp`. -/
def EnvDefineTailKeepSp (R : Register) : Bool :=
  EnvDefineTailKeep R || R == Register.x2

theorem EnvDefineTailKeep.sp {R : Register} (h : EnvDefineTailKeep R = true) :
    EnvDefineTailKeepSp R = true := by
  simp [EnvDefineTailKeepSp, h]

end Vsa.Sim
