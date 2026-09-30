import Vsa.Sim.EvalBinSim3
import Vsa.Sim.CmpTailSites
import Vsa.Sim.CmpTailSitesGen
import Vsa.Sim.CmpBridges
import Vsa.Sim.EvalBoolSim

/-!
# Layer 4 — M4 RECURSIVE cases: `evalLtSim`/`evalLeSim`/`evalGtSim`
(the `EvalE.binary .lt/.le/.gt` int comparisons)

Composes the two-operand binary arm of `eval_expr` for the three integer
comparison operators on two integer operands, in the `EvalIH` motive shape
(`EvalEntry → EvalExitD`) taking TWO induction hypotheses:

```
blockA_k        (prologue + dispatch → widened ArmEntryK @0x800034e8)
  ≫ blockB_binary (arm head + TWO recursive calls ⋈ IH_l/IH_r → TwoSubReturn @0x8000351c)
  ≫ blockC_lt/le/gt (operator dispatch tail → SHARED comparison arm @0x80003628
                     → value_bool → PreEpilogueVD .bool(cmp) @0x800033ec)
  ≫ blockD_v_rec  (shared epilogue → EvalExitD .bool(cmp))
```

The operator dispatch tail (σ1–σ16) is copied near-verbatim from `blockC_sub`
(EvalBinSim3): the same `lw a2,8(s0)`/`addiw`/`slli`/`srli`/`auipc`/`lw`/`jr`
jump-table dispatch off `CSWTCH.18` @0x80019f84, changing only the operator token
(12→20/21/22) and the jump-table slot (all three comparison tokens map to the
SAME shared arm 0x80003628, via slots at `opTableBase + {36,40,44}`, each storing
the word `0xfffe96a4` = bytes `a4 96 fe ff`).

The SHARED comparison arm @0x80003628 computes
`cmp = subw(slt Wr Wl, slt Wl Wr) = sign(a-b)`, then a `beq` ladder on the op
token selects an op-specific fixup:
* **lt** (token 20) → `0x800036c0` `srli a1,a1,0x3f` (sign-bit extract);
* **le** (token 21) → `0x80003af8` `slti a1,a1,1`;
* **gt** (token 22) → `0x80003ae4` `sgtz a1,a1`;
then `mv a0,s1; jal value_bool; ld s3 restore; j 0x800033ec`.  `value_bool`
produces `.bool (x11 != 0)`, and the `<op>_fixup_bridge` (CmpBridges) shows
`(x11 != 0) = <spec comparison>`.

RESTRICTED to `vl = .int a`, `vr = .int b`.  `blockC_lt/le/gt` carries the same
two head-dropped register/memory residuals as `blockC_sub` (the LEFT payload word
in `s3`/`x19`, and the respilled `vl.kind` word).

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

/-! ## `LtSlotPinned` — the operator jump-table slot pin for `.lt`

`.lt` (token 20, index 9) → slot bytes `a4 96 fe ff` @ `opTableBase + 36`,
target `opTableBase + (Int32)0xfffe96a4 = 0x80003628` (the SHARED comparison arm). -/

end Vsa.Sim
