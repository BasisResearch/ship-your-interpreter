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
def LtSlotPinned (m : Mem) : Prop :=
  m[(opTableBase + 36 : Nat)]? = some (0xa4 : BitVec 8) ∧
  m[(opTableBase + 37 : Nat)]? = some (0x96 : BitVec 8) ∧
  m[(opTableBase + 38 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(opTableBase + 39 : Nat)]? = some (0xff : BitVec 8)

/-- `.le` (token 21, index 10) → slot bytes @ `opTableBase + 40`. -/
def LeSlotPinned (m : Mem) : Prop :=
  m[(opTableBase + 40 : Nat)]? = some (0xa4 : BitVec 8) ∧
  m[(opTableBase + 41 : Nat)]? = some (0x96 : BitVec 8) ∧
  m[(opTableBase + 42 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(opTableBase + 43 : Nat)]? = some (0xff : BitVec 8)

/-- `.gt` (token 22, index 11) → slot bytes @ `opTableBase + 44`. -/
def GtSlotPinned (m : Mem) : Prop :=
  m[(opTableBase + 44 : Nat)]? = some (0xa4 : BitVec 8) ∧
  m[(opTableBase + 45 : Nat)]? = some (0x96 : BitVec 8) ∧
  m[(opTableBase + 46 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(opTableBase + 47 : Nat)]? = some (0xff : BitVec 8)

/-- `LtSlotPinned` survives a `writeMap8` disjoint from `[opTableBase+36, +4)`. -/
theorem ltSlot_writeMap8 (m : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ opTableBase + 36 ∨ opTableBase + 44 ≤ a8) (h : LtSlotPinned m) :
    LtSlotPinned (writeMap8 m a8 d) := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint m a8 _ d (by omega)]; assumption)

theorem leSlot_writeMap8 (m : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ opTableBase + 40 ∨ opTableBase + 48 ≤ a8) (h : LeSlotPinned m) :
    LeSlotPinned (writeMap8 m a8 d) := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint m a8 _ d (by omega)]; assumption)

theorem gtSlot_writeMap8 (m : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ opTableBase + 44 ∨ opTableBase + 52 ≤ a8) (h : GtSlotPinned m) :
    GtSlotPinned (writeMap8 m a8 d) := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint m a8 _ d (by omega)]; assumption)

end Vsa.Sim
