import Vsa.Sim.StmtChildArm

/-!
# `HelperCall` — the parametric in-frame runtime-helper call of `exec_stmt`

Every remaining statement leaf calls a runtime helper from inside the
`exec_stmt` frame and continues at the helper's return: `value_null` at the
two null bridges (`ret;`, `var x;`), `env_define` at the declaration tail,
`env_new` at the block and for arms.  This file states that seam once:

* a descriptor `HelperCall` (head PC, reflected prefix, `jal` site, callee
  entry) and its decided certificate `Cert`;
* `parked_of_gholds` runs the prefix and the `jal` from any parked state and
  lands at the callee entry (`Parked`: link register, reflected registers and
  write log, ABI frame); `parked_of_ready` enters from a `RouteReady`,
  `parked_of_armState` from an `ArmState`;
* `Return` is the helper's return as a route-ready state plus its memory
  footprint; each callee supplies one adapter `xReturn_of_parked` from its
  contract (`HelperCallNull.lean` for `value_null`);
* `RouteHead.toRouteReady`, `ArmState.frameFacts`, and
  `FrameFacts.afterStackHelper` connect the return to the existing
  continuation kit (`route_of_ready`, `ArmState.of_routeHead`,
  `normalExitPre_of_routeHead`, the retslot resume).

An instance is one `#derive_case` prefix, one descriptor, a certificate of
`decide`s, and a chain-facts theorem.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

local notation "SpecSt" => Vsa.While.St

/-- An in-frame call of a runtime helper: the reflected prefix from the
parked PC up to (excluding) the `jal`, the `jal` site, and the callee entry. -/
structure HelperCall where
  /-- The parked PC the prefix starts at. -/
  headPC : BitVec 64
  /-- The reflected prefix (loads, moves, stores, decided branches). -/
  seg : List BBlock
  /-- PC of the `jal`. -/
  jalPC : BitVec 64
  /-- Decoded 21-bit `jal` immediate. -/
  jalImm : BitVec 21
  /-- The callee entry. -/
  entry : BitVec 64

namespace HelperCall

/-- The reflected outcome of the prefix from the pinned registers `L`. -/
def out (H : HelperCall) (L : GRegs) (lds : List (List (BitVec 8))) : SegEvalState :=
  evalBlocks H.seg (SegEvalState.init L lds)

/-! ## Parked at the callee entry -/

/-! ## The helper's return -/

end HelperCall

/-! ## Connecting to the continuation kit -/

/-! ## Byte-level facts of a three-word copy

Every in-frame value copy is three `ld`s followed by three `sd`s; its
reflected write log is three `writeMap8`s of the loaded words.  The facts
below hold for any source and destination. -/

/-! ## A copied value's payload

A 24-byte value copy moves the tag and the payload pointer, not the payload.
The copy represents the value at the destination when the payload (a string,
if any) lies outside the copied window. -/

/-! ## Four-byte loads and routes that rewrite `s3`

The block arm reads the statement count with `lw` and rewrites `s3` to the
fresh scope before its loop head; both fall outside the eight-byte and
`abiButS0` conventions of the earlier layers. -/

/-- A non-negative 32-bit word sign-extends to its value. -/
theorem sext32_of_lt (b0 b1 b2 b3 : BitVec 8) (k : Nat) (hk : k < 2 ^ 31)
    (hrec : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) = k) :
    (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)) : BitVec 64)
      = BitVec.ofNat 64 k := by
  have hw : ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).toNat = k := by
    simp only [BitVec.append_eq, BitVec.toNat_append]
    have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
    simp only [Nat.shiftLeft_eq, Nat.reducePow]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend]
  have hmsb : ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega
  rw [hmsb]
  simp only [Bool.false_eq_true, if_false, Nat.add_zero, BitVec.toNat_setWidth]
  rw [hw, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]

end Vsa.Sim
