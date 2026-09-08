import Vsa.Sim.rows.StrCmpSignTail
import Vsa.Sim.rows.BinStrCells
import Vsa.While.StringOrder

/-!
# `StrCmpBlockC` — the sign-tail words and the order bridge of the string comparisons

Str-str operands route through `strcmp @0x80006ea0` (`strcmp_full_spec`), landing
its sign in `a1`, then join the SHARED operator sign-test tail
`0x800036a4 → jal value_bool` — the `#derive_case` segs of `StrCmpSignTail`
(`sTailLt`/`sTailGt`/`sTailLe`) and the `ge` `cmpFixupTail` (`CmpArmSeg`).  Each
tail produces a boolean payload WORD in `x11` that `value_bool` boxes into
`.bool (word != 0)`.  The word is a pure integer fixup of the strcmp return `w`:

* `lt`: `srli w 0x3f`  — top (sign) bit of `w`;
* `gt`: `sgtz w`        — `0 <ₛ w`;
* `le`: `slti w 1`      — `w ≤ₛ 0`;
* `ge`: `not w; srli`   — top bit of `~w`.

`sTailWord*` name these reflected fixups (the register the matching `STail*Post`
reads out in `x11`).  `StrCmpOrderBridge op bres` ties the boxed boolean to the
source order through the `strcmp`-post sign fact over the operand `CStr` lists; it
is proved for the four `binOpSem` closures in `rows/StrCmpOrderClose.lean`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.While Vsa.MemRepr
open Vsa.Machine (MState Config)

namespace Vsa.Sim

/-! ## The op-specific sign-tail fixup words (the reflected `x11` of each `STail*Post`) -/

/-- `lt` shared `srli w 0x3f` — the `x11` word `sTailLt` (`STailLtPost`) reads out. -/
def sTailWordLt (w : BitVec 64) : BitVec 64 :=
  shift_bits_right w (Sail.BitVec.extractLsb (0x3f#6) 5 0)

/-- `gt` `sgtz w` (`slt x0,w`) — the `x11` word `sTailGt` (`STailGtPost`) reads out. -/
def sTailWordGt (w : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) w))

/-- `le` `slti w 1` — the `x11` word `sTailLe` (`STailLePost`) reads out. -/
def sTailWordLe (w : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit (zopz0zI_s w (sign_extend (m := 64) (0x001#12))))

/-- `ge` `not w; srli 0x3f` — the `x11` word the landed `ge` `cmpFixupTail` reads
out (the shared `srli` applied to `~w`, the `ge` `not`). -/
def sTailWordGe (w : BitVec 64) : BitVec 64 :=
  shift_bits_right (w ^^^ sign_extend (m := 64) (0xfff#12))
    (Sail.BitVec.extractLsb (0x3f#6) 5 0)

/-- The op's boxed boolean payload word, selected by op token. -/
def sTailWord : BinOp → BitVec 64 → BitVec 64
  | .lt => sTailWordLt
  | .le => sTailWordLe
  | .gt => sTailWordGt
  | .ge => sTailWordGe
  | _   => fun _ => 0#64

/-! ## Named premise 1 — the ORDER BRIDGE (`w`-sign ↔ `String` order)

`value_bool` boxes `sTailWord op w` into `.bool (sTailWord op w != 0)`.  The order
bridge names the agreement between that boxed boolean and the source-level
`bres sl sr`, for `w` = the `strcmp` return on the two operand strings.

**HONEST (tied) form.**  An earlier version quantified `w` free of `sl`/`sr`
(`∀ w sl sr, (sTailWord op w != 0) = bres sl sr`); that is FALSE — nothing tied the
`strcmp` return `w` to the operand strings (machine-checked falsity, see
`experiments/observations.md`).  The correct bridge ties `w` to the operand strings
through the `strcmp`-post sign fact `strcmpSign w = strcmpSpecSign csa csb` over the
`CStr` char lists (`sl = ofList csa`, `sr = ofList csb`, `AllNonzero` = the `CStr`
interior invariant).  This is the single String-theory obligation the spec layer
lacked (it had only the equality bridge `string_eq_iff_strcmpSpecSign_zero`); it is
now PROVED for the four `binOpSem` closures in `Vsa/Sim/rows/StrCmpOrderClose.lean`
(`strCmpOrderBridge_{lt,le,gt,ge}`), resting on `Vsa/While/StringOrder.lean`. -/
def StrCmpOrderBridge (op : BinOp) (bres : String → String → Bool) : Prop :=
  ∀ (w : BitVec 64) (csa csb : List Char),
    Vsa.While.AllNonzero csa → Vsa.While.AllNonzero csb →
    strcmpSign w = strcmpSpecSign csa csb →
    (sTailWord op w != 0#64) = bres (String.ofList csa) (String.ofList csb)

/-! The machine chain that consumes the order bridge is `Vsa/Sim/StrCmpCell.lean`
(`blockC_strcmp`, ONE proof for the four operators); `rows/StrCmpCellInstances.lean`
instantiates it. -/

end Vsa.Sim
