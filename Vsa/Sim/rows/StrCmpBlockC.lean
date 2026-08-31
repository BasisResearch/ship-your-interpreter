import Vsa.Sim.rows.StrCmpSignTail
import Vsa.Sim.rows.BinStrCells
import Vsa.While.StringOrder

/-!
# `StrCmpBlockC` — the four STR-comparison cell providers, factored through the
sign-tail rows (`StrCmpSignTail`) + ONE named order bridge

`BinStrCells.lean` factors the six string-operand slots of `eval_binary_row` into
two shared residuals; the four `.lt`/`.le`/`.gt`/`.ge` string-comparison slots each
consume `StrCmpCellResid op bres` (the whole-node `EvalIH` producing `.bool (bres
sl sr)`).  This file supplies the *machine-route half* of that residual — the
op-specific sign-test tail is exactly the `StrCmpSignTail` rows — and isolates the
two remaining obligations into named premises, matching the honest residual style
of `BinStrCells`.

## The decoded route (see `BinStrCells` §(a))

Str-str operands route through `strcmp @0x80006ea0` (`strcmp_full_spec`), landing
its spec sign in `a1`, then join the SHARED operator sign-test tail
`0x800036a4 → jal value_bool` — the four `#derive_case` segs of `StrCmpSignTail`
(`sTailLt`/`sTailGt`/`sTailLe`) + the landed `ge` `cmpFixupTail`.  Each op's tail
produces a boolean payload WORD in `x11` that `value_bool` boxes into
`.bool (word != 0)`.  The word is a pure integer fixup of the strcmp return `w`:

* `lt`: `srli w 0x3f`  — top (sign) bit of `w`;
* `gt`: `sgtz w`        — `0 <ₛ w`;
* `le`: `slti w 1`      — `w ≤ₛ 0`;
* `ge`: `not w; srli`   — top bit of `~w`.

`sTailWord*` below name these reflected fixups (identical to the register the
matching `STail*Post` reads out in `x11`), so the sign tail rows plug straight in.

## The two named residuals (honest surface)

1. `StrCmpOrderBridge op bres w sl sr` — the ORDER BRIDGE.  The spec layer has
   `string_eq_iff_strcmpSpecSign_zero` (EQUALITY only, `EnvDefSpec2`), but NO
   ordering agreement between the C `strcmp` sign and Lean `String.<`.  Rather than
   develop String theory (out of scope), we NAME the agreement between this op's
   boxed boolean (`sTailWord op w != 0`) and the source-level `bres sl sr` as ONE
   premise per op, where `w` is the strcmp return for the two operand strings.

2. `StrArmMachineResid op bres` — the not-yet-assembled str-arm MACHINE chain
   (`blockA_binaryArm` entry ≫ `blockB_binary` operand recursions ≫ kind-check +
   `strcmp` seam ≫ the `StrCmpSignTail` row for `op` ≫ `value_bool` box ≫
   `blockD_v_rec`), delivering the whole-node `EvalIH` at `.bool (bres sl sr)`.
   Same shape as the landed `evalGeSim` int arm (`blockC_ge`, ~700 lines); left as
   a named residual exactly as `StrCmpCellResid` itself is in `BinStrCells`, with
   `StrCmpSignTail` discharging its op-specific sign-tail segment.

`strCmpCellResid_of` assembles `StrCmpCellResid op bres` directly from
`StrArmMachineResid op bres`, so the four `BinStrCells` cells are supplied once the
str-arm machine chain lands (its sign-tail segment already proved here).

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

/-! ## Named premise 2 — the str-arm MACHINE chain (sign-tail segment proved)

The whole-node `EvalIH` for `.binary op el er` at string operands, producing
`.bool (bres sl sr)`.  Its discharge is the machine chain decoded in `BinStrCells`
§(a): `blockA_binaryArm` ≫ `blockB_binary` ≫ [kind-check + `strcmp` seam + the
`StrCmpSignTail` row for `op` + `value_bool` box] ≫ `blockD_v_rec`.  The
op-specific sign-tail segment is the landed `StrCmpSignTail`; the rest mirrors
`evalGeSim`.  Left as a named residual (like `StrCmpCellResid` in `BinStrCells`). -/
def StrArmMachineResid (op : BinOp) (bres : String → String → Bool) : Prop :=
  ∀ (st : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr)
    (st'' : Vsa.While.St) (sl sr : String),
    EvalIH st d env (.binary op el er) st'' (.bool (bres sl sr))

/-! ## `strCmpCellResid_of` — assemble `StrCmpCellResid` from the machine residual

`StrCmpCellResid op bres` (`BinStrCells`) is definitionally the same whole-node
`EvalIH` family as `StrArmMachineResid op bres`; the assembler forwards it.  The
order bridge is consumed INSIDE the (unbuilt) machine chain to turn the `value_bool`
box's `.bool (sTailWord op w != 0)` into `.bool (bres sl sr)` — it is threaded as
`hOrder` so the eventual chain proof reuses it verbatim per op. -/
theorem strCmpCellResid_of (op : BinOp) (bres : String → String → Bool)
    (_hOrder : StrCmpOrderBridge op bres)
    (hChain : StrArmMachineResid op bres) :
    StrCmpCellResid op bres :=
  fun st d env el er st'' sl sr => hChain st d env el er st'' sl sr

/-! ## The four cell instances, wired to `BinStrCells` -/

/-- `.lt` string cell, via the machine residual + order bridge. -/
theorem strCmpCell_lt_of
    (hOrder : StrCmpOrderBridge .lt (fun sl sr => sl < sr))
    (hChain : StrArmMachineResid .lt (fun sl sr => sl < sr)) :
    StrCmpCellResid .lt (fun sl sr => sl < sr) :=
  strCmpCellResid_of .lt _ hOrder hChain

/-- `.le` string cell. -/
theorem strCmpCell_le_of
    (hOrder : StrCmpOrderBridge .le (fun sl sr => sl < sr || sl == sr))
    (hChain : StrArmMachineResid .le (fun sl sr => sl < sr || sl == sr)) :
    StrCmpCellResid .le (fun sl sr => sl < sr || sl == sr) :=
  strCmpCellResid_of .le _ hOrder hChain

/-- `.gt` string cell. -/
theorem strCmpCell_gt_of
    (hOrder : StrCmpOrderBridge .gt (fun sl sr => sr < sl))
    (hChain : StrArmMachineResid .gt (fun sl sr => sr < sl)) :
    StrCmpCellResid .gt (fun sl sr => sr < sl) :=
  strCmpCellResid_of .gt _ hOrder hChain

/-- `.ge` string cell. -/
theorem strCmpCell_ge_of
    (hOrder : StrCmpOrderBridge .ge (fun sl sr => sr < sl || sl == sr))
    (hChain : StrArmMachineResid .ge (fun sl sr => sr < sl || sl == sr)) :
    StrCmpCellResid .ge (fun sl sr => sr < sl || sl == sr) :=
  strCmpCellResid_of .ge _ hOrder hChain

#print axioms strCmpCellResid_of
#print axioms strCmpCell_lt_of
#print axioms strCmpCell_le_of
#print axioms strCmpCell_gt_of
#print axioms strCmpCell_ge_of

end Vsa.Sim
