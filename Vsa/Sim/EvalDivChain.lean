import Vsa.Sim.EvalGeChain

/-!
# `EvalDivChain` — the operator-dispatch prefix routing to the `.div` arm (item 1)

The binary-op arm-entry linkage (`TwoSubReturn` @0x8000351c → the arm's `SegPre`)
runs a SHARED kind-dispatch prefix then a `jr` jump-table dispatch @0x80003558 that
routes the op token to its arm.  `evalGeChain_run` (`EvalGeChain.lean`) proves this
for `.ge` (0x8000351c → 0x80003628); `.lt`/`.le` clone it.  This file supplies the
`.div` analog of the load-bearing constant that clone needs: the operator
jump-table slot for `.div` and the proof that it routes the `jr` to the `.div` arm
`0x800037dc` (the entry of `divDispatch`/`divDispatchRow`, `DivDispatchSeg.lean`).

The routing formula (read off `evalGeChain_run`, `EvalGeChain.lean:179-288`):
* switch index = `token - 11` (`0x80003524: addi x15,x15,-11`);
* slot address = `opTableBase + index*4` (`opTableBase = 0x80019f84`,
  `EvalBinSim2.lean:77`); the slot holds a little-endian `Int32` RELATIVE offset;
* `jr` target = `opTableBase + (Int32) slot` (`0x8000354c: lw` + `add` + `jr`).

Cross-checked against the two landed entries:
* `.add` (token 11, index 0, slot `opTableBase+0`) = `04 99 fe ff` = `0xfffe9904`
  (`AddSlotPinned`, `EvalBinSim2.lean:80`);
* `.ge`  (token 23, index 12, slot `opTableBase+48`) = `a4 96 fe ff` = `0xfffe96a4`,
  target `0x80019f84 + 0xfffe96a4 = 0x80003628` (`GeSlotPinned`, `EvalGeChain.lean:44`).

`.div` (token 14, index 3, slot `opTableBase+12` = `0x80019f90`): the target is the
`.div` arm `0x800037dc`, so the slot Int32 = `0x800037dc - 0x80019f84 = 0xfffe9858`
= little-endian `58 98 fe ff`.  `divSlot_routes` below PROVES (by `decide`, the same
`jr`-target computation `evalGeChain_run` uses at `EvalGeChain.lean:286`) that these
bytes land the `jr` exactly at `0x800037dc` — the derivation is self-checking, not a
guess.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Sim.Code

namespace Vsa.Sim

/-! ## `DivSlotPinned` — the operator jump-table slot pin for `.div`

`.div` (token 14, index 3) → slot bytes `58 98 fe ff` @ `opTableBase + 12`
(address `0x80019f90`), target `opTableBase + (Int32)0xfffe9858 = 0x800037dc`
(the `.div` arm entry).  Analogous to `GeSlotPinned` (index 12, +48). -/
def DivSlotPinned (m : Mem) : Prop :=
  m[(opTableBase + 12 : Nat)]? = some (0x58 : BitVec 8) ∧
  m[(opTableBase + 13 : Nat)]? = some (0x98 : BitVec 8) ∧
  m[(opTableBase + 14 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(opTableBase + 15 : Nat)]? = some (0xff : BitVec 8)

/-- `DivSlotPinned` survives a `writeMap8` disjoint from `[opTableBase+12, +4)`.
Clone of `geSlot_writeMap8` — lets the slot pin ride through the arm's stack
stores exactly as `GeSlotPinned` does. -/
theorem divSlot_writeMap8 (m : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ opTableBase + 12 ∨ opTableBase + 20 ≤ a8) (h : DivSlotPinned m) :
    DivSlotPinned (writeMap8 m a8 d) := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint m a8 _ d (by omega)]; assumption)

/-- **The `.div` slot routes the `jr` to the `.div` arm.**  With the derived slot
bytes `58 98 fe ff` and the table base `0x80019f84` (the `x14` value the prefix
computes), the `jr`-target computation `evalGeChain_run` performs at its terminator
(`EvalGeChain.lean:286`) lands exactly at `0x800037dc` — the entry PC of
`divDispatch`.  This `decide` is the proof that the derived slot bytes are correct:
had any byte been wrong, the target would not equal the `DivDispatchSeg` arm PC. -/
theorem divSlot_routes :
    (BitVec.update ((bytesVal MKind.lw [0x58#8, 0x98#8, 0xfe#8, 0xff#8]
        + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = (0x800037dc#64 : BitVec 64) := by decide

/-- `.div` op-token load bytes (`14 = [0x0e,0,0,0]`), concrete for the `bltu`
bounds guard.  Clone of `geLds1` with token 14 (vs ge's 23). -/
def divLds1 (b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8) :
    List (List (BitVec 8)) :=
  [[0x0e#8, 0x00#8, 0x00#8, 0x00#8], [b0, b1, b2, b3], [c0, c1, c2, c3],
   [d0, d1, d2, d3, d4, d5, d6, d7]]

/-- The `.div` switch index is `3` (`token 14 - 11`), so the prefix computes
`x15 = 3` after the `addi x15,x15,-11`, then the slot address
`opTableBase + 3*4 = 0x80019f90`.  Verifies the index arithmetic the
`evalGeChain_run` clone will pin (cf. `EvalGeChain.lean:179-181`, where ge pins
`x15 = 12`). -/
theorem divIndex_val :
    (sign_extend (m := 64) (Sail.BitVec.extractLsb
      (bytesVal MKind.lw [0x0e#8, 0x00#8, 0x00#8, 0x00#8]
        + sign_extend (m := 64) (0xff5#12)) 31 0) : BitVec 64) = 3#64 := by decide

/-- The `.div` op token is `14` (`= [0x0e,0,0,0]`).  Clone of ge's `hx12v`
(`EvalGeChain.lean:187`, token 23). -/
theorem divToken_val :
    (bytesVal MKind.lw [0x0e#8, 0x00#8, 0x00#8, 0x00#8] : BitVec 64) = 14#64 := by decide

#print axioms DivSlotPinned
#print axioms divSlot_writeMap8
#print axioms divSlot_routes
#print axioms divIndex_val
#print axioms divToken_val

/-! ## Remaining for `evalDivChain_run` (the item-1 bridge, a `evalGeChain_run` clone)

`evalDivChain_run` proves `0x8000351c → 0x800037dc` and lands the `divDispL` pins
(`x16=2, x10=2, x2=v2, x9=sret, x17=Wr, x19=Wl`).  It is a faithful clone of
`evalGeChain_run` (`EvalGeChain.lean:68-320`) reusing the arm-INDEPENDENT prefix
blocks `gtChainB1`/`gtChainB2a`/`gtChainB2b` VERBATIM, with these swaps:

* token `23 → 14`: `geLds1 → divLds1`; the `hx12v`/`bltu`-guard/`hx15_1` decides
  use `divToken_val` (`14`) and `divIndex_val` (`3`) instead of ge's `23`/`12`;
* slot `opTableBase+48 (0x80019fb4) → opTableBase+12 (0x80019f90)`: `hx15_2` pins
  `x15 = 0x80019f90` (`3*4 + base`) not `0x80019fb4`; `GeSlotPinned → DivSlotPinned`
  (bytes `58 98 fe ff`), `sLo/sHi/sHt/sAl` bounds re-`decide`d for `0x80019f90`;
* `jr` target `0x80003628 → 0x800037dc`: the terminator end-PC `decide` uses
  `divSlot_routes` (proven above);
* the CSWTCH.25 index / kind `beq` ladder that ge runs @0x80003628 is NOT part of
  this prefix — the `.div` arm's kind checks are the `divDispatch` seg's own two
  `bne`s, so `evalDivChain_run`'s conclusion is just the `divDispL` pins at
  `0x800037dc`, no `x12` token pin (div's arm never re-reads the token).

Then the item-1 bridge `TwoSubReturn → SegPre divDispatch` composes:
`evalDivChain_run` (lands the pins + `mem = m0`) ≫ build `ChainFacts` via
`chain_facts` (residual = the frame-window `MemFacts` from a `DivResid` bundle, the
`.div` analog of `GeResid`) ≫ `divDispatchRow`.  See
`experiments/binop-value-tail-wiring.md` for the full assembly.
-/

end Vsa.Sim
