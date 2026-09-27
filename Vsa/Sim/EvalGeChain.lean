import Vsa.Sim.EvalLtChain

/-!
# `EvalGeChain` — the `.ge` operator branch tail (0x80003698 → 0x800036c0)

Clone-by-reuse of `.lt`.  The comparison operators share the arm @0x80003628 and
the operator-fixup ladder @0x800036a4..0x800036c0.  `.ge` (token 23) FALLS THROUGH
all three comparison `beq`s — `li 21`/beq@0x36a8 (23≠21), `li 22`/beq@0x36b0
(23≠22), `li 20`/beq@0x36b8 (23≠20) — into the `not a1,a1` (`xori a1,a1,-1`)
@0x800036bc, then the SHARED `srli a1,a1,0x3f` sign-bit fixup @0x800036c0.

`.lt`, by contrast, TAKES the third `beq@0x36b8` (20 = 20) into 0x800036c0,
skipping the `not`.  So `.ge` is one instruction longer than `.lt`: its ladder tail
runs `gtLadB5` (beq@0x36a8 NOT taken) ≫ `ltLadB6` (beq@0x36b0 NOT taken) ≫
`geLadB7` (beq@0x36b8 NOT taken → 0x36bc) ≫ `geLadNot` (`not a1,a1` → 0x36c0),
producing `x11 = cmpScalar Wl Wr ^^^ sign_extend (m := 64) (0xfff#12)` (the
bitwise complement of the spaceship scalar).  The shared `srli` fixup (`ltLadG`)
then extracts its sign bit.

Reuses `evalGtChain_run`-family block defs (`gtLadB5`, `ltLadB6`, `ltLadG`)
verbatim; only `geLadB7`/`geLadNot`/`evalGeLadderEF` are new.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; DEFAULT recDepth.
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

namespace Vsa.Sim

/-! ## `GeSlotPinned` — the operator jump-table slot pin for `.ge`

`.ge` (token 23, index 12) → slot bytes `a4 96 fe ff` @ `opTableBase + 48`
(address `0x80019fb4`), target `opTableBase + (Int32)0xfffe96a4 = 0x80003628`
(the SHARED comparison arm).  Analogous to `LtSlotPinned` (index 9, +36). -/

end Vsa.Sim
