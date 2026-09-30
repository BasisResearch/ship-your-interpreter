import Vsa.Sim.EvalGtChain

/-!
# `EvalLtChain` — the `.lt` operator ladder (0x351c → 0x36c8)

Mirror of `evalLeChain_run` + `evalLeLadder*` for the `.lt` operator (token 20,
CSWTCH.18 slot `opTableBase+36` @ 0x80019fa8, CSWTCH.25 index `0`).  Reuses the gt
block definitions (`gtChainB1/B2a/B2b`, `gtLds2`, `gtLadB1..gtLadB4`, `gtLds3`,
`gtLadB5`, `evalGtBlkCmp`) verbatim — only threaded values differ (op token 20,
kind-ladder x15=9, CSWTCH.25 index 0 → slot 0x80019fe0).  The tail DIVERGES: `lt`
falls through all three comparison `beq`s into the `srli x11,x11,0x3f` sign-bit
fixup @0x36c0 (new blocks `ltLadB6`/`ltLadB7`/`ltLadG`).

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

/-! ## Le kind-ladder + branch ladder `0x80003628 → 0x80003b00`.

The `.le` counterpart of `evalGtLadder{AB,C,D,EF,G}`.  Reuses the gt block
definitions `gtLadB1..gtLadB4` verbatim (identical instruction words) — only the
op-token value (`x12 = 21` vs 22), the reloaded kind index (`x15 = 1` vs 2), and
the CSWTCH slot address (`0x80019fe0` vs `0x80019ff0`) differ.  The tail DIVERGES:
`le` takes ONE `beq@0x36a8` (21 = 21) into the `slti a1,a1,1` fixup @0x80003af8,
where `gt` fell through to a second `beq@0x36b0` and the `sgtz` fixup. -/

/-! ## LT branch tail `0x80003698 → 0x800036c8`.

`lt` (token 20) falls through ALL THREE comparison `beq`s — `li 21`/beq@0x36a8
(20≠21), `li 22`/beq@0x36b0 (20≠22), `li 20`/beq@0x36b8 TAKEN (20=20) — into the
`srli x11,x11,0x3f` sign-bit fixup @0x36c0.  Reuses gt's `gtLadB5` (cmp + beq@0x36a8
NOT-taken); new blocks `ltLadB6`/`ltLadB7` for the second/third `beq`. -/

end Vsa.Sim
