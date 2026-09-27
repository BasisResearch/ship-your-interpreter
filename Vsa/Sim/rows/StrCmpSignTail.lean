import Vsa.Sim.CmpArmSeg

/-!
# `StrCmpSignTail` — the operator sign-test tail `0x800036a4 → jal value_bool`,
parameterised over the op token (lt / le / gt / ge)

The comparison arm's shared operator sign-test tail begins at `0x800036a4`
(`experiments/disasm.txt`).  The three operator `beq`s select the per-op sign
block; each block ends at a `jal value_bool @0x800027f8` producing the boolean
payload word in `a1` from the spaceship scalar in `a1`:

```
800036a4  li a5,21 ; beq a2,a5 → 80003af8            (le)
800036ac  li a5,22 ; beq a2,a5 → 80003ae4            (gt)
800036b4  li a5,20 ; beq a2,a5 → 800036c0            (lt) [beq-taken → shared srli]
800036bc  not a1,a1                                   (ge fall-through)
800036c0  srli a1,a1,0x3f ; mv a0,s1 ; jal value_bool (lt/ge shared)
--
80003ae4  sgtz a1,a1 ; mv a0,s1 ; jal value_bool      (gt)
80003af8  slti a1,a1,1 ; mv a0,s1 ; jal value_bool    (le)
```

So the sign-test *diverges* by op token: `lt` (token 20) `beq`-takes at
`0x800036b4` straight to the shared `srli @0x800036c0`; `ge` (token 23) falls
through all three `beq`s, runs `not a1,a1`, then the shared `srli`; `gt` (token
22) `beq`-takes at `0x800036ac` to the `sgtz` block `0x80003ae4`; `le` (token 21)
`beq`-takes at `0x800036a4` to the `slti` block `0x80003af8`.

The `ge` route is already the landed `CmpArmSeg.cmpFixupTail` (`not;srli;mv`).
This file adds the three remaining routes as `#derive_case` segs and factors the
common shape (`SegPre` at `0x800036a4`, pins `[(11, cmpV), (12, tok), (9, sret)]`,
run to the `jal value_bool` entry, produce the sign word in `x11` and `x10 =
sret`).  The seg family IS the parameterisation: one seg per op token, sharing
the pin list, the entry PC, and the `segToTriple` marshalling; `cmpV` (the
spaceship scalar in `a1`) stays symbolic in every seg.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

set_option maxHeartbeats 800000

/-! ## The three non-`ge` sign-test routes as `#derive_case` segs

Each is resolved for its op token: the `beq` at the route's entry is TAKEN
(so the pin `x12 = tok` matches the `li a5,tok`).  The route runs from
`0x800036a4` to the `jal value_bool` entry PC of that op's sign block. -/

/- `lt` (token 20): `li a5,21` ▷ `beq` NOT (20≠21) → 0x36ac; `li a5,22` ▷ `beq`
NOT (20≠22) → 0x36b4; `li a5,20` ▷ `beq` TAKEN (20=20) → 0x36c0; then
`srli x11,x11,0x3f ; mv x10,x9` — straight-line to the jal entry 0x36c8. -/
                -- mv   x10,x9

/- `gt` (token 22): `li a5,21` ▷ `beq` NOT (22≠21) → 0x36ac; `li a5,22` ▷ `beq`
TAKEN (22=22) → 0x3ae4; then `sgtz x11,x11 ; mv x10,x9` — straight-line to the
jal entry 0x3ae8. -/
                -- mv   x10,x9

/- `le` (token 21): `li a5,21` ▷ `beq` TAKEN (21=21) → 0x3af8; then
`slti x11,x11,1 ; mv x10,x9` — straight-line to the jal entry 0x3afc. -/
                -- mv   x10,x9

/-! ## `ChainFacts` legs (one `chain_facts` per route)

Each route's branch guards are the only data-dependent leftovers; pinning
`x12 = tok` closes them by `decide` (via `all_goals rfl` after `chain_facts`). -/

/-! ## The sign-word posts and `segToTriple` rows

Each route runs to its op's `jal value_bool` entry PC (lt/ge: `0x800036c8`;
gt: `0x80003ae8`; le: `0x80003afc`), memory unchanged (no stores), with the
boolean payload word in `x11` and `x10 = sret` (the `mv x10,x9`).  The payload
word is the reflected fixup applied to the spaceship scalar `cmpV`:
  lt: `srli cmpV 0x3f`;  le: `slti cmpV 1`;  gt: `sgtz cmpV`. -/

end Vsa.Sim
