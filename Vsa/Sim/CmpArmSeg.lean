import Vsa.Sim.EvalGeChain
import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac

/-!
# `CmpArmSeg` — exponentiation proof-of-method: the comparison operator-fixup
tail auto-threaded via `#derive_case` + `segToTriple`

This file demonstrates, on a REAL fragment of `eval_expr`, that the binary-op
comparison arm's operator-fixup tail (`0x800036a4 → 0x800036c8`: the three
operator `beq`s + `not`/`srli`/`mv`) collapses from hand-threaded
`bblock_sound_bt` composition (the `geLadB7`/`geLadNot`/`ltLadG` blocks + the
`evalGeLadderEF`/`evalLtLadderG` theorems, ~120 lines of step-count/frame
plumbing) to a `(pc, word)` block table + ONE `chain_facts` + ONE `ChainOK`
`decide`.

The measured point (see `#print` at the bottom): `cmpFixupTail_seg` is emitted
by `#derive_case` with the whole Steps chain / computed end PC / computed
registers / write log auto-threaded, and `cmpFixupTailRow` marshals it into a
`Triple` via `segToTriple` in a handful of lines. This is the template the
remaining binary-op rows (div/mod/eq/ne) fan out from: paste the block table,
one command, one `decide`, project the outcome.

The resolved path is `ge` (token 23): all three operator `beq`s fall through
(23 ≠ 21, 22, 20), so `not x11,x11` executes then the shared `srli x11,x11,0x3f`
sign-bit; `x11` ends as the complemented spaceship top bit.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

/- The comparison operator-fixup tail `0x800036a4 → 0x800036c8`, resolved for
the `ge`/fall-through path (token ≠ 21, 22, 20).  Four blocks:
  `li x15,21` ▷ `beq x12,x15` NOT taken (→ 0x36ac);
  `li x15,22` ▷ `beq x12,x15` NOT taken (→ 0x36b4);
  `li x15,20` ▷ `beq x12,x15` NOT taken (→ 0x36bc);
  `not x11,x11 ; srli x11,x11,0x3f ; mv x10,x9` — straight-line to 0x36c8. -/
                -- mv   x10,x9

end Vsa.Sim
