import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BlockTactics2
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.EvalIntSim2
import Vsa.Sim.ExitFootprint
import Vsa.Sim.JmpSpec
import Vsa.Sim.SegFrameFacts
import Vsa.While.Cost

/-!
# `EqNeDispatchSeg` — the `eq`/`ne` arm spill-and-call-setup blocks as `#derive_case` leaves

The `eq` (token 19) and `ne` (token 17) arms do NOT run a kind-check ladder like
`div`/`mod`/`ge` — `value_equal` handles every kind itself.  Instead each arm is a
single straight-line block that reloads the two operands' repr words from their
spill slots, points `a0`/`a1` at two freshly-materialised `Value` structs on the
stack (`bufa = sp+0x40`, `bufb = sp+0x20`), spills the words into those structs,
and falls through to `jal value_equal`:

  `eq` arm `0x800036e4 → 0x8000371c`:
     `ld a7,0x78 ; ld a6,0x80 ; ld a2,0x88 ; ld a3,0x90 ; ld a4,0x98 ; ld a5,0xa0`
     `; addi a1,sp,0x20 ; addi a0,sp,0x40`
     `; sd a7,0x40 ; sd a6,0x48 ; sd a2,0x50 ; sd a3,0x20 ; sd a4,0x28 ; sd a5,0x30`
     ▷ (fall through) `jal value_equal @0x8000371c` — box with `value_bool(a0)`;
  `ne` arm `0x80003734 → 0x8000376c`: **the byte-identical block** (same 14
     instruction words, PCs shifted by +0x50) ▷ `jal value_equal @0x8000376c` —
     box with `value_bool(seqz a0)` (the extra `seqz` negation is in the suffix,
     not this seg).

Both rows park at their `jal value_equal` PC with `x10 = bufa = sp+0x40` and
`x11 = bufb = sp+0x20` — the `value_equal(bufa, bufb)` call arguments — and the
six field stores in `out.log`.  On top, `jal value_equal` is a Shape-D `callSeg`
seam threading `value_equal_spec_full` (already complete, `ValueEqualSpec4`) and
`jal value_bool` boxes the result — the same two-seam shape as `div`/`mod`, only
the callee is `value_equal` (a `.bool`, via `binOpSem_eq`/`binOpSem_ne`) rather
than `__divdi3`/`__moddi3` (an `.int`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (NativeFn)
open Vsa.Sim.Code (StrcmpLoaded)

namespace Vsa.Sim

set_option maxHeartbeats 4000000

/- The `eq` arm block `0x800036e4 → 0x8000371c`: one straight-line block, no
branch terminator (control falls through to `jal value_equal`).  Six operand
reloads, the two `addi` buffer-pointer setups, then the six field spills. -/
                -- sd   x15,0x30(x2)

/- The `ne` arm block `0x80003734 → 0x8000376c`: byte-identical instruction words
to `eqDispatch`, PCs shifted by +0x50. -/
                -- sd   x15,0x30(x2)

/-- The `eq`/`ne` arm pin list: only `x2 = sp` (the frame base of every load,
store, and `addi`).  Both operand words are reloaded from `lds`, `a0`/`a1` are
computed from `sp`, so nothing else is externally live in the block. -/
def eqDispL (sp : BitVec 64) : GRegs := [(2, sp)]

/-! ## The spec-side `eq`/`ne` bridges

`value_equal` returns `l.equal r` (a `Bool`), which the `value_bool` suffix boxes:
`eq` boxes it directly (`binOpSem .eq = .bool (l.equal r)`), `ne` boxes its
negation via the extra `seqz` (`binOpSem .ne = .bool (!(l.equal r))`).  Both are
total (no divisor-style guard). -/

/-! ## The `value_equal` seam via `callSeg`

The `eq`/`ne` arms' comparison tail is the Shape-D call splice
`spill-setup ≫ jal value_equal ≫ value_bool`.  The callee contract is the REAL
`value_equal_spec_full` (`ValueEqualSpec4`, `x10 = cond (va.equal vb) 1 0`,
covering both the `str`-`str` strcmp branch and all five non-`str` branches).
Unlike `divdi3_spec`/`moddi3_spec` it is stated as a raw `∃ c', Steps ∧ post`
with several universal side-conditions, so we first repackage it as a genuine
`Triple` (`valueEqualTriple`) whose entry predicate is `ve_pre` conjoined with
`x2 = sp` (the frame `value_equal_spec_full` additionally needs), then thread it
with `callSeg` exactly as `divCallSeam`/`modCallSeam` thread their libgcc callee.
The `eq` and `ne` arms share this ONE seam — they differ only in the boxing
suffix `Q` (`value_bool(a0)` vs `value_bool(seqz a0)`). -/

end Vsa.Sim
