import Vsa.Sim.EvalGeChain
import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.DeriveCallSeg
import Vsa.Sim.DivSpec3

/-!
# `DivDispatchSeg` — the `div` arm dispatch ladder as a NEW `#derive_case` leaf

The first genuinely NEW binary-op arm assembled on the `#derive_case`/`segToTriple`
combinator (validated in `Vsa/Sim/CmpDispatchSeg.lean` on the `ge` comparison arm)
— NOT a hand-cloned row.  `div` (token 14) reaches its own arithmetic arm
`0x800037dc → 0x8000381c` (ending just before `jal __divdi3`):

  D1 `ld a4,0x78 ; ld a5,0x88 ; li a3,2 ; sd a4,0xf0 ; sd a5,0x100` ▷
     `bne a6,a3` NOT (right kind `int`, a6=2=a3) → 0x37f4;
  D2 `ld a4,0x90 ; ld a3,0x98 ; ld a5,0xa0 ; sd a4,0xf0 ; sd a3,0xf8 ; sd a5,0x100` ▷
     `bne a0,a6` NOT (left kind `int`, a0=2=a6) → 0x380c;
  D3 (empty body) ▷ `beqz a7` NOT taken → 0x3814 — **the divisor-nonzero guard**:
     `a7 = Wr` (the divisor `b`), so this `beq a7,x0 = false` is exactly div's
     `b ≠ 0` value-path condition.  It is DATA-DEPENDENT (unlike the two kind
     `bne`s, which pin concretely), so `chain_facts` leaves it as a leftover — the
     caller supplies `Wr ≠ 0`, mirroring `binOpSem .div = if b == 0 then none …`;
  D4 `mv a1,a7 ; mv a0,s3` — straight-line to 0x381c: sets up the `__divdi3`
     arguments `a0 = s3 = Wl` (dividend `a`) and `a1 = a7 = Wr` (divisor `b`).

The row `divDispatchRow` parks at `0x8000381c` with `x10 = Wl`, `x11 = Wr` — the
libgcc `__divdi3(a, b)` call arguments — and the five stack stores in `out.log`.
On top of it, `jal __divdi3 @0x8000381c` is a Shape-D `callSeg` seam
(`divdi3_spec`, the `a0 = a.tdiv b` callee contract, mirror of `muldi3_spec`) and
`jal value_int @0x80003828` boxes the result into `.int (wrap64 (a.tdiv b))` — the
same two-seam arithmetic shape as the landed `blockC_mul`, composed on this seg.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

set_option maxHeartbeats 4000000

/- The `div` arithmetic arm `0x800037dc → 0x8000381c`, four blocks (two int-kind
`bne`s NOT taken, the divisor-nonzero `beqz` NOT taken, then the `__divdi3`
argument `mv`s).  All terminators are `br` with fixed polarity. -/
                -- mv   x10,x19  (a0 = s3  = dividend a)

/-! ## The `__divdi3` seam via `callSeg` — concluding the div value

The div arm's arithmetic tail is the Shape-D call splice
`dispatch ≫ jal __divdi3 ≫ value_int`.  The callee contract is the REAL
`divdi3_spec` (`Vsa/Sim/DivSpec3.lean`, `x10.toInt = n.toInt.tdiv d.toInt`);
`callSeg` threads it between the caller prefix (the `divDispatchRow` dispatch
above, then the `jal __divdi3` link landing at `divdi3_pre`'s entry `0x800046a4`
with `x10=a`, `x11=b`, `x1=return`) and the caller suffix (the `mv`s + `jal
value_int` boxing the quotient), exactly as the landed `blockC_mul` threads
`muldi3_spec`. -/

end Vsa.Sim
