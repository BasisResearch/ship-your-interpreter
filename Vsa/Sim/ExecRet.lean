import Vsa.Sim.ExecRecCommon
import Vsa.Sim.EnvGetSpec6
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 statement `ExecS.ret` (value-present path)

The `ret` statement arm (kind 6, `0x80004120 → 0x8000416c`, value present). It
evaluates the return expression `e` to `v` (store may change to `st'`), copies
`v`'s 24-byte `Value` struct into the caller-provided `retslot` (`s2 = aRet`,
ABI arg 3), and completes with status `.ret v` — exercising `ExecExit.retval`,
the `retslot` disjunct.

```
80004120:  ld   a2,8(s0)      -- a2 := stmt->expr (the operand node; retSome ⇒ p ≠ 0)
80004124:  beqz a2,…          -- (NOT taken: value present, p ≠ 0)
80004128:  mv   a3,s3         -- a3 := env
8000412c:  mv   a1,s1         -- a1 := interp*
80004130:  addi a0,sp,16      -- a0 := sp'+16 (the local sub-sret buffer)
80004134:  jal  eval_expr     -- the sub-derivation (EvalIH), link 0x80004138
80004138:  ld   a3,16(sp)     -- reload v.word0 from the sub-sret buffer
8000413c:  ld   a4,24(sp)     -- reload v.word1
80004140:  ld   a5,32(sp)     -- reload v.word2
80004144:  sd   a3,0(s2)      -- *retslot[0]  := v.word0   (s2 = aRet)
80004148:  sd   a4,8(s2)      -- *retslot[8]  := v.word1
8000414c:  sd   a5,16(s2)     -- *retslot[16] := v.word2
80004150:  ld   ra,168(sp)    -- epilogue restores (interleaved with li a0,3)
80004154:  ld   s0,160(sp)
80004158:  ld   s1,152(sp)
8000415c:  ld   s2,144(sp)
80004160:  ld   s3,136(sp)
80004164:  li   a0,3          -- x10 := 3 = StatusCode (.ret v)
80004168:  addi sp,sp,176
8000416c:  ret
```

## Structure

`execRetSim` mirrors `execExprSim` (`ExecExprRet.lean`): the `execBlockA` head
(prologue+dispatch to `0x80004120`) and the copy+epilogue TAIL are threaded
UNCONDITIONALLY around the recursion glue `hGlue`, which consumes the `EvalIH`
for the return expression. The glue postcondition is `SubExecReturnR` —
`SubExecReturn` (`ExecExprRet.lean`) PLUS the three `read64` facts on the
sub-sret buffer (the honest "`eval_expr` fills the whole 24-byte result buffer"
residual, needed for the reload `ld`s; the abstract `ValueRepr` alone only pins
the kind tag). `execRetGlue` discharges `hGlue` via the `ret`-arm setup
(`ld a2,8(s0)`, `beqz` not-taken, `mv a3,s3`, `mv a1,s1`, `addi a0,sp,16`) +
`armTail_rec_es`, and `execRetSimC` is the full case conditional only on named
residuals (the `execBlockA` geometry + the concrete sub-expr/code/headroom facts
+ the sub-sret readability), exactly the residual style of `execExprSimC`.

The `retNull` constructor (`return;`, `.ret none`) is a SEPARATE `ExecS`
constructor (`ExecS.retNull`) and is left as a follow-up (it takes the `beqz`
TAKEN path through `value_null`, not covered here).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
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

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `SubExecReturnR` — `SubExecReturn` + the sub-sret buffer readability

`SubExecReturn` re-represents `st'.store` and pins `ValueRepr … subsret vsub`,
but the three reload `ld`s at `0x80004138`/`0x8000413c`/`0x80004140` need the
buffer's three 8-byte words readable at the machine level. `ValueRepr` only pins
the 4-byte kind tag (and, per kind, the payload), not the full 24-byte struct;
so we carry the three `read64`s explicitly. (The concrete machine — `eval_expr`'s
sret write — does fill all 24 bytes; this is the abstraction's residual.) -/

/-! ## `ExecRetSimGoal` — the `ExecS.ret` simulation Triple (packaged) -/

/-! ## `execRetSim` — `ExecS.ret`: `execBlockA ≫ (jal eval_expr ≫ IH) ≫ copy ≫ epilogue`

The head (`execBlockA`, prologue+dispatch to `0x80004120`) and the 24-byte copy +
inline `li a0,3` epilogue TAIL are threaded UNCONDITIONALLY around the recursion
glue `hGlue` (which consumes the `EvalIH`). The `retval` disjunct is discharged
by `valueRepr_copy_of_writeWindow`: the three `sd`s write exactly
`[aRet, aRet+24)`, byte-for-byte copying the sub-result buffer where the
`ValueRepr vsub` lives. -/

end Vsa.Sim
