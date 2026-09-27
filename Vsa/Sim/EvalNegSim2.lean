import Vsa.Sim.EvalNegSim
import Vsa.Sim.NegTailSites
import Vsa.Sim.NegBlockProto
import Vsa.Sim.BlockTactics2
import Vsa.Sim.BlockAdapter
import Vsa.Sim.BlockLogic
import Vsa.Sim.ValueSpec
import Vsa.Sim.DivSites2
import Vsa.Sim.ObsAvoid
import Vsa.Sim.ExitFootprint

/-!
# Layer 4 — M4 pilot RECURSIVE case: the `neg` post-call tail (`blockC_neg`)

Continues `EvalNegSim.lean` (`blockB_unary`, ending in `SubEvalReturn … 0x800035ec`):
the `neg`-op post-call tail of the `EX_UNARY` arm. Machine path
(`experiments/pctrace.md`):

```
800035ec: lw   a4,8(s0)        # op token (s0 = caller Expr node = aExpr)
800035f0: li   a5,12           # T_MINUS = 12 = unOpTok .neg
800035f4: ld   a3,144(sp)      # v[0..8) (kind dword; bytes 4-7 dead)
800035f8: beq  a4,a5,800039ac  # neg vs not — TAKEN (op = 12)
-- neg tail @ 0x800039ac: --
800039ac: ld   a1,152(sp)      # v payload  n  (subsret+8)
800039b0: ld   a4,160(sp)      # v[16..24)  (dead — presence only)
800039b4: lw   a0,144(sp)      # v.kind  = 2
800039b8: sd   a3,240(sp)      # runtime-error arg staging (inside frame)
800039bc: sd   a1,248(sp)
800039c0: sd   a4,256(sp)
800039c4: li   a2,2            # VAL_INT = 2
800039c8: lw   s0,4(s0)        # s0 := e->line (CLOBBERS s0)
800039cc: bne  a0,a2,80003b58  # kind != int — NOT taken (kind = 2)
800039d0: neg  a1,a1           # a1 := 0 - n  (64-bit wrap)
800039d4: mv   a0,s1           # a0 := outer sret
800039d8: jal  value_int       # value_int(sret, -n)
800039dc: j    800033ec        # shared epilogue → blockD_v
```

Output: `PreEpilogueV … (.int (wrap64 (-n))) 0x800033ec` (fed unchanged to
`blockD_v`). The produced value is `.int (wrap64 (-n))` — exactly what the
amended `EvalE.neg` rule derives — via `neg_wrap_bridge` below.

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

/-! ## The wrap64 bridge for the `neg` exit value

`value_int_spec` produces `.int (BitVec.ofNat 64 pay.toNat).toInt` with the
payload `pay = 0#64 - n_bv` (the machine `neg`). Since `n_bv.toInt = n` (the
sub-value's `.int n` `ValueRepr` payload), this equals `.int (wrap64 (-n))`:
`BitVec.ofNat 64 x.toNat = x` (round-trip), `0#64 - n_bv = -n_bv`, and
`(-n_bv).toInt = wrap64 (-(n_bv.toInt))` via `BitVec.ofInt_neg`/`ofInt_toInt`.
At `n = -2^63` this gives `-2^63` (`wrap64_neg_min`), matching the machine. -/

/-! ## `readI64` extraction from `ValueRepr … (.int n)` -/

/-! ## Presence lift over `MemExtends`

The tail's `ld a3,144(sp)`/`ld a1,152(sp)`/`ld a4,160(sp)` read the whole
sub-`Value` buffer `[subsret, subsret+24)`; `ValueRepr … (.int n)` pins only
the kind word `[subsret, subsret+4)` and the payload `[subsret+8, subsret+16)`.
The dead bytes (`[subsret+4, subsret+8)`, `[subsret+16, subsret+24)`) must still
be PRESENT for the machine `ld`. They live in the caller's lowered frame
`[SL.lo, sp)` (populated at the pre-call memory `mcall` by the layout), so
`MemExtends mcall c.σ.mem` carries their presence to the post-call memory. The
the dead sub-`Value` padding bytes are read TOTALLY (wave 48k) — no frame-populated premise.
**WAVE 47i (`McallPopTotality`) AMENDMENT**: pointwise form — the old
totality-consuming form (`hpop : ∀ a, ∃ b, mcall[a]? = some b`) fed the
refuted `hMcallPop` oracle (`experiments/fleet/obstructions/
McallPopTotality.lean`); callers now hold a WINDOWED presence fact and apply
it at each concrete dead-byte address. -/

/-! ## `Value_intLoaded` survives agreement on `value_int`'s code region

The `value_int` code lives at `[0x8000280c, 0x8000281c)` (a separate function
from `eval_expr`), so `SubEvalReturn` — which only re-exposes `Eval_exprLoaded`
— does not carry it. The arm entry supplies `Value_intLoaded mcall`; this lemma
transports it to the post-sub-call memory via agreement on that region. -/

/-! ## `blockC_neg` — the post-call `neg` tail -/

end Vsa.Sim
