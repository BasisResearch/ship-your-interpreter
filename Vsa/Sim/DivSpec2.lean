import Vsa.Sim.DivLoops
import Vsa.Sim.DivSites2
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — total-correctness specs for the signed/remainder division wrappers

Config-level composition of the wrapper site steps (`Vsa/Sim/DivSites2.lean`)
around the shared unsigned core `udivdi3_spec` (`Vsa/Sim/DivLoops.lean`) into
total-correctness triples for the three libgcc wrapper entries:

* `umoddi3_spec` (`__umoddi3`, entry `0x800046f4`): unsigned remainder.
* `moddi3_spec`  (`__moddi3`,  entry `0x80004728`): signed remainder.
* `divdi3_spec`  (`__divdi3`,  entry `0x800046a4`): signed quotient.

## Threading the core call

The wrappers save the return address in `t0`/`x5` and call the unsigned core via
`jal`, returning through `jr t0`. Preservation of `x5` (and every other
non-clobbered register) across the core is recovered through the blanket
ghost-frame conjunct now carried by `Ust`/`udivdi3_post` (`DivSpec.lean`): at the
`jal`-successor state `cent`, we instantiate the core's ghost `g` with
`cent.σ.regs.get?` (so the entry frame `hframe` is `rfl`), and `udivdi3_post` then
returns `∀ R, NotWritten R → cent'.σ.regs.get? R = cent.σ.regs.get? R`; specialised
at `x5` this recovers the saved return address after the core runs.

## `divdi3` control-flow map (from `experiments/disasm.txt`)

```
46a4 bltz a0 → 4704            ; a0 < 0 ?
46a8 bltz a1 → 4714            ; a1 < 0 ?
46ac …core…  (a0≥0, a1≥0) ; core returns via ret/x1 straight to divdi3's caller
                            ; (no result fixup — quotient already correct sign)
--- a0 < 0 arm (from 4704) ---
4704 neg a0,a0                ; a0 := -a0
4708 bgtz a1 → 4718           ; a1 > 0 ? (mixed signs) → save-ra path
470c neg a1,a1                ; a1 ≤ 0 : both negative → negate a1 too
4710 j 46ac                   ; tail-call core (returns via ret/x1; quotient +)
--- a1 < 0 arm (from 4714), also fall-through target of the mixed path ---
4714 neg a1,a1                ; a1 := -a1
4718 mv t0,ra                 ; save ra (mixed signs: result must be negated)
471c jal 46ac                 ; call core, ra := 4720
4720 neg a0,a0                ; a0 := -quotient
4724 jr t0                    ; return
```

So `divdi3` has TWO ways into the core: (a) fall-through / `j` at `4710`
(same-sign, core returns straight via `x1 = ` original caller `ra`, no fixup);
(b) `jal` at `471c` (mixed sign, `t0 = ra`, negate result, `jr t0`). This is why
`divdi3` does not uniformly use `jal`: the same-sign paths reuse the caller's
return slot directly.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `__umoddi3` — unsigned remainder (entry `0x800046f4`)

```
f4 mv t0,ra   ; t0 := r
f8 jal 46ac   ; call unsigned core; ra := fc
fc mv a0,a1   ; a0 := a1 = n % d
00 jr t0      ; return to r
```

`umoddi3_pre`: at `0x800046f4` with `x10 = n`, `x11 = d`, `x1 = r`, `mem = m0`,
`d ≠ 0`, `r` 4-aligned, and BOTH the wrapper (`__umoddi3Loaded`) and core
(`__hidden___udivdi3Loaded`) regions loaded. -/

end Vsa.Sim
