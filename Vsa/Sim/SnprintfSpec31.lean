import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesRet

/-!
# M3 Layer-3 — `SnprintfSpec31` : svfprintf prologue segment E
## `0x800076f4 → 0x80007728` (the `jal __locale_mb_cur_max`)

Zero inits of the parse-state slots (incl. the TOTAL at `sp+16` — Spec26's
`htotS`), `s1 := &__global_locale`, the `'%'`/`16` constants, the fmt spill
`sd s6,0(sp)` and its immediate reload, and the static `mbtowc` function
pointer load `ld s4,232(s1)` (the parse loop's indirect callee).
Generated in the SnprintfSpec22 house style by /tmp/gen_spec31.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

