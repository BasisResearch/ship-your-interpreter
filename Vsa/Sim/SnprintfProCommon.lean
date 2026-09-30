import Vsa.Sim.RegPins
import Vsa.Sim.SlotFrame
import Vsa.Sim.PtrArith
import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.SnprintfSpec11
import Vsa.Sim.SnprintfSpec19
import Vsa.Sim.CodeRangeInsert
import Vsa.Sim.Code.Strlen
import Vsa.Sim.Code.__locale_mb_cur_max
import Vsa.Sim.Code.__ascii_mbtowc
import Vsa.Sim.Code.Memset
import Vsa.Sim.Code._localeconv_r

/-!
# M3 Layer-3 — shared helpers for the svfprintf PROLOGUE + first-parse-pass segments

Pin-list surgery (`pins_cons_pro` / `pins_dropN_pro`), the `sp -= 592`
prologue round-trip, `Loaded`-survival for the callee code regions touched by
the prologue path (`memset`), and small value/guard folds shared by
`SnprintfSpec27`–`SnprintfSpec34`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

