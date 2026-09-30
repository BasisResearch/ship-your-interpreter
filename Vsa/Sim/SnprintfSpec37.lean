import Vsa.Sim.SnprintfSpec36
import Vsa.Sim.SnprintfSpec16
import Vsa.Sim.SnprintfSpec26
import Vsa.Sim.PinW
import Vsa.Sim.SnprintfSpec44

/-!
# M3 Layer-3 — `SnprintfSpec37` : svfprintf entry → the `__ssprint_r` call
## `0x80007654` (`_svfprintf_r` ABI entry) → `0x8000e908` with `PreSr` assembled

THE post-widening capstone: one `Steps` chain

    svfPrologueParse_spec       (Spec36 : 0x80007654 → 0x80008534)
  ≫ parseToPrintEntry_spec      (Spec16 : 0x80008534 → 0x800080e4, widened)
  ≫ entryToPrint_neg_spec       (Spec8  : 0x800080e4 → 0x8000782c, widened)
  ≫ printEntryToSignIov_spec    (Spec11 : 0x8000782c → 0x800078ac, widened)
  ≫ iov2ToSsprintCall_spec      (Spec17 : 0x800078ac → jal done, PC = 0x8000e908,
                                 widened — kills Spec26's `hmidregs`)

from the svfprintf ABI entry with the `"%lld"` format and a negative multi-digit
argument to the completed `jal __ssprint_r`, with **`PreSr` fully assembled**
(n1 = 1 sign byte + n2 = p+1 digit bytes, count = 2, resid = 1+n2, both iovec
entries written, the running total `1+n2` at `sp+16`) plus every
`svfprintf_flushReturn_spec` (Spec25) input that is not wrapper-owned: `gp`,
the locale statics, the parse-state slots (fmt cursor at the NUL, FILE ptr,
total, `sp+0x20 = 0`), the 13 prologue spill slots, the fmt NUL byte, the FILE
`_flags` bytes, and a pointwise frame outside `[vsp, vsp+592)`.

## Residual hypotheses (the wrapper-owned facts; everything else is derived)

* the sink FILE struct built by `snprintf`/`_svsnprintf_r` (`hsinkcur`,
  `hsinkcap`, `hcap21`, `hcap31`, the `_flags` bytes `hfl0B/hfl1B/hflagB`) and
  the destination-buffer layout (`hdge/hdhi/hdstk`);
* the `va_list` area (`hvva*` layout + the eight argument bytes `ha0..ha7`);
* the argument-value ghost `hneg` (negative — ANY magnitude; the single-digit
  fast path is `entryToPrint_neg_any_spec`'s Spec43 arm);
* the static data / code pins of the loaded image (link-time constants);
* the `"%lld"` format bytes and the fmt/stack layout (as in Spec36).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

