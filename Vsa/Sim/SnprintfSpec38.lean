import Vsa.Sim.SnprintfSpec37

/-!
# M3 Layer-3 — `SnprintfSpec38` : the FULL svfprintf `%lld` spec
## `0x80007654` (`_svfprintf_r` ABI entry) → svfprintf's `ret`, `a0 = 1 + n2`

THE svfprintf capstone: one `Steps` chain

    svfEntryToSsprintCall_spec  (Spec37 : 0x80007654 → 0x8000e908, `PreSr`
                                 assembled + every non-wrapper Spec25 input)
  ≫ svfprintf_flushReturn_spec  (Spec25 : the `__ssprint_r` 2-iovec flush,
                                 post-call cleanup, parse-loop NUL exit,
                                 epilogue, `ret` with `a0 = the total`)

from the `_svfprintf_r` ABI entry (reent/FILE/fmt/va registers, the `"%lld"`
bytes, the sink FILE struct pins, the image statics, the value ghosts
`hneg`, layout) to svfprintf's `ret` with

* **`a0 = BitVec.ofNat 64 (1 + n2)`** — the total character count (`1` sign
  byte + `n2` digits), also pinned at the (dead) total slot;
* the destination buffer `[d, d + 1 + n2)` = the `'-'` byte (`signByte`)
  followed by the `n2` decimal digits — the exact Spec37 formula
  `bs2 k = ofNat 8 (48 + (mag / 10^(n2−1−k)) % 10)` for the magnitude
  `mag = ((0#64) − llArg …).toNat`, with `1 ≤ n2 ≤ 20`, the leading-digit
  bound `mag / 10^(n2−1) ≤ 9` and the minimality bound
  `n2 = 1 ∨ 9 < mag / 10^(n2−2)` (the leading digit is nonzero — `n2` is
  exactly the decimal digit count, from the widened `DLI`);
* the FILE cursor slot := `d + ofNat (1+n2)` and the capacity slot :=
  `cap32 − 1 − n2` (32-bit);
* callee-saves x8/x9/x18–x27 and `sp` restored, `PC = x1 = vra0`;
* a pointwise memory frame outside `[vsp − 88, vsp + 592)` (svfprintf's frame
  plus the `__ssprint_r`/`__ssputs_r` sub-frames), the destination window and
  the two written FILE fields.

## Residual hypotheses (wrapper-owned only)

Exactly Spec37's wrapper-owned inputs — the sink FILE struct (`hsinkcur`/
`hsinkcap`/capacity bounds/the `_flags` bytes with the `0x080` **and** `0x040`
bits clear), the destination-buffer layout, the va-area bytes + layout, the
value ghosts (negative, magnitude > 9), the `"%lld"` bytes, the static-image
pins, and the fmt/stack layout — plus `vra0` 4-aligned and two fmt-vs-sink/
dest disjointness facts (`hfd`/`hfpp`) the return path's re-read of the fmt
NUL needs.  `hfstk` is stated with the `vsp − 128` margin (the fmt bytes must
survive the flush sub-frames; on the real run the format is a `.rodata`
string far below the stack).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

