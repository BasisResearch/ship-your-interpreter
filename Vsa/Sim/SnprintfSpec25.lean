import Vsa.Sim.SnprintfSpec20
import Vsa.Sim.SnprintfSpec24
import Vsa.Sim.Mfr

/-!
# M3 Layer-3 — `SnprintfSpec25` : the composed svfprintf **flush return path**
## `0x8000e908` (the `jal __ssprint_r` completed) → svfprintf's `ret`, `a0 = total`

The glue for flush part 3b (pctrace `0x80008688 → 0x80007918 → parse-loop NUL
exit → epilogue 0x800079b0 → ret with a0 = mem[sp+16]`):

    ssprint_iov2_spec (SnprintfSpec20, r := 0x80008688)
      ≫ retA_spec (Spec21: beqz a0 / count clear / j loop head)
      ≫ retB_spec (Spec22: loop head + __locale_mb_cur_max + __ascii_mbtowc,
                   the NUL is read, mbtowc = 0)
      ≫ retC_spec (Spec23: pending-literal length = 0 → epilogue)
      ≫ retD_spec (Spec24: epilogue reloads → ret, a0 := mem[sp+16])

`ssprint_iov2_post` is consumed as the state at the return point: `a0 = 0` /
`PC = 0x80008688` discharge segment A's guards; its `Pin8 (q+16) 0` becomes the
`ld a5,240(sp) = 0` read; its pointwise six-window memory frame transports the
caller's prologue spills (`SlotHolds` at `sp+0x1e8 … sp+0x248`), the parse
state (`sp+0`, `sp+8`, `sp+16`, `sp+32`), the locale data pins and the format
NUL byte across the whole `__ssprint_r` call (`slotHolds_of_agree_rt`).

Residual caller obligations (all facts about the state at the `jal`, provided
by the earlier flush segments / the prologue when the full path is glued):
`PreSr` itself, the prologue spill slots, `mem[sp+32] = 0`, the fmt-NUL byte,
the FILE `_flags` bytes with bit 6 clear, `gp`/`s1`/locale-data constants, and
the address-layout disjointness hypotheses. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

