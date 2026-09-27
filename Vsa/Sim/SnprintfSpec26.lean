import Vsa.Sim.SnprintfSpec17
import Vsa.Sim.SnprintfSpec25
import Vsa.Sim.FrameOn

/-!
# M3 Layer-3 — `SnprintfSpec26` : PRINT/iov call setup ≫ flush ≫ svfprintf return
## `0x800078ac` (second-iovec entry) → svfprintf's `ret`, `a0 = total`

The glue that chains the verified PRINT/iov call setup into the verified
flush + return path:

    iov2ToSsprintCall_spec   (SnprintfSpec17: 0x800078ac → the jal completed,
                              PC = 0x8000e908, ra = 0x80008688)
      ≫ svfprintf_flushReturn_spec
                             (SnprintfSpec25: the __ssprint_r 2-iovec flush,
                              post-call cleanup, parse-loop NUL exit, epilogue,
                              PC = vra0 with a0 = the total)

`PreSr` (SnprintfSpec20) at the call is discharged from Spec17's postcondition
`writeMap` chain (the five writes: resid `sp+240 := n1+n2`, `iov[1].base
:= vbase` at `sp+368`, `iov[1].len := n2` at `sp+376`, count `sp+232 := 2`,
total `sp+16`) plus caller hypotheses transported across the writes through the
single pointwise agreement `hagree` (everything outside the five windows is
unchanged).

## Residual-hypothesis provenance

Every hypothesis below is established upstream on the real `%lld` run:

* register values at `0x800078ac` (`hx2 … hx28`) and the branch guards
  (`hvt0`, `hsubwle`, `hb256`, `hb4`) — the exit state of
  `printEntryToSignIov_spec` (SnprintfSpec11) / the parse-loop segments
  (Spec7–16); Spec11's post must still be strengthened to *export* them
  (its own composition note), so they are stated here;
* `hcnt0 … hcnt3` (count word = 1 at `sp+232`) — Spec11's `sw` (count 0 → 1
  over the prologue's `sw zero,232(sp)`);
* `hvcurF` (`a2 = cursor = n1`) — the prologue's `sd zero,240(sp)` plus
  Spec11's cursor bump (`0 → 1 = n1`); `hvnd6` (`s6` = digit count `n2`) —
  the digit-loop exit (Spec7's restore, `s6 = len`);
* `htotS`/`hstrS`/`hfmtS`/`hs020S` (total / sink-struct ptr / fmt cursor /
  parse slot at `sp+16/8/0/32`) — svfprintf prologue (`sd a1,8(sp)`) and
  parse loop; `hnulB` — the fmt NUL that ended the parse loop;
* `hviovS` + `hviovBN` (`mem[sp+224] = viovB = sp+352`) — the prologue's
  `addi s5,sp,352` / `sd s5,224(sp)` (uio.uio_iov := iov array);
  `hviov2N` (`s7 = sp+368`) — Spec11's `addi s7,s7,16`;
* `hiov0b`/`hiov0l`/`hsignB` (sign iovec `(sp+167, 1)` + the `'-'` byte) —
  Spec11's two `sd`s and the sign block (Spec4/6: the byte at `sp+167`
  survives to the PRINT segment);
* `hdigB` + `hvb1`/`hvb2` (digit bytes at `vbase`, inside the `BufInv` window
  `[vsp+328, vsp+348)` — the buffer top is `entryTop vsp = vsp+348` and at most
  20 digits are emitted, so `vbase = vsp+348−n2 ≥ vsp+328`) — the digit loop
  (Spec3/5) leaves the digits in svfprintf's stack buffer, `s10 = vbase`
  (Spec7's restore; see Spec37's `PreSr` instantiation for the exact base);
* `hsinkcur`/`hsinkcap`/`hfl0B`/`hfl1B`/`hflag`/`hcaplt`/`hcap31` — the FILE
  sink struct built by the `snprintf`/`_svsnprintf_r` wrapper (cursor `d`,
  capacity `cap32`, `_flags` bit 6 clear) — NOT yet verified (NEXT);
* the 15 spill slots `hsv1e8 … hsv248` — svfprintf's prologue `sd`s at
  `sp+488 … sp+584` (visible at `0x80007658 … 0x800076dc`), untouched since;
* `hfnslot`/`hmbB` — static locale data (`__global_locale.mbtowc =
  __ascii_mbtowc` at `0x8001b880`, `__mb_cur_max = 1` at `0x8001b8f8`),
  written once at startup — NOT yet verified (NEXT);
* `hmidregs` — the five register facts `iov2ToSsprintCall_spec`'s post omits
  (`gp = 0x8001b510`, `s1 = &__global_locale = 0x8001b798`, and x18/x19/x21
  defined): none of the 28 instructions `0x800078ac → 0x8000e908` writes
  x3/x9/x18/x19/x21, but Spec17 states no register frame, so (as with
  `env_get_found_spec`'s `hreach` residual) the preserved values are taken as
  a mid-state hypothesis, dischargeable mechanically once Spec17's post is
  strengthened with the obs-extraction additions its composition note already
  plans.  `gp` is set by crt0 and never rewritten; `s1` holds the current
  locale pointer loaded in svfprintf's prologue — NEXT;
* the layout block (`hsplo … hra0align`) — address facts of the concrete
  image (stack above `0x8001c000`, sink/dest above the static data, fmt
  cursor outside the touched windows).

The postcondition is `svfprintf_flushReturn_spec`'s, re-based to the memory at
`0x800078ac`: digits+sign flushed to `[d, d+n1+n2)`, sink cursor/capacity
updated, uio resid/count cleared, the wide-char out-slot zeroed, the running
total at `sp+16` (also returned in `a0`), and a pointwise frame outside nine
windows (Spec25's seven, plus the total slot `[sp+16, sp+24)` and the second
iovec entry `[sp+368, sp+384)`). -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

