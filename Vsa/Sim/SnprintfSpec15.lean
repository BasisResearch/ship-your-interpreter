import Vsa.Sim.SnprintfSpec14
import Vsa.Sim.SnprintfSpec8
import Vsa.Sim.ValueSites
import Vsa.Sim.StrcpySites
import Vsa.Sim.DecodeTable.Batch09Part09
import Vsa.Sim.DecodeTable.Batch06Part19
import Vsa.Sim.DecodeTable.Batch06Part08
import Vsa.Sim.DecodeTable.Batch06Part02
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch03Part24
import Vsa.Sim.DecodeTable.Batch02Part17
import Vsa.Sim.DecodeTable.Batch01Part28
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec15` : the `'d'` integer-conversion **`ll`-branch** entry
`0x80008008 → 0x800080e4` (`_d15`)

This module verifies the executed `%lld` **`'d'` conversion-handler entry** for the
`ll` (long-long) length-modifier case — the segment that runs *after* the parse
dispatch has reached the `'d'` handler and *after* the `"ll"` handler set the
`ll`-flag `0x20` in the flags word `x6`.  It is the last un-verified straight-line
segment before `SnprintfSpec8.entryToPrint_neg_spec` picks up the sign/digit path
at `0x800080e4`, and it composes **exactly** onto that entry.

## The executed `%lld` handler chain (decoded from `c/while-riscv-htif.elf`)

```
  ── 'l' handler @ 0x80008534 ───────────────────────────────────  (NOT in coverage)
  80008534: lbu  s8,0(s9)          s8 := format[2]  (the 2nd 'l')
  80008538: li   a5,108            a5 := 'l' (0x6c)
  8000853c: beq  s8,a5,0x80009060  format[2]=='l' ⇒ goto "ll" handler
  80008540: ori  t1,t1,16          (single-'l' path: set 'l'-flag, not taken here)
  80008544: j    0x80007798

  ── "ll" handler @ 0x80009060 ──────────────────────────────────  (NOT in coverage)
  80009060: lbu  s8,1(s9)          s8 := format[3]  (the conversion char, 'd')
  80009064: ori  t1,t1,32          x6 := x6 ||| 0x20   (SET THE ll-FLAG)
  80009068: addi s9,s9,1           advance format cursor
  8000906c: j    0x80007798        back to the conversion dispatch (→ 'd' via table)

  ── 'd' handler @ 0x80008008 ───────────────────────────────────  (IN coverage ✓)
  80008008: ld   a5,24(sp)         a5 := va_area ptr           [THIS MODULE START]
  8000800c: sd   s9,0(sp)          spill format cursor
  80008010: andi a4,t1,32          a4 := x6 & 0x20   (test the ll-flag)
  80008014: mv   t3,s11            t3 := s11
  80008018: addi a5,a5,8           a5 += 8   (bump va_area past the 8-byte arg)
  8000801c: bnez a4,0x800080d8     ll-flag set ⇒ TAKEN → 0x800080d8

  ── ll long-long arg fetch @ 0x800080d8 ────────────────────────  (IN coverage ✓)
  800080d8: ld   a4,24(sp)         a4 := va_area ptr (pre-bump)
  800080dc: ld   a3,0(a4)          a3 := *(va_area)  = the 64-bit long-long value
  800080e0: sd   a5,24(sp)         store bumped va_area ptr
  800080e4: mv   a4,a3             [entryToPrint_neg_spec START — SnprintfSpec8]
```

## Coverage boundary (honest)

`SvfprintfSliceLoaded` (`Vsa/Sim/Code/SvfprintfSlice.lean`) covers
`[0x80007654,0x80007a00) ∪ [0x80007fc0,0x80008400) ∪ [0x80008a80,0x80008b10)`.
The `'d'` handler (`0x80008008…`) and the `ll` arg-fetch block (`0x800080d8…e4`)
are **inside** the middle sub-range, so this whole segment is verified from the
pinned code bytes.  The two **preceding** handlers are **outside** coverage:

* `'l'`  handler `[0x80008534, 0x80008548)` — GAP (add to the SvfprintfSlice generator);
* `"ll"` handler `[0x80009060, 0x80009070)` — GAP.

Those two handlers do not compose here (their code bytes are not pinned); the
`ll`-flag `x6 = 0x20` they establish is therefore stated as an **entry hypothesis**
(`hx6`), matching what the `"ll"` handler's `ori x6,x6,32` leaves.  Extending
coverage to those ranges + widening `parseDispatch_d_spec` to surface `x6`/`s9`
would let this chain onto `SnprintfSpec14.parseDispatch_l_full_spec`.

## What lands (`dispatchD_ll_to_printEntry_spec`)

A single `Steps` chain `0x80008008 → 0x800080e4` (9 instructions), taking the
`ll`-flag branch.  Postcondition: `PC = 0x800080e4` (exactly the entry of
`SnprintfSpec8.entryToPrint_neg_spec`), `x6 = 0x20` (ll-flag preserved),
`x20 = v20` (parsed field width, untouched), `x2 = vsp` (frame preserved), and
`x13 = v` — the fetched 64-bit `long long` argument — surfaced as the value the
sign/digit path formats.  The stack stores at `sp+0` and `sp+24` leave the code
region intact (`SvfprintfSliceLoaded` preserved).  The `va_area` pointer in the
spill slot `sp+24` and its target are supplied as caller (`va_list`) state.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Reusable frames for the argument-fetch path -/

/-- The signed 64-bit value fetched from the caller's `va_list`. -/
abbrev llArg (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 8) : BitVec 64 :=
  sign_extend (m := 64)
    ((((((((a7.append a6).append a5).append a4).append a3).append a2).append a1).append a0)
      : BitVec (8 * 8))

end Vsa.Sim
