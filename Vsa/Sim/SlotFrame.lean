import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.ValueEqualSpec3
import Vsa.Sim.SsputsSites

/-!
# `SlotFrame` — unified stack-spill save / survive / reload API

Every verified function with a stack frame re-derives the same three facts:

1. **save** — after an `sd rs2,off(sp)` site, the 8 bytes at `sp+off` hold the
   value (`SlotHolds`, defined in `SnprintfSpec5`);
2. **survive** — `SlotHolds` transported across later disjoint writes (byte
   inserts, `writeMap4`/`writeMap8` stores, and whole verified sub-calls whose
   memory frame says "outside `[lo, hi)` unchanged");
3. **reload** — an `ld rd,off(sp)` site whose byte hypotheses are fed from
   `SlotHolds`, with the loaded sign-extended byte-append reassembling to the
   original value.

This file gathers the scattered machinery under uniform names:

* `slot_save`        — wraps `slotHolds_self`            (`SnprintfSpec5`);
* `slot_survives_insert`    — wraps `slotHolds_insert`   (`SnprintfSpec5`);
* `slot_survives_writeMap4` — two-sided generalization of
  `slotHolds_writeMap4_i2` (`SnprintfSpec17`), proved from `slotHolds_insert`;
* `slot_survives_writeMap8` — wraps `slotHolds_writeMap8` (`SnprintfSpec5`);
* `slot_survives_frame`     — NEW: transport across any pointwise
  "outside `[lo, hi)` unchanged" memory frame (the shape verified sub-call
  postconditions expose, e.g. `memmove_fwd_post` in `SnprintfSpec18`);
* `slot_reload_bytes`  — unpack `SlotHolds` into the eight `h0…h7` byte facts an
  `exec_ld`-style site wants;
* `slot_reassemble`    — wraps `ve_sext_reassemble` (`ValueEqualSpec3`): the
  sign-extended little-endian append of the eight stored bytes is the value.

Note on generality: `SlotHolds` (`SnprintfSpec5`) hardwires the effective
address as `base + sign_extend (BitVec.ofNat 12 off)`.  The `base` is an
arbitrary 64-bit pointer (usually `sp`, but nothing forces that); the offset is
a `Nat` fed through `ofNat12`, matching the 12-bit immediates of `sd`/`ld`
sites.  We keep exactly that shape here so the wrappers compose with all the
existing `SlotHolds` consumers without conversion.

A worked end-to-end `example` (sd postcondition → save → survive a later
disjoint `writeMap8` → reload bytes feeding the real `ld ra,56(sp)` site
`site_143e0_sp` from `SsputsSites` → reassemble) closes the file.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## 1. save -/

/-! ## 2. survive -/

/-! ## 3. reload -/

/-! ## Worked example — save → survive → reload through a real `ld` site

`σ` sits at the `__ssputs_r` epilogue's `ld ra,56(sp)` (`site_143e0_sp`,
`SsputsSites`).  Its memory is: some base memory `m0`, then the spilling
`sd`'s `writeMap8` at `sp+56` (the postcondition equation an sd site leaves
behind), then a later disjoint 8-byte store at `k`.  The chain
`slot_save → slot_survives_writeMap8 → slot_reload_bytes → site_143e0_sp →
slot_reassemble` recovers the spilled `vra` in `ra`. -/
end Vsa.Sim
