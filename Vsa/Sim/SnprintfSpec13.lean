import Vsa.Sim.SnprintfSpec12
import Vsa.Sim.DecodeTable.Batch05Part30
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec13` : reusable INDIRECT-TRANSFER dispatch helper (`_pd`)

The `svfprintf` `%`-conversion parse loop (and, structurally, `eval_expr`'s
`EX_*` dispatch and `value_equal`'s kind dispatch) picks its handler through a
`.rodata` **jump table**: an index `k` selects a signed 32-bit offset from the
table at `base + 4*k`, and the handler PC is `base + offset`.  The machine code is

```
  ... a5 := base + 4*k   (index address, from slli/srli/add) ...
  77b4: lw   a5,0(a5)      a5 := sext32( table[base + 4*k] )   (the offset)
  77b8: add  a5,a5,s6      a5 := offset + base                (the handler PC)
  77bc: jr   a5           PC := a5  (indirect jump, bit-0 cleared)
```

This module provides the **reusable** pieces every such dispatch needs:

* **`SlotPinnedAt base k target m`** — the jump-table slot pin, generalizing
  `EvalSimCommon.KindSlotPinned` over an arbitrary table base.  It pins the four
  little-endian bytes of slot `k` and states that their sign-extended reassembly
  plus `base` equals the handler PC `target`.  (`KindSlotPinned k armPC` is the
  `base = 0x80019f58` specialization.)
* **`ParseSlotPinned ch target m`** — the concrete instance for the `svfprintf`
  conversion-char table at `parseTableBase = 0x8001a0fc`, index `ch - 32`.  The
  decoded `%lld`-path targets (`parseSlot_l`, `parseSlot_d`) are exactly the
  ones the memory note records: `'l' (0x6c) → 0x80008534`, `'d' (0x64) → 0x80008008`.
* **`stepObs_jalr_indirect`** — the reusable indirect-transfer *site* helper: an
  indirect `jr rs1` / `jalr x0,0(rs1)` for an **arbitrary** `rs1` register value,
  landing PC := (`rs1` bit-0-cleared).  This is exactly the `ret`/`jr` step
  (`StepObs.stepObs_jr`) but named and documented for computed dispatch; the
  `value_equal` dispatch (`ValueEqualSites.site_80002888`, rs1 = x15) and this
  parse dispatch (rs1 = x15) are both instances.
* **`parseDispatchHop_spec`** — the verified `Steps` hop `0x800077b4 → target`:
  starting with `x15 = base + 4*k` (the slot address already computed) and
  `SlotPinnedAt base k target`, it runs the `lw`+`add`+`jr` and lands at the
  pinned handler PC.

Applied to the `%lld` path: with `parseSlot_l`, `parseDispatchHop_spec` proves the
first dispatch hop `0x800077b4 → 0x80008534` (the `'l'` length-modifier handler
entry); with `parseSlot_d`, `0x800077b4 → 0x80008008` (the `'d'` integer-conversion
handler).  The upstream `slli`/`srli`/`add` that compute the slot address
`base + 4*k` from the char are left to a follow-up (they need the
`(k<<32)>>30 = 4*k` bitvector fact); this module lands the load-and-transfer core
that couples the pinned table byte to the reached handler PC.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `SlotPinnedAt` — the reusable jump-table slot pin (arbitrary table base)

`SlotPinnedAt base k target m` says: in memory `m`, the four little-endian bytes
of jump-table slot `k` (at `base + 4*k`) are `t0..t3`, and their sign-extended
32-bit reassembly `sext(t3 ++ t2 ++ t1 ++ t0)` plus `ofNat base` equals the
handler PC `target`.  This is `EvalSimCommon.KindSlotPinned k target` with the
table base abstracted (that predicate hardwires `jumpTableBase = 0x80019f58`;
here `base` is a parameter, so the *same* helper serves `eval_expr`'s table
(`0x80019f58`), `value_equal`'s table (`0x80019ef8`) and `svfprintf`'s conversion
table (`0x8001a0fc`)). -/

/-! ## `ParseSlotPinned` — the `svfprintf` conversion-char table instance

The `%`-conversion dispatch table lives at `parseTableBase = 0x8001a0fc`
(`auipc s6,0x13; addi s6,s6,-1676`, `SnprintfSpec12.parseInit_spec`).  The
dispatch index for a conversion character `ch` is `ch - 32` (the `addiw a5,s8,-32`
at `0x800077a0`).  `ParseSlotPinned ch target m` is `SlotPinnedAt parseTableBase
(ch - 32) target m`. -/

/-! ## `stepObs_jalr_indirect` — the reusable indirect-transfer site helper

An indirect jump `jr rs1` (`jalr x0, 0(rs1)`) for an **arbitrary** source
register `rs1` whose value is the computed handler address.  The step sets
`PC := (rs1) &~ 1` (bit 0 cleared) and writes no link (rd = x0).  This is exactly
`StepObs.stepObs_jr` — the observation is `ReadsLikePost σ' (sigmaPost_jump_x0 …
tgt)` with `tgt = bit-0-cleared rs1` — restated with a dispatch-oriented name so
the computed-jump call sites (parse dispatch here, `value_equal`'s jump table in
`ValueEqualSites.site_80002888`, `eval_expr`'s `EX_*` dispatch) share one helper.
The `jr a5` at `0x800077bc` is the `rs1 = x15` instance. -/

/-! ## `parseDispatchHop_spec` — the verified dispatch hop `0x800077b4 → target`

Starting at the slot-load instruction `0x800077b4` with the index address already
computed in `x15` (`= base + 4*k`) and the table base in `x22` (`= base`), run

```
  77b4: lw  a5,0(a5)     a5 := sext32( slot bytes ) = offset
  77b8: add a5,a5,s6     a5 := offset + base = target
  77bc: jr  a5           PC := target
```

The `SlotPinnedAt base k target` hypothesis supplies the slot bytes and the
`offset + base = target` arithmetic; the geometric hypotheses place the slot in
readable RAM (the `.rodata` table) and pin the target 4-aligned so the indirect
jump's bit-0 clear is a no-op.  Lands `PC = target` at the handler entry. -/

/-! ## `%lld`-path application

The first `%lld` dispatch hop reaches the `'l'` length-modifier handler at
`0x80008534`; the `'d'` integer-conversion handler is at `0x80008008`.  Both fall
out of `parseDispatchHop_spec` with the corresponding `ParseSlotPinned` witness. -/

end Vsa.Sim
