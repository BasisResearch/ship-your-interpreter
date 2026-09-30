import Vsa.Sim.SnprintfSites
import Vsa.Sim.DecodeTable.Batch15Part23
import Vsa.Sim.DecodeTable.Batch11Part23
import Vsa.Sim.DecodeTable.Batch09Part12
import Vsa.Sim.DecodeTable.Batch07Part02
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part23

/-!
# M3 Layer-3 — `SnprintfSites2` : the sign-block + indirect-dispatch step battery

Session-4 file (`_sn4` suffix on all new names).  Extends the loop-body site
battery of `SnprintfSites.lean` with:

* the **sign block** of the `%lld` path (`experiments/M3-snprintf-lld.md` §1.3(c),
  disasm `[0x800080dc, 0x800080f4]`): the `bgez` split on the signed argument, the
  `'-'` sign-byte handling, and the `neg` producing the unsigned magnitude;
* the **conversion-char dispatch** `jr a5` at `0x800077bc` — the computed-goto
  jump table whose slot resolves the `%lld`→`d` handler.

## Sign-byte placement finding (buffer vs flush)

The disassembly is unambiguous: the `'-'` byte is stored by
`0x800080f0 sb a5,167(sp)` into a **dedicated stack slot** `167(sp)` — *not* into
the descending digit buffer (which starts at `sp+348` and grows downward, written
by `0x8000832c sb a0,-1(s9)`).  The sign byte is later **read back** at
`0x80008388 lbu t5,167(sp)` by the pad/emit machinery and prepended into the iov
that `__ssprint_r` flushes.  So: **the `'-'` is prepended at flush, never written
into the digit buffer.**  This is exactly `intToString (.negSucc m) = "-" ++
natToString (m+1)`: the sign and the magnitude digits are produced independently
and concatenated, the sign first.

## What is a step here vs a boundary hypothesis

There is no `stepObs_load` primitive in the current Sail-model step layer (LOADs
have no observational-step lemma; only ALU/branch/store/jump do).  The two loads
of the sign block —`0x800080dc ld a3,0(a4)` (fetch the 64-bit va_list arg) and
the preceding `ld a4,24(sp)`— are therefore modelled as a **boundary**: the site
lemmas below take the loaded argument value `v` as a hypothesis (`x13 = v` after
the load), and step the ALU/branch/store instructions that consume it.  The same
convention is used for the interleaved `0x800080e0 sd a5,24(sp)` (va_list bump,
an 8-byte stack store off the live path) and `0x800080f8 bltz s4` (the
already-set-flag guard): they are not on the value-producing path and are elided
from the linear trace, documented at the composition in `SnprintfSpec4.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Byte-word helpers for the new sign-block / dispatch words

Mirror the `w_*_sn` / `nr_*_sn` shape of `SnprintfSites.lean`.  `_sn4` suffix. -/

/-! ## Shared decode-prelude helper (same as `SnprintfSites`). -/

/-! ## Sign-block sites -/

/-! ### 0x800080e4 — `mv a4,a3` = `addi x14,x13,0` (x14 := x13 = the arg value) -/

/-! ### 0x800080e8 — `bgez a3` = `BTYPE(imm,x0,x13,BGE)` : taken iff `a3 ≥s 0`

Taken (`a3 ≥ 0`, non-negative) jumps to `0x80008050` (skip the sign block).
Not-taken (`a3 < 0`, negative) falls through to `0x800080ec` (emit `'-'`, `neg`). -/

/-! ### 0x800080ec — `li a5,45` = `addi x15,x0,45` (x15 := '-') -/

/-! ### 0x800080f0 — `sb a5,167(sp)` = `STORE(0x0a7,x15,x2,1)` : sign byte → 167(sp)

The load-bearing placement site: `'-'` (`x15`) is stored at `sp+167`, a dedicated
stack slot *disjoint* from the digit buffer at `sp+348 …`.  `v2 = sp`, `vdata =
x15`. -/

/-! ### 0x800080f4 — `neg a4,a4` = `RTYPE(x14,x0,x14,SUB)` : x14 := 0 - x14 (magnitude)

The two's-complement negation.  For a negative signed argument `v`, the result
`0 - v = BitVec.neg v` read as unsigned is `|v|` — including `INT64_MIN`, where
`neg` wraps to the same bit pattern but is consumed as unsigned `2^63` by the
loop (the arithmetic-core `neg_magnitude` lemma, `SnprintfSpec.lean`). -/

/-! ## The conversion-char dispatch — `jr a5` at `0x800077bc`

`jr a5` = `JALR(0x000, x15, x0)` (link `x0`, no return address written): an
indirect jump to `x15 = a5`.  On the `%lld` path, `a5` was computed by the
preceding table lookup

```
800077b0  add  a5,a5,s6      ; a5 = table_base + (char-32)*4
800077b4  lw   a5,0(a5)      ; a5 = table[char-32]   (a relative offset word)
800077b8  add  a5,a5,s6      ; a5 = table_base + offset  (the concrete handler PC)
800077bc  jr   a5            ; → handler
```

so `a5` holds a *concrete* address once the rodata table slot is pinned (the
`MaskPinned`/jump-table precedent — a data byte-pin makes the loaded offset a
literal).  This site takes that resolved target `tgt = a5` as a hypothesis and
steps to `PC := tgt`; the dispatch composition (future) supplies `tgt` = the
`d`-conversion handler `0x800080c4` by pinning `table[0x64-0x20]` and the base
`s6 = 0x8001a0fc`.  Target alignment (`tgt.toNat % 4 = 0`) is a hypothesis
(handler PCs are word-aligned). -/

end Vsa.Sim
