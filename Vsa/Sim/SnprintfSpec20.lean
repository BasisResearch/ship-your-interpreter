import Vsa.Sim.SsprintSites
import Vsa.Sim.SnprintfSpec19
import Vsa.Sim.SnprintfSpec9
import Vsa.Sim.RegPins
import Vsa.Sim.PtrArith
import Vsa.Sim.DecodeTable.Batch11Part27
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec20` : the `__ssprint_r` 2-iovec flush loop (`_sr`)

Total-correctness spec for the `%lld`-flush call of `__ssprint_r`
(`0x8000e908 … 0x8000e9c8`), composed twice with the verified `__ssputs_r`
fast path (`ssputs_fast_spec`, SnprintfSpec19) at the `jal` site `0x8000e97c`.

`__ssprint_r(reent, cursor_struct, uio)` is entered with

* `a0 = va0` (the reent pointer, passed through to `__ssputs_r`),
* `a1 = p` (the string-sink cursor struct: cursor `d` at `[p,p+8)`, capacity
  word `cap32` at `[p+12,p+16)`),
* `a2 = q` (the `_uio`-like struct: iov base pointer `viov` at `[q,q+8)`,
  iov count (= `2`) at `[q+8,q+12)`, resid (= `n1+n2`) at `[q+16,q+24)`),

and a 2-entry iov array at `viov`: `iov[0] = (s1, n1)` (the sign byte,
`bs1`) and `iov[1] = (s2, n2)` (the digits, `bs2`).  On this path the
`beqz`-empty short circuit at `0x8000e91c` is NOT taken, the loop runs
exactly twice (count `2 → 1 → 0`, resid `n1+n2 → n2 → 0`), each iteration
calls `__ssputs_r(reent, p, iov[i].base, iov[i].len)`, and the common tail
restores `ra/s0/s1/s2/s3/s4/s5/sp`, clears the `q` resid/count fields and
returns `0`.

The deliverable `ssprint_iov2_spec` : from the entry, the machine runs to
`PC = r` with `a0 = 0`, `[d,d+n1) = bs1`, `[d+n1,d+n1+n2) = bs2`, the cursor
slot advanced to `d + (n1+n2)`, the capacity word decremented twice
(`cap32 - n1 - n2`), the `q` resid/count fields zeroed, all callee-saves and
`sp` restored, and every byte outside the six written windows unchanged.

The second call's capacity guard comes from the first call's postcondition:
`swData (spNewCap cap32 n1) = cap32 - ofNat n1` (`swData_spNewCap`), whose
sign-extension is `cap32.toNat - n1` under the caller-level side conditions
`n1 + n2 < cap32.toNat < 2^31`.

Composition: `tr_ssprint_entry` (16 sites, `0xe908 → 0xe950`) `.seq`
`tr_ssprint_iter1` (18 sites + call 1, back to `0xe950`) `.seq`
`tr_ssprint_iter2` (18 sites + call 2, to `0xe99c`) `.seq`
`tr_ssprint_tail` (12 sites, to `ret`).

Sites are the generated `Vsa/Sim/SsprintSites.lean` battery
(`scripts/ssprint_sites.tsv`); the single `sub a4,a4,s2` site at `0x8000e98c`
is hand-written below (`gen_sites.py` has no RTYPE-SUB class).  Register
threading uses the `RegPins` pin lists (`pins_alu`/`pins_store`/… + one
`pins_of_frame` per call).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Small value bridges -/

/-! ## Code-region survival

`__ssprint_r` spans `[0x8000e908, 0x8000e9f8)`; `__ssputs_r` ends at
`0x80014520`; `memmove` ends at `0x80006b00`.  All data windows on this path
sit above `tohostAddr + 16 = 0x8001ad10`, above all three code regions. -/

/-! ## The hand-written RTYPE-SUB site (`gen_sites.py` gap)

`0x8000e98c: sub a4,a4,s2` — the generator supports `alu_add`/`subw` but not
64-bit `SUB`; this mirrors the `alu_add` template with
`execute_rtype_sub_char`. -/

/-! ## The seven-slot stack image

`__ssprint_r`'s prologue spills, in program order: `s1@sp+40`, `ra@sp+56`,
`s0@sp+48`, `s3@sp+24`, `s4@sp+16`, `s5@sp+8`, `s2@sp+32` (with the new
`sp = vsp - 64`), i.e. absolute slots `vsp-24, vsp-8, vsp-16, vsp-40,
vsp-48, vsp-56, vsp-32`. -/

/-! ## Ghost register frame (`NotWrittenSr`) and the callee-frame adapter -/

/-- Registers `__ssprint_r` itself may write: the `__ssputs_r` write-set
(`NotWrittenSp`, which includes memmove noise) plus `s2/s3/s4/s5`. -/
abbrev NotWrittenSr (R : Register) : Prop :=
  (Register.x18 == R) = false ∧ (Register.x19 == R) = false ∧
  (Register.x20 == R) = false ∧ (Register.x21 == R) = false ∧
  NotWrittenSp R

theorem NotWrittenSr.sp {R : Register} (h : NotWrittenSr R) : NotWrittenSp R := h.2.2.2.2

/-! ## Region / side-condition bundle -/

/-! ## Pin-list surgery helpers

`pins_cons` re-adds a register at the head after a site wrote it;
`pins_dropK` removes the `K`-th pin before transporting across a site that
writes that register. -/

/-! ## Pre / mid conditions -/

/-! ## Entry: `0x8000e908 → 0x8000e950` (16 sites, `beqz` NOT taken) -/

/-! ## Mid-states after iteration 1 and after the loop -/

/-! ## Iteration 1: `0x8000e950 → … → jal __ssputs_r (iov[0]) → … → 0x8000e950` -/

/-! ## Iteration 2: `0x8000e950 → … → jal __ssputs_r (iov[1]) → … → 0x8000e99c` -/

/-! ## Postcondition and the tail: `0x8000e99c → ret` -/

/-! ## The composed 2-iovec flush spec -/

end Vsa.Sim
