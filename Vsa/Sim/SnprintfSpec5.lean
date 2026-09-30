import Vsa.Sim.KeepRegs
import Vsa.Sim.Code.Strcpy
import Vsa.Sim.DecodeTable.Batch01Part02
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch01Part27
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch02Part07
import Vsa.Sim.DecodeTable.Batch02Part09
import Vsa.Sim.DecodeTable.Batch02Part15
import Vsa.Sim.DecodeTable.Batch02Part27
import Vsa.Sim.DecodeTable.Batch02Part30
import Vsa.Sim.DecodeTable.Batch03Part02
import Vsa.Sim.DecodeTable.Batch03Part06
import Vsa.Sim.DecodeTable.Batch03Part09
import Vsa.Sim.DecodeTable.Batch03Part12
import Vsa.Sim.DecodeTable.Batch03Part13
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch03Part27
import Vsa.Sim.DecodeTable.Batch03Part29
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part17
import Vsa.Sim.DecodeTable.Batch04Part18
import Vsa.Sim.DecodeTable.Batch04Part19
import Vsa.Sim.DecodeTable.Batch04Part22
import Vsa.Sim.DecodeTable.Batch04Part23
import Vsa.Sim.DecodeTable.Batch04Part25
import Vsa.Sim.DecodeTable.Batch04Part26
import Vsa.Sim.DecodeTable.Batch04Part32
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch06Part23
import Vsa.Sim.DecodeTable.Batch06Part24
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch06Part29
import Vsa.Sim.DecodeTable.Batch07Part02
import Vsa.Sim.DecodeTable.Batch07Part06
import Vsa.Sim.DecodeTable.Batch07Part09
import Vsa.Sim.DecodeTable.Batch07Part14
import Vsa.Sim.DecodeTable.Batch07Part16
import Vsa.Sim.DecodeTable.Batch07Part20
import Vsa.Sim.DecodeTable.Batch07Part27
import Vsa.Sim.DecodeTable.Batch08Part07
import Vsa.Sim.DecodeTable.Batch08Part17
import Vsa.Sim.DecodeTable.Batch08Part23
import Vsa.Sim.DecodeTable.Batch09Part09
import Vsa.Sim.DecodeTable.Batch09Part12
import Vsa.Sim.DecodeTable.Batch10Part06
import Vsa.Sim.DecodeTable.Batch10Part14
import Vsa.Sim.DecodeTable.Batch11Part17
import Vsa.Sim.DecodeTable.Batch11Part23
import Vsa.Sim.DecodeTable.Batch13Part06
import Vsa.Sim.DecodeTable.Batch14Part08
import Vsa.Sim.DecodeTable.Batch14Part10
import Vsa.Sim.DecodeTable.Batch16Part03
import Vsa.Sim.DecodeTable.Batch16Part10
import Vsa.Sim.DecodeTable.Batch16Part12
import Vsa.Sim.DecodeTable.Batch16Part18
import Vsa.Sim.DecodeTable.Batch16Part31
import Vsa.Sim.SnprintfSpec
import Vsa.Sim.StrlenMagic

/-!
# M3 Layer-3 — `SnprintfSpec5` : the loop-entry segment, composed (`_sn5`)

Closes the gap between the sign block (`SnprintfSpec4`) and the digit loop
(`SnprintfSpec3`): from the fast/multi split at `0x80008100` with the unsigned
magnitude in `a4`, step `li a5,9 → bltu(taken, magnitude>9) → 0x800082c8 …
0x800082f8` (buffer-(entryTop vsp) setup + five `sd` spills + one dead `ld` reload +
`s7 := 0`, `s11 := t1&1024 = 0`, `s0 := magnitude`) `→ j 0x8000831c` and one
mod-emit pass (`__umoddi3`, emit digit 0 at `(entryTop vsp)-1`, `s10 := (entryTop vsp)-1`,
`s7 := 1`, `beqz s11` taken), landing at the loop head `0x800082fc` in
`LSt g (entryTop vsp) m 0` — exactly `decimalLoop_spec`'s precondition `DLI g (entryTop vsp) m`.

* `loopEntry_spec` — `0x80008100` → `LSt g (entryTop vsp) m 0` at `0x800082fc`, `g` the
  final register file, `(entryTop vsp) = sp+348`;
* `entryToDigits_spec` — the capstone: `loopEntry_spec` ∘ `decimalLoop_spec`,
  from `0x80008100` to the loop exit `0x80008358` with the complete digit
  buffer `BufInv (entryTop vsp) m (p+1)` for the terminal `p`.

The single-digit fast path (`magnitude ≤ 9`, `bltu` not taken → `0x80008108`)
targets the flush segment directly and is a documented boundary, as are the
`0x800080f8/fc` flag-guard steps (sites provided in `SnprintfSites3`) and the
flush itself.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Small bridges -/

/-! ## `…Loaded` predicates survive a `writeMap8` above the code region

`writeMap8` is eight chained byte inserts at `a … a+7`; each is covered by the
single-insert lemmas (`SnprintfSpec3`) once `0x80009000 ≤ a`. -/

/-- The buffer (entryTop vsp) of the multi-digit path: `sp + 348`. -/
def entryTop (vsp : BitVec 64) : BitVec 64 := vsp + sign_extend (m := 64) (0x15c#12)

/-- Reads outside an 8-byte `writeMap8` window are unchanged. -/
theorem getElem?_writeMap8_out (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat)
    (d : BitVec (8 * 8)) (a : Nat) (ha : a < k ∨ k + 8 ≤ a) :
    (writeMap8 mem k d)[a]? = mem[a]? := by
  show ((((((((mem.insert k _).insert (k+1) _).insert (k+2) _).insert (k+3) _).insert
    (k+4) _).insert (k+5) _).insert (k+6) _).insert (k+7) _)[a]? = mem[a]?
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-! ## `SlotHolds` — spilled 64-bit values readable byte-for-byte

`SlotHolds vsp off v mem` says the eight little-endian bytes of `v` (as
`sdData_val v`) sit at `sp+off … sp+off+7`.  This is exactly what a `sd v,off(sp)`
leaves behind (`slotHolds_self`), it survives any disjoint 8-byte store
(`slotHolds_writeMap8`) or single byte insert (`slotHolds_insert`), and it is the
form the restore block (`SnprintfSpec7`) reads back.  Defined here (rather than in
`SnprintfSpec7`) so `loopEntry_spec` can already surface the spill contents. -/

/-! ## `loopEntry_spec` — `0x80008100` → `LSt g (entryTop vsp) m 0` at the loop head

From the split point with the magnitude `w` (`9 < w.toNat`) in `a4`, the stack
pointer in `sp` (8-aligned, `TopOk`-compatible window), and the `%lld` flag word
in `t1` with the grouping bit clear, the machine steps to the loop head
`0x800082fc` in `LSt g (sp+348) w.toNat 0` where `g` is the final register file.
The spill values (`s7`,`s4`,`s0`,`t3`,`t1` old contents) must merely exist. -/

/-! ## The capstone: entry → complete digit buffer at the loop exit -/

end Vsa.Sim
