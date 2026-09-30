import Vsa.Sim.SnprintfSites
import Vsa.Sim.ValueSites
import Vsa.Sim.StrcpySites
import Vsa.Sim.DecodeTable.Batch15Part25
import Vsa.Sim.DecodeTable.Batch11Part17
import Vsa.Sim.DecodeTable.Batch10Part14
import Vsa.Sim.DecodeTable.Batch10Part06
import Vsa.Sim.DecodeTable.Batch08Part23
import Vsa.Sim.DecodeTable.Batch08Part17
import Vsa.Sim.DecodeTable.Batch07Part20
import Vsa.Sim.DecodeTable.Batch07Part16
import Vsa.Sim.DecodeTable.Batch07Part14
import Vsa.Sim.DecodeTable.Batch06Part29
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch03Part27
import Vsa.Sim.DecodeTable.Batch02Part09
import Vsa.Sim.DecodeTable.Batch02Part07
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch01Part02

/-!
# M3 Layer-3 — `SnprintfSites3` : the decimal-loop entry step battery (`_sn5`)

Sites for the segment between the sign block and the digit loop
(`experiments/M3-snprintf-lld.md` §1.4): the flag guard `bltz s4` at
`0x800080f8`, the flag mask `andi t1,t1,-129`, the fast/multi split
`li a5,9; bltu a5,a4` at `0x80008100/04`, and the multi-digit loop-entry block
`0x800082c8 … 0x800082f8` (buffer-top setup, five `sd` spills, one `ld` reload,
digit count/grouping-flag init, `mv s0,a4`, and the `j 0x8000831c` into the
do-while's mod-emit step).

Instruction words were decoded from the pinned code bytes
(`Code/SvfprintfSlice.lean`); the decode lemmas are the exhaustive
`DecodeTable.Batch*` shards.  Store sites use `exec_sd_val`
(`ValueSites`), the reload uses `exec_ld_total` (`StrcpySites` — total, no
byte-definedness needed since the value is dead downstream).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

