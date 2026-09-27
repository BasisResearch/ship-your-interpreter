import Vsa.Sim.ValueEqualSites
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.DecodeTable.Batch12Part21
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch03Part20
import Vsa.Sim.DecodeTable.Batch02Part23

/-!
# Layer 3 — per-site observational step lemmas for the `str`-`str` handler of `value_equal`

The `str` handler (`0x800028c4 … 0x800028e4`) is the only `value_equal` handler with a
stack footprint (it spills `ra`):

```
0x800028c4  ld a1,8(a1)      ; a1 := *(a1+8)  = string ptr b        (word 0x0085b583)
0x800028c8  ld a0,8(a0)      ; a0 := *(a0+8)  = string ptr a        (word 0x00853503)
0x800028cc  addi sp,sp,-16   ; sp := entry_sp - 16                  (word 0xff010113)
0x800028d0  sd ra,8(sp)      ; mem[sp+8 .. sp+16) := ra             (word 0x00113423)
0x800028d4  jal strcmp       ; ra := 0x800028d8; PC := 0x80006ea0   (word 0x5cc040ef)
0x800028d8  ld ra,8(sp)      ; ra := *(sp+8) (restore)              (word 0x00813083)
0x800028dc  seqz a0,a0       ; a0 := (a0 == 0) ? 1 : 0              (word 0x00153513)
0x800028e0  addi sp,sp,16    ; sp := entry_sp (restore)             (word 0x01010113)
0x800028e4  ret              ; PC := ra (= r)                       (reuse `site_ret_gen`)
```

The `sd ra,8(sp)` writes the stack slot at `(entry_sp-16)+8 = entry_sp-8`; the spill
survives the `strcmp` call (which does not touch that slot) and is restored by `ld ra`.

All byte facts for these addresses come from `Value_equalLoaded` (`value_equal_at_*`).
Site bodies mirror `EnvNewSites` (store / jal / ld) and `ValueEqualSites` (alu / seqz /
ret): the write / no-read side goals are discharged inline by `BitVec.eq_of_toNat_eq;
decide` and the decode by the generated `DecodeTable.decode_*` lemmas.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

