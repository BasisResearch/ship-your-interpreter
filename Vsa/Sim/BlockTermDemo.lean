import Vsa.Sim.BlockTerm
import Vsa.Sim.BlockTactics
import Vsa.Sim.SnprintfSpec18

/-!
# `BlockTermDemo` — acceptance derivation for the basic-block chain lemma

The real branch-crossing `memmove` dispatch + setup segment

```
  800069c4: bgeu a1,a0 → 800069f0   TAKEN  (arm 1: dst+n ≤ src ⇒ src ≥ᵤ dst)
  800069f0: li   a5,31
  800069f4: bltu a5,a2 → 80006a24   NOT taken (n ≤ 31)
  800069f8: mv   a5,a0
  800069fc: addi a3,a2,-1
  80006a00: beqz a2   → 80006ae0    NOT taken (1 ≤ n)
  80006a04: addi a3,a3,1
  80006a08: add  a3,a5,a3
  ⇒ 80006a0c (loop head)
```

— 8 steps across 4 basic blocks, derived by **one** `bblocks_sound_bt`
application with real byte pins (`Code.Memmove`) and real DecodeTable lemmas.
The conclusions match the `SnprintfSpec18` two-theorem ceremony
(`tr_dispatch_mv` arm 1 + `tr_setup_mv`): 8-step `Steps` chain,
`PC = 0x80006a0c`, `a0 = dst`, `a1 = src`, `a2 = n`, `ra = r`, `a5 = dst`,
`a3 = dst + n`, minstret, tick, memory + HTIF unchanged, and the register
frame outside the written `{a5, a3}`.  The three branch guards are the same
facts the ceremony proves (`bgeu_of_le` / `bltu_false_of_ge` /
`beq_false_of_toNat_ne`), phrased at the block lemma's *computed* values.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

