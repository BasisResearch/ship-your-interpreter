import Vsa.Sim.BlockMem
import Vsa.Sim.Code.__ssputs_r
import Vsa.Sim.DecodeTable.Batch16Part01
import Vsa.Sim.DecodeTable.Batch06Part31
import Vsa.Sim.DecodeTable.Batch04Part10
import Vsa.Sim.DecodeTable.Batch06Part30
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part22

/-!
# `BlockMemDemo` — acceptance derivation for `block_mem_sound`

The real mixed ALU + STORE + LOAD segment: the `__ssputs_r` prologue run
`0x8001438c – 0x800143a4` (7 instructions),

```
  8001438c: addi sp,sp,-64        ALU   (writes the base of the three stores!)
  80014390: sd   s1,40(sp)        STORE (base = the *just-written* sp)
  80014394: lw   s1,12(a1)        LOAD  (pins on the post-store-1 memory)
  80014398: sd   s0,48(sp)        STORE
  8001439c: sd   ra,56(sp)        STORE
  800143a0: mv   s0,a1            ALU
  800143a4: mv   a5,a2            ALU
```

derived by **one** application of `block_mem_sound`, with real byte pins
(`Code.__ssputs_r_at_*`) and real DecodeTable lemmas — producing the same
conclusions as the per-site ceremony (`SnprintfSpec19.tr_ssputs_head`'s first
seven steps / the `/tmp` ceremony measurement file): the 7-step `Steps` chain,
`PC = 0x800143a8`, the four written registers (`sp`, the loaded `s1`, `s0`,
`a5`), the three nested `writeMap8` memory images, minstret, HTIF output, and
an `x10` frame.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The block description: `addi/sd/lw/sd/sd/mv/mv`, fully concrete. -/
def ssputsProlog : List MInstr :=
  [⟨0x8001438c#64, 0xfc010113#32, 0x13#8, 0x01#8, 0x01#8, 0xfc#8, .addi, 2, 2, 0, 0xfc0#12⟩,
   ⟨0x80014390#64, 0x02913423#32, 0x23#8, 0x34#8, 0x91#8, 0x02#8, .sd, 0, 2, 9, 0x028#12⟩,
   ⟨0x80014394#64, 0x00c5a483#32, 0x83#8, 0xa4#8, 0xc5#8, 0x00#8, .lw, 9, 11, 0, 0x00c#12⟩,
   ⟨0x80014398#64, 0x02813823#32, 0x23#8, 0x38#8, 0x81#8, 0x02#8, .sd, 0, 2, 8, 0x030#12⟩,
   ⟨0x8001439c#64, 0x02113c23#32, 0x23#8, 0x3c#8, 0x11#8, 0x02#8, .sd, 0, 2, 1, 0x038#12⟩,
   ⟨0x800143a0#64, 0x00058413#32, 0x13#8, 0x84#8, 0x05#8, 0x00#8, .addi, 8, 11, 0, 0x000#12⟩,
   ⟨0x800143a4#64, 0x00060793#32, 0x93#8, 0x07#8, 0x06#8, 0x00#8, .addi, 15, 12, 0, 0x000#12⟩]

/-- The `__ssputs_r` prologue via ONE `block_mem_sound` application.  The
data-dependent hypotheses are exactly the per-site ceremony's: RAM-bounds /
window / alignment for the three stack stores (addressed off the *computed*
`sp' = v2 - 64`), bounds + byte pins for the `lw` — the pins stated on the
post-store-1 memory, which is where the block reads them. -/
theorem ssputs_prologue_block (σ : MState) (i u : Nat)
    (vm v1 v2 v8 v9 v11 v12 : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8001438c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx1 : σ.regs.get? Register.x1 = some v1)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (h40lo : 0x80000000 ≤
      (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x028#12)).toNat)
    (h40hi : (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x028#12)).toNat + 8
      ≤ 0x100000000)
    (h40win : tohostAddr + 16 ≤
      (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x028#12)).toNat)
    (h40al : (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x028#12)).toNat % 8
      = 0)
    (h48lo : 0x80000000 ≤
      (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x030#12)).toNat)
    (h48hi : (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x030#12)).toNat + 8
      ≤ 0x100000000)
    (h48win : tohostAddr + 16 ≤
      (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x030#12)).toNat)
    (h48al : (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x030#12)).toNat % 8
      = 0)
    (h56lo : 0x80000000 ≤
      (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x038#12)).toNat)
    (h56hi : (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x038#12)).toNat + 8
      ≤ 0x100000000)
    (h56win : tohostAddr + 16 ≤
      (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x038#12)).toNat)
    (h56al : (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x038#12)).toNat % 8
      = 0)
    (hclo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x00c#12)).toNat)
    (hchi : (v11 + sign_extend (m := 64) (0x00c#12)).toNat + 4 ≤ 0x100000000)
    (hcht : (v11 + sign_extend (m := 64) (0x00c#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x00c#12)).toNat)
    (hcal : (v11 + sign_extend (m := 64) (0x00c#12)).toNat % 4 = 0)
    (hc0 : (writeMap8 σ.mem
        (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x028#12)).toNat
        (sdData_val v9))[(v11 + sign_extend (m := 64) (0x00c#12)).toNat]? = some b0)
    (hc1 : (writeMap8 σ.mem
        (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x028#12)).toNat
        (sdData_val v9))[(v11 + sign_extend (m := 64) (0x00c#12)).toNat + 1]? = some b1)
    (hc2 : (writeMap8 σ.mem
        (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x028#12)).toNat
        (sdData_val v9))[(v11 + sign_extend (m := 64) (0x00c#12)).toNat + 2]? = some b2)
    (hc3 : (writeMap8 σ.mem
        (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x028#12)).toNat
        (sdData_val v9))[(v11 + sign_extend (m := 64) (0x00c#12)).toNat + 3]? = some b3)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 7⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (writeMap8 (writeMap8 σ.mem
          (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x028#12)).toNat
          (sdData_val v9))
          (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x030#12)).toNat
          (sdData_val v8))
          (v2 + sign_extend (m := 64) (0xfc0#12) + sign_extend (m := 64) (0x038#12)).toNat
          (sdData_val v1) ∧
      σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (0x800143a8#64) ∧
      σ'.regs.get? Register.x2 = some (v2 + sign_extend (m := 64) (0xfc0#12)) ∧
      σ'.regs.get? Register.x9
        = some (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))) ∧
      σ'.regs.get? Register.x8 = some (v11 + sign_extend (m := 64) (0x000#12)) ∧
      σ'.regs.get? Register.x15 = some (v12 + sign_extend (m := 64) (0x000#12)) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      σ'.regs.get? Register.x10 = σ.regs.get? Register.x10 := by
  obtain ⟨hp1_0, hp1_1, hp1_2, hp1_3⟩ := Vsa.Sim.Code.__ssputs_r_at_8001438c hmem
  obtain ⟨hp2_0, hp2_1, hp2_2, hp2_3⟩ := Vsa.Sim.Code.__ssputs_r_at_80014390 hmem
  obtain ⟨hp3_0, hp3_1, hp3_2, hp3_3⟩ := Vsa.Sim.Code.__ssputs_r_at_80014394 hmem
  obtain ⟨hp4_0, hp4_1, hp4_2, hp4_3⟩ := Vsa.Sim.Code.__ssputs_r_at_80014398 hmem
  obtain ⟨hp5_0, hp5_1, hp5_2, hp5_3⟩ := Vsa.Sim.Code.__ssputs_r_at_8001439c hmem
  obtain ⟨hp6_0, hp6_1, hp6_2, hp6_3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143a0 hmem
  obtain ⟨hp7_0, hp7_1, hp7_2, hp7_3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143a4 hmem
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, hframe⟩ :=
    block_mem_sound ssputsProlog σ i u (0x8001438c#64) vm
      [(2, v2), (9, v9), (8, v8), (1, v1), (11, v11), (12, v12)]
      [[b0, b1, b2, b3]]
      hG hpc hmi ⟨hx2, hx9, hx8, hx1, hx11, hx12, trivial⟩
      (show KeysOK [2, 9, 8, 1, 11, 12] by decide)
      ⟨⟨hp1_0, hp1_1, hp1_2, hp1_3⟩, Vsa.Sim.DecodeTable.decode_fc010113, trivial,
       ⟨hp2_0, hp2_1, hp2_2, hp2_3⟩, Vsa.Sim.DecodeTable.decode_02913423,
         ⟨h40lo, h40hi, h40win, h40al⟩,
       ⟨hp3_0, hp3_1, hp3_2, hp3_3⟩, Vsa.Sim.DecodeTable.decode_00c5a483,
         ⟨⟨hclo, hchi, hcht, hcal⟩, hc0, hc1, hc2, hc3⟩,
       ⟨hp4_0, hp4_1, hp4_2, hp4_3⟩, Vsa.Sim.DecodeTable.decode_02813823,
         ⟨h48lo, h48hi, h48win, h48al⟩,
       ⟨hp5_0, hp5_1, hp5_2, hp5_3⟩, Vsa.Sim.DecodeTable.decode_02113c23,
         ⟨h56lo, h56hi, h56win, h56al⟩,
       ⟨hp6_0, hp6_1, hp6_2, hp6_3⟩, Vsa.Sim.DecodeTable.decode_00058413, trivial,
       ⟨hp7_0, hp7_1, hp7_2, hp7_3⟩, Vsa.Sim.DecodeTable.decode_00060793, trivial, trivial⟩
      (show BlockOKM (0x8001438c#64) [2, 9, 8, 1, 11, 12] ssputsProlog by decide) hi
  rw [show endPCM (0x8001438c#64) ssputsProlog = (0x800143a8#64 : BitVec 64) from by decide]
    at hpc'
  exact ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc',
    hGH.2.2.2.1, hGH.2.2.1, hGH.2.1, hGH.1, hmi',
    hframe Register.x10 (by decide) (by decide)⟩

end Vsa.Sim
