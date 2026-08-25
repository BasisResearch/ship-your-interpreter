import Vsa.Sim.BlockTerm
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
open Vsa.Sim.Code (MemmoveLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Block 1: the dispatch head — empty body, `bgeu a1,a0 → 0x800069f0` TAKEN. -/
def mvB1 : BBlock :=
  { body := [],
    term := some ⟨0x800069c4#64, 0x02a5f663#32, 0x63#8, 0xf6#8, 0xa5#8, 0x02#8,
      .br bop.BGEU true, 11, 10, 0x002c#13, 0#21, 0#12⟩ }

/-- Block 2: `li a5,31`, then `bltu a5,a2` NOT taken. -/
def mvB2 : BBlock :=
  { body := [⟨0x800069f0#64, 0x01f00793#32, 0x93#8, 0x07#8, 0xf0#8, 0x01#8,
      .addi, 15, 0, 0, 0x01f#12⟩],
    term := some ⟨0x800069f4#64, 0x02c7e863#32, 0x63#8, 0xe8#8, 0xc7#8, 0x02#8,
      .br bop.BLTU false, 15, 12, 0x0030#13, 0#21, 0#12⟩ }

/-- Block 3: `mv a5,a0; addi a3,a2,-1`, then `beqz a2` NOT taken. -/
def mvB3 : BBlock :=
  { body := [⟨0x800069f8#64, 0x00050793#32, 0x93#8, 0x07#8, 0x05#8, 0x00#8,
      .addi, 15, 10, 0, 0x000#12⟩,
     ⟨0x800069fc#64, 0xfff60693#32, 0x93#8, 0x06#8, 0xf6#8, 0xff#8,
      .addi, 13, 12, 0, 0xfff#12⟩],
    term := some ⟨0x80006a00#64, 0x0e060063#32, 0x63#8, 0x00#8, 0x06#8, 0x0e#8,
      .br bop.BEQ false, 12, 0, 0x00e0#13, 0#21, 0#12⟩ }

/-- Block 4: `addi a3,a3,1; add a3,a5,a3`, fall-through to the loop head. -/
def mvB4 : BBlock :=
  { body := [⟨0x80006a04#64, 0x00168693#32, 0x93#8, 0x86#8, 0x16#8, 0x00#8,
      .addi, 13, 13, 0, 0x001#12⟩,
     ⟨0x80006a08#64, 0x00d786b3#32, 0xb3#8, 0x86#8, 0xd7#8, 0x00#8,
      .add, 13, 15, 13, 0#12⟩],
    term := none }

def mvDispatchSetup : List BBlock := [mvB1, mvB2, mvB3, mvB4]

/-- The `memmove` dispatch (arm 1) + setup segment,
`0x800069c4 (bgeu taken) → 0x800069f0 … → 0x80006a0c`, via ONE
`bblocks_sound_bt` application. -/
theorem mv_dispatch_setup_block (σ : MState) (i u : Nat)
    (vm r dst src : BitVec 64) (n : Nat)
    (hn1 : 1 ≤ n) (hn31 : n ≤ 31)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x800069c4#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx10 : σ.regs.get? Register.x10 = some dst)
    (hx11 : σ.regs.get? Register.x11 = some src)
    (hx12 : σ.regs.get? Register.x12 = some (BitVec.ofNat 64 n))
    (hx1 : σ.regs.get? Register.x1 = some r)
    (hmem : MemmoveLoaded σ.mem)
    (hd : dst.toNat + n ≤ src.toNat)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 8⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (0x80006a0c#64) ∧
      σ'.regs.get? Register.x10 = some dst ∧
      σ'.regs.get? Register.x11 = some src ∧
      σ'.regs.get? Register.x12 = some (BitVec.ofNat 64 n) ∧
      σ'.regs.get? Register.x1 = some r ∧
      σ'.regs.get? Register.x15 = some dst ∧
      σ'.regs.get? Register.x13 = some (dst + BitVec.ofNat 64 n) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ nn ∈ ([15, 15, 13, 13, 13] : List Nat), (gprReg nn == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  have hntn : (BitVec.ofNat 64 n : BitVec 64).toNat = n :=
    BitVec.toNat_ofNat _ _ ▸ Nat.mod_eq_of_lt (by omega)
  obtain ⟨hc4_0, hc4_1, hc4_2, hc4_3⟩ := Vsa.Sim.Code.memmove_at_800069c4 hmem
  obtain ⟨hf0_0, hf0_1, hf0_2, hf0_3⟩ := Vsa.Sim.Code.memmove_at_800069f0 hmem
  obtain ⟨hf4_0, hf4_1, hf4_2, hf4_3⟩ := Vsa.Sim.Code.memmove_at_800069f4 hmem
  obtain ⟨hf8_0, hf8_1, hf8_2, hf8_3⟩ := Vsa.Sim.Code.memmove_at_800069f8 hmem
  obtain ⟨hfc_0, hfc_1, hfc_2, hfc_3⟩ := Vsa.Sim.Code.memmove_at_800069fc hmem
  obtain ⟨h00_0, h00_1, h00_2, h00_3⟩ := Vsa.Sim.Code.memmove_at_80006a00 hmem
  obtain ⟨h04_0, h04_1, h04_2, h04_3⟩ := Vsa.Sim.Code.memmove_at_80006a04 hmem
  obtain ⟨h08_0, h08_1, h08_2, h08_3⟩ := Vsa.Sim.Code.memmove_at_80006a08 hmem
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, hframe⟩ :=
    bblocks_sound_bt mvDispatchSetup σ i u (0x800069c4#64) vm
      [(10, dst), (11, src), (12, BitVec.ofNat 64 n), (1, r)] []
      hG hpc hmi ⟨hx10, hx11, hx12, hx1, trivial⟩
      (show KeysOK [10, 11, 12, 1] by decide)
      ⟨⟨trivial, ⟨⟨hc4_0, hc4_1, hc4_2, hc4_3⟩, Vsa.Sim.DecodeTable.decode_02a5f663⟩,
          bgeu_of_le src dst (by omega)⟩,
       ⟨⟨⟨hf0_0, hf0_1, hf0_2, hf0_3⟩, Vsa.Sim.DecodeTable.decode_01f00793, trivial, trivial⟩,
        ⟨⟨hf4_0, hf4_1, hf4_2, hf4_3⟩, Vsa.Sim.DecodeTable.decode_02c7e863⟩,
        show zopz0zI_u ((0#64) + sign_extend (m := 64) (0x01f#12)) (BitVec.ofNat 64 n)
            = false by
          rw [li31_val]
          exact bltu_false_of_ge _ _
            (by rw [hntn, show (0x1f#64 : BitVec 64).toNat = 31 from by decide]; omega)⟩,
       ⟨⟨⟨hf8_0, hf8_1, hf8_2, hf8_3⟩, Vsa.Sim.DecodeTable.decode_00050793, trivial,
          ⟨hfc_0, hfc_1, hfc_2, hfc_3⟩, Vsa.Sim.DecodeTable.decode_fff60693, trivial, trivial⟩,
        ⟨⟨h00_0, h00_1, h00_2, h00_3⟩, Vsa.Sim.DecodeTable.decode_0e060063⟩,
        beq_false_of_toNat_ne (BitVec.ofNat 64 n) (0#64)
          (by rw [hntn, show (0#64 : BitVec 64).toNat = 0 from by decide]; omega)⟩,
       ⟨⟨⟨h04_0, h04_1, h04_2, h04_3⟩, Vsa.Sim.DecodeTable.decode_00168693, trivial,
          ⟨h08_0, h08_1, h08_2, h08_3⟩, Vsa.Sim.DecodeTable.decode_00d786b3, trivial, trivial⟩,
        trivial, trivial⟩,
       trivial⟩
      (show ChainOK (0x800069c4#64) [10, 11, 12, 1] mvDispatchSetup by decide) hi
  rw [chainEndPC_eq_bt mvDispatchSetup (0x800069c4#64) _ _ (by decide),
    show chainEndPCc (0x800069c4#64) mvDispatchSetup = (0x80006a0c#64 : BitVec 64)
      from by decide] at hpc'
  have ha13 : σ'.regs.get? Register.x13
      = some ((dst + sign_extend (m := 64) (0x000#12))
        + ((BitVec.ofNat 64 n + sign_extend (m := 64) (0xfff#12))
          + sign_extend (m := 64) (0x001#12))) := hGH.1
  rw [sext0_add dst, dec1_fwd n hn1 (by omega), dec1_back n hn1 (by omega)] at ha13
  have ha15 : σ'.regs.get? Register.x15
      = some (dst + sign_extend (m := 64) (0x000#12)) := hGH.2.1
  rw [sext0_add dst] at ha15
  exact ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc',
    hGH.2.2.1, hGH.2.2.2.1, hGH.2.2.2.2.1, hGH.2.2.2.2.2.1, ha15, ha13, hmi',
    fun R hn hw => hframe R hn hw⟩

end Vsa.Sim
