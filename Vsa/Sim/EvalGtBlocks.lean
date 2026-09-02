import Vsa.Sim.AddTailSites
import Vsa.Sim.BlockMem
import Vsa.Sim.BlockTactics
import Vsa.Sim.BlockDecode
import Vsa.Sim.DecodeTable.Batch09Part24
import Vsa.Sim.DecodeTable.Batch09Part25
import Vsa.Sim.DecodeTable.Batch09Part32
import Vsa.Sim.DecodeTable.Batch05Part26
import Vsa.Sim.DecodeTable.Batch05Part24
import Vsa.Sim.DecodeTable.Batch11Part25
import Vsa.Sim.DecodeTable.Batch05Part29

/-!
# `EvalGtBlocks` — three straight-line eval-expr blocks via ONE `block_mem_sound` each

Merged from three isolated pilots (Blk2, BlkLdSt, BlkCmp).  Each block is a
self-contained standalone lemma derived by ONE `block_mem_sound` application.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

-- No heartbeat/recDepth overrides: block_mem_sound reflection elaborates within ALL defaults.

namespace Vsa.Sim

/-! ## Blk2 — straight-line block 0x80003538 … 0x80003554 -/

/-- The straight-line body, fully concrete via `mkLine` (auto-decode). -/
def evalGtBlk2 : List MInstr :=
  [mkLine 0x80003538#64 0x02079713#32,   -- slli x14,x15,0x20
   mkLine 0x8000353c#64 0x01e75793#32,   -- srli x15,x14,0x1e
   mkLine 0x80003540#64 0x00017717#32,   -- auipc x14,0x17
   mkLine 0x80003544#64 0xa4470713#32,   -- addi  x14,x14,-1468
   mkLine 0x80003548#64 0x00e787b3#32,   -- add   x15,x15,x14
   mkLine 0x8000354c#64 0x0007a783#32,   -- lw    x15,0(x15)
   mkLine 0x80003550#64 0x00013803#32,   -- ld    x16,0(x2)
   mkLine 0x80003554#64 0x00e787b3#32]   -- add   x15,x15,x14

/-- The block-computed effective address of `lw x15,0(x15)` at 0x8000354c: the
`add` result at 0x3548 (`srli(slli(x15))` + `auipc+(-1468)`), plus the zero
offset.  This is exactly `eaddrM` at that element, so the load MemFact goal is
discharged by defeq. -/
def blk2LwAddr (v15 : BitVec 64) : BitVec 64 :=
  ((shift_bits_right
        (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0))
        (Sail.BitVec.extractLsb (0x1e#6) 5 0))
    + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ (0x000#12)))
        + sign_extend (m := 64) (0xa44#12)))
  + sign_extend (m := 64) (0x000#12)

/-- The straight-line body of the eval-expr dispatch prologue via ONE
`block_mem_sound`.  Data-dependent hypotheses: bounds/align/byte-pins for the
`lw` (at the block-computed `x15`) and the `ld` (at entry `x2`). -/
theorem evalGtBlk2_run (σ : MState) (i u : Nat) (vm v2 v15 : BitVec 64)
    (a0 a1 a2 a3 : BitVec 8)
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003538#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    -- lw @ blk2LwAddr v15 (4-byte)
    (a_lo : 0x80000000 ≤ (blk2LwAddr v15).toNat)
    (a_hi : (blk2LwAddr v15).toNat + 4 ≤ 0x100000000)
    (a_ht : (blk2LwAddr v15).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (blk2LwAddr v15).toNat)
    (a_al : (blk2LwAddr v15).toNat % 4 = 0)
    (a_p0 : σ.mem[(blk2LwAddr v15).toNat]? = some a0)
    (a_p1 : σ.mem[(blk2LwAddr v15).toNat + 1]? = some a1)
    (a_p2 : σ.mem[(blk2LwAddr v15).toNat + 2]? = some a2)
    (a_p3 : σ.mem[(blk2LwAddr v15).toNat + 3]? = some a3)
    -- ld @ v2 + 0 (8-byte)
    (d_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)
    (d_hi : (v2 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (d_ht : (v2 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)
    (d_al : (v2 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (d_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat]? = some d0)
    (d_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some d1)
    (d_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some d2)
    (d_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some d3)
    (d_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some d4)
    (d_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some d5)
    (d_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some d6)
    (d_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some d7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 8⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some (0x80003558#64) := by
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, hframe⟩ :=
    block_mem_sound evalGtBlk2 σ i u (0x80003538#64) vm
      [(15, v15), (2, v2)]
      [[a0, a1, a2, a3], [d0, d1, d2, d3, d4, d5, d6, d7]]
      hG hpc hmi ⟨hx15, hx2, trivial⟩
      (show KeysOK [15, 2] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨a_lo, a_hi, a_ht, a_al⟩, lpin_of_present a_p0, lpin_of_present a_p1, lpin_of_present a_p2, lpin_of_present a_p3⟩
        · exact ⟨⟨d_lo, d_hi, d_ht, d_al⟩, lpin_of_present d_p0, lpin_of_present d_p1, lpin_of_present d_p2, lpin_of_present d_p3, lpin_of_present d_p4, lpin_of_present d_p5, lpin_of_present d_p6, lpin_of_present d_p7⟩)
      (show BlockOKM (0x80003538#64) [15, 2] evalGtBlk2 by decide) hi
  rw [show endPCM (0x80003538#64) evalGtBlk2 = (0x80003558#64 : BitVec 64) from by decide] at hpc'
  exact ⟨σ', i', hsteps, hi', hG', hpc'⟩

/-! ## BlkLdSt — straight-line ld/ld/ld/sd/sd/sd block 0x8000367c … 0x80003690 -/

/-- The ld/ld/ld/sd/sd/sd block, fully concrete via `mkLine` (auto-decode). -/
def evalGtBlkLdSt : List MInstr :=
  [mkLine 0x8000367c#64 0x09013703#32,   -- ld x14, 0x90(x2)
   mkLine 0x80003680#64 0x09813583#32,   -- ld x11, 0x98(x2)
   mkLine 0x80003684#64 0x0a013783#32,   -- ld x15, 0xa0(x2)
   mkLine 0x80003688#64 0x0ee13823#32,   -- sd x14, 0xf0(x2)
   mkLine 0x8000368c#64 0x0eb13c23#32,   -- sd x11, 0xf8(x2)
   mkLine 0x80003690#64 0x10f13023#32]   -- sd x15, 0x100(x2)

/-- The BlkLdSt block via ONE `block_mem_sound`. Three 8-byte loads (byte pins on
`σ.mem`, all off x2), then three 8-byte stores (RAM-bounds / window / alignment,
off x2). -/
theorem evalGtBlkLdSt_run (σ : MState) (i u : Nat) (vm v2 : BitVec 64)
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000367c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    -- load1 @ v2 + 0x090 (8-byte, x14)
    (a_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x090#12)).toNat)
    (a_hi : (v2 + sign_extend (m := 64) (0x090#12)).toNat + 8 ≤ 0x100000000)
    (a_ht : (v2 + sign_extend (m := 64) (0x090#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x090#12)).toNat)
    (a_al : (v2 + sign_extend (m := 64) (0x090#12)).toNat % 8 = 0)
    (a_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat]? = some a0)
    (a_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 1]? = some a1)
    (a_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 2]? = some a2)
    (a_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 3]? = some a3)
    (a_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 4]? = some a4)
    (a_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 5]? = some a5)
    (a_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 6]? = some a6)
    (a_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 7]? = some a7)
    -- load2 @ v2 + 0x098 (8-byte, x11)
    (b_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x098#12)).toNat)
    (b_hi : (v2 + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ 0x100000000)
    (b_ht : (v2 + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x098#12)).toNat)
    (b_al : (v2 + sign_extend (m := 64) (0x098#12)).toNat % 8 = 0)
    (b_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat]? = some b0)
    (b_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 1]? = some b1)
    (b_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 2]? = some b2)
    (b_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 3]? = some b3)
    (b_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 4]? = some b4)
    (b_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 5]? = some b5)
    (b_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 6]? = some b6)
    (b_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 7]? = some b7)
    -- load3 @ v2 + 0x0a0 (8-byte, x15)
    (c_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x0a0#12)).toNat)
    (c_hi : (v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 8 ≤ 0x100000000)
    (c_ht : (v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x0a0#12)).toNat)
    (c_al : (v2 + sign_extend (m := 64) (0x0a0#12)).toNat % 8 = 0)
    (c_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat]? = some c0)
    (c_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 1]? = some c1)
    (c_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 2]? = some c2)
    (c_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 3]? = some c3)
    (c_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 4]? = some c4)
    (c_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 5]? = some c5)
    (c_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 6]? = some c6)
    (c_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 7]? = some c7)
    -- store1 @ v2 + 0x0f0 (8-byte, x14)
    (s0lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x0f0#12)).toNat)
    (s0hi : (v2 + sign_extend (m := 64) (0x0f0#12)).toNat + 8 ≤ 0x100000000)
    (s0win : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x0f0#12)).toNat)
    (s0al : (v2 + sign_extend (m := 64) (0x0f0#12)).toNat % 8 = 0)
    -- store2 @ v2 + 0x0f8 (8-byte, x11)
    (s1lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x0f8#12)).toNat)
    (s1hi : (v2 + sign_extend (m := 64) (0x0f8#12)).toNat + 8 ≤ 0x100000000)
    (s1win : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x0f8#12)).toNat)
    (s1al : (v2 + sign_extend (m := 64) (0x0f8#12)).toNat % 8 = 0)
    -- store3 @ v2 + 0x100 (8-byte, x15)
    (s2lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x100#12)).toNat)
    (s2hi : (v2 + sign_extend (m := 64) (0x100#12)).toNat + 8 ≤ 0x100000000)
    (s2win : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x100#12)).toNat)
    (s2al : (v2 + sign_extend (m := 64) (0x100#12)).toNat % 8 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 6⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some (0x80003694#64) := by
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, hframe⟩ :=
    block_mem_sound evalGtBlkLdSt σ i u (0x8000367c#64) vm
      [(2, v2)]
      [[a0, a1, a2, a3, a4, a5, a6, a7],
       [b0, b1, b2, b3, b4, b5, b6, b7],
       [c0, c1, c2, c3, c4, c5, c6, c7]]
      hG hpc hmi ⟨hx2, trivial⟩
      (show KeysOK [2] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨a_lo, a_hi, a_ht, a_al⟩, lpin_of_present a_p0, lpin_of_present a_p1, lpin_of_present a_p2, lpin_of_present a_p3, lpin_of_present a_p4, lpin_of_present a_p5, lpin_of_present a_p6, lpin_of_present a_p7⟩
        · exact ⟨⟨b_lo, b_hi, b_ht, b_al⟩, lpin_of_present b_p0, lpin_of_present b_p1, lpin_of_present b_p2, lpin_of_present b_p3, lpin_of_present b_p4, lpin_of_present b_p5, lpin_of_present b_p6, lpin_of_present b_p7⟩
        · exact ⟨⟨c_lo, c_hi, c_ht, c_al⟩, lpin_of_present c_p0, lpin_of_present c_p1, lpin_of_present c_p2, lpin_of_present c_p3, lpin_of_present c_p4, lpin_of_present c_p5, lpin_of_present c_p6, lpin_of_present c_p7⟩
        · exact ⟨s0lo, s0hi, s0win, s0al⟩
        · exact ⟨s1lo, s1hi, s1win, s1al⟩
        · exact ⟨s2lo, s2hi, s2win, s2al⟩)
      (show BlockOKM (0x8000367c#64) [2] evalGtBlkLdSt by decide) hi
  rw [show endPCM (0x8000367c#64) evalGtBlkLdSt = (0x80003694#64 : BitVec 64) from by decide]
    at hpc'
  exact ⟨σ', i', hsteps, hi', hG', hpc'⟩

/-! ## BlkCmp — pure-ALU straight-line block 0x80003698 … 0x800036a4 -/

/-- The comparison-tail ALU block, fully concrete via `mkLine` (auto-decode). -/
def evalGtBlkCmp : List MInstr :=
  [mkLine 0x80003698#64 0x0138a733#32,   -- slt  x14,x17,x19
   mkLine 0x8000369c#64 0x0119a7b3#32,   -- slt  x15,x19,x17
   mkLine 0x800036a0#64 0x40f705bb#32,   -- subw x11,x14,x15
   mkLine 0x800036a4#64 0x01500793#32]   -- li   x15,0x15

/-- The comparison-tail ALU block via ONE `block_mem_sound`.  No loads, no stores,
so no data-dependent MemFacts hypotheses at all. -/
theorem evalGtBlkCmp_run (σ : MState) (i u : Nat) (vm v17 v19 : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003698#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hx19 : σ.regs.get? Register.x19 = some v19)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 4⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some (0x800036a8#64) := by
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, hframe⟩ :=
    block_mem_sound evalGtBlkCmp σ i u (0x80003698#64) vm
      [(17, v17), (19, v19)]
      []
      hG hpc hmi ⟨hx17, hx19, trivial⟩
      (show KeysOK [17, 19] by decide)
      (by block_facts hmem with "Vsa.Sim.Code.eval_expr_at_")
      (show BlockOKM (0x80003698#64) [17, 19] evalGtBlkCmp by decide) hi
  rw [show endPCM (0x80003698#64) evalGtBlkCmp = (0x800036a8#64 : BitVec 64) from by decide]
    at hpc'
  exact ⟨σ', i', hsteps, hi', hG', hpc'⟩

end Vsa.Sim
