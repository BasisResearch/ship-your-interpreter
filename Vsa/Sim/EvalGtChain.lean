import Vsa.Sim.EvalGtBlocks
import Vsa.Sim.EvalGtBlk1Pilot
import Vsa.Sim.EvalBinSim4
import Vsa.Sim.BlockTerm
import Vsa.Sim.BlockTactics

/-!
# `EvalGtChain` — chain `evalGtBlk1` + `evalGtBlk2` across two terminators

Re-lands `evalGtChain_run`: EvalGtRow's opening 16-instruction run
`0x8000351c … (bltu@0x3534 not-taken) … (jr@0x3558) → 0x80003628`.

## Why two `bblock_sound_bt`s, not one `bblocks_sound_bt`

A single multi-block `bblocks_sound_bt` phrases block 2's terminator obligations
over `runGM evalGtBlk2 (runGM evalGtBlk1 …) …` — a **nested** 14-instruction
symbolic reduction.  `decide`/`rfl` on that overruns the whnf recursion budget
(and cranking `maxRecDepth` only trades the confusing "free variables" error for a
native stack overflow — the reduction is genuinely too deep).

The compounding fix: apply `bblock_sound_bt` **once per block**, threading block 1's
clean register outputs (`x14 = 12`, `x15 = 11`, `x2 = v2`) into block 2's pin list.
Every guard / jr-target / address reduction is then only 6–8 instructions deep and
completes at the DEFAULT recursion depth — no ceiling needed.

* `gtChainB1` = `evalGtBlk1` (lw/li/lw/addiw/lw/ld) + `bltu a4,a5` NOT taken
  (`x14 = 12`, `x15 = 22 - 11 = 11`, `12 <u 11` false → fall to 0x3538).
* `gtChainB2` = `evalGtBlk2` (slli/srli/auipc/addi/add/lw/ld/add) + `jr a5`
  (slot @0x80019fb0 = `sext[a4 96 fe ff]` + `0x80019f84`; `x15` = 0x80003628).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.  NO `maxRecDepth` override.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

namespace Vsa.Sim

/-- Block 1: `evalGtBlk1` body, then `bltu a4,a5 → 0x3928` NOT taken (fall to 0x3538). -/
def gtChainB1 : BBlock :=
  { body := evalGtBlk1,
    term := some ⟨0x80003534#64, 0x3ef76a63#32, 0x63#8, 0x6a#8, 0xf7#8, 0x3e#8,
      .br bop.BLTU false, 14, 15, 0x03f4#13, 0#21, 0#12⟩ }

/-- Block 2a: `slli/srli/auipc/addi/add` (0x3538→0x354c, fall-through).  Computes
`x15 = 0x80019fb0` (the op-table slot address) and `x14 = 0x80019f84` (base). -/
def gtChainB2a : BBlock :=
  { body :=
      [mkLine 0x80003538#64 0x02079713#32,   -- slli x14,x15,0x20
       mkLine 0x8000353c#64 0x01e75793#32,   -- srli x15,x14,0x1e
       mkLine 0x80003540#64 0x00017717#32,   -- auipc x14,0x17
       mkLine 0x80003544#64 0xa4470713#32,   -- addi  x14,x14,-1468
       mkLine 0x80003548#64 0x00e787b3#32],  -- add   x15,x15,x14
    term := none }

/-- Block 2b: `lw/ld/add` (0x354c→0x3558) + `jr a5`.  The slot `lw` is now
input-relative (`x15 = 0x80019fb0` is B2b's INPUT), so its address is shallow.
Final `x15 = sext[a4 96 fe ff] + 0x80019f84 = 0x80003628` (the jr target). -/
def gtChainB2b : BBlock :=
  { body :=
      [mkLine 0x8000354c#64 0x0007a783#32,   -- lw    x15,0(x15)
       mkLine 0x80003550#64 0x00013803#32,   -- ld    x16,0(x2)
       mkLine 0x80003554#64 0x00e787b3#32],  -- add   x15,x15,x14
    term := some ⟨0x80003558#64, 0x00078067#32, 0x67#8, 0x80#8, 0x07#8, 0x00#8,
      .jr, 15, 0, 0#13, 0#21, 0x000#12⟩ }

/-- The op-token load bytes (`22 = [0x16,0,0,0]`) are concrete so the `bltu`
guard reduces; the three other block-1 loads keep free byte pins. -/
def gtLds1 (b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8) :
    List (List (BitVec 8)) :=
  [[0x16#8, 0x00#8, 0x00#8, 0x00#8], [b0, b1, b2, b3], [c0, c1, c2, c3],
   [d0, d1, d2, d3, d4, d5, d6, d7]]

/-- B2b's load bytes: op-table slot (`[a4 96 fe ff]`, concrete so the `jr` target
reduces to 0x80003628) then the kind-reload (free byte pins). -/
def gtLds2 (k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 8) : List (List (BitVec 8)) :=
  [[0xa4#8, 0x96#8, 0xfe#8, 0xff#8], [k0, k1, k2, k3, k4, k5, k6, k7]]

/-- The opening 16-instruction run of `blockC_gt`, `0x8000351c → 0x80003628`,
via TWO shallow `bblock_sound_bt` applications (block 1 + `bltu`, block 2 + `jr`). -/
theorem evalGtChain_run (σ : MState) (i u : Nat) (vm v2 v8 : BitVec 64)
    (b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8)
    (k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000351c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    -- block1 load1 @ v8 + 0x008 (4-byte, op token = 22 = [0x16,0,0,0])
    (a_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_hi : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (a_ht : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_al : (v8 + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (a_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some (0x16#8))
    (a_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some (0x00#8))
    (a_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some (0x00#8))
    (a_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some (0x00#8))
    -- block1 load2 @ v8 + 0x004 (4-byte)
    (b_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x004#12)).toNat)
    (b_hi : (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ 0x100000000)
    (b_ht : (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x004#12)).toNat)
    (b_al : (v8 + sign_extend (m := 64) (0x004#12)).toNat % 4 = 0)
    (b_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat]? = some b0)
    (b_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 1]? = some b1)
    (b_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 2]? = some b2)
    (b_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 3]? = some b3)
    -- block1 load3 @ v2 + 0x090 (4-byte)
    (c_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x090#12)).toNat)
    (c_hi : (v2 + sign_extend (m := 64) (0x090#12)).toNat + 4 ≤ 0x100000000)
    (c_ht : (v2 + sign_extend (m := 64) (0x090#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x090#12)).toNat)
    (c_al : (v2 + sign_extend (m := 64) (0x090#12)).toNat % 4 = 0)
    (c_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat]? = some c0)
    (c_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 1]? = some c1)
    (c_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 2]? = some c2)
    (c_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 3]? = some c3)
    -- block1 load4 @ v2 + 0x098 (8-byte)
    (d_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x098#12)).toNat)
    (d_hi : (v2 + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ 0x100000000)
    (d_ht : (v2 + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x098#12)).toNat)
    (d_al : (v2 + sign_extend (m := 64) (0x098#12)).toNat % 8 = 0)
    (d_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat]? = some d0)
    (d_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 1]? = some d1)
    (d_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 2]? = some d2)
    (d_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 3]? = some d3)
    (d_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 4]? = some d4)
    (d_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 5]? = some d5)
    (d_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 6]? = some d6)
    (d_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 7]? = some d7)
    -- block2 op-table slot @ opTableBase+44 (the .gt jump-table slot)
    (hSlot : GtSlotPinned σ.mem)
    -- block2 kind-reload @ v2 + 0x000 (8-byte)
    (e_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)
    (e_hi : (v2 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (e_ht : (v2 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)
    (e_al : (v2 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (e_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat]? = some k0)
    (e_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some k1)
    (e_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some k2)
    (e_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some k3)
    (e_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some k4)
    (e_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some k5)
    (e_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some k6)
    (e_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some k7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 16⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some (0x80003628#64) := by
  obtain ⟨sp0, sp1, sp2, sp3⟩ := hSlot
  -- ── Block 1 (evalGtBlk1) + bltu@0x3534 NOT taken → 0x80003538 ──────────────
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt gtChainB1 σ i u (0x8000351c#64) vm
      [(8, v8), (2, v2)] (gtLds1 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
      hG hpc hmi ⟨hx8, hx2, trivial⟩
      (show KeysOK [8, 2] by decide)
      (by
        -- BBlockFacts: block1 four load MemFacts + bltu guard (block_facts handles pins)
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨a_lo, a_hi, a_ht, a_al⟩, a_p0, a_p1, a_p2, a_p3⟩
        · exact ⟨⟨b_lo, b_hi, b_ht, b_al⟩, b_p0, b_p1, b_p2, b_p3⟩
        · exact ⟨⟨c_lo, c_hi, c_ht, c_al⟩, c_p0, c_p1, c_p2, c_p3⟩
        · exact ⟨⟨d_lo, d_hi, d_ht, d_al⟩, d_p0, d_p1, d_p2, d_p3, d_p4, d_p5, d_p6, d_p7⟩
        -- bltu = false.  Compound two SHALLOW reductions: `show` peels the 6-instr
        -- `runGM` wrapper to the clean structural operand forms (li 12 / addiw over
        -- the op-token load), then `decide` evaluates the concrete arithmetic.
        -- (Doing both at once — `show … (12#64) (11#64)` — overruns whnf depth.)
        · show guardB bop.BLTU
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x00c#12))
            (sign_extend (m := 64) (Sail.BitVec.extractLsb
              (bytesVal MKind.lw [0x16#8, 0x00#8, 0x00#8, 0x00#8]
                + sign_extend (m := 64) (0xff5#12)) 31 0)) = false
          decide)
      (show BBlockOK (0x8000351c#64) [8, 2] gtChainB1 by decide) hi
  -- σ1.mem = σ.mem: block1 has no stores, so `writeLog σ.mem [] ≡ σ.mem` (isDefEq).
  have hmem1e : σ1.mem = σ.mem := hmem1
  -- endPCB = tgtPC0 (bltu false) = pc+4 = 0x80003538 (tgtPCT ignores runGM for `br`).
  rw [show endPCB (0x8000351c#64) gtChainB1 [(8, v8), (2, v2)]
        (gtLds1 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
        = (0x80003538#64 : BitVec 64) from by
          show BitVec.addInt (0x80003534#64) 4 = (0x80003538#64 : BitVec 64)
          decide] at hpc1
  -- Clean block-1 register outputs.  x2 is untouched (shallow peel to the input pin).
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 := block_reg hGH1 2
  -- x15 = addiw(op-token, -11) = 11: peel the wrapper to the clean addiw form
  -- (block_reg, shallow), then rewrite that form to 11 (decide, shallow) — never both.
  have hx15v : (sign_extend (m := 64) (Sail.BitVec.extractLsb
      (bytesVal MKind.lw [0x16#8, 0x00#8, 0x00#8, 0x00#8]
        + sign_extend (m := 64) (0xff5#12)) 31 0) : BitVec 64) = 11#64 := by decide
  have hx15_1 : σ1.regs.get? Register.x15 = some (11#64) :=
    hx15v ▸ (block_reg hGH1 15 : σ1.regs.get? Register.x15
      = some (sign_extend (m := 64) (Sail.BitVec.extractLsb
          (bytesVal MKind.lw [0x16#8, 0x00#8, 0x00#8, 0x00#8]
            + sign_extend (m := 64) (0xff5#12)) 31 0)))
  obtain ⟨vm1, hmi1'⟩ := hmi1
  -- ── Block 2a (ALU) → x15=0x80019fb0, x14=0x80019f84 (fall-through to 0x354c) ──
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt gtChainB2a σ1 i1 (u + blenB gtChainB1) (0x80003538#64) vm1
      [(15, (11#64 : BitVec 64))] []
      hG1 hpc1 hmi1' ⟨hx15_1, trivial⟩
      (show KeysOK [15] by decide)
      (by block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
            with "Vsa.Sim.Code.eval_expr_at_")
      (show BBlockOK (0x80003538#64) [15] gtChainB2a by decide) hi1
  have hmem2e : σ2.mem = σ.mem := by rw [hmem2]; exact hmem1e
  -- endPCB (none) = endPCM = 0x8000354c
  rw [show endPCB (0x80003538#64) gtChainB2a [(15, (11#64 : BitVec 64))] []
        = (0x8000354c#64 : BitVec 64) from by
          show endPCM (0x80003538#64) gtChainB2a.body = (0x8000354c#64 : BitVec 64)
          decide] at hpc2
  obtain ⟨vm2, hmi2'⟩ := hmi2
  -- x15 = 0x80019fb0, x14 = 0x80019f84: peel wrapper to the arith form (block_reg,
  -- shallow), then rewrite that form to the literal (decide, shallow) — never both.
  have hx14v : ((((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
      + sign_extend (m := 64) (0xa44#12))) = 0x80019f84#64 := by decide
  have hx14_2 : σ2.regs.get? Register.x14 = some (0x80019f84#64) :=
    hx14v ▸ (block_reg hGH2 14 : σ2.regs.get? Register.x14
      = some (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
          + sign_extend (m := 64) (0xa44#12)))
  have hx15v : (shift_bits_right (shift_bits_left (11#64 : BitVec 64)
        (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
      + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
          + sign_extend (m := 64) (0xa44#12))) = 0x80019fb0#64 := by decide
  have hx15_2 : σ2.regs.get? Register.x15 = some (0x80019fb0#64) :=
    hx15v ▸ (block_reg hGH2 15 : σ2.regs.get? Register.x15
      = some (shift_bits_right (shift_bits_left (11#64 : BitVec 64)
            (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
          + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
              + sign_extend (m := 64) (0xa44#12))))
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 :=
    (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  -- slot pins + kind pins rephrased over σ2.mem (= σ.mem).
  have hSlot2 : σ2.mem[(0x80019fb0#64 : BitVec 64).toNat]? = some (0xa4#8) ∧
      σ2.mem[(0x80019fb0#64 : BitVec 64).toNat + 1]? = some (0x96#8) ∧
      σ2.mem[(0x80019fb0#64 : BitVec 64).toNat + 2]? = some (0xfe#8) ∧
      σ2.mem[(0x80019fb0#64 : BitVec 64).toNat + 3]? = some (0xff#8) := by
    rw [hmem2e]; exact ⟨sp0, sp1, sp2, sp3⟩
  -- Slot-load bounds at the LITERAL address (the block's address `srcVal 15 L + 0`
  -- carries free `v2`, so `decide` must see the literal — isDefEq peels the wrapper).
  have sLo : 0x80000000 ≤ (0x80019fb0#64 : BitVec 64).toNat := by decide
  have sHi : (0x80019fb0#64 : BitVec 64).toNat + 4 ≤ 0x100000000 := by decide
  have sHt : (0x80019fb0#64 : BitVec 64).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (0x80019fb0#64 : BitVec 64).toNat := by decide
  have sAl : (0x80019fb0#64 : BitVec 64).toNat % 4 = 0 := by decide
  have hKind2 : σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat]? = some k0 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some k1 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some k2 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some k3 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some k4 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some k5 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some k6 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some k7 := by
    rw [hmem2e]; exact ⟨e_p0, e_p1, e_p2, e_p3, e_p4, e_p5, e_p6, e_p7⟩
  -- ── Block 2b (lw/ld/add + jr@0x3558) → 0x80003628 ─────────────────────────
  obtain ⟨σ3, i3, hsteps3, hi3, hG3, hmem3, hout3, hpc3, hmi3, hGH3, hframe3⟩ :=
    bblock_sound_bt gtChainB2b σ2 i2 (u + blenB gtChainB1 + blenB gtChainB2a) (0x8000354c#64) vm2
      [(15, (0x80019fb0#64 : BitVec 64)), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
      (gtLds2 k0 k1 k2 k3 k4 k5 k6 k7)
      hG2 hpc2 hmi2' ⟨hx15_2, hx2_2, hx14_2, trivial⟩
      (show KeysOK [15, 2, 14] by decide)
      (by
        block_facts (hmem2e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ2.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        -- slot lw @ 0x80019fb0 (input-relative address, shallow):
        · exact ⟨⟨sLo, sHi, sHt, sAl⟩,
            hSlot2.1, hSlot2.2.1, hSlot2.2.2.1, hSlot2.2.2.2⟩
        -- kind ld @ v2+0:
        · exact ⟨⟨e_lo, e_hi, e_ht, e_al⟩,
            hKind2.1, hKind2.2.1, hKind2.2.2.1, hKind2.2.2.2.1,
            hKind2.2.2.2.2.1, hKind2.2.2.2.2.2.1, hKind2.2.2.2.2.2.2.1, hKind2.2.2.2.2.2.2.2⟩
        -- jr target aligned: peel B2b (3 instrs) to the clean form, then decide.
        · show (BitVec.update ((bytesVal MKind.lw [0xa4#8, 0x96#8, 0xfe#8, 0xff#8]
              + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
          decide)
      (show BBlockOK (0x8000354c#64) [15, 2, 14] gtChainB2b by decide) hi2
  -- endPCB = tgtPCT (jr) = final x15 = 0x80003628 (peel B2b, then decide arith).
  rw [show endPCB (0x8000354c#64) gtChainB2b
        [(15, (0x80019fb0#64 : BitVec 64)), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
        (gtLds2 k0 k1 k2 k3 k4 k5 k6 k7) = (0x80003628#64 : BitVec 64) from by
          show BitVec.update ((bytesVal MKind.lw [0xa4#8, 0x96#8, 0xfe#8, 0xff#8]
              + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1 = (0x80003628#64 : BitVec 64)
          decide] at hpc3
  -- Compose the three runs (7 + 5 + 4 = 16 steps).
  refine ⟨σ3, i3, ?_, hi3, hG3, hpc3⟩
  have hlen : u + blenB gtChainB1 + blenB gtChainB2a + blenB gtChainB2b = u + 16 := by
    rw [show blenB gtChainB1 = 7 from by decide, show blenB gtChainB2a = 5 from by decide,
      show blenB gtChainB2b = 4 from by decide]
  rw [← hlen]
  exact (hsteps1.trans hsteps2).trans hsteps3

/-! ## The branch ladder `0x80003628 → 0x8000364c` (kind-dispatch, first two blocks)

`evalGtChain_run` lands at the shared comparison arm `0x80003628` with the right
operand's kind in `x10 = 2` (int) and the op token in `x12 = 22` (.gt).  The kind
ladder then routes int-vs-int through a taken `bnez` and a not-taken `beq`:

* **LB1** `addi x15,x10,-3` (`x15 = 2 - 3 = -1`), `bnez x15 → 0x3638` TAKEN.
* **LB2** `addiw x15,x12,-20` (`x15 = 22 - 20 = 2`), `li x14,3`, `auipc/addi x13`
  (dead), `beq x15,x14 → 0x3648+…` NOT taken (`2 ≠ 3`), fall to `0x364c`.

Same compounding discipline: one `bblock_sound_bt` per block, guards discharged by
peeling the 1-4-instr wrapper to the clean form then `decide`. -/

def gtLadB1 : BBlock :=
  { body := [mkLine 0x80003628#64 0xffd50793#32],   -- addi x15,x10,-3
    term := some ⟨0x8000362c#64, 0x00079663#32, 0x63#8, 0x96#8, 0x07#8, 0x00#8,
      .br bop.BNE true, 15, 0, 0x000c#13, 0#21, 0#12⟩ }

def gtLadB2 : BBlock :=
  { body := [mkLine 0x80003638#64 0xfec6079b#32,   -- addiw x15,x12,-20
             mkLine 0x8000363c#64 0x00300713#32,   -- addi  x14,x0,3
             mkLine 0x80003640#64 0x00016697#32,   -- auipc x13,0x16 (dead)
             mkLine 0x80003644#64 0xd4068693#32],  -- addi  x13,x13,-704 (dead)
    term := some ⟨0x80003648#64, 0x00e78e63#32, 0x63#8, 0x8e#8, 0xe7#8, 0x00#8,
      .br bop.BEQ false, 15, 14, 0x001c#13, 0#21, 0#12⟩ }

/-- The int-vs-int kind-ladder prefix `0x80003628 → 0x8000364c` (7 steps), from the
comparison-arm entry with `x10 = 2` (kind int) and `x12 = 22` (op .gt). -/
theorem evalGtLadderAB (σ : MState) (i u : Nat) (vm : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003628#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx10 : σ.regs.get? Register.x10 = some (2#64))
    (hx12 : σ.regs.get? Register.x12 = some (22#64))
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 7⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some (0x8000364c#64) ∧
      σ'.regs.get? Register.x12 = some (22#64) ∧
      σ'.regs.get? Register.x15 = some (2#64) ∧
      σ'.regs.get? Register.x14 = some (3#64) := by
  -- ── LB1: addi + bnez TAKEN → 0x80003638 ───────────────────────────────────
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt gtLadB1 σ i u (0x80003628#64) vm
      [(10, (2#64 : BitVec 64))] []
      hG hpc hmi ⟨hx10, trivial⟩
      (show KeysOK [10] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        -- bnez (x10 - 3 = -1) ≠ 0 = true
        · show guardB bop.BNE ((2#64 : BitVec 64) + sign_extend (m := 64) (0xffd#12)) (0#64) = true
          decide)
      (show BBlockOK (0x80003628#64) [10] gtLadB1 by decide) hi
  rw [show endPCB (0x80003628#64) gtLadB1 [(10, (2#64 : BitVec 64))] []
        = (0x80003638#64 : BitVec 64) from by decide] at hpc1
  have hmem1e : σ1.mem = σ.mem := hmem1
  have hx12_1 : σ1.regs.get? Register.x12 = some (22#64) :=
    (hframe1 Register.x12 (by decide) (by decide)).trans hx12
  obtain ⟨vm1, hmi1'⟩ := hmi1
  -- ── LB2: addiw/li/auipc/addi + beq NOT taken → 0x8000364c ──────────────────
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt gtLadB2 σ1 i1 (u + blenB gtLadB1) (0x80003638#64) vm1
      [(12, (22#64 : BitVec 64))] []
      hG1 hpc1 hmi1' ⟨hx12_1, trivial⟩
      (show KeysOK [12] by decide)
      (by
        block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        -- beq (x15 = 22-20 = 2) (x14 = 3) = false
        · show guardB bop.BEQ
            (sign_extend (m := 64) (Sail.BitVec.extractLsb
              ((22#64 : BitVec 64) + sign_extend (m := 64) (0xfec#12)) 31 0))
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x003#12)) = false
          decide)
      (show BBlockOK (0x80003638#64) [12] gtLadB2 by decide) hi1
  rw [show endPCB (0x80003638#64) gtLadB2 [(12, (22#64 : BitVec 64))] []
        = (0x8000364c#64 : BitVec 64) from by decide] at hpc2
  -- outputs
  have hx12_2 : σ2.regs.get? Register.x12 = some (22#64) :=
    (hframe2 Register.x12 (by decide) (by decide)).trans hx12_1
  have hx15v : (sign_extend (m := 64) (Sail.BitVec.extractLsb
      ((22#64 : BitVec 64) + sign_extend (m := 64) (0xfec#12)) 31 0) : BitVec 64) = 2#64 := by decide
  have hx15_2 : σ2.regs.get? Register.x15 = some (2#64) :=
    hx15v ▸ (block_reg hGH2 15 : σ2.regs.get? Register.x15
      = some (sign_extend (m := 64) (Sail.BitVec.extractLsb
          ((22#64 : BitVec 64) + sign_extend (m := 64) (0xfec#12)) 31 0)))
  have hx14v : (((0#64 : BitVec 64) + sign_extend (m := 64) (0x003#12)) : BitVec 64) = 3#64 := by decide
  have hx14_2 : σ2.regs.get? Register.x14 = some (3#64) :=
    hx14v ▸ (block_reg hGH2 14 : σ2.regs.get? Register.x14
      = some ((0#64 : BitVec 64) + sign_extend (m := 64) (0x003#12)))
  refine ⟨σ2, i2, ?_, hi2, hG2, hpc2, hx12_2, hx15_2, hx14_2⟩
  have hlen : u + blenB gtLadB1 + blenB gtLadB2 = u + 7 := by
    rw [show blenB gtLadB1 = 2 from by decide, show blenB gtLadB2 = 5 from by decide]
  rw [← hlen]
  exact hsteps1.trans hsteps2

/-! ## The store block `0x8000364c → 0x8000367c` (LB3: CSWTCH slot compute + dead
loads + two scratch stores + `bne` NOT-taken).

`evalGtLadderAB` lands at `0x364c` with `x15 = 2` (the reloaded kind).  LB3 is the
second jump-table dispatch computing the CSWTCH.25 slot pointer, three dead loads,
and two scratch stores to `sp-848`/`sp-832`, then `bne x16,x11` NOT taken (2≠2 false).

Split into LB3a (pure ALU, computes `x15 = 0x80019ff0`, `x14 = 0x80019fe0`;
fall-through) and LB3b (three `ld`, `li`, two `sd`, `bne`).  The first `ld` reads the
block-computed slot `0x80019ff0`, which is LB3b's INPUT `x15` (input-relative =
shallow).  The memory outcome is exposed existentially as a `writeMap8²` image, so
the assembler bridges downstream (disjoint) loads with `getElem_writeMap8_disjoint`. -/

/-- LB3a: `slli/srli/auipc/addi/add` (0x364c→0x3660, fall-through). -/
def gtLadB3a : BBlock :=
  { body :=
      [mkLine 0x8000364c#64 0x02079713#32,   -- slli x14,x15,0x20
       mkLine 0x80003650#64 0x01d75793#32,   -- srli x15,x14,0x1d
       mkLine 0x80003654#64 0x00017717#32,   -- auipc x14,0x17
       mkLine 0x80003658#64 0x98c70713#32,   -- addi  x14,x14,-1652
       mkLine 0x8000365c#64 0x00f707b3#32],  -- add   x15,x14,x15
    term := none }

/-- LB3b: `ld/ld/ld/addi/sd/sd` (0x3660→0x3674) + `bne x16,x11 → 0x36a0` NOT taken
(fall to 0x367c).  The first `ld` is at the block-input slot `x15 = 0x80019ff0`. -/
def gtLadB3b : BBlock :=
  { body :=
      [mkLine 0x80003660#64 0x0007b683#32,   -- ld   x13,0(x15)
       mkLine 0x80003664#64 0x07813703#32,   -- ld   x14,0x78(x2)
       mkLine 0x80003668#64 0x08813783#32,   -- ld   x15,0x88(x2)
       mkLine 0x8000366c#64 0x00200593#32,   -- addi x11,x0,2
       mkLine 0x80003670#64 0x0ee13823#32,   -- sd   x14,0xf0(x2)
       mkLine 0x80003674#64 0x10f13023#32],  -- sd   x15,0x100(x2)
    term := some ⟨0x80003678#64, 0x02b812e3#32, 0xe3#8, 0x12#8, 0xb8#8, 0x02#8,
      .br bop.BNE false, 16, 11, 0x0824#13, 0#21, 0#12⟩ }

/-- LB3b's load bytes: the slot dead-load (`[s0..s7]`), then the two `v2`-relative
dead loads (`[a0..a7]` @ v2+0x78, `[b0..b7]` @ v2+0x88). -/
def gtLds3 (s0 s1 s2 s3 s4 s5 s6 s7 a0 a1 a2 a3 a4 a5 a6 a7
    b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : List (List (BitVec 8)) :=
  [[s0, s1, s2, s3, s4, s5, s6, s7], [a0, a1, a2, a3, a4, a5, a6, a7],
   [b0, b1, b2, b3, b4, b5, b6, b7]]

/-- LB3 `0x8000364c → 0x8000367c` (12 steps): the CSWTCH-slot dispatch, three dead
loads, two scratch stores, then `bne` NOT taken.  Registers `x10/x12/x16/x17/x9/x19`
pass through untouched; `x2 = v2` is the frame base.  The memory outcome is the two
scratch stores over `σ.mem`, exposed as a `writeMap8²` image. -/
theorem evalGtLadderC (σ : MState) (i u : Nat) (vm v2 : BitVec 64)
    (s0 s1 s2 s3 s4 s5 s6 s7 a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000364c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx15 : σ.regs.get? Register.x15 = some (2#64))
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx16 : σ.regs.get? Register.x16 = some (2#64))
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    -- slot dead-load @ 0x80019ff0 (8-byte)
    (s_p0 : σ.mem[(0x80019ff0#64 : BitVec 64).toNat]? = some s0)
    (s_p1 : σ.mem[(0x80019ff0#64 : BitVec 64).toNat + 1]? = some s1)
    (s_p2 : σ.mem[(0x80019ff0#64 : BitVec 64).toNat + 2]? = some s2)
    (s_p3 : σ.mem[(0x80019ff0#64 : BitVec 64).toNat + 3]? = some s3)
    (s_p4 : σ.mem[(0x80019ff0#64 : BitVec 64).toNat + 4]? = some s4)
    (s_p5 : σ.mem[(0x80019ff0#64 : BitVec 64).toNat + 5]? = some s5)
    (s_p6 : σ.mem[(0x80019ff0#64 : BitVec 64).toNat + 6]? = some s6)
    (s_p7 : σ.mem[(0x80019ff0#64 : BitVec 64).toNat + 7]? = some s7)
    -- dead-load @ v2 + 0x078 (8-byte)
    (a_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x078#12)).toNat)
    (a_hi : (v2 + sign_extend (m := 64) (0x078#12)).toNat + 8 ≤ 0x100000000)
    (a_ht : (v2 + sign_extend (m := 64) (0x078#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x078#12)).toNat)
    (a_al : (v2 + sign_extend (m := 64) (0x078#12)).toNat % 8 = 0)
    (a_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat]? = some a0)
    (a_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 1]? = some a1)
    (a_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 2]? = some a2)
    (a_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 3]? = some a3)
    (a_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 4]? = some a4)
    (a_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 5]? = some a5)
    (a_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 6]? = some a6)
    (a_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 7]? = some a7)
    -- dead-load @ v2 + 0x088 (8-byte)
    (b_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x088#12)).toNat)
    (b_hi : (v2 + sign_extend (m := 64) (0x088#12)).toNat + 8 ≤ 0x100000000)
    (b_ht : (v2 + sign_extend (m := 64) (0x088#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x088#12)).toNat)
    (b_al : (v2 + sign_extend (m := 64) (0x088#12)).toNat % 8 = 0)
    (b_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat]? = some b0)
    (b_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 1]? = some b1)
    (b_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 2]? = some b2)
    (b_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 3]? = some b3)
    (b_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 4]? = some b4)
    (b_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 5]? = some b5)
    (b_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 6]? = some b6)
    (b_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 7]? = some b7)
    -- store @ v2 + 0x0f0 (8-byte) safety
    (t0lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x0f0#12)).toNat)
    (t0hi : (v2 + sign_extend (m := 64) (0x0f0#12)).toNat + 8 ≤ 0x100000000)
    (t0win : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x0f0#12)).toNat)
    (t0al : (v2 + sign_extend (m := 64) (0x0f0#12)).toNat % 8 = 0)
    -- store @ v2 + 0x100 (8-byte) safety
    (t1lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x100#12)).toNat)
    (t1hi : (v2 + sign_extend (m := 64) (0x100#12)).toNat + 8 ≤ 0x100000000)
    (t1win : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x100#12)).toNat)
    (t1al : (v2 + sign_extend (m := 64) (0x100#12)).toNat % 8 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat) (D1 D2 : BitVec (8 * 8)),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 12⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (writeMap8 σ.mem (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D1)
        (v2 + sign_extend (m := 64) (0x100#12)).toNat D2 ∧
      σ'.regs.get? Register.PC = some (0x8000367c#64) ∧
      σ'.regs.get? Register.x2 = some v2 := by
  -- ── LB3a (ALU) → x14 = 0x80019fe0, x15 = 0x80019ff0 (fall-through to 0x3660) ──
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt gtLadB3a σ i u (0x8000364c#64) vm
      [(15, (2#64 : BitVec 64))] []
      hG hpc hmi ⟨hx15, trivial⟩
      (show KeysOK [15] by decide)
      (by block_facts hmem with "Vsa.Sim.Code.eval_expr_at_")
      (show BBlockOK (0x8000364c#64) [15] gtLadB3a by decide) hi
  have hmem1e : σ1.mem = σ.mem := hmem1
  rw [show endPCB (0x8000364c#64) gtLadB3a [(15, (2#64 : BitVec 64))] []
        = (0x80003660#64 : BitVec 64) from by
          show endPCM (0x8000364c#64) gtLadB3a.body = (0x80003660#64 : BitVec 64)
          decide] at hpc1
  obtain ⟨vm1, hmi1'⟩ := hmi1
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 :=
    (hframe1 Register.x2 (by decide) (by decide)).trans hx2
  have hx16_1 : σ1.regs.get? Register.x16 = some (2#64) :=
    (hframe1 Register.x16 (by decide) (by decide)).trans hx16
  -- x14 = 0x80019fe0, x15 = 0x80019ff0: peel wrapper (block_reg) then decide the arith.
  have hx14v : ((((0x80003654#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
      + sign_extend (m := 64) (0x98c#12))) = 0x80019fe0#64 := by decide
  have hx14_1 : σ1.regs.get? Register.x14 = some (0x80019fe0#64) :=
    hx14v ▸ (block_reg hGH1 14 : σ1.regs.get? Register.x14
      = some (((0x80003654#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
          + sign_extend (m := 64) (0x98c#12)))
  have hx15v : ((((0x80003654#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
        + sign_extend (m := 64) (0x98c#12))
      + shift_bits_right (shift_bits_left (2#64 : BitVec 64)
          (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1d#6) 5 0))
      = 0x80019ff0#64 := by decide
  have hx15_1 : σ1.regs.get? Register.x15 = some (0x80019ff0#64) :=
    hx15v ▸ (block_reg hGH1 15 : σ1.regs.get? Register.x15
      = some ((((0x80003654#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
            + sign_extend (m := 64) (0x98c#12))
          + shift_bits_right (shift_bits_left (2#64 : BitVec 64)
              (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1d#6) 5 0)))
  -- slot pins + v2-relative dead-load pins over σ1.mem (= σ.mem).
  have hSlot1 : σ1.mem[(0x80019ff0#64 : BitVec 64).toNat]? = some s0 ∧
      σ1.mem[(0x80019ff0#64 : BitVec 64).toNat + 1]? = some s1 ∧
      σ1.mem[(0x80019ff0#64 : BitVec 64).toNat + 2]? = some s2 ∧
      σ1.mem[(0x80019ff0#64 : BitVec 64).toNat + 3]? = some s3 ∧
      σ1.mem[(0x80019ff0#64 : BitVec 64).toNat + 4]? = some s4 ∧
      σ1.mem[(0x80019ff0#64 : BitVec 64).toNat + 5]? = some s5 ∧
      σ1.mem[(0x80019ff0#64 : BitVec 64).toNat + 6]? = some s6 ∧
      σ1.mem[(0x80019ff0#64 : BitVec 64).toNat + 7]? = some s7 := by
    rw [hmem1e]; exact ⟨s_p0, s_p1, s_p2, s_p3, s_p4, s_p5, s_p6, s_p7⟩
  have hLdA1 : σ1.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat]? = some a0 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 1]? = some a1 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 2]? = some a2 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 3]? = some a3 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 4]? = some a4 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 5]? = some a5 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 6]? = some a6 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 7]? = some a7 := by
    rw [hmem1e]; exact ⟨a_p0, a_p1, a_p2, a_p3, a_p4, a_p5, a_p6, a_p7⟩
  have hLdB1 : σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat]? = some b0 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 1]? = some b1 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 2]? = some b2 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 3]? = some b3 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 4]? = some b4 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 5]? = some b5 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 6]? = some b6 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 7]? = some b7 := by
    rw [hmem1e]; exact ⟨b_p0, b_p1, b_p2, b_p3, b_p4, b_p5, b_p6, b_p7⟩
  have sLo : 0x80000000 ≤ (0x80019ff0#64 : BitVec 64).toNat := by decide
  have sHi : (0x80019ff0#64 : BitVec 64).toNat + 8 ≤ 0x100000000 := by decide
  have sHt : (0x80019ff0#64 : BitVec 64).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (0x80019ff0#64 : BitVec 64).toNat := by decide
  have sAl : (0x80019ff0#64 : BitVec 64).toNat % 8 = 0 := by decide
  -- ── LB3b (loads/li/stores + bne NOT taken) → 0x367c ──────────────────────────
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt gtLadB3b σ1 i1 (u + blenB gtLadB3a) (0x80003660#64) vm1
      [(15, (0x80019ff0#64 : BitVec 64)), (2, v2), (16, (2#64 : BitVec 64))]
      (gtLds3 s0 s1 s2 s3 s4 s5 s6 s7 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7)
      hG1 hpc1 hmi1' ⟨hx15_1, hx2_1, hx16_1, trivial⟩
      (show KeysOK [15, 2, 16] by decide)
      (by
        block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        -- ld x13 @ slot 0x80019ff0 (input-relative, shallow):
        · exact ⟨⟨sLo, sHi, sHt, sAl⟩,
            hSlot1.1, hSlot1.2.1, hSlot1.2.2.1, hSlot1.2.2.2.1,
            hSlot1.2.2.2.2.1, hSlot1.2.2.2.2.2.1, hSlot1.2.2.2.2.2.2.1, hSlot1.2.2.2.2.2.2.2⟩
        -- ld x14 @ v2+0x78:
        · exact ⟨⟨a_lo, a_hi, a_ht, a_al⟩,
            hLdA1.1, hLdA1.2.1, hLdA1.2.2.1, hLdA1.2.2.2.1,
            hLdA1.2.2.2.2.1, hLdA1.2.2.2.2.2.1, hLdA1.2.2.2.2.2.2.1, hLdA1.2.2.2.2.2.2.2⟩
        -- ld x15 @ v2+0x88:
        · exact ⟨⟨b_lo, b_hi, b_ht, b_al⟩,
            hLdB1.1, hLdB1.2.1, hLdB1.2.2.1, hLdB1.2.2.2.1,
            hLdB1.2.2.2.2.1, hLdB1.2.2.2.2.2.1, hLdB1.2.2.2.2.2.2.1, hLdB1.2.2.2.2.2.2.2⟩
        -- sd x14 @ v2+0xf0:
        · exact ⟨t0lo, t0hi, t0win, t0al⟩
        -- sd x15 @ v2+0x100:
        · exact ⟨t1lo, t1hi, t1win, t1al⟩
        -- bne (x16 = 2) (x11 = 2) = false:
        · show guardB bop.BNE (2#64)
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x002#12)) = false
          decide)
      (show BBlockOK (0x80003660#64) [15, 2, 16] gtLadB3b by decide) hi1
  rw [show endPCB (0x80003660#64) gtLadB3b
        [(15, (0x80019ff0#64 : BitVec 64)), (2, v2), (16, (2#64 : BitVec 64))]
        (gtLds3 s0 s1 s2 s3 s4 s5 s6 s7 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7)
        = (0x8000367c#64 : BitVec 64) from by
          show BitVec.addInt (0x80003678#64) 4 = (0x8000367c#64 : BitVec 64)
          decide] at hpc2
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 :=
    (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  -- σ2.mem = writeLog σ.mem (wlogM …) — DEFEQ to the two-store `writeMap8²` image,
  -- so `exact` unifies the existential `D1`/`D2` against the reduction.
  have hmemW : σ2.mem = writeLog σ.mem (wlogM gtLadB3b.body
      [(15, (0x80019ff0#64 : BitVec 64)), (2, v2), (16, (2#64 : BitVec 64))]
      (gtLds3 s0 s1 s2 s3 s4 s5 s6 s7 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7)) :=
    hmem1e ▸ hmem2
  have hSteps : Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + 12⟩ := by
    have hlen : u + blenB gtLadB3a + blenB gtLadB3b = u + 12 := by
      rw [show blenB gtLadB3a = 5 from by decide, show blenB gtLadB3b = 7 from by decide]
    rw [← hlen]; exact hsteps1.trans hsteps2
  exact ⟨σ2, i2, _, _, hSteps, hi2, hG2, hmemW, hpc2, hx2_2⟩

/-! ## LB4 `0x8000367c → 0x80003698` (`evalGtBlkLdSt` body + `bne x10,x16` NOT taken).

Reuses the already-green `evalGtBlkLdSt` straight-line body (three `ld` @ v2+0x90/
0x98/0xa0, three `sd` @ v2+0xf0/0xf8/0x100) as one `bblock_sound_bt` with a `bne`
terminator (`x10 = x16 = 2` → false, fall to 0x3698).  Load pins are supplied over
`σ.mem` (the assembler bridges them past LB3's stores with disjointness); the three
scratch stores overwrite, so the memory outcome is a `writeMap8³` image. -/

def gtLadB4 : BBlock :=
  { body := evalGtBlkLdSt,
    term := some ⟨0x80003694#64, 0x7d051063#32, 0x63#8, 0x10#8, 0x05#8, 0x7d#8,
      .br bop.BNE false, 10, 16, 0x07c0#13, 0#21, 0#12⟩ }

/-- LB4 `0x8000367c → 0x80003698` (7 steps).  `x10/x12/x16/x17/x9/x19` pass through;
`x2 = v2` is the frame base.  Memory outcome = three scratch stores (`writeMap8³`). -/
theorem evalGtLadderD (σ : MState) (i u : Nat) (vm v2 : BitVec 64)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000367c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx10 : σ.regs.get? Register.x10 = some (2#64))
    (hx16 : σ.regs.get? Register.x16 = some (2#64))
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    -- load @ v2 + 0x090 (8-byte, x14)
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
    -- load @ v2 + 0x098 (8-byte, x11)
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
    -- load @ v2 + 0x0a0 (8-byte, x15)
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
    -- store safety @ v2 + 0x0f0 / 0x0f8 / 0x100 (8-byte each)
    (t0lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x0f0#12)).toNat)
    (t0hi : (v2 + sign_extend (m := 64) (0x0f0#12)).toNat + 8 ≤ 0x100000000)
    (t0win : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x0f0#12)).toNat)
    (t0al : (v2 + sign_extend (m := 64) (0x0f0#12)).toNat % 8 = 0)
    (t1lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x0f8#12)).toNat)
    (t1hi : (v2 + sign_extend (m := 64) (0x0f8#12)).toNat + 8 ≤ 0x100000000)
    (t1win : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x0f8#12)).toNat)
    (t1al : (v2 + sign_extend (m := 64) (0x0f8#12)).toNat % 8 = 0)
    (t2lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x100#12)).toNat)
    (t2hi : (v2 + sign_extend (m := 64) (0x100#12)).toNat + 8 ≤ 0x100000000)
    (t2win : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x100#12)).toNat)
    (t2al : (v2 + sign_extend (m := 64) (0x100#12)).toNat % 8 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat) (D1 D2 D3 : BitVec (8 * 8)),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 7⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (writeMap8 (writeMap8 σ.mem
          (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D1)
          (v2 + sign_extend (m := 64) (0x0f8#12)).toNat D2)
          (v2 + sign_extend (m := 64) (0x100#12)).toNat D3 ∧
      σ'.regs.get? Register.PC = some (0x80003698#64) ∧
      σ'.regs.get? Register.x2 = some v2 := by
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt gtLadB4 σ i u (0x8000367c#64) vm
      [(2, v2), (10, (2#64 : BitVec 64)), (16, (2#64 : BitVec 64))]
      [[a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7],
       [c0, c1, c2, c3, c4, c5, c6, c7]]
      hG hpc hmi ⟨hx2, hx10, hx16, trivial⟩
      (show KeysOK [2, 10, 16] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨a_lo, a_hi, a_ht, a_al⟩, a_p0, a_p1, a_p2, a_p3, a_p4, a_p5, a_p6, a_p7⟩
        · exact ⟨⟨b_lo, b_hi, b_ht, b_al⟩, b_p0, b_p1, b_p2, b_p3, b_p4, b_p5, b_p6, b_p7⟩
        · exact ⟨⟨c_lo, c_hi, c_ht, c_al⟩, c_p0, c_p1, c_p2, c_p3, c_p4, c_p5, c_p6, c_p7⟩
        · exact ⟨t0lo, t0hi, t0win, t0al⟩
        · exact ⟨t1lo, t1hi, t1win, t1al⟩
        · exact ⟨t2lo, t2hi, t2win, t2al⟩
        · show guardB bop.BNE (2#64) (2#64) = false
          decide)
      (show BBlockOK (0x8000367c#64) [2, 10, 16] gtLadB4 by decide) hi
  rw [show endPCB (0x8000367c#64) gtLadB4
        [(2, v2), (10, (2#64 : BitVec 64)), (16, (2#64 : BitVec 64))]
        [[a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7],
         [c0, c1, c2, c3, c4, c5, c6, c7]]
        = (0x80003698#64 : BitVec 64) from by
          show BitVec.addInt (0x80003694#64) 4 = (0x80003698#64 : BitVec 64)
          decide] at hpc1
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 :=
    (hframe1 Register.x2 (by decide) (by decide)).trans hx2
  have hmemW : σ1.mem = writeLog σ.mem (wlogM gtLadB4.body
      [(2, v2), (10, (2#64 : BitVec 64)), (16, (2#64 : BitVec 64))]
      [[a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7],
       [c0, c1, c2, c3, c4, c5, c6, c7]]) := hmem1
  exact ⟨σ1, i1, _, _, _, hsteps1, hi1, hG1, hmemW, hpc1, hx2_1⟩

end Vsa.Sim
