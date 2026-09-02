import Vsa.Sim.EvalGtChain

/-!
# `EvalAddChain` — the `.add` opening chain (0x351c → 0x80003888, the ADD-int arm)

The operator-dispatch prologue for `.add` (token 11).  Reuses the comparison
chain block defs `gtChainB1/gtChainB2a/gtChainB2b` + `gtLds2` verbatim — the
instruction WORDS are identical; only the op-token value (11), the kind-ladder
register `x15 = token-11 = 0`, the CSWTCH.18 slot address (`0x80019f84` =
`opTableBase+0` = the table base, since index 0), the slot bytes (`04 99 fe ff` via
`AddSlotPinned`), and the `jr` target (`0x80003888`, the ADD-int arm) differ.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; DEFAULT recDepth.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- Add op-token load bytes (`11 = [0x0b,0,0,0]`), concrete for the `bltu` guard. -/
def addLds1 (b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8) :
    List (List (BitVec 8)) :=
  [[0x0b#8, 0x00#8, 0x00#8, 0x00#8], [b0, b1, b2, b3], [c0, c1, c2, c3],
   [d0, d1, d2, d3, d4, d5, d6, d7]]

/-- B2b's load bytes for `.add`: op-table slot (`[04 99 fe ff]`, concrete so the
`jr` target reduces to 0x80003888) then the kind-reload (free byte pins). -/
def addLds2 (k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 8) : List (List (BitVec 8)) :=
  [[0x04#8, 0x99#8, 0xfe#8, 0xff#8], [k0, k1, k2, k3, k4, k5, k6, k7]]

/-- The opening 16-instruction run of `.add`, `0x8000351c → 0x80003888`,
via TWO shallow `bblock_sound_bt` applications (block 1 + `bltu`, block 2 + `jr`). -/
theorem evalAddChain_run (σ : MState) (i u : Nat) (vm v2 v8 sret Wl : BitVec 64)
    (b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8)
    (k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000351c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    -- the right-operand kind loads (block1 `lw x10`, block2b `ld x16`) hold 2 (int)
    (hc : bytesVal MKind.lw [c0, c1, c2, c3] = (2#64 : BitVec 64))
    (hk : bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7] = (2#64 : BitVec 64))
    -- block1 load1 @ v8 + 0x008 (4-byte, op token = 21 = [0x16,0,0,0])
    (a_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_hi : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (a_ht : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_al : (v8 + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (a_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some (0x0b#8))
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
    -- block2 op-table slot @ opTableBase+40 (the .le jump-table slot)
    (hSlot : AddSlotPinned σ.mem)
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
      σ'.regs.get? Register.PC = some (0x80003888#64) ∧
      σ'.regs.get? Register.x10 = some (2#64) ∧
      σ'.regs.get? Register.x12 = some (11#64) ∧
      σ'.regs.get? Register.x16 = some (2#64) ∧
      σ'.regs.get? Register.x17
        = some (bytesVal MKind.ld [d0, d1, d2, d3, d4, d5, d6, d7]) ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x19 = some Wl ∧
      σ'.mem = σ.mem ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  obtain ⟨sp0, sp1, sp2, sp3⟩ := hSlot
  -- ── Block 1 (evalGtBlk1) + bltu@0x3534 NOT taken → 0x80003538 ──────────────
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt gtChainB1 σ i u (0x8000351c#64) vm
      [(8, v8), (2, v2)] (addLds1 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
      hG hpc hmi ⟨hx8, hx2, trivial⟩
      (show KeysOK [8, 2] by decide)
      (by
        -- BBlockFacts: block1 four load MemFacts + bltu guard (block_facts handles pins)
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨a_lo, a_hi, a_ht, a_al⟩, lpin_of_present a_p0, lpin_of_present a_p1, lpin_of_present a_p2, lpin_of_present a_p3⟩
        · exact ⟨⟨b_lo, b_hi, b_ht, b_al⟩, lpin_of_present b_p0, lpin_of_present b_p1, lpin_of_present b_p2, lpin_of_present b_p3⟩
        · exact ⟨⟨c_lo, c_hi, c_ht, c_al⟩, lpin_of_present c_p0, lpin_of_present c_p1, lpin_of_present c_p2, lpin_of_present c_p3⟩
        · exact ⟨⟨d_lo, d_hi, d_ht, d_al⟩, lpin_of_present d_p0, lpin_of_present d_p1, lpin_of_present d_p2, lpin_of_present d_p3, lpin_of_present d_p4, lpin_of_present d_p5, lpin_of_present d_p6, lpin_of_present d_p7⟩
        -- bltu = false.  Compound two SHALLOW reductions: `show` peels the 6-instr
        -- `runGM` wrapper to the clean structural operand forms (li 12 / addiw over
        -- the op-token load), then `decide` evaluates the concrete arithmetic.
        -- (Doing both at once — `show … (12#64) (0#64)` — overruns whnf depth.)
        · show guardB bop.BLTU
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x00c#12))
            (sign_extend (m := 64) (Sail.BitVec.extractLsb
              (bytesVal MKind.lw [0x0b#8, 0x00#8, 0x00#8, 0x00#8]
                + sign_extend (m := 64) (0xff5#12)) 31 0)) = false
          decide)
      (show BBlockOK (0x8000351c#64) [8, 2] gtChainB1 by decide) hi
  -- σ1.mem = σ.mem: block1 has no stores, so `writeLog σ.mem [] ≡ σ.mem` (isDefEq).
  have hmem1e : σ1.mem = σ.mem := hmem1
  -- endPCB = tgtPC0 (bltu false) = pc+4 = 0x80003538 (tgtPCT ignores runGM for `br`).
  rw [show endPCB (0x8000351c#64) gtChainB1 [(8, v8), (2, v2)]
        (addLds1 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
        = (0x80003538#64 : BitVec 64) from by
          show BitVec.addInt (0x80003534#64) 4 = (0x80003538#64 : BitVec 64)
          decide] at hpc1
  -- Clean block-1 register outputs.  x2 is untouched (shallow peel to the input pin).
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 := block_reg hGH1 2
  -- x15 = addiw(op-token, -11) = 11: peel the wrapper to the clean addiw form
  -- (block_reg, shallow), then rewrite that form to 11 (decide, shallow) — never both.
  have hx15v : (sign_extend (m := 64) (Sail.BitVec.extractLsb
      (bytesVal MKind.lw [0x0b#8, 0x00#8, 0x00#8, 0x00#8]
        + sign_extend (m := 64) (0xff5#12)) 31 0) : BitVec 64) = 0#64 := by decide
  have hx15_1 : σ1.regs.get? Register.x15 = some (0#64) :=
    hx15v ▸ (block_reg hGH1 15 : σ1.regs.get? Register.x15
      = some (sign_extend (m := 64) (Sail.BitVec.extractLsb
          (bytesVal MKind.lw [0x0b#8, 0x00#8, 0x00#8, 0x00#8]
            + sign_extend (m := 64) (0xff5#12)) 31 0)))
  -- block-1 through-registers: op token `x12 = 22`, kind `x10 = 2` (via `hc`),
  -- payload `x17 = bytesVal .ld [d…]`, and the pass-through `x9 = sret` / `x19 = Wl`.
  have hx12v : (bytesVal MKind.lw [0x0b#8, 0x00#8, 0x00#8, 0x00#8] : BitVec 64) = 11#64 := by decide
  have hx12_1 : σ1.regs.get? Register.x12 = some (11#64) :=
    hx12v ▸ (block_reg hGH1 12 : σ1.regs.get? Register.x12
      = some (bytesVal MKind.lw [0x0b#8, 0x00#8, 0x00#8, 0x00#8]))
  have hx10_1 : σ1.regs.get? Register.x10 = some (2#64) :=
    hc ▸ (block_reg hGH1 10 : σ1.regs.get? Register.x10
      = some (bytesVal MKind.lw [c0, c1, c2, c3]))
  have hx17_1 : σ1.regs.get? Register.x17
      = some (bytesVal MKind.ld [d0, d1, d2, d3, d4, d5, d6, d7]) := block_reg hGH1 17
  have hx9_1 : σ1.regs.get? Register.x9 = some sret :=
    (hframe1 Register.x9 (by decide) (by decide)).trans hx9
  have hx19_1 : σ1.regs.get? Register.x19 = some Wl :=
    (hframe1 Register.x19 (by decide) (by decide)).trans hx19
  obtain ⟨vm1, hmi1'⟩ := hmi1
  -- ── Block 2a (ALU) → x15=0x80019f84, x14=0x80019f84 (fall-through to 0x354c) ──
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt gtChainB2a σ1 i1 (u + blenB gtChainB1) (0x80003538#64) vm1
      [(15, (0#64 : BitVec 64))] []
      hG1 hpc1 hmi1' ⟨hx15_1, trivial⟩
      (show KeysOK [15] by decide)
      (by block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
            with "Vsa.Sim.Code.eval_expr_at_")
      (show BBlockOK (0x80003538#64) [15] gtChainB2a by decide) hi1
  have hmem2e : σ2.mem = σ.mem := by rw [hmem2]; exact hmem1e
  -- endPCB (none) = endPCM = 0x8000354c
  rw [show endPCB (0x80003538#64) gtChainB2a [(15, (0#64 : BitVec 64))] []
        = (0x8000354c#64 : BitVec 64) from by
          show endPCM (0x80003538#64) gtChainB2a.body = (0x8000354c#64 : BitVec 64)
          decide] at hpc2
  obtain ⟨vm2, hmi2'⟩ := hmi2
  -- x15 = 0x80019f84, x14 = 0x80019f84: peel wrapper to the arith form (block_reg,
  -- shallow), then rewrite that form to the literal (decide, shallow) — never both.
  have hx14v : ((((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
      + sign_extend (m := 64) (0xa44#12))) = 0x80019f84#64 := by decide
  have hx14_2 : σ2.regs.get? Register.x14 = some (0x80019f84#64) :=
    hx14v ▸ (block_reg hGH2 14 : σ2.regs.get? Register.x14
      = some (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
          + sign_extend (m := 64) (0xa44#12)))
  have hx15v : (shift_bits_right (shift_bits_left (0#64 : BitVec 64)
        (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
      + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
          + sign_extend (m := 64) (0xa44#12))) = 0x80019f84#64 := by decide
  have hx15_2 : σ2.regs.get? Register.x15 = some (0x80019f84#64) :=
    hx15v ▸ (block_reg hGH2 15 : σ2.regs.get? Register.x15
      = some (shift_bits_right (shift_bits_left (0#64 : BitVec 64)
            (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
          + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
              + sign_extend (m := 64) (0xa44#12))))
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 :=
    (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  -- carry the block-1 through-registers past B2a (ALU touches only x14/x15).
  have hx12_2 : σ2.regs.get? Register.x12 = some (11#64) :=
    (hframe2 Register.x12 (by decide) (by decide)).trans hx12_1
  have hx10_2 : σ2.regs.get? Register.x10 = some (2#64) :=
    (hframe2 Register.x10 (by decide) (by decide)).trans hx10_1
  have hx17_2 : σ2.regs.get? Register.x17
      = some (bytesVal MKind.ld [d0, d1, d2, d3, d4, d5, d6, d7]) :=
    (hframe2 Register.x17 (by decide) (by decide)).trans hx17_1
  have hx9_2 : σ2.regs.get? Register.x9 = some sret :=
    (hframe2 Register.x9 (by decide) (by decide)).trans hx9_1
  have hx19_2 : σ2.regs.get? Register.x19 = some Wl :=
    (hframe2 Register.x19 (by decide) (by decide)).trans hx19_1
  -- slot pins + kind pins rephrased over σ2.mem (= σ.mem).
  have hSlot2 : σ2.mem[(0x80019f84#64 : BitVec 64).toNat]? = some (0x04#8) ∧
      σ2.mem[(0x80019f84#64 : BitVec 64).toNat + 1]? = some (0x99#8) ∧
      σ2.mem[(0x80019f84#64 : BitVec 64).toNat + 2]? = some (0xfe#8) ∧
      σ2.mem[(0x80019f84#64 : BitVec 64).toNat + 3]? = some (0xff#8) := by
    rw [hmem2e]; exact ⟨sp0, sp1, sp2, sp3⟩
  -- Slot-load bounds at the LITERAL address (the block's address `srcVal 15 L + 0`
  -- carries free `v2`, so `decide` must see the literal — isDefEq peels the wrapper).
  have sLo : 0x80000000 ≤ (0x80019f84#64 : BitVec 64).toNat := by decide
  have sHi : (0x80019f84#64 : BitVec 64).toNat + 4 ≤ 0x100000000 := by decide
  have sHt : (0x80019f84#64 : BitVec 64).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (0x80019f84#64 : BitVec 64).toNat := by decide
  have sAl : (0x80019f84#64 : BitVec 64).toNat % 4 = 0 := by decide
  have hKind2 : σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat]? = some k0 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some k1 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some k2 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some k3 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some k4 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some k5 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some k6 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some k7 := by
    rw [hmem2e]; exact ⟨e_p0, e_p1, e_p2, e_p3, e_p4, e_p5, e_p6, e_p7⟩
  -- ── Block 2b (lw/ld/add + jr@0x3558) → 0x80003888 ─────────────────────────
  obtain ⟨σ3, i3, hsteps3, hi3, hG3, hmem3, hout3, hpc3, hmi3, hGH3, hframe3⟩ :=
    bblock_sound_bt gtChainB2b σ2 i2 (u + blenB gtChainB1 + blenB gtChainB2a) (0x8000354c#64) vm2
      [(15, (0x80019f84#64 : BitVec 64)), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
      (addLds2 k0 k1 k2 k3 k4 k5 k6 k7)
      hG2 hpc2 hmi2' ⟨hx15_2, hx2_2, hx14_2, trivial⟩
      (show KeysOK [15, 2, 14] by decide)
      (by
        block_facts (hmem2e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ2.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        -- slot lw @ 0x80019f84 (input-relative address, shallow):
        · exact ⟨⟨sLo, sHi, sHt, sAl⟩,
            lpin_of_present hSlot2.1, lpin_of_present hSlot2.2.1, lpin_of_present hSlot2.2.2.1, lpin_of_present hSlot2.2.2.2⟩
        -- kind ld @ v2+0:
        · exact ⟨⟨e_lo, e_hi, e_ht, e_al⟩,
            lpin_of_present hKind2.1, lpin_of_present hKind2.2.1, lpin_of_present hKind2.2.2.1, lpin_of_present hKind2.2.2.2.1,
            lpin_of_present hKind2.2.2.2.2.1, lpin_of_present hKind2.2.2.2.2.2.1, lpin_of_present hKind2.2.2.2.2.2.2.1, lpin_of_present hKind2.2.2.2.2.2.2.2⟩
        -- jr target aligned: peel B2b (3 instrs) to the clean form, then decide.
        · show (BitVec.update ((bytesVal MKind.lw [0x04#8, 0x99#8, 0xfe#8, 0xff#8]
              + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
          decide)
      (show BBlockOK (0x8000354c#64) [15, 2, 14] gtChainB2b by decide) hi2
  -- endPCB = tgtPCT (jr) = final x15 = 0x80003888 (peel B2b, then decide arith).
  rw [show endPCB (0x8000354c#64) gtChainB2b
        [(15, (0x80019f84#64 : BitVec 64)), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
        (addLds2 k0 k1 k2 k3 k4 k5 k6 k7) = (0x80003888#64 : BitVec 64) from by
          show BitVec.update ((bytesVal MKind.lw [0x04#8, 0x99#8, 0xfe#8, 0xff#8]
              + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1 = (0x80003888#64 : BitVec 64)
          decide] at hpc3
  -- carry the through-registers past B2b (touches x15/x16); x16 = kind reload = 2.
  have hx16_3 : σ3.regs.get? Register.x16 = some (2#64) :=
    hk ▸ (block_reg hGH3 16 : σ3.regs.get? Register.x16
      = some (bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7]))
  have hx12_3 : σ3.regs.get? Register.x12 = some (11#64) :=
    (hframe3 Register.x12 (by decide) (by decide)).trans hx12_2
  have hx10_3 : σ3.regs.get? Register.x10 = some (2#64) :=
    (hframe3 Register.x10 (by decide) (by decide)).trans hx10_2
  have hx17_3 : σ3.regs.get? Register.x17
      = some (bytesVal MKind.ld [d0, d1, d2, d3, d4, d5, d6, d7]) :=
    (hframe3 Register.x17 (by decide) (by decide)).trans hx17_2
  have hx2_3 : σ3.regs.get? Register.x2 = some v2 :=
    (hframe3 Register.x2 (by decide) (by decide)).trans hx2_2
  have hx9_3 : σ3.regs.get? Register.x9 = some sret :=
    (hframe3 Register.x9 (by decide) (by decide)).trans hx9_2
  have hx19_3 : σ3.regs.get? Register.x19 = some Wl :=
    (hframe3 Register.x19 (by decide) (by decide)).trans hx19_2
  have hframeC : ∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
      σ3.regs.get? R = σ.regs.get? R := by
    intro R hR he8
    have hab := hR.1
    exact ((hframe3 R (abiNoise_noiseRegs hR) (by block_frame_wr [15, 16, 15])).trans
        (hframe2 R (abiNoise_noiseRegs hR) (by block_frame_wr [14, 15, 14, 14, 15]))).trans
      (hframe1 R (abiNoise_noiseRegs hR) (by block_frame_wr [12, 14, 8, 15, 10, 17]))
  have hmem3e : σ3.mem = σ.mem := by rw [hmem3]; exact hmem2e
  have hout3e : σ3.sailOutput = σ.sailOutput := hout3.trans (hout2.trans hout1)
  -- Compose the three runs (7 + 5 + 4 = 16 steps).
  refine ⟨σ3, i3, ?_, hi3, hG3, hpc3, hx10_3, hx12_3, hx16_3, hx17_3, hx2_3, hx9_3, hx19_3,
    hmem3e, hout3e, hmi3, hframeC⟩
  have hlen : u + blenB gtChainB1 + blenB gtChainB2a + blenB gtChainB2b = u + 16 := by
    rw [show blenB gtChainB1 = 7 from by decide, show blenB gtChainB2a = 5 from by decide,
      show blenB gtChainB2b = 4 from by decide]
  rw [← hlen]
  exact (hsteps1.trans hsteps2).trans hsteps3

/-! ## The `.add` int-arm ladder `0x80003888 → 0x800038d4`.

`evalAddChain_run` lands at `0x80003888` (the ADD-int arm).  The arm is:

* **N1/N2** — the null-kind prefix (`addi a5,{a0,a6},-3` + `beqz` NOT-taken; kind = 2,
  so `2-3 = -1 ≠ 0`).  No stores.
* **S1** `0x80003898 → 0x800038b0` — two dead loads (`ld a4,0x78(sp)`, `ld a5,0x88(sp)`),
  `li a3,2`, two scratch stores (`sd a4,0xf0(sp)`, `sd a5,0x100(sp)`), then `bne a6,a3`
  NOT taken (`2 ≠ 2` false).  Memory = `writeMap8²`.
* **S2** `0x800038b0 → 0x800038cc` — three dead loads (`ld a4,0x90`, `ld a3,0x98`,
  `ld a5,0xa0`), three scratch stores (`sd a4,0xf0`, `sd a3,0xf8`, `sd a5,0x100`), then
  `bne a0,a6` NOT taken.  Its loads @0x90/0x98/0xa0 are DISJOINT from S1's stores
  @0xf0/0x100 (loads below stores), bridged internally with `getElem_writeMap8_disjoint`.
  Memory = `writeMap8³` over S1's image (`writeMap8⁵` overall).
* **Fin** `0x800038cc → 0x800038d4` — `add a1,s3,a7` (`x11 = Wl + Wr`) + `mv a0,s1`
  (`x10 = sret`); `term = none` (the `jal value_int` seam is left to the assembler).

The five scratch stores land at `v2+0xf0/0x100/0xf0/0xf8/0x100` with OPAQUE data
`D1..D5` — the same addresses/nesting as the row's `m1..m5`, so the value_int TAIL's
data-generic mem lemmas drop in after the `sdData_val V*→D*` token swap. -/

/-- N1: `addi a5,a0,-3` + `beqz a5` NOT taken (0x3888→0x3890). -/
def addArmN1 : BBlock :=
  { body := [mkLine 0x80003888#64 0xffd50793#32],   -- addi x15,x10,-3
    term := some ⟨0x8000388c#64, 0x18078a63#32, 0x63#8, 0x8a#8, 0x07#8, 0x18#8,
      .br bop.BEQ false, 15, 0, 0x0194#13, 0#21, 0#12⟩ }

/-- N2: `addi a5,a6,-3` + `beqz a5` NOT taken (0x3890→0x3898). -/
def addArmN2 : BBlock :=
  { body := [mkLine 0x80003890#64 0xffd80793#32],   -- addi x15,x16,-3
    term := some ⟨0x80003894#64, 0x18078663#32, 0x63#8, 0x86#8, 0x07#8, 0x18#8,
      .br bop.BEQ false, 15, 0, 0x018c#13, 0#21, 0#12⟩ }

/-- S1: `ld/ld/li/sd/sd` + `bne a6,a3` NOT taken (0x3898→0x38b0).  First store block. -/
def addArmS1 : BBlock :=
  { body :=
      [mkLine 0x80003898#64 0x07813703#32,   -- ld   x14,0x78(x2)
       mkLine 0x8000389c#64 0x08813783#32,   -- ld   x15,0x88(x2)
       mkLine 0x800038a0#64 0x00200693#32,   -- addi x13,x0,2 (li x13,2)
       mkLine 0x800038a4#64 0x0ee13823#32,   -- sd   x14,0xf0(x2)
       mkLine 0x800038a8#64 0x10f13023#32],  -- sd   x15,0x100(x2)
    term := some ⟨0x800038ac#64, 0x54d81663#32, 0x63#8, 0x16#8, 0xd8#8, 0x54#8,
      .br bop.BNE false, 16, 13, 0x054c#13, 0#21, 0#12⟩ }

/-- S2: `ld/ld/ld/sd/sd/sd` + `bne a0,a6` NOT taken (0x38b0→0x38cc).  Second store block. -/
def addArmS2 : BBlock :=
  { body :=
      [mkLine 0x800038b0#64 0x09013703#32,   -- ld x14,0x90(x2)
       mkLine 0x800038b4#64 0x09813683#32,   -- ld x13,0x98(x2)
       mkLine 0x800038b8#64 0x0a013783#32,   -- ld x15,0xa0(x2)
       mkLine 0x800038bc#64 0x0ee13823#32,   -- sd x14,0xf0(x2)
       mkLine 0x800038c0#64 0x0ed13c23#32,   -- sd x13,0xf8(x2)
       mkLine 0x800038c4#64 0x10f13023#32],  -- sd x15,0x100(x2)
    term := some ⟨0x800038c8#64, 0x45051863#32, 0x63#8, 0x18#8, 0x05#8, 0x45#8,
      .br bop.BNE false, 10, 16, 0x0450#13, 0#21, 0#12⟩ }

/-- Fin: `add a1,s3,a7` + `mv a0,s1` (0x38cc→0x38d4, fall-through; the `jal` seam is
left to the assembler). -/
def addArmFin : BBlock :=
  { body :=
      [mkLine 0x800038cc#64 0x011985b3#32,   -- add  x11,x19,x17
       mkLine 0x800038d0#64 0x00048513#32],  -- addi x10,x9,0 (mv x10,x9)
    term := none }

/-- The `.add` int-arm ladder `0x80003888 → 0x800038d4` (19 steps) via five shallow
`bblock_sound_bt` applications.  `x2/x9/x19` pass through; `x11 = Wl + Wr`,
`x10 = sret`; memory = the five scratch stores (`writeMap8⁵`, opaque `D1..D5`). -/
theorem evalAddArm_run (σ : MState) (i u : Nat) (vm v2 sret Wl Wr : BitVec 64)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7 d0 d1 d2 d3 d4 d5 d6 d7
     e0 e1 e2 e3 e4 e5 e6 e7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003888#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx10 : σ.regs.get? Register.x10 = some (2#64))
    (hx16 : σ.regs.get? Register.x16 = some (2#64))
    (hx17 : σ.regs.get? Register.x17 = some Wr)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    -- v2-relative address normalization (no wrap), for the S2/S1 disjointness bridge
    (hn90 : (v2 + sign_extend (m := 64) (0x090#12)).toNat = v2.toNat + 0x90)
    (hn98 : (v2 + sign_extend (m := 64) (0x098#12)).toNat = v2.toNat + 0x98)
    (hna0 : (v2 + sign_extend (m := 64) (0x0a0#12)).toNat = v2.toNat + 0xa0)
    (hnf0 : (v2 + sign_extend (m := 64) (0x0f0#12)).toNat = v2.toNat + 0xf0)
    (hn100 : (v2 + sign_extend (m := 64) (0x100#12)).toNat = v2.toNat + 0x100)
    -- eval_expr code region [0x80003164,0x80003fe0) disjoint from each store window
    (hcf0 : (v2 + sign_extend (m := 64) (0x0f0#12)).toNat + 8 ≤ 0x80003164
      ∨ 0x80003fe0 ≤ (v2 + sign_extend (m := 64) (0x0f0#12)).toNat)
    (hcf8 : (v2 + sign_extend (m := 64) (0x0f8#12)).toNat + 8 ≤ 0x80003164
      ∨ 0x80003fe0 ≤ (v2 + sign_extend (m := 64) (0x0f8#12)).toNat)
    (hc100 : (v2 + sign_extend (m := 64) (0x100#12)).toNat + 8 ≤ 0x80003164
      ∨ 0x80003fe0 ≤ (v2 + sign_extend (m := 64) (0x100#12)).toNat)
    -- S1 dead load @ v2+0x78 (8-byte)
    (la_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x078#12)).toNat)
    (la_hi : (v2 + sign_extend (m := 64) (0x078#12)).toNat + 8 ≤ 0x100000000)
    (la_ht : (v2 + sign_extend (m := 64) (0x078#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x078#12)).toNat)
    (la_al : (v2 + sign_extend (m := 64) (0x078#12)).toNat % 8 = 0)
    (la_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat]? = some a0)
    (la_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 1]? = some a1)
    (la_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 2]? = some a2)
    (la_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 3]? = some a3)
    (la_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 4]? = some a4)
    (la_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 5]? = some a5)
    (la_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 6]? = some a6)
    (la_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 7]? = some a7)
    -- S1 dead load @ v2+0x88 (8-byte)
    (lb_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x088#12)).toNat)
    (lb_hi : (v2 + sign_extend (m := 64) (0x088#12)).toNat + 8 ≤ 0x100000000)
    (lb_ht : (v2 + sign_extend (m := 64) (0x088#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x088#12)).toNat)
    (lb_al : (v2 + sign_extend (m := 64) (0x088#12)).toNat % 8 = 0)
    (lb_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat]? = some b0)
    (lb_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 1]? = some b1)
    (lb_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 2]? = some b2)
    (lb_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 3]? = some b3)
    (lb_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 4]? = some b4)
    (lb_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 5]? = some b5)
    (lb_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 6]? = some b6)
    (lb_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 7]? = some b7)
    -- S2 dead load @ v2+0x90 (8-byte)
    (lc_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x090#12)).toNat)
    (lc_hi : (v2 + sign_extend (m := 64) (0x090#12)).toNat + 8 ≤ 0x100000000)
    (lc_ht : (v2 + sign_extend (m := 64) (0x090#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x090#12)).toNat)
    (lc_al : (v2 + sign_extend (m := 64) (0x090#12)).toNat % 8 = 0)
    (lc_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat]? = some c0)
    (lc_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 1]? = some c1)
    (lc_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 2]? = some c2)
    (lc_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 3]? = some c3)
    (lc_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 4]? = some c4)
    (lc_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 5]? = some c5)
    (lc_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 6]? = some c6)
    (lc_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 7]? = some c7)
    -- S2 dead load @ v2+0x98 (8-byte)
    (ld_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x098#12)).toNat)
    (ld_hi : (v2 + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ 0x100000000)
    (ld_ht : (v2 + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x098#12)).toNat)
    (ld_al : (v2 + sign_extend (m := 64) (0x098#12)).toNat % 8 = 0)
    (ld_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat]? = some d0)
    (ld_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 1]? = some d1)
    (ld_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 2]? = some d2)
    (ld_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 3]? = some d3)
    (ld_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 4]? = some d4)
    (ld_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 5]? = some d5)
    (ld_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 6]? = some d6)
    (ld_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 7]? = some d7)
    -- S2 dead load @ v2+0xa0 (8-byte)
    (le_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x0a0#12)).toNat)
    (le_hi : (v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 8 ≤ 0x100000000)
    (le_ht : (v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x0a0#12)).toNat)
    (le_al : (v2 + sign_extend (m := 64) (0x0a0#12)).toNat % 8 = 0)
    (le_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat]? = some e0)
    (le_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 1]? = some e1)
    (le_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 2]? = some e2)
    (le_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 3]? = some e3)
    (le_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 4]? = some e4)
    (le_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 5]? = some e5)
    (le_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 6]? = some e6)
    (le_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 7]? = some e7)
    -- store safety @ v2+0xf0 / 0xf8 / 0x100 (8-byte each)
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
    ∃ (σ' : MState) (i' : Nat) (D1 D2 D3 D4 D5 : BitVec (8 * 8)),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 19⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 σ.mem
          (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D1)
          (v2 + sign_extend (m := 64) (0x100#12)).toNat D2)
          (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D3)
          (v2 + sign_extend (m := 64) (0x0f8#12)).toNat D4)
          (v2 + sign_extend (m := 64) (0x100#12)).toNat D5 ∧
      σ'.regs.get? Register.PC = some (0x800038d4#64) ∧
      σ'.regs.get? Register.x11 = some (Wl + Wr) ∧
      σ'.regs.get? Register.x10 = some sret ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x19 = some Wl ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  -- local: push `Eval_exprLoaded` through a code-disjoint `writeMap8`.
  have pushCode : ∀ (m : Mem) (A : Nat) (dd : BitVec (8 * 8)),
      (A + 8 ≤ 0x80003164 ∨ 0x80003fe0 ≤ A) → Vsa.Sim.Code.Eval_exprLoaded m →
      Vsa.Sim.Code.Eval_exprLoaded (writeMap8 m A dd) :=
    fun m A dd hdis hc => loaded_eval_expr_agreeP m (writeMap8 m A dd)
      (fun a _ha => (getElem_writeMap8_disjoint m A a dd (by rcases hdis with h | h <;> omega)).symm) hc
  -- ── N1: addi + beqz NOT taken → 0x80003890 ──────────────────────────────────
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt addArmN1 σ i u (0x80003888#64) vm
      [(10, (2#64 : BitVec 64))] []
      hG hpc hmi ⟨hx10, trivial⟩
      (show KeysOK [10] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · show guardB bop.BEQ ((2#64 : BitVec 64) + sign_extend (m := 64) (0xffd#12)) (0#64) = false
          decide)
      (show BBlockOK (0x80003888#64) [10] addArmN1 by decide) hi
  rw [show endPCB (0x80003888#64) addArmN1 [(10, (2#64 : BitVec 64))] []
        = (0x80003890#64 : BitVec 64) from by
          show BitVec.addInt (0x8000388c#64) 4 = (0x80003890#64 : BitVec 64)
          decide] at hpc1
  have hmem1e : σ1.mem = σ.mem := hmem1
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 := (hframe1 Register.x2 (by decide) (by decide)).trans hx2
  have hx9_1 : σ1.regs.get? Register.x9 = some sret := (hframe1 Register.x9 (by decide) (by decide)).trans hx9
  have hx10_1 : σ1.regs.get? Register.x10 = some (2#64) := (hframe1 Register.x10 (by decide) (by decide)).trans hx10
  have hx16_1 : σ1.regs.get? Register.x16 = some (2#64) := (hframe1 Register.x16 (by decide) (by decide)).trans hx16
  have hx17_1 : σ1.regs.get? Register.x17 = some Wr := (hframe1 Register.x17 (by decide) (by decide)).trans hx17
  have hx19_1 : σ1.regs.get? Register.x19 = some Wl := (hframe1 Register.x19 (by decide) (by decide)).trans hx19
  obtain ⟨vm1, hmi1'⟩ := hmi1
  -- ── N2: addi + beqz NOT taken → 0x80003898 ──────────────────────────────────
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt addArmN2 σ1 i1 (u + blenB addArmN1) (0x80003890#64) vm1
      [(16, (2#64 : BitVec 64))] []
      hG1 hpc1 hmi1' ⟨hx16_1, trivial⟩
      (show KeysOK [16] by decide)
      (by
        block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        · show guardB bop.BEQ ((2#64 : BitVec 64) + sign_extend (m := 64) (0xffd#12)) (0#64) = false
          decide)
      (show BBlockOK (0x80003890#64) [16] addArmN2 by decide) hi1
  rw [show endPCB (0x80003890#64) addArmN2 [(16, (2#64 : BitVec 64))] []
        = (0x80003898#64 : BitVec 64) from by
          show BitVec.addInt (0x80003894#64) 4 = (0x80003898#64 : BitVec 64)
          decide] at hpc2
  have hmem2e : σ2.mem = σ.mem := by rw [hmem2]; exact hmem1e
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 := (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  have hx9_2 : σ2.regs.get? Register.x9 = some sret := (hframe2 Register.x9 (by decide) (by decide)).trans hx9_1
  have hx10_2 : σ2.regs.get? Register.x10 = some (2#64) := (hframe2 Register.x10 (by decide) (by decide)).trans hx10_1
  have hx16_2 : σ2.regs.get? Register.x16 = some (2#64) := (hframe2 Register.x16 (by decide) (by decide)).trans hx16_1
  have hx17_2 : σ2.regs.get? Register.x17 = some Wr := (hframe2 Register.x17 (by decide) (by decide)).trans hx17_1
  have hx19_2 : σ2.regs.get? Register.x19 = some Wl := (hframe2 Register.x19 (by decide) (by decide)).trans hx19_1
  obtain ⟨vm2, hmi2'⟩ := hmi2
  -- S1 dead-load pins over σ2.mem (= σ.mem).
  have hLA2 : σ2.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat]? = some a0 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 1]? = some a1 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 2]? = some a2 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 3]? = some a3 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 4]? = some a4 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 5]? = some a5 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 6]? = some a6 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 7]? = some a7 := by
    rw [hmem2e]; exact ⟨la_p0, la_p1, la_p2, la_p3, la_p4, la_p5, la_p6, la_p7⟩
  have hLB2 : σ2.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat]? = some b0 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 1]? = some b1 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 2]? = some b2 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 3]? = some b3 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 4]? = some b4 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 5]? = some b5 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 6]? = some b6 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 7]? = some b7 := by
    rw [hmem2e]; exact ⟨lb_p0, lb_p1, lb_p2, lb_p3, lb_p4, lb_p5, lb_p6, lb_p7⟩
  -- ── S1: ld/ld/li/sd/sd + bne NOT taken → 0x800038b0 ─────────────────────────
  obtain ⟨σ3, i3, hsteps3, hi3, hG3, hmem3, hout3, hpc3, hmi3, hGH3, hframe3⟩ :=
    bblock_sound_bt addArmS1 σ2 i2 (u + blenB addArmN1 + blenB addArmN2) (0x80003898#64) vm2
      [(2, v2), (16, (2#64 : BitVec 64))]
      [[a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7]]
      hG2 hpc2 hmi2' ⟨hx2_2, hx16_2, trivial⟩
      (show KeysOK [2, 16] by decide)
      (by
        block_facts (hmem2e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ2.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨la_lo, la_hi, la_ht, la_al⟩,
            lpin_of_present hLA2.1, lpin_of_present hLA2.2.1, lpin_of_present hLA2.2.2.1, lpin_of_present hLA2.2.2.2.1,
            lpin_of_present hLA2.2.2.2.2.1, lpin_of_present hLA2.2.2.2.2.2.1, lpin_of_present hLA2.2.2.2.2.2.2.1, lpin_of_present hLA2.2.2.2.2.2.2.2⟩
        · exact ⟨⟨lb_lo, lb_hi, lb_ht, lb_al⟩,
            lpin_of_present hLB2.1, lpin_of_present hLB2.2.1, lpin_of_present hLB2.2.2.1, lpin_of_present hLB2.2.2.2.1,
            lpin_of_present hLB2.2.2.2.2.1, lpin_of_present hLB2.2.2.2.2.2.1, lpin_of_present hLB2.2.2.2.2.2.2.1, lpin_of_present hLB2.2.2.2.2.2.2.2⟩
        · exact ⟨t0lo, t0hi, t0win, t0al⟩
        · exact ⟨t2lo, t2hi, t2win, t2al⟩
        · show guardB bop.BNE (2#64)
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x002#12)) = false
          decide)
      (show BBlockOK (0x80003898#64) [2, 16] addArmS1 by decide) hi2
  rw [show endPCB (0x80003898#64) addArmS1
        [(2, v2), (16, (2#64 : BitVec 64))]
        [[a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7]]
        = (0x800038b0#64 : BitVec 64) from by
          show BitVec.addInt (0x800038ac#64) 4 = (0x800038b0#64 : BitVec 64)
          decide] at hpc3
  have hx2_3 : σ3.regs.get? Register.x2 = some v2 := (hframe3 Register.x2 (by decide) (by decide)).trans hx2_2
  have hx9_3 : σ3.regs.get? Register.x9 = some sret := (hframe3 Register.x9 (by decide) (by decide)).trans hx9_2
  have hx10_3 : σ3.regs.get? Register.x10 = some (2#64) := (hframe3 Register.x10 (by decide) (by decide)).trans hx10_2
  have hx16_3 : σ3.regs.get? Register.x16 = some (2#64) := (hframe3 Register.x16 (by decide) (by decide)).trans hx16_2
  have hx17_3 : σ3.regs.get? Register.x17 = some Wr := (hframe3 Register.x17 (by decide) (by decide)).trans hx17_2
  have hx19_3 : σ3.regs.get? Register.x19 = some Wl := (hframe3 Register.x19 (by decide) (by decide)).trans hx19_2
  obtain ⟨vm3, hmi3'⟩ := hmi3
  -- expose σ3.mem = writeMap8² σ.mem (opaque D1,D2 unify by isDefEq).
  have hmem3W0 : σ3.mem = writeLog σ.mem (wlogM addArmS1.body
      [(2, v2), (16, (2#64 : BitVec 64))]
      [[a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7]]) := hmem2e ▸ hmem3
  obtain ⟨D1, D2, hmem3W⟩ : ∃ D1 D2 : BitVec (8 * 8), σ3.mem
      = writeMap8 (writeMap8 σ.mem (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D1)
          (v2 + sign_extend (m := 64) (0x100#12)).toNat D2 := ⟨_, _, hmem3W0⟩
  have hcode3 : Vsa.Sim.Code.Eval_exprLoaded σ3.mem := by
    rw [hmem3W]; exact pushCode _ _ _ hc100 (pushCode _ _ _ hcf0 hmem)
  -- bridge S2's loads @0x90/0x98/0xa0 over σ3.mem (below the stores @0xf0/0x100).
  have hbridge : ∀ k : Nat, k < (v2 + sign_extend (m := 64) (0x0f0#12)).toNat →
      σ3.mem[k]? = σ.mem[k]? := by
    intro k hk
    rw [hmem3W,
      getElem_writeMap8_disjoint (writeMap8 σ.mem (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D1)
        (v2 + sign_extend (m := 64) (0x100#12)).toNat k D2 (Or.inl (by rw [hnf0] at hk; rw [hn100]; omega)),
      getElem_writeMap8_disjoint σ.mem (v2 + sign_extend (m := 64) (0x0f0#12)).toNat k D1 (Or.inl hk)]
  have hLC3 : σ3.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat]? = some c0 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 1]? = some c1 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 2]? = some c2 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 3]? = some c3 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 4]? = some c4 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 5]? = some c5 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 6]? = some c6 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 7]? = some c7 :=
    ⟨(hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p0,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p1,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p2,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p3,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p4,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p5,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p6,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p7⟩
  have hLD3 : σ3.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat]? = some d0 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 1]? = some d1 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 2]? = some d2 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 3]? = some d3 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 4]? = some d4 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 5]? = some d5 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 6]? = some d6 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 7]? = some d7 :=
    ⟨(hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p0,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p1,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p2,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p3,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p4,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p5,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p6,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p7⟩
  have hLE3 : σ3.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat]? = some e0 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 1]? = some e1 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 2]? = some e2 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 3]? = some e3 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 4]? = some e4 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 5]? = some e5 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 6]? = some e6 ∧
      σ3.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 7]? = some e7 :=
    ⟨(hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p0,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p1,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p2,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p3,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p4,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p5,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p6,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p7⟩
  -- ── S2: ld/ld/ld/sd/sd/sd + bne NOT taken → 0x800038cc ──────────────────────
  obtain ⟨σ4, i4, hsteps4, hi4, hG4, hmem4, hout4, hpc4, hmi4, hGH4, hframe4⟩ :=
    bblock_sound_bt addArmS2 σ3 i3 (u + blenB addArmN1 + blenB addArmN2 + blenB addArmS1) (0x800038b0#64) vm3
      [(2, v2), (10, (2#64 : BitVec 64)), (16, (2#64 : BitVec 64))]
      [[c0, c1, c2, c3, c4, c5, c6, c7], [d0, d1, d2, d3, d4, d5, d6, d7],
       [e0, e1, e2, e3, e4, e5, e6, e7]]
      hG3 hpc3 hmi3' ⟨hx2_3, hx10_3, hx16_3, trivial⟩
      (show KeysOK [2, 10, 16] by decide)
      (by
        block_facts hcode3 with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨lc_lo, lc_hi, lc_ht, lc_al⟩,
            lpin_of_present hLC3.1, lpin_of_present hLC3.2.1, lpin_of_present hLC3.2.2.1, lpin_of_present hLC3.2.2.2.1,
            lpin_of_present hLC3.2.2.2.2.1, lpin_of_present hLC3.2.2.2.2.2.1, lpin_of_present hLC3.2.2.2.2.2.2.1, lpin_of_present hLC3.2.2.2.2.2.2.2⟩
        · exact ⟨⟨ld_lo, ld_hi, ld_ht, ld_al⟩,
            lpin_of_present hLD3.1, lpin_of_present hLD3.2.1, lpin_of_present hLD3.2.2.1, lpin_of_present hLD3.2.2.2.1,
            lpin_of_present hLD3.2.2.2.2.1, lpin_of_present hLD3.2.2.2.2.2.1, lpin_of_present hLD3.2.2.2.2.2.2.1, lpin_of_present hLD3.2.2.2.2.2.2.2⟩
        · exact ⟨⟨le_lo, le_hi, le_ht, le_al⟩,
            lpin_of_present hLE3.1, lpin_of_present hLE3.2.1, lpin_of_present hLE3.2.2.1, lpin_of_present hLE3.2.2.2.1,
            lpin_of_present hLE3.2.2.2.2.1, lpin_of_present hLE3.2.2.2.2.2.1, lpin_of_present hLE3.2.2.2.2.2.2.1, lpin_of_present hLE3.2.2.2.2.2.2.2⟩
        · exact ⟨t0lo, t0hi, t0win, t0al⟩
        · exact ⟨t1lo, t1hi, t1win, t1al⟩
        · exact ⟨t2lo, t2hi, t2win, t2al⟩
        · show guardB bop.BNE (2#64) (2#64) = false
          decide)
      (show BBlockOK (0x800038b0#64) [2, 10, 16] addArmS2 by decide) hi3
  rw [show endPCB (0x800038b0#64) addArmS2
        [(2, v2), (10, (2#64 : BitVec 64)), (16, (2#64 : BitVec 64))]
        [[c0, c1, c2, c3, c4, c5, c6, c7], [d0, d1, d2, d3, d4, d5, d6, d7],
         [e0, e1, e2, e3, e4, e5, e6, e7]]
        = (0x800038cc#64 : BitVec 64) from by
          show BitVec.addInt (0x800038c8#64) 4 = (0x800038cc#64 : BitVec 64)
          decide] at hpc4
  have hx2_4 : σ4.regs.get? Register.x2 = some v2 := (hframe4 Register.x2 (by decide) (by decide)).trans hx2_3
  have hx9_4 : σ4.regs.get? Register.x9 = some sret := (hframe4 Register.x9 (by decide) (by decide)).trans hx9_3
  have hx17_4 : σ4.regs.get? Register.x17 = some Wr := (hframe4 Register.x17 (by decide) (by decide)).trans hx17_3
  have hx19_4 : σ4.regs.get? Register.x19 = some Wl := (hframe4 Register.x19 (by decide) (by decide)).trans hx19_3
  obtain ⟨vm4, hmi4'⟩ := hmi4
  -- expose σ4.mem = writeMap8³ σ3.mem = writeMap8⁵ σ.mem.
  have hmem4W0 : σ4.mem = writeLog σ3.mem (wlogM addArmS2.body
      [(2, v2), (10, (2#64 : BitVec 64)), (16, (2#64 : BitVec 64))]
      [[c0, c1, c2, c3, c4, c5, c6, c7], [d0, d1, d2, d3, d4, d5, d6, d7],
       [e0, e1, e2, e3, e4, e5, e6, e7]]) := hmem4
  obtain ⟨D3, D4, D5, hmem4W⟩ : ∃ D3 D4 D5 : BitVec (8 * 8), σ4.mem
      = writeMap8 (writeMap8 (writeMap8 σ3.mem (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D3)
          (v2 + sign_extend (m := 64) (0x0f8#12)).toNat D4)
          (v2 + sign_extend (m := 64) (0x100#12)).toNat D5 := ⟨_, _, _, hmem4W0⟩
  have hcode4 : Vsa.Sim.Code.Eval_exprLoaded σ4.mem := by
    rw [hmem4W]; exact pushCode _ _ _ hc100 (pushCode _ _ _ hcf8 (pushCode _ _ _ hcf0 hcode3))
  -- ── Fin: add x11 := Wl+Wr, mv x10 := sret (fall-through to 0x800038d4) ───────
  obtain ⟨σ5, i5, hsteps5, hi5, hG5, hmem5, hout5, hpc5, hmi5, hGH5, hframe5⟩ :=
    bblock_sound_bt addArmFin σ4 i4
      (u + blenB addArmN1 + blenB addArmN2 + blenB addArmS1 + blenB addArmS2) (0x800038cc#64) vm4
      [(19, Wl), (17, Wr), (9, sret)] []
      hG4 hpc4 hmi4' ⟨hx19_4, hx17_4, hx9_4, trivial⟩
      (show KeysOK [19, 17, 9] by decide)
      (by block_facts hcode4 with "Vsa.Sim.Code.eval_expr_at_")
      (show BBlockOK (0x800038cc#64) [19, 17, 9] addArmFin by decide) hi4
  rw [show endPCB (0x800038cc#64) addArmFin [(19, Wl), (17, Wr), (9, sret)] []
        = (0x800038d4#64 : BitVec 64) from by
          show endPCM (0x800038cc#64) addArmFin.body = (0x800038d4#64 : BitVec 64)
          decide] at hpc5
  have hmem5e : σ5.mem = σ4.mem := hmem5
  -- x11 = Wl + Wr (add x11,x19,x17), x10 = sret (mv x10,x9).
  have hx11_5 : σ5.regs.get? Register.x11 = some (Wl + Wr) := block_reg hGH5 11
  have hx10v : (sret + sign_extend (m := 64) (0x000#12) : BitVec 64) = sret := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]
    have h0 : (sign_extend (m := 64) (0x000#12) : BitVec 64).toNat = 0 := by decide
    rw [h0]; have := sret.isLt; omega
  have hx10_5 : σ5.regs.get? Register.x10 = some sret :=
    hx10v ▸ (block_reg hGH5 10 : σ5.regs.get? Register.x10
      = some (sret + sign_extend (m := 64) (0x000#12)))
  have hx2_5 : σ5.regs.get? Register.x2 = some v2 := (hframe5 Register.x2 (by decide) (by decide)).trans hx2_4
  have hx9_5 : σ5.regs.get? Register.x9 = some sret := (hframe5 Register.x9 (by decide) (by decide)).trans hx9_4
  have hx19_5 : σ5.regs.get? Register.x19 = some Wl := (hframe5 Register.x19 (by decide) (by decide)).trans hx19_4
  -- combined ABI-noise frame over the five blocks.
  have hframeC : ∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
      σ5.regs.get? R = σ.regs.get? R := by
    intro R hR _he8
    have hab := hR.1
    exact ((((hframe5 R (abiNoise_noiseRegs hR) (by block_frame_wr [11, 10])).trans
        (hframe4 R (abiNoise_noiseRegs hR) (by block_frame_wr [14, 13, 15]))).trans
        (hframe3 R (abiNoise_noiseRegs hR) (by block_frame_wr [14, 15, 13]))).trans
        (hframe2 R (abiNoise_noiseRegs hR) (by block_frame_wr [15]))).trans
      (hframe1 R (abiNoise_noiseRegs hR) (by block_frame_wr [15]))
  -- assemble the memory image writeMap8⁵.
  have hmemW : σ5.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 σ.mem
      (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D1)
      (v2 + sign_extend (m := 64) (0x100#12)).toNat D2)
      (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D3)
      (v2 + sign_extend (m := 64) (0x0f8#12)).toNat D4)
      (v2 + sign_extend (m := 64) (0x100#12)).toNat D5 := by
    rw [hmem5e, hmem4W, hmem3W]
  have hout5e : σ5.sailOutput = σ.sailOutput :=
    hout5.trans (hout4.trans (hout3.trans (hout2.trans hout1)))
  refine ⟨σ5, i5, D1, D2, D3, D4, D5, ?_, hi5, hG5, hmemW, hpc5, hx11_5, hx10_5,
    hx2_5, hx9_5, hx19_5, hout5e, hmi5, hframeC⟩
  have hlen : u + blenB addArmN1 + blenB addArmN2 + blenB addArmS1 + blenB addArmS2
      + blenB addArmFin = u + 19 := by
    rw [show blenB addArmN1 = 2 from by decide, show blenB addArmN2 = 2 from by decide,
      show blenB addArmS1 = 6 from by decide, show blenB addArmS2 = 7 from by decide,
      show blenB addArmFin = 2 from by decide]
  rw [← hlen]
  exact ((((hsteps1.trans hsteps2).trans hsteps3).trans hsteps4).trans hsteps5)

end Vsa.Sim
