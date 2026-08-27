import Vsa.Sim.EvalGtChain

/-!
# `EvalLeChain` — the opening 16-instruction chain of `blockC_le` (0x351c → 0x3628)

Mirror of `evalGtChain_run` for the `.le` operator (token 21, CSWTCH slot
`opTableBase+40` @ 0x80019fac).  Reuses the gt block definitions
(`gtChainB1`/`gtChainB2a`/`gtChainB2b`, `leLds1`/`gtLds2`) verbatim — the
instruction WORDS are identical; only the op-token value (21 vs 22), the
kind-ladder register `x15 = token-11 = 10` (vs 11), and the first jump-table slot
address (0x80019fac vs 0x80019fb0) differ.  The `jr` target is the shared
comparison arm 0x80003628 for both.

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

/-- Le op-token load bytes (`21 = [0x15,0,0,0]`), concrete for the `bltu` guard;
the three other block-1 loads keep free byte pins (cf. `leLds1`). -/
def leLds1 (b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8) :
    List (List (BitVec 8)) :=
  [[0x15#8, 0x00#8, 0x00#8, 0x00#8], [b0, b1, b2, b3], [c0, c1, c2, c3],
   [d0, d1, d2, d3, d4, d5, d6, d7]]

/-- The opening 16-instruction run of `blockC_gt`, `0x8000351c → 0x80003628`,
via TWO shallow `bblock_sound_bt` applications (block 1 + `bltu`, block 2 + `jr`). -/
theorem evalLeChain_run (σ : MState) (i u : Nat) (vm v2 v8 sret Wl : BitVec 64)
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
    (a_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some (0x15#8))
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
    (hSlot : LeSlotPinned σ.mem)
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
      σ'.regs.get? Register.PC = some (0x80003628#64) ∧
      σ'.regs.get? Register.x10 = some (2#64) ∧
      σ'.regs.get? Register.x12 = some (21#64) ∧
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
      [(8, v8), (2, v2)] (leLds1 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
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
        -- (Doing both at once — `show … (12#64) (10#64)` — overruns whnf depth.)
        · show guardB bop.BLTU
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x00c#12))
            (sign_extend (m := 64) (Sail.BitVec.extractLsb
              (bytesVal MKind.lw [0x15#8, 0x00#8, 0x00#8, 0x00#8]
                + sign_extend (m := 64) (0xff5#12)) 31 0)) = false
          decide)
      (show BBlockOK (0x8000351c#64) [8, 2] gtChainB1 by decide) hi
  -- σ1.mem = σ.mem: block1 has no stores, so `writeLog σ.mem [] ≡ σ.mem` (isDefEq).
  have hmem1e : σ1.mem = σ.mem := hmem1
  -- endPCB = tgtPC0 (bltu false) = pc+4 = 0x80003538 (tgtPCT ignores runGM for `br`).
  rw [show endPCB (0x8000351c#64) gtChainB1 [(8, v8), (2, v2)]
        (leLds1 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
        = (0x80003538#64 : BitVec 64) from by
          show BitVec.addInt (0x80003534#64) 4 = (0x80003538#64 : BitVec 64)
          decide] at hpc1
  -- Clean block-1 register outputs.  x2 is untouched (shallow peel to the input pin).
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 := block_reg hGH1 2
  -- x15 = addiw(op-token, -11) = 11: peel the wrapper to the clean addiw form
  -- (block_reg, shallow), then rewrite that form to 11 (decide, shallow) — never both.
  have hx15v : (sign_extend (m := 64) (Sail.BitVec.extractLsb
      (bytesVal MKind.lw [0x15#8, 0x00#8, 0x00#8, 0x00#8]
        + sign_extend (m := 64) (0xff5#12)) 31 0) : BitVec 64) = 10#64 := by decide
  have hx15_1 : σ1.regs.get? Register.x15 = some (10#64) :=
    hx15v ▸ (block_reg hGH1 15 : σ1.regs.get? Register.x15
      = some (sign_extend (m := 64) (Sail.BitVec.extractLsb
          (bytesVal MKind.lw [0x15#8, 0x00#8, 0x00#8, 0x00#8]
            + sign_extend (m := 64) (0xff5#12)) 31 0)))
  -- block-1 through-registers: op token `x12 = 22`, kind `x10 = 2` (via `hc`),
  -- payload `x17 = bytesVal .ld [d…]`, and the pass-through `x9 = sret` / `x19 = Wl`.
  have hx12v : (bytesVal MKind.lw [0x15#8, 0x00#8, 0x00#8, 0x00#8] : BitVec 64) = 21#64 := by decide
  have hx12_1 : σ1.regs.get? Register.x12 = some (21#64) :=
    hx12v ▸ (block_reg hGH1 12 : σ1.regs.get? Register.x12
      = some (bytesVal MKind.lw [0x15#8, 0x00#8, 0x00#8, 0x00#8]))
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
  -- ── Block 2a (ALU) → x15=0x80019fac, x14=0x80019f84 (fall-through to 0x354c) ──
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt gtChainB2a σ1 i1 (u + blenB gtChainB1) (0x80003538#64) vm1
      [(15, (10#64 : BitVec 64))] []
      hG1 hpc1 hmi1' ⟨hx15_1, trivial⟩
      (show KeysOK [15] by decide)
      (by block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
            with "Vsa.Sim.Code.eval_expr_at_")
      (show BBlockOK (0x80003538#64) [15] gtChainB2a by decide) hi1
  have hmem2e : σ2.mem = σ.mem := by rw [hmem2]; exact hmem1e
  -- endPCB (none) = endPCM = 0x8000354c
  rw [show endPCB (0x80003538#64) gtChainB2a [(15, (10#64 : BitVec 64))] []
        = (0x8000354c#64 : BitVec 64) from by
          show endPCM (0x80003538#64) gtChainB2a.body = (0x8000354c#64 : BitVec 64)
          decide] at hpc2
  obtain ⟨vm2, hmi2'⟩ := hmi2
  -- x15 = 0x80019fac, x14 = 0x80019f84: peel wrapper to the arith form (block_reg,
  -- shallow), then rewrite that form to the literal (decide, shallow) — never both.
  have hx14v : ((((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
      + sign_extend (m := 64) (0xa44#12))) = 0x80019f84#64 := by decide
  have hx14_2 : σ2.regs.get? Register.x14 = some (0x80019f84#64) :=
    hx14v ▸ (block_reg hGH2 14 : σ2.regs.get? Register.x14
      = some (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
          + sign_extend (m := 64) (0xa44#12)))
  have hx15v : (shift_bits_right (shift_bits_left (10#64 : BitVec 64)
        (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
      + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
          + sign_extend (m := 64) (0xa44#12))) = 0x80019fac#64 := by decide
  have hx15_2 : σ2.regs.get? Register.x15 = some (0x80019fac#64) :=
    hx15v ▸ (block_reg hGH2 15 : σ2.regs.get? Register.x15
      = some (shift_bits_right (shift_bits_left (10#64 : BitVec 64)
            (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
          + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
              + sign_extend (m := 64) (0xa44#12))))
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 :=
    (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  -- carry the block-1 through-registers past B2a (ALU touches only x14/x15).
  have hx12_2 : σ2.regs.get? Register.x12 = some (21#64) :=
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
  have hSlot2 : σ2.mem[(0x80019fac#64 : BitVec 64).toNat]? = some (0xa4#8) ∧
      σ2.mem[(0x80019fac#64 : BitVec 64).toNat + 1]? = some (0x96#8) ∧
      σ2.mem[(0x80019fac#64 : BitVec 64).toNat + 2]? = some (0xfe#8) ∧
      σ2.mem[(0x80019fac#64 : BitVec 64).toNat + 3]? = some (0xff#8) := by
    rw [hmem2e]; exact ⟨sp0, sp1, sp2, sp3⟩
  -- Slot-load bounds at the LITERAL address (the block's address `srcVal 15 L + 0`
  -- carries free `v2`, so `decide` must see the literal — isDefEq peels the wrapper).
  have sLo : 0x80000000 ≤ (0x80019fac#64 : BitVec 64).toNat := by decide
  have sHi : (0x80019fac#64 : BitVec 64).toNat + 4 ≤ 0x100000000 := by decide
  have sHt : (0x80019fac#64 : BitVec 64).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (0x80019fac#64 : BitVec 64).toNat := by decide
  have sAl : (0x80019fac#64 : BitVec 64).toNat % 4 = 0 := by decide
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
      [(15, (0x80019fac#64 : BitVec 64)), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
      (gtLds2 k0 k1 k2 k3 k4 k5 k6 k7)
      hG2 hpc2 hmi2' ⟨hx15_2, hx2_2, hx14_2, trivial⟩
      (show KeysOK [15, 2, 14] by decide)
      (by
        block_facts (hmem2e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ2.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        -- slot lw @ 0x80019fac (input-relative address, shallow):
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
        [(15, (0x80019fac#64 : BitVec 64)), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
        (gtLds2 k0 k1 k2 k3 k4 k5 k6 k7) = (0x80003628#64 : BitVec 64) from by
          show BitVec.update ((bytesVal MKind.lw [0xa4#8, 0x96#8, 0xfe#8, 0xff#8]
              + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1 = (0x80003628#64 : BitVec 64)
          decide] at hpc3
  -- carry the through-registers past B2b (touches x15/x16); x16 = kind reload = 2.
  have hx16_3 : σ3.regs.get? Register.x16 = some (2#64) :=
    hk ▸ (block_reg hGH3 16 : σ3.regs.get? Register.x16
      = some (bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7]))
  have hx12_3 : σ3.regs.get? Register.x12 = some (21#64) :=
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

/-! ## Le kind-ladder + branch ladder `0x80003628 → 0x80003b00`.

The `.le` counterpart of `evalGtLadder{AB,C,D,EF,G}`.  Reuses the gt block
definitions `gtLadB1..gtLadB4` verbatim (identical instruction words) — only the
op-token value (`x12 = 21` vs 22), the reloaded kind index (`x15 = 1` vs 2), and
the CSWTCH slot address (`0x80019fe8` vs `0x80019ff0`) differ.  The tail DIVERGES:
`le` takes ONE `beq@0x36a8` (21 = 21) into the `slti a1,a1,1` fixup @0x80003af8,
where `gt` fell through to a second `beq@0x36b0` and the `sgtz` fixup. -/

/-- The int-vs-int kind-ladder prefix `0x80003628 → 0x8000364c` (7 steps), from the
comparison-arm entry with `x10 = 2` (kind int) and `x12 = 21` (op .le). -/
theorem evalLeLadderAB (σ : MState) (i u : Nat) (vm v2 sret Wr Wl : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003628#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx10 : σ.regs.get? Register.x10 = some (2#64))
    (hx12 : σ.regs.get? Register.x12 = some (21#64))
    (hx16 : σ.regs.get? Register.x16 = some (2#64))
    (hx17 : σ.regs.get? Register.x17 = some Wr)
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 7⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some (0x8000364c#64) ∧
      σ'.regs.get? Register.x12 = some (21#64) ∧
      σ'.regs.get? Register.x15 = some (1#64) ∧
      σ'.regs.get? Register.x14 = some (3#64) ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x10 = some (2#64) ∧
      σ'.regs.get? Register.x16 = some (2#64) ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x17 = some Wr ∧
      σ'.regs.get? Register.x19 = some Wl ∧
      σ'.mem = σ.mem ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  -- ── LB1: addi + bnez TAKEN → 0x80003638 ───────────────────────────────────
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt gtLadB1 σ i u (0x80003628#64) vm
      [(10, (2#64 : BitVec 64))] []
      hG hpc hmi ⟨hx10, trivial⟩
      (show KeysOK [10] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · show guardB bop.BNE ((2#64 : BitVec 64) + sign_extend (m := 64) (0xffd#12)) (0#64) = true
          decide)
      (show BBlockOK (0x80003628#64) [10] gtLadB1 by decide) hi
  rw [show endPCB (0x80003628#64) gtLadB1 [(10, (2#64 : BitVec 64))] []
        = (0x80003638#64 : BitVec 64) from by decide] at hpc1
  have hmem1e : σ1.mem = σ.mem := hmem1
  have hx12_1 : σ1.regs.get? Register.x12 = some (21#64) :=
    (hframe1 Register.x12 (by decide) (by decide)).trans hx12
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 :=
    (hframe1 Register.x2 (by decide) (by decide)).trans hx2
  have hx10_1 : σ1.regs.get? Register.x10 = some (2#64) :=
    (hframe1 Register.x10 (by decide) (by decide)).trans hx10
  have hx16_1 : σ1.regs.get? Register.x16 = some (2#64) :=
    (hframe1 Register.x16 (by decide) (by decide)).trans hx16
  have hx9_1 : σ1.regs.get? Register.x9 = some sret :=
    (hframe1 Register.x9 (by decide) (by decide)).trans hx9
  have hx17_1 : σ1.regs.get? Register.x17 = some Wr :=
    (hframe1 Register.x17 (by decide) (by decide)).trans hx17
  have hx19_1 : σ1.regs.get? Register.x19 = some Wl :=
    (hframe1 Register.x19 (by decide) (by decide)).trans hx19
  obtain ⟨vm1, hmi1'⟩ := hmi1
  -- ── LB2: addiw/li/auipc/addi + beq NOT taken → 0x8000364c ──────────────────
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt gtLadB2 σ1 i1 (u + blenB gtLadB1) (0x80003638#64) vm1
      [(12, (21#64 : BitVec 64))] []
      hG1 hpc1 hmi1' ⟨hx12_1, trivial⟩
      (show KeysOK [12] by decide)
      (by
        block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        -- beq (x15 = 21-20 = 1) (x14 = 3) = false
        · show guardB bop.BEQ
            (sign_extend (m := 64) (Sail.BitVec.extractLsb
              ((21#64 : BitVec 64) + sign_extend (m := 64) (0xfec#12)) 31 0))
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x003#12)) = false
          decide)
      (show BBlockOK (0x80003638#64) [12] gtLadB2 by decide) hi1
  rw [show endPCB (0x80003638#64) gtLadB2 [(12, (21#64 : BitVec 64))] []
        = (0x8000364c#64 : BitVec 64) from by decide] at hpc2
  have hx12_2 : σ2.regs.get? Register.x12 = some (21#64) :=
    (hframe2 Register.x12 (by decide) (by decide)).trans hx12_1
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 :=
    (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  have hx10_2 : σ2.regs.get? Register.x10 = some (2#64) :=
    (hframe2 Register.x10 (by decide) (by decide)).trans hx10_1
  have hx16_2 : σ2.regs.get? Register.x16 = some (2#64) :=
    (hframe2 Register.x16 (by decide) (by decide)).trans hx16_1
  have hx9_2 : σ2.regs.get? Register.x9 = some sret :=
    (hframe2 Register.x9 (by decide) (by decide)).trans hx9_1
  have hx17_2 : σ2.regs.get? Register.x17 = some Wr :=
    (hframe2 Register.x17 (by decide) (by decide)).trans hx17_1
  have hx19_2 : σ2.regs.get? Register.x19 = some Wl :=
    (hframe2 Register.x19 (by decide) (by decide)).trans hx19_1
  have hframeC : ∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
      σ2.regs.get? R = σ.regs.get? R := by
    intro R hR _he8
    have hab := hR.1
    exact (hframe2 R (abiNoise_noiseRegs hR) (by block_frame_wr [15, 14, 13, 13])).trans
      (hframe1 R (abiNoise_noiseRegs hR) (by block_frame_wr [15]))
  have hx15v : (sign_extend (m := 64) (Sail.BitVec.extractLsb
      ((21#64 : BitVec 64) + sign_extend (m := 64) (0xfec#12)) 31 0) : BitVec 64) = 1#64 := by decide
  have hx15_2 : σ2.regs.get? Register.x15 = some (1#64) :=
    hx15v ▸ (block_reg hGH2 15 : σ2.regs.get? Register.x15
      = some (sign_extend (m := 64) (Sail.BitVec.extractLsb
          ((21#64 : BitVec 64) + sign_extend (m := 64) (0xfec#12)) 31 0)))
  have hx14v : (((0#64 : BitVec 64) + sign_extend (m := 64) (0x003#12)) : BitVec 64) = 3#64 := by decide
  have hx14_2 : σ2.regs.get? Register.x14 = some (3#64) :=
    hx14v ▸ (block_reg hGH2 14 : σ2.regs.get? Register.x14
      = some ((0#64 : BitVec 64) + sign_extend (m := 64) (0x003#12)))
  have hmem2e : σ2.mem = σ.mem := by rw [hmem2]; exact hmem1e
  have hout2e : σ2.sailOutput = σ.sailOutput := hout2.trans hout1
  refine ⟨σ2, i2, ?_, hi2, hG2, hpc2, hx12_2, hx15_2, hx14_2,
    hx2_2, hx10_2, hx16_2, hx9_2, hx17_2, hx19_2, hmem2e, hout2e, hmi2, hframeC⟩
  have hlen : u + blenB gtLadB1 + blenB gtLadB2 = u + 7 := by
    rw [show blenB gtLadB1 = 2 from by decide, show blenB gtLadB2 = 5 from by decide]
  rw [← hlen]
  exact hsteps1.trans hsteps2

/-- LE `LB3` `0x8000364c → 0x8000367c` (12 steps): the CSWTCH-slot dispatch reads
INDEX `1<<3 = 8` (slot `0x80019fe8`, vs gt's `0x80019ff0`) because `x15 = 1` here.
Three dead loads, two scratch stores, then `bne` NOT taken.  `x10/x12/x16/x17/x9/x19`
pass through; `x2 = v2` is the frame base.  Memory outcome = two scratch stores
(`writeMap8²`). -/
theorem evalLeLadderC (σ : MState) (i u : Nat) (vm v2 sret Wr Wl : BitVec 64)
    (s0 s1 s2 s3 s4 s5 s6 s7 a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000364c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx15 : σ.regs.get? Register.x15 = some (1#64))
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx16 : σ.regs.get? Register.x16 = some (2#64))
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx10 : σ.regs.get? Register.x10 = some (2#64))
    (hx12 : σ.regs.get? Register.x12 = some (21#64))
    (hx17 : σ.regs.get? Register.x17 = some Wr)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    -- slot dead-load @ 0x80019fe8 (8-byte)
    (s_p0 : σ.mem[(0x80019fe8#64 : BitVec 64).toNat]? = some s0)
    (s_p1 : σ.mem[(0x80019fe8#64 : BitVec 64).toNat + 1]? = some s1)
    (s_p2 : σ.mem[(0x80019fe8#64 : BitVec 64).toNat + 2]? = some s2)
    (s_p3 : σ.mem[(0x80019fe8#64 : BitVec 64).toNat + 3]? = some s3)
    (s_p4 : σ.mem[(0x80019fe8#64 : BitVec 64).toNat + 4]? = some s4)
    (s_p5 : σ.mem[(0x80019fe8#64 : BitVec 64).toNat + 5]? = some s5)
    (s_p6 : σ.mem[(0x80019fe8#64 : BitVec 64).toNat + 6]? = some s6)
    (s_p7 : σ.mem[(0x80019fe8#64 : BitVec 64).toNat + 7]? = some s7)
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
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x10 = some (2#64) ∧
      σ'.regs.get? Register.x12 = some (21#64) ∧
      σ'.regs.get? Register.x16 = some (2#64) ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x17 = some Wr ∧
      σ'.regs.get? Register.x19 = some Wl ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  -- ── LB3a (ALU) → x14 = 0x80019fe0, x15 = 0x80019fe8 (fall-through to 0x3660) ──
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt gtLadB3a σ i u (0x8000364c#64) vm
      [(15, (1#64 : BitVec 64))] []
      hG hpc hmi ⟨hx15, trivial⟩
      (show KeysOK [15] by decide)
      (by block_facts hmem with "Vsa.Sim.Code.eval_expr_at_")
      (show BBlockOK (0x8000364c#64) [15] gtLadB3a by decide) hi
  have hmem1e : σ1.mem = σ.mem := hmem1
  rw [show endPCB (0x8000364c#64) gtLadB3a [(15, (1#64 : BitVec 64))] []
        = (0x80003660#64 : BitVec 64) from by
          show endPCM (0x8000364c#64) gtLadB3a.body = (0x80003660#64 : BitVec 64)
          decide] at hpc1
  obtain ⟨vm1, hmi1'⟩ := hmi1
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 :=
    (hframe1 Register.x2 (by decide) (by decide)).trans hx2
  have hx16_1 : σ1.regs.get? Register.x16 = some (2#64) :=
    (hframe1 Register.x16 (by decide) (by decide)).trans hx16
  have hx10_1 : σ1.regs.get? Register.x10 = some (2#64) :=
    (hframe1 Register.x10 (by decide) (by decide)).trans hx10
  have hx12_1 : σ1.regs.get? Register.x12 = some (21#64) :=
    (hframe1 Register.x12 (by decide) (by decide)).trans hx12
  have hx9_1 : σ1.regs.get? Register.x9 = some sret :=
    (hframe1 Register.x9 (by decide) (by decide)).trans hx9
  have hx17_1 : σ1.regs.get? Register.x17 = some Wr :=
    (hframe1 Register.x17 (by decide) (by decide)).trans hx17
  have hx19_1 : σ1.regs.get? Register.x19 = some Wl :=
    (hframe1 Register.x19 (by decide) (by decide)).trans hx19
  -- x14 = 0x80019fe0 (CSWTCH base), x15 = base + (1<<3) = 0x80019fe8.
  have hx14v : ((((0x80003654#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
      + sign_extend (m := 64) (0x98c#12))) = 0x80019fe0#64 := by decide
  have hx14_1 : σ1.regs.get? Register.x14 = some (0x80019fe0#64) :=
    hx14v ▸ (block_reg hGH1 14 : σ1.regs.get? Register.x14
      = some (((0x80003654#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
          + sign_extend (m := 64) (0x98c#12)))
  have hx15v : ((((0x80003654#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
        + sign_extend (m := 64) (0x98c#12))
      + shift_bits_right (shift_bits_left (1#64 : BitVec 64)
          (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1d#6) 5 0))
      = 0x80019fe8#64 := by decide
  have hx15_1 : σ1.regs.get? Register.x15 = some (0x80019fe8#64) :=
    hx15v ▸ (block_reg hGH1 15 : σ1.regs.get? Register.x15
      = some ((((0x80003654#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
            + sign_extend (m := 64) (0x98c#12))
          + shift_bits_right (shift_bits_left (1#64 : BitVec 64)
              (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1d#6) 5 0)))
  have hSlot1 : σ1.mem[(0x80019fe8#64 : BitVec 64).toNat]? = some s0 ∧
      σ1.mem[(0x80019fe8#64 : BitVec 64).toNat + 1]? = some s1 ∧
      σ1.mem[(0x80019fe8#64 : BitVec 64).toNat + 2]? = some s2 ∧
      σ1.mem[(0x80019fe8#64 : BitVec 64).toNat + 3]? = some s3 ∧
      σ1.mem[(0x80019fe8#64 : BitVec 64).toNat + 4]? = some s4 ∧
      σ1.mem[(0x80019fe8#64 : BitVec 64).toNat + 5]? = some s5 ∧
      σ1.mem[(0x80019fe8#64 : BitVec 64).toNat + 6]? = some s6 ∧
      σ1.mem[(0x80019fe8#64 : BitVec 64).toNat + 7]? = some s7 := by
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
  have sLo : 0x80000000 ≤ (0x80019fe8#64 : BitVec 64).toNat := by decide
  have sHi : (0x80019fe8#64 : BitVec 64).toNat + 8 ≤ 0x100000000 := by decide
  have sHt : (0x80019fe8#64 : BitVec 64).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (0x80019fe8#64 : BitVec 64).toNat := by decide
  have sAl : (0x80019fe8#64 : BitVec 64).toNat % 8 = 0 := by decide
  -- ── LB3b (loads/li/stores + bne NOT taken) → 0x367c ──────────────────────────
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt gtLadB3b σ1 i1 (u + blenB gtLadB3a) (0x80003660#64) vm1
      [(15, (0x80019fe8#64 : BitVec 64)), (2, v2), (16, (2#64 : BitVec 64))]
      (gtLds3 s0 s1 s2 s3 s4 s5 s6 s7 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7)
      hG1 hpc1 hmi1' ⟨hx15_1, hx2_1, hx16_1, trivial⟩
      (show KeysOK [15, 2, 16] by decide)
      (by
        block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨sLo, sHi, sHt, sAl⟩,
            hSlot1.1, hSlot1.2.1, hSlot1.2.2.1, hSlot1.2.2.2.1,
            hSlot1.2.2.2.2.1, hSlot1.2.2.2.2.2.1, hSlot1.2.2.2.2.2.2.1, hSlot1.2.2.2.2.2.2.2⟩
        · exact ⟨⟨a_lo, a_hi, a_ht, a_al⟩,
            hLdA1.1, hLdA1.2.1, hLdA1.2.2.1, hLdA1.2.2.2.1,
            hLdA1.2.2.2.2.1, hLdA1.2.2.2.2.2.1, hLdA1.2.2.2.2.2.2.1, hLdA1.2.2.2.2.2.2.2⟩
        · exact ⟨⟨b_lo, b_hi, b_ht, b_al⟩,
            hLdB1.1, hLdB1.2.1, hLdB1.2.2.1, hLdB1.2.2.2.1,
            hLdB1.2.2.2.2.1, hLdB1.2.2.2.2.2.1, hLdB1.2.2.2.2.2.2.1, hLdB1.2.2.2.2.2.2.2⟩
        · exact ⟨t0lo, t0hi, t0win, t0al⟩
        · exact ⟨t1lo, t1hi, t1win, t1al⟩
        · show guardB bop.BNE (2#64)
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x002#12)) = false
          decide)
      (show BBlockOK (0x80003660#64) [15, 2, 16] gtLadB3b by decide) hi1
  rw [show endPCB (0x80003660#64) gtLadB3b
        [(15, (0x80019fe8#64 : BitVec 64)), (2, v2), (16, (2#64 : BitVec 64))]
        (gtLds3 s0 s1 s2 s3 s4 s5 s6 s7 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7)
        = (0x8000367c#64 : BitVec 64) from by
          show BitVec.addInt (0x80003678#64) 4 = (0x8000367c#64 : BitVec 64)
          decide] at hpc2
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 :=
    (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  have hx10_2 : σ2.regs.get? Register.x10 = some (2#64) :=
    (hframe2 Register.x10 (by decide) (by decide)).trans hx10_1
  have hx12_2 : σ2.regs.get? Register.x12 = some (21#64) :=
    (hframe2 Register.x12 (by decide) (by decide)).trans hx12_1
  have hx16_2 : σ2.regs.get? Register.x16 = some (2#64) :=
    (hframe2 Register.x16 (by decide) (by decide)).trans hx16_1
  have hx9_2 : σ2.regs.get? Register.x9 = some sret :=
    (hframe2 Register.x9 (by decide) (by decide)).trans hx9_1
  have hx17_2 : σ2.regs.get? Register.x17 = some Wr :=
    (hframe2 Register.x17 (by decide) (by decide)).trans hx17_1
  have hx19_2 : σ2.regs.get? Register.x19 = some Wl :=
    (hframe2 Register.x19 (by decide) (by decide)).trans hx19_1
  have hframeC : ∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
      σ2.regs.get? R = σ.regs.get? R := by
    intro R hR _he8
    have hab := hR.1
    exact (hframe2 R (abiNoise_noiseRegs hR) (by block_frame_wr [13, 14, 15, 11])).trans
      (hframe1 R (abiNoise_noiseRegs hR) (by block_frame_wr [14, 15, 14, 14, 15]))
  have hmemW : σ2.mem = writeLog σ.mem (wlogM gtLadB3b.body
      [(15, (0x80019fe8#64 : BitVec 64)), (2, v2), (16, (2#64 : BitVec 64))]
      (gtLds3 s0 s1 s2 s3 s4 s5 s6 s7 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7)) :=
    hmem1e ▸ hmem2
  have hSteps : Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + 12⟩ := by
    have hlen : u + blenB gtLadB3a + blenB gtLadB3b = u + 12 := by
      rw [show blenB gtLadB3a = 5 from by decide, show blenB gtLadB3b = 7 from by decide]
    rw [← hlen]; exact hsteps1.trans hsteps2
  have hout2e : σ2.sailOutput = σ.sailOutput := hout2.trans hout1
  exact ⟨σ2, i2, _, _, hSteps, hi2, hG2, hmemW, hpc2, hx2_2,
    hx10_2, hx12_2, hx16_2, hx9_2, hx17_2, hx19_2, hout2e, hmi2, hframeC⟩

/-- LE `LB4` `0x8000367c → 0x80003698` (7 steps).  Identical to `evalGtLadderD`
except the op token `x12 = 21`.  Memory outcome = three scratch stores (`writeMap8³`). -/
theorem evalLeLadderD (σ : MState) (i u : Nat) (vm v2 sret Wr Wl : BitVec 64)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000367c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx10 : σ.regs.get? Register.x10 = some (2#64))
    (hx16 : σ.regs.get? Register.x16 = some (2#64))
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx12 : σ.regs.get? Register.x12 = some (21#64))
    (hx17 : σ.regs.get? Register.x17 = some Wr)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
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
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x12 = some (21#64) ∧
      σ'.regs.get? Register.x17 = some Wr ∧
      σ'.regs.get? Register.x19 = some Wl ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
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
  have hx9_1 : σ1.regs.get? Register.x9 = some sret :=
    (hframe1 Register.x9 (by decide) (by decide)).trans hx9
  have hx12_1 : σ1.regs.get? Register.x12 = some (21#64) :=
    (hframe1 Register.x12 (by decide) (by decide)).trans hx12
  have hx17_1 : σ1.regs.get? Register.x17 = some Wr :=
    (hframe1 Register.x17 (by decide) (by decide)).trans hx17
  have hx19_1 : σ1.regs.get? Register.x19 = some Wl :=
    (hframe1 Register.x19 (by decide) (by decide)).trans hx19
  have hframeC : ∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
      σ1.regs.get? R = σ.regs.get? R := by
    intro R hR _he8
    have hab := hR.1
    exact hframe1 R (abiNoise_noiseRegs hR) (by block_frame_wr [14, 11, 15])
  have hmemW : σ1.mem = writeLog σ.mem (wlogM gtLadB4.body
      [(2, v2), (10, (2#64 : BitVec 64)), (16, (2#64 : BitVec 64))]
      [[a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7],
       [c0, c1, c2, c3, c4, c5, c6, c7]]) := hmem1
  exact ⟨σ1, i1, _, _, _, hsteps1, hi1, hG1, hmemW, hpc1, hx2_1,
    hx9_1, hx12_1, hx17_1, hx19_1, hout1, hmi1, hframeC⟩

/-- LE `LB5` `0x80003698 → 0x80003af8` (5 steps): `evalGtBlkCmp` body (`slt/slt/subw/li`
`x11 = cmpScalar Wl Wr`, `x15 = 21`) + `beq x12,x15` TAKEN (21 = 21) → the `slti`
le-fixup @0x80003af8.  This is the divergence from `gt` (which fell through here). -/
def leLadB5 : BBlock :=
  { body := evalGtBlkCmp,
    term := some ⟨0x800036a8#64, 0x44f60863#32, 0x63#8, 0x08#8, 0xf6#8, 0x44#8,
      .br bop.BEQ true, 12, 15, 0x0450#13, 0#21, 0#12⟩ }

theorem evalLeLadderEF (σ : MState) (i u : Nat) (vm Wr Wl sret v2 : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003698#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx17 : σ.regs.get? Register.x17 = some Wr)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hx12 : σ.regs.get? Register.x12 = some (21#64))
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 5⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      σ'.regs.get? Register.PC = some (0x80003af8#64) ∧
      σ'.regs.get? Register.x11 = some (cmpScalar Wl Wr) ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x19 = some Wl ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt leLadB5 σ i u (0x80003698#64) vm
      [(17, Wr), (19, Wl), (12, (21#64 : BitVec 64))] []
      hG hpc hmi ⟨hx17, hx19, hx12, trivial⟩
      (show KeysOK [17, 19, 12] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        -- beq (x12 = 21) (x15 = 21) = true:
        · show guardB bop.BEQ (21#64)
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x015#12)) = true
          decide)
      (show BBlockOK (0x80003698#64) [17, 19, 12] leLadB5 by decide) hi
  have hmem1e : σ1.mem = σ.mem := hmem1
  rw [show endPCB (0x80003698#64) leLadB5
        [(17, Wr), (19, Wl), (12, (21#64 : BitVec 64))] []
        = (0x80003af8#64 : BitVec 64) from by
          show (0x800036a8#64 : BitVec 64) + sign_extend (m := 64) (0x0450#13)
            = (0x80003af8#64 : BitVec 64)
          decide] at hpc1
  have hx11_1 : σ1.regs.get? Register.x11 = some (cmpScalar Wl Wr) := block_reg hGH1 11
  have hx9_1 : σ1.regs.get? Register.x9 = some sret :=
    (hframe1 Register.x9 (by decide) (by decide)).trans hx9
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 :=
    (hframe1 Register.x2 (by decide) (by decide)).trans hx2
  have hx19_1 : σ1.regs.get? Register.x19 = some Wl :=
    (hframe1 Register.x19 (by decide) (by decide)).trans hx19
  have hframeC : ∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
      σ1.regs.get? R = σ.regs.get? R := by
    intro R hR _he8
    have hab := hR.1
    exact hframe1 R (abiNoise_noiseRegs hR) (by block_frame_wr [14, 15, 11, 15])
  refine ⟨σ1, i1, ?_, hi1, hG1, hmem1e, hpc1, hx11_1, hx9_1, hx2_1, hx19_1, hout1, hmi1, hframeC⟩
  have hlen : u + blenB leLadB5 = u + 5 := by
    rw [show blenB leLadB5 = 5 from by decide]
  rw [← hlen]
  exact hsteps1

/-- LE `LBG` `0x80003af8 → 0x80003b00` (2 steps): `slti x11,x11,1` (the `le` fixup)
+ `mv x10,x9` (`value_bool` self-pointer arg).  The `jal value_bool` @0x3b00 is NOT a
block terminator — the seam is hand-threaded by the assembler. -/
def leLadG : BBlock :=
  { body :=
      [mkLine 0x80003af8#64 0x0015a593#32,   -- slti x11,x11,1
       mkLine 0x80003afc#64 0x00048513#32],  -- mv   x10,x9  (addi x10,x9,0)
    term := none }

theorem evalLeLadderG (σ : MState) (i u : Nat) (vm cmpV sret v2 Wl : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003af8#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx11 : σ.regs.get? Register.x11 = some cmpV)
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 2⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      σ'.regs.get? Register.PC = some (0x80003b00#64) ∧
      σ'.regs.get? Register.x11
        = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_s cmpV (sign_extend (m := 64) (0x001#12))))) ∧
      σ'.regs.get? Register.x10 = some sret ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x19 = some Wl ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt leLadG σ i u (0x80003af8#64) vm
      [(11, cmpV), (9, sret)] []
      hG hpc hmi ⟨hx11, hx9, trivial⟩
      (show KeysOK [11, 9] by decide)
      (by block_facts hmem with "Vsa.Sim.Code.eval_expr_at_")
      (show BBlockOK (0x80003af8#64) [11, 9] leLadG by decide) hi
  have hmem1e : σ1.mem = σ.mem := hmem1
  rw [show endPCB (0x80003af8#64) leLadG [(11, cmpV), (9, sret)] []
        = (0x80003b00#64 : BitVec 64) from by
          show endPCM (0x80003af8#64) leLadG.body = (0x80003b00#64 : BitVec 64)
          decide] at hpc1
  have hx11_1 : σ1.regs.get? Register.x11
      = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_s cmpV (sign_extend (m := 64) (0x001#12))))) :=
    block_reg hGH1 11
  have hx10v : (sret + sign_extend (m := 64) (0x000#12)) = sret := by
    have : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by decide
    rw [this, BitVec.add_zero]
  have hx10_1 : σ1.regs.get? Register.x10 = some sret :=
    hx10v ▸ (block_reg hGH1 10 : σ1.regs.get? Register.x10
      = some (sret + sign_extend (m := 64) (0x000#12)))
  have hx9_1 : σ1.regs.get? Register.x9 = some sret :=
    (hframe1 Register.x9 (by decide) (by decide)).trans hx9
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 :=
    (hframe1 Register.x2 (by decide) (by decide)).trans hx2
  have hx19_1 : σ1.regs.get? Register.x19 = some Wl :=
    (hframe1 Register.x19 (by decide) (by decide)).trans hx19
  have hframeC : ∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
      σ1.regs.get? R = σ.regs.get? R := by
    intro R hR _he8
    have hab := hR.1
    exact hframe1 R (abiNoise_noiseRegs hR) (by block_frame_wr [11, 10])
  exact ⟨σ1, i1, hsteps1, hi1, hG1, hmem1e, hpc1, hx11_1, hx10_1, hx9_1, hx2_1, hx19_1, hout1, hmi1, hframeC⟩

end Vsa.Sim
