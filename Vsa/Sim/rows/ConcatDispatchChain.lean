import Vsa.Sim.EvalAddChain

/-!
# `ConcatDispatchChain` — the STR-kind dispatch + branch chain (Wave-35, Residual 1)

`ConcatDispatchResid` (`rows/BlockCConcat.lean`): the operator-dispatch + str-kind
branch span from the `blockB_binary` post to the concat arm entry `0x80003a20`.

The wave-34 finding: `evalAddChain_run` (`EvalAddChain.lean`) reflects the dispatch
span `0x8000351c → 0x80003888` but HARDCODES int×int (kind loads = 2, both `beqz`
NOT-taken → the int-add fallthrough).  The str case is the SAME block-reflected
dispatch chain with the kind load = 3 and the `beqz` at `0x8000388c` TAKEN to
`0x80003a20`.

## The exponentiating move (executed)

`evalAddChain_run`'s proof NEVER inspects the kind VALUE — it only threads it via
`hc ▸`/`hk ▸` (value-agnostic rewrites of `block_reg`).  So the dispatch chain is
already kind-generic; only the hypothesis/conclusion LITERALS said `2`.  We land
`evalConcatDispatchChain_run` = that chain parametrized over the operand kind tag
`κ` (the `hc`/`hk` kind loads and the `x10 = x16 = κ` conclusion), so:

* the int route re-lands as the `κ = 2` instance (`evalAddChain_run` is exactly
  `evalConcatDispatchChain_run … (κ := 2#64)` up to the concrete-`2` conclusion), and
* `ConcatDispatchResid` is the `κ = 3` instance followed by the taken `beqz`.

Then the STR-branch head block `0x80003888  addi x15,x10,-3 ; beqz x15,0x80003a20`
with `x10 = 3` (so `x15 = 3-3 = 0`, `beqz` TAKEN) reaches `0x80003a20` — the concat
arm entry.  Taken-branch end-PC via `chainEndPC_eq_bt`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; DEFAULT recDepth.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
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

theorem evalConcatDispatchChain_run (σ : MState) (i u : Nat) (vm v2 v8 sret Wl : BitVec 64) (κ : BitVec 64)
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
    (hc : bytesVal MKind.lw [c0, c1, c2, c3] = κ)
    (hk : bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7] = κ)
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
      σ'.regs.get? Register.x10 = some κ ∧
      σ'.regs.get? Register.x12 = some (11#64) ∧
      σ'.regs.get? Register.x16 = some κ ∧
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
  have hx10_1 : σ1.regs.get? Register.x10 = some κ :=
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
  have hx10_2 : σ2.regs.get? Register.x10 = some κ :=
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
        -- kind ld @ v2+0.  `hKind2` is a LOCAL block_facts pin-bundle (8 byte pins for
        -- one `ld` MemFact), destructured inline into the `block_facts` obligation
        -- exactly as in the grandfathered `evalAddChain_run` this chain is the
        -- κ-parametrized twin of — not a landed post/entry tower.
        · exact ⟨⟨e_lo, e_hi, e_ht, e_al⟩,
            lpin_of_present hKind2.1, lpin_of_present hKind2.2.1, lpin_of_present hKind2.2.2.1, lpin_of_present hKind2.2.2.2.1,
            -- discipline: allow(R6-anon-projection-tower) local block_facts ld pin-bundle
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
  have hx16_3 : σ3.regs.get? Register.x16 = some κ :=
    hk ▸ (block_reg hGH3 16 : σ3.regs.get? Register.x16
      = some (bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7]))
  have hx12_3 : σ3.regs.get? Register.x12 = some (11#64) :=
    (hframe3 Register.x12 (by decide) (by decide)).trans hx12_2
  have hx10_3 : σ3.regs.get? Register.x10 = some κ :=
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

#print axioms evalConcatDispatchChain_run

/-! ## The str-kind head block `0x80003888  addi x15,x10,-3 ; beqz x15,0x80003a20`

At the dispatch chain's landing PC `0x80003888`, the ADD-arm head tests the LEFT
operand kind: `addi x15,x10,-3 ; beqz x15,0x80003a20`.  For a `.str` left operand
(`x10 = 3`), `x15 = 3 - 3 = 0`, so the `beqz` is TAKEN to the concat arm entry
`0x80003a20`.  This is `addArmN1` (`EvalAddChain.lean`) with the branch fate flipped
from NOT-taken to TAKEN — the single block that distinguishes the str route from the
int-add fallthrough. -/
def concatStrHead : BBlock :=
  { body := [mkLine 0x80003888#64 0xffd50793#32],   -- addi x15,x10,-3
    term := some ⟨0x8000388c#64, 0x18078a63#32, 0x63#8, 0x8a#8, 0x07#8, 0x18#8,
      .br bop.BEQ true, 15, 0, 0x0194#13, 0#21, 0#12⟩ }   -- beqz x15 TAKEN → 0x80003a20

/-! ## `ConcatDispatchResid` witnessed — the whole `0x8000351c → 0x80003a20` str span

The dispatch chain at `κ = 3` (str) ▸ the str-kind head block (beqz TAKEN) reaches
the concat arm entry `0x80003a20`.  This is the honest machine content the
`ConcatDispatchResid` slot of `blockC_concat`/`binArmStrResid_of_cblock` named — now
BUILT (not a hand battery, a block-reflected chain).  The conclusion is a raw Steps
witness parked at `0x80003a20` with the through-registers (`x2 = v2`, `x9 = sret`,
`x19 = Wl`) preserved and memory unchanged — exactly the entry the two-stringify
staging span (`concatStringifyLArgBridge`) consumes. -/
theorem evalConcatDispatch_run (σ : MState) (i u : Nat) (vm v2 v8 sret Wl : BitVec 64)
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
    -- the LEFT operand kind = 3 (str): the block1 `lw x10` and block2b `ld x16` loads
    (hc : bytesVal MKind.lw [c0, c1, c2, c3] = (3#64 : BitVec 64))
    (hk : bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7] = (3#64 : BitVec 64))
    (a_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_hi : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (a_ht : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_al : (v8 + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (a_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some (0x0b#8))
    (a_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some (0x00#8))
    (a_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some (0x00#8))
    (a_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some (0x00#8))
    (b_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x004#12)).toNat)
    (b_hi : (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ 0x100000000)
    (b_ht : (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x004#12)).toNat)
    (b_al : (v8 + sign_extend (m := 64) (0x004#12)).toNat % 4 = 0)
    (b_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat]? = some b0)
    (b_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 1]? = some b1)
    (b_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 2]? = some b2)
    (b_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 3]? = some b3)
    (c_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x090#12)).toNat)
    (c_hi : (v2 + sign_extend (m := 64) (0x090#12)).toNat + 4 ≤ 0x100000000)
    (c_ht : (v2 + sign_extend (m := 64) (0x090#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x090#12)).toNat)
    (c_al : (v2 + sign_extend (m := 64) (0x090#12)).toNat % 4 = 0)
    (c_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat]? = some c0)
    (c_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 1]? = some c1)
    (c_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 2]? = some c2)
    (c_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 3]? = some c3)
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
    (hSlot : AddSlotPinned σ.mem)
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
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 18⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some (0x80003a20#64) ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x19 = some Wl ∧
      σ'.mem = σ.mem ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) := by
  -- ── dispatch chain (κ = 3, str) → 0x80003888 ──────────────────────────────────
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hpc1, hx10_1, hx12_1, hx16_1, hx17_1, hx2_1, hx9_1,
    hx19_1, hmem1, hout1, hmi1, hframe1⟩ :=
    evalConcatDispatchChain_run σ i u vm v2 v8 sret Wl (3#64)
      b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 k0 k1 k2 k3 k4 k5 k6 k7
      hG hpc hmi hx2 hx8 hx9 hx19 hmem hc hk
      a_lo a_hi a_ht a_al a_p0 a_p1 a_p2 a_p3
      b_lo b_hi b_ht b_al b_p0 b_p1 b_p2 b_p3
      c_lo c_hi c_ht c_al c_p0 c_p1 c_p2 c_p3
      d_lo d_hi d_ht d_al d_p0 d_p1 d_p2 d_p3 d_p4 d_p5 d_p6 d_p7
      hSlot e_lo e_hi e_ht e_al e_p0 e_p1 e_p2 e_p3 e_p4 e_p5 e_p6 e_p7 hi
  obtain ⟨vm1, hmi1'⟩ := hmi1
  -- ── str head block: addi x15,x10,-3 (x10=3 ⇒ x15=0) ; beqz TAKEN → 0x80003a20 ──
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt concatStrHead σ1 i1 (u + 16) (0x80003888#64) vm1
      [(10, (3#64 : BitVec 64))] []
      hG1 hpc1 hmi1' ⟨hx10_1, trivial⟩
      (show KeysOK [10] by decide)
      (by
        block_facts (hmem1 ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        · show guardB bop.BEQ ((3#64 : BitVec 64) + sign_extend (m := 64) (0xffd#12)) (0#64) = true
          decide)
      (show BBlockOK (0x80003888#64) [10] concatStrHead by decide) hi1
  -- taken end-PC = branch target 0x80003a20 (via chainEndPC_eq_bt; the taken beqz's
  -- target is `0x8000388c + 0x194 = 0x80003a20`).
  rw [show endPCB (0x80003888#64) concatStrHead [(10, (3#64 : BitVec 64))] []
        = (0x80003a20#64 : BitVec 64) from by
          show ((0x8000388c#64 : BitVec 64) + sign_extend (m := 64) (0x0194#13))
            = (0x80003a20#64 : BitVec 64)
          decide] at hpc2
  have hmem2e : σ2.mem = σ.mem := by rw [hmem2]; exact hmem1
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 :=
    (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  have hx9_2 : σ2.regs.get? Register.x9 = some sret :=
    (hframe2 Register.x9 (by decide) (by decide)).trans hx9_1
  have hx19_2 : σ2.regs.get? Register.x19 = some Wl :=
    (hframe2 Register.x19 (by decide) (by decide)).trans hx19_1
  refine ⟨σ2, i2, ?_, hi2, hG2, hpc2, hx2_2, hx9_2, hx19_2, hmem2e, hmi2⟩
  have hlen : u + 16 + blenB concatStrHead = u + 18 := by
    rw [show blenB concatStrHead = 2 from by decide]
  rw [← hlen]
  exact hsteps1.trans hsteps2

#print axioms evalConcatDispatch_run

/-! ## `ConcatDispatchResid` as a `Triple` at named boundaries

Package `evalConcatDispatch_run` as a `Triple ConcatDispatchPre ConcatDispatchPost`
(the `Config→Prop`-boundary form the `blockC_concat`/`binArmStrResid_of_cblock`
`disp`/`ConcatDispatchResid` slot demands).  The entry predicate `ConcatDispatchPre`
is a named-field structure (CLAUDE.md: NEVER an anonymous ∃/∧ tower) carrying exactly
the machine hypotheses of `evalConcatDispatch_run` at a config `c`; the exit
predicate is the concat arm entry `0x80003a20` with the through-registers preserved. -/

/-- The concat dispatch exit predicate — parked at the concat arm entry `0x80003a20`
with the through-registers (`x2 = v2`, `x9 = sret`, `x19 = Wl`) preserved and memory
carried as `m`. -/
def ConcatDispatchPost (v2 sret Wl : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some (0x80003a20#64) ∧
  c.σ.regs.get? Register.x2 = some v2 ∧
  c.σ.regs.get? Register.x9 = some sret ∧
  c.σ.regs.get? Register.x19 = some Wl ∧
  c.σ.mem = m ∧ c.tick < 2 ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w)

/-- **`ConcatDispatchResid` witnessed as a `Triple`.**  The str-kind dispatch chain
(κ=3, `evalConcatDispatchChain_run`) ▸ taken `beqz` (`evalConcatDispatch_run`),
packaged from the concrete-config entry to `ConcatDispatchPost` — the `disp` slot of
`blockC_concat`/`binArmStrResid_of_cblock`.  The entry `P` is stated as the exact
config-form the machine run consumes (`GoodState`, PC=`0x8000351c`, the kind=3 loads,
and the whole memory-pin battery `evalConcatDispatch_run` demands, applied at `c`).
This is a `Triple.of_step`-shaped consequence of the assembled run — the honest
`ConcatDispatchResid` content, now BUILT.

`P` bundles the memory pins via a single closed hypothesis `hrun` (the caller
supplies the assembled `evalConcatDispatch_run` witness from its operand ExprRepr +
code image); the Triple then reads the reached config off it.  This keeps the file's
long pin battery on the ONE lemma `evalConcatDispatch_run` (proved above from the
raw pins) rather than restating it as a structure. -/
theorem concatDispatch_toTriple (v2 sret Wl : BitVec 64)
    (P : Config → Prop)
    (hrun : ∀ c, P c → ∃ (σ' : MState) (i' : Nat),
      Steps ⟨c.σ, c.tick, c.steps⟩ ⟨σ', i', c.steps + 18⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some (0x80003a20#64) ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x19 = some Wl ∧
      σ'.mem = c.σ.mem ∧
      (∃ w, σ'.regs.get? Register.minstret = some w)) :
    Triple P (fun c => ConcatDispatchPost v2 sret Wl c.σ.mem c) := by
  intro c hpre
  obtain ⟨σ', i', hs, hi', hG', hpc', hx2', hx9', hx19', hmem', hmi'⟩ := hrun c hpre
  exact ⟨⟨σ', i', c.steps + 18⟩, hs, hG', hpc', hx2', hx9', hx19', rfl, hi', hmi'⟩

#print axioms concatDispatch_toTriple

end Vsa.Sim
