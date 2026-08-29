import Vsa.Sim.EvalGeChain

/-!
# `BinopChainGen` — the generic binary-op item-1 ENTRY LINKAGE, parameterised

`evalDivChain_run` (`EvalDivChain.lean`) is the `.div` instance of the arm-entry
linkage `TwoSubReturn (0x8000351c) → SegPre <arm>`: a 16-step dispatch prefix
(`gtChainB1`/`gtChainB2a`/`gtChainB2b`, ALL arm-independent) then the `jr`
jump-table dispatch @0x80003558 routing the op token to its arm PC.  Every binop
runs the SAME prefix + the SAME jump table; only FOUR data points differ:

  1. the op token bytes `tokBytes` (`[0x0e,0,0,0]` for `.div` = token 14);
  2. the switch index `idx` (`token − 11`);
  3. the jump-table slot address `slotAddr` (`opTableBase + 4*idx`) and its four
     little-endian slot bytes `slotBytes` (the relative offset to `armPC`);
  4. the arm PC `armPC` (the `jr` target).

`evalBinopChain_run` below proves the whole entry linkage ONCE, taking those four
data points as parameters and the per-op `decide` facts (token value, index value,
slot-address value, `jr`-routing) as hypotheses.  `#derive_binop_item1` (and the
hand `EvalDivChain`/mod/eq/ne instantiations) then supply the four `decide`s in
~15 lines — the heavy 16-step block-soundness proof elaborates only in THIS file,
so each op's item-1 entry linkage costs ~one composition, not a 250-line clone.

This is a strict generalisation of `evalDivChain_run`: instantiating it at
`tokBytes := [0x0e,0,0,0]`, `idx := 3`, `slotAddr := 0x80019f90`,
`slotBytes := [0x58,0x98,0xfe,0xff]`, `armPC := 0x800037dc` reproduces
`evalDivChain_run`'s conclusion (see `EvalBinopChainDiv.lean`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Sim.Code

namespace Vsa.Sim

/-- A generic 4-byte jump-table slot pin at `slotAddr` holding `[s0,s1,s2,s3]`.
The `.div` `DivSlotPinned` is the `slotAddr := opTableBase+12`, bytes
`[0x58,0x98,0xfe,0xff]` instance. -/
def SlotPinned (slotAddr : BitVec 64) (s0 s1 s2 s3 : BitVec 8)
    (m : Mem) : Prop :=
  m[slotAddr.toNat]? = some s0 ∧
  m[slotAddr.toNat + 1]? = some s1 ∧
  m[slotAddr.toNat + 2]? = some s2 ∧
  m[slotAddr.toNat + 3]? = some s3

/-- The generic `block-2b` load data: the slot word `[s0,s1,s2,s3]` (routing to
`armPC`) then the left-kind reload `[k0..k7]`.  Generalises `divLds2`. -/
def binopLds2 (s0 s1 s2 s3 : BitVec 8) (k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 8) :
    List (List (BitVec 8)) :=
  [[s0, s1, s2, s3], [k0, k1, k2, k3, k4, k5, k6, k7]]

/-- The generic `block-1` op-token / operand load data.  Generalises `divLds1`;
the token bytes `[t0,t1,t2,t3]` are the op-token word (`14 = [0x0e,0,0,0]`). -/
def binopLds1 (t0 t1 t2 t3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8) :
    List (List (BitVec 8)) :=
  [[t0, t1, t2, t3], [b0, b1, b2, b3], [c0, c1, c2, c3],
   [d0, d1, d2, d3, d4, d5, d6, d7]]

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- **The generic binary-op item-1 entry linkage: `0x8000351c → armPC`.**  Faithful
generalisation of `evalDivChain_run` reusing the arm-independent prefix blocks
`gtChainB1`/`gtChainB2a`/`gtChainB2b` VERBATIM (16 steps), parameterised by the four
data points (`tokBytes`, `idx`, `slotAddr`, `slotBytes`, `armPC`) via the four
per-op `decide` hypotheses.  Lands the arm-entry pins (`x16=2, x10=2, x2=v2,
x9=sret, x17=Wr, x19=Wl`, plus `x12=token`) at `armPC`. -/
theorem evalBinopChain_run (σ : MState) (i u : Nat) (vm v2 v8 sret Wl : BitVec 64)
    (token idx slotAddr armPC : BitVec 64)
    (t0 t1 t2 t3 : BitVec 8) (s0 s1 s2 s3 : BitVec 8)
    (b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8)
    (k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 8)
    -- the four per-op `decide` facts (self-checking on the derived data):
    (hTokVal : (bytesVal MKind.lw [t0, t1, t2, t3] : BitVec 64) = token)
    (hIndexVal : (sign_extend (m := 64) (Sail.BitVec.extractLsb
      (bytesVal MKind.lw [t0, t1, t2, t3]
        + sign_extend (m := 64) (0xff5#12)) 31 0) : BitVec 64) = idx)
    (hSlotAddr : (shift_bits_right (shift_bits_left idx
        (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
      + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
          + sign_extend (m := 64) (0xa44#12))) = slotAddr)
    (hRoutes : (BitVec.update ((bytesVal MKind.lw [s0, s1, s2, s3]
        + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1) = armPC)
    (hBltu : guardB bop.BLTU
        ((0#64 : BitVec 64) + sign_extend (m := 64) (0x00c#12))
        (sign_extend (m := 64) (Sail.BitVec.extractLsb
          (bytesVal MKind.lw [t0, t1, t2, t3]
            + sign_extend (m := 64) (0xff5#12)) 31 0)) = false)
    (sLo : 0x80000000 ≤ slotAddr.toNat)
    (sHi : slotAddr.toNat + 4 ≤ 0x100000000)
    (sHt : slotAddr.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ slotAddr.toNat)
    (sAl : slotAddr.toNat % 4 = 0)
    (hRoutesAl : (BitVec.update ((bytesVal MKind.lw [s0, s1, s2, s3]
        + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000351c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hc : bytesVal MKind.lw [c0, c1, c2, c3] = (2#64 : BitVec 64))
    (hk : bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7] = (2#64 : BitVec 64))
    (a_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_hi : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (a_ht : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_al : (v8 + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (a_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some t0)
    (a_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some t1)
    (a_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some t2)
    (a_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some t3)
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
    (hSlot : SlotPinned slotAddr s0 s1 s2 s3 σ.mem)
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
      σ'.regs.get? Register.PC = some armPC ∧
      σ'.regs.get? Register.x10 = some (2#64) ∧
      σ'.regs.get? Register.x12 = some token ∧
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
  -- ── Block 1 (gtChainB1) + bltu@0x3534 NOT taken → 0x80003538 ──────────────
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt gtChainB1 σ i u (0x8000351c#64) vm
      [(8, v8), (2, v2)] (binopLds1 t0 t1 t2 t3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
      hG hpc hmi ⟨hx8, hx2, trivial⟩
      (show KeysOK [8, 2] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨a_lo, a_hi, a_ht, a_al⟩, a_p0, a_p1, a_p2, a_p3⟩
        · exact ⟨⟨b_lo, b_hi, b_ht, b_al⟩, b_p0, b_p1, b_p2, b_p3⟩
        · exact ⟨⟨c_lo, c_hi, c_ht, c_al⟩, c_p0, c_p1, c_p2, c_p3⟩
        · exact ⟨⟨d_lo, d_hi, d_ht, d_al⟩, d_p0, d_p1, d_p2, d_p3, d_p4, d_p5, d_p6, d_p7⟩
        · exact hBltu)
      (show BBlockOK (0x8000351c#64) [8, 2] gtChainB1 by decide) hi
  have hmem1e : σ1.mem = σ.mem := hmem1
  rw [show endPCB (0x8000351c#64) gtChainB1 [(8, v8), (2, v2)]
        (binopLds1 t0 t1 t2 t3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
        = (0x80003538#64 : BitVec 64) from by
          show BitVec.addInt (0x80003534#64) 4 = (0x80003538#64 : BitVec 64)
          decide] at hpc1
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 := block_reg hGH1 2
  have hx15_1 : σ1.regs.get? Register.x15 = some idx :=
    hIndexVal ▸ (block_reg hGH1 15 : σ1.regs.get? Register.x15
      = some (sign_extend (m := 64) (Sail.BitVec.extractLsb
          (bytesVal MKind.lw [t0, t1, t2, t3]
            + sign_extend (m := 64) (0xff5#12)) 31 0)))
  have hx12_1 : σ1.regs.get? Register.x12 = some token :=
    hTokVal ▸ (block_reg hGH1 12 : σ1.regs.get? Register.x12
      = some (bytesVal MKind.lw [t0, t1, t2, t3]))
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
  -- ── Block 2a (ALU) → x15=slotAddr, x14=0x80019f84 (fall-through to 0x354c) ──
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt gtChainB2a σ1 i1 (u + blenB gtChainB1) (0x80003538#64) vm1
      [(15, idx)] []
      hG1 hpc1 hmi1' ⟨hx15_1, trivial⟩
      (show KeysOK [15] by decide)
      (by block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
            with "Vsa.Sim.Code.eval_expr_at_")
      (show BBlockOK (0x80003538#64) [15] gtChainB2a by decide) hi1
  have hmem2e : σ2.mem = σ.mem := by rw [hmem2]; exact hmem1e
  rw [show endPCB (0x80003538#64) gtChainB2a [(15, idx)] []
        = (0x8000354c#64 : BitVec 64) from by
          show endPCM (0x80003538#64) gtChainB2a.body = (0x8000354c#64 : BitVec 64)
          decide] at hpc2
  obtain ⟨vm2, hmi2'⟩ := hmi2
  have hx14v : ((((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
      + sign_extend (m := 64) (0xa44#12))) = 0x80019f84#64 := by decide
  have hx14_2 : σ2.regs.get? Register.x14 = some (0x80019f84#64) :=
    hx14v ▸ (block_reg hGH2 14 : σ2.regs.get? Register.x14
      = some (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
          + sign_extend (m := 64) (0xa44#12)))
  have hx15_2 : σ2.regs.get? Register.x15 = some slotAddr :=
    hSlotAddr ▸ (block_reg hGH2 15 : σ2.regs.get? Register.x15
      = some (shift_bits_right (shift_bits_left idx
            (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
          + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
              + sign_extend (m := 64) (0xa44#12))))
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 :=
    (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  have hx12_2 : σ2.regs.get? Register.x12 = some token :=
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
  -- the slot `lw x15,0(x15)` has effective address `slotAddr + sign_extend(0) = slotAddr`.
  have hsa0 : (slotAddr + sign_extend (m := 64) (0#12) : BitVec 64) = slotAddr := by
    rw [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 from by decide, BitVec.add_zero]
  have hSlot2 : σ2.mem[(slotAddr + sign_extend (m := 64) (0#12)).toNat]? = some s0 ∧
      σ2.mem[(slotAddr + sign_extend (m := 64) (0#12)).toNat + 1]? = some s1 ∧
      σ2.mem[(slotAddr + sign_extend (m := 64) (0#12)).toNat + 2]? = some s2 ∧
      σ2.mem[(slotAddr + sign_extend (m := 64) (0#12)).toNat + 3]? = some s3 := by
    rw [hmem2e, hsa0]; exact ⟨sp0, sp1, sp2, sp3⟩
  have sLo' : 0x80000000 ≤ (slotAddr + sign_extend (m := 64) (0#12)).toNat := by rw [hsa0]; exact sLo
  have sHi' : (slotAddr + sign_extend (m := 64) (0#12)).toNat + 4 ≤ 0x100000000 := by rw [hsa0]; exact sHi
  have sHt' : (slotAddr + sign_extend (m := 64) (0#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (slotAddr + sign_extend (m := 64) (0#12)).toNat := by rw [hsa0]; exact sHt
  have sAl' : (slotAddr + sign_extend (m := 64) (0#12)).toNat % 4 = 0 := by rw [hsa0]; exact sAl
  have hKind2 : σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat]? = some k0 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some k1 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some k2 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some k3 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some k4 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some k5 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some k6 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some k7 := by
    rw [hmem2e]; exact ⟨e_p0, e_p1, e_p2, e_p3, e_p4, e_p5, e_p6, e_p7⟩
  -- ── Block 2b (lw/ld/add + jr@0x3558) → armPC ─────────────────────────
  obtain ⟨σ3, i3, hsteps3, hi3, hG3, hmem3, hout3, hpc3, hmi3, hGH3, hframe3⟩ :=
    bblock_sound_bt gtChainB2b σ2 i2 (u + blenB gtChainB1 + blenB gtChainB2a) (0x8000354c#64) vm2
      [(15, slotAddr), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
      (binopLds2 s0 s1 s2 s3 k0 k1 k2 k3 k4 k5 k6 k7)
      hG2 hpc2 hmi2' ⟨hx15_2, hx2_2, hx14_2, trivial⟩
      (show KeysOK [15, 2, 14] by decide)
      (by
        block_facts (hmem2e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ2.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨sLo', sHi', sHt', sAl'⟩,
            hSlot2.1, hSlot2.2.1, hSlot2.2.2.1, hSlot2.2.2.2⟩
        · exact ⟨⟨e_lo, e_hi, e_ht, e_al⟩,
            hKind2.1, hKind2.2.1, hKind2.2.2.1, hKind2.2.2.2.1,
            hKind2.2.2.2.2.1, hKind2.2.2.2.2.2.1, hKind2.2.2.2.2.2.2.1, hKind2.2.2.2.2.2.2.2⟩
        · exact hRoutesAl)
      (show BBlockOK (0x8000354c#64) [15, 2, 14] gtChainB2b by decide) hi2
  rw [show endPCB (0x8000354c#64) gtChainB2b
        [(15, slotAddr), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
        (binopLds2 s0 s1 s2 s3 k0 k1 k2 k3 k4 k5 k6 k7) = armPC from by
          rw [← hRoutes]
          show BitVec.update ((bytesVal MKind.lw [s0, s1, s2, s3]
              + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1
            = BitVec.update ((bytesVal MKind.lw [s0, s1, s2, s3]
              + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1
          rfl] at hpc3
  have hx16_3 : σ3.regs.get? Register.x16 = some (2#64) :=
    hk ▸ (block_reg hGH3 16 : σ3.regs.get? Register.x16
      = some (bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7]))
  have hx12_3 : σ3.regs.get? Register.x12 = some token :=
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
  refine ⟨σ3, i3, ?_, hi3, hG3, hpc3, hx10_3, hx12_3, hx16_3, hx17_3, hx2_3, hx9_3, hx19_3,
    hmem3e, hout3e, hmi3, hframeC⟩
  have hlen : u + blenB gtChainB1 + blenB gtChainB2a + blenB gtChainB2b = u + 16 := by
    rw [show blenB gtChainB1 = 7 from by decide, show blenB gtChainB2a = 5 from by decide,
      show blenB gtChainB2b = 4 from by decide]
  rw [← hlen]
  exact (hsteps1.trans hsteps2).trans hsteps3

#print axioms evalBinopChain_run

end Vsa.Sim
