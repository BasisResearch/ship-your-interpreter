import Vsa.Sim.EvalGtChain
import Vsa.Sim.DecodeTable.Batch11Part13
import Vsa.Sim.DecodeTable.Batch12Part02

/-!
# `EvalMulChain` — the `.mul` opening chain (0x351c → 0x80003834, the MUL-int arm)

The operator-dispatch prologue for `.mul` (token 13).  Reuses the comparison
chain block defs `gtChainB1/gtChainB2a/gtChainB2b` + `gtLds2` verbatim — the
instruction WORDS are identical; only the op-token value (13), the kind-ladder
register `x15 = token-11 = 2`, the CSWTCH.18 slot address (`0x80019f8c` =
`opTableBase+8` = index 2), the slot bytes (`b0 98 fe ff` via `MulSlotPinned`),
and the `jr` target (`0x80003834`, the MUL-int arm) differ from `.sub`.

The MUL-int arm `0x80003834 → 0x80003868` (S1/S2 store ladder) is byte-identical
to the SUB arm's `S1`/`S2` at shifted PCs — only the two `bne` TERMINATORS differ
(offsets 0x438 / 0x3d4 vs sub's 0x5f8 / 0x5b4, i.e. words `0x42d81c63` /
`0x3d051a63`).  The MUL arm has NO `sub`/`mv` `Fin` block: it lands at 0x80003868
where the `__muldi3` seam (`MulTailSites`) takes over.

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

/-! ## The `wrap64` bridge for the `mul` exit value -/

/-- `value_int` produces `.int (BitVec.ofNat 64 pay.toNat).toInt` with the payload
`pay = Wr * Wl` (the machine 64-bit `__muldi3`, which computes `x10*x11 = a0*a1 =
Wr*Wl`).  Since `Wl.toInt = a`, `Wr.toInt = b`, this equals `.int (wrap64 (a*b))`
(commuting the machine's `Wr*Wl` to the spec's `a*b`). -/
theorem mul_wrap_bridge (Wl Wr : BitVec 64) (a b : Int)
    (ha : Wl.toInt = a) (hb : Wr.toInt = b) :
    (BitVec.ofNat 64 (Wr * Wl).toNat).toInt = wrap64 (a * b) := by
  rw [ofNat_toNat_self64, ← ha, ← hb]
  unfold wrap64
  have h : (BitVec.ofInt 64 (Wl.toInt * Wr.toInt)) = Wr * Wl := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_mul, BitVec.toInt_ofInt, Int.mul_comm]
  rw [h]

/-! ## `MulSlotPinned` — the operator jump-table slot pin for `.mul`

`.mul` (token 13, index 2) → slot bytes `b0 98 fe ff` @ `0x80019f8c`, target
`0x80019f84 + (Int32)0xfffe98b0 = 0x80003834`. -/
def MulSlotPinned (m : Mem) : Prop :=
  m[(opTableBase + 8 : Nat)]? = some (0xb0 : BitVec 8) ∧
  m[(opTableBase + 9 : Nat)]? = some (0x98 : BitVec 8) ∧
  m[(opTableBase + 10 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(opTableBase + 11 : Nat)]? = some (0xff : BitVec 8)

/-- `MulSlotPinned` survives a `writeMap8` disjoint from `[opTableBase+8, +4)`. -/
theorem mulSlot_writeMap8 (m : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ opTableBase + 8 ∨ opTableBase + 12 ≤ a8) (h : MulSlotPinned m) :
    MulSlotPinned (writeMap8 m a8 d) := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint m a8 _ d (by omega)]; assumption)

/-- Mul op-token load bytes (`13 = [0x0d,0,0,0]`), concrete for the `bltu` guard. -/
def mulLds1 (b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8) :
    List (List (BitVec 8)) :=
  [[0x0d#8, 0x00#8, 0x00#8, 0x00#8], [b0, b1, b2, b3], [c0, c1, c2, c3],
   [d0, d1, d2, d3, d4, d5, d6, d7]]

/-- B2b's load bytes for `.mul`: op-table slot (`[b0 98 fe ff]`, concrete so the
`jr` target reduces to 0x80003834) then the kind-reload (free byte pins). -/
def mulLds2 (k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 8) : List (List (BitVec 8)) :=
  [[0xb0#8, 0x98#8, 0xfe#8, 0xff#8], [k0, k1, k2, k3, k4, k5, k6, k7]]

/-- The opening 16-instruction run of `.mul`, `0x8000351c → 0x80003834`,
via TWO shallow `bblock_sound_bt` applications (block 1 + `bltu`, block 2 + `jr`). -/
theorem evalMulChain_run (σ : MState) (i u : Nat) (vm v2 v8 sret Wl : BitVec 64)
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
    (hc : bytesVal MKind.lw [c0, c1, c2, c3] = (2#64 : BitVec 64))
    (hk : bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7] = (2#64 : BitVec 64))
    (a_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_hi : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (a_ht : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_al : (v8 + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (a_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some (0x0d#8))
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
    (hSlot : MulSlotPinned σ.mem)
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
      σ'.regs.get? Register.PC = some (0x80003834#64) ∧
      σ'.regs.get? Register.x10 = some (2#64) ∧
      σ'.regs.get? Register.x12 = some (13#64) ∧
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
      [(8, v8), (2, v2)] (mulLds1 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
      hG hpc hmi ⟨hx8, hx2, trivial⟩
      (show KeysOK [8, 2] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨a_lo, a_hi, a_ht, a_al⟩, lpin_of_present a_p0, lpin_of_present a_p1, lpin_of_present a_p2, lpin_of_present a_p3⟩
        · exact ⟨⟨b_lo, b_hi, b_ht, b_al⟩, lpin_of_present b_p0, lpin_of_present b_p1, lpin_of_present b_p2, lpin_of_present b_p3⟩
        · exact ⟨⟨c_lo, c_hi, c_ht, c_al⟩, lpin_of_present c_p0, lpin_of_present c_p1, lpin_of_present c_p2, lpin_of_present c_p3⟩
        · exact ⟨⟨d_lo, d_hi, d_ht, d_al⟩, lpin_of_present d_p0, lpin_of_present d_p1, lpin_of_present d_p2, lpin_of_present d_p3, lpin_of_present d_p4, lpin_of_present d_p5, lpin_of_present d_p6, lpin_of_present d_p7⟩
        · show guardB bop.BLTU
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x00c#12))
            (sign_extend (m := 64) (Sail.BitVec.extractLsb
              (bytesVal MKind.lw [0x0d#8, 0x00#8, 0x00#8, 0x00#8]
                + sign_extend (m := 64) (0xff5#12)) 31 0)) = false
          decide)
      (show BBlockOK (0x8000351c#64) [8, 2] gtChainB1 by decide) hi
  have hmem1e : σ1.mem = σ.mem := hmem1
  rw [show endPCB (0x8000351c#64) gtChainB1 [(8, v8), (2, v2)]
        (mulLds1 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
        = (0x80003538#64 : BitVec 64) from by
          show BitVec.addInt (0x80003534#64) 4 = (0x80003538#64 : BitVec 64)
          decide] at hpc1
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 := block_reg hGH1 2
  -- x15 = addiw(op-token, -11) = 2 (token 13): peel the wrapper, then decide.
  have hx15v : (sign_extend (m := 64) (Sail.BitVec.extractLsb
      (bytesVal MKind.lw [0x0d#8, 0x00#8, 0x00#8, 0x00#8]
        + sign_extend (m := 64) (0xff5#12)) 31 0) : BitVec 64) = 2#64 := by decide
  have hx15_1 : σ1.regs.get? Register.x15 = some (2#64) :=
    hx15v ▸ (block_reg hGH1 15 : σ1.regs.get? Register.x15
      = some (sign_extend (m := 64) (Sail.BitVec.extractLsb
          (bytesVal MKind.lw [0x0d#8, 0x00#8, 0x00#8, 0x00#8]
            + sign_extend (m := 64) (0xff5#12)) 31 0)))
  have hx12v : (bytesVal MKind.lw [0x0d#8, 0x00#8, 0x00#8, 0x00#8] : BitVec 64) = 13#64 := by decide
  have hx12_1 : σ1.regs.get? Register.x12 = some (13#64) :=
    hx12v ▸ (block_reg hGH1 12 : σ1.regs.get? Register.x12
      = some (bytesVal MKind.lw [0x0d#8, 0x00#8, 0x00#8, 0x00#8]))
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
  -- ── Block 2a (ALU) → x15=0x80019f8c, x14=0x80019f84 (fall-through to 0x354c) ──
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt gtChainB2a σ1 i1 (u + blenB gtChainB1) (0x80003538#64) vm1
      [(15, (2#64 : BitVec 64))] []
      hG1 hpc1 hmi1' ⟨hx15_1, trivial⟩
      (show KeysOK [15] by decide)
      (by block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
            with "Vsa.Sim.Code.eval_expr_at_")
      (show BBlockOK (0x80003538#64) [15] gtChainB2a by decide) hi1
  have hmem2e : σ2.mem = σ.mem := by rw [hmem2]; exact hmem1e
  rw [show endPCB (0x80003538#64) gtChainB2a [(15, (2#64 : BitVec 64))] []
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
  have hx15v : (shift_bits_right (shift_bits_left (2#64 : BitVec 64)
        (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
      + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
          + sign_extend (m := 64) (0xa44#12))) = 0x80019f8c#64 := by decide
  have hx15_2 : σ2.regs.get? Register.x15 = some (0x80019f8c#64) :=
    hx15v ▸ (block_reg hGH2 15 : σ2.regs.get? Register.x15
      = some (shift_bits_right (shift_bits_left (2#64 : BitVec 64)
            (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
          + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
              + sign_extend (m := 64) (0xa44#12))))
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 :=
    (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  have hx12_2 : σ2.regs.get? Register.x12 = some (13#64) :=
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
  have hSlot2 : σ2.mem[(0x80019f8c#64 : BitVec 64).toNat]? = some (0xb0#8) ∧
      σ2.mem[(0x80019f8c#64 : BitVec 64).toNat + 1]? = some (0x98#8) ∧
      σ2.mem[(0x80019f8c#64 : BitVec 64).toNat + 2]? = some (0xfe#8) ∧
      σ2.mem[(0x80019f8c#64 : BitVec 64).toNat + 3]? = some (0xff#8) := by
    rw [hmem2e]; exact ⟨sp0, sp1, sp2, sp3⟩
  have sLo : 0x80000000 ≤ (0x80019f8c#64 : BitVec 64).toNat := by decide
  have sHi : (0x80019f8c#64 : BitVec 64).toNat + 4 ≤ 0x100000000 := by decide
  have sHt : (0x80019f8c#64 : BitVec 64).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (0x80019f8c#64 : BitVec 64).toNat := by decide
  have sAl : (0x80019f8c#64 : BitVec 64).toNat % 4 = 0 := by decide
  have hKind2 : σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat]? = some k0 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some k1 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some k2 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some k3 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some k4 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some k5 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some k6 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some k7 := by
    rw [hmem2e]; exact ⟨e_p0, e_p1, e_p2, e_p3, e_p4, e_p5, e_p6, e_p7⟩
  -- ── Block 2b (lw/ld/add + jr@0x3558) → 0x80003834 ─────────────────────────
  obtain ⟨σ3, i3, hsteps3, hi3, hG3, hmem3, hout3, hpc3, hmi3, hGH3, hframe3⟩ :=
    bblock_sound_bt gtChainB2b σ2 i2 (u + blenB gtChainB1 + blenB gtChainB2a) (0x8000354c#64) vm2
      [(15, (0x80019f8c#64 : BitVec 64)), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
      (mulLds2 k0 k1 k2 k3 k4 k5 k6 k7)
      hG2 hpc2 hmi2' ⟨hx15_2, hx2_2, hx14_2, trivial⟩
      (show KeysOK [15, 2, 14] by decide)
      (by
        block_facts (hmem2e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ2.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨sLo, sHi, sHt, sAl⟩,
            lpin_of_present hSlot2.1, lpin_of_present hSlot2.2.1, lpin_of_present hSlot2.2.2.1, lpin_of_present hSlot2.2.2.2⟩
        · exact ⟨⟨e_lo, e_hi, e_ht, e_al⟩,
            lpin_of_present hKind2.1, lpin_of_present hKind2.2.1, lpin_of_present hKind2.2.2.1, lpin_of_present hKind2.2.2.2.1,
            lpin_of_present hKind2.2.2.2.2.1, lpin_of_present hKind2.2.2.2.2.2.1, lpin_of_present hKind2.2.2.2.2.2.2.1, lpin_of_present hKind2.2.2.2.2.2.2.2⟩
        · show (BitVec.update ((bytesVal MKind.lw [0xb0#8, 0x98#8, 0xfe#8, 0xff#8]
              + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
          decide)
      (show BBlockOK (0x8000354c#64) [15, 2, 14] gtChainB2b by decide) hi2
  rw [show endPCB (0x8000354c#64) gtChainB2b
        [(15, (0x80019f8c#64 : BitVec 64)), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
        (mulLds2 k0 k1 k2 k3 k4 k5 k6 k7) = (0x80003834#64 : BitVec 64) from by
          show BitVec.update ((bytesVal MKind.lw [0xb0#8, 0x98#8, 0xfe#8, 0xff#8]
              + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1 = (0x80003834#64 : BitVec 64)
          decide] at hpc3
  have hx16_3 : σ3.regs.get? Register.x16 = some (2#64) :=
    hk ▸ (block_reg hGH3 16 : σ3.regs.get? Register.x16
      = some (bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7]))
  have hx12_3 : σ3.regs.get? Register.x12 = some (13#64) :=
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

/-! ## The `.mul` int-arm ladder `0x80003834 → 0x80003868`.

`evalMulChain_run` lands at `0x80003834` (the MUL-int arm) — the mul arm has NO
null-kind prefix.  Structure = the sub arm's `S1`/`S2` at shifted PCs (S1 @0x3834,
S2 @0x384c), with different `bne` terminators (offsets 0x438 / 0x3d4).  There is
NO `Fin` block: the arm falls through at `0x80003868` where the `__muldi3` seam
takes over.  Memory outcome = the five scratch stores (`writeMap8⁵`, opaque
`D1..D5`) at `v2+0xf0/0x100/0xf0/0xf8/0x100`. -/

/-- S1: `ld/ld/li/sd/sd` + `bne a6,a3` NOT taken (0x3834→0x384c). -/
def mulArmS1 : BBlock :=
  { body :=
      [mkLine 0x80003834#64 0x07813703#32,   -- ld   x14,0x78(x2)
       mkLine 0x80003838#64 0x08813783#32,   -- ld   x15,0x88(x2)
       mkLine 0x8000383c#64 0x00200693#32,   -- addi x13,x0,2 (li x13,2)
       mkLine 0x80003840#64 0x0ee13823#32,   -- sd   x14,0xf0(x2)
       mkLine 0x80003844#64 0x10f13023#32],  -- sd   x15,0x100(x2)
    term := some ⟨0x80003848#64, 0x42d81c63#32, 0x63#8, 0x1c#8, 0xd8#8, 0x42#8,
      .br bop.BNE false, 16, 13, 0x0438#13, 0#21, 0#12⟩ }

/-- S2: `ld/ld/ld/sd/sd/sd` + `bne a0,a6` NOT taken (0x384c→0x3868). -/
def mulArmS2 : BBlock :=
  { body :=
      [mkLine 0x8000384c#64 0x09013703#32,   -- ld x14,0x90(x2)
       mkLine 0x80003850#64 0x09813683#32,   -- ld x13,0x98(x2)
       mkLine 0x80003854#64 0x0a013783#32,   -- ld x15,0xa0(x2)
       mkLine 0x80003858#64 0x0ee13823#32,   -- sd x14,0xf0(x2)
       mkLine 0x8000385c#64 0x0ed13c23#32,   -- sd x13,0xf8(x2)
       mkLine 0x80003860#64 0x10f13023#32],  -- sd x15,0x100(x2)
    term := some ⟨0x80003864#64, 0x3d051a63#32, 0x63#8, 0x1a#8, 0x05#8, 0x3d#8,
      .br bop.BNE false, 10, 16, 0x03d4#13, 0#21, 0#12⟩ }

/-- The `.mul` int-arm ladder `0x80003834 → 0x80003868` (13 steps) via two shallow
`bblock_sound_bt` applications.  `x2/x9/x17/x19` pass through; memory = the five
scratch stores (`writeMap8⁵`, opaque `D1..D5`).  Lands at 0x80003868, the entry
to the `__muldi3` seam. -/
theorem evalMulArm_run (σ : MState) (i u : Nat) (vm v2 v12 sret Wl Wr : BitVec 64)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7 d0 d1 d2 d3 d4 d5 d6 d7
     e0 e1 e2 e3 e4 e5 e6 e7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003834#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx10 : σ.regs.get? Register.x10 = some (2#64))
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx16 : σ.regs.get? Register.x16 = some (2#64))
    (hx17 : σ.regs.get? Register.x17 = some Wr)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hn90 : (v2 + sign_extend (m := 64) (0x090#12)).toNat = v2.toNat + 0x90)
    (hn98 : (v2 + sign_extend (m := 64) (0x098#12)).toNat = v2.toNat + 0x98)
    (hna0 : (v2 + sign_extend (m := 64) (0x0a0#12)).toNat = v2.toNat + 0xa0)
    (hnf0 : (v2 + sign_extend (m := 64) (0x0f0#12)).toNat = v2.toNat + 0xf0)
    (hn100 : (v2 + sign_extend (m := 64) (0x100#12)).toNat = v2.toNat + 0x100)
    (hcf0 : (v2 + sign_extend (m := 64) (0x0f0#12)).toNat + 8 ≤ 0x80003164
      ∨ 0x80003fe0 ≤ (v2 + sign_extend (m := 64) (0x0f0#12)).toNat)
    (hcf8 : (v2 + sign_extend (m := 64) (0x0f8#12)).toNat + 8 ≤ 0x80003164
      ∨ 0x80003fe0 ≤ (v2 + sign_extend (m := 64) (0x0f8#12)).toNat)
    (hc100 : (v2 + sign_extend (m := 64) (0x100#12)).toNat + 8 ≤ 0x80003164
      ∨ 0x80003fe0 ≤ (v2 + sign_extend (m := 64) (0x100#12)).toNat)
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
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 13⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 σ.mem
          (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D1)
          (v2 + sign_extend (m := 64) (0x100#12)).toNat D2)
          (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D3)
          (v2 + sign_extend (m := 64) (0x0f8#12)).toNat D4)
          (v2 + sign_extend (m := 64) (0x100#12)).toNat D5 ∧
      σ'.regs.get? Register.PC = some (0x80003868#64) ∧
      σ'.regs.get? Register.x17 = some Wr ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x19 = some Wl ∧
      σ'.regs.get? Register.x12 = some v12 ∧
      (∃ w, σ'.regs.get? Register.x13 = some w) ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  have pushCode : ∀ (m : Mem) (A : Nat) (dd : BitVec (8 * 8)),
      (A + 8 ≤ 0x80003164 ∨ 0x80003fe0 ≤ A) → Vsa.Sim.Code.Eval_exprLoaded m →
      Vsa.Sim.Code.Eval_exprLoaded (writeMap8 m A dd) :=
    fun m A dd hdis hc => loaded_eval_expr_agreeP m (writeMap8 m A dd)
      (fun a _ha => (getElem_writeMap8_disjoint m A a dd (by rcases hdis with h | h <;> omega)).symm) hc
  have hLA : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat]? = some a0 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 1]? = some a1 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 2]? = some a2 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 3]? = some a3 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 4]? = some a4 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 5]? = some a5 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 6]? = some a6 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 7]? = some a7 :=
    ⟨la_p0, la_p1, la_p2, la_p3, la_p4, la_p5, la_p6, la_p7⟩
  have hLB : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat]? = some b0 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 1]? = some b1 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 2]? = some b2 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 3]? = some b3 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 4]? = some b4 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 5]? = some b5 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 6]? = some b6 ∧
      σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 7]? = some b7 :=
    ⟨lb_p0, lb_p1, lb_p2, lb_p3, lb_p4, lb_p5, lb_p6, lb_p7⟩
  -- ── S1: ld/ld/li/sd/sd + bne NOT taken → 0x8000384c ─────────────────────────
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt mulArmS1 σ i u (0x80003834#64) vm
      [(2, v2), (16, (2#64 : BitVec 64))]
      [[a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7]]
      hG hpc hmi ⟨hx2, hx16, trivial⟩
      (show KeysOK [2, 16] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨la_lo, la_hi, la_ht, la_al⟩,
            lpin_of_present hLA.1, lpin_of_present hLA.2.1, lpin_of_present hLA.2.2.1, lpin_of_present hLA.2.2.2.1,
            lpin_of_present hLA.2.2.2.2.1, lpin_of_present hLA.2.2.2.2.2.1, lpin_of_present hLA.2.2.2.2.2.2.1, lpin_of_present hLA.2.2.2.2.2.2.2⟩
        · exact ⟨⟨lb_lo, lb_hi, lb_ht, lb_al⟩,
            lpin_of_present hLB.1, lpin_of_present hLB.2.1, lpin_of_present hLB.2.2.1, lpin_of_present hLB.2.2.2.1,
            lpin_of_present hLB.2.2.2.2.1, lpin_of_present hLB.2.2.2.2.2.1, lpin_of_present hLB.2.2.2.2.2.2.1, lpin_of_present hLB.2.2.2.2.2.2.2⟩
        · exact ⟨t0lo, t0hi, t0win, t0al⟩
        · exact ⟨t2lo, t2hi, t2win, t2al⟩
        · show guardB bop.BNE (2#64)
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x002#12)) = false
          decide)
      (show BBlockOK (0x80003834#64) [2, 16] mulArmS1 by decide) hi
  rw [show endPCB (0x80003834#64) mulArmS1
        [(2, v2), (16, (2#64 : BitVec 64))]
        [[a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7]]
        = (0x8000384c#64 : BitVec 64) from by
          show BitVec.addInt (0x80003848#64) 4 = (0x8000384c#64 : BitVec 64)
          decide] at hpc1
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 := (hframe1 Register.x2 (by decide) (by decide)).trans hx2
  have hx9_1 : σ1.regs.get? Register.x9 = some sret := (hframe1 Register.x9 (by decide) (by decide)).trans hx9
  have hx10_1 : σ1.regs.get? Register.x10 = some (2#64) := (hframe1 Register.x10 (by decide) (by decide)).trans hx10
  have hx16_1 : σ1.regs.get? Register.x16 = some (2#64) := (hframe1 Register.x16 (by decide) (by decide)).trans hx16
  have hx17_1 : σ1.regs.get? Register.x17 = some Wr := (hframe1 Register.x17 (by decide) (by decide)).trans hx17
  have hx19_1 : σ1.regs.get? Register.x19 = some Wl := (hframe1 Register.x19 (by decide) (by decide)).trans hx19
  have hx12_1 : σ1.regs.get? Register.x12 = some v12 := (hframe1 Register.x12 (by decide) (by decide)).trans hx12
  obtain ⟨vm1, hmi1'⟩ := hmi1
  have hmem1W0 : σ1.mem = writeLog σ.mem (wlogM mulArmS1.body
      [(2, v2), (16, (2#64 : BitVec 64))]
      [[a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7]]) := hmem1
  obtain ⟨D1, D2, hmem1W⟩ : ∃ D1 D2 : BitVec (8 * 8), σ1.mem
      = writeMap8 (writeMap8 σ.mem (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D1)
          (v2 + sign_extend (m := 64) (0x100#12)).toNat D2 := ⟨_, _, hmem1W0⟩
  have hcode1 : Vsa.Sim.Code.Eval_exprLoaded σ1.mem := by
    rw [hmem1W]; exact pushCode _ _ _ hc100 (pushCode _ _ _ hcf0 hmem)
  have hbridge : ∀ k : Nat, k < (v2 + sign_extend (m := 64) (0x0f0#12)).toNat →
      σ1.mem[k]? = σ.mem[k]? := by
    intro k hk
    rw [hmem1W,
      getElem_writeMap8_disjoint (writeMap8 σ.mem (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D1)
        (v2 + sign_extend (m := 64) (0x100#12)).toNat k D2 (Or.inl (by rw [hnf0] at hk; rw [hn100]; omega)),
      getElem_writeMap8_disjoint σ.mem (v2 + sign_extend (m := 64) (0x0f0#12)).toNat k D1 (Or.inl hk)]
  have hLC : σ1.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat]? = some c0 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 1]? = some c1 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 2]? = some c2 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 3]? = some c3 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 4]? = some c4 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 5]? = some c5 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 6]? = some c6 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 7]? = some c7 :=
    ⟨(hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p0,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p1,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p2,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p3,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p4,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p5,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p6,
     (hbridge _ (by rw [hn90, hnf0]; omega)).trans lc_p7⟩
  have hLD : σ1.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat]? = some d0 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 1]? = some d1 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 2]? = some d2 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 3]? = some d3 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 4]? = some d4 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 5]? = some d5 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 6]? = some d6 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 7]? = some d7 :=
    ⟨(hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p0,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p1,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p2,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p3,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p4,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p5,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p6,
     (hbridge _ (by rw [hn98, hnf0]; omega)).trans ld_p7⟩
  have hLE : σ1.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat]? = some e0 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 1]? = some e1 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 2]? = some e2 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 3]? = some e3 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 4]? = some e4 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 5]? = some e5 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 6]? = some e6 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x0a0#12)).toNat + 7]? = some e7 :=
    ⟨(hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p0,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p1,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p2,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p3,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p4,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p5,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p6,
     (hbridge _ (by rw [hna0, hnf0]; omega)).trans le_p7⟩
  -- ── S2: ld/ld/ld/sd/sd/sd + bne NOT taken → 0x80003868 ──────────────────────
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt mulArmS2 σ1 i1 (u + blenB mulArmS1) (0x8000384c#64) vm1
      [(2, v2), (10, (2#64 : BitVec 64)), (16, (2#64 : BitVec 64))]
      [[c0, c1, c2, c3, c4, c5, c6, c7], [d0, d1, d2, d3, d4, d5, d6, d7],
       [e0, e1, e2, e3, e4, e5, e6, e7]]
      hG1 hpc1 hmi1' ⟨hx2_1, hx10_1, hx16_1, trivial⟩
      (show KeysOK [2, 10, 16] by decide)
      (by
        block_facts hcode1 with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨lc_lo, lc_hi, lc_ht, lc_al⟩,
            lpin_of_present hLC.1, lpin_of_present hLC.2.1, lpin_of_present hLC.2.2.1, lpin_of_present hLC.2.2.2.1,
            lpin_of_present hLC.2.2.2.2.1, lpin_of_present hLC.2.2.2.2.2.1, lpin_of_present hLC.2.2.2.2.2.2.1, lpin_of_present hLC.2.2.2.2.2.2.2⟩
        · exact ⟨⟨ld_lo, ld_hi, ld_ht, ld_al⟩,
            lpin_of_present hLD.1, lpin_of_present hLD.2.1, lpin_of_present hLD.2.2.1, lpin_of_present hLD.2.2.2.1,
            lpin_of_present hLD.2.2.2.2.1, lpin_of_present hLD.2.2.2.2.2.1, lpin_of_present hLD.2.2.2.2.2.2.1, lpin_of_present hLD.2.2.2.2.2.2.2⟩
        · exact ⟨⟨le_lo, le_hi, le_ht, le_al⟩,
            lpin_of_present hLE.1, lpin_of_present hLE.2.1, lpin_of_present hLE.2.2.1, lpin_of_present hLE.2.2.2.1,
            lpin_of_present hLE.2.2.2.2.1, lpin_of_present hLE.2.2.2.2.2.1, lpin_of_present hLE.2.2.2.2.2.2.1, lpin_of_present hLE.2.2.2.2.2.2.2⟩
        · exact ⟨t0lo, t0hi, t0win, t0al⟩
        · exact ⟨t1lo, t1hi, t1win, t1al⟩
        · exact ⟨t2lo, t2hi, t2win, t2al⟩
        · show guardB bop.BNE (2#64) (2#64) = false
          decide)
      (show BBlockOK (0x8000384c#64) [2, 10, 16] mulArmS2 by decide) hi1
  rw [show endPCB (0x8000384c#64) mulArmS2
        [(2, v2), (10, (2#64 : BitVec 64)), (16, (2#64 : BitVec 64))]
        [[c0, c1, c2, c3, c4, c5, c6, c7], [d0, d1, d2, d3, d4, d5, d6, d7],
         [e0, e1, e2, e3, e4, e5, e6, e7]]
        = (0x80003868#64 : BitVec 64) from by
          show BitVec.addInt (0x80003864#64) 4 = (0x80003868#64 : BitVec 64)
          decide] at hpc2
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 := (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  have hx9_2 : σ2.regs.get? Register.x9 = some sret := (hframe2 Register.x9 (by decide) (by decide)).trans hx9_1
  have hx17_2 : σ2.regs.get? Register.x17 = some Wr := (hframe2 Register.x17 (by decide) (by decide)).trans hx17_1
  have hx19_2 : σ2.regs.get? Register.x19 = some Wl := (hframe2 Register.x19 (by decide) (by decide)).trans hx19_1
  have hx12_2 : σ2.regs.get? Register.x12 = some v12 := (hframe2 Register.x12 (by decide) (by decide)).trans hx12_1
  have hx13_2 : ∃ w, σ2.regs.get? Register.x13 = some w := ⟨_, block_reg hGH2 13⟩
  have hmem2W0 : σ2.mem = writeLog σ1.mem (wlogM mulArmS2.body
      [(2, v2), (10, (2#64 : BitVec 64)), (16, (2#64 : BitVec 64))]
      [[c0, c1, c2, c3, c4, c5, c6, c7], [d0, d1, d2, d3, d4, d5, d6, d7],
       [e0, e1, e2, e3, e4, e5, e6, e7]]) := hmem2
  obtain ⟨D3, D4, D5, hmem2W⟩ : ∃ D3 D4 D5 : BitVec (8 * 8), σ2.mem
      = writeMap8 (writeMap8 (writeMap8 σ1.mem (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D3)
          (v2 + sign_extend (m := 64) (0x0f8#12)).toNat D4)
          (v2 + sign_extend (m := 64) (0x100#12)).toNat D5 := ⟨_, _, _, hmem2W0⟩
  have hx2_3 : σ2.regs.get? Register.x2 = some v2 := hx2_2
  have hframeC : ∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
      σ2.regs.get? R = σ.regs.get? R := by
    intro R hR _he8
    have hab := hR.1
    exact ((hframe2 R (abiNoise_noiseRegs hR) (by block_frame_wr [14, 13, 15])).trans
        (hframe1 R (abiNoise_noiseRegs hR) (by block_frame_wr [14, 15, 13])))
  have hmemW : σ2.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 σ.mem
      (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D1)
      (v2 + sign_extend (m := 64) (0x100#12)).toNat D2)
      (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D3)
      (v2 + sign_extend (m := 64) (0x0f8#12)).toNat D4)
      (v2 + sign_extend (m := 64) (0x100#12)).toNat D5 := by
    rw [hmem2W, hmem1W]
  have hout2e : σ2.sailOutput = σ.sailOutput := hout2.trans hout1
  refine ⟨σ2, i2, D1, D2, D3, D4, D5, ?_, hi2, hG2, hmemW, hpc2, hx17_2, hx2_3, hx9_2, hx19_2,
    hx12_2, hx13_2, hout2e, hmi2, hframeC⟩
  have hlen : u + blenB mulArmS1 + blenB mulArmS2 = u + 13 := by
    rw [show blenB mulArmS1 = 6 from by decide, show blenB mulArmS2 = 7 from by decide]
  rw [← hlen]
  exact hsteps1.trans hsteps2

end Vsa.Sim
