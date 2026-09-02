import Vsa.Sim.EvalLtChain

/-!
# `EvalGeChain` — the `.ge` operator branch tail (0x80003698 → 0x800036c0)

Clone-by-reuse of `.lt`.  The comparison operators share the arm @0x80003628 and
the operator-fixup ladder @0x800036a4..0x800036c0.  `.ge` (token 23) FALLS THROUGH
all three comparison `beq`s — `li 21`/beq@0x36a8 (23≠21), `li 22`/beq@0x36b0
(23≠22), `li 20`/beq@0x36b8 (23≠20) — into the `not a1,a1` (`xori a1,a1,-1`)
@0x800036bc, then the SHARED `srli a1,a1,0x3f` sign-bit fixup @0x800036c0.

`.lt`, by contrast, TAKES the third `beq@0x36b8` (20 = 20) into 0x800036c0,
skipping the `not`.  So `.ge` is one instruction longer than `.lt`: its ladder tail
runs `gtLadB5` (beq@0x36a8 NOT taken) ≫ `ltLadB6` (beq@0x36b0 NOT taken) ≫
`geLadB7` (beq@0x36b8 NOT taken → 0x36bc) ≫ `geLadNot` (`not a1,a1` → 0x36c0),
producing `x11 = cmpScalar Wl Wr ^^^ sign_extend (m := 64) (0xfff#12)` (the
bitwise complement of the spaceship scalar).  The shared `srli` fixup (`ltLadG`)
then extracts its sign bit.

Reuses `evalGtChain_run`-family block defs (`gtLadB5`, `ltLadB6`, `ltLadG`)
verbatim; only `geLadB7`/`geLadNot`/`evalGeLadderEF` are new.

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

/-! ## `GeSlotPinned` — the operator jump-table slot pin for `.ge`

`.ge` (token 23, index 12) → slot bytes `a4 96 fe ff` @ `opTableBase + 48`
(address `0x80019fb4`), target `opTableBase + (Int32)0xfffe96a4 = 0x80003628`
(the SHARED comparison arm).  Analogous to `LtSlotPinned` (index 9, +36). -/
def GeSlotPinned (m : Mem) : Prop :=
  m[(opTableBase + 48 : Nat)]? = some (0xa4 : BitVec 8) ∧
  m[(opTableBase + 49 : Nat)]? = some (0x96 : BitVec 8) ∧
  m[(opTableBase + 50 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(opTableBase + 51 : Nat)]? = some (0xff : BitVec 8)

/-- `GeSlotPinned` survives a `writeMap8` disjoint from `[opTableBase+48, +4)`. -/
theorem geSlot_writeMap8 (m : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ opTableBase + 48 ∨ opTableBase + 56 ≤ a8) (h : GeSlotPinned m) :
    GeSlotPinned (writeMap8 m a8 d) := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint m a8 _ d (by omega)]; assumption)

/-- Ge op-token load bytes (`23 = [0x17,0,0,0]`), concrete for the `bltu` guard.
Clone of `ltLds1`/`gtLds1` with token 23. -/
def geLds1 (b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8) :
    List (List (BitVec 8)) :=
  [[0x17#8, 0x00#8, 0x00#8, 0x00#8], [b0, b1, b2, b3], [c0, c1, c2, c3],
   [d0, d1, d2, d3, d4, d5, d6, d7]]

/-- The opening 16-instruction run `0x8000351c → 0x80003628`, clone of
`evalLtChain_run` for token 23 (slot @ `opTableBase+48` = `0x80019fb4`,
kind-ladder x15=12, CSWTCH slot).  Reuses `gtChainB1/B2a/B2b` verbatim. -/
theorem evalGeChain_run (σ : MState) (i u : Nat) (vm v2 v8 sret Wl : BitVec 64)
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
    (a_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some (0x17#8))
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
    (hSlot : GeSlotPinned σ.mem)
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
      σ'.regs.get? Register.x12 = some (23#64) ∧
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
      [(8, v8), (2, v2)] (geLds1 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
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
              (bytesVal MKind.lw [0x17#8, 0x00#8, 0x00#8, 0x00#8]
                + sign_extend (m := 64) (0xff5#12)) 31 0)) = false
          decide)
      (show BBlockOK (0x8000351c#64) [8, 2] gtChainB1 by decide) hi
  have hmem1e : σ1.mem = σ.mem := hmem1
  rw [show endPCB (0x8000351c#64) gtChainB1 [(8, v8), (2, v2)]
        (geLds1 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
        = (0x80003538#64 : BitVec 64) from by
          show BitVec.addInt (0x80003534#64) 4 = (0x80003538#64 : BitVec 64)
          decide] at hpc1
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 := block_reg hGH1 2
  have hx15v : (sign_extend (m := 64) (Sail.BitVec.extractLsb
      (bytesVal MKind.lw [0x17#8, 0x00#8, 0x00#8, 0x00#8]
        + sign_extend (m := 64) (0xff5#12)) 31 0) : BitVec 64) = 12#64 := by decide
  have hx15_1 : σ1.regs.get? Register.x15 = some (12#64) :=
    hx15v ▸ (block_reg hGH1 15 : σ1.regs.get? Register.x15
      = some (sign_extend (m := 64) (Sail.BitVec.extractLsb
          (bytesVal MKind.lw [0x17#8, 0x00#8, 0x00#8, 0x00#8]
            + sign_extend (m := 64) (0xff5#12)) 31 0)))
  have hx12v : (bytesVal MKind.lw [0x17#8, 0x00#8, 0x00#8, 0x00#8] : BitVec 64) = 23#64 := by decide
  have hx12_1 : σ1.regs.get? Register.x12 = some (23#64) :=
    hx12v ▸ (block_reg hGH1 12 : σ1.regs.get? Register.x12
      = some (bytesVal MKind.lw [0x17#8, 0x00#8, 0x00#8, 0x00#8]))
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
  -- ── Block 2a (ALU) → x15=0x80019fb4, x14=0x80019f84 (fall-through to 0x354c) ──
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt gtChainB2a σ1 i1 (u + blenB gtChainB1) (0x80003538#64) vm1
      [(15, (12#64 : BitVec 64))] []
      hG1 hpc1 hmi1' ⟨hx15_1, trivial⟩
      (show KeysOK [15] by decide)
      (by block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
            with "Vsa.Sim.Code.eval_expr_at_")
      (show BBlockOK (0x80003538#64) [15] gtChainB2a by decide) hi1
  have hmem2e : σ2.mem = σ.mem := by rw [hmem2]; exact hmem1e
  rw [show endPCB (0x80003538#64) gtChainB2a [(15, (12#64 : BitVec 64))] []
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
  have hx15v : (shift_bits_right (shift_bits_left (12#64 : BitVec 64)
        (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
      + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
          + sign_extend (m := 64) (0xa44#12))) = 0x80019fb4#64 := by decide
  have hx15_2 : σ2.regs.get? Register.x15 = some (0x80019fb4#64) :=
    hx15v ▸ (block_reg hGH2 15 : σ2.regs.get? Register.x15
      = some (shift_bits_right (shift_bits_left (12#64 : BitVec 64)
            (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
          + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
              + sign_extend (m := 64) (0xa44#12))))
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 :=
    (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  have hx12_2 : σ2.regs.get? Register.x12 = some (23#64) :=
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
  have hSlot2 : σ2.mem[(0x80019fb4#64 : BitVec 64).toNat]? = some (0xa4#8) ∧
      σ2.mem[(0x80019fb4#64 : BitVec 64).toNat + 1]? = some (0x96#8) ∧
      σ2.mem[(0x80019fb4#64 : BitVec 64).toNat + 2]? = some (0xfe#8) ∧
      σ2.mem[(0x80019fb4#64 : BitVec 64).toNat + 3]? = some (0xff#8) := by
    rw [hmem2e]; exact ⟨sp0, sp1, sp2, sp3⟩
  have sLo : 0x80000000 ≤ (0x80019fb4#64 : BitVec 64).toNat := by decide
  have sHi : (0x80019fb4#64 : BitVec 64).toNat + 4 ≤ 0x100000000 := by decide
  have sHt : (0x80019fb4#64 : BitVec 64).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (0x80019fb4#64 : BitVec 64).toNat := by decide
  have sAl : (0x80019fb4#64 : BitVec 64).toNat % 4 = 0 := by decide
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
      [(15, (0x80019fb4#64 : BitVec 64)), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
      (gtLds2 k0 k1 k2 k3 k4 k5 k6 k7)
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
        · show (BitVec.update ((bytesVal MKind.lw [0xa4#8, 0x96#8, 0xfe#8, 0xff#8]
              + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
          decide)
      (show BBlockOK (0x8000354c#64) [15, 2, 14] gtChainB2b by decide) hi2
  rw [show endPCB (0x8000354c#64) gtChainB2b
        [(15, (0x80019fb4#64 : BitVec 64)), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
        (gtLds2 k0 k1 k2 k3 k4 k5 k6 k7) = (0x80003628#64 : BitVec 64) from by
          show BitVec.update ((bytesVal MKind.lw [0xa4#8, 0x96#8, 0xfe#8, 0xff#8]
              + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1 = (0x80003628#64 : BitVec 64)
          decide] at hpc3
  have hx16_3 : σ3.regs.get? Register.x16 = some (2#64) :=
    hk ▸ (block_reg hGH3 16 : σ3.regs.get? Register.x16
      = some (bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7]))
  have hx12_3 : σ3.regs.get? Register.x12 = some (23#64) :=
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

/-- GE `LB2` variant: `addiw/li/auipc/addi` + `beq@0x80003648` TAKEN (token 23 →
`x15 = 23-20 = 3 = x14`), jumping to 0x80003664 (SKIPS the CSWTCH.25 slot block).
Same body as `gtLadB2`; only the guard bit flips `false → true`. -/
def geLadB2 : BBlock :=
  { body := [mkLine 0x80003638#64 0xfec6079b#32,   -- addiw x15,x12,-20
             mkLine 0x8000363c#64 0x00300713#32,   -- addi  x14,x0,3
             mkLine 0x80003640#64 0x00016697#32,   -- auipc x13,0x16 (dead)
             mkLine 0x80003644#64 0xd4068693#32],  -- addi  x13,x13,-704 (dead)
    term := some ⟨0x80003648#64, 0x00e78e63#32, 0x63#8, 0x8e#8, 0xe7#8, 0x00#8,
      .br bop.BEQ true, 15, 14, 0x001c#13, 0#21, 0#12⟩ }

/-- GE kind-ladder prefix `0x80003628 → 0x80003664` (7 steps): `gtLadB1` (addi +
bnez TAKEN → 0x3638) ≫ `geLadB2` (beq@0x3648 TAKEN → 0x3664).  Reuses `gtLadB1`
verbatim; the beq-taken jump skips lt's CSWTCH.25 dispatch. -/
theorem evalGeLadderAB (σ : MState) (i u : Nat) (vm v2 sret Wr Wl : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003628#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx10 : σ.regs.get? Register.x10 = some (2#64))
    (hx12 : σ.regs.get? Register.x12 = some (23#64))
    (hx16 : σ.regs.get? Register.x16 = some (2#64))
    (hx17 : σ.regs.get? Register.x17 = some Wr)
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 7⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some (0x80003664#64) ∧
      σ'.regs.get? Register.x12 = some (23#64) ∧
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
  -- ── LB1: addi + bnez TAKEN → 0x80003638 (reuse gtLadB1) ─────────────────────
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
  have hx12_1 : σ1.regs.get? Register.x12 = some (23#64) :=
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
  -- ── LB2: addiw/li/auipc/addi + beq@0x3648 TAKEN → 0x80003664 ────────────────
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt geLadB2 σ1 i1 (u + blenB gtLadB1) (0x80003638#64) vm1
      [(12, (23#64 : BitVec 64))] []
      hG1 hpc1 hmi1' ⟨hx12_1, trivial⟩
      (show KeysOK [12] by decide)
      (by
        block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        -- beq (x15 = 23-20 = 3) (x14 = 3) = true
        · show guardB bop.BEQ
            (sign_extend (m := 64) (Sail.BitVec.extractLsb
              ((23#64 : BitVec 64) + sign_extend (m := 64) (0xfec#12)) 31 0))
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x003#12)) = true
          decide)
      (show BBlockOK (0x80003638#64) [12] geLadB2 by decide) hi1
  rw [show endPCB (0x80003638#64) geLadB2 [(12, (23#64 : BitVec 64))] []
        = (0x80003664#64 : BitVec 64) from by
          show (0x80003648#64 : BitVec 64) + sign_extend (m := 64) (0x001c#13)
            = (0x80003664#64 : BitVec 64)
          decide] at hpc2
  have hx12_2 : σ2.regs.get? Register.x12 = some (23#64) :=
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
  have hmem2e : σ2.mem = σ.mem := by rw [hmem2]; exact hmem1e
  have hout2e : σ2.sailOutput = σ.sailOutput := hout2.trans hout1
  refine ⟨σ2, i2, ?_, hi2, hG2, hpc2, hx12_2, hx2_2, hx10_2, hx16_2, hx9_2, hx17_2, hx19_2,
    hmem2e, hout2e, hmi2, hframeC⟩
  have hlen : u + blenB gtLadB1 + blenB geLadB2 = u + 7 := by
    rw [show blenB gtLadB1 = 2 from by decide, show blenB geLadB2 = 5 from by decide]
  rw [← hlen]
  exact hsteps1.trans hsteps2

/-- GE `LB3c` `0x80003664 → 0x8000367c` (6 steps): the shared block ge lands on
after the beq — `ld x14,0x78(x2); ld x15,0x88(x2); li x11,2; sd x14,0xf0(x2);
sd x15,0x100(x2); bne x16,x11` NOT taken (x16 = 2 = x11 → fall to 0x367c).
This is `gtLadB3b` minus its leading CSWTCH.25 slot load `ld x13,0(x15)`. -/
def geLadB3c : BBlock :=
  { body :=
      [mkLine 0x80003664#64 0x07813703#32,   -- ld   x14,0x78(x2)
       mkLine 0x80003668#64 0x08813783#32,   -- ld   x15,0x88(x2)
       mkLine 0x8000366c#64 0x00200593#32,   -- addi x11,x0,2
       mkLine 0x80003670#64 0x0ee13823#32,   -- sd   x14,0xf0(x2)
       mkLine 0x80003674#64 0x10f13023#32],  -- sd   x15,0x100(x2)
    term := some ⟨0x80003678#64, 0x02b812e3#32, 0xe3#8, 0x12#8, 0xb8#8, 0x02#8,
      .br bop.BNE false, 16, 11, 0x0824#13, 0#21, 0#12⟩ }

/-- GE `LB3c` `0x80003664 → 0x8000367c` (6 steps): two dead loads @ v2+0x78/0x88,
two scratch stores @ v2+0xf0/0x100, then `bne` NOT taken.  `x10/x12/x16/x9/x17/x19`
pass through; memory outcome = two scratch stores (`writeMap8²`). -/
theorem evalGeLadderC (σ : MState) (i u : Nat) (vm v2 sret Wr Wl : BitVec 64)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003664#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx16 : σ.regs.get? Register.x16 = some (2#64))
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx10 : σ.regs.get? Register.x10 = some (2#64))
    (hx12 : σ.regs.get? Register.x12 = some (23#64))
    (hx17 : σ.regs.get? Register.x17 = some Wr)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
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
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 6⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (writeMap8 σ.mem (v2 + sign_extend (m := 64) (0x0f0#12)).toNat D1)
        (v2 + sign_extend (m := 64) (0x100#12)).toNat D2 ∧
      σ'.regs.get? Register.PC = some (0x8000367c#64) ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x10 = some (2#64) ∧
      σ'.regs.get? Register.x12 = some (23#64) ∧
      σ'.regs.get? Register.x16 = some (2#64) ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x17 = some Wr ∧
      σ'.regs.get? Register.x19 = some Wl ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt geLadB3c σ i u (0x80003664#64) vm
      [(2, v2), (16, (2#64 : BitVec 64))]
      [[a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7]]
      hG hpc hmi ⟨hx2, hx16, trivial⟩
      (show KeysOK [2, 16] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨a_lo, a_hi, a_ht, a_al⟩, lpin_of_present a_p0, lpin_of_present a_p1, lpin_of_present a_p2, lpin_of_present a_p3, lpin_of_present a_p4, lpin_of_present a_p5, lpin_of_present a_p6, lpin_of_present a_p7⟩
        · exact ⟨⟨b_lo, b_hi, b_ht, b_al⟩, lpin_of_present b_p0, lpin_of_present b_p1, lpin_of_present b_p2, lpin_of_present b_p3, lpin_of_present b_p4, lpin_of_present b_p5, lpin_of_present b_p6, lpin_of_present b_p7⟩
        · exact ⟨t0lo, t0hi, t0win, t0al⟩
        · exact ⟨t1lo, t1hi, t1win, t1al⟩
        · show guardB bop.BNE (2#64)
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x002#12)) = false
          decide)
      (show BBlockOK (0x80003664#64) [2, 16] geLadB3c by decide) hi
  rw [show endPCB (0x80003664#64) geLadB3c
        [(2, v2), (16, (2#64 : BitVec 64))]
        [[a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7]]
        = (0x8000367c#64 : BitVec 64) from by
          show BitVec.addInt (0x80003678#64) 4 = (0x8000367c#64 : BitVec 64)
          decide] at hpc1
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 :=
    (hframe1 Register.x2 (by decide) (by decide)).trans hx2
  have hx10_1 : σ1.regs.get? Register.x10 = some (2#64) :=
    (hframe1 Register.x10 (by decide) (by decide)).trans hx10
  have hx12_1 : σ1.regs.get? Register.x12 = some (23#64) :=
    (hframe1 Register.x12 (by decide) (by decide)).trans hx12
  have hx16_1 : σ1.regs.get? Register.x16 = some (2#64) :=
    (hframe1 Register.x16 (by decide) (by decide)).trans hx16
  have hx9_1 : σ1.regs.get? Register.x9 = some sret :=
    (hframe1 Register.x9 (by decide) (by decide)).trans hx9
  have hx17_1 : σ1.regs.get? Register.x17 = some Wr :=
    (hframe1 Register.x17 (by decide) (by decide)).trans hx17
  have hx19_1 : σ1.regs.get? Register.x19 = some Wl :=
    (hframe1 Register.x19 (by decide) (by decide)).trans hx19
  have hframeC : ∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
      σ1.regs.get? R = σ.regs.get? R := by
    intro R hR _he8
    have hab := hR.1
    exact hframe1 R (abiNoise_noiseRegs hR) (by block_frame_wr [14, 15, 11])
  have hmemW : σ1.mem = writeLog σ.mem (wlogM geLadB3c.body
      [(2, v2), (16, (2#64 : BitVec 64))]
      [[a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7]]) := hmem1
  exact ⟨σ1, i1, _, _, hsteps1, hi1, hG1, hmemW, hpc1, hx2_1,
    hx10_1, hx12_1, hx16_1, hx9_1, hx17_1, hx19_1, hout1, hmi1, hframeC⟩

/-- GE `LD` `0x8000367c → 0x80003698` (7 steps): the operand-load/store block
(`gtLadB4`, token-agnostic).  Token `x12 = 23` threads through unchanged.  Exact
clone of `evalLtLadderD` with the pinned token `20 → 23`. -/
theorem evalGeLadderD (σ : MState) (i u : Nat) (vm v2 sret Wr Wl : BitVec 64)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000367c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx10 : σ.regs.get? Register.x10 = some (2#64))
    (hx16 : σ.regs.get? Register.x16 = some (2#64))
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx12 : σ.regs.get? Register.x12 = some (23#64))
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
      σ'.regs.get? Register.x12 = some (23#64) ∧
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
        · exact ⟨⟨a_lo, a_hi, a_ht, a_al⟩, lpin_of_present a_p0, lpin_of_present a_p1, lpin_of_present a_p2, lpin_of_present a_p3, lpin_of_present a_p4, lpin_of_present a_p5, lpin_of_present a_p6, lpin_of_present a_p7⟩
        · exact ⟨⟨b_lo, b_hi, b_ht, b_al⟩, lpin_of_present b_p0, lpin_of_present b_p1, lpin_of_present b_p2, lpin_of_present b_p3, lpin_of_present b_p4, lpin_of_present b_p5, lpin_of_present b_p6, lpin_of_present b_p7⟩
        · exact ⟨⟨c_lo, c_hi, c_ht, c_al⟩, lpin_of_present c_p0, lpin_of_present c_p1, lpin_of_present c_p2, lpin_of_present c_p3, lpin_of_present c_p4, lpin_of_present c_p5, lpin_of_present c_p6, lpin_of_present c_p7⟩
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
  have hx12_1 : σ1.regs.get? Register.x12 = some (23#64) :=
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

/-- GE `LB7` `0x800036b4 → 0x800036bc` (2 steps): `li x15,0x14` + `beq@0x36b8`
NOT taken (token 23 ≠ 20), so it falls through to 0x800036bc.  Identical body to
`ltLadB7`; only the guard bit flips `true → false` and the endPC is pc+4. -/
def geLadB7 : BBlock :=
  { body := [mkLine 0x800036b4#64 0x01400793#32],   -- li x15,0x14
    term := some ⟨0x800036b8#64, 0x00f60463#32, 0x63#8, 0x04#8, 0xf6#8, 0x00#8,
      .br bop.BEQ false, 12, 15, 0x0008#13, 0#21, 0#12⟩ }

/-- GE `LBnot` `0x800036bc → 0x800036c0` (1 step): `not x11,x11` (`xori x11,x11,-1`),
straight-line, no terminator.  Complements the spaceship scalar. -/
def geLadNot : BBlock :=
  { body := [mkLine 0x800036bc#64 0xfff5c593#32],   -- not x11,x11 = xori x11,x11,-1
    term := none }

/-- GE `LB5+LB6+LB7+LBnot` `0x80003698 → 0x800036c0` (10 steps).  `x9 = sret`
passes through; `x11 = cmpScalar Wl Wr ^^^ sign_extend (m := 64) (0xfff#12)` (the
complemented scalar) survives the three-`beq` fall-through and the `not`. -/
theorem evalGeLadderEF (σ : MState) (i u : Nat) (vm Wr Wl sret v2 : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003698#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx17 : σ.regs.get? Register.x17 = some Wr)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hx12 : σ.regs.get? Register.x12 = some (23#64))
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 10⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      σ'.regs.get? Register.PC = some (0x800036c0#64) ∧
      σ'.regs.get? Register.x11
        = some (cmpScalar Wl Wr ^^^ sign_extend (m := 64) (0xfff#12)) ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x19 = some Wl ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  -- LB5: cmp + beq@0x36a8 NOT taken (23≠21) → 0x36ac (reuse gtLadB5)
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt gtLadB5 σ i u (0x80003698#64) vm
      [(17, Wr), (19, Wl), (12, (23#64 : BitVec 64))] []
      hG hpc hmi ⟨hx17, hx19, hx12, trivial⟩
      (show KeysOK [17, 19, 12] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · show guardB bop.BEQ (23#64)
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x015#12)) = false
          decide)
      (show BBlockOK (0x80003698#64) [17, 19, 12] gtLadB5 by decide) hi
  have hmem1e : σ1.mem = σ.mem := hmem1
  rw [show endPCB (0x80003698#64) gtLadB5
        [(17, Wr), (19, Wl), (12, (23#64 : BitVec 64))] []
        = (0x800036ac#64 : BitVec 64) from by
          show BitVec.addInt (0x800036a8#64) 4 = (0x800036ac#64 : BitVec 64)
          decide] at hpc1
  obtain ⟨vm1, hmi1'⟩ := hmi1
  have hx11_1 : σ1.regs.get? Register.x11 = some (cmpScalar Wl Wr) := block_reg hGH1 11
  have hx12_1 : σ1.regs.get? Register.x12 = some (23#64) :=
    (hframe1 Register.x12 (by decide) (by decide)).trans hx12
  have hx9_1 : σ1.regs.get? Register.x9 = some sret :=
    (hframe1 Register.x9 (by decide) (by decide)).trans hx9
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 :=
    (hframe1 Register.x2 (by decide) (by decide)).trans hx2
  have hx19_1 : σ1.regs.get? Register.x19 = some Wl :=
    (hframe1 Register.x19 (by decide) (by decide)).trans hx19
  -- LB6: li x15,22 + beq@0x36b0 NOT taken (23≠22) → 0x36b4 (reuse ltLadB6)
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt ltLadB6 σ1 i1 (u + blenB gtLadB5) (0x800036ac#64) vm1
      [(12, (23#64 : BitVec 64))] []
      hG1 hpc1 hmi1' ⟨hx12_1, trivial⟩
      (show KeysOK [12] by decide)
      (by
        block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        · show guardB bop.BEQ (23#64)
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x016#12)) = false
          decide)
      (show BBlockOK (0x800036ac#64) [12] ltLadB6 by decide) hi1
  have hmem2e : σ2.mem = σ.mem := by rw [hmem2]; exact hmem1e
  rw [show endPCB (0x800036ac#64) ltLadB6 [(12, (23#64 : BitVec 64))] []
        = (0x800036b4#64 : BitVec 64) from by
          show BitVec.addInt (0x800036b0#64) 4 = (0x800036b4#64 : BitVec 64)
          decide] at hpc2
  obtain ⟨vm2, hmi2'⟩ := hmi2
  have hx11_2 : σ2.regs.get? Register.x11 = some (cmpScalar Wl Wr) :=
    (hframe2 Register.x11 (by decide) (by decide)).trans hx11_1
  have hx12_2 : σ2.regs.get? Register.x12 = some (23#64) :=
    (hframe2 Register.x12 (by decide) (by decide)).trans hx12_1
  have hx9_2 : σ2.regs.get? Register.x9 = some sret :=
    (hframe2 Register.x9 (by decide) (by decide)).trans hx9_1
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 :=
    (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  have hx19_2 : σ2.regs.get? Register.x19 = some Wl :=
    (hframe2 Register.x19 (by decide) (by decide)).trans hx19_1
  -- LB7: li x15,20 + beq@0x36b8 NOT taken (23≠20) → 0x36bc (fall-through)
  obtain ⟨σ3, i3, hsteps3, hi3, hG3, hmem3, hout3, hpc3, hmi3, hGH3, hframe3⟩ :=
    bblock_sound_bt geLadB7 σ2 i2 (u + blenB gtLadB5 + blenB ltLadB6) (0x800036b4#64) vm2
      [(12, (23#64 : BitVec 64))] []
      hG2 hpc2 hmi2' ⟨hx12_2, trivial⟩
      (show KeysOK [12] by decide)
      (by
        block_facts (hmem2e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ2.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        · show guardB bop.BEQ (23#64)
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x014#12)) = false
          decide)
      (show BBlockOK (0x800036b4#64) [12] geLadB7 by decide) hi2
  have hmem3e : σ3.mem = σ.mem := by rw [hmem3]; exact hmem2e
  rw [show endPCB (0x800036b4#64) geLadB7 [(12, (23#64 : BitVec 64))] []
        = (0x800036bc#64 : BitVec 64) from by
          show BitVec.addInt (0x800036b8#64) 4 = (0x800036bc#64 : BitVec 64)
          decide] at hpc3
  obtain ⟨vm3, hmi3'⟩ := hmi3
  have hx11_3 : σ3.regs.get? Register.x11 = some (cmpScalar Wl Wr) :=
    (hframe3 Register.x11 (by decide) (by decide)).trans hx11_2
  have hx9_3 : σ3.regs.get? Register.x9 = some sret :=
    (hframe3 Register.x9 (by decide) (by decide)).trans hx9_2
  have hx2_3 : σ3.regs.get? Register.x2 = some v2 :=
    (hframe3 Register.x2 (by decide) (by decide)).trans hx2_2
  have hx19_3 : σ3.regs.get? Register.x19 = some Wl :=
    (hframe3 Register.x19 (by decide) (by decide)).trans hx19_2
  -- LBnot: not x11,x11 (= xori x11,x11,-1) → 0x36c0 (complement the scalar)
  obtain ⟨σ4, i4, hsteps4, hi4, hG4, hmem4, hout4, hpc4, hmi4, hGH4, hframe4⟩ :=
    bblock_sound_bt geLadNot σ3 i3 (u + blenB gtLadB5 + blenB ltLadB6 + blenB geLadB7)
      (0x800036bc#64) vm3
      [(11, (cmpScalar Wl Wr))] []
      hG3 hpc3 hmi3' ⟨hx11_3, trivial⟩
      (show KeysOK [11] by decide)
      (by block_facts (hmem3e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ3.mem)
            with "Vsa.Sim.Code.eval_expr_at_")
      (show BBlockOK (0x800036bc#64) [11] geLadNot by decide) hi3
  have hmem4e : σ4.mem = σ.mem := by rw [hmem4]; exact hmem3e
  rw [show endPCB (0x800036bc#64) geLadNot [(11, (cmpScalar Wl Wr))] []
        = (0x800036c0#64 : BitVec 64) from by
          show endPCM (0x800036bc#64) geLadNot.body = (0x800036c0#64 : BitVec 64)
          decide] at hpc4
  have hx11_4 : σ4.regs.get? Register.x11
      = some (cmpScalar Wl Wr ^^^ sign_extend (m := 64) (0xfff#12)) := block_reg hGH4 11
  have hx9_4 : σ4.regs.get? Register.x9 = some sret :=
    (hframe4 Register.x9 (by decide) (by decide)).trans hx9_3
  have hx2_4 : σ4.regs.get? Register.x2 = some v2 :=
    (hframe4 Register.x2 (by decide) (by decide)).trans hx2_3
  have hx19_4 : σ4.regs.get? Register.x19 = some Wl :=
    (hframe4 Register.x19 (by decide) (by decide)).trans hx19_3
  have hframeC : ∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
      σ4.regs.get? R = σ.regs.get? R := by
    intro R hR _he8
    have hab := hR.1
    exact (((hframe4 R (abiNoise_noiseRegs hR) (by block_frame_wr [11])).trans
      (hframe3 R (abiNoise_noiseRegs hR) (by block_frame_wr [15]))).trans
      (hframe2 R (abiNoise_noiseRegs hR) (by block_frame_wr [15]))).trans
      (hframe1 R (abiNoise_noiseRegs hR) (by block_frame_wr [14, 15, 11, 15]))
  have hout4e : σ4.sailOutput = σ.sailOutput := hout4.trans (hout3.trans (hout2.trans hout1))
  refine ⟨σ4, i4, ?_, hi4, hG4, hmem4e, hpc4, hx11_4, hx9_4, hx2_4, hx19_4, hout4e, hmi4, hframeC⟩
  have hlen : u + blenB gtLadB5 + blenB ltLadB6 + blenB geLadB7 + blenB geLadNot = u + 10 := by
    rw [show blenB gtLadB5 = 5 from by decide, show blenB ltLadB6 = 2 from by decide,
      show blenB geLadB7 = 2 from by decide, show blenB geLadNot = 1 from by decide]
  rw [← hlen]
  exact ((hsteps1.trans hsteps2).trans hsteps3).trans hsteps4

end Vsa.Sim
