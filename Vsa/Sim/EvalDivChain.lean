import Vsa.Sim.EvalGeChain

/-!
# `EvalDivChain` — the operator-dispatch prefix routing to the `.div` arm (item 1)

The binary-op arm-entry linkage (`TwoSubReturn` @0x8000351c → the arm's `SegPre`)
runs a SHARED kind-dispatch prefix then a `jr` jump-table dispatch @0x80003558 that
routes the op token to its arm.  `evalGeChain_run` (`EvalGeChain.lean`) proves this
for `.ge` (0x8000351c → 0x80003628); `.lt`/`.le` clone it.  This file supplies the
`.div` analog of the load-bearing constant that clone needs: the operator
jump-table slot for `.div` and the proof that it routes the `jr` to the `.div` arm
`0x800037dc` (the entry of `divDispatch`/`divDispatchRow`, `DivDispatchSeg.lean`).

The routing formula (read off `evalGeChain_run`, `EvalGeChain.lean:179-288`):
* switch index = `token - 11` (`0x80003524: addi x15,x15,-11`);
* slot address = `opTableBase + index*4` (`opTableBase = 0x80019f84`,
  `EvalBinSim2.lean:77`); the slot holds a little-endian `Int32` RELATIVE offset;
* `jr` target = `opTableBase + (Int32) slot` (`0x8000354c: lw` + `add` + `jr`).

Cross-checked against the two landed entries:
* `.add` (token 11, index 0, slot `opTableBase+0`) = `04 99 fe ff` = `0xfffe9904`
  (`AddSlotPinned`, `EvalBinSim2.lean:80`);
* `.ge`  (token 23, index 12, slot `opTableBase+48`) = `a4 96 fe ff` = `0xfffe96a4`,
  target `0x80019f84 + 0xfffe96a4 = 0x80003628` (`GeSlotPinned`, `EvalGeChain.lean:44`).

`.div` (token 14, index 3, slot `opTableBase+12` = `0x80019f90`): the target is the
`.div` arm `0x800037dc`, so the slot Int32 = `0x800037dc - 0x80019f84 = 0xfffe9858`
= little-endian `58 98 fe ff`.  `divSlot_routes` below PROVES (by `decide`, the same
`jr`-target computation `evalGeChain_run` uses at `EvalGeChain.lean:286`) that these
bytes land the `jr` exactly at `0x800037dc` — the derivation is self-checking, not a
guess.

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

/-! ## `DivSlotPinned` — the operator jump-table slot pin for `.div`

`.div` (token 14, index 3) → slot bytes `58 98 fe ff` @ `opTableBase + 12`
(address `0x80019f90`), target `opTableBase + (Int32)0xfffe9858 = 0x800037dc`
(the `.div` arm entry).  Analogous to `GeSlotPinned` (index 12, +48). -/
def DivSlotPinned (m : Mem) : Prop :=
  m[(opTableBase + 12 : Nat)]? = some (0x58 : BitVec 8) ∧
  m[(opTableBase + 13 : Nat)]? = some (0x98 : BitVec 8) ∧
  m[(opTableBase + 14 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(opTableBase + 15 : Nat)]? = some (0xff : BitVec 8)

/-- `DivSlotPinned` survives a `writeMap8` disjoint from `[opTableBase+12, +4)`.
Clone of `geSlot_writeMap8` — lets the slot pin ride through the arm's stack
stores exactly as `GeSlotPinned` does. -/
theorem divSlot_writeMap8 (m : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ opTableBase + 12 ∨ opTableBase + 20 ≤ a8) (h : DivSlotPinned m) :
    DivSlotPinned (writeMap8 m a8 d) := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint m a8 _ d (by omega)]; assumption)

/-- **The `.div` slot routes the `jr` to the `.div` arm.**  With the derived slot
bytes `58 98 fe ff` and the table base `0x80019f84` (the `x14` value the prefix
computes), the `jr`-target computation `evalGeChain_run` performs at its terminator
(`EvalGeChain.lean:286`) lands exactly at `0x800037dc` — the entry PC of
`divDispatch`.  This `decide` is the proof that the derived slot bytes are correct:
had any byte been wrong, the target would not equal the `DivDispatchSeg` arm PC. -/
theorem divSlot_routes :
    (BitVec.update ((bytesVal MKind.lw [0x58#8, 0x98#8, 0xfe#8, 0xff#8]
        + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = (0x800037dc#64 : BitVec 64) := by decide

/-- `.div` op-token load bytes (`14 = [0x0e,0,0,0]`), concrete for the `bltu`
bounds guard.  Clone of `geLds1` with token 14 (vs ge's 23). -/
def divLds1 (b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8) :
    List (List (BitVec 8)) :=
  [[0x0e#8, 0x00#8, 0x00#8, 0x00#8], [b0, b1, b2, b3], [c0, c1, c2, c3],
   [d0, d1, d2, d3, d4, d5, d6, d7]]

/-- The `.div` block-2b load data: the slot word `58 98 fe ff` (routing to
`0x800037dc`) then the left-kind reload `[k0..k7]`.  Clone of `gtLds2`
(`EvalGtChain.lean:79`) with div's slot bytes as the head. -/
def divLds2 (k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 8) : List (List (BitVec 8)) :=
  [[0x58#8, 0x98#8, 0xfe#8, 0xff#8], [k0, k1, k2, k3, k4, k5, k6, k7]]

/-- The `.div` switch index is `3` (`token 14 - 11`), so the prefix computes
`x15 = 3` after the `addi x15,x15,-11`, then the slot address
`opTableBase + 3*4 = 0x80019f90`.  Verifies the index arithmetic the
`evalGeChain_run` clone will pin (cf. `EvalGeChain.lean:179-181`, where ge pins
`x15 = 12`). -/
theorem divIndex_val :
    (sign_extend (m := 64) (Sail.BitVec.extractLsb
      (bytesVal MKind.lw [0x0e#8, 0x00#8, 0x00#8, 0x00#8]
        + sign_extend (m := 64) (0xff5#12)) 31 0) : BitVec 64) = 3#64 := by decide

/-- The `.div` op token is `14` (`= [0x0e,0,0,0]`).  Clone of ge's `hx12v`
(`EvalGeChain.lean:187`, token 23). -/
theorem divToken_val :
    (bytesVal MKind.lw [0x0e#8, 0x00#8, 0x00#8, 0x00#8] : BitVec 64) = 14#64 := by decide

#print axioms DivSlotPinned
#print axioms divSlot_writeMap8
#print axioms divSlot_routes
#print axioms divIndex_val
#print axioms divToken_val

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- **The `.div` item-1 entry linkage: `0x8000351c → 0x800037dc`.**  Faithful clone
of `evalGeChain_run` (`EvalGeChain.lean:68`) reusing the arm-independent prefix
blocks `gtChainB1`/`gtChainB2a`/`gtChainB2b` VERBATIM (16 steps), swapping only the
op token (`23 → 14`), switch index (`12 → 3`), jump-table slot (`0x80019fb4 →
0x80019f90`, bytes `a4 96 fe ff → 58 98 fe ff`), and `jr` target (`0x80003628 →
0x800037dc`).  Lands the `divDispL` pins (`x16=2, x10=2, x2=v2, x9=sret, x17=Wr,
x19=Wl`) at the `.div` arm entry — the state `divDispatchRow`'s `SegPre` consumes. -/
theorem evalDivChain_run (σ : MState) (i u : Nat) (vm v2 v8 sret Wl : BitVec 64)
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
    (a_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some (0x0e#8))
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
    (hSlot : DivSlotPinned σ.mem)
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
      σ'.regs.get? Register.PC = some (0x800037dc#64) ∧
      σ'.regs.get? Register.x10 = some (2#64) ∧
      σ'.regs.get? Register.x12 = some (14#64) ∧
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
      [(8, v8), (2, v2)] (divLds1 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
      hG hpc hmi ⟨hx8, hx2, trivial⟩
      (show KeysOK [8, 2] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨a_lo, a_hi, a_ht, a_al⟩, a_p0, a_p1, a_p2, a_p3⟩
        · exact ⟨⟨b_lo, b_hi, b_ht, b_al⟩, b_p0, b_p1, b_p2, b_p3⟩
        · exact ⟨⟨c_lo, c_hi, c_ht, c_al⟩, c_p0, c_p1, c_p2, c_p3⟩
        · exact ⟨⟨d_lo, d_hi, d_ht, d_al⟩, d_p0, d_p1, d_p2, d_p3, d_p4, d_p5, d_p6, d_p7⟩
        · show guardB bop.BLTU
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x00c#12))
            (sign_extend (m := 64) (Sail.BitVec.extractLsb
              (bytesVal MKind.lw [0x0e#8, 0x00#8, 0x00#8, 0x00#8]
                + sign_extend (m := 64) (0xff5#12)) 31 0)) = false
          decide)
      (show BBlockOK (0x8000351c#64) [8, 2] gtChainB1 by decide) hi
  have hmem1e : σ1.mem = σ.mem := hmem1
  rw [show endPCB (0x8000351c#64) gtChainB1 [(8, v8), (2, v2)]
        (divLds1 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7)
        = (0x80003538#64 : BitVec 64) from by
          show BitVec.addInt (0x80003534#64) 4 = (0x80003538#64 : BitVec 64)
          decide] at hpc1
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 := block_reg hGH1 2
  have hx15v : (sign_extend (m := 64) (Sail.BitVec.extractLsb
      (bytesVal MKind.lw [0x0e#8, 0x00#8, 0x00#8, 0x00#8]
        + sign_extend (m := 64) (0xff5#12)) 31 0) : BitVec 64) = 3#64 := by decide
  have hx15_1 : σ1.regs.get? Register.x15 = some (3#64) :=
    hx15v ▸ (block_reg hGH1 15 : σ1.regs.get? Register.x15
      = some (sign_extend (m := 64) (Sail.BitVec.extractLsb
          (bytesVal MKind.lw [0x0e#8, 0x00#8, 0x00#8, 0x00#8]
            + sign_extend (m := 64) (0xff5#12)) 31 0)))
  have hx12v : (bytesVal MKind.lw [0x0e#8, 0x00#8, 0x00#8, 0x00#8] : BitVec 64) = 14#64 := by decide
  have hx12_1 : σ1.regs.get? Register.x12 = some (14#64) :=
    hx12v ▸ (block_reg hGH1 12 : σ1.regs.get? Register.x12
      = some (bytesVal MKind.lw [0x0e#8, 0x00#8, 0x00#8, 0x00#8]))
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
  -- ── Block 2a (ALU) → x15=0x80019f90, x14=0x80019f84 (fall-through to 0x354c) ──
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt gtChainB2a σ1 i1 (u + blenB gtChainB1) (0x80003538#64) vm1
      [(15, (3#64 : BitVec 64))] []
      hG1 hpc1 hmi1' ⟨hx15_1, trivial⟩
      (show KeysOK [15] by decide)
      (by block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
            with "Vsa.Sim.Code.eval_expr_at_")
      (show BBlockOK (0x80003538#64) [15] gtChainB2a by decide) hi1
  have hmem2e : σ2.mem = σ.mem := by rw [hmem2]; exact hmem1e
  rw [show endPCB (0x80003538#64) gtChainB2a [(15, (3#64 : BitVec 64))] []
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
  have hx15v : (shift_bits_right (shift_bits_left (3#64 : BitVec 64)
        (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
      + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
          + sign_extend (m := 64) (0xa44#12))) = 0x80019f90#64 := by decide
  have hx15_2 : σ2.regs.get? Register.x15 = some (0x80019f90#64) :=
    hx15v ▸ (block_reg hGH2 15 : σ2.regs.get? Register.x15
      = some (shift_bits_right (shift_bits_left (3#64 : BitVec 64)
            (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
          + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
              + sign_extend (m := 64) (0xa44#12))))
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 :=
    (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  have hx12_2 : σ2.regs.get? Register.x12 = some (14#64) :=
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
  have hSlot2 : σ2.mem[(0x80019f90#64 : BitVec 64).toNat]? = some (0x58#8) ∧
      σ2.mem[(0x80019f90#64 : BitVec 64).toNat + 1]? = some (0x98#8) ∧
      σ2.mem[(0x80019f90#64 : BitVec 64).toNat + 2]? = some (0xfe#8) ∧
      σ2.mem[(0x80019f90#64 : BitVec 64).toNat + 3]? = some (0xff#8) := by
    rw [hmem2e]; exact ⟨sp0, sp1, sp2, sp3⟩
  have sLo : 0x80000000 ≤ (0x80019f90#64 : BitVec 64).toNat := by decide
  have sHi : (0x80019f90#64 : BitVec 64).toNat + 4 ≤ 0x100000000 := by decide
  have sHt : (0x80019f90#64 : BitVec 64).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (0x80019f90#64 : BitVec 64).toNat := by decide
  have sAl : (0x80019f90#64 : BitVec 64).toNat % 4 = 0 := by decide
  have hKind2 : σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat]? = some k0 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some k1 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some k2 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some k3 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some k4 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some k5 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some k6 ∧
      σ2.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some k7 := by
    rw [hmem2e]; exact ⟨e_p0, e_p1, e_p2, e_p3, e_p4, e_p5, e_p6, e_p7⟩
  -- ── Block 2b (lw/ld/add + jr@0x3558) → 0x800037dc ─────────────────────────
  obtain ⟨σ3, i3, hsteps3, hi3, hG3, hmem3, hout3, hpc3, hmi3, hGH3, hframe3⟩ :=
    bblock_sound_bt gtChainB2b σ2 i2 (u + blenB gtChainB1 + blenB gtChainB2a) (0x8000354c#64) vm2
      [(15, (0x80019f90#64 : BitVec 64)), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
      (divLds2 k0 k1 k2 k3 k4 k5 k6 k7)
      hG2 hpc2 hmi2' ⟨hx15_2, hx2_2, hx14_2, trivial⟩
      (show KeysOK [15, 2, 14] by decide)
      (by
        block_facts (hmem2e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ2.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨sLo, sHi, sHt, sAl⟩,
            hSlot2.1, hSlot2.2.1, hSlot2.2.2.1, hSlot2.2.2.2⟩
        · exact ⟨⟨e_lo, e_hi, e_ht, e_al⟩,
            hKind2.1, hKind2.2.1, hKind2.2.2.1, hKind2.2.2.2.1,
            hKind2.2.2.2.2.1, hKind2.2.2.2.2.2.1, hKind2.2.2.2.2.2.2.1, hKind2.2.2.2.2.2.2.2⟩
        · show (BitVec.update ((bytesVal MKind.lw [0x58#8, 0x98#8, 0xfe#8, 0xff#8]
              + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
          decide)
      (show BBlockOK (0x8000354c#64) [15, 2, 14] gtChainB2b by decide) hi2
  rw [show endPCB (0x8000354c#64) gtChainB2b
        [(15, (0x80019f90#64 : BitVec 64)), (2, v2), (14, (0x80019f84#64 : BitVec 64))]
        (divLds2 k0 k1 k2 k3 k4 k5 k6 k7) = (0x800037dc#64 : BitVec 64) from by
          show BitVec.update ((bytesVal MKind.lw [0x58#8, 0x98#8, 0xfe#8, 0xff#8]
              + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1 = (0x800037dc#64 : BitVec 64)
          decide] at hpc3
  have hx16_3 : σ3.regs.get? Register.x16 = some (2#64) :=
    hk ▸ (block_reg hGH3 16 : σ3.regs.get? Register.x16
      = some (bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7]))
  have hx12_3 : σ3.regs.get? Register.x12 = some (14#64) :=
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

#print axioms evalDivChain_run

/-! ## Remaining for `evalDivChain_run` (the item-1 bridge, a `evalGeChain_run` clone)

`evalDivChain_run` proves `0x8000351c → 0x800037dc` and lands the `divDispL` pins
(`x16=2, x10=2, x2=v2, x9=sret, x17=Wr, x19=Wl`).  It is a faithful clone of
`evalGeChain_run` (`EvalGeChain.lean:68-320`) reusing the arm-INDEPENDENT prefix
blocks `gtChainB1`/`gtChainB2a`/`gtChainB2b` VERBATIM, with these swaps:

* token `23 → 14`: `geLds1 → divLds1`; the `hx12v`/`bltu`-guard/`hx15_1` decides
  use `divToken_val` (`14`) and `divIndex_val` (`3`) instead of ge's `23`/`12`;
* slot `opTableBase+48 (0x80019fb4) → opTableBase+12 (0x80019f90)`: `hx15_2` pins
  `x15 = 0x80019f90` (`3*4 + base`) not `0x80019fb4`; `GeSlotPinned → DivSlotPinned`
  (bytes `58 98 fe ff`), `sLo/sHi/sHt/sAl` bounds re-`decide`d for `0x80019f90`;
* `jr` target `0x80003628 → 0x800037dc`: the terminator end-PC `decide` uses
  `divSlot_routes` (proven above);
* the CSWTCH.25 index / kind `beq` ladder that ge runs @0x80003628 is NOT part of
  this prefix — the `.div` arm's kind checks are the `divDispatch` seg's own two
  `bne`s, so `evalDivChain_run`'s conclusion is just the `divDispL` pins at
  `0x800037dc`, no `x12` token pin (div's arm never re-reads the token).

Then the item-1 bridge `TwoSubReturn → SegPre divDispatch` composes:
`evalDivChain_run` (lands the pins + `mem = m0`) ≫ build `ChainFacts` via
`chain_facts` (residual = the frame-window `MemFacts` from a `DivResid` bundle, the
`.div` analog of `GeResid`) ≫ `divDispatchRow`.  See
`experiments/binop-value-tail-wiring.md` for the full assembly.
-/

end Vsa.Sim
