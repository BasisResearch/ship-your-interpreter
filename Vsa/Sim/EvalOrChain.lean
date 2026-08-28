import Vsa.Sim.EvalLogical2
import Vsa.Sim.EvalGtChain

/-!
# `EvalOrChain` — block-reflection lemma for `blockC_orFalse` (`.or`, falsy left)

`blockC_andTrue` (in `EvalLogical3`) walks `0x8000356c → 0x800035bc` (the shared
`blockC_logTail` entry).  The walk is broken by two *call* seams that are NOT block
terminators (`jal value_truthy @0x3594`, `jal eval_expr @0x35ac` = the RIGHT
`armTail_rec`), so this file collapses the three straight-line runs between them
into block-reflection lemmas (`bblock_sound_bt`), leaving the two call seams +
`blockC_logTail` to the row.

* `evalOrPrefix_run` : `0x356c → 0x3594` (op-check `beq` NOT-taken + the 24-byte
  copy of `vl` into the `value_truthy` arg buffer `sp-1024`).  Exposes the store
  tower `writeMap8³` AND the copy-window equality/outside-unchanged facts, so the
  row builds the buffer `ValueRepr` in three lines instead of the 70-line tower.
* `evalAndMid_run` : `0x3598 → 0x35ac` (reload-env `ld` + `beqz` NOT-taken + the
  RIGHT-operand call setup `ld a2,24(s0); mv a1,s2; addi a0,sp,240`), mem-fixed.
* `evalAndPost_run` : `0x35b0 → 0x35bc` (the three `ld` of the rv buffer), mem-fixed.

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

/-- B1: `lw x14,8(x8)` (op token) / `li x15,25` / `ld x12,120(x2)` (K13),
then `beq x14,x15 → …` NOT taken (op token `24 ≠ 25`) → fall to `0x8000357c`.
The op-token load bytes are pinned concrete (`25 = [0x19,0,0,0]`) so the guard
reduces; the K13 load keeps free byte pins. -/
def orB1 : BBlock :=
  { body :=
      [mkLine 0x8000356c#64 0x00842703#32,   -- lw   x14,8(x8)
       mkLine 0x80003570#64 0x01900793#32,   -- addi x15,x0,25 (li x15,25)
       mkLine 0x80003574#64 0x07813603#32],  -- ld   x12,120(x2)
    term := some ⟨0x80003578#64, 0x40f70063#32, 0x63#8, 0x00#8, 0xf7#8, 0x40#8,
      .br bop.BEQ true, 14, 15, 0x0400#13, 0#21, 0#12⟩ }

/-- B2: `ld x14,128(x2)` (PV) / `ld x15,136(x2)` (QV) / `addi x10,x2,64` (buf) /
`sd x12,64(x2)` / `sd x14,72(x2)` / `sd x15,80(x2)` — the three copy stores.
Fall-through (`jal value_truthy` seam is NOT a terminator). -/
def orB2 : BBlock :=
  { body :=
      [mkLine 0x80003978#64 0x08013703#32,   -- ld   x14,128(x2)
       mkLine 0x8000397c#64 0x08813783#32,   -- ld   x15,136(x2)
       mkLine 0x80003980#64 0x04010513#32,   -- addi x10,x2,64
       mkLine 0x80003984#64 0x04c13023#32,   -- sd   x12,64(x2)
       mkLine 0x80003988#64 0x04e13423#32,   -- sd   x14,72(x2)
       mkLine 0x8000398c#64 0x04f13823#32],  -- sd   x15,80(x2)
    term := none }

/-- B1's load-byte pins: op token (`[0x18,0,0,0]` = 24, concrete for the `beq`
guard) then K13 (free byte pins). -/
def orLds1 (k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 8) : List (List (BitVec 8)) :=
  [[0x19#8, 0x00#8, 0x00#8, 0x00#8], [k0, k1, k2, k3, k4, k5, k6, k7]]

/-- B2's load-byte pins: PV then QV (both free). -/
def orLds2 (p0 p1 p2 p3 p4 p5 p6 p7 q0 q1 q2 q3 q4 q5 q6 q7 : BitVec 8) :
    List (List (BitVec 8)) :=
  [[p0, p1, p2, p3, p4, p5, p6, p7], [q0, q1, q2, q3, q4, q5, q6, q7]]

/-- `0x8000356c → 0x80003594` (op-check `beq` NOT-taken + the 24-byte copy of `vl`
into the `value_truthy` arg buffer `sp-1024 = v2+0x40`), via two shallow
`bblock_sound_bt` applications.  Besides the store image `writeMap8³`, exposes the
24-byte copy-window equality and outside-unchanged facts so the row builds the
buffer `ValueRepr` directly (the omega-heavy byte tower is baked in here, once). -/
theorem evalOrPrefix_run (σ : MState) (i u : Nat)
    (vm v2 v8 sret aEnv : BitVec 64)
    (k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 8)   -- K13 dword @ v2+0x78
    (p0 p1 p2 p3 p4 p5 p6 p7 : BitVec 8)   -- PV  dword @ v2+0x80
    (q0 q1 q2 q3 q4 q5 q6 q7 : BitVec 8)   -- QV  dword @ v2+0x88
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000356c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx18 : σ.regs.get? Register.x18 = some aEnv)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    -- op-token load @ v8+0x008 (4-byte, = 25 = [0x19,0,0,0])
    (o_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (o_hi : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (o_ht : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (o_al : (v8 + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (o_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some (0x19#8))
    (o_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some (0x00#8))
    (o_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some (0x00#8))
    (o_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some (0x00#8))
    -- K13 load @ v2+0x078 (8-byte)
    (hK_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x078#12)).toNat)
    (hK_hi : (v2 + sign_extend (m := 64) (0x078#12)).toNat + 8 ≤ 0x100000000)
    (hK_ht : (v2 + sign_extend (m := 64) (0x078#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x078#12)).toNat)
    (hK_al : (v2 + sign_extend (m := 64) (0x078#12)).toNat % 8 = 0)
    (hK_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat]? = some k0)
    (hK_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 1]? = some k1)
    (hK_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 2]? = some k2)
    (hK_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 3]? = some k3)
    (hK_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 4]? = some k4)
    (hK_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 5]? = some k5)
    (hK_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 6]? = some k6)
    (hK_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x078#12)).toNat + 7]? = some k7)
    -- PV load @ v2+0x080 (8-byte)
    (hP_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x080#12)).toNat)
    (hP_hi : (v2 + sign_extend (m := 64) (0x080#12)).toNat + 8 ≤ 0x100000000)
    (hP_ht : (v2 + sign_extend (m := 64) (0x080#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x080#12)).toNat)
    (hP_al : (v2 + sign_extend (m := 64) (0x080#12)).toNat % 8 = 0)
    (hP_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat]? = some p0)
    (hP_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 1]? = some p1)
    (hP_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 2]? = some p2)
    (hP_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 3]? = some p3)
    (hP_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 4]? = some p4)
    (hP_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 5]? = some p5)
    (hP_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 6]? = some p6)
    (hP_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 7]? = some p7)
    -- QV load @ v2+0x088 (8-byte)
    (hQ_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x088#12)).toNat)
    (hQ_hi : (v2 + sign_extend (m := 64) (0x088#12)).toNat + 8 ≤ 0x100000000)
    (hQ_ht : (v2 + sign_extend (m := 64) (0x088#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x088#12)).toNat)
    (hQ_al : (v2 + sign_extend (m := 64) (0x088#12)).toNat % 8 = 0)
    (hQ_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat]? = some q0)
    (hQ_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 1]? = some q1)
    (hQ_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 2]? = some q2)
    (hQ_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 3]? = some q3)
    (hQ_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 4]? = some q4)
    (hQ_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 5]? = some q5)
    (hQ_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 6]? = some q6)
    (hQ_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 7]? = some q7)
    -- store safety @ v2+0x040 / 0x048 / 0x050 (buf, 8-byte each)
    (s0lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x040#12)).toNat)
    (s0hi : (v2 + sign_extend (m := 64) (0x040#12)).toNat + 8 ≤ 0x100000000)
    (s0win : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x040#12)).toNat)
    (s0al : (v2 + sign_extend (m := 64) (0x040#12)).toNat % 8 = 0)
    (s1lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x048#12)).toNat)
    (s1hi : (v2 + sign_extend (m := 64) (0x048#12)).toNat + 8 ≤ 0x100000000)
    (s1win : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x048#12)).toNat)
    (s1al : (v2 + sign_extend (m := 64) (0x048#12)).toNat % 8 = 0)
    (s2lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x050#12)).toNat)
    (s2hi : (v2 + sign_extend (m := 64) (0x050#12)).toNat + 8 ≤ 0x100000000)
    (s2win : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x050#12)).toNat)
    (s2al : (v2 + sign_extend (m := 64) (0x050#12)).toNat % 8 = 0)
    -- v2-relative address normalization (no wrap)
    (hn40 : (v2 + sign_extend (m := 64) (0x040#12)).toNat = v2.toNat + 0x40)
    (hn48 : (v2 + sign_extend (m := 64) (0x048#12)).toNat = v2.toNat + 0x48)
    (hn50 : (v2 + sign_extend (m := 64) (0x050#12)).toNat = v2.toNat + 0x50)
    (hn78 : (v2 + sign_extend (m := 64) (0x078#12)).toNat = v2.toNat + 0x78)
    (hn80 : (v2 + sign_extend (m := 64) (0x080#12)).toNat = v2.toNat + 0x80)
    (hn88 : (v2 + sign_extend (m := 64) (0x088#12)).toNat = v2.toNat + 0x88)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat) (D1 D2 D3 : BitVec (8 * 8)),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + blenB orB1 + blenB orB2⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (writeMap8 (writeMap8 σ.mem
          (v2 + sign_extend (m := 64) (0x040#12)).toNat D1)
          (v2 + sign_extend (m := 64) (0x048#12)).toNat D2)
          (v2 + sign_extend (m := 64) (0x050#12)).toNat D3 ∧
      -- 24-byte copy: buffer @ v2+0x40 mirrors the sub-value @ v2+0x78.
      (∀ j : Nat, j < 24 →
        σ'.mem[v2.toNat + 0x40 + j]? = σ.mem[v2.toNat + 0x78 + j]?) ∧
      -- everything outside the 24-byte buffer window is unchanged.
      (∀ a : Nat, (a < v2.toNat + 0x40 ∨ v2.toNat + 0x40 + 24 ≤ a) →
        σ'.mem[a]? = σ.mem[a]?) ∧
      σ'.regs.get? Register.PC = some (0x80003990#64) ∧
      σ'.regs.get? Register.x10 = some (v2 + sign_extend (m := 64) (0x040#12)) ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x8 = some v8 ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x18 = some aEnv ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, AbiPreservedNoise R → σ'.regs.get? R = σ.regs.get? R) := by
  -- ── B1: lw/li/ld + beq NOT taken (24 ≠ 25) → 0x8000357c ──────────────────────
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    bblock_sound_bt orB1 σ i u (0x8000356c#64) vm
      [(8, v8), (2, v2)]
      (orLds1 k0 k1 k2 k3 k4 k5 k6 k7)
      hG hpc hmi ⟨hx8, hx2, trivial⟩
      (show KeysOK [8, 2] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨o_lo, o_hi, o_ht, o_al⟩, o_p0, o_p1, o_p2, o_p3⟩
        · exact ⟨⟨hK_lo, hK_hi, hK_ht, hK_al⟩,
            hK_p0, hK_p1, hK_p2, hK_p3, hK_p4, hK_p5, hK_p6, hK_p7⟩
        · show guardB bop.BEQ (bytesVal MKind.lw [0x19#8, 0x00#8, 0x00#8, 0x00#8])
            ((0#64 : BitVec 64) + sign_extend (m := 64) (0x019#12)) = true
          decide)
      (show BBlockOK (0x8000356c#64) [8, 2] orB1 by decide) hi
  rw [show endPCB (0x8000356c#64) orB1 [(8, v8), (2, v2)]
        (orLds1 k0 k1 k2 k3 k4 k5 k6 k7) = (0x80003978#64 : BitVec 64) from by
          show (0x80003578#64 : BitVec 64) + sign_extend (m := 64) (0x0400#13) = (0x80003978#64 : BitVec 64)
          decide] at hpc1
  have hmem1e : σ1.mem = σ.mem := hmem1
  have hx2_1 : σ1.regs.get? Register.x2 = some v2 := (hframe1 Register.x2 (by decide) (by decide)).trans hx2
  have hx8_1 : σ1.regs.get? Register.x8 = some v8 := (hframe1 Register.x8 (by decide) (by decide)).trans hx8
  have hx9_1 : σ1.regs.get? Register.x9 = some sret := (hframe1 Register.x9 (by decide) (by decide)).trans hx9
  have hx18_1 : σ1.regs.get? Register.x18 = some aEnv := (hframe1 Register.x18 (by decide) (by decide)).trans hx18
  have hx12_1 : σ1.regs.get? Register.x12
      = some (bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7]) := block_reg hGH1 12
  obtain ⟨vm1, hmi1'⟩ := hmi1
  -- PV/QV load pins over σ1.mem (= σ.mem).
  have hP1 : σ1.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat]? = some p0 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 1]? = some p1 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 2]? = some p2 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 3]? = some p3 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 4]? = some p4 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 5]? = some p5 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 6]? = some p6 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x080#12)).toNat + 7]? = some p7 := by
    rw [hmem1e]; exact ⟨hP_p0, hP_p1, hP_p2, hP_p3, hP_p4, hP_p5, hP_p6, hP_p7⟩
  have hQ1 : σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat]? = some q0 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 1]? = some q1 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 2]? = some q2 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 3]? = some q3 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 4]? = some q4 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 5]? = some q5 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 6]? = some q6 ∧
      σ1.mem[(v2 + sign_extend (m := 64) (0x088#12)).toNat + 7]? = some q7 := by
    rw [hmem1e]; exact ⟨hQ_p0, hQ_p1, hQ_p2, hQ_p3, hQ_p4, hQ_p5, hQ_p6, hQ_p7⟩
  -- ── B2: ld/ld/addi/sd/sd/sd (fall-through) ──────────────────────────────────
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
    bblock_sound_bt orB2 σ1 i1 (u + blenB orB1) (0x80003978#64) vm1
      [(2, v2), (12, bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7])]
      (orLds2 p0 p1 p2 p3 p4 p5 p6 p7 q0 q1 q2 q3 q4 q5 q6 q7)
      hG1 hpc1 hmi1' ⟨hx2_1, hx12_1, trivial⟩
      (show KeysOK [2, 12] by decide)
      (by
        block_facts (hmem1e ▸ hmem : Vsa.Sim.Code.Eval_exprLoaded σ1.mem)
          with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨hP_lo, hP_hi, hP_ht, hP_al⟩,
            hP1.1, hP1.2.1, hP1.2.2.1, hP1.2.2.2.1,
            hP1.2.2.2.2.1, hP1.2.2.2.2.2.1, hP1.2.2.2.2.2.2.1, hP1.2.2.2.2.2.2.2⟩
        · exact ⟨⟨hQ_lo, hQ_hi, hQ_ht, hQ_al⟩,
            hQ1.1, hQ1.2.1, hQ1.2.2.1, hQ1.2.2.2.1,
            hQ1.2.2.2.2.1, hQ1.2.2.2.2.2.1, hQ1.2.2.2.2.2.2.1, hQ1.2.2.2.2.2.2.2⟩
        · exact ⟨s0lo, s0hi, s0win, s0al⟩
        · exact ⟨s1lo, s1hi, s1win, s1al⟩
        · exact ⟨s2lo, s2hi, s2win, s2al⟩)
      (show BBlockOK (0x80003978#64) [2, 12] orB2 by decide) hi1
  rw [show endPCB (0x80003978#64) orB2 [(2, v2), (12, bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7])]
        (orLds2 p0 p1 p2 p3 p4 p5 p6 p7 q0 q1 q2 q3 q4 q5 q6 q7)
        = (0x80003990#64 : BitVec 64) from by
          show endPCM (0x80003978#64) orB2.body = (0x80003990#64 : BitVec 64)
          decide] at hpc2
  have hx2_2 : σ2.regs.get? Register.x2 = some v2 := (hframe2 Register.x2 (by decide) (by decide)).trans hx2_1
  have hx8_2 : σ2.regs.get? Register.x8 = some v8 := (hframe2 Register.x8 (by decide) (by decide)).trans hx8_1
  have hx9_2 : σ2.regs.get? Register.x9 = some sret := (hframe2 Register.x9 (by decide) (by decide)).trans hx9_1
  have hx18_2 : σ2.regs.get? Register.x18 = some aEnv := (hframe2 Register.x18 (by decide) (by decide)).trans hx18_1
  have hx10v : (v2 + sign_extend (m := 64) (0x040#12) : BitVec 64) = v2 + sign_extend (m := 64) (0x040#12) := rfl
  have hx10_2 : σ2.regs.get? Register.x10 = some (v2 + sign_extend (m := 64) (0x040#12)) := block_reg hGH2 10
  obtain ⟨vm2, hmi2'⟩ := hmi2
  -- memory image writeMap8³ (concrete stored data = sdData of the loaded dwords).
  have hmemW0 : σ2.mem = writeLog σ.mem (wlogM orB2.body
      [(2, v2), (12, bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7])]
      (orLds2 p0 p1 p2 p3 p4 p5 p6 p7 q0 q1 q2 q3 q4 q5 q6 q7)) := hmem1e ▸ hmem2
  have hmemCopy : σ2.mem = writeMap8 (writeMap8 (writeMap8 σ.mem
      (v2 + sign_extend (m := 64) (0x040#12)).toNat
        (sdData_val (sign_extend (m := 64)
          ((((((((k7.append k6).append k5).append k4).append k3).append k2).append k1).append k0) : BitVec (8*8)))))
      (v2 + sign_extend (m := 64) (0x048#12)).toNat
        (sdData_val (sign_extend (m := 64)
          ((((((((p7.append p6).append p5).append p4).append p3).append p2).append p1).append p0) : BitVec (8*8)))))
      (v2 + sign_extend (m := 64) (0x050#12)).toNat
        (sdData_val (sign_extend (m := 64)
          ((((((((q7.append q6).append q5).append q4).append q3).append q2).append q1).append q0) : BitVec (8*8)))) := hmemW0
  -- outside-window agreement.
  have hcopyOut : ∀ a : Nat, (a < v2.toNat + 0x40 ∨ v2.toNat + 0x40 + 24 ≤ a) →
      σ2.mem[a]? = σ.mem[a]? := by
    intro a ha
    rw [hmemCopy,
      getElem_writeMap8_disjoint _ (v2 + sign_extend (m := 64) (0x050#12)).toNat a _ (by rw [hn50]; omega),
      getElem_writeMap8_disjoint _ (v2 + sign_extend (m := 64) (0x048#12)).toNat a _ (by rw [hn48]; omega),
      getElem_writeMap8_disjoint _ (v2 + sign_extend (m := 64) (0x040#12)).toNat a _ (by rw [hn40]; omega)]
  -- 24-byte copy-window equality.
  obtain ⟨eK0, eK1, eK2, eK3, eK4, eK5, eK6, eK7⟩ := sdData_sext_bytes k0 k1 k2 k3 k4 k5 k6 k7
  obtain ⟨eP0, eP1, eP2, eP3, eP4, eP5, eP6, eP7⟩ := sdData_sext_bytes p0 p1 p2 p3 p4 p5 p6 p7
  obtain ⟨eQ0, eQ1, eQ2, eQ3, eQ4, eQ5, eQ6, eQ7⟩ := sdData_sext_bytes q0 q1 q2 q3 q4 q5 q6 q7
  have hDK : ∀ o : Nat, o < 8 → σ2.mem[v2.toNat + 0x40 + o]?
      = (writeMap8 σ.mem (v2 + sign_extend (m := 64) (0x040#12)).toNat
          (sdData_val (sign_extend (m := 64)
            ((((((((k7.append k6).append k5).append k4).append k3).append k2).append k1).append k0) : BitVec (8*8)))))[v2.toNat + 0x40 + o]? := by
    intro o ho
    rw [hmemCopy,
      getElem_writeMap8_disjoint _ (v2 + sign_extend (m := 64) (0x050#12)).toNat _ _ (by rw [hn50]; omega),
      getElem_writeMap8_disjoint _ (v2 + sign_extend (m := 64) (0x048#12)).toNat _ _ (by rw [hn48]; omega)]
  have hDP : ∀ o : Nat, o < 8 → σ2.mem[v2.toNat + 0x48 + o]?
      = (writeMap8 (writeMap8 σ.mem (v2 + sign_extend (m := 64) (0x040#12)).toNat
          (sdData_val (sign_extend (m := 64)
            ((((((((k7.append k6).append k5).append k4).append k3).append k2).append k1).append k0) : BitVec (8*8)))))
          (v2 + sign_extend (m := 64) (0x048#12)).toNat
          (sdData_val (sign_extend (m := 64)
            ((((((((p7.append p6).append p5).append p4).append p3).append p2).append p1).append p0) : BitVec (8*8)))))[v2.toNat + 0x48 + o]? := by
    intro o ho
    rw [hmemCopy,
      getElem_writeMap8_disjoint _ (v2 + sign_extend (m := 64) (0x050#12)).toNat _ _ (by rw [hn50]; omega)]
  have hcopyWin : ∀ j : Nat, j < 24 →
      σ2.mem[v2.toNat + 0x40 + j]? = σ.mem[v2.toNat + 0x78 + j]? := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
        j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨
        j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 from by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hDK 0 (by omega), hn40, show v2.toNat + 0x40 + 0 = v2.toNat + 0x40 from by omega,
        getElem_writeMap8_0, eK0, show v2.toNat + 0x78 + 0 = v2.toNat + 0x78 from by omega]
      rw [hn78] at hK_p0; exact hK_p0.symm
    · rw [hDK 1 (by omega), hn40, getElem_writeMap8_1, eK1]; rw [hn78] at hK_p1; exact hK_p1.symm
    · rw [hDK 2 (by omega), hn40, getElem_writeMap8_2, eK2]; rw [hn78] at hK_p2; exact hK_p2.symm
    · rw [hDK 3 (by omega), hn40, getElem_writeMap8_3, eK3]; rw [hn78] at hK_p3; exact hK_p3.symm
    · rw [hDK 4 (by omega), hn40, getElem_writeMap8_4, eK4]; rw [hn78] at hK_p4; exact hK_p4.symm
    · rw [hDK 5 (by omega), hn40, getElem_writeMap8_5, eK5]; rw [hn78] at hK_p5; exact hK_p5.symm
    · rw [hDK 6 (by omega), hn40, getElem_writeMap8_6, eK6]; rw [hn78] at hK_p6; exact hK_p6.symm
    · rw [hDK 7 (by omega), hn40, getElem_writeMap8_7, eK7]; rw [hn78] at hK_p7; exact hK_p7.symm
    · rw [show v2.toNat + 0x40 + 8 = v2.toNat + 0x48 + 0 from by omega, hDP 0 (by omega), hn48,
        show v2.toNat + 0x48 + 0 = v2.toNat + 0x48 from by omega, getElem_writeMap8_0, eP0,
        show v2.toNat + 0x78 + 8 = v2.toNat + 0x80 from by omega]; rw [hn80] at hP_p0; exact hP_p0.symm
    · rw [show v2.toNat + 0x40 + 9 = v2.toNat + 0x48 + 1 from by omega, hDP 1 (by omega), hn48,
        getElem_writeMap8_1, eP1, show v2.toNat + 0x78 + 9 = v2.toNat + 0x80 + 1 from by omega]
      rw [hn80] at hP_p1; exact hP_p1.symm
    · rw [show v2.toNat + 0x40 + 10 = v2.toNat + 0x48 + 2 from by omega, hDP 2 (by omega), hn48,
        getElem_writeMap8_2, eP2, show v2.toNat + 0x78 + 10 = v2.toNat + 0x80 + 2 from by omega]
      rw [hn80] at hP_p2; exact hP_p2.symm
    · rw [show v2.toNat + 0x40 + 11 = v2.toNat + 0x48 + 3 from by omega, hDP 3 (by omega), hn48,
        getElem_writeMap8_3, eP3, show v2.toNat + 0x78 + 11 = v2.toNat + 0x80 + 3 from by omega]
      rw [hn80] at hP_p3; exact hP_p3.symm
    · rw [show v2.toNat + 0x40 + 12 = v2.toNat + 0x48 + 4 from by omega, hDP 4 (by omega), hn48,
        getElem_writeMap8_4, eP4, show v2.toNat + 0x78 + 12 = v2.toNat + 0x80 + 4 from by omega]
      rw [hn80] at hP_p4; exact hP_p4.symm
    · rw [show v2.toNat + 0x40 + 13 = v2.toNat + 0x48 + 5 from by omega, hDP 5 (by omega), hn48,
        getElem_writeMap8_5, eP5, show v2.toNat + 0x78 + 13 = v2.toNat + 0x80 + 5 from by omega]
      rw [hn80] at hP_p5; exact hP_p5.symm
    · rw [show v2.toNat + 0x40 + 14 = v2.toNat + 0x48 + 6 from by omega, hDP 6 (by omega), hn48,
        getElem_writeMap8_6, eP6, show v2.toNat + 0x78 + 14 = v2.toNat + 0x80 + 6 from by omega]
      rw [hn80] at hP_p6; exact hP_p6.symm
    · rw [show v2.toNat + 0x40 + 15 = v2.toNat + 0x48 + 7 from by omega, hDP 7 (by omega), hn48,
        getElem_writeMap8_7, eP7, show v2.toNat + 0x78 + 15 = v2.toNat + 0x80 + 7 from by omega]
      rw [hn80] at hP_p7; exact hP_p7.symm
    · rw [hmemCopy, show v2.toNat + 0x40 + 16 = (v2 + sign_extend (m := 64) (0x050#12)).toNat from by rw [hn50],
        getElem_writeMap8_0, eQ0, show v2.toNat + 0x78 + 16 = v2.toNat + 0x88 from by omega]
      rw [hn88] at hQ_p0; exact hQ_p0.symm
    · rw [hmemCopy, show v2.toNat + 0x40 + 17 = (v2 + sign_extend (m := 64) (0x050#12)).toNat + 1 from by rw [hn50],
        getElem_writeMap8_1, eQ1, show v2.toNat + 0x78 + 17 = v2.toNat + 0x88 + 1 from by omega]
      rw [hn88] at hQ_p1; exact hQ_p1.symm
    · rw [hmemCopy, show v2.toNat + 0x40 + 18 = (v2 + sign_extend (m := 64) (0x050#12)).toNat + 2 from by rw [hn50],
        getElem_writeMap8_2, eQ2, show v2.toNat + 0x78 + 18 = v2.toNat + 0x88 + 2 from by omega]
      rw [hn88] at hQ_p2; exact hQ_p2.symm
    · rw [hmemCopy, show v2.toNat + 0x40 + 19 = (v2 + sign_extend (m := 64) (0x050#12)).toNat + 3 from by rw [hn50],
        getElem_writeMap8_3, eQ3, show v2.toNat + 0x78 + 19 = v2.toNat + 0x88 + 3 from by omega]
      rw [hn88] at hQ_p3; exact hQ_p3.symm
    · rw [hmemCopy, show v2.toNat + 0x40 + 20 = (v2 + sign_extend (m := 64) (0x050#12)).toNat + 4 from by rw [hn50],
        getElem_writeMap8_4, eQ4, show v2.toNat + 0x78 + 20 = v2.toNat + 0x88 + 4 from by omega]
      rw [hn88] at hQ_p4; exact hQ_p4.symm
    · rw [hmemCopy, show v2.toNat + 0x40 + 21 = (v2 + sign_extend (m := 64) (0x050#12)).toNat + 5 from by rw [hn50],
        getElem_writeMap8_5, eQ5, show v2.toNat + 0x78 + 21 = v2.toNat + 0x88 + 5 from by omega]
      rw [hn88] at hQ_p5; exact hQ_p5.symm
    · rw [hmemCopy, show v2.toNat + 0x40 + 22 = (v2 + sign_extend (m := 64) (0x050#12)).toNat + 6 from by rw [hn50],
        getElem_writeMap8_6, eQ6, show v2.toNat + 0x78 + 22 = v2.toNat + 0x88 + 6 from by omega]
      rw [hn88] at hQ_p6; exact hQ_p6.symm
    · rw [hmemCopy, show v2.toNat + 0x40 + 23 = (v2 + sign_extend (m := 64) (0x050#12)).toNat + 7 from by rw [hn50],
        getElem_writeMap8_7, eQ7, show v2.toNat + 0x78 + 23 = v2.toNat + 0x88 + 7 from by omega]
      rw [hn88] at hQ_p7; exact hQ_p7.symm
  -- combined ABI-noise frame over the two blocks.
  have hframeC : ∀ R : Register, AbiPreservedNoise R → σ2.regs.get? R = σ.regs.get? R := by
    intro R hR
    have hab := hR.1
    exact (hframe2 R (abiNoise_noiseRegs hR) (by block_frame_wr [14, 15, 10])).trans
      (hframe1 R (abiNoise_noiseRegs hR) (by block_frame_wr [14, 15, 12]))
  have hout2e : σ2.sailOutput = σ.sailOutput := hout2.trans hout1
  refine ⟨σ2, i2, _, _, _, ?_, hi2, hG2,
    hmemCopy, hcopyWin, hcopyOut, hpc2, hx10_2, hx2_2, hx8_2, hx9_2, hx18_2, hout2e, ⟨vm2, hmi2'⟩, hframeC⟩
  exact hsteps1.trans hsteps2

end Vsa.Sim
