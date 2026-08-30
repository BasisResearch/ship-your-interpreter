import Vsa.Sim.SnprintfSites2
import Vsa.Sim.SnprintfSpec2
import Vsa.Sim.Code.FlushPins
import Vsa.Sim.KeepRegs
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec4` : the sign block, composed

Session-4 file (`_sn4` suffix).  Composes the sign-block step battery of
`SnprintfSites2.lean` into a `Steps` chain over the `%lld` sign segment
(`experiments/M3-snprintf-lld.md` §1.3(c), disasm `[0x800080e4, 0x800080f4]`) and
bridges its result to the arithmetic core (`SnprintfSpec.lean`:
`neg_magnitude`, `intToString_of_bv`).  The two arms mirror the machine's `bgez`
split exactly:

* **negative** (`bgez` not taken, `2^63 ≤ v.toNat`): emit `'-'` into the sign slot
  `sp+167`, `neg a4,a4` so `x14 = 0 - v = |v.toInt|` (the magnitude the decimal
  loop consumes) — `signBlock_neg_spec` below;
* **nonnegative** (`bgez` taken, `v.toNat < 2^63`): skip the sign block, the
  magnitude is `x14 = v = v.toNat` — `signBlock_nonneg_step_sn4`.

## Sign-byte placement — the load-bearing finding

The `'-'` byte is stored at `sp+167` (`0x800080f0 sb a5,167(sp)`), a dedicated
stack slot **disjoint** from the descending digit buffer at `sp+348` (written by
`0x8000832c sb a0,-1(s9)`).  It is read back at `0x80008388 lbu t5,167(sp)` by the
pad/flush machinery and prepended into the iov `__ssprint_r` copies to the caller
buffer.  So the `'-'` is **prepended at flush, never in the digit buffer** — the
byte-level realisation of `intToString (.negSucc m) = "-" ++ natToString (m+1)`
(`intToString_of_bv`: sign prefix ++ magnitude digits, computed independently).

## What composes here, and what is a documented boundary

The two loads that begin the sign block — `0x800080dc ld a3,0(a4)` (the 64-bit
va_list arg) and its `ld a4,24(sp)` predecessor — have **no `stepObs_load`
primitive** in the current step layer, so they are a precondition boundary: the
specs below take `x13 = v` (the loaded value) as a hypothesis.  The interleaved
`0x800080e0 sd a5,24(sp)` (va_list bump) and `0x800080f8 bltz s4` (already-set
flag guard) are off the value-producing path and elided; the linear trace steps
`mv a4,a3 → bgez → [li '-' ; sb '-' ; neg]`.  The subsequent loop-entry setup
(`0x800082c8 …` establishing `LSt g top m 0`, which feeds `decimalLoop_spec`'s
`DLI`) and the flush (`0x80008a80 … __ssprint_r`, memmove into the caller buffer)
are the remaining segments; their precise shape is documented at the end.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code (SvfprintfSliceLoaded)
open Vsa.While (intToString natToString)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Store read-backs and `…Loaded`-insert (self-contained `_sn4` copies)

These mirror the STORE-class observation helpers and the byte-store frame for
`SvfprintfSliceLoaded`.  They are re-derived here (rather than imported from
`SnprintfSpec3`) so this file depends only on the machine-stepping layer
(`SnprintfSpec2`) — keeping the sign-block composition independent of the
digit-loop file. -/

theorem obs_store_pc_sn4 {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) := by
  rw [hobs.1 Register.PC (by decide) (by decide) (by decide)]
  show ((((sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, reduceCtorEq,
    dif_neg, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_store_other_sn4 {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)} (R : Register) {w : RegisterType R}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m'))
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w := by
  rw [hobs.1 R hmc hmt hmi]
  rw [get?_sigmaPost_store σ pc vm m' R h1 h2 h4 h5]; exact hσ

theorem obs_store_minstret_sn4 {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, ?_⟩
  rw [hobs.1 Register.minstret (by decide) (by decide) (by decide)]
  show ((((sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-- Read-over-write below the store key: a byte store at `k ≥ 0x80009000` leaves
every read at a code address `a < 0x80009000` unchanged.  Used as a conditional
rewrite (`simp (disch := omega)`) so the `…Loaded` conjunction transfers in one
pass instead of goal-by-goal. -/
theorem getElem?_insert_above_sn4 (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80009000 ≤ k) (a : Nat) (ha : a < 0x80009000) :
    (mem.insert k v)[a]? = mem[a]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-- `SvfprintfSliceLoaded` survives a byte store at a key above the code region
(`0x80009000 ≤ k`; the slice spans `[0x80007654, 0x80008b11)`). -/
theorem svfprintfSlice_insert_sn4 (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80009000 ≤ k) (h : SvfprintfSliceLoaded mem) :
    SvfprintfSliceLoaded (mem.insert k v) := by
  unfold SvfprintfSliceLoaded at h ⊢
  simp only [Vsa.Sim.Code.svfprintfSliceChunk0, Vsa.Sim.Code.svfprintfSliceChunk1,
    Vsa.Sim.Code.svfprintfSliceChunk2, Vsa.Sim.Code.svfprintfSliceChunk3,
    Vsa.Sim.Code.svfprintfSliceChunk4, Vsa.Sim.Code.svfprintfSliceChunk5,
    Vsa.Sim.Code.svfprintfSliceChunk6, Vsa.Sim.Code.svfprintfSliceChunk7,
    Vsa.Sim.Code.svfprintfSliceChunk8, Vsa.Sim.Code.svfprintfSliceChunk9,
    Vsa.Sim.Code.svfprintfSliceChunk10, Vsa.Sim.Code.svfprintfSliceChunk11,
    Vsa.Sim.Code.svfprintfSliceChunk12, Vsa.Sim.Code.svfprintfSliceChunk13,
    Vsa.Sim.Code.svfprintfSliceChunk14, Vsa.Sim.Code.svfprintfSliceChunk15,
    Vsa.Sim.Code.svfprintfSliceChunk16, Vsa.Sim.Code.svfprintfSliceChunk17,
    Vsa.Sim.Code.svfprintfSliceChunk18, Vsa.Sim.Code.svfprintfSliceChunk19,
    Vsa.Sim.Code.svfprintfSliceChunk20, Vsa.Sim.Code.svfprintfSliceChunk21,
    Vsa.Sim.Code.svfprintfSliceChunk22, Vsa.Sim.Code.svfprintfSliceChunk23,
    Vsa.Sim.Code.svfprintfSliceChunk24, Vsa.Sim.Code.svfprintfSliceChunk25,
    Vsa.Sim.Code.svfprintfSliceChunk26, Vsa.Sim.Code.svfprintfSliceChunk27,
    Vsa.Sim.Code.svfprintfSliceChunk28, Vsa.Sim.Code.svfprintfSliceChunk29,
    Vsa.Sim.Code.svfprintfSliceChunk30, Vsa.Sim.Code.svfprintfSliceChunk31,
    Vsa.Sim.Code.svfprintfSliceChunk32, Vsa.Sim.Code.svfprintfSliceChunk33] at h ⊢
  simp (disch := omega) only [getElem?_insert_above_sn4 mem k v hk]
  exact h

/-- `__umoddi3Loaded` survives a byte store above the code region. -/
theorem umoddi3_insert_sn4 (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80009000 ≤ k) (h : Vsa.Sim.Code.__umoddi3Loaded mem) :
    Vsa.Sim.Code.__umoddi3Loaded (mem.insert k v) := by
  have c0 := Vsa.Sim.Code.__umoddi3_chunk0 h
  show Vsa.Sim.Code.__umoddi3Chunk0 (mem.insert k v)
  simp only [Vsa.Sim.Code.__umoddi3Chunk0] at c0 ⊢
  simp (disch := omega) only [getElem?_insert_above_sn4 mem k v hk]
  exact c0

/-- `__hidden___udivdi3Loaded` survives a byte store above the code region. -/
theorem cudivdi3_insert_sn4 (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80009000 ≤ k) (h : Vsa.Sim.Code.__hidden___udivdi3Loaded mem) :
    Vsa.Sim.Code.__hidden___udivdi3Loaded (mem.insert k v) := by
  obtain ⟨c0, c1⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [Vsa.Sim.Code.__hidden___udivdi3Chunk0] at c0 ⊢
    simp (disch := omega) only [getElem?_insert_above_sn4 mem k v hk]
    exact c0
  · simp only [Vsa.Sim.Code.__hidden___udivdi3Chunk1] at c1 ⊢
    simp (disch := omega) only [getElem?_insert_above_sn4 mem k v hk]
    exact c1

/-! ## Branch-not-taken read-backs (sign block's `bgez`)

Mirror the `obs_store_*_sn4` shape for the not-taken branch step.  Built directly
on `get?_sigmaPost_branch_nottaken` (`StepBranch.lean`). -/

theorem obs_bnt_pc_sn4 {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) := by
  rw [hobs.1 Register.PC (by decide) (by decide) (by decide)]
  show ((((sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, reduceCtorEq,
    dif_neg, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_bnt_other_sn4 {σ' σ : MState} {pc vm : BitVec 64} (R : Register) {w : RegisterType R}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm))
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w := by
  rw [hobs.1 R hmc hmt hmi, get?_sigmaPost_branch_nottaken σ pc vm R h1 h2 h4 h5]; exact hσ

theorem obs_bnt_minstret_sn4 {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, ?_⟩
  rw [hobs.1 Register.minstret (by decide) (by decide) (by decide)]
  show ((((sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_bt_pc_sn4 {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) :
    σ'.regs.get? Register.PC = some (pc + sign_extend (m := 64) imm) := by
  rw [hobs.1 Register.PC (by decide) (by decide) (by decide)]
  show ((((sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, reduceCtorEq,
    dif_neg, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_bt_minstret_sn4 {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, ?_⟩
  rw [hobs.1 Register.minstret (by decide) (by decide) (by decide)]
  show ((((sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-! ## The magnitude value bridge

For a negative argument (top bit set), the machine's `neg a4,a4` yields
`x14 = 0 - v`, whose `toNat` is the magnitude `|v.toInt|` — the very `Nat` the
decimal loop's `LSt g top (magnitude) 0` invariant is stated over.  This is the
value-level link between the sign block's output and `decimalLoop_spec`'s `m`. -/

/-- The `neg` output `(0#64) - v` equals `- v` (two's complement), so its `toNat`
is the unsigned magnitude, `= (- v.toInt).toNat` for `v` negative (`neg_magnitude`). -/
theorem neg_out_toNat_sn4 (v : BitVec 64) (hneg : 2 ^ 63 ≤ v.toNat) :
    ((0#64) - v).toNat = (- v.toInt).toNat := by
  have hn : ((0#64) - v) = (- v) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_neg, BitVec.toNat_sub]; simp
  rw [hn]; exact neg_magnitude v hneg

/-- `intToString` of the signed value, in terms of the sign-block outputs: the
sign prefix (`"-"` iff `bgez` not taken) concatenated with `natToString` of the
magnitude the loop receives (`(0#64)-v` for negatives, `v` for nonnegatives). -/
theorem intToString_signblock_sn4 (v : BitVec 64) :
    intToString v.toInt =
      (if 2 ^ 63 ≤ v.toNat then "-" ++ natToString ((0#64) - v).toNat
       else natToString v.toNat) := by
  rw [intToString_of_bv]
  by_cases h : 2 ^ 63 ≤ v.toNat
  · rw [if_pos h, if_pos h]
    congr 1
  · rw [if_neg h, if_neg h]

/-! ## `signBlock_neg_spec` — the negative arm, composed

From the sign-block entry at `0x800080e4` with `x13 = v` (the loaded argument) and
`v` negative, step `mv a4,a3 → bgez(not taken) → li a5,45 → sb a5,167(sp) →
neg a4,a4`, landing at `0x800080f8` with:

* `x14 = (0#64) - v` — the unsigned magnitude the decimal loop consumes;
* the sign byte `'-' = 45` stored at `sp+167` (`x2 = sp`), disjoint from the digit
  buffer;
* `PC = 0x800080f8`, `GoodState`, `tick < 2`, `minstret` defined;
* `x13` (the original value) still available for downstream use.

`x2 = sp` (the stack pointer, live throughout) and the sign-slot address bounds
(`sp+167` is in RAM, above `tohost`) are hypotheses. -/
theorem signBlock_neg_spec
    (v vsp vt1 v8 v20 v23 v28 v12 : BitVec 64) (c : Config)
    (hG : GoodState c.σ) (hmem : SvfprintfSliceLoaded c.σ.mem)
    (hfp : Vsa.Sim.Code.FlushPinsLoaded c.σ.mem)
    (huload : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem)
    (hcuload : Vsa.Sim.Code.__hidden___udivdi3Loaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800080e4#64))
    (hx13 : c.σ.regs.get? Register.x13 = some v)
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some vt1)
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx23 : c.σ.regs.get? Register.x23 = some v23)
    (hx28 : c.σ.regs.get? Register.x28 = some v28)
    (hx12 : c.σ.regs.get? Register.x12 = some v12)
    (hneg : zopz0zKzJ_s v (0#64) = false)
    (hmi : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (htick : c.tick < 2)
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x0a7#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x0a7#12)).toNat) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800080f8#64) ∧
      c'.σ.regs.get? Register.x14 = some ((0#64) - v) ∧
      c'.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (stData 1 ((0#64) + sign_extend (m := 64) (0x02d#12))) ∧
      c'.tick < 2 ∧ (∃ w, c'.σ.regs.get? Register.minstret = some w) ∧
      c'.σ.regs.get? Register.x13 = some v ∧ c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x6 = some vt1 ∧ c'.σ.regs.get? Register.x8 = some v8 ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧ c'.σ.regs.get? Register.x23 = some v23 ∧
      c'.σ.regs.get? Register.x28 = some v28 ∧ c'.σ.regs.get? Register.x12 = some v12 ∧
      SvfprintfSliceLoaded c'.σ.mem ∧ Vsa.Sim.Code.__umoddi3Loaded c'.σ.mem ∧
      Vsa.Sim.Code.__hidden___udivdi3Loaded c'.σ.mem ∧
      Vsa.Sim.Code.FlushPinsLoaded c'.σ.mem ∧
      -- post-widening: mid-register preservation + the single-byte memory frame
      KeepRegs midRegs5 c.σ c'.σ ∧
      (∀ a : Nat, a ≠ (vsp + sign_extend (m := 64) (0x0a7#12)).toNat →
        c'.σ.mem[a]? = c.σ.mem[a]?) := by
  obtain ⟨vmi, hvmi⟩ := hmi
  -- Step e4: mv a4,a3  ⇒ x14 := v + 0
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800080e4_sn4 c.σ c.tick c.steps (0x800080e4#64) vmi v hG hpc hvmi hx13 hmem rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x800080e8#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800080e4#64 : BitVec 64) 4 = (0x800080e8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_1 : σ1.regs.get? Register.x14 = some (v + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx13_1 : σ1.regs.get? Register.x13 = some v :=
    obs_alu_other' hobs1 Register.x13 (by decide) hx13
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs1 Register.x2 (by decide) hx2
  have hx6_1 : σ1.regs.get? Register.x6 = some vt1 :=
    obs_alu_other' hobs1 Register.x6 (by decide) hx6
  have hx8_1 : σ1.regs.get? Register.x8 = some v8 :=
    obs_alu_other' hobs1 Register.x8 (by decide) hx8
  have hx20_1 : σ1.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs1 Register.x20 (by decide) hx20
  have hx23_1 : σ1.regs.get? Register.x23 = some v23 :=
    obs_alu_other' hobs1 Register.x23 (by decide) hx23
  have hx28_1 : σ1.regs.get? Register.x28 = some v28 :=
    obs_alu_other' hobs1 Register.x28 (by decide) hx28
  have hx12_1 : σ1.regs.get? Register.x12 = some v12 :=
    obs_alu_other' hobs1 Register.x12 (by decide) hx12
  obtain ⟨vmi1, hvmi1⟩ := obs_alu_minstret hobs1
  have hmem1' : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hmem
  have huload1 : Vsa.Sim.Code.__umoddi3Loaded σ1.mem := hmem1 ▸ huload
  have hcuload1 : Vsa.Sim.Code.__hidden___udivdi3Loaded σ1.mem := hmem1 ▸ hcuload
  -- Step e8: bgez a3 (not taken, v negative) ⇒ fall through to ec
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800080e8_nottaken_sn4 σ1 i1 (c.steps + 1) (0x800080e8#64) vmi1 v hG1 hpc1 hvmi1 hx13_1 hmem1' rfl hneg hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x800080ec#64) := by
    have := obs_bnt_pc_sn4 hobs2
    rwa [show BitVec.addInt (0x800080e8#64 : BitVec 64) 4 = (0x800080ec#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_2 : σ2.regs.get? Register.x14 = some (v + sign_extend (m := 64) (0x000#12)) :=
    obs_bnt_other_sn4 Register.x14 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_1
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_bnt_other_sn4 Register.x2 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx13_2 : σ2.regs.get? Register.x13 = some v :=
    obs_bnt_other_sn4 Register.x13 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_1
  have hx6_2 : σ2.regs.get? Register.x6 = some vt1 :=
    obs_bnt_other_sn4 Register.x6 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_1
  have hx8_2 : σ2.regs.get? Register.x8 = some v8 :=
    obs_bnt_other_sn4 Register.x8 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_1
  have hx20_2 : σ2.regs.get? Register.x20 = some v20 :=
    obs_bnt_other_sn4 Register.x20 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_1
  have hx23_2 : σ2.regs.get? Register.x23 = some v23 :=
    obs_bnt_other_sn4 Register.x23 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_1
  have hx28_2 : σ2.regs.get? Register.x28 = some v28 :=
    obs_bnt_other_sn4 Register.x28 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_1
  have hx12_2 : σ2.regs.get? Register.x12 = some v12 :=
    obs_bnt_other_sn4 Register.x12 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
  obtain ⟨vmi2, hvmi2⟩ := obs_bnt_minstret_sn4 hobs2
  have hmem2' : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hmem1'
  have huload2 : Vsa.Sim.Code.__umoddi3Loaded σ2.mem := hmem2 ▸ huload1
  have hcuload2 : Vsa.Sim.Code.__hidden___udivdi3Loaded σ2.mem := hmem2 ▸ hcuload1
  -- Step ec: li a5,45  ⇒ x15 := 45 ('-')
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_800080ec_sn4 σ2 i2 (c.steps + 1 + 1) (0x800080ec#64) vmi2 hG2 hpc2 hvmi2 hmem2' rfl hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x800080f0#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x800080ec#64 : BitVec 64) 4 = (0x800080f0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx15_3 : σ3.regs.get? Register.x15 = some ((0#64) + sign_extend (m := 64) (0x02d#12)) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx14_3 : σ3.regs.get? Register.x14 = some (v + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_other' hobs3 Register.x14 (by decide) hx14_2
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs3 Register.x2 (by decide) hx2_2
  have hx13_3 : σ3.regs.get? Register.x13 = some v :=
    obs_alu_other' hobs3 Register.x13 (by decide) hx13_2
  have hx6_3 : σ3.regs.get? Register.x6 = some vt1 :=
    obs_alu_other' hobs3 Register.x6 (by decide) hx6_2
  have hx8_3 : σ3.regs.get? Register.x8 = some v8 :=
    obs_alu_other' hobs3 Register.x8 (by decide) hx8_2
  have hx20_3 : σ3.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs3 Register.x20 (by decide) hx20_2
  have hx23_3 : σ3.regs.get? Register.x23 = some v23 :=
    obs_alu_other' hobs3 Register.x23 (by decide) hx23_2
  have hx28_3 : σ3.regs.get? Register.x28 = some v28 :=
    obs_alu_other' hobs3 Register.x28 (by decide) hx28_2
  have hx12_3 : σ3.regs.get? Register.x12 = some v12 :=
    obs_alu_other' hobs3 Register.x12 (by decide) hx12_2
  obtain ⟨vmi3, hvmi3⟩ := obs_alu_minstret hobs3
  have hmem3' : SvfprintfSliceLoaded σ3.mem := hmem3 ▸ hmem2'
  have huload3 : Vsa.Sim.Code.__umoddi3Loaded σ3.mem := hmem3 ▸ huload2
  have hcuload3 : Vsa.Sim.Code.__hidden___udivdi3Loaded σ3.mem := hmem3 ▸ hcuload2
  -- Step f0: sb a5,167(sp)  ⇒ mem[sp+167] := '-'
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_800080f0_sn4 σ3 i3 (c.steps + 1 + 1 + 1) (0x800080f0#64) vmi3 vsp ((0#64) + sign_extend (m := 64) (0x02d#12))
      hG3 hpc3 hvmi3 hx2_3 hx15_3 hmem3' rfl hlo hhiram hhiwin hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x800080f4#64) := by
    have := obs_store_pc_sn4 hobs4
    rwa [show BitVec.addInt (0x800080f0#64 : BitVec 64) 4 = (0x800080f4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_4 : σ4.regs.get? Register.x14 = some (v + sign_extend (m := 64) (0x000#12)) :=
    obs_store_other_sn4' Register.x14 hobs4 (by decide) hx14_3
  have hx13_4 : σ4.regs.get? Register.x13 = some v :=
    obs_store_other_sn4' Register.x13 hobs4 (by decide) hx13_3
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4' Register.x2 hobs4 (by decide) hx2_3
  have hx6_4 : σ4.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4' Register.x6 hobs4 (by decide) hx6_3
  have hx8_4 : σ4.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4' Register.x8 hobs4 (by decide) hx8_3
  have hx20_4 : σ4.regs.get? Register.x20 = some v20 :=
    obs_store_other_sn4' Register.x20 hobs4 (by decide) hx20_3
  have hx23_4 : σ4.regs.get? Register.x23 = some v23 :=
    obs_store_other_sn4' Register.x23 hobs4 (by decide) hx23_3
  have hx28_4 : σ4.regs.get? Register.x28 = some v28 :=
    obs_store_other_sn4' Register.x28 hobs4 (by decide) hx28_3
  have hx12_4 : σ4.regs.get? Register.x12 = some v12 :=
    obs_store_other_sn4' Register.x12 hobs4 (by decide) hx12_3
  obtain ⟨vmi4, hvmi4⟩ := obs_store_minstret_sn4 hobs4
  -- the stored sign byte: σ4.mem = (afterNextPC …).mem.insert (sp+167) (stData 1 '-')
  have hmemNP4 : (afterNextPC (afterPrelude σ3) (0x800080f0#64)).mem = σ3.mem := rfl
  have hmem4q : σ4.mem = σ3.mem.insert (vsp + sign_extend (m := 64) (0x0a7#12)).toNat
      (stData 1 ((0#64) + sign_extend (m := 64) (0x02d#12))) := by rw [hmem4, hmemNP4]
  have hsign : σ4.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]?
      = some (stData 1 ((0#64) + sign_extend (m := 64) (0x02d#12))) := by
    rw [hmem4q, Std.ExtHashMap.getElem?_insert_self]
  have hmem4loaded : SvfprintfSliceLoaded σ4.mem := by
    rw [hmem4q]
    have hbound : 0x80009000 ≤ (vsp + sign_extend (m := 64) (0x0a7#12)).toNat := by
      have : tohostAddr = 0x8001ad00 := rfl
      omega
    exact svfprintfSlice_insert_sn4 σ3.mem _ _ hbound hmem3'
  have hbound4 : 0x80009000 ≤ (vsp + sign_extend (m := 64) (0x0a7#12)).toNat := by
    have : tohostAddr = 0x8001ad00 := rfl
    omega
  have huload4 : Vsa.Sim.Code.__umoddi3Loaded σ4.mem := by
    rw [hmem4q]; exact umoddi3_insert_sn4 σ3.mem _ _ hbound4 huload3
  have hcuload4 : Vsa.Sim.Code.__hidden___udivdi3Loaded σ4.mem := by
    rw [hmem4q]; exact cudivdi3_insert_sn4 σ3.mem _ _ hbound4 hcuload3
  -- Step f4: neg a4,a4  ⇒ x14 := 0 - x14 = 0 - (v+0) = 0 - v
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_800080f4_sn4 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x800080f4#64) vmi4 (v + sign_extend (m := 64) (0x000#12))
      hG4 hpc4 hvmi4 hx14_4 hmem4loaded rfl hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x800080f8#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x800080f4#64 : BitVec 64) 4 = (0x800080f8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_5 : σ5.regs.get? Register.x14 = some ((0#64) - v) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    -- 0 - (v + sext 0) = 0 - v
    rwa [show (v + sign_extend (m := 64) (0x000#12)) = v from by
      rw [sext_zero]; exact BitVec.add_zero v] at this
  have hx13_5 : σ5.regs.get? Register.x13 = some v :=
    obs_alu_other' hobs5 Register.x13 (by decide) hx13_4
  have hx2_5 : σ5.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs5 Register.x2 (by decide) hx2_4
  have hx6_5 : σ5.regs.get? Register.x6 = some vt1 :=
    obs_alu_other' hobs5 Register.x6 (by decide) hx6_4
  have hx8_5 : σ5.regs.get? Register.x8 = some v8 :=
    obs_alu_other' hobs5 Register.x8 (by decide) hx8_4
  have hx20_5 : σ5.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs5 Register.x20 (by decide) hx20_4
  have hx23_5 : σ5.regs.get? Register.x23 = some v23 :=
    obs_alu_other' hobs5 Register.x23 (by decide) hx23_4
  have hx28_5 : σ5.regs.get? Register.x28 = some v28 :=
    obs_alu_other' hobs5 Register.x28 (by decide) hx28_4
  have hx12_5 : σ5.regs.get? Register.x12 = some v12 :=
    obs_alu_other' hobs5 Register.x12 (by decide) hx12_4
  obtain ⟨vmi5, hvmi5⟩ := obs_alu_minstret hobs5
  have hmem5' : SvfprintfSliceLoaded σ5.mem := hmem5 ▸ hmem4loaded
  have huload5 : Vsa.Sim.Code.__umoddi3Loaded σ5.mem := hmem5 ▸ huload4
  have hcuload5 : Vsa.Sim.Code.__hidden___udivdi3Loaded σ5.mem := hmem5 ▸ hcuload4
  -- the sign byte is preserved by the neg (a register write, no memory change)
  have hsign5 : σ5.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]?
      = some (stData 1 ((0#64) + sign_extend (m := 64) (0x02d#12))) := by
    rw [hmem5]; exact hsign
  -- FlushPins survive the sign block: only the '-' byte at sp+167 (≥ 0x8000b000) is written
  have hfp5 : Vsa.Sim.Code.FlushPinsLoaded σ5.mem := by
    have hfp3 : Vsa.Sim.Code.FlushPinsLoaded σ3.mem := hmem3 ▸ hmem2 ▸ hmem1 ▸ hfp
    have htoh : tohostAddr = 0x8001ad00 := rfl
    have hfp4 : Vsa.Sim.Code.FlushPinsLoaded σ4.mem := by
      rw [hmem4q]
      refine Vsa.Sim.Code.flushPins_of_agree (fun a ha => ?_) hfp3
      rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]
    exact hmem5 ▸ hfp4
  -- post-widening: the five mid-registers survive the whole block
  have hkeep5 : KeepRegs midRegs5 c.σ σ5 := by
    have h0 := keep_rfl midRegs5 c.σ
    have h1 := keep_alu hobs1 (by decide) h0
    have h2 := keep_bnottaken hobs2 (by decide) h1
    have h3 := keep_alu hobs3 (by decide) h2
    have h4 := keep_store hobs4 (by decide) h3
    exact keep_alu hobs5 (by decide) h4
  -- post-widening: everything except the sign byte reads as at entry
  have hmframe : ∀ a : Nat, a ≠ (vsp + sign_extend (m := 64) (0x0a7#12)).toNat →
      σ5.mem[a]? = c.σ.mem[a]? := by
    intro a ha
    rw [hmem5, hmem4q, Std.ExtHashMap.getElem?_insert,
      if_neg (by simp only [beq_iff_eq]; omega), hmem3, hmem2, hmem1]
  refine ⟨⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩, ?_, hG5, hpc5, hx14_5, hsign5, hi5, ⟨vmi5, hvmi5⟩,
    hx13_5, hx2_5, hx6_5, hx8_5, hx20_5, hx23_5, hx28_5, hx12_5, hmem5', huload5, hcuload5, hfp5,
    hkeep5, hmframe⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans
    ((Steps.single hstep3).trans ((Steps.single hstep4).trans (Steps.single hstep5))))

/-! ## `signBlock_nonneg_step_sn4` — the nonnegative arm (one branch)

For a nonnegative argument (`bgez` taken), the sign block is skipped: `mv a4,a3`
puts the value in `x14`, then `bgez` jumps to `0x80008050` (past the sign store /
neg).  The magnitude is `x14 = v = v.toNat` directly, no sign byte written.  This
single-branch step lands at `0x80008050`. -/
theorem signBlock_nonneg_step_sn4
    (v : BitVec 64) (c : Config)
    (hG : GoodState c.σ) (hmem : SvfprintfSliceLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800080e8#64))
    (hx13 : c.σ.regs.get? Register.x13 = some v)
    (hnn : zopz0zKzJ_s v (0#64) = true)
    (hmi : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (htick : c.tick < 2) :
    ∃ c' : Config, Step c c' ∧ GoodState c'.σ ∧ c'.σ.mem = c.σ.mem ∧
      c'.σ.regs.get? Register.PC = some (0x80008050#64) ∧
      c'.tick < 2 ∧ (∃ w, c'.σ.regs.get? Register.minstret = some w) := by
  obtain ⟨vmi, hvmi⟩ := hmi
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800080e8_taken_sn4 c.σ c.tick c.steps (0x800080e8#64) vmi v hG hpc hvmi hx13 hmem rfl hnn htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  refine ⟨⟨σ1, i1, c.steps + 1⟩, hstep1, hG1, hmem1, ?_, hi1, obs_bt_minstret_sn4 hobs1⟩
  -- taken branch: PC := pc + sext imm = 0x800080e8 + sext 0x1f68 = 0x80008050
  have := obs_bt_pc_sn4 hobs1
  rwa [show (0x800080e8#64 : BitVec 64) + sign_extend (m := 64) (0x1f68#13) = (0x80008050#64 : BitVec 64) from by
    apply BitVec.eq_of_toNat_eq; decide] at this

/-! ## Remaining segments — documented composition boundary

`signBlock_neg_spec` / `signBlock_nonneg_step_sn4` land the sign segment.  To
compose the full `%lld` slice entry→return, the remaining pieces are:

1. **Two loads** `0x800080dc ld a3,0(a4)` + `ld a4,24(sp)`: a `stepObs_load`
   primitive (not yet in the step layer) would remove the `x13 = v` boundary
   hypothesis by deriving `v` from the pinned va_list slot.

2. **Loop-entry setup** `0x800080fc andi t1,… → 0x80008100 li a5,9 →
   0x80008104 bltu a5,a4 → 0x800082c8 …`: the `bltu` splits the single-digit fast
   path (`magnitude ≤ 9`, emits one digit at `sp+347`, lands at the length/flush
   code) from the multi-digit path (`0x800082c8` sets `s6=sp+348`, `s9=s6`, `s7=0`,
   `s0=magnitude`, `j 0x8000831c` — one mod-emit that establishes `LSt g top m 0`
   at the loop head `0x800082fc`).  With `x14 = (0#64)-v` (negatives, from
   `signBlock_neg_spec`) or `x14 = v` (nonnegatives) as the magnitude, this
   segment feeds `decimalLoop_spec`'s precondition `DLI g top m`
   (`SnprintfSpec3.lean`) with `m = (magnitude).toNat`.

3. **Flush** `0x80008a80 … 0x80008af8 jal __ssprint_r`: assembles the iov
   (`sp+224`) from the sign byte (`sp+167`), the digit window `[cursor, sp+348)`,
   and padding, then `__ssprint_r → __ssputs_r → memmove` copies it into the
   caller buffer.  Per `MemcpySpec`'s `MemInv` described-update pattern, the copy
   `Q` is: for each `j < len`, `buf[base + j] = (iov bytes)[j]`, where the iov
   bytes are `['-'] ++ (digit window MSB-first)` for negatives — i.e. exactly
   `(intToString v.toInt).toUTF8` (`intToString_signblock_sn4` +
   `loopDigits_natToString`, `SnprintfSpec.lean`).  The `'-'` at `sp+167` is
   copied **first** (prepended), the digit window after: the buffer-vs-flush
   finding realised.

The value-level correspondence that ties (2)+(3) to the spec is
`intToString_signblock_sn4` (this file): `intToString v.toInt` is the sign prefix
concatenated with `natToString` of the magnitude, the two arms matching the
`bgez` split byte-exactly, `INT64_MIN`-safe via `neg_out_toNat_sn4`/`neg_magnitude`.
-/

end Vsa.Sim
