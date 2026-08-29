import Vsa.Sim.SnprintfSpec2

/-!
# M3 Layer-3 — `decimalLoop_spec` : closing the digit-emission loop

Session-3 file.  Builds on the machine-stepping layer of `SnprintfSpec2.lean`
(the per-site `StepObs` battery, `umoddi3_frame_spec`, `BufInv`/`bufinv_store`,
the loop-head predicate `LSt`, the arithmetic bridges) and the strengthened
`udivdi3_post` (`DivLoops.lean`, session 3) that now surfaces `∃ v, x12/x13 =
some v`.  That strengthening is what discharges the documented obligation: the
second callee call (`__umoddi3` at `0x80008324`) needs `x12`/`x13` defined at its
entry, and the first callee (`__hidden___udivdi3`) leaves them so.

Contents:

* `loop_iter` — one iteration of the do-while body `[0x800082fc, 0x80008338]`
  under the guard `m / 10^p > 9`, stepping `LSt g top m p` to `LSt g top m (p+1)`;
* `decimalLoop_spec` — the `Triple.loop` assembly: measure `(m / 10^p)`
  PC-guarded at the loop head `0x800082fc`, exit edge the `bgeu`-taken at
  `0x80008318` (when `m / 10^p ≤ 9`) landing at `0x80008358` with the complete
  `loopDigits (m+1) m = natDigits (m+1) m` digit string in the descending buffer
  (`BufInv`), digit count `s7 = p + 1`.

## Buffer / cursor arithmetic (at `LSt g top m p`)

`s9 = top − p` (cursor above last-written byte), `s10 = top − 1 − p` (next slot),
`s7 = p + 1` (count), `s0 = m / 10^p` (running value).  One iteration:
`8310 mv s9,s10` sets `s9 = top−1−p`; `832c sb a0,-1(s9)` writes digit `p+1` at
`top−1−p−1 = top−1−(p+1)` (exactly `BufInv`'s slot for index `p+1`);
`8330 addi s10,s9,-1` sets `s10 = top−1−(p+1)`; so at `LSt (p+1)`:
`s9 = top−(p+1) = top−1−p`, `s10 = top−1−(p+1)`.  ✓
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded SvfprintfSliceLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Store read-back helpers (`sigmaPost_store`)

`SnprintfSites`' `sb` site (`site_8000832c_sn`) delivers `ReadsLikePost σ'
(sigmaPost_store …)`.  These mirror the `obs_*` consumers for the STORE class,
built directly on `ReadsLikePost` + `get?_sigmaPost_store` (`StepStore.lean`). -/

theorem obs_store_pc_sn3 {σ' σ : MState} {pc vm : BitVec 64}
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

theorem obs_store_other_sn3 {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)} (R : Register) {w : RegisterType R}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m'))
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w := by
  rw [hobs.1 R hmc hmt hmi]
  rw [get?_sigmaPost_store σ pc vm m' R h1 h2 h4 h5]; exact hσ

theorem obs_store_minstret_sn3 {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, ?_⟩
  rw [hobs.1 Register.minstret (by decide) (by decide) (by decide)]
  show ((((sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-- Loop-live frame across the STORE step (`832c sb`): non-written registers read
back unchanged (the store touches memory + PC/minstret only). -/
theorem frameL_store_sn3 {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register)
    (hR : NotWrittenL R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := notWrittenL_ctrl hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_store σ pc vm m' R hmi hpc hnpc hmii

/-! ## `…Loaded` preserved by a byte store above the code region

The descending buffer sits above the `tohost` window (`TopOk`), hence above **all**
code (`< 0x80008b11 < 0x8001ad10 = tohostAddr+16`).  A single byte insert at such a
key leaves every code-byte pin intact.  `getElem_transfer_sn3` is the per-byte
read-over-write; the three wrappers thread it through each `…Loaded` conjunction. -/

theorem getElem_transfer_sn3 (mem : Std.ExtHashMap Nat (BitVec 8)) (k a : Nat) (v b : BitVec 8)
    (hne : k ≠ a) (h : mem[a]? = some b) : (mem.insert k v)[a]? = some b := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp [hne])]; exact h

/-- Read-over-write below the store key: a byte store at `k ≥ 0x80009000` leaves
every read at a code address `a < 0x80009000` unchanged.  Used as a conditional
rewrite (`simp (disch := omega)`) so the `…Loaded` conjunctions transfer in one
pass instead of goal-by-goal. -/
theorem getElem?_insert_above_sn3 (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80009000 ≤ k) (a : Nat) (ha : a < 0x80009000) :
    (mem.insert k v)[a]? = mem[a]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-- `SvfprintfSliceLoaded` survives a byte store at a key above the code region
(`0x80009000 ≤ k`; the slice spans `[0x80007654, 0x80008b11)`). -/
theorem svfprintfSlice_insert_sn3 (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
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
  simp (disch := omega) only [getElem?_insert_above_sn3 mem k v hk]
  exact h

/-- `__umoddi3Loaded` survives a byte store above the code region (the wrapper
spans `[0x800046f4, 0x800046fd)`; `0x80009000 ≤ k` clears it). -/
theorem umoddi3_insert_sn3 (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80009000 ≤ k) (h : Vsa.Sim.Code.__umoddi3Loaded mem) :
    Vsa.Sim.Code.__umoddi3Loaded (mem.insert k v) := by
  have c0 := Vsa.Sim.Code.__umoddi3_chunk0 h
  show Vsa.Sim.Code.__umoddi3Chunk0 (mem.insert k v)
  simp only [Vsa.Sim.Code.__umoddi3Chunk0] at c0 ⊢
  simp (disch := omega) only [getElem?_insert_above_sn3 mem k v hk]
  exact c0

/-- `__hidden___udivdi3Loaded` survives a byte store above the code region (the
core spans `[0x800046ac, 0x800046f4)`; `0x80009000 ≤ k` clears it). -/
theorem cudivdi3_insert_sn3 (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x80009000 ≤ k) (h : __hidden___udivdi3Loaded mem) :
    __hidden___udivdi3Loaded (mem.insert k v) := by
  obtain ⟨c0, c1⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [Vsa.Sim.Code.__hidden___udivdi3Chunk0] at c0 ⊢
    simp (disch := omega) only [getElem?_insert_above_sn3 mem k v hk]
    exact c0
  · simp only [Vsa.Sim.Code.__hidden___udivdi3Chunk1] at c1 ⊢
    simp (disch := omega) only [getElem?_insert_above_sn3 mem k v hk]
    exact c1

/-! ## Small ALU value bridges -/

/-- `mv`/`addi rd,rs,0` folds `v + sext 0 = v`. -/
theorem addi0_sn3 (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [sext_zero]; exact BitVec.add_zero v

/-- `addiw rd,rs,1` on `ofNat a` (with `a+1 < 2^31`, so the 32-bit result
sign-extends transparently): `sext32(ofNat a + sext 1) = ofNat (a+1)`. -/
theorem addiw1_sn3 (a : Nat) (h : a + 1 < 2^31) :
    (sign_extend (m := 64) (Sail.BitVec.extractLsb ((BitVec.ofNat 64 a) + sign_extend (m := 64) (0x001#12)) 31 0))
      = BitVec.ofNat 64 (a+1) := by
  apply BitVec.eq_of_toNat_eq
  have ha : a < 2^64 := by omega
  have hsext1 : (sign_extend (m := 64) (0x001#12) : BitVec 64).toNat = 1 := by decide
  have hsum : ((BitVec.ofNat 64 a) + sign_extend (m := 64) (0x001#12)).toNat = a + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, hsext1, Nat.mod_eq_of_lt (by omega)]
  -- the 32-bit slice `extractLsb 31 0 = extractLsb' 0 32 = ofNat 32 (sum >>> 0)`
  show ((Sail.BitVec.extractLsb ((BitVec.ofNat 64 a) + sign_extend (m := 64) (0x001#12)) 31 0).signExtend 64).toNat
    = (BitVec.ofNat 64 (a+1)).toNat
  have hslice : (Sail.BitVec.extractLsb ((BitVec.ofNat 64 a) + sign_extend (m := 64) (0x001#12)) 31 0)
      = BitVec.ofNat 32 (a+1) := by
    show (((BitVec.ofNat 64 a) + sign_extend (m := 64) (0x001#12)).extractLsb 31 0) = _
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    show (BitVec.ofNat (31-0+1) ((((BitVec.ofNat 64 a) + sign_extend (m := 64) (0x001#12)).toNat) >>> 0)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.shiftRight_zero, hsum]
  rw [hslice, BitVec.toNat_signExtend]
  have hmsb : (BitVec.ofNat 32 (a+1)).msb = false := by
    rw [BitVec.msb_eq_getLsbD_last]
    simp only [BitVec.getLsbD_ofNat]
    rw [Nat.testBit_lt_two_pow (by omega)]
    rfl
  rw [hmsb, if_neg (by simp), Nat.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-! ## Loop-live frame across the two branch classes -/

theorem frameL_btaken_sn3 {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    (hR : NotWrittenL R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := notWrittenL_ctrl hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_taken σ pc vm imm R hmi hpc hnpc hmii

theorem frameL_bnottaken_sn3 {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWrittenL R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := notWrittenL_ctrl hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hmi hpc hnpc hmii

/-! ## Guard bridge (Nat `9 < k` ⇒ `bgeu 9 k = false`) -/

/-- If `9 < k < 2^64` then the machine `bgeu 9#64 (ofNat 64 k)` is **false** (loop
continues).  Uses `bgeu_true`'s contrapositive on `bgeu_cases`. -/
theorem bgeu9_false_sn3 (k : Nat) (h9 : 9 < k) (hk : k < 2^64) :
    zopz0zKzJ_u (9#64) (BitVec.ofNat 64 k) = false := by
  rcases bgeu_cases (9#64) (BitVec.ofNat 64 k) with hb | hb
  · exfalso
    have := bgeu_true (9#64) (BitVec.ofNat 64 k) hb
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, show (9#64 : BitVec 64).toNat = 9 from by decide] at this
    omega
  · exact hb

/-- If `k ≤ 9` then `bgeu 9#64 (ofNat 64 k) = true` (loop exits). -/
theorem bgeu9_true_sn3 (k : Nat) (h9 : k ≤ 9) :
    zopz0zKzJ_u (9#64) (BitVec.ofNat 64 k) = true := by
  rcases bgeu_cases (9#64) (BitVec.ofNat 64 k) with hb | hb
  · exact hb
  · exfalso
    have := bgeu_false (9#64) (BitVec.ofNat 64 k) hb
    simp only [BitVec.toNat_ofNat] at this
    omega

/-! ## `top` window hypotheses

The descending buffer is a stack region; the `sb` site needs the write address in
RAM and disjoint from the `tohost` window.  With `m < 2^64` there are at most 20
digits, so `p ≤ 19`; the caller pins `top` in a window comfortably clearing both
bounds.  We package the constraints `loop_iter`/`decimalLoop_spec` propagate. -/

/-- The buffer top is a valid descending-write base placed **above** the `tohost`
device window (`tohostAddr + 16 + 64 ≤ top`), hence above all code (svfprintf
slice ends at `0x80008b10`, the div cluster far below, both `< tohostAddr`), and
`top < 2^32` so stores stay in RAM and never wrap.  With `m < 2^64` there are ≤20
digit slots, all within the ≥64-byte slack, all above `tohost+16` (so the `sb`
disjointness holds) and above the code region (so `…Loaded` pins survive). -/
def TopOk (top : BitVec 64) : Prop :=
  tohostAddr + 16 + 64 ≤ top.toNat ∧ top.toNat + 1 ≤ 0x100000000

/-! ## Loop-state-preserving `__umoddi3` spec

`umoddi3_frame_spec` (`SnprintfSpec2`) preserves only `NotWrittenL` registers,
which **excludes** the loop-state set `{x8, x22, x23, x25, x26, x27}`.  Those
registers are nonetheless preserved by `__umoddi3` physically (the wrapper writes
only `x5, x10, x11`, and the inner `__hidden___udivdi3` preserves them via its
`NotWritten` frame — `NotWritten` does **not** exclude `x8`/…).  We reprove the
wrapper here threading those six registers explicitly, so the decimal loop can
re-establish `LSt` after the mod call. -/
theorem umoddi3_loopframe_spec (g : (R : Register) → Option (RegisterType R))
    (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (v8 v23 v25 v27 : BitVec 64) (c : Config)
    (hpre : umoddi3_pre n d r m0 c)
    (h8 : c.σ.regs.get? Register.x8 = some v8)
    (h23 : c.σ.regs.get? Register.x23 = some v23) (h25 : c.σ.regs.get? Register.x25 = some v25)
    (h27 : c.σ.regs.get? Register.x27 = some v27)
    (hgframe : ∀ R, NotWrittenL R → c.σ.regs.get? R = g R) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧ c'.σ.mem = m0 ∧
      c'.σ.regs.get? Register.PC = some r ∧ c'.σ.regs.get? Register.x10 = some (n % d) ∧
      c'.tick < 2 ∧ (∃ v, c'.σ.regs.get? Register.minstret = some v) ∧
      c'.σ.regs.get? Register.x8 = some v8 ∧
      c'.σ.regs.get? Register.x23 = some v23 ∧ c'.σ.regs.get? Register.x25 = some v25 ∧
      c'.σ.regs.get? Register.x27 = some v27 ∧
      (∃ v, c'.σ.regs.get? Register.x12 = some v) ∧ (∃ v, c'.σ.regs.get? Register.x13 = some v) ∧
      (∃ v, c'.σ.regs.get? Register.x1 = some v) ∧
      (∀ R, NotWrittenL R → c'.σ.regs.get? R = g R) := by
  obtain ⟨hG, huload, hcload, hmem, hpc, hn, hd, hr, ⟨vmi, hmi⟩,
    ⟨v12, hh12⟩, ⟨v13, hh13⟩, htick, hdpos, halign⟩ := hpre
  -- f4: mv t0,ra ⇒ x5 := r
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site2_800046f4 c.σ c.tick c.steps (0x800046f4#64) vmi r hG hpc hmi hr (hmem ▸ huload) rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x800046f8#64) := obs_alu_pc hobs1
  have hx5_1 : σ1.regs.get? Register.x5 = some r := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 r] at this
  have hn1 : σ1.regs.get? Register.x10 = some n :=
    obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn
  have hd1 : σ1.regs.get? Register.x11 = some d :=
    obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd
  have h12_1 : σ1.regs.get? Register.x12 = some v12 :=
    obs_alu_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hh12
  have h13_1 : σ1.regs.get? Register.x13 = some v13 :=
    obs_alu_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hh13
  have h8_1 : σ1.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h8
  have h23_1 : σ1.regs.get? Register.x23 = some v23 :=
    obs_alu_other hobs1 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h23
  have h25_1 : σ1.regs.get? Register.x25 = some v25 :=
    obs_alu_other hobs1 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h25
  have h27_1 : σ1.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs1 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h27
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hmem1q : σ1.mem = m0 := by rw [hmem1]; exact hmem
  have huload1 : Vsa.Sim.Code.__umoddi3Loaded σ1.mem := hmem1 ▸ hmem ▸ huload
  have hcload1 : __hidden___udivdi3Loaded σ1.mem := hmem1 ▸ hmem ▸ hcload
  -- f8: jal udivdi3 ⇒ x1 := fc, PC := 46ac
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site2_800046f8 σ1 i1 (c.steps + 1) (0x800046f8#64) vmi1 hG1 hpc1 hmi1 huload1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x800046ac#64) := by
    have := obs_jal_pc hobs2
    rwa [show (0x800046f8#64 : BitVec 64) + sign_extend (m := 64) (0x1fffb4#21)
      = (0x800046ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx1_2 : σ2.regs.get? Register.x1 = some (0x800046fc#64) := by
    have := obs_jal_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x800046f8#64 : BitVec 64) 4 = (0x800046fc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hn2 : σ2.regs.get? Register.x10 = some n :=
    obs_jal_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn1
  have hd2 : σ2.regs.get? Register.x11 = some d :=
    obs_jal_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd1
  have h12_2 : σ2.regs.get? Register.x12 = some v12 :=
    obs_jal_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h12_1
  have h13_2 : σ2.regs.get? Register.x13 = some v13 :=
    obs_jal_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h13_1
  obtain ⟨vmi2, hmi2⟩ := obs_jal_minstret hobs2
  have hmem2q : σ2.mem = m0 := by rw [hmem2]; exact hmem1q
  have huload2 : Vsa.Sim.Code.__umoddi3Loaded σ2.mem := hmem2 ▸ huload1
  have hcload2 : __hidden___udivdi3Loaded σ2.mem := hmem2 ▸ hcload1
  -- loop-state regs carried through the jal (rd = x1)
  have h8_2 : σ2.regs.get? Register.x8 = some v8 :=
    obs_jal_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h8_1
  have h23_2 : σ2.regs.get? Register.x23 = some v23 :=
    obs_jal_other hobs2 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h23_1
  have h25_2 : σ2.regs.get? Register.x25 = some v25 :=
    obs_jal_other hobs2 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h25_1
  have h27_2 : σ2.regs.get? Register.x27 = some v27 :=
    obs_jal_other hobs2 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h27_1
  -- core: udivdi3 from 46ac, r = 46fc
  have hcorepre : udivdi3_pre (fun R => σ2.regs.get? R) n d (0x800046fc#64) m0 σ2.sailOutput ⟨σ2, i2, c.steps + 1 + 1⟩ := by
    refine ⟨⟨v12, v13, ?_⟩, hdpos, by decide⟩
    exact {
      good := hG2, loaded := by rw [show (⟨σ2,i2,c.steps+1+1⟩ : Config).σ.mem = σ2.mem from rfl]; exact hcload2,
      mem := hmem2q, sailOut := rfl, pc := hpc2, a0 := hn2, a1 := hd2, a2 := h12_2, a3 := h13_2,
      ra := hx1_2, minstret := ⟨vmi2, hmi2⟩, tick := hi2, hframe := fun R _ => rfl }
  obtain ⟨c3, hs3, hG3, hmem3, _hout3, hpc3, _hq3, hrem3, _hra3, htick3, hframe3, hx12_3e, hx13_3e⟩ :=
    udivdi3_spec (fun R => σ2.regs.get? R) n d (0x800046fc#64) m0 σ2.sailOutput ⟨σ2, i2, c.steps + 1 + 1⟩ hcorepre
  have hmem3q : c3.σ.mem = m0 := hmem3
  have huload3 : Vsa.Sim.Code.__umoddi3Loaded c3.σ.mem := by rw [hmem3q, ← hmem]; exact huload
  obtain ⟨vmi3, hmi3⟩ := hG3.minstret
  -- loop-state preserved by the core (NotWritten covers them)
  have h8_3 : c3.σ.regs.get? Register.x8 = some v8 := by rw [hframe3 Register.x8 (by decide)]; exact h8_2
  have h23_3 : c3.σ.regs.get? Register.x23 = some v23 := by rw [hframe3 Register.x23 (by decide)]; exact h23_2
  have h25_3 : c3.σ.regs.get? Register.x25 = some v25 := by rw [hframe3 Register.x25 (by decide)]; exact h25_2
  have h27_3 : c3.σ.regs.get? Register.x27 = some v27 := by rw [hframe3 Register.x27 (by decide)]; exact h27_2
  -- x5 preserved by the core (NotWritten covers x5)
  have hx5_3 : c3.σ.regs.get? Register.x5 = some r := by
    rw [hframe3 Register.x5 (by decide)]
    exact obs_jal_other hobs2 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_1
  -- fc: mv a0,a1 ⇒ x10 := n%d
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site2_800046fc c3.σ c3.tick c3.steps (0x800046fc#64) vmi3 (n % d) hG3 hpc3 hmi3 hrem3 huload3 rfl htick3
  have hstep4 : Step c3 ⟨σ4, i4, c3.steps + 1⟩ := by cases c3; exact hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80004700#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x800046fc#64 : BitVec 64) 4 = (0x80004700#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_4 : σ4.regs.get? Register.x10 = some (n % d) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 (n % d)] at this
  have hx5_4 : σ4.regs.get? Register.x5 = some r :=
    obs_alu_other hobs4 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_3
  have h8_4 : σ4.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs4 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h8_3
  have h23_4 : σ4.regs.get? Register.x23 = some v23 :=
    obs_alu_other hobs4 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h23_3
  have h25_4 : σ4.regs.get? Register.x25 = some v25 :=
    obs_alu_other hobs4 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h25_3
  have h27_4 : σ4.regs.get? Register.x27 = some v27 :=
    obs_alu_other hobs4 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h27_3
  have h12_4 : ∃ v, σ4.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_3e
    exact ⟨v, obs_alu_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have h13_4 : ∃ v, σ4.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_3e
    exact ⟨v, obs_alu_other hobs4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hmem4q : σ4.mem = m0 := by rw [hmem4]; exact hmem3q
  have huload4 : Vsa.Sim.Code.__umoddi3Loaded σ4.mem := by rw [hmem4q, ← hmem]; exact huload
  -- 4700: jr t0 ⇒ PC := r
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halign]; exact halign
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site2_80004700 σ4 i4 (c3.steps + 1) (0x80004700#64) vmi4 r hG4 hpc4 hmi4 hx5_4 huload4 rfl htgt hi4
  have hstep5 : Step ⟨σ4, i4, c3.steps + 1⟩ ⟨σ5, i5, c3.steps + 1 + 1⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some r := by rw [obs_jr_pc hobs5, ret_tgt r halign]
  have hx10_5 : σ5.regs.get? Register.x10 = some (n % d) :=
    obs_jr_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_4
  have h8_5 : σ5.regs.get? Register.x8 = some v8 :=
    obs_jr_other hobs5 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h8_4
  have h23_5 : σ5.regs.get? Register.x23 = some v23 :=
    obs_jr_other hobs5 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h23_4
  have h25_5 : σ5.regs.get? Register.x25 = some v25 :=
    obs_jr_other hobs5 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h25_4
  have h27_5 : σ5.regs.get? Register.x27 = some v27 :=
    obs_jr_other hobs5 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h27_4
  have h12_5 : ∃ v, σ5.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := h12_4
    exact ⟨v, obs_jr_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have h13_5 : ∃ v, σ5.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := h13_4
    exact ⟨v, obs_jr_other hobs5 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi5, hmi5⟩ := hG5.minstret
  have hmem5q : σ5.mem = m0 := by rw [hmem5]; exact hmem4q
  -- x1 = 46fc (set by the wrapper's jal, untouched by mv a0,a1 and jr t0)
  have hx1_4 : σ4.regs.get? Register.x1 = some (0x800046fc#64) :=
    obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _hra3
  have hx1_5 : σ5.regs.get? Register.x1 = some (0x800046fc#64) :=
    obs_jr_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_4
  -- NotWrittenL frame chain: σ5 ← σ4 ← c3 ← σ2 ← σ1 ← c.σ = g
  have hframeChain : ∀ R, NotWrittenL R → σ5.regs.get? R = g R := by
    intro R hR
    have e5 : σ5.regs.get? R = σ4.regs.get? R := frameL_jr hobs5 R hR
    have e4 : σ4.regs.get? R = c3.σ.regs.get? R := frameL_alu hobs4 R (by obtain ⟨h10, _⟩ := hR; exact h10) hR
    have e3 : c3.σ.regs.get? R = σ2.regs.get? R := hframe3 R (notWrittenL_toCore hR)
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frameL_jal hobs2 R (by obtain ⟨_,_,_,_,hx1,_⟩ := hR; exact hx1) hR
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frameL_alu hobs1 R (by obtain ⟨_,_,_,_,_,hx5,_⟩ := hR; exact hx5) hR
    rw [e5, e4, e3, e2, e1]; exact hgframe R hR
  refine ⟨⟨σ5, i5, c3.steps + 1 + 1⟩, ?_, hG5, hmem5q, hpc5, hx10_5, hi5, ⟨vmi5, hmi5⟩,
    h8_5, h23_5, h25_5, h27_5, h12_5, h13_5, ⟨_, hx1_5⟩, hframeChain⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans
    (hs3.trans ((Steps.single hstep4).trans (Steps.single hstep5))))

/-! ## One loop iteration (`loop_iter`)

From `LSt g top m p` with guard `m / 10^p > 9`, step the 16-instruction body in
program order to `LSt g top m (p+1)`.  The two callee calls are composed via
`udivdi3_spec` (now surfacing `x12`/`x13`) and `umoddi3_frame_spec`. -/
/-- With `m < 2^64`, a live guard `9 < m / 10^p` bounds the digit index:
`p + 2 ≤ 20` (64-bit numbers have at most 20 decimal digits). -/
theorem p_bound_sn3 (m p : Nat) (hm : m < 2^64) (hguard : 9 < m / 10^p) : p + 2 ≤ 20 := by
  rcases Nat.lt_or_ge p 19 with hp | hp
  · omega
  · exfalso
    have h10p : 10 ≤ m / 10 ^ p := by omega
    have hmul : 10 ^ p * 10 ≤ m :=
      Nat.le_trans (Nat.mul_le_mul_left (10 ^ p) h10p) (Nat.mul_div_le m (10 ^ p))
    have hpow : (10:Nat) ^ 19 * 10 ≤ 10 ^ p * 10 :=
      Nat.mul_le_mul_right 10 (Nat.pow_le_pow_right (by decide) hp)
    exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans hpow hmul) hm) (by decide)

theorem loop_iter (g : (R : Register) → Option (RegisterType R))
    (top : BitVec 64) (m p : Nat) (hm : m < 2^64) (htop : TopOk top)
    (hguard : 9 < m / 10^p) (c : Config) (hSt : LSt g top m p c) :
    ∃ c', Steps c c' ∧ LSt g top m (p+1) c' ∧
      c'.σ.mem = c.σ.mem.insert (top.toNat - 1 - (p+1))
        (BitVec.ofNat 8 (48 + (m / 10^(p+1)) % 10)) := by
  obtain ⟨htlo, sthi⟩ := htop
  have htohv : tohostAddr = 0x8001ad00 := rfl
  -- shorthand digit / value facts
  have hmp : m / 10^p < 2^64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm
  have hmp1 : m / 10^(p+1) < 2^64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm
  have htop_lt : top.toNat < 2^64 := top.isLt
  -- p ≤ 19 (m < 2^64 ⇒ m/10^p > 9 forces p small, but we only need p+1 ≤ top slack)
  -- running-value / cursor abbreviations at LSt p
  obtain ⟨vmi0, hmi0⟩ := hSt.minstret
  -- === 82fc: mv a0,s0  ⇒ x10 := m/10^p ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800082fc_sn c.σ c.tick c.steps (0x800082fc#64) vmi0 (BitVec.ofNat 64 (m/10^p))
      hSt.good hSt.pc hmi0 hSt.s0 hSt.loaded rfl hSt.tick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80008300#64) := obs_alu_pc hobs1
  have hx10_1 : σ1.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^p)) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 (BitVec.ofNat 64 (m/10^p))] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hmem1q : σ1.mem = c.σ.mem := hmem1
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hSt.loaded
  have hcuload1 : __hidden___udivdi3Loaded σ1.mem := hmem1 ▸ hSt.culoaded
  have huload1 : Vsa.Sim.Code.__umoddi3Loaded σ1.mem := hmem1 ▸ hSt.uloaded
  -- frame σ1 = c.σ on NotWrittenL
  have hf1 : ∀ R, NotWrittenL R → σ1.regs.get? R = c.σ.regs.get? R := fun R hR =>
    frameL_alu hobs1 R (by obtain ⟨h10, _⟩ := hR; exact h10) hR
  -- carry loop-state regs (s0=x8, s10=x26, s7=x23, s11=x27) through 82fc (rd=x10)
  have s0_1 : σ1.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_alu_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.s0
  have s10_1 : σ1.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs1 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.s10
  have s7_1 : σ1.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs1 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.s7
  have s11_1 : σ1.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs1 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.s11
  -- === 8300: li a1,10 ⇒ x11 := 10 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80008300_sn σ1 i1 (c.steps+1) (0x80008300#64) vmi1 hG1 hpc1 hmi1 hload1 rfl hi1
  have hstep2 : Step ⟨σ1,i1,c.steps+1⟩ ⟨σ2,i2,c.steps+1+1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80008304#64) := obs_alu_pc hobs2
  have hx11_2 : σ2.regs.get? Register.x11 = some (10#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [li10] at this
  have hx10_2 : σ2.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hmem2q : σ2.mem = c.σ.mem := by rw [hmem2]; exact hmem1q
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  have hcuload2 : __hidden___udivdi3Loaded σ2.mem := hmem2 ▸ hcuload1
  have huload2 : Vsa.Sim.Code.__umoddi3Loaded σ2.mem := hmem2 ▸ huload1
  have hf2 : ∀ R, NotWrittenL R → σ2.regs.get? R = σ1.regs.get? R := fun R hR =>
    frameL_alu hobs2 R (by obtain ⟨_, h11, _⟩ := hR; exact h11) hR
  -- carry loop-state through 8300 (rd=x11)
  have s0_2 : σ2.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_alu_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s0_1
  have s10_2 : σ2.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs2 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s10_1
  have s7_2 : σ2.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs2 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s7_1
  have s11_2 : σ2.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs2 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s11_1
  -- x12/x13 defined at σ2 (from LSt via frame — x12/x13 are in NotWrittenL? NO)
  -- x12/x13 are NOT in NotWrittenL; they are unwritten by the two ALU steps, so read them directly.
  obtain ⟨v12_0, h12_0⟩ := hSt.x12
  obtain ⟨v13_0, h13_0⟩ := hSt.x13
  have h12_1 : σ1.regs.get? Register.x12 = some v12_0 :=
    obs_alu_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h12_0
  have h13_1 : σ1.regs.get? Register.x13 = some v13_0 :=
    obs_alu_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h13_0
  have h12_2 : σ2.regs.get? Register.x12 = some v12_0 :=
    obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h12_1
  have h13_2 : σ2.regs.get? Register.x13 = some v13_0 :=
    obs_alu_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h13_1
  -- x1 defined at σ2 (from LSt, but x1 IS in NotWrittenL — frame it)
  obtain ⟨v1_0, h1_0⟩ := hSt.x1
  -- === 8304: jal __hidden___udivdi3 ⇒ x1 := 8308, PC := 46ac ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80008304_sn σ2 i2 (c.steps+1+1) (0x80008304#64) vmi2 hG2 hpc2 hmi2 hload2 rfl hi2
  have hstep3 : Step ⟨σ2,i2,c.steps+1+1⟩ ⟨σ3,i3,c.steps+1+1+1⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x800046ac#64) := by
    have := obs_jal_pc hobs3
    rwa [show (0x80008304#64 : BitVec 64) + sign_extend (m := 64) (0x1fc3a8#21)
      = (0x800046ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx1_3 : σ3.regs.get? Register.x1 = some (0x80008308#64) := by
    have := obs_jal_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80008304#64 : BitVec 64) 4 = (0x80008308#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_3 : σ3.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_jal_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_2
  have hx11_3 : σ3.regs.get? Register.x11 = some (10#64) :=
    obs_jal_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_2
  have h12_3 : σ3.regs.get? Register.x12 = some v12_0 :=
    obs_jal_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h12_2
  have h13_3 : σ3.regs.get? Register.x13 = some v13_0 :=
    obs_jal_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h13_2
  obtain ⟨vmi3, hmi3⟩ := obs_jal_minstret hobs3
  have hmem3q : σ3.mem = c.σ.mem := by rw [hmem3]; exact hmem2q
  have hload3 : SvfprintfSliceLoaded σ3.mem := hmem3 ▸ hload2
  have hcuload3 : __hidden___udivdi3Loaded σ3.mem := hmem3 ▸ hcuload2
  have huload3 : Vsa.Sim.Code.__umoddi3Loaded σ3.mem := hmem3 ▸ huload2
  have hf3 : ∀ R, NotWrittenL R → σ3.regs.get? R = σ2.regs.get? R := fun R hR =>
    frameL_jal hobs3 R (by obtain ⟨_, _, _, _, hx1, _⟩ := hR; exact hx1) hR
  -- carry loop-state through 8304 (jal, rd=x1)
  have s0_3 : σ3.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_jal_other hobs3 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s0_2
  have s10_3 : σ3.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_jal_other hobs3 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s10_2
  have s7_3 : σ3.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_jal_other hobs3 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s7_2
  have s11_3 : σ3.regs.get? Register.x27 = some (0#64) :=
    obs_jal_other hobs3 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s11_2
  -- === core: udivdi3_spec from 46ac (n = m/10^p, d = 10, r = 8308) ===
  -- 10#64 = (m/10^p) argument: state x11 = 10; treat d := 10#64
  have hdpos : 0 < (10#64 : BitVec 64).toNat := by decide
  have hcorepre : udivdi3_pre (fun R => σ3.regs.get? R) (BitVec.ofNat 64 (m/10^p)) (10#64)
      (0x80008308#64) c.σ.mem σ3.sailOutput ⟨σ3, i3, c.steps+1+1+1⟩ := by
    refine ⟨⟨v12_0, v13_0, ?_⟩, hdpos, by decide⟩
    exact {
      good := hG3, loaded := by rw [show (⟨σ3,i3,c.steps+1+1+1⟩ : Config).σ.mem = σ3.mem from rfl]; exact hcuload3,
      mem := hmem3q, sailOut := rfl, pc := hpc3, a0 := hx10_3, a1 := hx11_3, a2 := h12_3, a3 := h13_3,
      ra := hx1_3, minstret := ⟨vmi3, hmi3⟩, tick := hi3, hframe := fun R _ => rfl }
  obtain ⟨c4, hs4, hG4, hmem4, _hout4, hpc4, hq4, _hrem4, hra4, htick4, hframe4, hx12_4e, hx13_4e⟩ :=
    udivdi3_spec (fun R => σ3.regs.get? R) (BitVec.ofNat 64 (m/10^p)) (10#64) (0x80008308#64) c.σ.mem σ3.sailOutput
      ⟨σ3, i3, c.steps+1+1+1⟩ hcorepre
  -- x10 = (m/10^p) / 10 = m/10^(p+1)
  have hq4' : c4.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^(p+1))) := by
    rw [hq4]; congr 1; exact divstep m p hm
  have hmem4q : c4.σ.mem = c.σ.mem := hmem4
  have hload4 : SvfprintfSliceLoaded c4.σ.mem := hmem4q ▸ hSt.loaded
  have hcuload4 : __hidden___udivdi3Loaded c4.σ.mem := hmem4q ▸ hSt.culoaded
  have huload4 : Vsa.Sim.Code.__umoddi3Loaded c4.σ.mem := hmem4q ▸ hSt.uloaded
  -- frame σ3 → c4 on NotWrittenL (core preserves NotWritten ⊇ NotWrittenL's core part)
  have hframe4L : ∀ R, NotWrittenL R → c4.σ.regs.get? R = σ3.regs.get? R := fun R hR =>
    hframe4 R (notWrittenL_toCore hR)
  -- Recover loop-state regs at c4: they are OUTSIDE the core's write set (`NotWritten`),
  -- so the core's blanket frame `hframe4` preserves them from σ3.
  have hs0_4 : c4.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^p)) := by
    rw [hframe4 Register.x8 (by decide)]; exact s0_3
  have hs10_4 : c4.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-p)) := by
    rw [hframe4 Register.x26 (by decide)]; exact s10_3
  have hs7_4 : c4.σ.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) := by
    rw [hframe4 Register.x23 (by decide)]; exact s7_3
  have hs11_4 : c4.σ.regs.get? Register.x27 = some (0#64) := by
    rw [hframe4 Register.x27 (by decide)]; exact s11_3
  have hbufinv4 : BufInv top m (p+1) c4.σ.mem := by rw [hmem4q]; exact hSt.bufinv
  obtain ⟨vmi4, hmi4⟩ := hG4.minstret
  -- decompose c4 into σ4 for further site stepping
  -- === 8308: mv s6,s0 ⇒ x22 := m/10^p ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80008308_sn c4.σ c4.tick c4.steps (0x80008308#64) vmi4 (BitVec.ofNat 64 (m/10^p))
      hG4 hpc4 hmi4 hs0_4 hload4 rfl htick4
  have hstep5 : Step c4 ⟨σ5,i5,c4.steps+1⟩ := by cases c4; exact hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000830c#64) := obs_alu_pc hobs5
  have hx22_5 : σ5.regs.get? Register.x22 = some (BitVec.ofNat 64 (m/10^p)) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 (BitVec.ofNat 64 (m/10^p))] at this
  have hx10_5 : σ5.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_alu_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hq4'
  have hs10_5 : σ5.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs5 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs10_4
  have hs7_5 : σ5.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs5 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_4
  have hs11_5 : σ5.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs5 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11_4
  have hx12_5 : ∃ v, σ5.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_4e
    exact ⟨v, obs_alu_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_5 : ∃ v, σ5.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_4e
    exact ⟨v, obs_alu_other hobs5 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hmem5q : σ5.mem = c.σ.mem := by rw [hmem5]; exact hmem4q
  have hload5 : SvfprintfSliceLoaded σ5.mem := hmem5 ▸ hload4
  have hcuload5 : __hidden___udivdi3Loaded σ5.mem := hmem5 ▸ hcuload4
  have huload5 : Vsa.Sim.Code.__umoddi3Loaded σ5.mem := hmem5 ▸ huload4
  have hbufinv5 : BufInv top m (p+1) σ5.mem := by rw [hmem5]; exact hbufinv4
  -- === 830c: li a5,9 ⇒ x15 := 9 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_8000830c_sn σ5 i5 (c4.steps+1) (0x8000830c#64) vmi5 hG5 hpc5 hmi5 hload5 rfl hi5
  have hstep6 : Step ⟨σ5,i5,c4.steps+1⟩ ⟨σ6,i6,c4.steps+1+1⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x80008310#64) := obs_alu_pc hobs6
  have hx15_6 : σ6.regs.get? Register.x15 = some (9#64) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [li9] at this
  have hx22_6 : σ6.regs.get? Register.x22 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_alu_other hobs6 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_5
  have hx10_6 : σ6.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_5
  have hs10_6 : σ6.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs6 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs10_5
  have hs7_6 : σ6.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs6 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_5
  have hs11_6 : σ6.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs6 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11_5
  have hx12_6 : ∃ v, σ6.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_5
    exact ⟨v, obs_alu_other hobs6 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_6 : ∃ v, σ6.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_5
    exact ⟨v, obs_alu_other hobs6 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hmem6q : σ6.mem = c.σ.mem := by rw [hmem6]; exact hmem5q
  have hload6 : SvfprintfSliceLoaded σ6.mem := hmem6 ▸ hload5
  have hcuload6 : __hidden___udivdi3Loaded σ6.mem := hmem6 ▸ hcuload5
  have huload6 : Vsa.Sim.Code.__umoddi3Loaded σ6.mem := hmem6 ▸ huload5
  have hbufinv6 : BufInv top m (p+1) σ6.mem := by rw [hmem6]; exact hbufinv5
  -- === 8310: mv s9,s10 ⇒ x25 := top-1-p ===
  obtain ⟨σ7, i7, hs7', hi7, hG7, hmem7, hobs7⟩ :=
    site_80008310_sn σ6 i6 (c4.steps+1+1) (0x80008310#64) vmi6 (BitVec.ofNat 64 (top.toNat-1-p))
      hG6 hpc6 hmi6 hs10_6 hload6 rfl hi6
  have hstep7 : Step ⟨σ6,i6,c4.steps+1+1⟩ ⟨σ7,i7,c4.steps+1+1+1⟩ := hs7'
  have hpc7 : σ7.regs.get? Register.PC = some (0x80008314#64) := obs_alu_pc hobs7
  have hx25_7 : σ7.regs.get? Register.x25 = some (BitVec.ofNat 64 (top.toNat-1-p)) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 (BitVec.ofNat 64 (top.toNat-1-p))] at this
  have hx15_7 : σ7.regs.get? Register.x15 = some (9#64) :=
    obs_alu_other hobs7 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_6
  have hx22_7 : σ7.regs.get? Register.x22 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_alu_other hobs7 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_6
  have hx10_7 : σ7.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_alu_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_6
  have hs7_7 : σ7.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs7 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_6
  have hs11_7 : σ7.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs7 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11_6
  have hx12_7 : ∃ v, σ7.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_6
    exact ⟨v, obs_alu_other hobs7 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_7 : ∃ v, σ7.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_6
    exact ⟨v, obs_alu_other hobs7 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hmem7q : σ7.mem = c.σ.mem := by rw [hmem7]; exact hmem6q
  have hload7 : SvfprintfSliceLoaded σ7.mem := hmem7 ▸ hload6
  have hcuload7 : __hidden___udivdi3Loaded σ7.mem := hmem7 ▸ hcuload6
  have huload7 : Vsa.Sim.Code.__umoddi3Loaded σ7.mem := hmem7 ▸ huload6
  have hbufinv7 : BufInv top m (p+1) σ7.mem := by rw [hmem7]; exact hbufinv6
  -- === 8314: mv s0,a0 ⇒ x8 := m/10^(p+1) ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80008314_sn σ7 i7 (c4.steps+1+1+1) (0x80008314#64) vmi7 (BitVec.ofNat 64 (m/10^(p+1)))
      hG7 hpc7 hmi7 hx10_7 hload7 rfl hi7
  have hstep8 : Step ⟨σ7,i7,c4.steps+1+1+1⟩ ⟨σ8,i8,c4.steps+1+1+1+1⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80008318#64) := obs_alu_pc hobs8
  have hs0_8 : σ8.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^(p+1))) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 (BitVec.ofNat 64 (m/10^(p+1)))] at this
  have hx25_8 : σ8.regs.get? Register.x25 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs8 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_7
  have hx15_8 : σ8.regs.get? Register.x15 = some (9#64) :=
    obs_alu_other hobs8 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_7
  have hx22_8 : σ8.regs.get? Register.x22 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_alu_other hobs8 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_7
  have hs7_8 : σ8.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs8 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_7
  have hs11_8 : σ8.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs8 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11_7
  have hx12_8 : ∃ v, σ8.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_7
    exact ⟨v, obs_alu_other hobs8 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_8 : ∃ v, σ8.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_7
    exact ⟨v, obs_alu_other hobs8 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hmem8q : σ8.mem = c.σ.mem := by rw [hmem8]; exact hmem7q
  have hload8 : SvfprintfSliceLoaded σ8.mem := hmem8 ▸ hload7
  have hcuload8 : __hidden___udivdi3Loaded σ8.mem := hmem8 ▸ hcuload7
  have huload8 : Vsa.Sim.Code.__umoddi3Loaded σ8.mem := hmem8 ▸ huload7
  have hbufinv8 : BufInv top m (p+1) σ8.mem := by rw [hmem8]; exact hbufinv7
  -- === 8318: bgeu a5,s6 (9 ≥ m/10^p?) NOT TAKEN (m/10^p > 9) ⇒ fall to 831c ===
  have hbge : zopz0zKzJ_u (9#64) (BitVec.ofNat 64 (m/10^p)) = false :=
    bgeu9_false_sn3 (m/10^p) hguard hmp
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80008318_nottaken_sn σ8 i8 (c4.steps+1+1+1+1) (0x80008318#64) vmi8 (9#64)
      (BitVec.ofNat 64 (m/10^p)) hG8 hpc8 hmi8 hx15_8 hx22_8 hload8 rfl hbge hi8
  have hstep9 : Step ⟨σ8,i8,c4.steps+1+1+1+1⟩ ⟨σ9,i9,c4.steps+1+1+1+1+1⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x8000831c#64) := by
    have := obs_bnottaken_pc hobs9
    rwa [show BitVec.addInt (0x80008318#64 : BitVec 64) 4 = (0x8000831c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hs0_9 : σ9.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_bnottaken_other hobs9 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs0_8
  have hx25_9 : σ9.regs.get? Register.x25 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_bnottaken_other hobs9 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_8
  have hs7_9 : σ9.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_bnottaken_other hobs9 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_8
  have hs11_9 : σ9.regs.get? Register.x27 = some (0#64) :=
    obs_bnottaken_other hobs9 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11_8
  have hx12_9 : ∃ v, σ9.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_8
    exact ⟨v, obs_bnottaken_other hobs9 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_9 : ∃ v, σ9.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_8
    exact ⟨v, obs_bnottaken_other hobs9 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi9, hmi9⟩ := obs_bnottaken_minstret hobs9
  have hmem9q : σ9.mem = c.σ.mem := by rw [hmem9]; exact hmem8q
  have hload9 : SvfprintfSliceLoaded σ9.mem := hmem9 ▸ hload8
  have hcuload9 : __hidden___udivdi3Loaded σ9.mem := hmem9 ▸ hcuload8
  have huload9 : Vsa.Sim.Code.__umoddi3Loaded σ9.mem := hmem9 ▸ huload8
  have hbufinv9 : BufInv top m (p+1) σ9.mem := by rw [hmem9]; exact hbufinv8
  -- === 831c: li a1,10 ⇒ x11 := 10 ===
  obtain ⟨σ10, i10, hs10', hi10, hG10, hmem10, hobs10⟩ :=
    site_8000831c_sn σ9 i9 (c4.steps+1+1+1+1+1) (0x8000831c#64) vmi9 hG9 hpc9 hmi9 hload9 rfl hi9
  have hstep10 : Step ⟨σ9,i9,c4.steps+1+1+1+1+1⟩ ⟨σ10,i10,c4.steps+1+1+1+1+1+1⟩ := hs10'
  have hpc10 : σ10.regs.get? Register.PC = some (0x80008320#64) := obs_alu_pc hobs10
  have hx11_10 : σ10.regs.get? Register.x11 = some (10#64) := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [li10] at this
  have hs0_10 : σ10.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_alu_other hobs10 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs0_9
  have hx25_10 : σ10.regs.get? Register.x25 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs10 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_9
  have hs7_10 : σ10.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs10 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_9
  have hs11_10 : σ10.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs10 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11_9
  have hx12_10 : ∃ v, σ10.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_9
    exact ⟨v, obs_alu_other hobs10 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_10 : ∃ v, σ10.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_9
    exact ⟨v, obs_alu_other hobs10 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hmem10q : σ10.mem = c.σ.mem := by rw [hmem10]; exact hmem9q
  have hload10 : SvfprintfSliceLoaded σ10.mem := hmem10 ▸ hload9
  have hcuload10 : __hidden___udivdi3Loaded σ10.mem := hmem10 ▸ hcuload9
  have huload10 : Vsa.Sim.Code.__umoddi3Loaded σ10.mem := hmem10 ▸ huload9
  have hbufinv10 : BufInv top m (p+1) σ10.mem := by rw [hmem10]; exact hbufinv9
  -- === 8320: mv a0,s0 ⇒ x10 := m/10^(p+1) ===
  obtain ⟨σ11, i11, hs11'', hi11, hG11, hmem11, hobs11⟩ :=
    site_80008320_sn σ10 i10 (c4.steps+1+1+1+1+1+1) (0x80008320#64) vmi10 (BitVec.ofNat 64 (m/10^(p+1)))
      hG10 hpc10 hmi10 hs0_10 hload10 rfl hi10
  have hstep11 : Step ⟨σ10,i10,c4.steps+1+1+1+1+1+1⟩ ⟨σ11,i11,c4.steps+1+1+1+1+1+1+1⟩ := hs11''
  have hpc11 : σ11.regs.get? Register.PC = some (0x80008324#64) := obs_alu_pc hobs11
  have hx10_11 : σ11.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^(p+1))) := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 (BitVec.ofNat 64 (m/10^(p+1)))] at this
  have hx11_11 : σ11.regs.get? Register.x11 = some (10#64) :=
    obs_alu_other hobs11 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_10
  have hs0_11 : σ11.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_alu_other hobs11 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs0_10
  have hx25_11 : σ11.regs.get? Register.x25 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs11 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_10
  have hs7_11 : σ11.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs11 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_10
  have hs11_11 : σ11.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs11 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11_10
  have hx12_11 : ∃ v, σ11.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_10
    exact ⟨v, obs_alu_other hobs11 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_11 : ∃ v, σ11.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_10
    exact ⟨v, obs_alu_other hobs11 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hmem11q : σ11.mem = c.σ.mem := by rw [hmem11]; exact hmem10q
  have hload11 : SvfprintfSliceLoaded σ11.mem := hmem11 ▸ hload10
  have hcuload11 : __hidden___udivdi3Loaded σ11.mem := hmem11 ▸ hcuload10
  have huload11 : Vsa.Sim.Code.__umoddi3Loaded σ11.mem := hmem11 ▸ huload10
  have hbufinv11 : BufInv top m (p+1) σ11.mem := by rw [hmem11]; exact hbufinv10
  -- === 8324: jal __umoddi3 ⇒ x1 := 8328, PC := 46f4 ; then umoddi3_frame_spec ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80008324_sn σ11 i11 (c4.steps+1+1+1+1+1+1+1) (0x80008324#64) vmi11 hG11 hpc11 hmi11 hload11 rfl hi11
  have hstep12 : Step ⟨σ11,i11,c4.steps+1+1+1+1+1+1+1⟩ ⟨σ12,i12,c4.steps+1+1+1+1+1+1+1+1⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x800046f4#64) := by
    have := obs_jal_pc hobs12
    rwa [show (0x80008324#64 : BitVec 64) + sign_extend (m := 64) (0x1fc3d0#21)
      = (0x800046f4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx1_12 : σ12.regs.get? Register.x1 = some (0x80008328#64) := by
    have := obs_jal_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80008324#64 : BitVec 64) 4 = (0x80008328#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_12 : σ12.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_jal_other hobs12 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_11
  have hx11_12 : σ12.regs.get? Register.x11 = some (10#64) :=
    obs_jal_other hobs12 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_11
  have hx12_12 : ∃ v, σ12.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_11
    exact ⟨v, obs_jal_other hobs12 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_12 : ∃ v, σ12.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_11
    exact ⟨v, obs_jal_other hobs12 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  -- loop-state carried through 8324 (jal, rd=x1)
  have hs0_12 : σ12.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_jal_other hobs12 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs0_11
  have hs7_12 : σ12.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_jal_other hobs12 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_11
  have hx25_12 : σ12.regs.get? Register.x25 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_jal_other hobs12 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_11
  have hs11_12 : σ12.regs.get? Register.x27 = some (0#64) :=
    obs_jal_other hobs12 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11_11
  obtain ⟨vmi12, hmi12⟩ := obs_jal_minstret hobs12
  have hmem12q : σ12.mem = c.σ.mem := by rw [hmem12]; exact hmem11q
  have hload12 : SvfprintfSliceLoaded σ12.mem := hmem12 ▸ hload11
  have hcuload12 : __hidden___udivdi3Loaded σ12.mem := hmem12 ▸ hcuload11
  have huload12 : Vsa.Sim.Code.__umoddi3Loaded σ12.mem := hmem12 ▸ huload11
  have hbufinv12 : BufInv top m (p+1) σ12.mem := by rw [hmem12]; exact hbufinv11
  have hf12 : ∀ R, NotWrittenL R → σ12.regs.get? R = σ11.regs.get? R := fun R hR =>
    frameL_jal hobs12 R (by obtain ⟨_, _, _, _, hx1, _⟩ := hR; exact hx1) hR
  -- umoddi3_loopframe_spec from 46f4: n = m/10^(p+1), d = 10, r = 8328, preserving x8/x23/x25/x27
  have humpre : umoddi3_pre (BitVec.ofNat 64 (m/10^(p+1))) (10#64) (0x80008328#64) c.σ.mem
      ⟨σ12, i12, c4.steps+1+1+1+1+1+1+1+1⟩ := by
    refine ⟨hG12, by exact hmem12q ▸ huload12, by exact hmem12q ▸ hcuload12, hmem12q,
      hpc12, hx10_12, hx11_12, hx1_12, ⟨vmi12, hmi12⟩, hx12_12, hx13_12, hi12, by decide, by decide⟩
  obtain ⟨c13, hs13, hG13, hmem13, hpc13, hrem13, htick13, hmi13,
    hs0_13, hs7_13, hx25_13, hs11_13, hx12_13, hx13_13, hx1_13e, hframe13⟩ :=
    umoddi3_loopframe_spec (fun R => σ12.regs.get? R) (BitVec.ofNat 64 (m/10^(p+1))) (10#64) (0x80008328#64) c.σ.mem
      (BitVec.ofNat 64 (m/10^(p+1))) (BitVec.ofNat 64 (p+1)) (BitVec.ofNat 64 (top.toNat-1-p)) (0#64)
      ⟨σ12, i12, c4.steps+1+1+1+1+1+1+1+1⟩ humpre hs0_12 hs7_12 hx25_12 hs11_12 (fun R _ => rfl)
  -- x10 = (m/10^(p+1)) % 10
  have hrem13' : c13.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 ((m/10^(p+1)) % 10)) := by
    rw [hrem13]; congr 1; exact modstep m p hm
  have hmem13q : c13.σ.mem = c.σ.mem := hmem13
  have hload13 : SvfprintfSliceLoaded c13.σ.mem := hmem13q ▸ hSt.loaded
  have hbufinv13 : BufInv top m (p+1) c13.σ.mem := by rw [hmem13q]; exact hSt.bufinv
  obtain ⟨vmi13, hmi13'⟩ := hmi13
  -- === 8328: addiw a0,a0,48 ⇒ x10 := '0' + digit ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_80008328_sn c13.σ c13.tick c13.steps (0x80008328#64) vmi13
      (BitVec.ofNat 64 ((m/10^(p+1)) % 10)) hG13 hpc13 hmi13' hrem13' hload13 rfl htick13
  have hstep14 : Step c13 ⟨σ14,i14,c13.steps+1⟩ := by cases c13; exact hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x8000832c#64) := obs_alu_pc hobs14
  -- the emit value read-back: x10 = sext32(ofNat(d)+48)
  have hd_lt : (m/10^(p+1)) % 10 < 10 := Nat.mod_lt _ (by decide)
  have hx10_14 : σ14.regs.get? Register.x10 =
      some (sign_extend (m := 64) (Sail.BitVec.extractLsb ((BitVec.ofNat 64 ((m/10^(p+1)) % 10)) + sign_extend (m := 64) (0x030#12)) 31 0)) :=
    obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx25_14 : σ14.regs.get? Register.x25 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs14 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_13
  have hs0_14 : σ14.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_alu_other hobs14 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs0_13
  have hs7_14 : σ14.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs14 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_13
  have hs11_14 : σ14.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs14 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11_13
  have hx12_14 : ∃ v, σ14.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_13
    exact ⟨v, obs_alu_other hobs14 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_14 : ∃ v, σ14.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_13
    exact ⟨v, obs_alu_other hobs14 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hmem14q : σ14.mem = c.σ.mem := by rw [hmem14]; exact hmem13q
  have hload14 : SvfprintfSliceLoaded σ14.mem := hmem14 ▸ hload13
  have hbufinv14 : BufInv top m (p+1) σ14.mem := by rw [hmem14]; exact hbufinv13
  -- === 832c: sb a0,-1(s9) ⇒ mem[top-1-(p+1)] := digit char ; extends BufInv to p+2 ===
  -- write address: (top-1-p) + (-1) = top-1-p-1
  -- bounds: need 0x80000000 ≤ addr, addr+1 ≤ 0x100000000, tohost+16 ≤ addr
  have hp_small : p + 2 ≤ 20 := by
    -- from 9 < m/10^p we get 10·10^p ≤ m; p ≥ 19 would force 10^20 ≤ m < 2^64, absurd
    rcases Nat.lt_or_ge p 19 with hp | hp
    · omega
    · exfalso
      have h10p : 10 ≤ m / 10 ^ p := by omega
      have hmul : 10 ^ p * 10 ≤ m :=
        Nat.le_trans (Nat.mul_le_mul_left (10 ^ p) h10p) (Nat.mul_div_le m (10 ^ p))
      have hpow : (10:Nat) ^ 19 * 10 ≤ 10 ^ p * 10 :=
        Nat.mul_le_mul_right 10 (Nat.pow_le_pow_right (by decide) hp)
      exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans hpow hmul) hm) (by decide)
  have haddr_eq : (BitVec.ofNat 64 (top.toNat-1-p) + sign_extend (m := 64) (0xfff#12))
      = BitVec.ofNat 64 (top.toNat-1-(p+1)) := by
    rw [sub1_ofNat (top.toNat-1-p) (by omega) (by omega),
        show top.toNat-1-p-1 = top.toNat-1-(p+1) from by omega]
  have haddr_toNat : (BitVec.ofNat 64 (top.toNat-1-p) + sign_extend (m := 64) (0xfff#12)).toNat
      = top.toNat - 1 - (p+1) := by
    rw [haddr_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlo : 0x80000000 ≤ (BitVec.ofNat 64 (top.toNat-1-p) + sign_extend (m := 64) (0xfff#12)).toNat := by
    rw [haddr_toNat]; omega
  have hhiram : (BitVec.ofNat 64 (top.toNat-1-p) + sign_extend (m := 64) (0xfff#12)).toNat + 1 ≤ 0x100000000 := by
    rw [haddr_toNat]; omega
  have hhiwin : tohostAddr + 16 ≤ (BitVec.ofNat 64 (top.toNat-1-p) + sign_extend (m := 64) (0xfff#12)).toNat := by
    rw [haddr_toNat]; omega
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_8000832c_sn σ14 i14 (c13.steps+1) (0x8000832c#64) vmi14 (BitVec.ofNat 64 (top.toNat-1-p))
      (sign_extend (m := 64) (Sail.BitVec.extractLsb ((BitVec.ofNat 64 ((m/10^(p+1)) % 10)) + sign_extend (m := 64) (0x030#12)) 31 0))
      hG14 hpc14 hmi14 hx25_14 hx10_14 hload14 rfl hlo hhiram hhiwin hi14
  have hstep15 : Step ⟨σ14,i14,c13.steps+1⟩ ⟨σ15,i15,c13.steps+1+1⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x80008330#64) := obs_store_pc_sn3 hobs15
  have hs0_15 : σ15.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_store_other_sn3 Register.x8 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs0_14
  have hx25_15 : σ15.regs.get? Register.x25 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_store_other_sn3 Register.x25 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_14
  have hs7_15 : σ15.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_store_other_sn3 Register.x23 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_14
  have hs11_15 : σ15.regs.get? Register.x27 = some (0#64) :=
    obs_store_other_sn3 Register.x27 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11_14
  have hx12_15 : ∃ v, σ15.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_14
    exact ⟨v, obs_store_other_sn3 Register.x12 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_15 : ∃ v, σ15.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_14
    exact ⟨v, obs_store_other_sn3 Register.x13 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi15, hmi15⟩ := obs_store_minstret_sn3 hobs15
  -- new BufInv extends to p+2
  have hbufinv15 : BufInv top m (p+2) σ15.mem := by
    rw [hmem15]
    -- σ15.mem = (afterNextPC (afterPrelude σ14) 832c).mem.insert (addr).toNat (stData 1 emit)
    -- afterNextPC/afterPrelude are register-only ⇒ .mem = σ14.mem
    have hmemNP : (afterNextPC (afterPrelude σ14) (0x8000832c#64)).mem = σ14.mem := rfl
    rw [hmemNP, haddr_toNat]
    -- stData 1 emit = ofNat 8 (48 + digit) via emit_byte
    have hstd : stData 1 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((BitVec.ofNat 64 ((m/10^(p+1)) % 10)) + sign_extend (m := 64) (0x030#12)) 31 0))
        = BitVec.ofNat 8 (48 + (m/10^(p+1)) % 10) := emit_byte ((m/10^(p+1)) % 10) hd_lt
    rw [hstd]
    -- bufinv_store extends p+1 → p+2 with digit (m / 10^(p+1)) % 10 at slot top-1-(p+1)
    exact bufinv_store top m (p+1) σ14.mem hbufinv14 (by omega)
  have hmem15q : σ15.mem = ((afterNextPC (afterPrelude σ14) (0x8000832c#64)).mem.insert
      (top.toNat - 1 - (p+1)) (stData 1 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((BitVec.ofNat 64 ((m/10^(p+1)) % 10)) + sign_extend (m := 64) (0x030#12)) 31 0)))) := by
    rw [hmem15, haddr_toNat]
  have hG15' : GoodState σ15 := hG15
  have hload15 : SvfprintfSliceLoaded σ15.mem := by
    -- the store lands in the stack buffer above `tohost` (TopOk + p ≤ 18 ⇒ key ≥ 0x80009000),
    -- above the whole code region, so every code-byte pin survives the insert
    rw [hmem15q]
    exact svfprintfSlice_insert_sn3 _ _ _ (by omega) hload14
  -- === 8330: addi s10,s9,-1 ⇒ x26 := (top-1-p)-1 = top-1-(p+1) ===
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_80008330_sn σ15 i15 (c13.steps+1+1) (0x80008330#64) vmi15 (BitVec.ofNat 64 (top.toNat-1-p))
      hG15' hpc15 hmi15 hx25_15 hload15 rfl hi15
  have hstep16 : Step ⟨σ15,i15,c13.steps+1+1⟩ ⟨σ16,i16,c13.steps+1+1+1⟩ := hs16
  have hpc16 : σ16.regs.get? Register.PC = some (0x80008334#64) := obs_alu_pc hobs16
  have hs10_16 : σ16.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-(p+1))) := by
    have := obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [haddr_eq] at this; exact this
  have hs0_16 : σ16.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_alu_other hobs16 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs0_15
  have hx25_16 : σ16.regs.get? Register.x25 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs16 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_15
  have hs7_16 : σ16.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs16 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_15
  have hs11_16 : σ16.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs16 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11_15
  have hx12_16 : ∃ v, σ16.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_15
    exact ⟨v, obs_alu_other hobs16 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_16 : ∃ v, σ16.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_15
    exact ⟨v, obs_alu_other hobs16 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  have hmem16q : σ16.mem = σ15.mem := hmem16
  have hload16 : SvfprintfSliceLoaded σ16.mem := hmem16 ▸ hload15
  have hbufinv16 : BufInv top m (p+2) σ16.mem := by rw [hmem16]; exact hbufinv15
  -- === 8334: addiw s7,s7,1 ⇒ x23 := (p+1)+1 = p+2 ===
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_80008334_sn σ16 i16 (c13.steps+1+1+1) (0x80008334#64) vmi16 (BitVec.ofNat 64 (p+1))
      hG16 hpc16 hmi16 hs7_16 hload16 rfl hi16
  have hstep17 : Step ⟨σ16,i16,c13.steps+1+1+1⟩ ⟨σ17,i17,c13.steps+1+1+1+1⟩ := hs17
  have hpc17 : σ17.regs.get? Register.PC = some (0x80008338#64) := obs_alu_pc hobs17
  have hs7_17 : σ17.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+2)) := by
    have := obs_alu_rd hobs17 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [addiw1_sn3 (p+1) (by omega)] at this
    have : σ17.regs.get? Register.x23 = some (BitVec.ofNat 64 ((p+1)+1)) := this
    rwa [show (p+1)+1 = p+2 from rfl] at this
  have hs0_17 : σ17.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_alu_other hobs17 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs0_16
  have hx25_17 : σ17.regs.get? Register.x25 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs17 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_16
  have hs10_17 : σ17.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-(p+1))) :=
    obs_alu_other hobs17 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs10_16
  have hs11_17 : σ17.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs17 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11_16
  have hx12_17 : ∃ v, σ17.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_16
    exact ⟨v, obs_alu_other hobs17 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_17 : ∃ v, σ17.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_16
    exact ⟨v, obs_alu_other hobs17 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  obtain ⟨vmi17, hmi17⟩ := obs_alu_minstret hobs17
  have hload17 : SvfprintfSliceLoaded σ17.mem := hmem17 ▸ hload16
  have hbufinv17 : BufInv top m (p+2) σ17.mem := by rw [hmem17]; exact hbufinv16
  -- === 8338: beqz s11 (s11 = 0) TAKEN ⇒ PC := 82fc ===
  obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
    site_80008338_taken_sn σ17 i17 (c13.steps+1+1+1+1) (0x80008338#64) vmi17 (0#64)
      hG17 hpc17 hmi17 hs11_17 hload17 rfl (by decide) hi17
  have hstep18 : Step ⟨σ17,i17,c13.steps+1+1+1+1⟩ ⟨σ18,i18,c13.steps+1+1+1+1+1⟩ := hs18
  have hpc18 : σ18.regs.get? Register.PC = some (0x800082fc#64) := by
    have := obs_btaken_pc hobs18
    rwa [show (0x80008338#64 : BitVec 64) + sign_extend (m := 64) (0x1fc4#13)
      = (0x800082fc#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hs0_18 : σ18.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_btaken_other hobs18 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs0_17
  have hx25_18 : σ18.regs.get? Register.x25 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_btaken_other hobs18 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx25_17
  have hs10_18 : σ18.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-(p+1))) :=
    obs_btaken_other hobs18 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs10_17
  have hs7_18 : σ18.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+2)) :=
    obs_btaken_other hobs18 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_17
  have hs11_18 : σ18.regs.get? Register.x27 = some (0#64) :=
    obs_btaken_other hobs18 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11_17
  have hx12_18 : ∃ v, σ18.regs.get? Register.x12 = some v := by
    obtain ⟨v, hv⟩ := hx12_17
    exact ⟨v, obs_btaken_other hobs18 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx13_18 : ∃ v, σ18.regs.get? Register.x13 = some v := by
    obtain ⟨v, hv⟩ := hx13_17
    exact ⟨v, obs_btaken_other hobs18 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩
  have hx1_18 : ∃ v, σ18.regs.get? Register.x1 = some v := by
    obtain ⟨v1, hv1⟩ := hx1_13e
    have hx1_14 : σ14.regs.get? Register.x1 = some v1 :=
      obs_alu_other hobs14 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv1
    have hx1_15 : σ15.regs.get? Register.x1 = some v1 :=
      obs_store_other_sn3 Register.x1 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_14
    have hx1_16 : σ16.regs.get? Register.x1 = some v1 :=
      obs_alu_other hobs16 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_15
    have hx1_17 : σ17.regs.get? Register.x1 = some v1 :=
      obs_alu_other hobs17 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_16
    exact ⟨v1, obs_btaken_other hobs18 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_17⟩
  obtain ⟨vmi18, hmi18⟩ := obs_btaken_minstret hobs18
  have hload18 : SvfprintfSliceLoaded σ18.mem := hmem18 ▸ hload17
  -- `…Loaded` for the two div-cluster code regions survive the buffer store
  have h14u : Vsa.Sim.Code.__umoddi3Loaded σ14.mem := by rw [hmem14q]; exact hSt.uloaded
  have h14cu : __hidden___udivdi3Loaded σ14.mem := by rw [hmem14q]; exact hSt.culoaded
  have huload18 : Vsa.Sim.Code.__umoddi3Loaded σ18.mem := by
    rw [hmem18, hmem17, hmem16, hmem15q]
    exact umoddi3_insert_sn3 _ _ _ (by omega) h14u
  have hcuload18 : __hidden___udivdi3Loaded σ18.mem := by
    rw [hmem18, hmem17, hmem16, hmem15q]
    exact cudivdi3_insert_sn3 _ _ _ (by omega) h14cu
  have hbufinv18 : BufInv top m (p+2) σ18.mem := by rw [hmem18]; exact hbufinv17
  -- frame σ18 = c.σ on NotWrittenL — needed for LSt.hframe
  -- Chain: σ18 ← σ17 ← … ← σ14 ← c13 ← σ12 ← σ11 ← … ← σ1 ← c.σ, all NotWrittenL-preserving.
  -- We assemble hframe via the individual frames.
  -- exact final memory: one byte insert at top-1-(p+1) over the entry memory
  have hmemfinal : σ18.mem = c.σ.mem.insert (top.toNat - 1 - (p+1))
      (BitVec.ofNat 8 (48 + (m / 10^(p+1)) % 10)) := by
    rw [hmem18, hmem17, hmem16, hmem15q,
      emit_byte ((m/10^(p+1)) % 10) hd_lt,
      show (afterNextPC (afterPrelude σ14) (0x8000832c#64)).mem = σ14.mem from rfl, hmem14q]
  -- Assemble LSt g top m (p+1) at σ18
  refine ⟨⟨σ18, i18, c13.steps+1+1+1+1+1⟩, ?_, ?_, hmemfinal⟩
  · -- Steps chain
    exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
      (hs4.trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans
      ((Steps.single hstep8).trans ((Steps.single hstep9).trans ((Steps.single hstep10).trans
      ((Steps.single hstep11).trans ((Steps.single hstep12).trans (hs13.trans ((Steps.single hstep14).trans
      ((Steps.single hstep15).trans ((Steps.single hstep16).trans ((Steps.single hstep17).trans
      (Steps.single hstep18)))))))))))))))))
  · -- LSt g top m (p+1)
    refine {
      good := hG18, loaded := hload18, uloaded := huload18, culoaded := hcuload18,
      pc := hpc18, s0 := hs0_18, s9 := ?_, s10 := hs10_18, s7 := hs7_18, s11 := hs11_18,
      x12 := hx12_18, x13 := hx13_18, x1 := hx1_18, minstret := ⟨vmi18, hmi18⟩, tick := hi18,
      bufinv := hbufinv18, hframe := ?_ }
    · -- s9 = top - (p+1) = top-1-p ✓
      rw [show top.toNat - (p+1) = top.toNat - 1 - p from by omega]; exact hx25_18
    · -- hframe: σ18 = g on NotWrittenL
      intro R hR
      -- σ18=σ17=σ16(store: frame)=σ15=σ14=c13(umoddi3 frame)=σ12(jal frame)=σ11=…=σ1=c.σ=g
      have e18 : σ18.regs.get? R = σ17.regs.get? R := frameL_btaken_sn3 hobs18 R hR
      have e17 : σ17.regs.get? R = σ16.regs.get? R := frameL_alu hobs17 R (by obtain ⟨_,_,_,_,_,_,_,_,h23,_⟩ := hR; exact h23) hR
      have e16 : σ16.regs.get? R = σ15.regs.get? R := frameL_alu hobs16 R (by obtain ⟨_,_,_,_,_,_,_,_,_,_,h26,_⟩ := hR; exact h26) hR
      have e15 : σ15.regs.get? R = σ14.regs.get? R := frameL_store_sn3 hobs15 R hR
      have e14 : σ14.regs.get? R = c13.σ.regs.get? R := frameL_alu hobs14 R (by obtain ⟨h10,_⟩ := hR; exact h10) hR
      have e13 : c13.σ.regs.get? R = σ12.regs.get? R := hframe13 R hR
      have e12 : σ12.regs.get? R = σ11.regs.get? R := hf12 R hR
      have e11 : σ11.regs.get? R = σ10.regs.get? R := frameL_alu hobs11 R (by obtain ⟨h10,_⟩ := hR; exact h10) hR
      have e10 : σ10.regs.get? R = σ9.regs.get? R := frameL_alu hobs10 R (by obtain ⟨_,h11,_⟩ := hR; exact h11) hR
      have e9 : σ9.regs.get? R = σ8.regs.get? R := frameL_bnottaken_sn3 hobs9 R hR
      have e8 : σ8.regs.get? R = σ7.regs.get? R := frameL_alu hobs8 R (by obtain ⟨_,_,_,_,_,_,h8,_⟩ := hR; exact h8) hR
      have e7 : σ7.regs.get? R = σ6.regs.get? R := frameL_alu hobs7 R (by obtain ⟨_,_,_,_,_,_,_,_,_,h25,_⟩ := hR; exact h25) hR
      have e6 : σ6.regs.get? R = σ5.regs.get? R := frameL_alu hobs6 R (by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,h15,_⟩ := hR; exact h15) hR
      have e5 : σ5.regs.get? R = c4.σ.regs.get? R := frameL_alu hobs5 R (by obtain ⟨_,_,_,_,_,_,_,h22,_⟩ := hR; exact h22) hR
      have e4 : c4.σ.regs.get? R = σ3.regs.get? R := hframe4L R hR
      have e3 : σ3.regs.get? R = σ2.regs.get? R := hf3 R hR
      have e2 : σ2.regs.get? R = σ1.regs.get? R := hf2 R hR
      have e1 : σ1.regs.get? R = c.σ.regs.get? R := hf1 R hR
      rw [e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]
      exact hSt.hframe R hR

/-! ## Exit iteration (`loop_exit`)

From `LSt g top m p` with the exit guard `m / 10^p ≤ 9`, step the head prefix
`0x800082fc … 0x80008318` where the `bgeu` at `0x80008318` is now **taken** (`9 ≥
m/10^p`), landing at `0x80008358` with the complete emitted digit buffer
`BufInv top m (p+1)` and digit count `s7 = p + 1`.  No `__umoddi3`, no `sb`: the
final digit was already emitted at the previous iteration (do-while shape). -/
theorem loop_exit (g : (R : Register) → Option (RegisterType R))
    (top : BitVec 64) (m p : Nat) (hm : m < 2^64) (_htop : TopOk top)
    (hexit : m / 10^p ≤ 9) (c : Config) (hSt : LSt g top m p c) :
    ∃ c', Steps c c' ∧ GoodState c'.σ ∧ c'.σ.regs.get? Register.PC = some (0x80008358#64) ∧
      c'.σ.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) ∧
      BufInv top m (p+1) c'.σ.mem ∧ c'.tick < 2 ∧
      (∃ v, c'.σ.regs.get? Register.minstret = some v) ∧ c'.σ.mem = c.σ.mem ∧
      c'.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat - 1 - p)) ∧
      (∀ R, NotWrittenL R → c'.σ.regs.get? R = c.σ.regs.get? R) := by
  have hmp : m / 10^p < 2^64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm
  obtain ⟨vmi0, hmi0⟩ := hSt.minstret
  obtain ⟨v12_0, h12_0⟩ := hSt.x12
  obtain ⟨v13_0, h13_0⟩ := hSt.x13
  -- 82fc: mv a0,s0
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800082fc_sn c.σ c.tick c.steps (0x800082fc#64) vmi0 (BitVec.ofNat 64 (m/10^p))
      hSt.good hSt.pc hmi0 hSt.s0 hSt.loaded rfl hSt.tick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80008300#64) := obs_alu_pc hobs1
  have hx10_1 : σ1.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^p)) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 (BitVec.ofNat 64 (m/10^p))] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hSt.loaded
  have hcuload1 : __hidden___udivdi3Loaded σ1.mem := hmem1 ▸ hSt.culoaded
  have s0_1 : σ1.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_alu_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.s0
  have s7_1 : σ1.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs1 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.s7
  have s10_1 : σ1.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs1 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.s10
  have h12_1 : σ1.regs.get? Register.x12 = some v12_0 :=
    obs_alu_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h12_0
  have h13_1 : σ1.regs.get? Register.x13 = some v13_0 :=
    obs_alu_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h13_0
  have hbufinv1 : BufInv top m (p+1) σ1.mem := by rw [hmem1]; exact hSt.bufinv
  -- 8300: li a1,10
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80008300_sn σ1 i1 (c.steps+1) (0x80008300#64) vmi1 hG1 hpc1 hmi1 hload1 rfl hi1
  have hstep2 : Step ⟨σ1,i1,c.steps+1⟩ ⟨σ2,i2,c.steps+1+1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80008304#64) := obs_alu_pc hobs2
  have hx11_2 : σ2.regs.get? Register.x11 = some (10#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [li10] at this
  have hx10_2 : σ2.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  have hcuload2 : __hidden___udivdi3Loaded σ2.mem := hmem2 ▸ hcuload1
  have s0_2 : σ2.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_alu_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s0_1
  have s7_2 : σ2.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs2 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s7_1
  have h12_2 : σ2.regs.get? Register.x12 = some v12_0 :=
    obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h12_1
  have h13_2 : σ2.regs.get? Register.x13 = some v13_0 :=
    obs_alu_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h13_1
  have hbufinv2 : BufInv top m (p+1) σ2.mem := by rw [hmem2]; exact hbufinv1
  -- 8304: jal udivdi3
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80008304_sn σ2 i2 (c.steps+1+1) (0x80008304#64) vmi2 hG2 hpc2 hmi2 hload2 rfl hi2
  have hstep3 : Step ⟨σ2,i2,c.steps+1+1⟩ ⟨σ3,i3,c.steps+1+1+1⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x800046ac#64) := by
    have := obs_jal_pc hobs3
    rwa [show (0x80008304#64 : BitVec 64) + sign_extend (m := 64) (0x1fc3a8#21)
      = (0x800046ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx1_3 : σ3.regs.get? Register.x1 = some (0x80008308#64) := by
    have := obs_jal_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80008304#64 : BitVec 64) 4 = (0x80008308#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_3 : σ3.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_jal_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_2
  have hx11_3 : σ3.regs.get? Register.x11 = some (10#64) :=
    obs_jal_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_2
  have h12_3 : σ3.regs.get? Register.x12 = some v12_0 :=
    obs_jal_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h12_2
  have h13_3 : σ3.regs.get? Register.x13 = some v13_0 :=
    obs_jal_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h13_2
  obtain ⟨vmi3, hmi3⟩ := obs_jal_minstret hobs3
  have hload3 : SvfprintfSliceLoaded σ3.mem := hmem3 ▸ hload2
  have hcuload3 : __hidden___udivdi3Loaded σ3.mem := hmem3 ▸ hcuload2
  have s0_3 : σ3.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_jal_other hobs3 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s0_2
  have s7_3 : σ3.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_jal_other hobs3 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s7_2
  have hbufinv3 : BufInv top m (p+1) σ3.mem := by rw [hmem3]; exact hbufinv2
  have hmem3q : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  -- core
  have hcorepre : udivdi3_pre (fun R => σ3.regs.get? R) (BitVec.ofNat 64 (m/10^p)) (10#64)
      (0x80008308#64) c.σ.mem σ3.sailOutput ⟨σ3, i3, c.steps+1+1+1⟩ := by
    refine ⟨⟨v12_0, v13_0, ?_⟩, by decide, by decide⟩
    exact {
      good := hG3, loaded := by rw [show (⟨σ3,i3,c.steps+1+1+1⟩ : Config).σ.mem = σ3.mem from rfl]; exact hmem3q ▸ hSt.culoaded,
      mem := hmem3q, sailOut := rfl, pc := hpc3, a0 := hx10_3, a1 := hx11_3, a2 := h12_3, a3 := h13_3,
      ra := hx1_3, minstret := ⟨vmi3, hmi3⟩, tick := hi3, hframe := fun R _ => rfl }
  obtain ⟨c4, hs4, hG4, hmem4, _hout4, hpc4, hq4, _hrem4, _hra4, htick4, hframe4, _hx12_4, _hx13_4⟩ :=
    udivdi3_spec (fun R => σ3.regs.get? R) (BitVec.ofNat 64 (m/10^p)) (10#64) (0x80008308#64) c.σ.mem σ3.sailOutput
      ⟨σ3, i3, c.steps+1+1+1⟩ hcorepre
  have hmem4q : c4.σ.mem = c.σ.mem := hmem4
  have hload4 : SvfprintfSliceLoaded c4.σ.mem := hmem4q ▸ hSt.loaded
  have hs0_4 : c4.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 (m/10^p)) := by
    rw [hframe4 Register.x8 (by decide)]; exact s0_3
  have hs7_4 : c4.σ.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) := by
    rw [hframe4 Register.x23 (by decide)]; exact s7_3
  have hbufinv4 : BufInv top m (p+1) c4.σ.mem := by rw [hmem4q]; exact hSt.bufinv
  obtain ⟨vmi4, hmi4⟩ := hG4.minstret
  -- 8308: mv s6,s0 ⇒ x22 := m/10^p
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80008308_sn c4.σ c4.tick c4.steps (0x80008308#64) vmi4 (BitVec.ofNat 64 (m/10^p))
      hG4 hpc4 hmi4 hs0_4 hload4 rfl htick4
  have hstep5 : Step c4 ⟨σ5,i5,c4.steps+1⟩ := by cases c4; exact hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000830c#64) := obs_alu_pc hobs5
  have hx22_5 : σ5.regs.get? Register.x22 = some (BitVec.ofNat 64 (m/10^p)) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 (BitVec.ofNat 64 (m/10^p))] at this
  have hs7_5 : σ5.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs5 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hload5 : SvfprintfSliceLoaded σ5.mem := hmem5 ▸ hload4
  have hbufinv5 : BufInv top m (p+1) σ5.mem := by rw [hmem5]; exact hbufinv4
  -- 830c: li a5,9 ⇒ x15 := 9
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_8000830c_sn σ5 i5 (c4.steps+1) (0x8000830c#64) vmi5 hG5 hpc5 hmi5 hload5 rfl hi5
  have hstep6 : Step ⟨σ5,i5,c4.steps+1⟩ ⟨σ6,i6,c4.steps+1+1⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x80008310#64) := obs_alu_pc hobs6
  have hx15_6 : σ6.regs.get? Register.x15 = some (9#64) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [li9] at this
  have hx22_6 : σ6.regs.get? Register.x22 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_alu_other hobs6 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_5
  have hs7_6 : σ6.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs6 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hload6 : SvfprintfSliceLoaded σ6.mem := hmem6 ▸ hload5
  have hbufinv6 : BufInv top m (p+1) σ6.mem := by rw [hmem6]; exact hbufinv5
  have hs10_5 : σ5.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs5 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      rw [hframe4 Register.x26 (by decide)]; exact (obs_jal_other hobs3 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (obs_alu_other hobs2 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s10_1)))
  have hs10_6 : σ6.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs6 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs10_5
  -- 8310: mv s9,s10 ⇒ x25 := top-1-p
  obtain ⟨σ7, i7, hs7', hi7, hG7, hmem7, hobs7⟩ :=
    site_80008310_sn σ6 i6 (c4.steps+1+1) (0x80008310#64) vmi6 (BitVec.ofNat 64 (top.toNat-1-p))
      hG6 hpc6 hmi6 hs10_6 hload6 rfl hi6
  have hstep7 : Step ⟨σ6,i6,c4.steps+1+1⟩ ⟨σ7,i7,c4.steps+1+1+1⟩ := hs7'
  have hpc7 : σ7.regs.get? Register.PC = some (0x80008314#64) := obs_alu_pc hobs7
  have hx15_7 : σ7.regs.get? Register.x15 = some (9#64) :=
    obs_alu_other hobs7 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_6
  have hx22_7 : σ7.regs.get? Register.x22 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_alu_other hobs7 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_6
  have hs10_7 : σ7.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs7 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs10_6
  have hs7_7 : σ7.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs7 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hload7 : SvfprintfSliceLoaded σ7.mem := hmem7 ▸ hload6
  have hbufinv7 : BufInv top m (p+1) σ7.mem := by rw [hmem7]; exact hbufinv6
  -- 8314: mv s0,a0 ⇒ x8 := m/10^(p+1) (unused past exit)
  have hx10_4 : c4.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^(p+1))) := by
    rw [hq4]; congr 1; exact divstep m p hm
  have hx10_5 : σ5.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_alu_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_4
  have hx10_6 : σ6.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_5
  have hx10_7 : σ7.regs.get? Register.x10 = some (BitVec.ofNat 64 (m/10^(p+1))) :=
    obs_alu_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_6
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80008314_sn σ7 i7 (c4.steps+1+1+1) (0x80008314#64) vmi7 (BitVec.ofNat 64 (m/10^(p+1)))
      hG7 hpc7 hmi7 hx10_7 hload7 rfl hi7
  have hstep8 : Step ⟨σ7,i7,c4.steps+1+1+1⟩ ⟨σ8,i8,c4.steps+1+1+1+1⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80008318#64) := obs_alu_pc hobs8
  have hx15_8 : σ8.regs.get? Register.x15 = some (9#64) :=
    obs_alu_other hobs8 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_7
  have hx22_8 : σ8.regs.get? Register.x22 = some (BitVec.ofNat 64 (m/10^p)) :=
    obs_alu_other hobs8 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_7
  have hs7_8 : σ8.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_alu_other hobs8 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_7
  have hs10_8 : σ8.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_alu_other hobs8 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs10_7
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hload8 : SvfprintfSliceLoaded σ8.mem := hmem8 ▸ hload7
  have hbufinv8 : BufInv top m (p+1) σ8.mem := by rw [hmem8]; exact hbufinv7
  -- 8318: bgeu a5,s6 (9 ≥ m/10^p) TAKEN → 8358
  have hbge : zopz0zKzJ_u (9#64) (BitVec.ofNat 64 (m/10^p)) = true := bgeu9_true_sn3 (m/10^p) hexit
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80008318_taken_sn σ8 i8 (c4.steps+1+1+1+1) (0x80008318#64) vmi8 (9#64)
      (BitVec.ofNat 64 (m/10^p)) hG8 hpc8 hmi8 hx15_8 hx22_8 hload8 rfl hbge hi8
  have hstep9 : Step ⟨σ8,i8,c4.steps+1+1+1+1⟩ ⟨σ9,i9,c4.steps+1+1+1+1+1⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x80008358#64) := by
    have := obs_btaken_pc hobs9
    rwa [show (0x80008318#64 : BitVec 64) + sign_extend (m := 64) (0x0040#13)
      = (0x80008358#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hs7_9 : σ9.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) :=
    obs_btaken_other hobs9 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7_8
  have hs10_9 : σ9.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat-1-p)) :=
    obs_btaken_other hobs9 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs10_8
  obtain ⟨vmi9, hmi9⟩ := obs_btaken_minstret hobs9
  have hbufinv9 : BufInv top m (p+1) σ9.mem := by rw [hmem9]; exact hbufinv8
  have hmem9q : σ9.mem = c.σ.mem := by
    rw [hmem9, hmem8, hmem7, hmem6, hmem5, hmem4q]
  have hframeX : ∀ R, NotWrittenL R → σ9.regs.get? R = c.σ.regs.get? R := by
    intro R hR
    have e9 : σ9.regs.get? R = σ8.regs.get? R := frameL_btaken_sn3 hobs9 R hR
    have e8 : σ8.regs.get? R = σ7.regs.get? R := frameL_alu hobs8 R (by obtain ⟨_,_,_,_,_,_,h8,_⟩ := hR; exact h8) hR
    have e7 : σ7.regs.get? R = σ6.regs.get? R := frameL_alu hobs7 R (by obtain ⟨_,_,_,_,_,_,_,_,_,h25,_⟩ := hR; exact h25) hR
    have e6 : σ6.regs.get? R = σ5.regs.get? R := frameL_alu hobs6 R (by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,h15,_⟩ := hR; exact h15) hR
    have e5 : σ5.regs.get? R = c4.σ.regs.get? R := frameL_alu hobs5 R (by obtain ⟨_,_,_,_,_,_,_,h22,_⟩ := hR; exact h22) hR
    have e4 : c4.σ.regs.get? R = σ3.regs.get? R := hframe4 R (notWrittenL_toCore hR)
    have e3 : σ3.regs.get? R = σ2.regs.get? R := frameL_jal hobs3 R (by obtain ⟨_,_,_,_,hx1,_⟩ := hR; exact hx1) hR
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frameL_alu hobs2 R (by obtain ⟨_,h11,_⟩ := hR; exact h11) hR
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frameL_alu hobs1 R (by obtain ⟨h10,_⟩ := hR; exact h10) hR
    rw [e9, e8, e7, e6, e5, e4, e3, e2, e1]
  refine ⟨⟨σ9, i9, c4.steps+1+1+1+1+1⟩, ?_, hG9, hpc9, hs7_9, hbufinv9, hi9, ⟨vmi9, hmi9⟩, hmem9q,
    hs10_9, hframeX⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
    (hs4.trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans
    ((Steps.single hstep8).trans (Steps.single hstep9))))))))

/-! ## The `Triple.loop` assembly — `decimalLoop_spec`

Invariant `DLI`: at the loop head `0x800082fc` in some `LSt g top m p`.  Guard
`DLB`: additionally `m / 10^p > 9` (the `bgeu` at `0x80008318` will be *not*
taken).  Measure `DLMu`: `m / 10^p` at the head (`0` off it) — strictly decreasing
each iteration since `m / 10^(p+1) < m / 10^p` for `m / 10^p > 9`.  `Triple.loop`
delivers `LSt p ∧ ¬(m/10^p > 9)`, i.e. `LSt p` with `m/10^p ≤ 9`; `loop_exit`
then steps the head prefix to `0x80008358` with the complete digit buffer. -/

/-- Loop invariant: at the head in some `LSt g top m p`. -/
def DLI (g : (R : Register) → Option (RegisterType R)) (top : BitVec 64) (m : Nat) (c : Config) : Prop :=
  ∃ p, LSt g top m p c

/-- Loop guard: at the head with `m / 10^p > 9` (continue). -/
def DLB (g : (R : Register) → Option (RegisterType R)) (top : BitVec 64) (m : Nat) (c : Config) : Prop :=
  ∃ p, LSt g top m p c ∧ 9 < m / 10^p

open Classical in
/-- Measure: `m / 10^p` at the head, else `0`. -/
noncomputable def DLMu (g : (R : Register) → Option (RegisterType R)) (top : BitVec 64) (m : Nat) (c : Config) : Nat :=
  if h : ∃ p, LSt g top m p c then m / 10^(Classical.choose h) else 0

/-- `LSt` pins the running value `s0 = ofNat (m/10^p)`; since `LSt` at a given
`c` fixes `p` (via `s0`), the measure is well-defined. This extracts that the
`Classical.choose`n `p` gives the same `m/10^p` as any witnessed `p`. -/
theorem lst_p_unique (g : (R : Register) → Option (RegisterType R)) (top : BitVec 64) (m p q : Nat)
    (hm : m < 2^64) (c : Config) (hp : LSt g top m p c) (hq : LSt g top m q c) :
    m / 10^p = m / 10^q := by
  have h1 := hp.s0; have h2 := hq.s0
  rw [h1] at h2
  have heq : (BitVec.ofNat 64 (m/10^p)) = (BitVec.ofNat 64 (m/10^q)) := by injection h2
  have hp' : m / 10^p < 2^64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm
  have hq' : m / 10^q < 2^64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm
  have := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp', Nat.mod_eq_of_lt hq'] at this
  exact this

/-- Memory frame of the digit loop: everything outside the 20-byte digit window
`[top-20, top)` reads as in the pre-loop memory `m0`.  The sign byte at `sp+167`
and the caller's world live in this domain — the flush reads them after the loop. -/
def DigitFrame (top : BitVec 64) (m0 mem : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ a, (a < top.toNat - 20 ∨ top.toNat ≤ a) → mem[a]? = m0[a]?

theorem digitFrame_rfl (top : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    DigitFrame top m0 m0 := fun _ _ => rfl

/-- One in-window byte insert preserves the frame. -/
theorem digitFrame_insert (top : BitVec 64) (m0 mem : Std.ExtHashMap Nat (BitVec 8))
    (k : Nat) (v : BitVec 8) (hk : top.toNat - 20 ≤ k ∧ k < top.toNat)
    (h : DigitFrame top m0 mem) : DigitFrame top m0 (mem.insert k v) := by
  intro a ha
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]
  exact h a ha

theorem decimalLoop_spec (g : (R : Register) → Option (RegisterType R))
    (top : BitVec 64) (m : Nat) (hm : m < 2^64) (htop : TopOk top)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (fun c => (∃ p, LSt g top m p c ∧ p + 1 ≤ 20 ∧ (p = 0 ∨ 9 < m / 10 ^ (p - 1)))
        ∧ DigitFrame top m0 c.σ.mem)
      (fun c => ∃ p, m / 10^p ≤ 9 ∧ p + 1 ≤ 20 ∧ (p = 0 ∨ 9 < m / 10 ^ (p - 1)) ∧
        c.σ.regs.get? Register.PC = some (0x80008358#64) ∧
        c.σ.regs.get? Register.x23 = some (BitVec.ofNat 64 (p+1)) ∧
        BufInv top m (p+1) c.σ.mem ∧ GoodState c.σ ∧ c.tick < 2 ∧
        (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ DigitFrame top m0 c.σ.mem ∧
        c.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat - 1 - p)) ∧
        Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem ∧
        (∀ R, NotWrittenL R → c.σ.regs.get? R = g R)) := by
  -- body: one guarded iteration decreases the measure and keeps the frame.
  -- The invariant carries the digit-count bound `p + 1 ≤ 20` (a 64-bit magnitude
  -- has ≤ 20 decimal digits); it is preserved because each iteration runs only
  -- when the guard `9 < m/10^p` holds, whence `p_bound_sn3` gives `p + 2 ≤ 20`.
  have body : ∀ n, Triple
      (fun c => ((∃ p, LSt g top m p c ∧ p + 1 ≤ 20 ∧ (p = 0 ∨ 9 < m / 10 ^ (p - 1))) ∧ DigitFrame top m0 c.σ.mem) ∧ DLB g top m c ∧ DLMu g top m c = n)
      (fun c => ((∃ p, LSt g top m p c ∧ p + 1 ≤ 20 ∧ (p = 0 ∨ 9 < m / 10 ^ (p - 1))) ∧ DigitFrame top m0 c.σ.mem) ∧ DLMu g top m c < n) := by
    intro n c ⟨⟨hI, hFr⟩, ⟨p, hLSt, hgt⟩, hmu⟩
    obtain ⟨c', hs', hLSt', hmem'⟩ := loop_iter g top m p hm htop hgt c hLSt
    have hp20 : p + 2 ≤ 20 := p_bound_sn3 m p hm hgt
    have hFr' : DigitFrame top m0 c'.σ.mem := by
      rw [hmem']
      exact digitFrame_insert top m0 c.σ.mem _ _ (by obtain ⟨ht1, ht2⟩ := htop; omega) hFr
    refine ⟨c', hs', ⟨⟨p+1, hLSt', by omega,
      Or.inr (by simp only [Nat.add_sub_cancel]; exact hgt)⟩, hFr'⟩, ?_⟩
    -- DLMu c = m/10^p (via LSt-pins-p), DLMu c' = m/10^(p+1) < m/10^p
    have hex : ∃ q, LSt g top m q c := ⟨p, hLSt⟩
    have hex' : ∃ q, LSt g top m q c' := ⟨p+1, hLSt'⟩
    have hmuc : DLMu g top m c = m / 10^p := by
      simp only [DLMu, dif_pos hex]
      exact lst_p_unique g top m _ p hm c (Classical.choose_spec hex) hLSt
    have hmuc' : DLMu g top m c' = m / 10^(p+1) := by
      simp only [DLMu, dif_pos hex']
      exact lst_p_unique g top m _ (p+1) hm c' (Classical.choose_spec hex') hLSt'
    rw [hmuc'] ; rw [← hmu, hmuc]
    -- m/10^(p+1) < m/10^p since m/10^p > 9
    have : m / 10^(p+1) = (m / 10^p) / 10 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    rw [this]; exact Nat.div_lt_self (by omega) (by decide)
  have hloop := Triple.loop (I := fun c => (∃ p, LSt g top m p c ∧ p + 1 ≤ 20 ∧ (p = 0 ∨ 9 < m / 10 ^ (p - 1))) ∧ DigitFrame top m0 c.σ.mem)
    (B := DLB g top m) (DLMu g top m) body
  refine hloop.seq ?_
  intro c ⟨⟨hI, hFr⟩, hnB⟩
  obtain ⟨p, hLSt, hpb, hmin⟩ := hI
  -- ¬DLB ⇒ ¬(9 < m/10^p) ⇒ m/10^p ≤ 9
  have hexit : m / 10^p ≤ 9 := by
    rcases Nat.lt_or_ge 9 (m / 10^p) with h | h
    · exact absurd ⟨p, hLSt, h⟩ hnB
    · exact h
  obtain ⟨c', hs', hG', hpc', hs7', hbuf', htick', hmi', hmemeq', hs10', hframe'⟩ :=
    loop_exit g top m p hm htop hexit c hLSt
  refine ⟨c', hs', p, hexit, hpb, hmin, hpc', hs7', hbuf', hG', htick', hmi', by rw [hmemeq']; exact hFr,
    hs10', by rw [hmemeq']; exact hLSt.loaded, ?_⟩
  intro R hR
  rw [hframe' R hR]
  exact hLSt.hframe R hR

end Vsa.Sim
