import Vsa.Sim.MemcpySpec3
import Vsa.Sim.MemcpySites4
import Vsa.Triple
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `memcpy` dispatch prologue, no-tail exit, and unified spec

Builds on `Vsa/Sim/MemcpySpec3.lean` (the small word-loop rule `word_loop_spec`,
the byte-tail epilogue `epilogue_tail_spec`, and the epilogue plumbing
`epilogue_a2`/`epilogue_ptr`/`mask_low3`) and `Vsa/Sim/MemcpySites4.lean` (the
per-site steps for the dispatch prologue `[0x80006bc8, 0x80006bf8]` and the `c3c`
`ret`).

## Task a — no-tail exit (`epilogue_notail_spec`)

When the word loop copies exactly `p = n/8` words with `8p = n` (whole copy
word-aligned), the epilogue's `c38 bltu a4,a7` is *not*-taken (`a4 = dst+8p =
dst+n = a7`), falling to the `c3c ret`.  This mirrors `epilogue_tail_spec` but the
seven epilogue ALU steps are followed by `ret` instead of the byte loop.

## Task b — dispatch transitions (`bc8 → {byte | word}`)

The dispatch classifies `(dst, src, n)` and routes:
* misaligned (`(src ^^^ dst) &&& 7 ≠ 0`) — `bd4` taken → byte path `c40`;
* small (`n < 8`) — `bdc` taken → byte path `c40`;
* aligned, `n ≥ 8`, and (via `P`) `dst%8 = 0`, `8p ≤ 64` — fall through the
  classification to the small word-loop setup `bfc`/`c00`/`c04` (`PreW`).

## Task c — unified spec (`memcpy_spec`)

The single total-correctness triple from the function entry `0x80006bc8`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## No-tail exit -/

/-- `bltu a4,a7` at `c38`, not-taken when `8p = n`: `a4 = dst+8p`, `a7 = dst+n`,
`8p = n` ⇒ equal pointers ⇒ `<u` false. -/
theorem bltu_notail_false (dst : BitVec 64) (n p : Nat) (heq : 8 * p = n) :
    zopz0zI_u (dst + BitVec.ofNat 64 (8 * p)) (dst + BitVec.ofNat 64 n) = false := by
  rw [heq]
  unfold zopz0zI_u Sail.BitVec.toNatInt
  rw [decide_eq_false_iff_not]
  exact fun h => absurd (Int.ofNat_lt.mp h) (Nat.lt_irrefl _)

/-- The `memcpy` post specialized to the return address `r`, destination `dst`,
byte count `n`, ghost byte function `bs`, and ghost frame `g` (`NotWrittenB`).
Identical in shape to `memcpy_bytepath_post`. -/
abbrev memcpy_post (g : (R : Register) → Option (RegisterType R)) (r dst : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  memcpy_bytepath_post g r dst n m0 bs c

/-- **No-tail exit composition**: from `StWDone` (word loop done, `1 ≤ p`) with the
copy exactly word-aligned (`8p = n`), the epilogue recomputes the pointers, the
`c38 bltu` is not-taken, and the `c3c ret` returns to `r` with all `n` bytes
copied — reaching `memcpy_bytepath_post`.  Fresh ghost `g'` (the epilogue rewrites
the frame across the `NotWrittenW → NotWrittenB` boundary; the post's own frame
re-exposes every untouched register).  Requires `r` 4-aligned (for the `ret`). -/
theorem epilogue_notail_spec (g : (R : Register) → Option (RegisterType R)) (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (hpos : 1 ≤ p) (hnotail : 8 * p = n) (halign : r.toNat % 4 = 0) :
    Triple (fun c => StWDone g p r dst src n m0 bs c)
      (fun c => ∃ g', memcpy_bytepath_post g' r dst n m0 bs c) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha4, ha7, hra, ⟨vmi, hmi⟩, htick,
    hreg, hda, hsa, hple, hminv, _⟩ := hSt
  have hnw := hreg.dst_nowrap
  -- === c1c: addi a2,a2,-1 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006c1c c.σ c.tick c.steps (0x80006c1c#64) vmi (dst + BitVec.ofNat 64 (8 * p))
      hgood hpc hmi ha2 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006c20#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006c1c#64) 4 = (0x80006c20#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha4_1 := obs_alu_other' hobs1 Register.x14 (by decide) ha4
  have ha7_1 := obs_alu_other' hobs1 Register.x17 (by decide) ha7
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha2_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- === c20: sub a2,a2,a4 ===  (a4 = dst)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006c20 σ1 i1 (c.steps + 1) (0x80006c20#64) vmi1
      ((dst + BitVec.ofNat 64 (8 * p)) + sign_extend (m := 64) (0xfff#12)) dst
      hG1 hpc1 hmi1' ha2_1 ha4_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006c24#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006c20#64) 4 = (0x80006c24#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have ha7_2 := obs_alu_other' hobs2 Register.x17 (by decide) ha7_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha2_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- === c24: andi a2,a2,-8 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006c24 σ2 i2 (c.steps + 1 + 1) (0x80006c24#64) vmi2
      (((dst + BitVec.ofNat 64 (8 * p)) + sign_extend (m := 64) (0xfff#12)) - dst)
      hG2 hpc2 hmi2' ha2_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006c28#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006c24#64) 4 = (0x80006c28#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_alu_other' hobs3 Register.x11 (by decide) ha1_2
  have ha4_3 := obs_alu_other' hobs3 Register.x14 (by decide) ha4_2
  have ha7_3 := obs_alu_other' hobs3 Register.x17 (by decide) ha7_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha2_3 : σ3.regs.get? Register.x12 = some (BitVec.ofNat 64 (8 * (p - 1))) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [epilogue_a2 dst p (by omega) (by omega)] at this
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- === c28: addi a1,a1,8 ===  (a1 = src)
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006c28 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006c28#64) vmi3 src
      hG3 hpc3 hmi3' ha1_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006c2c#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006c28#64) 4 = (0x80006c2c#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
  have ha4_4 := obs_alu_other' hobs4 Register.x14 (by decide) ha4_3
  have ha7_4 := obs_alu_other' hobs4 Register.x17 (by decide) ha7_3
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have ha2_4 := obs_alu_other' hobs4 Register.x12 (by decide) ha2_3
  have ha1_4 : σ4.regs.get? Register.x11 = some (src + sign_extend (m := 64) (0x008#12)) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- === c2c: addi a4,a4,8 ===  (a4 = dst)
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006c2c σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006c2c#64) vmi4 dst
      hG4 hpc4 hmi4' ha4_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006c30#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006c2c#64) 4 = (0x80006c30#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other' hobs5 Register.x10 (by decide) ha0_4
  have ha7_5 := obs_alu_other' hobs5 Register.x17 (by decide) ha7_4
  have hra_5 := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have ha2_5 := obs_alu_other' hobs5 Register.x12 (by decide) ha2_4
  have ha1_5 := obs_alu_other' hobs5 Register.x11 (by decide) ha1_4
  have ha4_5 := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  -- === c30: add a1,a1,a2 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006c30 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006c30#64) vmi5
      (src + sign_extend (m := 64) (0x008#12)) (BitVec.ofNat 64 (8 * (p - 1)))
      hG5 hpc5 hmi5' ha1_5 ha2_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006c34#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006c30#64) 4 = (0x80006c34#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other' hobs6 Register.x10 (by decide) ha0_5
  have ha7_6 := obs_alu_other' hobs6 Register.x17 (by decide) ha7_5
  have hra_6 := obs_alu_other' hobs6 Register.x1 (by decide) hra_5
  have ha2_6 := obs_alu_other' hobs6 Register.x12 (by decide) ha2_5
  have ha4_6 := obs_alu_other' hobs6 Register.x14 (by decide) ha4_5
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  -- === c34: add a4,a4,a2 ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80006c34 σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80006c34#64) vmi6
      (dst + sign_extend (m := 64) (0x008#12)) (BitVec.ofNat 64 (8 * (p - 1)))
      hG6 hpc6 hmi6' ha4_6 ha2_6 (by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x80006c38#64 : BitVec 64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80006c34#64) 4 = (0x80006c38#64 : BitVec 64) from by decide] at this
  have ha0_7 := obs_alu_other' hobs7 Register.x10 (by decide) ha0_6
  have ha7_7 := obs_alu_other' hobs7 Register.x17 (by decide) ha7_6
  have hra_7 := obs_alu_other' hobs7 Register.x1 (by decide) hra_6
  have ha4_7 : σ7.regs.get? Register.x14 = some (dst + BitVec.ofNat 64 (8 * p)) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [epilogue_ptr dst p (by omega)] at this
  obtain ⟨vmi7, hmi7'⟩ := obs_alu_minstret hobs7
  have hmem7eq : σ7.mem = c.σ.mem := by rw [hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  -- === c38: bltu a4,a7 not-taken (8p = n) → c3c ===
  have hv : zopz0zI_u (dst + BitVec.ofNat 64 (8 * p)) (dst + BitVec.ofNat 64 n) = false :=
    bltu_notail_false dst n p hnotail
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80006c38_nottaken σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006c38#64) vmi7
      (dst + BitVec.ofNat 64 (8 * p)) (dst + BitVec.ofNat 64 n)
      hG7 hpc7 hmi7' ha4_7 ha7_7 (by rw [hmem7eq]; exact hloaded) rfl hv hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x80006c3c#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs8
    rwa [show BitVec.addInt (0x80006c38#64) 4 = (0x80006c3c#64 : BitVec 64) from by decide] at this
  have ha0_8 := obs_bnottaken_other' hobs8 Register.x10 (by decide) ha0_7
  have hra_8 := obs_bnottaken_other' hobs8 Register.x1 (by decide) hra_7
  obtain ⟨vmi8, hmi8'⟩ := obs_bnottaken_minstret hobs8
  have hmem8eq : σ8.mem = c.σ.mem := by rw [hmem8, hmem7eq]
  -- === c3c: ret → r ===
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halign]; exact halign
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80006c3c σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006c3c#64) vmi8 r
      hG8 hpc8 hmi8' hra_8 (by rw [hmem8eq]; exact hloaded) rfl htgt hi8
  have hpc9 : σ9.regs.get? Register.PC = some r := by
    rw [obs_jr_pc hobs9, ret_tgt r halign]
  have ha0_9 := obs_jr_other' hobs9 Register.x10 (by decide) ha0_8
  have hra_9 := obs_jr_other' hobs9 Register.x1 (by decide) hra_8
  have hmem9eq : σ9.mem = c.σ.mem := by rw [hmem9, hmem8eq]
  -- MemInv at 8p = n gives the described update
  have hminv_n : MemInv dst src n bs n m0 c.σ.mem := hnotail ▸ hminv
  have hsteps : Steps c ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ :=
    ((((((((Steps.single (by cases c; exact hs1)).trans (Steps.single hs2)).trans
      (Steps.single hs3)).trans (Steps.single hs4)).trans (Steps.single hs5)).trans
      (Steps.single hs6)).trans (Steps.single hs7)).trans (Steps.single hs8)).trans (Steps.single hs9)
  refine ⟨⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, hsteps,
    fun R => σ9.regs.get? R, ?_⟩
  refine ⟨hG9, hpc9, ha0_9, hra_9, ?_, ?_, hi9, fun R _ => rfl⟩
  · intro k hk; rw [hmem9eq]; exact hminv_n.copied k hk
  · intro a ha; rw [hmem9eq]; exact hminv_n.outside a ha

/-! ## Dispatch prologue transitions (`bc8 → {byte | word}`)

The dispatch classifies `(dst, src, n)`.  It performs no stores, so `MemInv … 0`
transfers unchanged from the entry state to the routed target.  Fresh ghosts per
the crossover pattern (the entry ghost `g` cannot survive the frame rewrite across
the classification, but each target predicate's own frame re-exposes untouched
registers). -/

/-! ### Mask facts (`andi …,7` and `andi …,-8` bitwise route) -/

/-- `(v &&& sext 0x007).toNat = v.toNat % 8`. -/
theorem and7_toNat (v : BitVec 64) : (v &&& sign_extend (m := 64) (0x007#12)).toNat = v.toNat % 8 := by
  rw [BitVec.toNat_and, show (sign_extend (m := 64) (0x007#12) : BitVec 64).toNat = 7 from by decide,
    show (7:Nat) = 2^3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, show (2:Nat)^3 = 8 from rfl]

/-- `(v &&& sext 0x007) ≠ 0#64` iff `v.toNat % 8 ≠ 0`. -/
theorem and7_ne_zero_iff (v : BitVec 64) :
    ((v &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = true ↔ v.toNat % 8 ≠ 0 := by
  rw [bne_iff_ne, ne_eq, ne_eq]
  constructor
  · intro h hmod; exact h (by apply BitVec.eq_of_toNat_eq; rw [and7_toNat]; simpa using hmod)
  · intro hmod h; exact hmod (by have := congrArg BitVec.toNat h; rwa [and7_toNat, BitVec.toNat_ofNat] at this)

/-- `(v &&& sext 0x007) = 0#64` when `v.toNat % 8 = 0` — and then the `bnez` guard is false. -/
theorem and7_eq_zero_false (v : BitVec 64) (hmod : v.toNat % 8 = 0) :
    ((v &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = false := by
  rw [bne_eq_false_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [and7_toNat]; simpa using hmod

/-- `(x ^^^ y).toNat = x.toNat ^^^ y.toNat`. -/
theorem xor_toNat (x y : BitVec 64) : (x ^^^ y).toNat = x.toNat ^^^ y.toNat := by
  rw [BitVec.toNat_xor]

/-- If `(a ^^^ b) % 8 = 0` and `b % 8 = 0` then `a % 8 = 0` (low-3-bit xor). -/
theorem src_align_of_xor (a b : Nat) (hxor : (a ^^^ b) % 8 = 0) (hb : b % 8 = 0) : a % 8 = 0 := by
  have h : (a ^^^ b) % 8 = (a % 8) ^^^ (b % 8) := by
    rw [show (8:Nat) = 2^3 from rfl, Nat.xor_mod_two_pow]
  rw [hb, Nat.xor_zero] at h
  omega

/-- `sltiu v 8` value: `true` iff `v.toNat < 8`. -/
theorem sltiu8_val (v : BitVec 64) :
    zopz0zI_u v (sign_extend (m := 64) (0x008#12)) = true ↔ v.toNat < 8 := by
  unfold zopz0zI_u Sail.BitVec.toNatInt
  rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 from by decide, decide_eq_true_iff]
  constructor
  · intro h; have := Int.ofNat_lt.mp h; omega
  · intro h; exact Int.ofNat_lt.mpr h

/-- `sltiu v 8` written value nonzero iff `v.toNat < 8`. -/
theorem sltiu8_ne_zero_iff (v : BitVec 64) :
    ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x008#12))))) != (0#64)) = true
      ↔ v.toNat < 8 := by
  rw [bne_iff_ne, ne_eq]
  by_cases hlt : v.toNat < 8
  · have hv : zopz0zI_u v (sign_extend (m := 64) (0x008#12)) = true := (sltiu8_val v).mpr hlt
    rw [hv]
    simp only [hlt, iff_true]
    intro h; exact absurd (congrArg BitVec.toNat h) (by decide)
  · have hv : zopz0zI_u v (sign_extend (m := 64) (0x008#12)) = false := by
      cases h : zopz0zI_u v (sign_extend (m := 64) (0x008#12)) with
      | false => rfl
      | true => exact absurd ((sltiu8_val v).mp h) hlt
    rw [hv, show (zero_extend (m := 64) (bool_to_bit false) : BitVec 64) = 0#64 from by
      apply BitVec.eq_of_toNat_eq; decide]
    simp only [hlt, iff_false, Classical.not_not]

/-- Same, false direction (`v.toNat ≥ 8` ⇒ the `bnez` guard is false). -/
theorem sltiu8_ge_false (v : BitVec 64) (hge : 8 ≤ v.toNat) :
    ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x008#12))))) != (0#64)) = false := by
  have hv : zopz0zI_u v (sign_extend (m := 64) (0x008#12)) = false := by
    cases h : zopz0zI_u v (sign_extend (m := 64) (0x008#12)) with
    | false => rfl
    | true => have := (sltiu8_val v).mp h; omega
  rw [hv, show (zero_extend (m := 64) (bool_to_bit false) : BitVec 64) = 0#64 from by
    apply BitVec.eq_of_toNat_eq; decide]
  simp

/-- `andi a2,a7,-8` on `a7 = dst+n` with `dst%8 = 0`: `(dst+n) &&& ~7 = dst + 8*(n/8)`. -/
theorem andneg8_dst_span (dst : BitVec 64) (n : Nat) (hda : dst.toNat % 8 = 0)
    (hnw : dst.toNat + n < 2^64) :
    ((dst + BitVec.ofNat 64 n) &&& sign_extend (m := 64) (0xff8#12))
      = dst + BitVec.ofNat 64 (8 * (n / 8)) := by
  have hspan : (dst + BitVec.ofNat 64 n).toNat = dst.toNat + n := ptr_toNat dst n hnw
  have hmask : (sign_extend (m := 64) (0xff8#12) : BitVec 64) = BitVec.ofNat 64 (2^64 - 8) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hmask]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, hspan, BitVec.toNat_ofNat,
    show (2^64 - 8) % 2^64 = 2^64 - 8 from Nat.mod_eq_of_lt (by omega),
    mask_low3 (dst.toNat + n) (by omega)]
  -- (dst+n)/8*8 = dst + 8*(n/8), using dst%8 = 0
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    show (8 * (n / 8)) % 2^64 = 8 * (n / 8) from Nat.mod_eq_of_lt (by omega)]
  have hkey : (dst.toNat + n) / 8 * 8 = dst.toNat + 8 * (n / 8) := by omega
  rw [hkey, Nat.mod_eq_of_lt (by omega)]

/-- `sub a3,a2,a4`: `(dst + ofNat k) - dst = ofNat k`. -/
theorem sub_base_span (dst : BitVec 64) (k : Nat) :
    (dst + BitVec.ofNat 64 k) - dst = BitVec.ofNat 64 k := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

/-- `blt a5,a3` with `a5 = 64`, `a3 = ofNat(8p)` and `8p ≤ 64`: not-taken (`64 ≥s 8p`). -/
theorem blt64_span_false (p : Nat) (hle : 8 * p ≤ 64) :
    zopz0zI_s ((0#64) + sign_extend (m := 64) (0x040#12)) (BitVec.ofNat 64 (8 * p)) = false := by
  have hlhs : ((0#64) + sign_extend (m := 64) (0x040#12) : BitVec 64) = BitVec.ofNat 64 64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hlhs]
  unfold zopz0zI_s
  rw [decide_eq_false_iff_not]
  intro h
  have h64 : (BitVec.ofNat 64 64).toInt = ((64 : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, show (BitVec.ofNat 64 64).toNat = 64 from by decide, if_pos (by decide)]
  have hp : (BitVec.ofNat 64 (8 * p)).toInt = ((8 * p : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_cond,
      show (BitVec.ofNat 64 (8 * p)).toNat = 8 * p from by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega),
      if_pos (by omega)]
  rw [h64, hp] at h
  omega

/-! ### Dispatch entry predicate (`0x80006bc8`) -/

/-- Entry precondition at the `memcpy` entry `0x80006bc8`: the ABI-in registers
(`a0 = dst`, `a1 = src`, `a2 = n`), the return address `x1 = r`, region
well-formedness, `n > 0`, and the described-memory invariant at `i = 0` (nothing
copied yet). -/
structure PreDispatch (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006bc8#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  a2 : c.σ.regs.get? Register.x12 = some (BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : Regions dst src n
  npos : 0 < n
  meminv : MemInv dst src n bs 0 m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenB R → c.σ.regs.get? R = g R

/-! ### `a2 = ofNat n` reads back as `n` under no-wrap -/

theorem a2_ofNat_toNat (n : Nat) (hn : n < 2^64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn

/-! ### Common dispatch prefix `bc8 → bd4` (three ALU steps to the first branch)

Runs `xor a5,a1,a0`; `andi a5,a5,7`; `add a7,a0,a2`, reaching `0x80006bd4` with
`a5 = (src^^^dst)&&&7`, `a7 = dst+n`, and `a0/a1/a2/ra` intact.  Packaged as an
intermediate config predicate `AtBd4`. -/
structure AtBd4 (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006bd4#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  a2 : c.σ.regs.get? Register.x12 = some (BitVec.ofNat 64 n)
  a5 : c.σ.regs.get? Register.x15 = some ((src ^^^ dst) &&& sign_extend (m := 64) (0x007#12))
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : Regions dst src n
  npos : 0 < n
  meminv : MemInv dst src n bs 0 m0 c.σ.mem

theorem to_bd4 (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (PreDispatch g r dst src n m0 bs) (AtBd4 r dst src n m0 bs) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, hra, ⟨vmi, hmi⟩, htick, hreg, hnpos, hminv, _⟩ := hPre
  -- === bc8: xor a5,a1,a0 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006bc8 c.σ c.tick c.steps (0x80006bc8#64) vmi src dst
      hgood hpc hmi ha1 ha0 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006bcc#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006bc8#64) 4 = (0x80006bcc#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha2_1 := obs_alu_other' hobs1 Register.x12 (by decide) ha2
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha5_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- === bcc: andi a5,a5,7 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006bcc σ1 i1 (c.steps + 1) (0x80006bcc#64) vmi1 (src ^^^ dst)
      hG1 hpc1 hmi1' ha5_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006bd0#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006bcc#64) 4 = (0x80006bd0#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha2_2 := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- === bd0: add a7,a0,a2 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006bd0 σ2 i2 (c.steps + 1 + 1) (0x80006bd0#64) vmi2 dst (BitVec.ofNat 64 n)
      hG2 hpc2 hmi2' ha0_2 ha2_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006bd4#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006bd0#64) 4 = (0x80006bd4#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_alu_other' hobs3 Register.x11 (by decide) ha1_2
  have ha2_3 := obs_alu_other' hobs3 Register.x12 (by decide) ha2_2
  have ha5_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha5_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha7_3 := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩,
    ((Steps.single (by cases c; exact hs1)).trans (Steps.single hs2)).trans (Steps.single hs3), ?_⟩
  exact ⟨hG3, by rw [hmem3eq]; exact hloaded, hpc3, ha0_3, ha1_3, ha2_3, ha5_3, ha7_3, hra_3,
    ⟨_, hmi3'⟩, hi3, hreg, hnpos, by rw [hmem3eq]; exact hminv⟩

/-! ### Misaligned byte route: `bd4` taken → `c40` (`PreB`)

When `(src ^^^ dst) &&& 7 ≠ 0` (source/destination not congruent mod 8), the
`bnez a5` at `bd4` is taken, jumping to the byte-path prefix `0x80006c40`.  The
byte-path ghost is fresh (`∃ g'`). -/
theorem dispatch_misaligned_to_byte (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (hmis : (src.toNat ^^^ dst.toNat) % 8 ≠ 0) :
    Triple (AtBd4 r dst src n m0 bs) (fun c => ∃ g', PreB g' r dst src n m0 bs c) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha5, ha7, hra, ⟨vmi, hmi⟩, htick, hreg, hnpos, hminv⟩ := hSt
  have hv : (((src ^^^ dst) &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = true := by
    rw [and7_ne_zero_iff]; rw [xor_toNat] at *; exact hmis
  have htgt : ((0x80006bd4#64 : BitVec 64) + sign_extend (m := 64) (0x006c#13)).toNat % 4 = 0 := by decide
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006bd4_taken c.σ c.tick c.steps (0x80006bd4#64) vmi
      ((src ^^^ dst) &&& sign_extend (m := 64) (0x007#12))
      hgood hpc hmi ha5 hloaded rfl htgt hv htick
  have hpceq : (0x80006bd4#64 : BitVec 64) + sign_extend (m := 64) (0x006c#13) = (0x80006c40#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hpc' : σ'.regs.get? Register.PC = some (0x80006c40#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs, hpceq]
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, fun R => σ'.regs.get? R, ?_⟩
  refine ⟨hG', by rw [hmem']; exact hloaded, hpc',
    obs_btaken_other' hobs Register.x10 (by decide) ha0,
    obs_btaken_other' hobs Register.x11 (by decide) ha1,
    obs_btaken_other' hobs Register.x17 (by decide) ha7,
    obs_btaken_other' hobs Register.x1 (by decide) hra,
    obs_btaken_minstret hobs, hi', hreg, hnpos, by rw [hmem']; exact hminv, fun R _ => rfl⟩

/-! ### Small byte route: `bd4` nottaken → `bd8` → `bdc` taken → `c40` (`PreB`)

When aligned (`(src ^^^ dst) &&& 7 = 0`) but small (`n < 8`), `bd4` is not-taken,
`bd8 sltiu a2,a2,8` sets `a2 := 1` (since `n < 8`), and `bdc bnez a2` is taken to
the byte path.  Note `a2` is clobbered but the byte path recomputes what it needs;
`PreB`'s `a2` field is absent (the byte path re-derives `a7 = dst+n`). -/
theorem dispatch_small_to_byte (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign_xor : (src.toNat ^^^ dst.toNat) % 8 = 0) (hsmall : n < 8) :
    Triple (AtBd4 r dst src n m0 bs) (fun c => ∃ g', PreB g' r dst src n m0 bs c) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha5, ha7, hra, ⟨vmi, hmi⟩, htick, hreg, hnpos, hminv⟩ := hSt
  -- === bd4: bnez a5 nottaken (a5 = 0, aligned) → bd8 ===
  have hv4 : (((src ^^^ dst) &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = false := by
    apply and7_eq_zero_false; rw [xor_toNat]; exact halign_xor
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006bd4_nottaken c.σ c.tick c.steps (0x80006bd4#64) vmi
      ((src ^^^ dst) &&& sign_extend (m := 64) (0x007#12))
      hgood hpc hmi ha5 hloaded rfl hv4 htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006bd8#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006bd4#64) 4 = (0x80006bd8#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_bnottaken_other' hobs1 Register.x11 (by decide) ha1
  have ha2_1 := obs_bnottaken_other' hobs1 Register.x12 (by decide) ha2
  have ha7_1 := obs_bnottaken_other' hobs1 Register.x17 (by decide) ha7
  have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  -- === bd8: sltiu a2,a2,8  (a2 := (n<8 ? 1 : 0) = nonzero) → bdc ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006bd8 σ1 i1 (c.steps + 1) (0x80006bd8#64) vmi1 (BitVec.ofNat 64 n)
      hG1 hpc1 hmi1' ha2_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006bdc#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006bd8#64) 4 = (0x80006bdc#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha7_2 := obs_alu_other' hobs2 Register.x17 (by decide) ha7_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha2_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  -- === bdc: bnez a2 taken (n < 8 ⇒ a2 ≠ 0) → c40 ===
  have hvdc : ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (BitVec.ofNat 64 n) (sign_extend (m := 64) (0x008#12))))) != (0#64)) = true := by
    rw [sltiu8_ne_zero_iff]; rw [a2_ofNat_toNat n (by have := hreg.dst_nowrap; omega)]; exact hsmall
  have htgt : ((0x80006bdc#64 : BitVec 64) + sign_extend (m := 64) (0x0064#13)).toNat % 4 = 0 := by decide
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006bdc_taken σ2 i2 (c.steps + 1 + 1) (0x80006bdc#64) vmi2
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (BitVec.ofNat 64 n) (sign_extend (m := 64) (0x008#12)))))
      hG2 hpc2 hmi2' ha2_2 (by rw [hmem2eq]; exact hloaded) rfl htgt hvdc hi2
  have hpceq : (0x80006bdc#64 : BitVec 64) + sign_extend (m := 64) (0x0064#13) = (0x80006c40#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006c40#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs3, hpceq]
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2eq]
  refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩,
    ((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3),
    fun R => σ3.regs.get? R, ?_⟩
  refine ⟨hG3, by rw [hmem3eq]; exact hloaded, hpc3,
    obs_btaken_other' hobs3 Register.x10 (by decide) ha0_2,
    obs_btaken_other' hobs3 Register.x11 (by decide) ha1_2,
    obs_btaken_other' hobs3 Register.x17 (by decide) ha7_2,
    obs_btaken_other' hobs3 Register.x1 (by decide) hra_2,
    obs_btaken_minstret hobs3, hi3, hreg, hnpos, by rw [hmem3eq]; exact hminv, fun R _ => rfl⟩

/-! ### Word route: `bd4/bdc/be8` nottaken → `bfc/c00/c04` (`PreW`)

When aligned (`(src ^^^ dst) &&& 7 = 0`), `n ≥ 8`, `dst % 8 = 0`, and the rounded
word count fits (`8*(n/8) ≤ 64`), the classification falls through the three
`bnez`s and the `blt`, reaching the small word-loop setup and entry `c04`
(`PreW`) with `p = n/8`.  Fresh word-loop ghost. -/
theorem dispatch_to_word (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign_xor : (src.toNat ^^^ dst.toNat) % 8 = 0) (hbig : 8 ≤ n)
    (hda : dst.toNat % 8 = 0) (hfit : 8 * (n / 8) ≤ 64) :
    Triple (AtBd4 r dst src n m0 bs)
      (fun c => ∃ g', PreW g' (n / 8) r dst src n m0 bs c) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha5, ha7, hra, ⟨vmi, hmi⟩, htick, hreg, hnpos, hminv⟩ := hSt
  have hnn := hreg.dst_nowrap
  have h8p0 : 8 * (n / 8) ≤ n := by omega
  have hppos0 : 0 < n / 8 := by omega
  generalize hp_def : n / 8 = p at hfit h8p0 hppos0 ⊢
  have h8p : 8 * p ≤ n := h8p0
  have hppos : 0 < p := hppos0
  -- === bd4: bnez a5 nottaken → bd8 ===
  have hv4 : (((src ^^^ dst) &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = false := by
    apply and7_eq_zero_false; rw [xor_toNat]; exact halign_xor
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006bd4_nottaken c.σ c.tick c.steps (0x80006bd4#64) vmi
      ((src ^^^ dst) &&& sign_extend (m := 64) (0x007#12))
      hgood hpc hmi ha5 hloaded rfl hv4 htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006bd8#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006bd4#64) 4 = (0x80006bd8#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_bnottaken_other' hobs1 Register.x11 (by decide) ha1
  have ha2_1 := obs_bnottaken_other' hobs1 Register.x12 (by decide) ha2
  have ha7_1 := obs_bnottaken_other' hobs1 Register.x17 (by decide) ha7
  have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  -- === bd8: sltiu a2,a2,8 → bdc ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006bd8 σ1 i1 (c.steps + 1) (0x80006bd8#64) vmi1 (BitVec.ofNat 64 n)
      hG1 hpc1 hmi1' ha2_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006bdc#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006bd8#64) 4 = (0x80006bdc#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha7_2 := obs_alu_other' hobs2 Register.x17 (by decide) ha7_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha2_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- === bdc: bnez a2 nottaken (n ≥ 8 ⇒ a2 = 0) → be0 ===
  have hvdc : ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (BitVec.ofNat 64 n) (sign_extend (m := 64) (0x008#12))))) != (0#64)) = false := by
    apply sltiu8_ge_false; rw [a2_ofNat_toNat n (by omega)]; exact hbig
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006bdc_nottaken σ2 i2 (c.steps + 1 + 1) (0x80006bdc#64) vmi2
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (BitVec.ofNat 64 n) (sign_extend (m := 64) (0x008#12)))))
      hG2 hpc2 hmi2' ha2_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hvdc hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006be0#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs3; rwa [show BitVec.addInt (0x80006bdc#64) 4 = (0x80006be0#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_bnottaken_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_bnottaken_other' hobs3 Register.x11 (by decide) ha1_2
  have ha7_3 := obs_bnottaken_other' hobs3 Register.x17 (by decide) ha7_2
  have hra_3 := obs_bnottaken_other' hobs3 Register.x1 (by decide) hra_2
  obtain ⟨vmi3, hmi3'⟩ := obs_bnottaken_minstret hobs3
  -- === be0: andi a5,a0,7 → be4 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006be0 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006be0#64) vmi3 dst
      hG3 hpc3 hmi3' ha0_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006be4#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006be0#64) 4 = (0x80006be4#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 := obs_alu_other' hobs4 Register.x11 (by decide) ha1_3
  have ha7_4 := obs_alu_other' hobs4 Register.x17 (by decide) ha7_3
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have ha5_4 := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- === be4: mv a4,a0 → be8 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006be4 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006be4#64) vmi4 dst
      hG4 hpc4 hmi4' ha0_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006be8#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006be4#64) 4 = (0x80006be8#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other' hobs5 Register.x10 (by decide) ha0_4
  have ha1_5 := obs_alu_other' hobs5 Register.x11 (by decide) ha1_4
  have ha7_5 := obs_alu_other' hobs5 Register.x17 (by decide) ha7_4
  have hra_5 := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have ha5_5 := obs_alu_other' hobs5 Register.x15 (by decide) ha5_4
  have ha4_5 : σ5.regs.get? Register.x14 = some dst := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show dst + sign_extend (m := 64) (0x000#12) = dst from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]; exact BitVec.add_zero dst] at this
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  -- === be8: bnez a5 nottaken (a5 = dst&7 = 0, dst%8=0) → bec ===
  have hv8 : (((dst &&& sign_extend (m := 64) (0x007#12))) != (0#64)) = false := by
    apply and7_eq_zero_false; exact hda
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006be8_nottaken σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006be8#64) vmi5
      (dst &&& sign_extend (m := 64) (0x007#12))
      hG5 hpc5 hmi5' ha5_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hv8 hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006bec#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs6; rwa [show BitVec.addInt (0x80006be8#64) 4 = (0x80006bec#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_bnottaken_other' hobs6 Register.x10 (by decide) ha0_5
  have ha1_6 := obs_bnottaken_other' hobs6 Register.x11 (by decide) ha1_5
  have ha7_6 := obs_bnottaken_other' hobs6 Register.x17 (by decide) ha7_5
  have hra_6 := obs_bnottaken_other' hobs6 Register.x1 (by decide) hra_5
  have ha4_6 := obs_bnottaken_other' hobs6 Register.x14 (by decide) ha4_5
  obtain ⟨vmi6, hmi6'⟩ := obs_bnottaken_minstret hobs6
  -- === bec: andi a2,a7,-8 → bf0 ===  (a7 = dst+n, a2 := dst + 8p)
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80006bec σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80006bec#64) vmi6
      (dst + BitVec.ofNat 64 n)
      hG6 hpc6 hmi6' ha7_6 (by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x80006bf0#64 : BitVec 64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80006bec#64) 4 = (0x80006bf0#64 : BitVec 64) from by decide] at this
  have ha0_7 := obs_alu_other' hobs7 Register.x10 (by decide) ha0_6
  have ha1_7 := obs_alu_other' hobs7 Register.x11 (by decide) ha1_6
  have ha7_7 := obs_alu_other' hobs7 Register.x17 (by decide) ha7_6
  have hra_7 := obs_alu_other' hobs7 Register.x1 (by decide) hra_6
  have ha4_7 := obs_alu_other' hobs7 Register.x14 (by decide) ha4_6
  have ha2_7 : σ7.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8 * p)) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [andneg8_dst_span dst n hda (by omega), hp_def] at this; exact this
  obtain ⟨vmi7, hmi7'⟩ := obs_alu_minstret hobs7
  -- === bf0: sub a3,a2,a4 → bf4 ===  (a3 := (dst+8p) - dst = ofNat 8p)
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80006bf0 σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006bf0#64) vmi7
      (dst + BitVec.ofNat 64 (8 * p)) dst
      hG7 hpc7 hmi7' ha2_7 ha4_7 (by rw [hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x80006bf4#64 : BitVec 64) := by
    have := obs_alu_pc hobs8; rwa [show BitVec.addInt (0x80006bf0#64) 4 = (0x80006bf4#64 : BitVec 64) from by decide] at this
  have ha0_8 := obs_alu_other' hobs8 Register.x10 (by decide) ha0_7
  have ha1_8 := obs_alu_other' hobs8 Register.x11 (by decide) ha1_7
  have ha7_8 := obs_alu_other' hobs8 Register.x17 (by decide) ha7_7
  have hra_8 := obs_alu_other' hobs8 Register.x1 (by decide) hra_7
  have ha4_8 := obs_alu_other' hobs8 Register.x14 (by decide) ha4_7
  have ha2_8 := obs_alu_other' hobs8 Register.x12 (by decide) ha2_7
  have ha3_8 : σ8.regs.get? Register.x13 = some (BitVec.ofNat 64 (8 * p)) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sub_base_span dst (8 * p)] at this
  obtain ⟨vmi8, hmi8'⟩ := obs_alu_minstret hobs8
  -- === bf4: li a5,64 → bf8 ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80006bf4 σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006bf4#64) vmi8
      hG8 hpc8 hmi8' (by rw [hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi8
  have hpc9 : σ9.regs.get? Register.PC = some (0x80006bf8#64 : BitVec 64) := by
    have := obs_alu_pc hobs9; rwa [show BitVec.addInt (0x80006bf4#64) 4 = (0x80006bf8#64 : BitVec 64) from by decide] at this
  have ha0_9 := obs_alu_other' hobs9 Register.x10 (by decide) ha0_8
  have ha1_9 := obs_alu_other' hobs9 Register.x11 (by decide) ha1_8
  have ha7_9 := obs_alu_other' hobs9 Register.x17 (by decide) ha7_8
  have hra_9 := obs_alu_other' hobs9 Register.x1 (by decide) hra_8
  have ha4_9 := obs_alu_other' hobs9 Register.x14 (by decide) ha4_8
  have ha2_9 := obs_alu_other' hobs9 Register.x12 (by decide) ha2_8
  have ha3_9 := obs_alu_other' hobs9 Register.x13 (by decide) ha3_8
  have ha5_9 := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi9, hmi9'⟩ := obs_alu_minstret hobs9
  -- === bf8: blt a5,a3 nottaken (64 ≥s 8p) → bfc ===
  have hv8b : zopz0zI_s ((0#64) + sign_extend (m := 64) (0x040#12)) (BitVec.ofNat 64 (8 * p)) = false :=
    blt64_span_false p hfit
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80006bf8_nottaken σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006bf8#64) vmi9
      ((0#64) + sign_extend (m := 64) (0x040#12)) (BitVec.ofNat 64 (8 * p))
      hG9 hpc9 hmi9' ha5_9 ha3_9 (by rw [hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hv8b hi9
  have hpc10 : σ10.regs.get? Register.PC = some (0x80006bfc#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs10; rwa [show BitVec.addInt (0x80006bf8#64) 4 = (0x80006bfc#64 : BitVec 64) from by decide] at this
  have ha0_10 := obs_bnottaken_other' hobs10 Register.x10 (by decide) ha0_9
  have ha1_10 := obs_bnottaken_other' hobs10 Register.x11 (by decide) ha1_9
  have ha7_10 := obs_bnottaken_other' hobs10 Register.x17 (by decide) ha7_9
  have hra_10 := obs_bnottaken_other' hobs10 Register.x1 (by decide) hra_9
  have ha4_10 := obs_bnottaken_other' hobs10 Register.x14 (by decide) ha4_9
  have ha2_10 := obs_bnottaken_other' hobs10 Register.x12 (by decide) ha2_9
  obtain ⟨vmi10, hmi10'⟩ := obs_bnottaken_minstret hobs10
  -- === bfc: mv a3,a1 → c00 ===  (a3 := src)
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80006bfc σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006bfc#64) vmi10 src
      hG10 hpc10 hmi10' ha1_10 (by rw [hmem10, hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi10
  have hpc11 : σ11.regs.get? Register.PC = some (0x80006c00#64 : BitVec 64) := by
    have := obs_alu_pc hobs11; rwa [show BitVec.addInt (0x80006bfc#64) 4 = (0x80006c00#64 : BitVec 64) from by decide] at this
  have ha0_11 := obs_alu_other' hobs11 Register.x10 (by decide) ha0_10
  have ha1_11 := obs_alu_other' hobs11 Register.x11 (by decide) ha1_10
  have ha7_11 := obs_alu_other' hobs11 Register.x17 (by decide) ha7_10
  have hra_11 := obs_alu_other' hobs11 Register.x1 (by decide) hra_10
  have ha4_11 := obs_alu_other' hobs11 Register.x14 (by decide) ha4_10
  have ha2_11 := obs_alu_other' hobs11 Register.x12 (by decide) ha2_10
  have ha3_11 : σ11.regs.get? Register.x13 = some src := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show src + sign_extend (m := 64) (0x000#12) = src from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]; exact BitVec.add_zero src] at this
  obtain ⟨vmi11, hmi11'⟩ := obs_alu_minstret hobs11
  -- === c00: mv a5,a4 → c04 ===  (a5 := dst)
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80006c00 σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006c00#64) vmi11 dst
      hG11 hpc11 hmi11' ha4_11 (by rw [hmem11, hmem10, hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi11
  have hpc12 : σ12.regs.get? Register.PC = some (0x80006c04#64 : BitVec 64) := by
    have := obs_alu_pc hobs12; rwa [show BitVec.addInt (0x80006c00#64) 4 = (0x80006c04#64 : BitVec 64) from by decide] at this
  have ha0_12 := obs_alu_other' hobs12 Register.x10 (by decide) ha0_11
  have ha1_12 := obs_alu_other' hobs12 Register.x11 (by decide) ha1_11
  have ha7_12 := obs_alu_other' hobs12 Register.x17 (by decide) ha7_11
  have hra_12 := obs_alu_other' hobs12 Register.x1 (by decide) hra_11
  have ha4_12 := obs_alu_other' hobs12 Register.x14 (by decide) ha4_11
  have ha2_12 := obs_alu_other' hobs12 Register.x12 (by decide) ha2_11
  have ha3_12 := obs_alu_other' hobs12 Register.x13 (by decide) ha3_11
  have ha5_12 : σ12.regs.get? Register.x15 = some dst := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show dst + sign_extend (m := 64) (0x000#12) = dst from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]; exact BitVec.add_zero dst] at this
  obtain ⟨vmi12, hmi12'⟩ := obs_alu_minstret hobs12
  have hmem12eq : σ12.mem = c.σ.mem := by
    rw [hmem12, hmem11, hmem10, hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  have hsteps : Steps c ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ :=
    (((((((((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6)).trans
      (Steps.single hs7)).trans (Steps.single hs8)).trans (Steps.single hs9)).trans
      (Steps.single hs10)).trans (Steps.single hs11)).trans (Steps.single hs12)
  refine ⟨⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, hsteps,
    fun R => σ12.regs.get? R, ?_⟩
  -- PreW at p = n/8
  refine ⟨hG12, by rw [hmem12eq]; exact hloaded, hpc12, ha0_12, ha1_12, ha2_12, ha3_12, ha4_12,
    ha5_12, ha7_12, hra_12, ⟨_, hmi12'⟩, hi12, hreg, hda, ?_, hppos, h8p, ?_, fun R _ => rfl⟩
  · -- src%8 = 0 from aligned xor and dst%8 = 0
    exact src_align_of_xor src.toNat dst.toNat halign_xor hda
  · -- MemInv … 0
    rw [hmem12eq]; exact hminv

/-! ## Task c — the unified `memcpy` spec (`memcpy_spec`)

The single total-correctness triple from the function entry `0x80006bc8`.

### Precondition `P` — the exact constraints

`P` (via `PreDispatch g`) fixes: `GoodState`, `MemcpyLoaded`, `PC = 0x80006bc8`,
`a0 = dst`, `a1 = src`, `a2 = n`, `x1 = r`, `minstret` defined, `tick < 2`,
`Regions dst src n` (region well-formedness / no-wrap / disjointness / RAM+HTIF
bounds), `0 < n`, `MemInv dst src n bs 0 m0 mem` (source bytes `bs` readable, dest
untouched), and the ghost frame `hframe`.  On top of `PreDispatch`, `memcpy_spec`
requires `r.toNat % 4 = 0` (return address 4-aligned, for the `ret`) and the
**route/size/alignment disjunction**

```
    (src.toNat ^^^ dst.toNat) % 8 ≠ 0                                  -- (A) misaligned → byte path
  ∨ n < 8                                                              -- (B) small → byte path
  ∨ (dst.toNat % 8 = 0 ∧ 8 * (n / 8) ≤ 64)                            -- (C) aligned word path
```

The `8 * (n / 8) ≤ 64` bound is the EXACT threshold derived from the `bf8`
`blt a5,a3` guard (`a5 = 64`, `a3 = 8*(n/8)`): the small word loop is entered iff
the rounded word-byte count fits in 64.  For interpreter call sites this covers
`Value` copies (24 B) and small strings; larger aligned copies take the `c60`
×8-unrolled path (documented follow-up).  Disjunct (C)'s `dst % 8 = 0` excludes
the `be8` head-align peel (`0x80006cbc`): the peel fires only when aligned-xor but
`dst % 8 ≠ 0`, which (C) rules out (cases (A)/(B) never reach `be8`).

### Postcondition `Q` — `memcpy_bytepath_post`

`Q c := ∃ g', memcpy_bytepath_post g' r dst n m0 bs c`, i.e. `GoodState`,
`PC = r`, `x10 = dst` (memcpy returns dst), `x1 = r`, `∀ k < n, mem[dst+k] = bs k`
(the described copy), `∀ a ∉ [dst,dst+n), mem[a] = m0[a]` (outside unchanged),
`tick < 2`, and a blanket ghost frame against the RETURN state's reads (a fresh
top-level `g'`).

### Ghost reconciliation

Each path instantiates its own fresh ghost at the crossover (`PreB`/`PreW` ghosts
are `fun R => σ.regs.get?` at the dispatch-successor state; the entry ghost `g`
does not survive the frame rewrites across `NotWrittenW`/`NotWrittenB`).  The
top-level `Q` frame is likewise packaged existentially (`∃ g'`), so the composed
spec exposes ONE fresh ghost — the return state's own reads — reconciling all the
per-path fresh ghosts into a single top-level frame witness. -/
theorem memcpy_spec (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign : r.toNat % 4 = 0)
    (hroute : (src.toNat ^^^ dst.toNat) % 8 ≠ 0 ∨ n < 8 ∨ (dst.toNat % 8 = 0 ∧ 8 * (n / 8) ≤ 64)) :
    Triple (PreDispatch g r dst src n m0 bs)
      (fun c => ∃ g', memcpy_bytepath_post g' r dst n m0 bs c) := by
  -- run the common prefix to bd4, then route
  refine (to_bd4 g r dst src n m0 bs).seq ?_
  rcases hroute with hmis | hsmall | ⟨hda, hfit⟩
  · -- (A) misaligned → byte path
    refine (dispatch_misaligned_to_byte r dst src n m0 bs hmis).seq ?_
    refine Triple.exists_pre (fun g' => ?_)
    exact memcpy_bytepath_spec g' r dst src n m0 bs halign |>.conseq (fun _ h => h)
      (fun c h => ⟨g', h⟩)
  · -- (B) small aligned → byte path.  Determine the alignment-xor from a case split.
    by_cases halx : (src.toNat ^^^ dst.toNat) % 8 = 0
    · refine (dispatch_small_to_byte r dst src n m0 bs halx hsmall).seq ?_
      refine Triple.exists_pre (fun g' => ?_)
      exact memcpy_bytepath_spec g' r dst src n m0 bs halign |>.conseq (fun _ h => h)
        (fun c h => ⟨g', h⟩)
    · -- misaligned after all
      refine (dispatch_misaligned_to_byte r dst src n m0 bs halx).seq ?_
      refine Triple.exists_pre (fun g' => ?_)
      exact memcpy_bytepath_spec g' r dst src n m0 bs halign |>.conseq (fun _ h => h)
        (fun c h => ⟨g', h⟩)
  · -- (C) aligned word path.  Sub-case on misaligned vs aligned-xor.
    by_cases halx : (src.toNat ^^^ dst.toNat) % 8 = 0
    · by_cases hbig : 8 ≤ n
      · -- word route
        refine (dispatch_to_word r dst src n m0 bs halx hbig hda hfit).seq ?_
        refine Triple.exists_pre (fun g' => ?_)
        -- word loop to StWDone, then tail or notail
        refine (word_loop_spec g' (n / 8) r dst src n m0 bs).seq ?_
        by_cases hdvd : 8 * (n / 8) = n
        · exact epilogue_notail_spec g' (n / 8) r dst src n m0 bs (by omega) hdvd halign
        · exact epilogue_tail_spec g' (n / 8) r dst src n m0 bs (by omega) (by omega) halign
      · -- n < 8 but landed in (C): route via small byte path
        refine (dispatch_small_to_byte r dst src n m0 bs halx (by omega)).seq ?_
        refine Triple.exists_pre (fun g' => ?_)
        exact memcpy_bytepath_spec g' r dst src n m0 bs halign |>.conseq (fun _ h => h)
          (fun c h => ⟨g', h⟩)
    · -- misaligned
      refine (dispatch_misaligned_to_byte r dst src n m0 bs halx).seq ?_
      refine Triple.exists_pre (fun g' => ?_)
      exact memcpy_bytepath_spec g' r dst src n m0 bs halign |>.conseq (fun _ h => h)
        (fun c h => ⟨g', h⟩)

end Vsa.Sim
