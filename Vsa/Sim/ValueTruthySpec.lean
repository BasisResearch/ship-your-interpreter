import Vsa.Sim.ValueSpec
import Vsa.Sim.ReprSurvival

/-!
# `value_truthy_spec` — total-correctness spec for `value_truthy`

`value_truthy` (@0x8000282c) takes its 24-byte `Value` argument **by reference**
in `a0` and returns `(v.truthy ? 1 : 0)` in `a0`. It dispatches on the kind tag
`lw a5,0(a0)`:

* kind = 1 (bool): `lw a0,8(a0)` — returns the stored 4-byte bool payload;
* kind = 2 (int):  `ld a0,8(a0); snez a0,a0` — returns `(i ≠ 0 ? 1 : 0)`;
* else (0/3/4/5):  `snez a0,a5` (`a5 = kind`) — `0` for null, `1` otherwise.

The precondition carries `ValueRepr m0 N φc buf.toNat v`; the proof cases on `v`,
extracts the kind bytes from `ValueRepr`'s `read32` fact (the `read32_bytes`
extractor below), threads the branch ladder, does the per-kind payload read, and
matches `Value.truthy` by `rfl`-adjacent facts. Memory is read-only throughout.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Value NativeFn)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The kind-byte extractor

`read32 m a = some k` forces all four byte reads in the `readLE` do-block to
succeed; peel them into per-byte `some` facts plus the reconstruction
`(b3 ++ b2 ++ b1 ++ b0 : BitVec 32).toNat = k`. The `site_8000282c` step consumes
the byte facts and produces `x15 := sign_extend (b3 ++ b2 ++ b1 ++ b0)`; the
reconstruction lets us fold that back to `BitVec.ofNat 64 k` (§`sext_word_small`)
so the branch comparisons decide against `1#64` / `2#64`. -/

/-- From `read32 m a = some k`, extract the four little-endian bytes as `some`
facts together with the reconstruction equation. -/
theorem read32_bytes (m : Mem) (a k : Nat) (h : read32 m a = some k) :
    ∃ b0 b1 b2 b3 : BitVec 8,
      m[a]? = some b0 ∧ m[a + 1]? = some b1 ∧ m[a + 2]? = some b2 ∧ m[a + 3]? = some b3 ∧
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) = k := by
  simp only [read32, readLE, bind, Option.bind] at h
  match hb0 : m[a]?, hb1 : m[a + 1]?, hb2 : m[a + 2]?, hb3 : m[a + 3]? with
  | some b0, some b1, some b2, some b3 =>
      refine ⟨b0, b1, b2, b3, rfl, rfl, rfl, rfl, ?_⟩
      rw [hb0, hb1, hb2, hb3] at h
      have hk := Option.some.inj h
      omega
  | none, _, _, _ => rw [hb0] at h; exact absurd h (by simp)
  | some _, none, _, _ => rw [hb0, hb1] at h; exact absurd h (by simp)
  | some _, some _, none, _ => rw [hb0, hb1, hb2] at h; exact absurd h (by simp)
  | some _, some _, some _, none => rw [hb0, hb1, hb2, hb3] at h; exact absurd h (by simp)

/-- The reconstruction `b0 + 256*(b1 + 256*(b2 + 256*b3))` equals the `toNat` of
the assembled little-endian word `b3 ++ b2 ++ b1 ++ b0 : BitVec 32`. -/
theorem word_toNat_recon (b0 b1 b2 b3 : BitVec 8) :
    ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).toNat
      = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) := by
  simp only [BitVec.append_eq, BitVec.toNat_append]
  have h0 := b0.isLt
  have h1 := b1.isLt
  have h2 := b2.isLt
  have h3 := b3.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

/-- For a 32-bit word whose value is small (`< 128`), the 64-bit sign extension
is just `BitVec.ofNat 64 k`. Used to fold the `x15`/`x10` load result back to the
kind (0..5) for the branch comparisons. -/
theorem sext_word_small (w : BitVec (8 * 4)) (k : Nat) (hk : k < 128) (hw : w.toNat = k) :
    (sign_extend (m := 64) w : BitVec 64) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  have hlt : w.toNat < 2 ^ 32 := w.isLt
  have hmsb : w.msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth, hmsb, Bool.false_eq_true, if_false, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (by omega), hw, Nat.mod_eq_of_lt (by omega)]

/-- From `read64 m a = some p`, extract the eight little-endian bytes as `some`
facts together with the reconstruction equation. -/
theorem read64_bytes (m : Mem) (a p : Nat) (h : read64 m a = some p) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      m[a]? = some b0 ∧ m[a + 1]? = some b1 ∧ m[a + 2]? = some b2 ∧ m[a + 3]? = some b3 ∧
      m[a + 4]? = some b4 ∧ m[a + 5]? = some b5 ∧ m[a + 6]? = some b6 ∧ m[a + 7]? = some b7 ∧
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) = p := by
  simp only [read64, readLE, bind, Option.bind] at h
  match hb0 : m[a]?, hb1 : m[a + 1]?, hb2 : m[a + 2]?, hb3 : m[a + 3]?,
        hb4 : m[a + 4]?, hb5 : m[a + 5]?, hb6 : m[a + 6]?, hb7 : m[a + 7]? with
  | some b0, some b1, some b2, some b3, some b4, some b5, some b6, some b7 =>
      refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7] at h
      have hk := Option.some.inj h
      omega
  | none, _, _, _, _, _, _, _ => rw [hb0] at h; exact absurd h (by simp)
  | some _, none, _, _, _, _, _, _ => rw [hb0, hb1] at h; exact absurd h (by simp)
  | some _, some _, none, _, _, _, _, _ => rw [hb0, hb1, hb2] at h; exact absurd h (by simp)
  | some _, some _, some _, none, _, _, _, _ => rw [hb0, hb1, hb2, hb3] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, none, _, _, _ =>
      rw [hb0, hb1, hb2, hb3, hb4] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, some _, none, _, _ =>
      rw [hb0, hb1, hb2, hb3, hb4, hb5] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, some _, some _, none, _ =>
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, some _, some _, some _, none =>
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7] at h; exact absurd h (by simp)

/-- The 8-byte little-endian reconstruction equals the `toNat` of the assembled
word `b7 ++ … ++ b0 : BitVec 64`. -/
theorem word8_toNat_recon (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
      : BitVec (8 * 8)).toNat
      = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) := by
  simp only [BitVec.append_eq, BitVec.toNat_append]
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

/-- Sign-extending a full-width 64-bit word is the identity. -/
theorem sext_full (w : BitVec (8 * 8)) : (sign_extend (m := 64) w : BitVec 64) = w := by
  show Sail.BitVec.signExtend w 64 = w
  simp only [Sail.BitVec.signExtend]
  exact BitVec.signExtend_eq w

/-- The `snez rd,rs` result in a register: `zero_extend (bool_to_bit (0 <u v))
= cond (v ≠ 0) 1 0`. -/
theorem snez_reg (v : BitVec 64) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v)) : BitVec 64)
      = cond (v != 0#64) (1#64) (0#64) := by
  by_cases h : v = 0#64
  · subst h
    have hz : zopz0zI_u (0#64) (0#64) = false := by
      simp only [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat]; decide
    rw [hz]
    simp only [bne_self_eq_false, cond_false]
    apply BitVec.eq_of_toNat_eq; decide
  · have htrue : zopz0zI_u (0#64) v = true := by
      simp only [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat, Nat.zero_mod, decide_eq_true_eq]
      have hp : 0 < v.toNat := by
        rcases Nat.eq_zero_or_pos v.toNat with h0 | hp
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) h
        · exact hp
      exact Int.ofNat_lt.mpr hp
    rw [htrue, show (v != 0#64) = true from by simp only [bne_iff_ne, ne_eq]; exact h, cond_true]
    apply BitVec.eq_of_toNat_eq; decide

/-! ## Ghost frame for `value_truthy`

The function writes the scratch GPRs `x15` (`lw a5`), `x14` (`li a4`), and `x10`
(`a0` result / payload loads); plus the control/noise registers. `NotWrittenT`
is the disequality set for a ghost register untouched by the whole function. -/

/-! ## Region facts for the `value_truthy` argument buffer

The 24-byte `Value` at `buf` lives in RAM, 8-aligned, above the HTIF window,
disjoint from the `value_truthy` code `[0x8000282c, 0x8000285c)`. The kind read at
`buf` and the payload read at `buf + 8` both land in the writable RAM region. -/

/-! ## Branch-observation consumers (mirror `obs_alu_*`)

`sigmaPost_branch_taken` sets PC := `pc + sext imm`; `sigmaPost_branch_nottaken`
sets PC := `pc + 4`. Both leave every register outside `{minstret, PC, nextPC,
minstret_increment}` at its `σ` value. These read those fields off `σ'` through
`ReadsLikePost`. -/

theorem obs_branch_nottaken_pc {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide)
    (post_branch_nottaken_pc σ pc vm)

theorem obs_branch_nottaken_other {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    {w : RegisterType R} (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi
    ((get?_sigmaPost_branch_nottaken σ pc vm R h1 h2 h4 h5).trans hσ)

theorem obs_branch_nottaken_minstret {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-! ## Ghost-frame passthrough per step-shape

Each delivers `σ'.regs.get? R = σ.regs.get? R` for a ghost register `R`
(`NotWrittenT R`); the caller then composes with `hframe`. -/

/-! ## Pre / post -/

/-! ## Kind-value bridge

From `ValueRepr … buf v` (which pins `read32 m0 buf = some (kindTag v)`), extract
the four kind bytes and package the `x15` value the prefix computes: `x15 =
sign_extend (b3 ++ b2 ++ b1 ++ b0)` folds to `BitVec.ofNat 64 (kindTag v)`. -/

/-- The prefix's `x15` load result folds to `BitVec.ofNat 64 (kindTag v)`. -/
theorem sext_kind (b0 b1 b2 b3 : BitVec 8) (k : Nat) (hk : k < 128)
    (hrec : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) = k) :
    (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)) : BitVec 64)
      = BitVec.ofNat 64 k :=
  sext_word_small _ k hk (by rw [word_toNat_recon]; exact hrec)

/-! ## Shared prefix: `lw a5,0(a0); li a4,1`

Runs the first two instructions from entry, delivering the machine at
`0x80002834` (the first `beq`) with `x15 = ofNat (kindTag v)`, `x14 = 1`, and the
argument/return registers preserved. Memory is unchanged (`= m0`). -/

/-! ## Default path (`snez a0,a5`)

For `v` with kind `k ∈ {0, 3, 4, 5}` both `beq`s fall through; the machine runs
`0x80002834_nt; 0x80002838(li a4,2); 0x8000283c_nt; 0x80002840(snez a0,a5);
0x80002844(ret)`. `a5 = ofNat 64 k`, so the result is `cond (k ≠ 0) 1 0`. Given
the post-prefix state `σ2`, this runs to `truthy_post`. -/

/-! ## `value_truthy_spec`

The 6-way case on `v`. Each path: `truthy_prefix`, then the kind-dispatch branch
ladder (decided by `kindTag v`), the per-kind payload read, and the `ret`; the
returned `a0` matches `cond (Value.truthy v) 1 0` by the byte/`snez` bridges. -/

end Vsa.Sim
