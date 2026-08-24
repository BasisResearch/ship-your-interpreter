import Vsa.Sim.ValueSpec

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

/-- The int-payload non-zero test agrees with the spec: for `p` with
`(BitVec.ofNat 64 p).toInt = n`, the register test `(BitVec.ofNat 64 p ≠ 0)`
equals `(n ≠ 0)`. -/
theorem int_nonzero_bridge (p : Nat) (n : Int) (hp : (BitVec.ofNat 64 p).toInt = n) :
    (BitVec.ofNat 64 p != 0#64) = (n != 0) := by
  have hz : (BitVec.ofNat 64 p = 0#64) ↔ (n = 0) := by
    constructor
    · intro h; rw [← hp, h]; decide
    · intro h
      apply BitVec.toInt_inj.mp
      rw [hp, h]; decide
  by_cases h : BitVec.ofNat 64 p = 0#64
  · rw [show (BitVec.ofNat 64 p != 0#64) = false from by simpa using h,
        show (n != 0) = false from by simp only [bne_eq_false_iff_eq]; exact hz.mp h]
  · rw [show (BitVec.ofNat 64 p != 0#64) = true from by simpa using h,
        show (n != 0) = true from by simp only [bne_iff_ne, ne_eq]; exact fun hn => h (hz.mpr hn)]

/-! ## Ghost frame for `value_truthy`

The function writes the scratch GPRs `x15` (`lw a5`), `x14` (`li a4`), and `x10`
(`a0` result / payload loads); plus the control/noise registers. `NotWrittenT`
is the disequality set for a ghost register untouched by the whole function. -/

abbrev NotWrittenT (R : Register) : Prop :=
  (Register.x10 == R) = false ∧ (Register.x14 == R) = false ∧ (Register.x15 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

/-! ## Region facts for the `value_truthy` argument buffer

The 24-byte `Value` at `buf` lives in RAM, 8-aligned, above the HTIF window,
disjoint from the `value_truthy` code `[0x8000282c, 0x8000285c)`. The kind read at
`buf` and the payload read at `buf + 8` both land in the writable RAM region. -/
structure TruthyRegion (buf : BitVec 64) : Prop where
  align : buf.toNat % 8 = 0
  lo : 0x80000000 ≤ buf.toNat
  hi : buf.toNat + 24 ≤ 0x100000000
  win : tohostAddr + 16 ≤ buf.toNat

theorem truthy_kind_addr (buf : BitVec 64) :
    (buf + sign_extend (m := 64) (0x000#12)).toNat = buf.toNat := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
    apply BitVec.eq_of_toNat_eq; decide]
  rw [BitVec.add_zero]

theorem truthy_pay_addr (buf : BitVec 64) (hr : TruthyRegion buf) :
    (buf + sign_extend (m := 64) (0x008#12)).toNat = buf.toNat + 8 := by
  have hsext : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hsext, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := hr.hi
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## Branch-observation consumers (mirror `obs_alu_*`)

`sigmaPost_branch_taken` sets PC := `pc + sext imm`; `sigmaPost_branch_nottaken`
sets PC := `pc + 4`. Both leave every register outside `{minstret, PC, nextPC,
minstret_increment}` at its `σ` value. These read those fields off `σ'` through
`ReadsLikePost`. -/

theorem obs_branch_taken_pc {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) :
    σ'.regs.get? Register.PC = some (pc + sign_extend (m := 64) imm) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide)
    (post_branch_taken_pc σ pc vm imm)

theorem obs_branch_nottaken_pc {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide)
    (post_branch_nottaken_pc σ pc vm)

theorem obs_branch_taken_other {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    {w : RegisterType R} (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi
    ((get?_sigmaPost_branch_taken σ pc vm imm R h1 h2 h4 h5).trans hσ)

theorem obs_branch_nottaken_other {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    {w : RegisterType R} (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi
    ((get?_sigmaPost_branch_nottaken σ pc vm R h1 h2 h4 h5).trans hσ)

theorem obs_branch_taken_minstret {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

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

theorem frame_alu_t {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hR : NotWrittenT R) (hrd : (rd == R) = false) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

theorem frame_branch_taken_t {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    (hR : NotWrittenT R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_taken σ pc vm imm R hmi hpc hnpc hmii

theorem frame_branch_nottaken_t {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWrittenT R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hmi hpc hnpc hmii

theorem frame_jr_t {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenT R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

/-! ## Pre / post -/

def truthy_pre (g : (R : Register) → Option (RegisterType R)) (buf r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ Value_truthyLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x8000282c#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
  ValueRepr m0 N φc buf.toNat v ∧ TruthyRegion buf ∧
  (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
  (∀ R : Register, NotWrittenT R → c.σ.regs.get? R = g R)

def truthy_post (g : (R : Register) → Option (RegisterType R)) (r : BitVec 64) (v : Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
  c.σ.regs.get? Register.x10 = some (cond (Value.truthy v) (1#64) (0#64)) ∧
  c.σ.regs.get? Register.x1 = some r ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
  c.σ.mem = m0 ∧
  (∀ R : Register, NotWrittenT R → c.σ.regs.get? R = g R)

/-! ## Kind-value bridge

From `ValueRepr … buf v` (which pins `read32 m0 buf = some (kindTag v)`), extract
the four kind bytes and package the `x15` value the prefix computes: `x15 =
sign_extend (b3 ++ b2 ++ b1 ++ b0)` folds to `BitVec.ofNat 64 (kindTag v)`. -/

theorem kind_read32 (m : Mem) (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (a : Nat) (v : Value)
    (h : ValueRepr m N φc a v) : read32 m a = some (kindTag v) := by
  cases v <;> simp only [ValueRepr, kindTag] at h ⊢ <;>
    first
      | exact h
      | exact h.1

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
theorem truthy_prefix (g : (R : Register) → Option (RegisterType R)) (buf r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config)
    (hG : GoodState c.σ) (hloaded : Value_truthyLoaded c.σ.mem) (hmem : c.σ.mem = m0)
    (hpc : c.σ.regs.get? Register.PC = some (0x8000282c#64 : BitVec 64))
    (ha0 : c.σ.regs.get? Register.x10 = some buf) (hra : c.σ.regs.get? Register.x1 = some r)
    (vmi : BitVec 64) (hmi : c.σ.regs.get? Register.minstret = some vmi)
    (htick : c.tick < 2) (hrepr : ValueRepr m0 N φc buf.toNat v) (hreg : TruthyRegion buf)
    (hframe : ∀ R : Register, NotWrittenT R → c.σ.regs.get? R = g R) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps c ⟨σ2, i2, c.steps + 1 + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧ σ2.mem = m0 ∧
      σ2.regs.get? Register.PC = some (0x80002834#64 : BitVec 64) ∧
      σ2.regs.get? Register.x15 = some (BitVec.ofNat 64 (kindTag v)) ∧
      σ2.regs.get? Register.x14 = some (1#64) ∧
      σ2.regs.get? Register.x10 = some buf ∧ σ2.regs.get? Register.x1 = some r ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, NotWrittenT R → σ2.regs.get? R = g R) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hkind : read32 m0 buf.toNat = some (kindTag v) := kind_read32 m0 N φc buf.toNat v hrepr
  obtain ⟨b0, b1, b2, b3, hbb0, hbb1, hbb2, hbb3, hrec⟩ := read32_bytes m0 buf.toNat _ hkind
  have hktlt : kindTag v < 128 := by cases v <;> simp [kindTag]
  have hkalign : buf.toNat % 4 = 0 := by have := hreg.align; omega
  -- === 0x8000282c: lw a5,0(a0) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_8000282c c.σ c.tick c.steps (0x8000282c#64) vmi buf b0 b1 b2 b3 hG hpc hmi ha0 hloaded rfl
      (by rw [truthy_kind_addr]; exact hreg.lo) (by rw [truthy_kind_addr]; have := hreg.hi; omega)
      (by rw [truthy_kind_addr]; right; rw [htoh]; have := hreg.win; rw [htoh] at this; omega)
      (by rw [truthy_kind_addr]; exact hkalign)
      (by rw [truthy_kind_addr, hmem]; exact hbb0) (by rw [truthy_kind_addr, hmem]; exact hbb1)
      (by rw [truthy_kind_addr, hmem]; exact hbb2) (by rw [truthy_kind_addr, hmem]; exact hbb3)
      htick
  have hmem1eq : σ1.mem = m0 := by rw [hmem1, hmem]
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002830#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000282c#64) 4 = (0x80002830#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha5_1 : σ1.regs.get? Register.x15
      = some (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have ha5_1' : σ1.regs.get? Register.x15 = some (BitVec.ofNat 64 (kindTag v)) := by
    rw [ha5_1, sext_kind b0 b1 b2 b3 (kindTag v) hktlt hrec]
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hframe1 : ∀ R : Register, NotWrittenT R → σ1.regs.get? R = g R := fun R hR =>
    (frame_alu_t hobs1 R hR hR.2.2.1).trans (hframe R hR)
  -- === 0x80002830: li a4,1 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002830 σ1 i1 (c.steps + 1) (0x80002830#64) vmi1 hG1 hpc1 hmi1
      (by rw [hmem1eq]; exact hmem ▸ hloaded) rfl hi1
  have hmem2eq : σ2.mem = m0 := by rw [hmem2, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002834#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80002830#64) 4 = (0x80002834#64 : BitVec 64) from by decide] at this
  have ha14_2 : σ2.regs.get? Register.x14 = some (1#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have ha5_2 := obs_alu_other hobs2 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_1'
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hframe2 : ∀ R : Register, NotWrittenT R → σ2.regs.get? R = g R := fun R hR =>
    (frame_alu_t hobs2 R hR hR.2.1).trans (hframe1 R hR)
  exact ⟨σ2, i2, (Steps.single hs1).trans (Steps.single hs2), hi2, hG2, hmem2eq, hpc2,
    ha5_2, ha14_2, ha0_2, hra_2, ⟨vmi2, hmi2⟩, hframe2⟩

/-! ## Default path (`snez a0,a5`)

For `v` with kind `k ∈ {0, 3, 4, 5}` both `beq`s fall through; the machine runs
`0x80002834_nt; 0x80002838(li a4,2); 0x8000283c_nt; 0x80002840(snez a0,a5);
0x80002844(ret)`. `a5 = ofNat 64 k`, so the result is `cond (k ≠ 0) 1 0`. Given
the post-prefix state `σ2`, this runs to `truthy_post`. -/
theorem truthy_default_path (g : (R : Register) → Option (RegisterType R)) (buf r : BitVec 64)
    (v : Value) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config)
    (σ2 : MState) (i2 : Nat)
    (hloaded0 : Value_truthyLoaded m0) (hrettgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hsteps2 : Steps c ⟨σ2, i2, c.steps + 1 + 1⟩) (hi2 : i2 < 2) (hG2 : GoodState σ2)
    (hmem2 : σ2.mem = m0) (hpc2 : σ2.regs.get? Register.PC = some (0x80002834#64 : BitVec 64))
    (ha15_2 : σ2.regs.get? Register.x15 = some (BitVec.ofNat 64 (kindTag v)))
    (ha14_2 : σ2.regs.get? Register.x14 = some (1#64))
    (ha0_2 : σ2.regs.get? Register.x10 = some buf) (hra_2 : σ2.regs.get? Register.x1 = some r)
    (vmi2 : BitVec 64) (hmi2 : σ2.regs.get? Register.minstret = some vmi2)
    (hframe2 : ∀ R : Register, NotWrittenT R → σ2.regs.get? R = g R)
    (hk1 : (kindTag v) ≠ 1) (hk2 : (kindTag v) ≠ 2)
    (hres : cond (BitVec.ofNat 64 (kindTag v) != 0#64) (1#64) (0#64)
      = cond (Value.truthy v) (1#64) (0#64)) :
    ∃ c' : Config, Steps c c' ∧ truthy_post g r v m0 c' := by
  have hktlt : kindTag v < 128 := by cases v <;> simp [kindTag]
  have hne1 : ((BitVec.ofNat 64 (kindTag v)) == (1#64 : BitVec 64)) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h; apply hk1
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show kindTag v < 2^64 by omega)] using this
  have hne2 : ((BitVec.ofNat 64 (kindTag v)) == (2#64 : BitVec 64)) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h; apply hk2
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show kindTag v < 2^64 by omega)] using this
  -- === 0x80002834: beq (nottaken) ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002834_nottaken σ2 i2 (c.steps + 1 + 1) (0x80002834#64) vmi2
      (BitVec.ofNat 64 (kindTag v)) (1#64) hG2 hpc2 hmi2 ha15_2 ha14_2 (hmem2 ▸ hloaded0) rfl hne1 hi2
  have hmem3eq : σ3.mem = m0 := by rw [hmem3, hmem2]
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002838#64 : BitVec 64) := by
    have := obs_branch_nottaken_pc hobs3
    rwa [show BitVec.addInt (0x80002834#64) 4 = (0x80002838#64 : BitVec 64) from by decide] at this
  have ha15_3 := obs_branch_nottaken_other hobs3 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha15_2
  have ha0_3 := obs_branch_nottaken_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have hra_3 := obs_branch_nottaken_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  obtain ⟨vmi3, hmi3⟩ := obs_branch_nottaken_minstret hobs3
  have hframe3 : ∀ R : Register, NotWrittenT R → σ3.regs.get? R = g R := fun R hR =>
    (frame_branch_nottaken_t hobs3 R hR).trans (hframe2 R hR)
  -- === 0x80002838: li a4,2 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002838 σ3 i3 (c.steps + 1 + 1 + 1) (0x80002838#64) vmi3 hG3 hpc3 hmi3 (hmem3eq ▸ hloaded0) rfl hi3
  have hmem4eq : σ4.mem = m0 := by rw [hmem4, hmem3eq]
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000283c#64 : BitVec 64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80002838#64) 4 = (0x8000283c#64 : BitVec 64) from by decide] at this
  have ha14_4 : σ4.regs.get? Register.x14 = some (2#64) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x002#12) : BitVec 64) = 2#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have ha15_4 := obs_alu_other hobs4 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha15_3
  have ha0_4 := obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hframe4 : ∀ R : Register, NotWrittenT R → σ4.regs.get? R = g R := fun R hR =>
    (frame_alu_t hobs4 R hR hR.2.1).trans (hframe3 R hR)
  -- === 0x8000283c: beq (nottaken) ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_8000283c_nottaken σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000283c#64) vmi4
      (BitVec.ofNat 64 (kindTag v)) (2#64) hG4 hpc4 hmi4 ha15_4 ha14_4 (hmem4eq ▸ hloaded0) rfl hne2 hi4
  have hmem5eq : σ5.mem = m0 := by rw [hmem5, hmem4eq]
  have hpc5 : σ5.regs.get? Register.PC = some (0x80002840#64 : BitVec 64) := by
    have := obs_branch_nottaken_pc hobs5
    rwa [show BitVec.addInt (0x8000283c#64) 4 = (0x80002840#64 : BitVec 64) from by decide] at this
  have ha15_5 := obs_branch_nottaken_other hobs5 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha15_4
  have hra_5 := obs_branch_nottaken_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
  obtain ⟨vmi5, hmi5⟩ := obs_branch_nottaken_minstret hobs5
  have hframe5 : ∀ R : Register, NotWrittenT R → σ5.regs.get? R = g R := fun R hR =>
    (frame_branch_nottaken_t hobs5 R hR).trans (hframe4 R hR)
  -- === 0x80002840: snez a0,a5 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80002840 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80002840#64) vmi5
      (BitVec.ofNat 64 (kindTag v)) hG5 hpc5 hmi5 ha15_5 (hmem5eq ▸ hloaded0) rfl hi5
  have hmem6eq : σ6.mem = m0 := by rw [hmem6, hmem5eq]
  have hpc6 : σ6.regs.get? Register.PC = some (0x80002844#64 : BitVec 64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80002840#64) 4 = (0x80002844#64 : BitVec 64) from by decide] at this
  have ha0_6 : σ6.regs.get? Register.x10 = some (cond (Value.truthy v) (1#64) (0#64)) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, snez_reg]; exact congrArg some hres
  have hra_6 := obs_alu_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hframe6 : ∀ R : Register, NotWrittenT R → σ6.regs.get? R = g R := fun R hR =>
    (frame_alu_t hobs6 R hR hR.1).trans (hframe5 R hR)
  -- === 0x80002844: ret ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80002844 σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80002844#64) vmi6 r hG6 hpc6 hmi6 hra_6
      (hmem6eq ▸ hloaded0) rfl hrettgt hi6
  have hsteps : Steps c ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ :=
    (((((hsteps2.trans (Steps.single hs3)).trans (Steps.single hs4)).trans (Steps.single hs5)).trans
      (Steps.single hs6)).trans (Steps.single hs7))
  exact ⟨_, hsteps, hG7, obs_jr_pc hobs7,
    obs_jr_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_6,
    obs_jr_other hobs7 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_6,
    obs_jr_minstret hobs7, hi7, by rw [hmem7, hmem6eq],
    fun R hR => (frame_jr_t hobs7 R hR).trans (hframe6 R hR)⟩

/-! ## `value_truthy_spec`

The 6-way case on `v`. Each path: `truthy_prefix`, then the kind-dispatch branch
ladder (decided by `kindTag v`), the per-kind payload read, and the `ret`; the
returned `a0` matches `cond (Value.truthy v) 1 0` by the byte/`snez` bridges. -/
theorem value_truthy_spec (g : (R : Register) → Option (RegisterType R)) (buf r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (truthy_pre g buf r N φc v m0) (truthy_post g r v m0) := by
  intro c hpre
  obtain ⟨hG, hloaded, hmem, hpc, ha0, hra, ⟨vmi, hmi⟩, htick, hrepr, hreg, hrettgt, hframe⟩ := hpre
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hloaded0 : Value_truthyLoaded m0 := hmem ▸ hloaded
  obtain ⟨σ2, i2, hsteps2, hi2, hG2, hmem2, hpc2, ha15_2, ha14_2, ha0_2, hra_2, ⟨vmi2, hmi2⟩, hframe2⟩ :=
    truthy_prefix g buf r N φc v m0 c hG hloaded hmem hpc ha0 hra vmi hmi htick hrepr hreg hframe
  have hpay_addr : (buf + sign_extend (m := 64) (0x008#12)).toNat = buf.toNat + 8 :=
    truthy_pay_addr buf hreg
  cases v with
  | bool b =>
    -- kind = 1: beq taken → 0x80002854 (lw a0,8(a0)); ret
    obtain ⟨htagr, hpayr⟩ := hrepr
    -- byte facts for the bool payload read
    obtain ⟨p0, p1, p2, p3, hp0, hp1, hp2, hp3, hprec⟩ := read32_bytes m0 (buf.toNat + 8) _ hpayr
    -- === 0x80002834: beq a5,a4 (taken, kind 1 = 1) ===
    have hveq : ((BitVec.ofNat 64 (kindTag (Value.bool b))) == (1#64 : BitVec 64)) = true := by
      simp only [kindTag]; decide
    obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
      site_80002834_taken σ2 i2 (c.steps + 1 + 1) (0x80002834#64) vmi2
        (BitVec.ofNat 64 (kindTag (Value.bool b))) (1#64) hG2 hpc2 hmi2 ha15_2 ha14_2
        (hmem2 ▸ hloaded0) rfl
        (by rw [show ((0x80002834#64 : BitVec 64) + sign_extend (m := 64) (0x0020#13))
              = 0x80002854#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide)
        hveq hi2
    have hmem3eq : σ3.mem = m0 := by rw [hmem3, hmem2]
    have hpc3 : σ3.regs.get? Register.PC = some (0x80002854#64 : BitVec 64) := by
      have := obs_branch_taken_pc hobs3
      rwa [show ((0x80002834#64 : BitVec 64) + sign_extend (m := 64) (0x0020#13))
        = 0x80002854#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
    have ha0_3 := obs_branch_taken_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
    have hra_3 := obs_branch_taken_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
    obtain ⟨vmi3, hmi3⟩ := obs_branch_taken_minstret hobs3
    have hframe3 : ∀ R : Register, NotWrittenT R → σ3.regs.get? R = g R := fun R hR =>
      (frame_branch_taken_t hobs3 R hR).trans (hframe2 R hR)
    -- === 0x80002854: lw a0,8(a0) ===
    obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
      site_80002854 σ3 i3 (c.steps + 1 + 1 + 1) (0x80002854#64) vmi3 buf p0 p1 p2 p3
        hG3 hpc3 hmi3 ha0_3 (hmem3eq ▸ hloaded0) rfl
        (by rw [hpay_addr]; have := hreg.lo; omega) (by rw [hpay_addr]; have := hreg.hi; omega)
        (by rw [hpay_addr]; right; rw [htoh]; have := hreg.win; rw [htoh] at this; omega)
        (by rw [hpay_addr]; have := hreg.align; omega)
        (by rw [hpay_addr, hmem3eq]; exact hp0) (by rw [hpay_addr, hmem3eq]; exact hp1)
        (by rw [hpay_addr, hmem3eq]; exact hp2) (by rw [hpay_addr, hmem3eq]; exact hp3) hi3
    have hmem4eq : σ4.mem = m0 := by rw [hmem4, hmem3eq]
    have hpc4 : σ4.regs.get? Register.PC = some (0x80002858#64 : BitVec 64) := by
      have := obs_alu_pc hobs4
      rwa [show BitVec.addInt (0x80002854#64) 4 = (0x80002858#64 : BitVec 64) from by decide] at this
    have ha0_4 : σ4.regs.get? Register.x10 = some (cond (Value.truthy (Value.bool b)) (1#64) (0#64)) := by
      have hr := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [hr, sext_word_small _ (cond b 1 0) (by cases b <;> decide)
        (by rw [word_toNat_recon]; exact hprec)]
      simp only [Value.truthy]; cases b <;> (apply congrArg; apply BitVec.eq_of_toNat_eq; decide)
    have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
    obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
    have hframe4 : ∀ R : Register, NotWrittenT R → σ4.regs.get? R = g R := fun R hR =>
      (frame_alu_t hobs4 R hR hR.1).trans (hframe3 R hR)
    -- === 0x80002858: ret ===
    obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
      site_80002858 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80002858#64) vmi4 r hG4 hpc4 hmi4 hra_4
        (hmem4eq ▸ hloaded0) rfl hrettgt hi4
    have hsteps : Steps c ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ :=
      (((hsteps2.trans (Steps.single hs3)).trans (Steps.single hs4)).trans (Steps.single hs5))
    refine ⟨⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩, hsteps, hG5, obs_jr_pc hobs5,
      obs_jr_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4,
      obs_jr_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4,
      obs_jr_minstret hobs5, hi5, by rw [hmem5, hmem4eq],
      fun R hR => (frame_jr_t hobs5 R hR).trans (hframe4 R hR)⟩
  | int n =>
    -- kind = 2: beq nt → 0x80002838(li a4,2) → beq taken → 0x80002848(ld a0,8(a0)); snez; ret
    obtain ⟨htagr, hpayr⟩ := hrepr
    -- readI64 gives read64 = some p with (ofNat p).toInt = n
    simp only [readI64, Option.map_eq_some_iff] at hpayr
    obtain ⟨p, hp64, hpn⟩ := hpayr
    obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hqrec⟩ :=
      read64_bytes m0 (buf.toNat + 8) _ hp64
    -- === 0x80002834: beq (nottaken, kind 2 ≠ 1) ===
    have hne1 : ((BitVec.ofNat 64 (kindTag (Value.int n))) == (1#64 : BitVec 64)) = false := by
      simp only [kindTag]; decide
    obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
      site_80002834_nottaken σ2 i2 (c.steps + 1 + 1) (0x80002834#64) vmi2
        (BitVec.ofNat 64 (kindTag (Value.int n))) (1#64) hG2 hpc2 hmi2 ha15_2 ha14_2
        (hmem2 ▸ hloaded0) rfl hne1 hi2
    have hmem3eq : σ3.mem = m0 := by rw [hmem3, hmem2]
    have hpc3 : σ3.regs.get? Register.PC = some (0x80002838#64 : BitVec 64) := by
      have := obs_branch_nottaken_pc hobs3
      rwa [show BitVec.addInt (0x80002834#64) 4 = (0x80002838#64 : BitVec 64) from by decide] at this
    have ha15_3 := obs_branch_nottaken_other hobs3 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha15_2
    have ha0_3 := obs_branch_nottaken_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
    have hra_3 := obs_branch_nottaken_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
    obtain ⟨vmi3, hmi3⟩ := obs_branch_nottaken_minstret hobs3
    have hframe3 : ∀ R : Register, NotWrittenT R → σ3.regs.get? R = g R := fun R hR =>
      (frame_branch_nottaken_t hobs3 R hR).trans (hframe2 R hR)
    -- === 0x80002838: li a4,2 ===
    obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
      site_80002838 σ3 i3 (c.steps + 1 + 1 + 1) (0x80002838#64) vmi3 hG3 hpc3 hmi3 (hmem3eq ▸ hloaded0) rfl hi3
    have hmem4eq : σ4.mem = m0 := by rw [hmem4, hmem3eq]
    have hpc4 : σ4.regs.get? Register.PC = some (0x8000283c#64 : BitVec 64) := by
      have := obs_alu_pc hobs4
      rwa [show BitVec.addInt (0x80002838#64) 4 = (0x8000283c#64 : BitVec 64) from by decide] at this
    have ha14_4 : σ4.regs.get? Register.x14 = some (2#64) := by
      have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [show ((0#64) + sign_extend (m := 64) (0x002#12) : BitVec 64) = 2#64 from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    have ha15_4 := obs_alu_other hobs4 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha15_3
    have ha0_4 := obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
    have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
    obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
    have hframe4 : ∀ R : Register, NotWrittenT R → σ4.regs.get? R = g R := fun R hR =>
      (frame_alu_t hobs4 R hR hR.2.1).trans (hframe3 R hR)
    -- === 0x8000283c: beq (taken, kind 2 = 2) → 0x80002848 ===
    have hveq : ((BitVec.ofNat 64 (kindTag (Value.int n))) == (2#64 : BitVec 64)) = true := by
      simp only [kindTag]; decide
    obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
      site_8000283c_taken σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000283c#64) vmi4
        (BitVec.ofNat 64 (kindTag (Value.int n))) (2#64) hG4 hpc4 hmi4 ha15_4 ha14_4
        (hmem4eq ▸ hloaded0) rfl
        (by rw [show ((0x8000283c#64 : BitVec 64) + sign_extend (m := 64) (0x000c#13))
              = 0x80002848#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide)
        hveq hi4
    have hmem5eq : σ5.mem = m0 := by rw [hmem5, hmem4eq]
    have hpc5 : σ5.regs.get? Register.PC = some (0x80002848#64 : BitVec 64) := by
      have := obs_branch_taken_pc hobs5
      rwa [show ((0x8000283c#64 : BitVec 64) + sign_extend (m := 64) (0x000c#13))
        = 0x80002848#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
    have ha0_5 := obs_branch_taken_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4
    have hra_5 := obs_branch_taken_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
    obtain ⟨vmi5, hmi5⟩ := obs_branch_taken_minstret hobs5
    have hframe5 : ∀ R : Register, NotWrittenT R → σ5.regs.get? R = g R := fun R hR =>
      (frame_branch_taken_t hobs5 R hR).trans (hframe4 R hR)
    -- === 0x80002848: ld a0,8(a0) ===
    obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
      site_80002848 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80002848#64) vmi5 buf
        q0 q1 q2 q3 q4 q5 q6 q7 hG5 hpc5 hmi5 ha0_5 (hmem5eq ▸ hloaded0) rfl
        (by rw [hpay_addr]; have := hreg.lo; omega) (by rw [hpay_addr]; have := hreg.hi; omega)
        (by rw [hpay_addr]; right; rw [htoh]; have := hreg.win; rw [htoh] at this; omega)
        (by rw [hpay_addr]; have := hreg.align; omega)
        (by rw [hpay_addr, hmem5eq]; exact hq0) (by rw [hpay_addr, hmem5eq]; exact hq1)
        (by rw [hpay_addr, hmem5eq]; exact hq2) (by rw [hpay_addr, hmem5eq]; exact hq3)
        (by rw [hpay_addr, hmem5eq]; exact hq4) (by rw [hpay_addr, hmem5eq]; exact hq5)
        (by rw [hpay_addr, hmem5eq]; exact hq6) (by rw [hpay_addr, hmem5eq]; exact hq7) hi5
    have hmem6eq : σ6.mem = m0 := by rw [hmem6, hmem5eq]
    have hpc6 : σ6.regs.get? Register.PC = some (0x8000284c#64 : BitVec 64) := by
      have := obs_alu_pc hobs6
      rwa [show BitVec.addInt (0x80002848#64) 4 = (0x8000284c#64 : BitVec 64) from by decide] at this
    have ha0_6 : σ6.regs.get? Register.x10 = some (BitVec.ofNat 64 p) := by
      have hr := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [hr, sext_full]
      apply congrArg
      apply BitVec.eq_of_toNat_eq
      rw [word8_toNat_recon, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      · omega
      · have hpp : p < 2 ^ 64 := by
          have := hq7.symm; omega
        omega
    have hra_6 := obs_alu_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_5
    obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
    have hframe6 : ∀ R : Register, NotWrittenT R → σ6.regs.get? R = g R := fun R hR =>
      (frame_alu_t hobs6 R hR hR.1).trans (hframe5 R hR)
    -- === 0x8000284c: snez a0,a0 ===
    obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
      site_8000284c σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x8000284c#64) vmi6
        (BitVec.ofNat 64 p) hG6 hpc6 hmi6 ha0_6 (hmem6eq ▸ hloaded0) rfl hi6
    have hmem7eq : σ7.mem = m0 := by rw [hmem7, hmem6eq]
    have hpc7 : σ7.regs.get? Register.PC = some (0x80002850#64 : BitVec 64) := by
      have := obs_alu_pc hobs7
      rwa [show BitVec.addInt (0x8000284c#64) 4 = (0x80002850#64 : BitVec 64) from by decide] at this
    have ha0_7 : σ7.regs.get? Register.x10 = some (cond (Value.truthy (Value.int n)) (1#64) (0#64)) := by
      have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [this, snez_reg]
      simp only [Value.truthy]
      rw [int_nonzero_bridge p n hpn]
    have hra_7 := obs_alu_other hobs7 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_6
    obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
    have hframe7 : ∀ R : Register, NotWrittenT R → σ7.regs.get? R = g R := fun R hR =>
      (frame_alu_t hobs7 R hR hR.1).trans (hframe6 R hR)
    -- === 0x80002850: ret ===
    obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
      site_80002850 σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002850#64) vmi7 r hG7 hpc7 hmi7 hra_7
        (hmem7eq ▸ hloaded0) rfl hrettgt hi7
    have hsteps : Steps c ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ :=
      ((((((hsteps2.trans (Steps.single hs3)).trans (Steps.single hs4)).trans (Steps.single hs5)).trans
        (Steps.single hs6)).trans (Steps.single hs7)).trans (Steps.single hs8))
    exact ⟨_, hsteps, hG8, obs_jr_pc hobs8,
      obs_jr_other hobs8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_7,
      obs_jr_other hobs8 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_7,
      obs_jr_minstret hobs8, hi8, by rw [hmem8, hmem7eq],
      fun R hR => (frame_jr_t hobs8 R hR).trans (hframe7 R hR)⟩
  | null =>
    exact truthy_default_path g buf r Value.null m0 c σ2 i2 hloaded0 hrettgt hsteps2 hi2 hG2 hmem2
      hpc2 ha15_2 ha14_2 ha0_2 hra_2 vmi2 hmi2 hframe2 (by decide) (by decide)
      (by simp only [kindTag, Value.truthy]; decide)
  | str s =>
    obtain ⟨htagr, _⟩ := hrepr
    exact truthy_default_path g buf r (Value.str s) m0 c σ2 i2 hloaded0 hrettgt hsteps2 hi2 hG2 hmem2
      hpc2 ha15_2 ha14_2 ha0_2 hra_2 vmi2 hmi2 hframe2 (by simp [kindTag]) (by simp [kindTag])
      (by simp only [kindTag, Value.truthy]; decide)
  | closure ca =>
    obtain ⟨htagr, _⟩ := hrepr
    exact truthy_default_path g buf r (Value.closure ca) m0 c σ2 i2 hloaded0 hrettgt hsteps2 hi2 hG2 hmem2
      hpc2 ha15_2 ha14_2 ha0_2 hra_2 vmi2 hmi2 hframe2 (by simp [kindTag]) (by simp [kindTag])
      (by simp only [kindTag, Value.truthy]; decide)
  | native f =>
    obtain ⟨htagr, _⟩ := hrepr
    exact truthy_default_path g buf r (Value.native f) m0 c σ2 i2 hloaded0 hrettgt hsteps2 hi2 hG2 hmem2
      hpc2 ha15_2 ha14_2 ha0_2 hra_2 vmi2 hmi2 hframe2 (by simp [kindTag]) (by simp [kindTag])
      (by simp only [kindTag, Value.truthy]; decide)

end Vsa.Sim
