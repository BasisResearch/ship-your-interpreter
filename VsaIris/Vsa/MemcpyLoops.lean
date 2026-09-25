import VsaIris.Vsa.MemcpySteps
import VsaIris.Vsa.AllocTac

/-!
# `memcpy` as one run

The whole function from its entry `0x80006bc8`, over the step table
(`MemcpySteps.lean`): the dispatch, the destination-alignment head
(`0x80006cbc`), the 72-byte loop (`0x80006c60`), the word loop (`0x80006c08`)
with its normalization (`0x80006c1c`), and the byte loop (`0x80006c48`). Each
loop is an induction whose motive is `MW` at the loop head, with the
registers given by their `toNat`s and the copied prefix `Cp`.
-/

namespace VsaIris.Memcpy

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast VsaIris.Sym
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-! ## Stores into the copied prefix -/

/-- Bytes `D + k` (`P k`) hold the source's `X + k`. -/
def CpS (D X : Nat) (img : Nat → BitVec 8) (P : Nat → Prop) (Mt : Mem) : Prop :=
  ∀ k, P k → imgM Mt (D + k) = img (X + k)

theorem CpS.mono {D X : Nat} {img : Nat → BitVec 8} {P P' : Nat → Prop} {Mt : Mem}
    (h : CpS D X img P Mt) (hP : ∀ k, P' k → P k) : CpS D X img P' Mt :=
  fun k hk => h k (hP k hk)

theorem imgM_sb (Mt : Mem) (a : Nat) (v : BitVec 64) (b : Nat) :
    imgM (writeLog Mt [(a, 1, v)]) b = if b = a then sbData v else imgM Mt b := by
  show ((Mt.insert a (sbData v))[b]?).getD 0 = _
  rw [Std.ExtHashMap.getElem?_insert]
  by_cases h : b = a
  · subst h; simp
  · simp only [beq_iff_eq, Ne.symm h, h, ite_false]; rfl

/-- One byte copied: `sb` of an `lbu` from the source. -/
theorem CpS.sb {D X : Nat} {img : Nat → BitVec 8} {P : Nat → Prop} {Mt : Mem}
    (h : CpS D X img P Mt) {a s o : Nat} (ha : a = D + o) (hs : s = X + o) :
    CpS D X img (fun k => P k ∨ k = o) (writeLog Mt [(a, 1, ldvf .lbu img s)]) := by
  intro k hk
  rw [imgM_sb]
  by_cases hko : k = o
  · subst hko
    rw [ite_eq_left_of_eq_true _ _ (eq_true ha.symm), hs]
    show sbData (zero_extend (m := 64) ((bytesAt img (X + k) 1).getD 0 0#8 : BitVec (8 * 1))) = _
    rw [sbData_zext]
    simp [bytesAt]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact h k (hk.resolve_right hko)

/-- One word copied: `sd` of an `ld` from the source. -/
theorem CpS.sd {D X : Nat} {img : Nat → BitVec 8} {P : Nat → Prop} {Mt : Mem}
    (h : CpS D X img P Mt) {a s o : Nat} (ha : a = D + o) (hs : s = X + o) :
    CpS D X img (fun k => P k ∨ (o ≤ k ∧ k < o + 8)) (writeLog Mt [(a, 8, ldvf .ld img s)]) := by
  intro k hk
  show ((writeMap8 Mt a (sdData_val (bytesVal .ld (bytesAt img s 8))))[D + k]?).getD 0 = _
  by_cases hko : o ≤ k ∧ k < o + 8
  · rw [show D + k = a + (k - o) by omega, writeMap8_ld_byte _ _ _ _ (by omega)]
    show (bytesAt img s 8).getD (k - o) 0#8 = _
    rw [bytesAt_getD img s (by omega), hs, show X + o + (k - o) = X + k by omega]
  · rw [getElem?_writeMap8_out _ _ _ _ (by omega)]
    exact h k (hk.resolve_right hko)

/-! ## The run's parameters -/

/-- The destination and source windows, and the return address. -/
structure Geo (dst src r : BitVec 64) (n : Nat) : Prop where
  dlo : 0x80000000 ≤ dst.toNat
  dhi : dst.toNat + n ≤ 0x100000000
  dhtif : 0x8001ad00 + 16 ≤ dst.toNat
  slo : 0x80000000 ≤ src.toNat
  shi : src.toNat + n ≤ 0x100000000
  shtif : src.toNat + n ≤ 0x8001ad00 ∨ 0x8001ad00 + 16 ≤ src.toNat
  ral : r.toNat % 4 = 0

/-- The end of a `memcpy` run: back at `r`, `a0 = dst`, the destination
holding the source image. -/
def mQ (dst r : BitVec 64) (n X : Nat) (img : Nat → BitVec 8) (rv : Nat → BitVec 64)
    (mv : Nat → BitVec 8) : Prop :=
  rv VsaIris.PC = r ∧ rv 1 = r ∧ rv 10 = dst ∧ ∀ k, k < n → mv (dst.toNat + k) = img (X + k)

/-- The run of `memcpy dst src n` returning to `r`. -/
abbrev MR (live : Nat → Prop) (dst src r : BitVec 64) (n : Nat) (img : Nat → BitVec 8) :
    BitVec 64 → (Nat → BitVec 64) → Mem → Prop :=
  MW live src.toNat n img (VsaIris.InExt (dst.toNat, n)) (mQ dst r n src.toNat img)

section Loops

variable {live : Nat → Prop} {dst src r : BitVec 64} {n : Nat} {img : Nat → BitVec 8}

/-- The return, with the whole destination copied. -/
theorem finish {R : Nat → BitVec 64} {Mt : Mem} (h1 : R 1 = r) (h10 : R 10 = dst)
    (hc : CpS dst.toNat src.toNat img (· < n) Mt) : MR live dst src r n img (R 1) R Mt :=
  mw_done fun rv mv hm => ⟨hm.pc.trans h1, (hm.regs 1 (by decide) (by decide)).trans h1,
    (hm.regs 10 (by decide) (by decide)).trans h10,
    fun k hk => (hm.img _ ⟨by omega, by omega⟩).trans (hc k hk)⟩

/-! ## Arithmetic -/

theorem toNat_and7 (x : BitVec 64) : (x &&& 7#64).toNat = x.toNat % 8 := and7_toNat x

theorem toNat_andm8 (x : BitVec 64) : (x &&& 18446744073709551608#64).toNat = x.toNat / 8 * 8 := by
  rw [show (18446744073709551608#64 : BitVec 64) = BitVec.allOnes 64 <<< 3 by decide,
    VsaIris.MallocFast.and_high_toNat x 3 (by decide)]

/-- A signed comparison of two small words is the unsigned one. -/
theorem toInt_small {x : BitVec 64} (h : x.toNat < 2 ^ 63) : x.toInt = x.toNat :=
  BitVec.toInt_eq_toNat_of_lt (by omega)

/-- Arithmetic side conditions: addresses, bounds and windows as `Nat` facts. -/
syntax "mx_side" : tactic
macro_rules
  | `(tactic| mx_side) => `(tactic| (
      (try simp only [LdOK, StOK, StOKb, InExt, Vsa.Sim.tohostAddr, upd_apply, Nat.reduceEqDiff,
        ite_true, ite_false, reduceIte, LeanRV64DExecutable.Functions.sign_extend,
        Sail.BitVec.signExtend, BitVec.reduceSignExtend, BitVec.add_zero]);
      (repeat (first | rw [BitVec.toNat_add] | rw [BitVec.toNat_sub] | rw [toNat_and7] | rw [toNat_andm8]));
      (try simp only [BitVec.reduceToNat, Nat.reducePow, BitVec.toNat_ofNat]);
      (try intro b hb); (try have hb' := of_mem_accAddrs hb);
      (first | done | omega)))

/-- A register equation or `toNat` fact after the register-file updates. -/
syntax "mx_reg" : tactic
macro_rules
  | `(tactic| mx_reg) => `(tactic| (first | assumption | (sx_norm; first | assumption | mx_side)))

theorem geo_facts {dst src r : BitVec 64} {n : Nat} (G : Geo dst src r n) :
    0x80000000 ≤ dst.toNat ∧ dst.toNat + n ≤ 0x100000000 ∧ 0x8001ad00 + 16 ≤ dst.toNat ∧
    0x80000000 ≤ src.toNat ∧ src.toNat + n ≤ 0x100000000 ∧
    (src.toNat + n ≤ 0x8001ad00 ∨ 0x8001ad00 + 16 ≤ src.toNat) :=
  ⟨G.dlo, G.dhi, G.dhtif, G.slo, G.shi, G.shtif⟩

theorem ne_of_toNat_ne {a b : BitVec 64} (h : a.toNat ≠ b.toNat) : a ≠ b := fun e => h (e ▸ rfl)

theorem byteLoop {live : Nat → Prop} (hlive : ∀ p ∈ mText, live p.1) {dst src r : BitVec 64} {n : Nat}
    {img : Nat → BitVec 8} (G : Geo dst src r n) :
    ∀ m i (R : Nat → BitVec 64) (Mt : Mem), i + m + 1 = n →
    (R 11).toNat = src.toNat + i → (R 14).toNat = dst.toNat + i →
    (R 17).toNat = dst.toNat + n → R 1 = r → R 10 = dst →
    CpS dst.toNat src.toNat img (· < i) Mt →
    MR live dst src r n img 0x80006c48#64 R Mt := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := geo_facts G
  intro m
  induction m with
  | zero =>
    intro i R Mt hm h11 h14 h17 h1 h10 hc
    refine mst_80006c48 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c4c hlive ?_
    refine mst_80006c50 hlive ?_
    refine mst_80006c54 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c58 hlive (fun hc' => absurd ?_ hc') (fun _ => ?_)
    · sx_norm; apply BitVec.eq_of_toNat_eq; mx_side
    · refine mst_80006c5c hlive (by sx_norm; rw [h1]; exact G.ral) ?_
      refine finish ?_ ?_ ?_
      · mx_reg
      · mx_reg
      exact (hc.sb (o := i) (by mx_side) (by mx_side)).mono (fun k hk => by omega)
  | succ m ih =>
    intro i R Mt hm h11 h14 h17 h1 h10 hc
    refine mst_80006c48 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c4c hlive ?_
    refine mst_80006c50 hlive ?_
    refine mst_80006c54 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c58 hlive (fun _ => ?_) (fun hc' => absurd ?_ hc')
    · sx_norm
      refine ih (i + 1) _ _ (by omega) (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg) ?_
      exact (hc.sb (o := i) (by mx_side) (by mx_side)).mono (fun k hk => by omega)
    · sx_norm; exact ne_of_toNat_ne (by mx_side)

end Loops

/-- The nine stores of one 72-byte iteration extend the copied prefix. -/
syntax "bulk_cp " term : tactic
macro_rules
  | `(tactic| bulk_cp $i) => `(tactic| exact
      ((((((((((‹CpS _ _ _ _ _›.sd (o := $i) (by mx_side) (by mx_side)).sd (o := $i + 8) (by mx_side) (by mx_side)).sd
        (o := $i + 64) (by mx_side) (by mx_side)).sd (o := $i + 16) (by mx_side) (by mx_side)).sd
        (o := $i + 24) (by mx_side) (by mx_side)).sd (o := $i + 32) (by mx_side) (by mx_side)).sd
        (o := $i + 40) (by mx_side) (by mx_side)).sd (o := $i + 48) (by mx_side) (by mx_side)).sd
        (o := $i + 56) (by mx_side) (by mx_side)).mono (fun k hk => by omega)))

theorem toNat_ne_of_ne {a b : BitVec 64} (h : ¬ a = b) : a.toNat ≠ b.toNat :=
  fun e => h (BitVec.eq_of_toNat_eq e)

theorem sltiu_ne {R : Nat → BitVec 64} {v : BitVec 64} :
    upd R 12 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x008#12))))) 12
      ≠ 0#64 ↔ v.toNat < 8 := by
  rw [upd_same]; exact bne_iff_ne.symm.trans (sltiu8_ne_zero_iff v)

theorem blt_iff_of {a b : BitVec 64} {A B : Nat} (ha : a.toNat = A) (hb : b.toNat = B)
    (hA : A < 2 ^ 63) (hB : B < 2 ^ 63) : a.toInt < b.toInt ↔ A < B := by
  rw [toInt_small (by omega), toInt_small (by omega), ha, hb]; omega

section Run
variable {live : Nat → Prop} (hlive : ∀ p ∈ mText, live p.1) {dst src r : BitVec 64} {n : Nat}
  {img : Nat → BitVec 8} (G : Geo dst src r n)
include hlive G

/-- The trailing-byte test `0x80006c38`: bytes left, or return. -/
theorem tailRun (i : Nat) (R : Nat → BitVec 64) (Mt : Mem) (hi : i ≤ n)
    (h11 : (R 11).toNat = src.toNat + i) (h14 : (R 14).toNat = dst.toNat + i)
    (h17 : (R 17).toNat = dst.toNat + n) (h1 : R 1 = r) (h10 : R 10 = dst)
    (hc : CpS dst.toNat src.toNat img (· < i) Mt) :
    MR live dst src r n img 0x80006c38#64 R Mt := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := geo_facts G
  refine mst_80006c38 hlive (fun hlt => ?_) (fun hge => ?_)
  · exact byteLoop hlive G (n - i - 1) i R Mt (by omega) h11 h14 h17 h1 h10 hc
  · refine mst_80006c3c hlive (by rw [h1]; exact G.ral) ?_
    refine finish h1 h10 (hc.mono fun k hk => by omega)

/-- The byte path `0x80006c40` from the entry registers. -/
theorem bytePath (R : Nat → BitVec 64) (Mt : Mem)
    (h11 : (R 11).toNat = src.toNat) (h17 : (R 17).toNat = dst.toNat + n) (h1 : R 1 = r)
    (h10 : R 10 = dst) : MR live dst src r n img 0x80006c40#64 R Mt := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := geo_facts G
  have e10 : (R 10).toNat = dst.toNat := by rw [h10]
  refine mst_80006c40 hlive ?_
  refine mst_80006c44 hlive (fun hge => ?_) (fun hlt => ?_)
  · refine mst_80006c3c hlive (by sx_norm; rw [h1]; exact G.ral) ?_
    refine finish ?_ ?_ ?_
    · mx_reg
    · mx_reg
    · intro k hk
      exfalso
      sx_norm
      rw [h10] at hge
      omega
  · refine byteLoop hlive G (n - 1) 0 _ Mt ?_ (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg)
      (by mx_reg) (fun k hk => absurd hk (by omega))
    sx_norm
    rw [h10] at hlt
    omega

/-- The word loop `0x80006c08` (`j` bytes copied, `m + 1` words left before the
last aligned word), and its normalization `0x80006c1c` into the tail. -/
theorem wordLoop (i0 : Nat) (hi0 : (dst.toNat + i0) % 8 = 0) :
    ∀ m j (R : Nat → BitVec 64) (Mt : Mem),
    dst.toNat + j + 8 * (m + 1) = (dst.toNat + n) / 8 * 8 → (dst.toNat + j) % 8 = 0 → i0 ≤ j →
    (R 13).toNat = src.toNat + j → (R 15).toNat = dst.toNat + j →
    (R 12).toNat = (dst.toNat + n) / 8 * 8 → (R 14).toNat = dst.toNat + i0 →
    (R 11).toNat = src.toNat + i0 → (R 17).toNat = dst.toNat + n → R 1 = r → R 10 = dst →
    CpS dst.toNat src.toNat img (· < j) Mt →
    MR live dst src r n img 0x80006c08#64 R Mt := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := geo_facts G
  intro m
  induction m with
  | zero =>
    intro j R Mt hm hj hij h13 h15 h12 h14 h11 h17 h1 h10 hc
    refine mst_80006c08 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c0c hlive ?_
    refine mst_80006c10 hlive ?_
    refine mst_80006c14 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c18 hlive (fun hlt => absurd hlt ?_) (fun _ => ?_)
    · mx_side
    refine mst_80006c1c hlive ?_
    refine mst_80006c20 hlive ?_
    refine mst_80006c24 hlive ?_
    refine mst_80006c28 hlive ?_
    refine mst_80006c2c hlive ?_
    refine mst_80006c30 hlive ?_
    refine mst_80006c34 hlive ?_
    sx_norm
    refine tailRun hlive G ((dst.toNat + n) / 8 * 8 - dst.toNat) _ _ (by omega) (by mx_reg)
      (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg) ?_
    exact (hc.sd (o := j) (by mx_side) (by mx_side)).mono (fun k hk => by omega)
  | succ m ih =>
    intro j R Mt hm hj hij h13 h15 h12 h14 h11 h17 h1 h10 hc
    refine mst_80006c08 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c0c hlive ?_
    refine mst_80006c10 hlive ?_
    refine mst_80006c14 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c18 hlive (fun _ => ?_) (fun hge => absurd ?_ hge)
    · sx_norm
      refine ih (j + 8) _ _ (by omega) (by omega) (by omega) (by mx_reg) (by mx_reg) (by mx_reg)
        (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg) ?_
      exact (hc.sd (o := j) (by mx_side) (by mx_side)).mono (fun k hk => by omega)
    · mx_side

/-- The word-loop entry `0x80006bfc` at an aligned offset `i`. -/
theorem wordEntry (i : Nat) (R : Nat → BitVec 64) (Mt : Mem) (hi : (dst.toNat + i) % 8 = 0)
    (hle : dst.toNat + i ≤ (dst.toNat + n) / 8 * 8)
    (h11 : (R 11).toNat = src.toNat + i) (h14 : (R 14).toNat = dst.toNat + i)
    (h12 : (R 12).toNat = (dst.toNat + n) / 8 * 8)
    (h17 : (R 17).toNat = dst.toNat + n) (h1 : R 1 = r) (h10 : R 10 = dst)
    (hc : CpS dst.toNat src.toNat img (· < i) Mt) :
    MR live dst src r n img 0x80006bfc#64 R Mt := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := geo_facts G
  refine mst_80006bfc hlive ?_
  refine mst_80006c00 hlive ?_
  refine mst_80006c04 hlive (fun hge => ?_) (fun hlt => ?_)
  · refine tailRun hlive G i _ Mt (by omega) (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg)
      (by mx_reg) hc
  · sx_norm
    refine wordLoop hlive G i hi (((dst.toNat + n) / 8 * 8 - (dst.toNat + i)) / 8 - 1) i _ Mt
      (by omega) hi (Nat.le_refl _) (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg)
      (by mx_reg) (by mx_reg) (by mx_reg) hc

/-- The 72-byte loop `0x80006c60` at an aligned offset `i` with at least 72
bytes before the last aligned word. -/
theorem bulkLoop : ∀ m i (R : Nat → BitVec 64) (Mt : Mem),
    (dst.toNat + n) / 8 * 8 < dst.toNat + i + 72 * (m + 1) →
    dst.toNat + i + 72 ≤ (dst.toNat + n) / 8 * 8 → (dst.toNat + i) % 8 = 0 →
    (R 11).toNat = src.toNat + i → (R 14).toNat = dst.toNat + i →
    (R 12).toNat = (dst.toNat + n) / 8 * 8 → (R 15).toNat = 64 →
    (R 17).toNat = dst.toNat + n → R 1 = r → R 10 = dst →
    CpS dst.toNat src.toNat img (· < i) Mt →
    MR live dst src r n img 0x80006c60#64 R Mt := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := geo_facts G
  intro m
  induction m with
  | zero => intro i R Mt hm hroom; omega
  | succ m ih =>
    intro i R Mt hm hroom hal h11 h14 h12 h15 h17 h1 h10 hc
    refine mst_80006c60 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c64 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c68 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c6c hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c70 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c74 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c78 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c7c hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c80 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c84 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c88 hlive ?_
    refine mst_80006c8c hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c90 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c94 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006c98 hlive ?_
    refine mst_80006c9c hlive (by mx_side) (by mx_side) ?_
    refine mst_80006ca0 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006ca4 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006ca8 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006cac hlive (by mx_side) (by mx_side) ?_
    refine mst_80006cb0 hlive ?_
    sx_norm
    refine mst_80006cb4 hlive (fun hlt => ?_) (fun hge => ?_)
    · have hlt' := (blt_iff_of (A := 64) (B := (dst.toNat + n) / 8 * 8 - (dst.toNat + i + 72)) (by mx_side) (by mx_side) (by omega) (by omega)).1 hlt
      exact ih (i + 72) _ _ (by omega) (by omega) (by omega) (by mx_reg) (by mx_reg) (by mx_reg)
        (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg) (by bulk_cp i)
    · have hge' : ¬ _ := fun h => hge ((blt_iff_of (A := 64) (B := (dst.toNat + n) / 8 * 8 - (dst.toNat + i + 72)) (by mx_side) (by mx_side) (by omega) (by omega)).2 h)
      refine mst_80006cb8 hlive ?_
      exact wordEntry hlive G (i + 72) _ _ (by omega) (by omega) (by mx_reg) (by mx_reg) (by mx_reg)
        (by mx_reg) (by mx_reg) (by mx_reg) (by bulk_cp i)

/-- The aligned entry `0x80006bec`: the last aligned word, then the 72-byte
loop or the word loop. -/
theorem alignedRun (i : Nat) (R : Nat → BitVec 64) (Mt : Mem) (hi : (dst.toNat + i) % 8 = 0)
    (hin : i ≤ n) (h11 : (R 11).toNat = src.toNat + i) (h14 : (R 14).toNat = dst.toNat + i)
    (h17 : (R 17).toNat = dst.toNat + n) (h1 : R 1 = r) (h10 : R 10 = dst)
    (hc : CpS dst.toNat src.toNat img (· < i) Mt) :
    MR live dst src r n img 0x80006bec#64 R Mt := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := geo_facts G
  refine mst_80006bec hlive ?_
  refine mst_80006bf0 hlive ?_
  refine mst_80006bf4 hlive ?_
  refine mst_80006bf8 hlive (fun hlt => ?_) (fun hge => ?_)
  · have hlt' := (blt_iff_of (A := 64) (B := (dst.toNat + n) / 8 * 8 - (dst.toNat + i))
      (by mx_side) (by mx_side) (by omega) (by omega)).1 hlt
    exact bulkLoop hlive G ((dst.toNat + n) / 8 * 8 - (dst.toNat + i)) i _ Mt (by omega) (by omega) hi
      (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg) hc
  · exact wordEntry hlive G i _ Mt hi (by omega) (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg)
      (by mx_reg) (by mx_reg) hc

/-- The destination-alignment head `0x80006cbc`: at most seven bytes, two per
iteration, until the destination is aligned. -/
theorem headLoop (h8 : 8 ≤ n) : ∀ m i (R : Nat → BitVec 64) (Mt : Mem),
    8 - (dst.toNat + i) % 8 ≤ m → (dst.toNat + i) % 8 ≠ 0 → dst.toNat % 8 + i < 8 →
    (R 11).toNat = src.toNat + i → (R 14).toNat = dst.toNat + i →
    (R 17).toNat = dst.toNat + n → R 1 = r → R 10 = dst →
    CpS dst.toNat src.toNat img (· < i) Mt →
    MR live dst src r n img 0x80006cbc#64 R Mt := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := geo_facts G
  intro m
  induction m with
  | zero => intro i R Mt hm hal; omega
  | succ m ih =>
    intro i R Mt hm hal hi8 h11 h14 h17 h1 h10 hc
    refine mst_80006cbc hlive (by mx_side) (by mx_side) ?_
    refine mst_80006cc0 hlive ?_
    refine mst_80006cc4 hlive ?_
    refine mst_80006cc8 hlive (by mx_side) (by mx_side) ?_
    refine mst_80006ccc hlive ?_
    refine mst_80006cd0 hlive (fun hz => ?_) (fun hnz => ?_)
    · have hz' := congrArg BitVec.toNat hz
      sx_norm
      have e1 : (dst.toNat + (i + 1)) % 8 = 0 := by revert hz'; mx_side
      exact alignedRun hlive G (i + 1) _ _ e1 (by omega) (by mx_reg) (by mx_reg) (by mx_reg)
        (by mx_reg) (by mx_reg) ((hc.sb (o := i) (by mx_side) (by mx_side)).mono fun k hk => by omega)
    · have hnz' := toNat_ne_of_ne hnz
      sx_norm
      have e1 : (dst.toNat + (i + 1)) % 8 ≠ 0 := by revert hnz'; mx_side
      refine mst_80006cd4 hlive (by mx_side) (by mx_side) ?_
      refine mst_80006cd8 hlive ?_
      refine mst_80006cdc hlive ?_
      refine mst_80006ce0 hlive (by mx_side) (by mx_side) ?_
      refine mst_80006ce4 hlive ?_
      refine mst_80006ce8 hlive (fun hnz2 => ?_) (fun hz2 => ?_)
      · have hnz2' := toNat_ne_of_ne hnz2
        sx_norm
        have e2 : (dst.toNat + (i + 2)) % 8 ≠ 0 := by revert hnz2'; mx_side
        exact ih (i + 2) _ _ (by omega) e2 (by omega) (by mx_reg) (by mx_reg) (by mx_reg)
          (by mx_reg) (by mx_reg)
          ((((hc.sb (o := i) (by mx_side) (by mx_side)).sb (o := i + 1) (by mx_side)
            (by mx_side))).mono fun k hk => by omega)
      · have hz2' : _ := Classical.not_not.mp hz2
        have hz2'' := congrArg BitVec.toNat hz2'
        sx_norm
        have e2 : (dst.toNat + (i + 2)) % 8 = 0 := by revert hz2''; mx_side
        refine mst_80006cec hlive ?_
        exact alignedRun hlive G (i + 2) _ _ e2 (by omega) (by mx_reg) (by mx_reg) (by mx_reg)
          (by mx_reg) (by mx_reg)
          ((((hc.sb (o := i) (by mx_side) (by mx_side)).sb (o := i + 1) (by mx_side)
            (by mx_side))).mono fun k hk => by omega)

/-- **`memcpy` from its entry**: the dispatch into the byte path, the head, or
the aligned path. -/
theorem entryRun (R : Nat → BitVec 64) (Mt : Mem) (h10 : R 10 = dst) (h11 : R 11 = src)
    (h12 : R 12 = BitVec.ofNat 64 n) (h1 : R 1 = r) :
    MR live dst src r n img 0x80006bc8#64 R Mt := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := geo_facts G
  have e10 : (R 10).toNat = dst.toNat := by rw [h10]
  have e11 : (R 11).toNat = src.toNat := by rw [h11]
  have e12 : (R 12).toNat = n := by rw [h12, BitVec.toNat_ofNat]; omega
  refine mst_80006bc8 hlive ?_
  refine mst_80006bcc hlive ?_
  refine mst_80006bd0 hlive ?_
  refine mst_80006bd4 hlive (fun _ => ?_) (fun _ => ?_)
  · exact bytePath hlive G _ Mt (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg)
  refine mst_80006bd8 hlive ?_
  refine mst_80006bdc hlive (fun _ => ?_) (fun hge => ?_)
  · exact bytePath hlive G _ Mt (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg)
  have h8 : 8 ≤ n := by
    refine Classical.byContradiction fun hlt => hge (sltiu_ne.2 ?_)
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    omega
  refine mst_80006be0 hlive ?_
  refine mst_80006be4 hlive ?_
  refine mst_80006be8 hlive (fun hnz => ?_) (fun hz => ?_)
  · have hnz' := toNat_ne_of_ne hnz
    sx_norm
    have e : (dst.toNat + 0) % 8 ≠ 0 := by revert hnz'; mx_side
    exact headLoop hlive G h8 8 0 _ Mt (by omega) e (by omega) (by mx_reg) (by mx_reg) (by mx_reg)
      (by mx_reg) (by mx_reg) (fun k hk => absurd hk (by omega))
  · have hz' := congrArg BitVec.toNat (Classical.not_not.mp hz)
    sx_norm
    have e : (dst.toNat + 0) % 8 = 0 := by revert hz'; mx_side
    exact alignedRun hlive G 0 _ Mt e (by omega) (by mx_reg) (by mx_reg) (by mx_reg) (by mx_reg)
      (by mx_reg) (fun k hk => absurd hk (by omega))

/-- **`memcpy` as one bounded local run** from its entry: `a0 = dst`,
`a1 = src`, `a2 = n`, `ra = r`, the destination at any tracked image. -/
theorem memcpyLocalRun (rv : Nat → BitVec 64) (Mt : Mem) (hpc : rv VsaIris.PC = 0x80006bc8#64)
    (h1 : rv 1 = r) (h10 : rv 10 = dst) (h11 : rv 11 = src) (h12 : rv 12 = BitVec.ofNat 64 n) :
    ∃ N, LocalRun (vsaModel live) [] (mText ++ srcText src.toNat n img) mRegs
      (VsaIris.InExt (dst.toNat, n)) (mQ dst r n src.toNat img) N rv (imgM Mt) := by
  obtain ⟨N, hN⟩ := entryRun hlive G rv Mt h10 h11 h12 h1
  exact ⟨N, hN rv (imgM Mt) ⟨hpc, fun _ _ _ => rfl, fun _ _ => rfl⟩⟩

end Run

end VsaIris.Memcpy
