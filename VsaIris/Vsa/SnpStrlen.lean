import VsaIris.Vsa.SnpMove
import Vsa.Sim.StrlenMagic
import Vsa.Sim.MemcpySpec2
import Vsa.Sim.StrlenSpec

/-!
# `strlen` in a `snprintf` run

`strlen(a)` (`0x80006cf0`) on a string whose bytes are readable (`ReadWin`:
data or owned) up to its NUL: the byte peel to an 8-byte boundary, the word
loop (a load past the NUL reads bytes of any owner, `ntP_80006d10`; VSA's
zero-byte arithmetic `StrlenMagic.detect_all_ones` decides the exit) and the
byte tail. Memory is unchanged; `a0`–`a5` are clobbered.
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.MallocFast

/-- Byte `k` of a loaded word. -/
theorem ldvf_ld_byte (f : Nat → BitVec 8) (t k : Nat) (hk : k < 8) :
    (ldvf .ld f t).extractLsb' (8 * k) 8 = f (t + k) := by
  simp only [ldvf, bytesVal, widthOfM, sext64_self, bytesAt_getD f t (n := 8) (by decide : 0 < 8),
    bytesAt_getD f t (n := 8) (by decide : 1 < 8), bytesAt_getD f t (n := 8) (by decide : 2 < 8),
    bytesAt_getD f t (n := 8) (by decide : 3 < 8), bytesAt_getD f t (n := 8) (by decide : 4 < 8),
    bytesAt_getD f t (n := 8) (by decide : 5 < 8), bytesAt_getD f t (n := 8) (by decide : 6 < 8),
    bytesAt_getD f t (n := 8) (by decide : 7 < 8)]
  refine extractLsb'_ldData8 _ _ _ _ _ _ _ _ k hk _ ?_
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl

theorem byte_ne_zero_iff (b : BitVec 8) : b ≠ 0 ↔ b.toNat ≠ 0 := by
  constructor
  · intro h h0; exact h (BitVec.eq_of_toNat_eq h0)
  · intro h h0; exact h (by rw [h0]; rfl)

/-- A word of nonzero bytes passes the loop test. -/
theorem word_all_ones (f : Nat → BitVec 8) (t : Nat) (h : ∀ k, k < 8 → f (t + k) ≠ 0) :
    strlenWordVal (ldvf .ld f t) = BitVec.allOnes 64 :=
  (detect_all_ones _).mpr fun k hk => by rw [ldvf_ld_byte f t k hk]; exact h k hk

/-- A word with a NUL fails it. -/
theorem word_not_all_ones (f : Nat → BitVec 8) (t k : Nat) (hk : k < 8) (h : f (t + k) = 0) :
    strlenWordVal (ldvf .ld f t) ≠ BitVec.allOnes 64 := fun he =>
  (detect_all_ones _).mp he k hk (by rw [ldvf_ld_byte f t k hk]; exact h)

theorem ofNat_wrap (x k c : Nat) :
    BitVec.ofNat 64 (x + k + c) = BitVec.ofNat 64 (x + (k + c) % 18446744073709551616) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

theorem lbu_g (g : Nat → BitVec 8) (x : Nat) : ldvf .lbu g x = BitVec.zeroExtend 64 (g x) := by
  simp [ldvf, bytesVal, bytesAt, widthOfM]; rfl

theorem zext_eq_zero (b : BitVec 8) : BitVec.zeroExtend 64 b = 0#64 ↔ b = 0#8 := by
  constructor <;> intro h <;> bv_omega

/-- A string readable up to its NUL: `len` nonzero bytes at `a`, then `0`, all
readable (`ReadWin`); the word loop's last load may run 7 bytes past the NUL,
so the geometry reserves them. -/
structure StrRead (Dt : Mem) (DA : List Nat) (S : Nat → Prop) (Mt : Mem) (a len : Nat)
    (g : Nat → BitVec 8) : Prop where
  win : ReadWin Dt DA S Mt a (a + len + 1) g
  nz : ∀ i, i < len → g (a + i) ≠ 0
  nul : g (a + len) = 0
  lo : 0x80000000 ≤ a
  hi : a + len + 8 ≤ 0x100000000
  htif : a + len + 8 ≤ 0x8001ad00 ∨ 0x8001ad08 ≤ a

/-- The registers `strlen` keeps: all but `a0`–`a5`. -/
def SLKeep (R' R : Nat → BitVec 64) : Prop :=
  ∀ z, z ≠ 10 → z ≠ 11 → z ≠ 12 → z ≠ 13 → z ≠ 14 → z ≠ 15 → R' z = R z

theorem SLKeep.trans {R R' R'' : Nat → BitVec 64} (h1 : SLKeep R' R) (h2 : SLKeep R'' R') :
    SLKeep R'' R := fun z a b c d e f => (h2 z a b c d e f).trans (h1 z a b c d e f)

macro "sl_keep" : tactic =>
  `(tactic| (intro z h1 h2 h3 h4 h5 h6; simp only [upd_apply, h1, h2, h3, h4, h5, h6, ite_false]))

theorem StrRead.byteNz {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {Mt : Mem} {a len : Nat}
    {g : Nat → BitVec 8} (h : StrRead Dt DA S Mt a len g) {x : Nat} (h1 : a ≤ x) (h2 : x < a + len) :
    g (BitVec.ofNat 64 x).toNat ≠ 0#8 := by
  have hx : (BitVec.ofNat 64 x).toNat = a + (x - a) := by
    have := h.hi; simp only [BitVec.toNat_ofNat]; omega
  rw [hx]; exact h.nz _ (by omega)

theorem StrRead.byteNul {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {Mt : Mem} {a len : Nat}
    {g : Nat → BitVec 8} (h : StrRead Dt DA S Mt a len g) {x : Nat} (h1 : x = a + len) :
    g (BitVec.ofNat 64 x).toNat = 0#8 := by
  have hx : (BitVec.ofNat 64 x).toNat = a + len := by
    have := h.hi; simp only [BitVec.toNat_ofNat]; omega
  rw [hx]; exact h.nul

theorem snez_zero {b : BitVec 8} (h : b = 0#8) :
    LeanRV64DExecutable.zero_extend (m := 64) (LeanRV64DExecutable.Functions.bool_to_bit
      (LeanRV64DExecutable.Functions.zopz0zI_u (0#64) (BitVec.zeroExtend 64 b))) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have := snez_toNat b
  refine this.trans ?_
  simp [h]

theorem snez_one {b : BitVec 8} (h : b ≠ 0#8) :
    LeanRV64DExecutable.zero_extend (m := 64) (LeanRV64DExecutable.Functions.bool_to_bit
      (LeanRV64DExecutable.Functions.zopz0zI_u (0#64) (BitVec.zeroExtend 64 b))) = 1#64 := by
  apply BitVec.eq_of_toNat_eq
  have := snez_toNat b
  refine this.trans ?_
  simp [h]

/-- A branch on a tail byte whose value the context fixes. -/
macro_rules
  | `(tactic| sx_side) => `(tactic| (intro hc; simp only [zext_eq_zero] at hc; contradiction))

/-- **One arm of the byte tail** (`0x80006d2c`): the word at `t` holds the NUL
at `t + K`; `strlen` returns `len`. -/
macro "#sl_tail " nm:ident K:num : command => `(
theorem $nm {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem} {a len : Nat}
    {g : Nat → BitVec 8} (SR : StrRead Dt DA S Mt a len g) (R0 : Nat → BitVec 64)
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', R' 10 = BitVec.ofNat 64 len → SLKeep R' R0 → NW live Dt DA S Q (R0 1) R' Mt)
    (t : Nat) (R : Nat → BitVec 64) (htk : t + $K = a + len) (hta : a ≤ t)
    (h14 : R 14 = BitVec.ofNat 64 (t + 8)) (h10 : R 10 = BitVec.ofNat 64 a) (hkp : SLKeep R R0) :
    NW live Dt DA S Q 0x80006d2c#64 R Mt := by
  have hw := SR.win
  have hlo := SR.lo
  have hhi := SR.hi
  have hh := SR.htif
  have hR1 : R 1 = R0 1 := hkp 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have fZ : g (BitVec.ofNat 64 (t + $K)).toNat = 0#8 := SR.byteNul htk
  (try simp only [Nat.add_zero] at fZ)
  (try have f0 : g (BitVec.ofNat 64 t).toNat ≠ 0#8 := SR.byteNz hta (by omega))
  (try have f1 : g (BitVec.ofNat 64 (t + 1)).toNat ≠ 0#8 := SR.byteNz (by omega) (by omega))
  (try have f2 : g (BitVec.ofNat 64 (t + 2)).toNat ≠ 0#8 := SR.byteNz (by omega) (by omega))
  (try have f3 : g (BitVec.ofNat 64 (t + 3)).toNat ≠ 0#8 := SR.byteNz (by omega) (by omega))
  (try have f4 : g (BitVec.ofNat 64 (t + 4)).toNat ≠ 0#8 := SR.byteNz (by omega) (by omega))
  (try have f5 : g (BitVec.ofNat 64 (t + 5)).toNat ≠ 0#8 := SR.byteNz (by omega) (by omega))
  (try have f6 : g (BitVec.ofNat 64 (t + 6)).toNat ≠ 0#8 := SR.byteNz (by omega) (by omega))
  iterate 9 (all_goals (try (snp_ld hw; simp only [lbu_g])); all_goals (try nx_run hlive using [h14, ofNat_add_ofNat, ofNat_wrap, Nat.reduceAdd, Nat.reduceMod, Nat.add_zero, zext_eq_zero]))
  case hal => simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [hR1]; exact hal
  rw [hR1]
  refine hk _ ?_ (SLKeep.trans hkp (by sl_keep))
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [h10]
  (try first | rw [snez_zero fZ] | rw [snez_one f6])
  bv_nat)

#sl_tail sl_tail0 0
#sl_tail sl_tail7 7
#sl_tail sl_tail1 1
#sl_tail sl_tail2 2
#sl_tail sl_tail3 3
#sl_tail sl_tail4 4
#sl_tail sl_tail5 5
#sl_tail sl_tail6 6

theorem sl_tailK {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem} {a len : Nat}
    {g : Nat → BitVec 8} (SR : StrRead Dt DA S Mt a len g) (R0 : Nat → BitVec 64)
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', R' 10 = BitVec.ofNat 64 len → SLKeep R' R0 → NW live Dt DA S Q (R0 1) R' Mt)
    (t k : Nat) (R : Nat → BitVec 64) (hk8 : k < 8) (htk : t + k = a + len) (hta : a ≤ t)
    (h14 : R 14 = BitVec.ofNat 64 (t + 8)) (h10 : R 10 = BitVec.ofNat 64 a) (hkp : SLKeep R R0) :
    NW live Dt DA S Q 0x80006d2c#64 R Mt := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  · exact sl_tail0 hlive SR R0 hal hk t R htk hta h14 h10 hkp
  · exact sl_tail1 hlive SR R0 hal hk t R htk hta h14 h10 hkp
  · exact sl_tail2 hlive SR R0 hal hk t R htk hta h14 h10 hkp
  · exact sl_tail3 hlive SR R0 hal hk t R htk hta h14 h10 hkp
  · exact sl_tail4 hlive SR R0 hal hk t R htk hta h14 h10 hkp
  · exact sl_tail5 hlive SR R0 hal hk t R htk hta h14 h10 hkp
  · exact sl_tail6 hlive SR R0 hal hk t R htk hta h14 h10 hkp
  · exact sl_tail7 hlive SR R0 hal hk t R htk hta h14 h10 hkp

/-- **The word loop** (`0x80006d10`) at the aligned `t`, the NUL within the
next `m` words. -/
theorem sl_words {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem} {a len : Nat}
    {g : Nat → BitVec 8} (SR : StrRead Dt DA S Mt a len g) (R0 : Nat → BitVec 64)
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', R' 10 = BitVec.ofNat 64 len → SLKeep R' R0 → NW live Dt DA S Q (R0 1) R' Mt) :
    ∀ m t (R : Nat → BitVec 64), a + len < t + 8 * m → a ≤ t → t ≤ a + len →
      R 14 = BitVec.ofNat 64 t → R 13 = 9187201950435737471#64 → R 11 = 18446744073709551615#64 →
      R 10 = BitVec.ofNat 64 a → SLKeep R R0 → NW live Dt DA S Q 0x80006d10#64 R Mt := by
  have hlo := SR.lo
  have hhi := SR.hi
  have hh := SR.htif
  intro m
  induction m with
  | zero => intro t _ h; omega
  | succ m ih =>
    intro t R hm hta ht h14 h13 h11 h10 hkp
    nx_run hlive using [h14] at 0x80006d14
    rintro ⟨f, hfD, hfS, hv⟩
    have et : (BitVec.ofNat 64 t).toNat = t := by simp only [BitVec.toNat_ofNat]; omega
    rw [et] at hv
    subst hv
    by_cases hfull : t + 8 ≤ a + len
    · have hg : (((ldvf .ld f t &&& 9187201950435737471#64) + 9187201950435737471#64 |||
          ldvf .ld f t) ||| 9187201950435737471#64) = 18446744073709551615#64 := by
        rw [ldvf_readWin SR.win hfD hfS .ld (by omega) (by simp only [widthOfM]; omega)]
        exact (word_all_ones g t fun k hk => by
          have := SR.nz (t + k - a) (by omega); rwa [show a + (t + k - a) = t + k by omega] at this).trans
          (by decide)
      nx_run hlive using [h14, h13, h11, h10, ofNat_add_ofNat] at 0x80006d10 0x80006d2c
      all_goals rename_i hc
      all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h11] at hc
      case hT =>
        refine ih (t + 8) _ (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_ (SLKeep.trans hkp (by sl_keep))
        all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        all_goals first | rfl | assumption
      case hF => exact absurd hg hc
    · have hz : f (t + (a + len - t)) = 0#8 := by
        rw [show t + (a + len - t) = a + len by omega]
        exact ((SR.win (a + len) (by omega) (by omega)).img hfD hfS).trans SR.nul
      have hg : ¬ (((ldvf .ld f t &&& 9187201950435737471#64) + 9187201950435737471#64 |||
          ldvf .ld f t) ||| 9187201950435737471#64) = 18446744073709551615#64 := fun he =>
        word_not_all_ones f t (a + len - t) (by omega) hz (he.trans (by decide))
      nx_run hlive using [h14, h13, h11, h10, ofNat_add_ofNat] at 0x80006d10 0x80006d2c
      all_goals rename_i hc
      all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h11] at hc
      case hT => exact absurd hc hg
      case hF =>
        refine sl_tailK hlive SR R0 hal hk t (a + len - t) _ (by omega) (by omega) hta ?_ ?_
          (SLKeep.trans hkp (by sl_keep))
        all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        all_goals first | rfl | assumption

/-- The word loop's setup (`0x80006cfc`: the mask `0x7f…7f` and `-1`). -/
theorem sl_align {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem} {a len : Nat}
    {g : Nat → BitVec 8} (SR : StrRead Dt DA S Mt a len g) (R0 : Nat → BitVec 64)
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', R' 10 = BitVec.ofNat 64 len → SLKeep R' R0 → NW live Dt DA S Q (R0 1) R' Mt)
    (t : Nat) (R : Nat → BitVec 64) (hta : a ≤ t) (ht : t ≤ a + len)
    (h14 : R 14 = BitVec.ofNat 64 t) (h10 : R 10 = BitVec.ofNat 64 a) (hkp : SLKeep R R0) :
    NW live Dt DA S Q 0x80006cfc#64 R Mt := by
  nx_run hlive using [h14] at 0x80006d10
  refine sl_words hlive SR R0 hal hk ((a + len - t) / 8 + 1) t _ (by omega) hta ht ?_ ?_ ?_ ?_
    (SLKeep.trans hkp (by sl_keep))
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  all_goals first | rfl | assumption

/-- One pass of the byte peel (`0x80006d78`) at `a + j`. -/
theorem sl_peel_step {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem} {a len : Nat}
    {g : Nat → BitVec 8} (SR : StrRead Dt DA S Mt a len g) (R0 : Nat → BitVec 64)
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', R' 10 = BitVec.ofNat 64 len → SLKeep R' R0 → NW live Dt DA S Q (R0 1) R' Mt)
    (j : Nat) (R : Nat → BitVec 64) (hj : j ≤ len)
    (h14 : R 14 = BitVec.ofNat 64 (a + j)) (h10 : R 10 = BitVec.ofNat 64 a) (hkp : SLKeep R R0)
    (hnext : j < len → ∀ R' : Nat → BitVec 64, R' 14 = BitVec.ofNat 64 (a + (j + 1)) →
      R' 10 = BitVec.ofNat 64 a → SLKeep R' R0 → NW live Dt DA S Q 0x80006d78#64 R' Mt) :
    NW live Dt DA S Q 0x80006d78#64 R Mt := by
  have hlo := SR.lo
  have hhi := SR.hi
  have hh := SR.htif
  have hR1 : R 1 = R0 1 := hkp 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hb : ReadB Dt DA S Mt (a + j) (g (a + j)) := SR.win _ (by omega) (by omega)
  refine ntP_80006d78 hlive ?_ ?_
  · rw [h14]; sx_addr
  rintro v ⟨f, hfD, hfS, rfl⟩
  have e14 : (R 14 + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)).toNat = a + j := by
    rw [h14]
    simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
      BitVec.reduceSignExtend, BitVec.add_zero, BitVec.toNat_ofNat]; omega
  rw [e14, ldvf_lbu_readB hb hfD hfS]
  have hjl_of : BitVec.zeroExtend 64 (g (a + j)) ≠ 0#64 → j < len := fun hc0 => by
    rcases Nat.lt_or_ge j len with hlt | hge
    · exact hlt
    · exact absurd (by rw [show j = len by omega, SR.nul]; rfl) hc0
  nx_run hlive using [h14, ofNat_add_ofNat] at 0x80006d78 0x80006cfc
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *)
  case hF.hal => rw [hR1]; exact hal
  case hF.hk =>
    rename_i hc
    have hj' : j = len := by
      rcases Nat.lt_or_ge j len with hlt | hge
      · exact absurd (fun h0 => SR.nz j hlt ((zext_eq_zero _).mp h0)) hc
      · omega
    subst hj'
    rw [hR1]
    refine hk _ ?_ (SLKeep.trans hkp (by sl_keep))
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [h10]
    bv_nat
  all_goals rename_i hc0 hc1
  case hT.hT =>
    have hjl := hjl_of hc0
    refine sl_align hlive SR R0 hal hk (a + j + 1) _ (by omega) (by omega) ?_ ?_ (SLKeep.trans hkp (by sl_keep))
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    all_goals first | rfl | assumption
  case hT.hF =>
    have hjl := hjl_of hc0
    refine hnext hjl _ ?_ ?_ (SLKeep.trans hkp (by sl_keep))
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    all_goals first | rfl | assumption | (rw [Nat.add_assoc])

/-- **`strlen(a)`** (`0x80006cf0`) in a `snprintf` run: returns `len` in
`a0`, keeps every register outside `a0`–`a5` and memory. -/
theorem strlen_nw {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem} {a len : Nat}
    {g : Nat → BitVec 8} (SR : StrRead Dt DA S Mt a len g) (R : Nat → BitVec 64)
    (h10 : R 10 = BitVec.ofNat 64 a) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', R' 10 = BitVec.ofNat 64 len → SLKeep R' R → NW live Dt DA S Q (R 1) R' Mt) :
    NW live Dt DA S Q 0x80006cf0#64 R Mt := by
  have hpeel : ∀ k j (R' : Nat → BitVec 64), j + k = len → R' 14 = BitVec.ofNat 64 (a + j) →
      R' 10 = BitVec.ofNat 64 a → SLKeep R' R → NW live Dt DA S Q 0x80006d78#64 R' Mt := by
    intro k
    induction k with
    | zero =>
      intro j R' hj h14 h10' hkp
      exact sl_peel_step hlive SR R hal hk j R' (by omega) h14 h10' hkp (fun h => absurd h (by omega))
    | succ k ih =>
      intro j R' hj h14 h10' hkp
      exact sl_peel_step hlive SR R hal hk j R' (by omega) h14 h10' hkp
        (fun _ R'' h14' h10'' hkp' => ih (j + 1) R'' (by omega) h14' h10'' hkp')
  nx_run hlive using [h10] at 0x80006d78 0x80006cfc
  case hT =>
    refine hpeel len 0 _ (by omega) ?_ ?_ (by sl_keep)
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero]
    all_goals first | rfl | assumption
  case hF =>
    refine sl_align hlive SR R hal hk a _ (by omega) (by omega) ?_ ?_ (by sl_keep)
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    all_goals first | rfl | assumption

end VsaIris.Sym
