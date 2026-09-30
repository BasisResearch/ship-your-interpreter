import Vsa.Sim.StrcmpSpecW2
import Vsa.Sim.ObsAvoid

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem slli32_eq_iff (w w' : BitVec 64) :
    (w <<< (32:Nat) = w' <<< (32:Nat)) ↔
      (∀ m, m < 4 → w.extractLsb' (8*m) 8 = w'.extractLsb' (8*m) 8) := by
  rw [shiftLeft_eq_iff w w' 32 (by omega)]
  constructor
  · intro h m hm; exact shiftLeft_bytes_agree w w' 4 (by simpa using h) m (by omega)
  · intro h i hi
    have hm : i / 8 < 4 := by omega
    have := congrArg (fun x => x.getLsbD (i % 8)) (h (i/8) hm)
    simp only [BitVec.getLsbD_extractLsb', decide_eq_true (show i % 8 < 8 from Nat.mod_lt _ (by decide)),
      Bool.true_and, show 8*(i/8) + i%8 = i from by omega] at this
    exact this

theorem slli16_eq_iff (w w' : BitVec 64) :
    (w <<< (16:Nat) = w' <<< (16:Nat)) ↔
      (∀ m, m < 6 → w.extractLsb' (8*m) 8 = w'.extractLsb' (8*m) 8) := by
  rw [shiftLeft_eq_iff w w' 16 (by omega)]
  constructor
  · intro h m hm; exact shiftLeft_bytes_agree w w' 2 (by simpa using h) m (by omega)
  · intro h i hi
    have hm : i / 8 < 6 := by omega
    have := congrArg (fun x => x.getLsbD (i % 8)) (h (i/8) hm)
    simp only [BitVec.getLsbD_extractLsb', decide_eq_true (show i % 8 < 8 from Nat.mod_lt _ (by decide)),
      Bool.true_and, show 8*(i/8) + i%8 = i from by omega] at this
    exact this

theorem shl_shr48_lo (w : BitVec 64) (s : Nat) (hs : s ≤ 6) :
    ((w <<< (8*s)) >>> (48:Nat)).extractLsb' 0 8 = w.extractLsb' (8*(6-s)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    Nat.zero_add, decide_eq_true (show i < 8 from hi), Bool.true_and]
  rw [show decide (48 + i < 8*s) = false from by simp; omega,
    show decide (48 + i < 64) = true from by simp; omega,
    show 48 + i - 8*s = 8*(6-s) + i from by omega]
  simp

theorem shl_shr48_hi (w : BitVec 64) (s : Nat) (hs : s ≤ 6) :
    ((w <<< (8*s)) >>> (48:Nat)).extractLsb' 8 8 = w.extractLsb' (8*(7-s)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    decide_eq_true (show i < 8 from hi), Bool.true_and]
  rw [show decide (48 + (8 + i) < 8*s) = false from by simp; omega,
    show decide (48 + (8 + i) < 64) = true from by simp; omega,
    show 48 + (8 + i) - 8*s = 8*(7-s) + i from by omega]
  simp

theorem andi_ff_eq_zext_byte (v : BitVec 64) :
    v &&& sign_extend (m := 64) (0x0ff#12) = zero_extend (m := 64) (v.extractLsb' 0 8) := by
  have hmaskeq : (sign_extend (m := 64) (0x0ff#12) : BitVec 64) = (0xff#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hmaskeq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0xff#64 : BitVec 64).toNat = 0xff from by decide]
  rw [zext_toNat]
  rw [BitVec.extractLsb'_toNat]
  rw [Nat.shiftRight_zero]

  rw [show (0xff:Nat) = 2^8 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem strcmpSign_block_sub (x y : BitVec 64)
    (hx : x.toNat < 2^16) (hy : y.toNat < 2^16)
    (hlo : x.toNat % 256 = y.toNat % 256)
    (hhx : x.toNat / 256 < 128) (hhy : y.toNat / 256 < 128) :
    strcmpSign (x - y) = isign (x.toNat / 256) (y.toNat / 256) := by
  have hxnat : (x - y).toNat = (2^64 - y.toNat + x.toNat) % 2^64 := by rw [BitVec.toNat_sub]
  generalize hxdef : (x - y) = z at hxnat ⊢
  unfold strcmpSign isign
  by_cases heq : x.toNat / 256 = y.toNat / 256
  · have hxy : x.toNat = y.toNat := by
      have e1 : x.toNat = 256 * (x.toNat / 256) + x.toNat % 256 := by omega
      have e2 : y.toNat = 256 * (y.toNat / 256) + y.toNat % 256 := by omega
      rw [e1, e2, heq, hlo]
    have hz0 : z = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [hxnat, hxy]; simp; rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
    rw [if_pos hz0, if_neg (by omega : ¬ x.toNat / 256 < y.toNat / 256), if_pos heq]
  · rcases Nat.lt_or_ge (x.toNat / 256) (y.toNat / 256) with hlt | hge
    · have hxlty : x.toNat < y.toNat := by
        have e1 : x.toNat = 256 * (x.toNat / 256) + x.toNat % 256 := by omega
        have e2 : y.toNat = 256 * (y.toNat / 256) + y.toNat % 256 := by omega
        rw [e1, e2, hlo]; have : 256 * (x.toNat / 256) < 256 * (y.toNat / 256) := by omega
        omega
      have hmod : z.toNat = 2^64 - (y.toNat - x.toNat) := by
        rw [hxnat, Nat.mod_eq_of_lt (by omega)]; omega
      have hzne : z ≠ 0 := by intro h; rw [h] at hmod; simp at hmod; omega
      have hneg : z.toInt < 0 := by
        rw [BitVec.toInt_eq_msb_cond]
        have hmsb : z.msb = true := by rw [BitVec.msb_eq_decide]; simp; rw [hmod]; omega
        rw [if_pos hmsb, hmod]; omega
      rw [if_neg hzne, if_pos hneg, if_pos hlt]
    · have hgt : y.toNat / 256 < x.toNat / 256 := by omega
      have hxgty : y.toNat < x.toNat := by
        have e1 : x.toNat = 256 * (x.toNat / 256) + x.toNat % 256 := by omega
        have e2 : y.toNat = 256 * (y.toNat / 256) + y.toNat % 256 := by omega
        rw [e1, e2, hlo]; have : 256 * (y.toNat / 256) < 256 * (x.toNat / 256) := by omega
        omega
      have hmod : z.toNat = x.toNat - y.toNat := by
        rw [hxnat, show 2^64 - y.toNat + x.toNat = 2^64 + (x.toNat - y.toNat) from by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      have hzne : z ≠ 0 := by intro h; rw [h] at hmod; simp at hmod; omega
      have hpos : ¬ z.toInt < 0 := by
        rw [BitVec.toInt_eq_toNat_of_lt (by rw [hmod]; omega), hmod]; omega
      rw [if_neg hzne, if_neg hpos, if_neg (by omega : ¬ x.toNat / 256 < y.toNat / 256), if_neg heq]

theorem shr48_lt (w : BitVec 64) : (w >>> (48:Nat)).toNat < 2^16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := w.isLt; omega

theorem block_lo (v : BitVec 64) : (v.extractLsb' 0 8).toNat = v.toNat % 256 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, show (2:Nat)^8 = 256 from by decide]

theorem block_hi (v : BitVec 64) (hv : v.toNat < 2^16) :
    (v.extractLsb' 8 8).toNat = v.toNat / 256 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, show (2:Nat)^8 = 256 from by decide]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem block_diff_lo_zero (A B : BitVec 64) (hA : A.toNat < 2^16) (hB : B.toNat < 2^16) :
    ((A - B).extractLsb' 0 8 = 0#8) ↔ (A.extractLsb' 0 8 = B.extractLsb' 0 8) := by
  have h264 : (2:Nat)^64 = 256 * 72057594037927936 := by decide
  have hBle : B.toNat ≤ 2^64 := by omega

  have hdiffmod : (A - B).toNat % 256 = ((256 - B.toNat % 256) + A.toNat % 256) % 256 := by
    rw [BitVec.toNat_sub]
    rcases Nat.lt_or_ge A.toNat B.toNat with hlt | hge
    · rw [Nat.mod_eq_of_lt (show 2^64 - B.toNat + A.toNat < 2^64 from by omega)]
      rw [h264]; omega
    · rw [show 2^64 - B.toNat + A.toNat = 2^64 + (A.toNat - B.toNat) from by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (show A.toNat - B.toNat < 2^64 from by omega)]
      omega
  rw [show (0#8 : BitVec 8) = (0#64 : BitVec 64).extractLsb' 0 8 from by decide]
  constructor
  · intro h
    have hnat : (A - B).toNat % 256 = 0 := by
      have := congrArg BitVec.toNat h; rw [block_lo] at this; simpa using this
    rw [hdiffmod] at hnat
    apply BitVec.eq_of_toNat_eq; rw [block_lo, block_lo]; omega
  · intro h
    have hlo : A.toNat % 256 = B.toNat % 256 := by
      have := congrArg BitVec.toNat h; rw [block_lo, block_lo] at this; exact this
    apply BitVec.eq_of_toNat_eq; rw [block_lo]
    show (A - B).toNat % 256 = _
    rw [hdiffmod]; simp; omega

theorem byteVal_drop (cs : List Char) (n i : Nat) :
    byteVal (cs.drop n) i = byteVal cs (n + i) := by
  unfold byteVal
  rw [List.getElem?_drop, Nat.add_comm n i]

theorem firstDiff_at_agree (csa csb : List Char) (d : Nat)
    (hagree : ∀ i, i < d → byteVal csa i = byteVal csb i)
    (hne : byteVal csa d ≠ byteVal csb d) :
    ∀ B, d + 1 ≤ B → firstDiff csa csb B = d := by
  intro B
  induction B with
  | zero => intro h; omega
  | succ B ih =>
    intro hB
    rcases Nat.lt_or_ge d (B+1) with hlt | hge
    · have hdB : d ≤ B := by omega
      rcases Nat.lt_or_ge d B with hdb | hdb
      · have hrec := ih (by omega)
        simp only [firstDiff, hrec]; rw [if_pos hdb]
      · have hdb' : d = B := by omega
        have hpre_n : firstDiff csa csb B = B := firstDiff_agree_eq csa csb d hagree B hdb
        simp only [firstDiff, hpre_n]
        rw [if_neg (Nat.lt_irrefl B), if_neg (hdb' ▸ hne)]; exact hdb'.symm
    · omega

theorem firstDiff_le (csa csb : List Char) : ∀ B, firstDiff csa csb B ≤ B := by
  intro B
  induction B with
  | zero => simp [firstDiff]
  | succ B ihB =>
    simp only [firstDiff]
    split
    · omega
    · split <;> omega

theorem firstDiff_is_least (csa csb : List Char) :
    ∀ B, (∀ i, i < firstDiff csa csb B → byteVal csa i = byteVal csb i) ∧
      (firstDiff csa csb B < B → byteVal csa (firstDiff csa csb B) ≠ byteVal csb (firstDiff csa csb B)) := by
  intro B
  induction B with
  | zero => exact ⟨fun i hi => by simp [firstDiff] at hi, fun h => by simp [firstDiff] at h⟩
  | succ B ih =>
    obtain ⟨ihagree, ihdiff⟩ := ih
    by_cases hkB : firstDiff csa csb B < B
    ·
      have hstep : firstDiff csa csb (B+1) = firstDiff csa csb B := by
        simp only [firstDiff]; rw [if_pos hkB]
      rw [hstep]
      exact ⟨ihagree, fun _ => ihdiff hkB⟩
    ·
      have hkeqB : firstDiff csa csb B = B := by
        have hle := firstDiff_le csa csb B
        omega
      have hagreeB : ∀ i, i < B → byteVal csa i = byteVal csb i := by
        rw [← hkeqB]; exact ihagree
      by_cases hbB : byteVal csa B = byteVal csb B
      · have hstep : firstDiff csa csb (B+1) = B + 1 := by
          simp only [firstDiff, hkeqB]
          rw [if_neg (Nat.lt_irrefl B), if_pos hbB]
        rw [hstep]
        refine ⟨fun i hi => ?_, fun h => by omega⟩
        rcases Nat.lt_or_ge i B with h | h
        · exact hagreeB i h
        · have : i = B := by omega
          subst this; exact hbB
      · have hstep : firstDiff csa csb (B+1) = B := by
          simp only [firstDiff, hkeqB]
          rw [if_neg (Nat.lt_irrefl B), if_neg hbB]
        rw [hstep]
        exact ⟨hagreeB, fun _ => hbB⟩

theorem strcmpSpecSign_drop (csa csb : List Char) (n : Nat)
    (hpre : ∀ i, i < n → byteVal csa i = byteVal csb i) :
    strcmpSpecSign (csa.drop n) (csb.drop n) = strcmpSpecSign csa csb := by
  classical
  by_cases hall : ∀ i, byteVal csa i = byteVal csb i
  ·
    have hsuf : ∀ i, byteVal (csa.drop n) i = byteVal (csb.drop n) i := by
      intro i
      rw [byteVal_drop, byteVal_drop]
      exact hall (n + i)
    have hz : ∀ (ca cb : List Char), (∀ i, byteVal ca i = byteVal cb i) → strcmpSpecSign ca cb = 0 := by
      intro ca cb h
      have : strcmpSpecSign ca cb
          = isign (byteVal ca (firstDiff ca cb (max ca.length cb.length + 1)))
                  (byteVal cb (firstDiff ca cb (max ca.length cb.length + 1))) := rfl
      rw [this, h (firstDiff ca cb (max ca.length cb.length + 1))]; simp [isign]
    rw [hz _ _ hsuf, hz _ _ hall]
  ·
    have hex : ∃ i, byteVal csa i ≠ byteVal csb i := by
      apply Decidable.byContradiction; intro h
      exact hall (fun i => Decidable.byContradiction (fun hne => h ⟨i, hne⟩))
    obtain ⟨wagree, wdiff⟩ := firstDiff_is_least csa csb (max csa.length csb.length + 1)

    have hfdlt : firstDiff csa csb (max csa.length csb.length + 1) < max csa.length csb.length + 1 := by
      rcases Nat.lt_or_ge (firstDiff csa csb (max csa.length csb.length + 1))
        (max csa.length csb.length + 1) with hlt | hge
      · exact hlt
      · exfalso
        obtain ⟨i, hi⟩ := hex
        have hib : i ≤ max csa.length csb.length := by
          by_cases ha : byteVal csa i = 0
          · have hb : byteVal csb i ≠ 0 := fun h => hi (by rw [ha, h])
            have := byteVal_ne_zero_lt hb; omega
          · have := byteVal_ne_zero_lt ha; omega
        exact hi (wagree i (by omega))

    have hdle : firstDiff csa csb (max csa.length csb.length + 1) ≤ max csa.length csb.length := by omega
    have hddiff := wdiff hfdlt
    have hdagree := wagree
    have hdn : n ≤ firstDiff csa csb (max csa.length csb.length + 1) := by
      rcases Nat.lt_or_ge (firstDiff csa csb (max csa.length csb.length + 1)) n with h | h
      · exact absurd (hpre _ h) hddiff
      · exact h

    have hwhole : strcmpSpecSign csa csb
        = isign (byteVal csa (firstDiff csa csb (max csa.length csb.length + 1)))
                (byteVal csb (firstDiff csa csb (max csa.length csb.length + 1))) := rfl

    have hsufdiff : byteVal (csa.drop n) (firstDiff csa csb (max csa.length csb.length + 1) - n)
        ≠ byteVal (csb.drop n) (firstDiff csa csb (max csa.length csb.length + 1) - n) := by
      rw [byteVal_drop, byteVal_drop,
        show n + (firstDiff csa csb (max csa.length csb.length + 1) - n)
           = firstDiff csa csb (max csa.length csb.length + 1) from by omega]
      exact hddiff
    have hsufagree : ∀ i, i < firstDiff csa csb (max csa.length csb.length + 1) - n →
        byteVal (csa.drop n) i = byteVal (csb.drop n) i := by
      intro i hi; rw [byteVal_drop, byteVal_drop]; exact hdagree (n + i) (by omega)
    have hsuf : strcmpSpecSign (csa.drop n) (csb.drop n)
        = isign (byteVal (csa.drop n) (firstDiff csa csb (max csa.length csb.length + 1) - n))
                (byteVal (csb.drop n) (firstDiff csa csb (max csa.length csb.length + 1) - n)) := by
      have hsufself : strcmpSpecSign (csa.drop n) (csb.drop n)
          = isign (byteVal (csa.drop n)
              (firstDiff (csa.drop n) (csb.drop n) (max (csa.drop n).length (csb.drop n).length + 1)))
              (byteVal (csb.drop n)
              (firstDiff (csa.drop n) (csb.drop n) (max (csa.drop n).length (csb.drop n).length + 1))) := rfl
      rw [hsufself, firstDiff_at_agree (csa.drop n) (csb.drop n)
        (firstDiff csa csb (max csa.length csb.length + 1) - n) hsufagree hsufdiff _ (by
          have hh : firstDiff csa csb (max csa.length csb.length + 1) - n
              ≤ max (csa.drop n).length (csb.drop n).length := by
            rw [List.length_drop, List.length_drop]; omega
          omega)]
    rw [hsuf, hwhole, byteVal_drop, byteVal_drop,
      show n + (firstDiff csa csb (max csa.length csb.length + 1) - n)
         = firstDiff csa csb (max csa.length csb.length + 1) from by omega]

end Vsa.Sim
