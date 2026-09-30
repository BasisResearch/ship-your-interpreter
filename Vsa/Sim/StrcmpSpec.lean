import Vsa.Sim.Code.Strcmp
import Vsa.Sim.ChainFrameOut
import Vsa.Sim.StrlenSpec

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

def byteVal (cs : List Char) (k : Nat) : Nat :=
  match cs[k]? with
  | some c => c.toNat
  | none => 0

def firstDiff (csa csb : List Char) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let k := firstDiff csa csb n
    if k < n then k
    else if byteVal csa n = byteVal csb n then n + 1 else n

def isign (a b : Nat) : Int := if a < b then -1 else if a = b then 0 else 1

def strcmpSpecSign (csa csb : List Char) : Int :=
  let n := max csa.length csb.length + 1
  let k := firstDiff csa csb n
  isign (byteVal csa k) (byteVal csb k)

def strcmpSign (x : BitVec 64) : Int := if x = 0 then 0 else if x.toInt < 0 then -1 else 1

def BytePrefix (csa csb : List Char) (k : Nat) : Prop :=
  ∀ i, i < k → byteVal csa i = byteVal csb i ∧ byteVal csa i ≠ 0

theorem byteVal_ne_zero_lt {cs : List Char} {i : Nat} (h : byteVal cs i ≠ 0) :
    i < cs.length := by
  rcases Nat.lt_or_ge i cs.length with hlt | hge
  · exact hlt
  · have : cs[i]? = none := by simp; omega
    simp [byteVal, this] at h

theorem firstDiff_agree_eq (csa csb : List Char) (k : Nat)
    (h : ∀ i, i < k → byteVal csa i = byteVal csb i) :
    ∀ n, n ≤ k → firstDiff csa csb n = n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hnk : n ≤ k := by omega
    have hrec := ih hnk
    have hnltk : n < k := by omega
    have heq := h n hnltk
    simp only [firstDiff, hrec]
    rw [if_neg (Nat.lt_irrefl n), if_pos heq]

theorem firstDiff_prefix_eq (csa csb : List Char) (k : Nat) (h : BytePrefix csa csb k) :
    ∀ n, n ≤ k → firstDiff csa csb n = n :=
  firstDiff_agree_eq csa csb k (fun i hi => (h i hi).1)

theorem firstDiff_at (csa csb : List Char) (k : Nat) (hpre : BytePrefix csa csb k)
    (hne : byteVal csa k ≠ byteVal csb k) :
    ∀ n, k + 1 ≤ n → firstDiff csa csb n = k := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn
    rcases Nat.lt_or_ge k (n+1) with hlt | hge
    ·
      have hnk : k ≤ n := by omega
      rcases Nat.lt_or_ge k n with hkn | hkn
      ·
        have hrec := ih (by omega)
        simp only [firstDiff, hrec]
        rw [if_pos hkn]
      ·
        have hnk' : n = k := by omega
        have hpre_n : firstDiff csa csb n = n :=
          firstDiff_prefix_eq csa csb k hpre n hkn
        simp only [firstDiff, hpre_n]
        rw [if_neg (Nat.lt_irrefl n), if_neg (hnk' ▸ hne)]
        exact hnk'
    · omega

theorem strcmpSpecSign_at (csa csb : List Char) (k : Nat) (hpre : BytePrefix csa csb k)
    (hne : byteVal csa k ≠ byteVal csb k) :
    strcmpSpecSign csa csb = isign (byteVal csa k) (byteVal csb k) := by

  have hkmax : k ≤ max csa.length csb.length := by
    by_cases ha : byteVal csa k = 0
    · have hb : byteVal csb k ≠ 0 := fun h => hne (by rw [ha, h])
      have := byteVal_ne_zero_lt hb
      omega
    · have := byteVal_ne_zero_lt ha
      omega
  have hbound : k + 1 ≤ max csa.length csb.length + 1 := by omega
  show isign (byteVal csa (firstDiff csa csb (max csa.length csb.length + 1)))
    (byteVal csb (firstDiff csa csb (max csa.length csb.length + 1)))
    = isign (byteVal csa k) (byteVal csb k)
  rw [firstDiff_at csa csb k hpre hne _ hbound]

theorem strcmpSpecSign_eq (csa csb : List Char) (k : Nat) (hpre : BytePrefix csa csb k)
    (hka : csa.length = k) (hkb : csb.length = k) :
    strcmpSpecSign csa csb = 0 := by

  have hmax : max csa.length csb.length + 1 = k + 1 := by rw [hka, hkb]; simp

  have hbyteEqk : byteVal csa k = byteVal csb k := by
    have ha : byteVal csa k = 0 := by
      unfold byteVal
      have : csa[k]? = none := by simp; omega
      rw [this]
    have hb : byteVal csb k = 0 := by
      unfold byteVal
      have : csb[k]? = none := by simp; omega
      rw [this]
    rw [ha, hb]
  have hagree1 : ∀ i, i < k + 1 → byteVal csa i = byteVal csb i := by
    intro i hi
    rcases Nat.lt_or_ge i k with hik | hik
    · exact (hpre i hik).1
    · have hik' : i = k := by omega
      subst hik'; exact hbyteEqk
  show isign (byteVal csa (firstDiff csa csb (max csa.length csb.length + 1)))
    (byteVal csb (firstDiff csa csb (max csa.length csb.length + 1))) = 0
  rw [hmax, firstDiff_agree_eq csa csb (k+1) hagree1 (k+1) (Nat.le_refl _)]

  have hna : byteVal csa (k+1) = 0 := by
    unfold byteVal
    have : csa[k+1]? = none := by simp; omega
    rw [this]
  have hnb : byteVal csb (k+1) = 0 := by
    unfold byteVal
    have : csb[k+1]? = none := by simp; omega
    rw [this]
  rw [hna, hnb]; simp [isign]

theorem ptr_incr1 (p : BitVec 64) (k : Nat) :
    (p + BitVec.ofNat 64 k) + sign_extend (m := 64) (0x001#12) = p + BitVec.ofNat 64 (k+1) := by
  rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = BitVec.ofNat 64 1 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem zext_toNat (b : BitVec 8) : (zero_extend (m := 64) b).toNat = b.toNat := by
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (show b.toNat < 2^64 from by have := b.isLt; omega)]

theorem strcmpSign_sub (ba bb : BitVec 8) (hba : ba.toNat < 128) (hbb : bb.toNat < 128) :
    strcmpSign (zero_extend (m := 64) ba - zero_extend (m := 64) bb)
      = isign ba.toNat bb.toNat := by
  have hza := zext_toNat ba
  have hzb := zext_toNat bb
  have hb : ba.toNat < 2^64 := by have := ba.isLt; omega
  have hb2 : bb.toNat < 2^64 := by have := bb.isLt; omega
  have hxnat : (zero_extend (m := 64) ba - zero_extend (m := 64) bb).toNat
      = (2^64 - bb.toNat + ba.toNat) % 2^64 := by
    rw [BitVec.toNat_sub, hza, hzb]

  generalize hxdef : (zero_extend (m := 64) ba - zero_extend (m := 64) bb) = x at hxnat ⊢
  unfold strcmpSign isign
  by_cases heq : ba.toNat = bb.toNat
  · have hx0 : x = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [hxnat, heq]; simp; rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
    rw [if_pos hx0, if_neg (by omega : ¬ ba.toNat < bb.toNat), if_pos heq]
  · rcases Nat.lt_or_ge ba.toNat bb.toNat with hlt | hge
    ·
      have hmod : x.toNat = 2^64 - (bb.toNat - ba.toNat) := by
        rw [hxnat, Nat.mod_eq_of_lt (by omega)]; omega
      have hxne : x ≠ 0 := by intro hx; rw [hx] at hmod; simp at hmod; omega
      have hneg : x.toInt < 0 := by
        rw [BitVec.toInt_eq_msb_cond]
        have hmsb : x.msb = true := by rw [BitVec.msb_eq_decide]; simp; rw [hmod]; omega
        rw [if_pos hmsb, hmod]; omega
      rw [if_neg hxne, if_pos hneg, if_pos hlt]
    ·
      have hgt : bb.toNat < ba.toNat := by omega
      have hmod : x.toNat = ba.toNat - bb.toNat := by
        rw [hxnat, show 2^64 - bb.toNat + ba.toNat = 2^64 + (ba.toNat - bb.toNat) from by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      have hxne : x ≠ 0 := by intro hx; rw [hx] at hmod; simp at hmod; omega
      have hpos : ¬ x.toInt < 0 := by
        rw [BitVec.toInt_eq_toNat_of_lt (by rw [hmod]; omega), hmod]; omega
      rw [if_neg hxne, if_neg hpos, if_neg (by omega : ¬ ba.toNat < bb.toNat), if_neg heq]

theorem prefix_le_lena {csa csb : List Char} {k : Nat} (h : BytePrefix csa csb k) :
    k ≤ csa.length := by
  rcases Nat.lt_or_ge csa.length k with hk1 | hk1
  · obtain ⟨_, hne⟩ := h csa.length hk1
    exact absurd (byteVal_ne_zero_lt hne) (Nat.lt_irrefl _)
  · exact hk1

theorem prefix_le_lenb {csa csb : List Char} {k : Nat} (h : BytePrefix csa csb k) :
    k ≤ csb.length := by
  rcases Nat.lt_or_ge csb.length k with hk1 | hk1
  · obtain ⟨heq, hne⟩ := h csb.length hk1
    rw [heq] at hne
    exact absurd (byteVal_ne_zero_lt hne) (Nat.lt_irrefl _)
  · exact hk1

end Vsa.Sim
