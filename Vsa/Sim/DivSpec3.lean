import Vsa.Sim.DivSites3
import Vsa.Sim.ObsAvoid
import Vsa.Sim.SegEffect

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem toInt_of_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) :
    x.toInt = (x.toNat : Int) - 2^64 := by
  rw [BitVec.toInt_eq_toNat_cond]; have hx := x.isLt; rw [if_neg (by omega)]; simp

theorem toInt_of_notop (x : BitVec 64) (h : x.toNat < 2^63) :
    x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]; rw [if_pos (by omega)]

theorem neg_toNat_of_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) :
    ((0#64) - x).toNat = 2^64 - x.toNat := by
  rw [BitVec.toNat_sub]; have hx := x.isLt
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega

theorem natAbs_of_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) :
    x.toInt.natAbs = 2^64 - x.toNat := by
  rw [toInt_of_top x h]; have hx := x.isLt
  rw [Int.natAbs_eq_iff]; right; push_cast; omega

theorem natAbs_of_notop (x : BitVec 64) (h : x.toNat < 2^63) :
    x.toInt.natAbs = x.toNat := by
  rw [toInt_of_notop x h]; simp

theorem bltz_true' (x : BitVec 64) (h : zopz0zI_s x (0#64) = true) : 2^63 ≤ x.toNat := by
  unfold zopz0zI_s at h; simp only [BitVec.toInt_zero] at h
  have hlt : x.toInt < 0 := by have := of_decide_eq_true h; simpa using this
  rw [BitVec.toInt_eq_toNat_cond] at hlt
  by_cases hb : 2 * x.toNat < 2^64
  · rw [if_pos hb] at hlt; omega
  · omega

theorem bltz_false' (x : BitVec 64) (h : zopz0zI_s x (0#64) = false) : x.toNat < 2^63 := by
  unfold zopz0zI_s at h; simp only [BitVec.toInt_zero] at h
  have hge : 0 ≤ x.toInt := by
    have := of_decide_eq_false h; simp only [Int.not_lt] at this; exact this
  rw [BitVec.toInt_eq_toNat_cond] at hge
  by_cases hb : 2 * x.toNat < 2^64
  · omega
  · rw [if_neg hb] at hge; have := x.isLt; omega

theorem bgez_true' (x : BitVec 64) (h : zopz0zKzJ_s x (0#64) = true) : x.toNat < 2^63 := by
  unfold zopz0zKzJ_s at h; simp only [BitVec.toInt_zero] at h
  have hge : 0 ≤ x.toInt := by have := of_decide_eq_true h; simpa using this
  rw [BitVec.toInt_eq_toNat_cond] at hge
  by_cases hb : 2 * x.toNat < 2^64
  · omega
  · rw [if_neg hb] at hge; have := x.isLt; omega

theorem bgez_false' (x : BitVec 64) (h : zopz0zKzJ_s x (0#64) = false) : 2^63 ≤ x.toNat := by
  unfold zopz0zKzJ_s at h; simp only [BitVec.toInt_zero] at h
  have hlt : x.toInt < 0 := by
    have := of_decide_eq_false h; simp only [Int.not_le] at this; exact this
  rw [BitVec.toInt_eq_toNat_cond] at hlt
  by_cases hb : 2 * x.toNat < 2^64
  · rw [if_pos hb] at hlt; omega
  · omega

theorem bltz_cases' (x : BitVec 64) : zopz0zI_s x (0#64) = true ∨ zopz0zI_s x (0#64) = false :=
  Bool.eq_false_or_eq_true _
theorem bgez_cases' (x : BitVec 64) : zopz0zKzJ_s x (0#64) = true ∨ zopz0zKzJ_s x (0#64) = false :=
  Bool.eq_false_or_eq_true _

theorem bgtz_true' (x : BitVec 64) (h : zopz0zI_s (0#64) x = true) : 0 < x.toInt := by
  unfold zopz0zI_s at h; simp only [BitVec.toInt_zero] at h
  have := of_decide_eq_true h; simpa using this
theorem bgtz_false' (x : BitVec 64) (h : zopz0zI_s (0#64) x = false) : x.toInt ≤ 0 := by
  unfold zopz0zI_s at h; simp only [BitVec.toInt_zero] at h
  have := of_decide_eq_false h; simp only [Int.not_lt] at this; exact this
theorem bgtz_cases' (x : BitVec 64) : zopz0zI_s (0#64) x = true ∨ zopz0zI_s (0#64) x = false :=
  Bool.eq_false_or_eq_true _

theorem tmod_nonpos_of_nonpos (a b : Int) (h : a ≤ 0) : a.tmod b ≤ 0 := by
  have := Int.tmod_nonneg (a := -a) b (by omega)
  rw [Int.neg_tmod] at this; omega

theorem tmod_of_natAbs_sign (a b q : Int)
    (hmag : q.natAbs = a.natAbs % b.natAbs)
    (hsign : 0 ≤ a → 0 ≤ q) (hsign2 : a < 0 → q ≤ 0) :
    q = a.tmod b := by
  have hnat : (a.tmod b).natAbs = a.natAbs % b.natAbs := Int.natAbs_tmod a b
  have habs : q.natAbs = (a.tmod b).natAbs := by rw [hmag, hnat]
  have hcases := Int.natAbs_eq_natAbs_iff.mp habs
  rcases Int.lt_trichotomy a 0 with ha | ha | ha
  · have hq0 := hsign2 (by omega)
    have htm := tmod_nonpos_of_nonpos a b (by omega)
    rcases hcases with h | h
    · exact h
    · omega
  · subst ha; simp only [Int.zero_tmod]
    have : q.natAbs = 0 := by rw [hmag]; simp
    exact Int.natAbs_eq_zero.mp this
  · have hq0 := hsign (by omega)
    have htm := Int.tmod_nonneg b (by omega : (0:Int) ≤ a)
    rcases hcases with h | h
    · exact h
    · omega

theorem tdiv_of_natAbs_sign (a b q : Int) (hb : b ≠ 0)
    (hmag : q.natAbs = a.natAbs / b.natAbs)
    (hsign : (0 ≤ a ↔ 0 ≤ b) → 0 ≤ q)
    (hsign2 : ¬(0 ≤ a ↔ 0 ≤ b) → q ≤ 0) :
    q = a.tdiv b := by
  have hnat : (a.tdiv b).natAbs = a.natAbs / b.natAbs := Int.natAbs_tdiv a b
  have habs : q.natAbs = (a.tdiv b).natAbs := by rw [hmag, hnat]
  have hcases := Int.natAbs_eq_natAbs_iff.mp habs

  by_cases hz : a.natAbs / b.natAbs = 0
  ·
    have hq0 : q = 0 := Int.natAbs_eq_zero.mp (by rw [hmag]; exact hz)
    have ht0 : a.tdiv b = 0 := Int.natAbs_eq_zero.mp (by rw [hnat]; exact hz)
    rw [hq0, ht0]
  ·
    rcases hcases with h | h
    · exact h
    · exfalso

      have htdne : a.tdiv b ≠ 0 := fun hc => hz (by rw [← hnat, hc]; simp)

      by_cases ha : 0 ≤ a <;> by_cases hb2 : 0 ≤ b
      · have hs : (0 ≤ a ↔ 0 ≤ b) := ⟨fun _ => hb2, fun _ => ha⟩
        have hq0 := hsign hs
        have htpos : 0 ≤ a.tdiv b := Int.tdiv_nonneg ha hb2
        omega
      · have hbneg : b < 0 := by omega
        have hs : ¬(0 ≤ a ↔ 0 ≤ b) := fun hi => absurd (hi.mp ha) (by omega)
        have hq0 := hsign2 hs
        have htneg : a.tdiv b ≤ 0 := by
          have := Int.tdiv_nonneg (a := a) (b := -b) ha (by omega); rw [Int.tdiv_neg] at this; omega
        omega
      · have haneg : a < 0 := by omega
        have hs : ¬(0 ≤ a ↔ 0 ≤ b) := fun hi => absurd (hi.mpr hb2) (by omega)
        have hq0 := hsign2 hs
        have htneg : a.tdiv b ≤ 0 := by
          have := Int.tdiv_nonneg (a := -a) (b := b) (by omega) hb2; rw [Int.neg_tdiv] at this; omega
        omega
      · have hs : (0 ≤ a ↔ 0 ≤ b) := ⟨fun hi => absurd hi ha, fun hi => absurd hi hb2⟩
        have hq0 := hsign hs
        have htpos : 0 ≤ a.tdiv b := by
          have := Int.tdiv_nonneg (a := -a) (b := -b) (by omega) (by omega)
          rwa [Int.neg_tdiv_neg] at this
        omega

theorem core_call_tail_f
    (A B r q : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (cent : Config)
    (hG : GoodState cent.σ)
    (hcl : __hidden___udivdi3Loaded cent.σ.mem) (hmem : cent.σ.mem = m0)
    (hout : cent.σ.sailOutput = o)
    (hpc : cent.σ.regs.get? Register.PC = some (0x800046ac#64))
    (hx10 : cent.σ.regs.get? Register.x10 = some A)
    (hx11 : cent.σ.regs.get? Register.x11 = some B)
    (hx1 : cent.σ.regs.get? Register.x1 = some q)
    (hx12 : ∃ v, cent.σ.regs.get? Register.x12 = some v)
    (hx13 : ∃ v, cent.σ.regs.get? Register.x13 = some v)
    (hmi : ∃ v, cent.σ.regs.get? Register.minstret = some v)
    (htick : cent.tick < 2) (hBpos : 0 < B.toNat) (halign : q.toNat % 4 = 0) :
    ∃ c3 : Config, Steps cent c3 ∧ GoodState c3.σ ∧ c3.σ.mem = m0 ∧
      c3.σ.sailOutput = o ∧
      c3.σ.regs.get? Register.PC = some q ∧
      c3.σ.regs.get? Register.x10 = some (A / B) ∧
      c3.σ.regs.get? Register.x11 = some (A % B) ∧
      c3.σ.regs.get? Register.x1 = some q ∧ c3.tick < 2 ∧
      (∀ R : Register, NotWritten R → c3.σ.regs.get? R = cent.σ.regs.get? R) ∧
      (∃ v, c3.σ.regs.get? Register.minstret = some v) := by
  obtain ⟨v12, h12⟩ := hx12
  obtain ⟨v13, h13⟩ := hx13
  have hcorepre : udivdi3_pre (fun R => cent.σ.regs.get? R) A B q m0 o cent := by
    refine ⟨⟨v12, v13, ?_⟩, hBpos, halign⟩
    exact {
      good := hG, loaded := hcl, mem := hmem, sailOut := hout, pc := hpc,
      a0 := hx10, a1 := hx11, a2 := h12, a3 := h13, ra := hx1, minstret := hmi,
      tick := htick, hframe := fun R _ => rfl }
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, hrem3, hra3, htick3, hframe3, _hx12_3, _hx13_3⟩ :=
    udivdi3_spec (fun R => cent.σ.regs.get? R) A B q m0 o cent hcorepre
  obtain ⟨vmi3, hmi3⟩ := hG3.minstret
  exact ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, hrem3, hra3, htick3, hframe3, ⟨vmi3, hmi3⟩⟩

theorem natAbs_le (x : BitVec 64) : x.toInt.natAbs ≤ 2^63 := by
  by_cases h : x.toNat < 2^63
  · rw [natAbs_of_notop x h]; omega
  · rw [natAbs_of_top x (by omega)]; have := x.isLt; omega

theorem mag_notop (x : BitVec 64) (h : x.toNat < 2^63) : x.toNat = x.toInt.natAbs :=
  (natAbs_of_notop x h).symm

theorem mag_neg_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) : ((0#64) - x).toNat = x.toInt.natAbs := by
  rw [neg_toNat_of_top x h, natAbs_of_top x h]

theorem res_pos (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hnneg : 0 ≤ n.toInt) (hd0 : d.toInt ≠ 0) :
    (A % B).toInt = n.toInt.tmod d.toInt := by
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  have hBpos : 0 < B.toNat := by rw [hB]; omega
  have hBle : d.toInt.natAbs ≤ 2^63 := natAbs_le d
  have hmod : (A % B).toNat = n.toInt.natAbs % d.toInt.natAbs := by rw [BitVec.toNat_umod, hA, hB]
  have hlt : (A % B).toNat < 2^63 := by
    rw [hmod]; have := Nat.mod_lt (n.toInt.natAbs) (show 0 < d.toInt.natAbs by omega); omega
  have hresInt : (A % B).toInt = ((A % B).toNat : Int) := toInt_of_notop _ hlt
  apply tmod_of_natAbs_sign
  · rw [hresInt, Int.natAbs_natCast, hmod]
  · intro _; rw [hresInt]; exact Int.natCast_nonneg _
  · intro h; omega

theorem res_neg (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hnneg : n.toInt < 0) (hd0 : d.toInt ≠ 0) :
    ((0#64) - (A % B)).toInt = n.toInt.tmod d.toInt := by
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  have hBpos : 0 < B.toNat := by rw [hB]; omega
  have hBle : d.toInt.natAbs ≤ 2^63 := natAbs_le d
  have hmod : (A % B).toNat = n.toInt.natAbs % d.toInt.natAbs := by rw [BitVec.toNat_umod, hA, hB]
  have hlt : (A % B).toNat < 2^63 := by
    rw [hmod]; have := Nat.mod_lt (n.toInt.natAbs) (show 0 < d.toInt.natAbs by omega); omega
  by_cases hz : (A % B).toNat = 0
  · have h0 : ((0#64) - (A%B)) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp [hz]
    rw [h0]
    apply tmod_of_natAbs_sign
    · simp only [BitVec.toInt_zero, Int.natAbs_zero]; rw [hmod] at hz; omega
    · intro h; omega
    · intro _; simp
  · have hres : ((0#64) - (A%B)).toNat = 2^64 - (A%B).toNat := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.zero_mod]; have := (A%B).isLt; omega
    have hresTop : 2^63 ≤ ((0#64) - (A%B)).toNat := by rw [hres]; omega
    have hresInt : ((0#64)-(A%B)).toInt = (((0#64)-(A%B)).toNat : Int) - 2^64 := toInt_of_top _ hresTop
    apply tmod_of_natAbs_sign
    · rw [natAbs_of_top _ hresTop, hres, hmod]; omega
    · intro h; omega
    · intro _; rw [hresInt, hres]; omega

theorem toInt_lt_2p63 (n : BitVec 64) : n.toInt < 2^63 := by
  by_cases h : n.toNat < 2^63
  · rw [toInt_of_notop n h]; have := n.isLt; omega
  · rw [toInt_of_top n (by omega)]; have := n.isLt; omega

theorem udiv_le (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs) :
    (A / B).toNat ≤ 2^63 := by
  rw [BitVec.toNat_udiv, hA, hB]
  have h1 : n.toInt.natAbs ≤ 2^63 := natAbs_le n
  calc n.toInt.natAbs / d.toInt.natAbs ≤ n.toInt.natAbs := Nat.div_le_self _ _
    _ ≤ 2^63 := h1

theorem udiv_lt_of_not_overflow (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hsame : 0 ≤ n.toInt ↔ 0 ≤ d.toInt) (hd0 : d.toInt ≠ 0)
    (hexcl : ¬(n.toInt = -2^63 ∧ d.toInt = -1)) :
    (A / B).toNat < 2^63 := by
  rw [BitVec.toNat_udiv, hA, hB]
  have h1 : n.toInt.natAbs ≤ 2^63 := natAbs_le n
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  have hnlt : n.toInt < 2^63 := toInt_lt_2p63 n
  by_cases hd1 : d.toInt.natAbs = 1
  · rw [hd1, Nat.div_one]
    by_cases hn : n.toInt.natAbs = 2^63
    · exfalso
      have hnval : n.toInt = -2^63 := by
        rcases Int.natAbs_eq n.toInt with he | he
        · rw [hn] at he; omega
        · rw [hn] at he; omega
      have hdval : d.toInt = -1 := by
        have hdneg : ¬ (0 ≤ d.toInt) := fun hc => absurd (hsame.mpr hc) (by omega)
        rcases Int.natAbs_eq d.toInt with he | he
        · rw [hd1] at he; omega
        · rw [hd1] at he; omega
      exact hexcl ⟨hnval, hdval⟩
    · omega
  · have hd2 : 2 ≤ d.toInt.natAbs := by omega
    calc n.toInt.natAbs / d.toInt.natAbs ≤ n.toInt.natAbs / 2 := Nat.div_le_div_left hd2 (by omega)
      _ < 2^63 := by omega

theorem res_div_same (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hsame : 0 ≤ n.toInt ↔ 0 ≤ d.toInt) (hd0 : d.toInt ≠ 0)
    (hnov : (A / B).toNat < 2^63) :
    (A / B).toInt = n.toInt.tdiv d.toInt := by
  have hmag : (A / B).toNat = n.toInt.natAbs / d.toInt.natAbs := by rw [BitVec.toNat_udiv, hA, hB]
  have hresInt : (A / B).toInt = ((A/B).toNat : Int) := toInt_of_notop _ hnov
  apply tdiv_of_natAbs_sign _ _ _ hd0
  · rw [hresInt, Int.natAbs_natCast, hmag]
  · intro _; rw [hresInt]; exact Int.natCast_nonneg _
  · intro h; exact absurd hsame h

theorem res_div_mixed (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hdiff : ¬(0 ≤ n.toInt ↔ 0 ≤ d.toInt)) (hd0 : d.toInt ≠ 0) :
    ((0#64) - (A / B)).toInt = n.toInt.tdiv d.toInt := by
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  have hmag : (A / B).toNat = n.toInt.natAbs / d.toInt.natAbs := by rw [BitVec.toNat_udiv, hA, hB]
  have hle : (A / B).toNat ≤ 2^63 := udiv_le n d A B hA hB
  by_cases hz : (A / B).toNat = 0
  · have h0 : ((0#64) - (A/B)) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp [hz]
    rw [h0]
    apply tdiv_of_natAbs_sign _ _ _ hd0
    · simp only [BitVec.toInt_zero, Int.natAbs_zero]; rw [hmag] at hz; omega
    · intro _; simp
    · intro _; simp
  · have hres : ((0#64) - (A/B)).toNat = 2^64 - (A/B).toNat := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.zero_mod]; have := (A/B).isLt; omega
    have hresTop : 2^63 ≤ ((0#64) - (A/B)).toNat := by rw [hres]; omega
    have hresInt : ((0#64)-(A/B)).toInt = (((0#64)-(A/B)).toNat : Int) - 2^64 := toInt_of_top _ hresTop
    apply tdiv_of_natAbs_sign _ _ _ hd0
    · rw [natAbs_of_top _ hresTop, hres, hmag]; omega
    · intro h; exact absurd h hdiff
    · intro _; rw [hresInt, hres]; omega

private theorem addi0 (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [sext_zero]; exact BitVec.add_zero v

abbrev NotWrittenD (R : Register) : Prop :=
  NotWritten R ∧ (Register.x1 == R) = false ∧ (Register.x5 == R) = false

theorem NotWrittenD.nw {R : Register} (h : NotWrittenD R) : NotWritten R := h.1

theorem frame_jal {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) (R : Register)
    (hrd : (rd_reg == R) = false) (hR : NotWritten R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jal σ pc vm imm rd_reg link R hmi hpc hrd hnpc hmii

def divOverflowKeep (R : Register) : Bool := decide (NotWrittenD R)

theorem SelectedFramedSegResult.frameD {bs : List BBlock} {L : GRegs}
    {lds : List (List (BitVec 8))} {pc0 : BitVec 64} {sel : GRegs} {c c' : Config}
    {g : (R : Register) → Option (RegisterType R)}
    (res : SelectedFramedSegResult bs L lds pc0 (fun _ => False) divOverflowKeep sel c c')
    (h : ∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R) :
    ∀ R : Register, NotWrittenD R → c'.σ.regs.get? R = g R :=
  fun R hR => (res.reg_frame R (decide_eq_true hR)).trans (h R hR)

theorem jr_tgt_ok (r : BitVec 64) (h : r.toNat % 4 = 0) :
    (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
  rw [ret_tgt r h]; exact h

theorem core_call_seg {c : Config} {pc vm link A B r w12 w13 : BitVec 64} {imm : BitVec 21}
    {m0 : Std.ExtHashMap Nat (BitVec 8)} {o : Array String}
    (hsite : ∃ (σ' : MState) (i' : Nat), Step ⟨c.σ, c.tick, c.steps⟩ ⟨σ', i', c.steps + 1⟩ ∧
      i' < 2 ∧ GoodState σ' ∧ σ'.mem = c.σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal c.σ pc vm imm Register.x1 link))
    (hce : pc + sign_extend (m := 64) imm = 0x800046ac#64)
    (hcl : __hidden___udivdi3Loaded c.σ.mem) (hmem : c.σ.mem = m0) (hout : c.σ.sailOutput = o)
    (hL : GHolds c.σ [(10, A), (11, B), (5, r), (12, w12), (13, w13)])
    (hBpos : 0 < B.toNat) (hlink : link.toNat % 4 = 0) :
    ∃ c3 : Config, Steps c c3 ∧ GoodState c3.σ ∧ c3.σ.mem = m0 ∧ c3.σ.sailOutput = o ∧
      c3.σ.regs.get? Register.PC = some link ∧ c3.tick < 2 ∧
      (∃ v, c3.σ.regs.get? Register.minstret = some v) ∧
      GHolds c3.σ [(10, A / B), (11, A % B), (5, r)] ∧
      ∀ R : Register, NotWrittenD R → c3.σ.regs.get? R = c.σ.regs.get? R := by
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ := hsite
  obtain ⟨h10, h11, h5, h12, h13, _⟩ := hL
  have keepJ : ∀ (R : Register) {w : RegisterType R}, NotWritten R → (Register.x1 == R) = false →
      c.σ.regs.get? R = some w → σ2.regs.get? R = some w :=
    fun R _ hR h1 hw => (frame_jal hobs R h1 hR).trans hw
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, hrem3, _, hi3, hfr3, hmi3⟩ :=
    core_call_tail_f A B r link m0 o ⟨σ2, i2, c.steps + 1⟩ hG2 (hmem2 ▸ hcl) (hmem2.trans hmem)
      (hobs.2.trans hout) ((obs_jal_pc_env hobs).trans (congrArg some hce))
      (obs_jal_other_env hobs Register.x10 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h10)
      (obs_jal_other_env hobs Register.x11 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h11)
      (obs_jal_rd_env hobs (by decide) (by decide) (by decide) (by decide) (by decide))
      ⟨w12, obs_jal_other_env hobs Register.x12 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h12⟩
      ⟨w13, obs_jal_other_env hobs Register.x13 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h13⟩
      (obs_jal_minstret_env hobs) hi2 hBpos hlink
  refine ⟨c3, (Steps.single hstep).trans hs3, hG3, hmem3, hout3, hpc3, hi3, hmi3,
    ⟨hq3, hrem3, (hfr3 Register.x5 (by decide)).trans (keepJ Register.x5 (by decide) (by decide) h5),
      trivial⟩, fun R hR => (hfr3 R hR.nw).trans (frame_jal hobs R hR.2.1 hR.nw)⟩

def divIn (n d r w12 w13 : BitVec 64) : GRegs :=
  [(10, n), (11, d), (1, r), (12, w12), (13, w13)]

#derive_case divOverflowBranchSeg chain []
  terminator ⟨0x800046a4#64, 0x06054063#32, 0x63#8, 0x40#8, 0x05#8, 0x06#8,
    .br bop.BLT true, 10, 0, 0x0060#13, 0#21, 0#12⟩

#derive_case divdi3PosSeg chain []
  terminator ⟨0x800046a4#64, 0x06054063#32, 0x63#8, 0x40#8, 0x05#8, 0x06#8,
    .br bop.BLT false, 10, 0, 0x0060#13, 0#21, 0#12⟩ ;;
  [] terminator ⟨0x800046a8#64, 0x0605c663#32, 0x63#8, 0xc6#8, 0x05#8, 0x06#8,
    .br bop.BLT false, 11, 0, 0x006c#13, 0#21, 0#12⟩

#derive_case divdi3PosNegSeg chain []
  terminator ⟨0x800046a4#64, 0x06054063#32, 0x63#8, 0x40#8, 0x05#8, 0x06#8,
    .br bop.BLT false, 10, 0, 0x0060#13, 0#21, 0#12⟩ ;;
  [] terminator ⟨0x800046a8#64, 0x0605c663#32, 0x63#8, 0xc6#8, 0x05#8, 0x06#8,
    .br bop.BLT true, 11, 0, 0x006c#13, 0#21, 0#12⟩

#derive_case divdi3PosNegSeg2 chain
  [(0x80004714#64, 0x40b005b3#32), (0x80004718#64, 0x00008293#32)]

#derive_case divdi3NegPosSeg chain
  [(0x80004704#64, 0x40a00533#32)]
    terminator ⟨0x80004708#64, 0x00b04863#32, 0x63#8, 0x48#8, 0xb0#8, 0x00#8,
      .br bop.BLT true, 0, 11, 0x0010#13, 0#21, 0#12⟩ ;;
  [(0x80004718#64, 0x00008293#32)]

#derive_case divdi3NegNegSeg chain
  [(0x80004704#64, 0x40a00533#32)]
    terminator ⟨0x80004708#64, 0x00b04863#32, 0x63#8, 0x48#8, 0xb0#8, 0x00#8,
      .br bop.BLT false, 0, 11, 0x0010#13, 0#21, 0#12⟩ ;;
  [(0x8000470c#64, 0x40b005b3#32)]
    terminator ⟨0x80004710#64, 0xf9dff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xf9#8,
      .j, 0, 0, 0#13, 0x1fff9c#21, 0#12⟩

#derive_case divdi3NegTailSeg chain
  [(0x80004720#64, 0x40a00533#32)]
    terminator ⟨0x80004724#64, 0x00028067#32, 0x67#8, 0x80#8, 0x02#8, 0x00#8,
      .jr, 5, 0, 0#13, 0#21, 0#12⟩

def moddi3_pre (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ Vsa.Sim.Code.__moddi3Loaded c.σ.mem ∧ __hidden___udivdi3Loaded c.σ.mem ∧
  c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧ c.σ.regs.get? Register.PC = some (0x80004728#64) ∧
  c.σ.regs.get? Register.x10 = some n ∧ c.σ.regs.get? Register.x11 = some d ∧
  c.σ.regs.get? Register.x1 = some r ∧ (∃ v, c.σ.regs.get? Register.minstret = some v) ∧
  (∃ v, c.σ.regs.get? Register.x12 = some v) ∧ (∃ v, c.σ.regs.get? Register.x13 = some v) ∧
  c.tick < 2 ∧ d.toInt ≠ 0 ∧ r.toNat % 4 = 0 ∧
  (∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R)

def moddi3_post (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧ c.σ.regs.get? Register.PC = some r ∧
  c.tick < 2 ∧
  (∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R) ∧
  ∃ res, c.σ.regs.get? Register.x10 = some res ∧ res.toInt = n.toInt.tmod d.toInt

#derive_case moddi3PPSeg chain
  [(0x80004728#64, 0x00008293#32)]
    terminator ⟨0x8000472c#64, 0x0005ca63#32, 0x63#8, 0xca#8, 0x05#8, 0x00#8,
      .br bop.BLT false, 11, 0, 0x0014#13, 0#21, 0#12⟩ ;;
  [] terminator ⟨0x80004730#64, 0x00054c63#32, 0x63#8, 0x4c#8, 0x05#8, 0x00#8,
      .br bop.BLT false, 10, 0, 0x0018#13, 0#21, 0#12⟩

#derive_case moddi3NPSeg chain
  [(0x80004728#64, 0x00008293#32)]
    terminator ⟨0x8000472c#64, 0x0005ca63#32, 0x63#8, 0xca#8, 0x05#8, 0x00#8,
      .br bop.BLT false, 11, 0, 0x0014#13, 0#21, 0#12⟩ ;;
  [] terminator ⟨0x80004730#64, 0x00054c63#32, 0x63#8, 0x4c#8, 0x05#8, 0x00#8,
      .br bop.BLT true, 10, 0, 0x0018#13, 0#21, 0#12⟩ ;;
  [(0x80004748#64, 0x40a00533#32)]

#derive_case moddi3PNSeg chain
  [(0x80004728#64, 0x00008293#32)]
    terminator ⟨0x8000472c#64, 0x0005ca63#32, 0x63#8, 0xca#8, 0x05#8, 0x00#8,
      .br bop.BLT true, 11, 0, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x80004740#64, 0x40b005b3#32)]
    terminator ⟨0x80004744#64, 0xfe0558e3#32, 0xe3#8, 0x58#8, 0x05#8, 0xfe#8,
      .br bop.BGE true, 10, 0, 0x1ff0#13, 0#21, 0#12⟩

#derive_case moddi3NNSeg chain
  [(0x80004728#64, 0x00008293#32)]
    terminator ⟨0x8000472c#64, 0x0005ca63#32, 0x63#8, 0xca#8, 0x05#8, 0x00#8,
      .br bop.BLT true, 11, 0, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x80004740#64, 0x40b005b3#32)]
    terminator ⟨0x80004744#64, 0xfe0558e3#32, 0xe3#8, 0x58#8, 0x05#8, 0xfe#8,
      .br bop.BGE false, 10, 0, 0x1ff0#13, 0#21, 0#12⟩ ;;
  [(0x80004748#64, 0x40a00533#32)]

#derive_case moddi3PosTailSeg chain
  [(0x80004738#64, 0x00058513#32)]
    terminator ⟨0x8000473c#64, 0x00028067#32, 0x67#8, 0x80#8, 0x02#8, 0x00#8,
      .jr, 5, 0, 0#13, 0#21, 0#12⟩

#derive_case moddi3NegTailSeg chain
  [(0x80004750#64, 0x40b00533#32)]
    terminator ⟨0x80004754#64, 0x00028067#32, 0x67#8, 0x80#8, 0x02#8, 0x00#8,
      .jr, 5, 0, 0#13, 0#21, 0#12⟩

theorem moddi3_fin_pos (g : (R : Register) → Option (RegisterType R))
    (n d A B r w12 w13 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (c : Config) (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some 0x80004734#64)
    (hmi : ∃ v, c.σ.regs.get? Register.minstret = some v) (hi : c.tick < 2)
    (hwl : Vsa.Sim.Code.__moddi3Loaded c.σ.mem) (hcl : __hidden___udivdi3Loaded c.σ.mem)
    (hmem : c.σ.mem = m0) (hout : c.σ.sailOutput = o)
    (hL : GHolds c.σ [(10, A), (11, B), (5, r), (12, w12), (13, w13)])
    (hBpos : 0 < B.toNat) (halign : r.toNat % 4 = 0)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hd0 : d.toInt ≠ 0) (hsign : 0 ≤ n.toInt)
    (hframe0 : ∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R) :
    ∃ c' : Config, Steps c c' ∧ moddi3_post g n d r m0 o c' := by
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hi3, ⟨vm3, hvm3⟩, hL3, hfr3⟩ :=
    core_call_seg (site3_80004734 c.σ c.tick c.steps _ vm hG hpc hvm hwl rfl hi) (by decide)
      hcl hmem hout hL hBpos (by decide)
  have hwl3 : Vsa.Sim.Code.__moddi3Loaded c3.σ.mem := by rw [hmem3, ← hmem]; exact hwl
  have facts : ChainFacts c3.σ.mem c3.σ.mem [(10, A / B), (11, A % B), (5, r)] []
      moddi3PosTailSeg := by
    chain_facts hwl3 with "Vsa.Sim.Code.__moddi3_at_"
    exact jr_tgt_ok r halign
  obtain ⟨c4, res⟩ := segEval_selected_framed moddi3PosTailSeg _ [] 0x80004738#64 vm3
    (fun _ => False) divOverflowKeep [(10, A % B)] c3 hG3 hpc3 hvm3 hL3
    (by show KeysOK [10, 11, 5]; decide) facts (by show ChainOK _ [10, 11, 5] _; decide) hi3
    (fun _ _ => rfl) (by decide) (by decide) ⟨congrArg some (addi0 _), trivial⟩
  obtain ⟨hq, _⟩ := res.selected_regs
  refine ⟨c4, hs3.trans res.steps, res.good, res.mem_eq.trans hmem3, res.output.trans hout3,
    res.pc.trans (congrArg some (ret_tgt r halign)), res.tick, ?_, _, hq,
    res_pos n d A B hA hB hsign hd0⟩
  intro R hR
  exact (res.reg_frame R (decide_eq_true hR)).trans ((hfr3 R hR).trans (hframe0 R hR))

theorem moddi3_fin_neg (g : (R : Register) → Option (RegisterType R))
    (n d A B r w12 w13 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (c : Config) (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some 0x8000474c#64)
    (hmi : ∃ v, c.σ.regs.get? Register.minstret = some v) (hi : c.tick < 2)
    (hwl : Vsa.Sim.Code.__moddi3Loaded c.σ.mem) (hcl : __hidden___udivdi3Loaded c.σ.mem)
    (hmem : c.σ.mem = m0) (hout : c.σ.sailOutput = o)
    (hL : GHolds c.σ [(10, A), (11, B), (5, r), (12, w12), (13, w13)])
    (hBpos : 0 < B.toNat) (halign : r.toNat % 4 = 0)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hd0 : d.toInt ≠ 0) (hsign : n.toInt < 0)
    (hframe0 : ∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R) :
    ∃ c' : Config, Steps c c' ∧ moddi3_post g n d r m0 o c' := by
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hi3, ⟨vm3, hvm3⟩, hL3, hfr3⟩ :=
    core_call_seg (site3_8000474c c.σ c.tick c.steps _ vm hG hpc hvm hwl rfl hi) (by decide)
      hcl hmem hout hL hBpos (by decide)
  have hwl3 : Vsa.Sim.Code.__moddi3Loaded c3.σ.mem := by rw [hmem3, ← hmem]; exact hwl
  have facts : ChainFacts c3.σ.mem c3.σ.mem [(10, A / B), (11, A % B), (5, r)] []
      moddi3NegTailSeg := by
    chain_facts hwl3 with "Vsa.Sim.Code.__moddi3_at_"
    exact jr_tgt_ok r halign
  obtain ⟨c4, res⟩ := segEval_selected_framed moddi3NegTailSeg _ [] 0x80004750#64 vm3
    (fun _ => False) divOverflowKeep [(10, 0#64 - A % B)] c3 hG3 hpc3 hvm3 hL3
    (by show KeysOK [10, 11, 5]; decide) facts (by show ChainOK _ [10, 11, 5] _; decide) hi3
    (fun _ _ => rfl) (by decide) (by decide) ⟨rfl, trivial⟩
  obtain ⟨hq, _⟩ := res.selected_regs
  refine ⟨c4, hs3.trans res.steps, res.good, res.mem_eq.trans hmem3, res.output.trans hout3,
    res.pc.trans (congrArg some (ret_tgt r halign)), res.tick, ?_, _, hq,
    res_neg n d A B hA hB hsign hd0⟩
  intro R hR
  exact (res.reg_frame R (decide_eq_true hR)).trans ((hfr3 R hR).trans (hframe0 R hR))

theorem moddi3_spec (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (moddi3_pre g n d r m0 o) (moddi3_post g n d r m0 o) := by
  intro c hc
  obtain ⟨hG, hwl, hcl, hmem, hout, hpc, hn, hd, hr, ⟨vm, hmi⟩,
    ⟨w12, h12⟩, ⟨w13, h13⟩, htick, hd0, halign, hframeE⟩ := hc
  have held : GHolds c.σ (divIn n d r w12 w13) := ⟨hn, hd, hr, h12, h13, trivial⟩
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  rcases bltz_cases' d with hdlt | hdge
  · have hdtop : 2^63 ≤ d.toNat := bltz_true' d hdlt
    have hBmag : ((0#64) - d).toNat = d.toInt.natAbs := mag_neg_top d hdtop
    rcases bgez_cases' n with hnge | hnlt
    · have hntop : n.toNat < 2^63 := bgez_true' n hnge
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] moddi3PNSeg := by
        chain_facts hwl with "Vsa.Sim.Code.__moddi3_at_"
        exact hdlt
        exact hnge
      obtain ⟨c1, r1⟩ := segEval_selected_framed moddi3PNSeg _ [] _ vm (fun _ => False)
        divOverflowKeep [(10, n), (11, 0#64 - d), (5, r), (12, w12), (13, w13)] c hG hpc hmi held
        (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, congrArg some (addi0 r), rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨cf, hsf, post⟩ := moddi3_fin_pos g n d n (0#64 - d) r w12 w13 m0 o c1 r1.good
        r1.pc r1.minstret r1.tick (m1 ▸ hwl) (m1 ▸ hcl) (m1.trans hmem) (r1.output.trans hout)
        r1.selected_regs (by rw [hBmag]; omega) halign (mag_notop n hntop) hBmag hd0
        (by rw [toInt_of_notop n hntop]; exact Int.natCast_nonneg _) (r1.frameD hframeE)
      exact ⟨cf, r1.steps.trans hsf, post⟩
    · have hntop : 2^63 ≤ n.toNat := bgez_false' n hnlt
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] moddi3NNSeg := by
        chain_facts hwl with "Vsa.Sim.Code.__moddi3_at_"
        exact hdlt
        exact hnlt
      obtain ⟨c1, r1⟩ := segEval_selected_framed moddi3NNSeg _ [] _ vm (fun _ => False)
        divOverflowKeep [(10, 0#64 - n), (11, 0#64 - d), (5, r), (12, w12), (13, w13)] c hG hpc
        hmi held (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, congrArg some (addi0 r), rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨cf, hsf, post⟩ := moddi3_fin_neg g n d (0#64 - n) (0#64 - d) r w12 w13 m0 o c1
        r1.good r1.pc r1.minstret r1.tick (m1 ▸ hwl) (m1 ▸ hcl) (m1.trans hmem)
        (r1.output.trans hout) r1.selected_regs (by rw [hBmag]; omega) halign
        (mag_neg_top n hntop) hBmag hd0
        (by rw [toInt_of_top n hntop]; have := n.isLt; omega) (r1.frameD hframeE)
      exact ⟨cf, r1.steps.trans hsf, post⟩
  · have hdtop : d.toNat < 2^63 := bltz_false' d hdge
    have hBmag : d.toNat = d.toInt.natAbs := mag_notop d hdtop
    rcases bltz_cases' n with hnlt | hnge
    · have hntop : 2^63 ≤ n.toNat := bltz_true' n hnlt
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] moddi3NPSeg := by
        chain_facts hwl with "Vsa.Sim.Code.__moddi3_at_"
        exact hdge
        exact hnlt
      obtain ⟨c1, r1⟩ := segEval_selected_framed moddi3NPSeg _ [] _ vm (fun _ => False)
        divOverflowKeep [(10, 0#64 - n), (11, d), (5, r), (12, w12), (13, w13)] c hG hpc hmi held
        (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, congrArg some (addi0 r), rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨cf, hsf, post⟩ := moddi3_fin_neg g n d (0#64 - n) d r w12 w13 m0 o c1 r1.good
        r1.pc r1.minstret r1.tick (m1 ▸ hwl) (m1 ▸ hcl) (m1.trans hmem) (r1.output.trans hout)
        r1.selected_regs (by rw [hBmag]; omega) halign (mag_neg_top n hntop) hBmag hd0
        (by rw [toInt_of_top n hntop]; have := n.isLt; omega) (r1.frameD hframeE)
      exact ⟨cf, r1.steps.trans hsf, post⟩
    · have hntop : n.toNat < 2^63 := bltz_false' n hnge
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] moddi3PPSeg := by
        chain_facts hwl with "Vsa.Sim.Code.__moddi3_at_"
        exact hdge
        exact hnge
      obtain ⟨c1, r1⟩ := segEval_selected_framed moddi3PPSeg _ [] _ vm (fun _ => False)
        divOverflowKeep [(10, n), (11, d), (5, r), (12, w12), (13, w13)] c hG hpc hmi held
        (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, congrArg some (addi0 r), rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨cf, hsf, post⟩ := moddi3_fin_pos g n d n d r w12 w13 m0 o c1 r1.good
        r1.pc r1.minstret r1.tick (m1 ▸ hwl) (m1 ▸ hcl) (m1.trans hmem) (r1.output.trans hout)
        r1.selected_regs (by rw [hBmag]; omega) halign (mag_notop n hntop) hBmag hd0
        (by rw [toInt_of_notop n hntop]; exact Int.natCast_nonneg _) (r1.frameD hframeE)
      exact ⟨cf, r1.steps.trans hsf, post⟩

def divdi3_pre (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ Vsa.Sim.Code.__divdi3Loaded c.σ.mem ∧ Vsa.Sim.Code.__umoddi3Loaded c.σ.mem ∧
  __hidden___udivdi3Loaded c.σ.mem ∧
  c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧ c.σ.regs.get? Register.PC = some (0x800046a4#64) ∧
  c.σ.regs.get? Register.x10 = some n ∧ c.σ.regs.get? Register.x11 = some d ∧
  c.σ.regs.get? Register.x1 = some r ∧ (∃ v, c.σ.regs.get? Register.minstret = some v) ∧
  (∃ v, c.σ.regs.get? Register.x12 = some v) ∧ (∃ v, c.σ.regs.get? Register.x13 = some v) ∧
  c.tick < 2 ∧ d.toInt ≠ 0 ∧ ¬(n.toInt = -2^63 ∧ d.toInt = -1) ∧ r.toNat % 4 = 0 ∧
  (∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R)

def divdi3_post (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧ c.σ.regs.get? Register.PC = some r ∧
  c.tick < 2 ∧
  (∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R) ∧
  ∃ res, c.σ.regs.get? Register.x10 = some res ∧ res.toInt = n.toInt.tdiv d.toInt

theorem divdi3_mixed_fin (g : (R : Register) → Option (RegisterType R))
    (n d A B r w12 w13 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (c : Config) (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some 0x8000471c#64)
    (hmi : ∃ v, c.σ.regs.get? Register.minstret = some v) (hi : c.tick < 2)
    (hul : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem) (hcl : __hidden___udivdi3Loaded c.σ.mem)
    (hmem : c.σ.mem = m0) (hout : c.σ.sailOutput = o)
    (hL : GHolds c.σ [(10, A), (11, B), (5, r), (12, w12), (13, w13)])
    (hBpos : 0 < B.toNat) (halign : r.toNat % 4 = 0)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hd0 : d.toInt ≠ 0) (hdiff : ¬(0 ≤ n.toInt ↔ 0 ≤ d.toInt))
    (hframe0 : ∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R) :
    ∃ c' : Config, Steps c c' ∧ divdi3_post g n d r m0 o c' := by
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hi3, ⟨vm3, hvm3⟩, hL3, hfr3⟩ :=
    core_call_seg (site3_8000471c c.σ c.tick c.steps _ vm hG hpc hvm hul rfl hi) (by decide)
      hcl hmem hout hL hBpos (by decide)
  have hul3 : Vsa.Sim.Code.__umoddi3Loaded c3.σ.mem := by rw [hmem3, ← hmem]; exact hul
  have facts : ChainFacts c3.σ.mem c3.σ.mem [(10, A / B), (11, A % B), (5, r)] []
      divdi3NegTailSeg := by
    chain_facts hul3 with "Vsa.Sim.Code.__umoddi3_at_"
    exact jr_tgt_ok r halign
  obtain ⟨c4, res⟩ := segEval_selected_framed divdi3NegTailSeg _ [] 0x80004720#64 vm3
    (fun _ => False) divOverflowKeep [(10, 0#64 - A / B)] c3 hG3 hpc3 hvm3 hL3
    (by show KeysOK [10, 11, 5]; decide) facts (by show ChainOK _ [10, 11, 5] _; decide) hi3
    (fun _ _ => rfl) (by decide) (by decide) ⟨rfl, trivial⟩
  obtain ⟨hq, _⟩ := res.selected_regs
  refine ⟨c4, hs3.trans res.steps, res.good, res.mem_eq.trans hmem3, res.output.trans hout3,
    res.pc.trans (congrArg some (ret_tgt r halign)), res.tick, ?_, _, hq,
    res_div_mixed n d A B hA hB hdiff hd0⟩
  intro R hR
  exact (res.reg_frame R (decide_eq_true hR)).trans ((hfr3 R hR).trans (hframe0 R hR))

theorem divdi3_same_tail
    (g : (R : Register) → Option (RegisterType R))
    (n d A B r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (cA : Config)
    (hG : GoodState cA.σ)
    (hcl : __hidden___udivdi3Loaded cA.σ.mem) (hmem : cA.σ.mem = m0)
    (hout : cA.σ.sailOutput = o)
    (hpc : cA.σ.regs.get? Register.PC = some (0x800046ac#64))
    (hx10 : cA.σ.regs.get? Register.x10 = some A)
    (hx11 : cA.σ.regs.get? Register.x11 = some B)
    (hx1 : cA.σ.regs.get? Register.x1 = some r)
    (hx12 : ∃ v, cA.σ.regs.get? Register.x12 = some v)
    (hx13 : ∃ v, cA.σ.regs.get? Register.x13 = some v)
    (hmi : ∃ v, cA.σ.regs.get? Register.minstret = some v)
    (htick : cA.tick < 2) (hBpos : 0 < B.toNat) (halign : r.toNat % 4 = 0)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hd0 : d.toInt ≠ 0) (hsame : 0 ≤ n.toInt ↔ 0 ≤ d.toInt)
    (hnov : (A / B).toNat < 2^63)
    (hframe0 : ∀ R : Register, NotWrittenD R → cA.σ.regs.get? R = g R) :
    ∃ c' : Config, Steps cA c' ∧ divdi3_post g n d r m0 o c' := by
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, _hrem3, _hra3, htick3, hframe3, _hmi3⟩ :=
    core_call_tail_f A B r r m0 o cA hG hcl hmem hout hpc hx10 hx11 hx1 hx12 hx13 hmi htick hBpos halign
  refine ⟨c3, hs3, hG3, hmem3, hout3, hpc3, htick3, ?_, A / B, hq3,
    res_div_same n d A B hA hB hsame hd0 hnov⟩

  intro R hR
  rw [hframe3 R hR.nw]; exact hframe0 R hR

theorem divdi3_spec (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (divdi3_pre g n d r m0 o) (divdi3_post g n d r m0 o) := by
  intro c hc
  obtain ⟨hG, hdl, hul, hcl, hmem, hout, hpc, hn, hd, hr, ⟨vm, hmi⟩,
    ⟨w12, h12⟩, ⟨w13, h13⟩, htick, hd0, hexcl, halign, hframeE⟩ := hc
  have held : GHolds c.σ (divIn n d r w12 w13) := ⟨hn, hd, hr, h12, h13, trivial⟩
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  rcases bltz_cases' n with hnlt | hnge
  · have hntop : 2^63 ≤ n.toNat := bltz_true' n hnlt
    have hnneg : n.toInt < 0 := by rw [toInt_of_top n hntop]; have := n.isLt; omega
    have hAmag : ((0#64) - n).toNat = n.toInt.natAbs := mag_neg_top n hntop
    have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] divOverflowBranchSeg := by
      chain_facts hdl with "Vsa.Sim.Code.__divdi3_at_"
      exact hnlt
    obtain ⟨c1, r1⟩ := segEval_selected_framed divOverflowBranchSeg _ [] _ vm (fun _ => False)
      divOverflowKeep (divIn n d r w12 w13) c hG hpc hmi held
      (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
      (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
      (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
    have m1 := r1.mem_eq
    obtain ⟨vm1, hvm1⟩ := r1.minstret
    have hul1 : Vsa.Sim.Code.__umoddi3Loaded c1.σ.mem := m1 ▸ hul
    rcases bgtz_cases' d with hdgt | hdle
    · have hdpos : 0 < d.toInt := bgtz_true' d hdgt
      have hdtop : d.toNat < 2^63 := by
        by_cases hc' : d.toNat < 2^63
        · exact hc'
        · rw [toInt_of_top d (by omega)] at hdpos; have := d.isLt; omega
      have hBmag : d.toNat = d.toInt.natAbs := mag_notop d hdtop
      have f2 : ChainFacts c1.σ.mem c1.σ.mem (divIn n d r w12 w13) [] divdi3NegPosSeg := by
        chain_facts hul1 with "Vsa.Sim.Code.__umoddi3_at_"
        exact hdgt
      obtain ⟨c2, r2⟩ := segEval_selected_framed divdi3NegPosSeg _ [] 0x80004704#64 vm1
        (fun _ => False) divOverflowKeep [(10, 0#64 - n), (11, d), (5, r), (12, w12), (13, w13)]
        c1 r1.good r1.pc hvm1 r1.selected_regs (by show KeysOK [10, 11, 1, 12, 13]; decide) f2
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) r1.tick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, congrArg some (addi0 r), rfl, rfl, trivial⟩
      have m2 := r2.mem_eq.trans m1
      obtain ⟨cf, hsf, post⟩ := divdi3_mixed_fin g n d (0#64 - n) d r w12 w13 m0 o c2 r2.good
        r2.pc r2.minstret r2.tick (m2 ▸ hul) (m2 ▸ hcl) (m2.trans hmem)
        (r2.output.trans (r1.output.trans hout)) r2.selected_regs (by rw [hBmag]; omega) halign
        hAmag hBmag hd0 (fun hi => absurd (hi.mpr (Int.le_of_lt hdpos)) (by omega))
        (r2.frameD (r1.frameD hframeE))
      exact ⟨cf, r1.steps.trans (r2.steps.trans hsf), post⟩
    · have hdle' : d.toInt ≤ 0 := bgtz_false' d hdle
      have hdneg : d.toInt < 0 := by omega
      have hdtop : 2^63 ≤ d.toNat := by
        by_cases hc' : d.toNat < 2^63
        · rw [toInt_of_notop d hc'] at hdneg; have := d.isLt; omega
        · omega
      have hBmag : ((0#64) - d).toNat = d.toInt.natAbs := mag_neg_top d hdtop
      have hsame : (0 ≤ n.toInt ↔ 0 ≤ d.toInt) :=
        ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
      have f2 : ChainFacts c1.σ.mem c1.σ.mem (divIn n d r w12 w13) [] divdi3NegNegSeg := by
        chain_facts hul1 with "Vsa.Sim.Code.__umoddi3_at_"
        exact hdle
      obtain ⟨c2, r2⟩ := segEval_selected_framed divdi3NegNegSeg _ [] 0x80004704#64 vm1
        (fun _ => False) divOverflowKeep (divIn (0#64 - n) (0#64 - d) r w12 w13)
        c1 r1.good r1.pc hvm1 r1.selected_regs (by show KeysOK [10, 11, 1, 12, 13]; decide) f2
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) r1.tick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
      have m2 := r2.mem_eq.trans m1
      obtain ⟨x10, x11, x1, x12, x13, _⟩ := r2.selected_regs
      obtain ⟨cf, hsf, post⟩ := divdi3_same_tail g n d (0#64 - n) (0#64 - d) r m0 o c2 r2.good
        (m2 ▸ hcl) (m2.trans hmem) (r2.output.trans (r1.output.trans hout)) r2.pc x10 x11 x1
        ⟨w12, x12⟩ ⟨w13, x13⟩ r2.minstret r2.tick (by rw [hBmag]; omega) halign hAmag hBmag hd0
        hsame (udiv_lt_of_not_overflow n d _ _ hAmag hBmag hsame hd0 hexcl)
        (r2.frameD (r1.frameD hframeE))
      exact ⟨cf, r1.steps.trans (r2.steps.trans hsf), post⟩
  · have hntop : n.toNat < 2^63 := bltz_false' n hnge
    have hnInt : 0 ≤ n.toInt := by rw [toInt_of_notop n hntop]; exact Int.natCast_nonneg _
    have hAmag : n.toNat = n.toInt.natAbs := mag_notop n hntop
    rcases bltz_cases' d with hdlt | hdge
    · have hdtop : 2^63 ≤ d.toNat := bltz_true' d hdlt
      have hdneg : d.toInt < 0 := by rw [toInt_of_top d hdtop]; have := d.isLt; omega
      have hBmag : ((0#64) - d).toNat = d.toInt.natAbs := mag_neg_top d hdtop
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] divdi3PosNegSeg := by
        chain_facts hdl with "Vsa.Sim.Code.__divdi3_at_"
        exact hnge
        exact hdlt
      obtain ⟨c1, r1⟩ := segEval_selected_framed divdi3PosNegSeg _ [] _ vm (fun _ => False)
        divOverflowKeep (divIn n d r w12 w13) c hG hpc hmi held
        (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨vm1, hvm1⟩ := r1.minstret
      have f2 : ChainFacts c1.σ.mem c1.σ.mem (divIn n d r w12 w13) [] divdi3PosNegSeg2 := by
        chain_facts (m1 ▸ hul : Vsa.Sim.Code.__umoddi3Loaded c1.σ.mem)
          with "Vsa.Sim.Code.__umoddi3_at_"
      obtain ⟨c2, r2⟩ := segEval_selected_framed divdi3PosNegSeg2 _ [] 0x80004714#64 vm1
        (fun _ => False) divOverflowKeep [(10, n), (11, 0#64 - d), (5, r), (12, w12), (13, w13)]
        c1 r1.good r1.pc hvm1 r1.selected_regs (by show KeysOK [10, 11, 1, 12, 13]; decide) f2
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) r1.tick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, congrArg some (addi0 r), rfl, rfl, trivial⟩
      have m2 := r2.mem_eq.trans m1
      obtain ⟨cf, hsf, post⟩ := divdi3_mixed_fin g n d n (0#64 - d) r w12 w13 m0 o c2 r2.good
        r2.pc r2.minstret r2.tick (m2 ▸ hul) (m2 ▸ hcl) (m2.trans hmem)
        (r2.output.trans (r1.output.trans hout)) r2.selected_regs (by rw [hBmag]; omega) halign
        hAmag hBmag hd0 (fun hi => absurd (hi.mp hnInt) (by omega))
        (r2.frameD (r1.frameD hframeE))
      exact ⟨cf, r1.steps.trans (r2.steps.trans hsf), post⟩
    · have hdtop : d.toNat < 2^63 := bltz_false' d hdge
      have hdInt : 0 ≤ d.toInt := by rw [toInt_of_notop d hdtop]; exact Int.natCast_nonneg _
      have hBmag : d.toNat = d.toInt.natAbs := mag_notop d hdtop
      have hsame : (0 ≤ n.toInt ↔ 0 ≤ d.toInt) := ⟨fun _ => hdInt, fun _ => hnInt⟩
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] divdi3PosSeg := by
        chain_facts hdl with "Vsa.Sim.Code.__divdi3_at_"
        exact hnge
        exact hdge
      obtain ⟨c1, r1⟩ := segEval_selected_framed divdi3PosSeg _ [] _ vm (fun _ => False)
        divOverflowKeep (divIn n d r w12 w13) c hG hpc hmi held
        (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨x10, x11, x1, x12, x13, _⟩ := r1.selected_regs
      obtain ⟨cf, hsf, post⟩ := divdi3_same_tail g n d n d r m0 o c1 r1.good
        (m1 ▸ hcl) (m1.trans hmem) (r1.output.trans hout) r1.pc x10 x11 x1
        ⟨w12, x12⟩ ⟨w13, x13⟩ r1.minstret r1.tick (by rw [hBmag]; omega) halign hAmag hBmag hd0
        hsame (udiv_lt_of_not_overflow n d _ _ hAmag hBmag hsame hd0 hexcl) (r1.frameD hframeE)
      exact ⟨cf, r1.steps.trans hsf, post⟩

end Vsa.Sim
