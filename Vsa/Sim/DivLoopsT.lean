import Vsa.Sim.DivT

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps RunT)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem norm_loopT (d n neg1 r : BitVec 64) (hd : 0 < d.toNat) :
    ∀ (M : Nat) (a2 a3 : BitVec 64), 2^64 - a2.toNat ≤ M → NrmK d a2 a3 →
    ∃ (a2f a3f : BitVec 64) (τ : List (BitVec 64)), NrmK d a2f a3f ∧ n.toNat < 2 * a2f.toNat ∧
      ∀ g m0 o, TripleT τ (Ust g (0x800046c4#64) neg1 n a2 a3 r m0 o)
        (Ust g (0x800046d4#64) neg1 n a2f a3f r m0 o) := by
  intro M
  induction M with
  | zero =>
    intro a2 a3 hM _
    have := a2.isLt
    omega
  | succ M ih =>
    intro a2 a3 hM hK
    obtain ⟨k, hk2, hk3, hkbnd⟩ := hK
    have ha2pos : 0 < a2.toNat := by rw [hk2]; exact Nat.mul_pos hd (Nat.two_pow_pos k)
    have ha2ne : a2 ≠ 0#64 := by intro h; rw [h] at ha2pos; simp at ha2pos
    rcases blez_cases a2 with hblez | hblez
    · have htop : 2^63 ≤ a2.toNat := toInt_nonpos_top a2 (blez_true a2 hblez) ha2ne
      have hnlt : n.toNat < 2^64 := n.isLt
      exact ⟨a2, a3, _, ⟨k, hk2, hk3, hkbnd⟩, by omega,
        fun g m0 o => utrT_c4_d4 g neg1 n a2 a3 r m0 o hblez⟩
    · have hnotop : 2 * a2.toNat < 2^64 := toInt_pos_notop a2 (blez_false a2 hblez)
      have hpk : (2:Nat)^(k+1) = 2 * 2^k := by rw [Nat.pow_succ, Nat.mul_comm]
      have hdd : d.toNat * 2^(k+1) = 2 * (d.toNat * 2^k) := by
        rw [hpk, Nat.mul_left_comm]
      have hd2 : (a2 <<< (1:Nat)).toNat = d.toNat * 2^(k+1) := by
        rw [shl_double a2 hnotop, hk2, hdd]
      have hd3 : (a3 <<< (1:Nat)).toNat = 2^(k+1) := by
        have hh : 2 * a3.toNat < 2^64 := by
          rw [hk3]
          have hle : 2^k ≤ d.toNat * 2^k := Nat.le_mul_of_pos_left _ hd
          omega
        rw [shl_double a3 hh, hk3, hpk]
      have hbnd2 : d.toNat * 2^(k+1) < 2^64 := by
        rw [hdd, ← hk2]; exact hnotop
      have pre : ∀ g m0 o, TripleT (pcsC udivBlezNSeg ++ pcsC udivSlliA2Seg ++ pcsC udivSlliA3Seg)
          (Ust g (0x800046c4#64) neg1 n a2 a3 r m0 o)
          (Ust g (0x800046d0#64) neg1 n (a2 <<< (1:Nat)) (a3 <<< (1:Nat)) r m0 o) :=
        fun g m0 o => ((utrT_c4_c8 g neg1 n a2 a3 r m0 o hblez).seq
          (utrT_c8_cc g neg1 n a2 a3 r m0 o)).seq (utrT_cc_d0 g neg1 n (a2 <<< (1:Nat)) a3 r m0 o)
      rcases bltu_cases (a2 <<< (1:Nat)) n with hbltu | hbltu
      · have hlt := normMeasure_lt a2 ha2pos hnotop
        obtain ⟨a2f, a3f, τ, hK', hlt', hT⟩ := ih (a2 <<< (1:Nat)) (a3 <<< (1:Nat)) (by omega)
          ⟨k + 1, hd2, hd3, hbnd2⟩
        exact ⟨a2f, a3f, _, hK', hlt', fun g m0 o => ((pre g m0 o).seq
          (utrT_d0_c4 g neg1 n (a2 <<< (1:Nat)) (a3 <<< (1:Nat)) r m0 o hbltu)).seq (hT g m0 o)⟩
      · have hge : n.toNat ≤ (a2 <<< (1:Nat)).toNat := bltu_false (a2 <<< (1:Nat)) n hbltu
        have : 0 < (a2 <<< (1:Nat)).toNat := by rw [hd2]; exact Nat.mul_pos hd (Nat.two_pow_pos _)
        exact ⟨_, _, _, ⟨k + 1, hd2, hd3, hbnd2⟩, by omega, fun g m0 o => (pre g m0 o).seq
          (utrT_d0_d4 g neg1 n (a2 <<< (1:Nat)) (a3 <<< (1:Nat)) r m0 o hbltu)⟩

theorem entry_normT (d n neg1 r : BitVec 64) (hd : 0 < d.toNat) :
    ∃ (a2f a3f : BitVec 64) (τ : List (BitVec 64)), NrmK d a2f a3f ∧ n.toNat < 2 * a2f.toNat ∧
      ∀ g m0 o, TripleT τ (Ust g (0x800046c0#64) neg1 n d (1#64) r m0 o)
        (Ust g (0x800046d4#64) neg1 n a2f a3f r m0 o) := by
  have hK : NrmK d d (1#64) := by
    refine ⟨0, ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa using d.isLt
  rcases bgeu_cases d n with hb | hb
  · have hge : n.toNat ≤ d.toNat := bgeu_true d n hb
    exact ⟨d, 1#64, _, hK, by omega, fun g m0 o => utrT_c0_d4 g neg1 n d (1#64) r m0 o hb⟩
  · obtain ⟨a2f, a3f, τ, hK', hlt, hT⟩ := norm_loopT d n neg1 r hd _ d (1#64) (Nat.le_refl _) hK
    exact ⟨a2f, a3f, _, hK', hlt, fun g m0 o =>
      (utrT_c0_c4 g neg1 n d (1#64) r m0 o hb).seq (hT g m0 o)⟩

theorem div_loopT (d n r : BitVec 64) (hd : 0 < d.toNat) :
    ∀ (j : Nat) (a0 a1 a2 a3 : BitVec 64), DivK d a2 a3 j → a0.toNat % 2^(j+1) = 0 →
      n.toNat = d.toNat * a0.toNat + a1.toNat → a1.toNat < 2 * a2.toNat →
    ∃ (b0 b1 b2 b3 : BitVec 64) (τ : List (BitVec 64)),
      b0.toNat = n.toNat / d.toNat ∧ b1.toNat = n.toNat % d.toNat ∧
      ∀ g m0 o, TripleT τ (Ust g (0x800046d8#64) a0 a1 a2 a3 r m0 o)
        (Ust g (0x800046f0#64) b0 b1 b2 b3 r m0 o) := by
  intro j
  induction j with
  | zero =>
    intro a0 a1 a2 a3 hK hmod hprog hbound
    obtain ⟨hk2, hk3, hkbnd⟩ := hK
    have hk2' : a2.toNat = d.toNat := by simpa using hk2
    have hbound' : a1.toNat < 2 * d.toNat := by rw [hk2'] at hbound; exact hbound
    have ha3half0 : (a3 >>> (1:Nat)) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [a3_half a3 0 hk3]; decide
    have hbnz : ((a3 >>> (1:Nat)) != (0#64)) = false := by rw [ha3half0]; rfl
    rcases bltu_cases a1 a2 with hbltu | hbltu
    · have ha1lt : a1.toNat < d.toNat := by have := bltu_true a1 a2 hbltu; rw [hk2'] at this; exact this
      have hdm : n.toNat / d.toNat = a0.toNat ∧ n.toNat % d.toNat = a1.toNat := by
        rw [Nat.div_mod_unique hd]; exact ⟨by omega, ha1lt⟩
      exact ⟨a0, a1, _, _, _, hdm.1.symm, hdm.2.symm, fun g m0 o =>
        (((utrT_d8_e4 g a0 a1 a2 a3 r m0 o hbltu).seq (utrT_e4_e8 g a0 a1 a2 a3 r m0 o)).seq
          (utrT_e8_ec g a0 a1 a2 (a3 >>> (1:Nat)) r m0 o)).seq
          (utrT_ec_f0 g a0 a1 (a2 >>> (1:Nat)) (a3 >>> (1:Nat)) r m0 o hbnz)⟩
    · have hge : a2.toNat ≤ a1.toNat := bltu_false a1 a2 hbltu
      have ha2le : a2 ≤ a1 := BitVec.le_def.mpr hge
      have ha1sub : (a1 - a2).toNat = a1.toNat - a2.toNat := BitVec.toNat_sub_of_le ha2le
      have hora0 : (a0 ||| a3).toNat = a0.toNat + 1 := by
        have := or_a3_toNat a0 a3 0 hk3 hmod
        simpa using this
      have ha1'lt : (a1 - a2).toNat < d.toNat := by rw [ha1sub, hk2']; omega
      have hdm : n.toNat / d.toNat = (a0 ||| a3).toNat ∧ n.toNat % d.toNat = (a1 - a2).toNat := by
        rw [Nat.div_mod_unique hd]
        refine ⟨?_, ha1'lt⟩
        rw [hora0, ha1sub, hk2']; rw [Nat.mul_add]; omega
      exact ⟨_, _, _, _, _, hdm.1.symm, hdm.2.symm, fun g m0 o =>
        (((((utrT_d8_dc g a0 a1 a2 a3 r m0 o hbltu).seq (utrT_dc_e0 g a0 a1 a2 a3 r m0 o)).seq
          (utrT_e0_e4 g a0 (a1 - a2) a2 a3 r m0 o)).seq
          (utrT_e4_e8 g (a0 ||| a3) (a1 - a2) a2 a3 r m0 o)).seq
          (utrT_e8_ec g (a0 ||| a3) (a1 - a2) a2 (a3 >>> (1:Nat)) r m0 o)).seq
          (utrT_ec_f0 g (a0 ||| a3) (a1 - a2) (a2 >>> (1:Nat)) (a3 >>> (1:Nat)) r m0 o hbnz)⟩
  | succ j ih =>
    intro a0 a1 a2 a3 hK hmod hprog hbound
    obtain ⟨hk2, hk3, hkbnd⟩ := hK
    have hj1 : 1 ≤ j + 1 := by omega
    have ha3half : (a3 >>> (1:Nat)).toNat = 2^j := by
      rw [a3_half a3 (j + 1) hk3, half_pow (j + 1) hj1]; rfl
    have ha2half : (a2 >>> (1:Nat)).toNat = d.toNat * 2^j := a2_half d a2 (j + 1) hj1 hk2
    have ha3half_ne : (a3 >>> (1:Nat)) ≠ 0#64 := by
      intro h; rw [h] at ha3half
      have hz : (0#64 : BitVec 64).toNat = 0 := by decide
      rw [hz] at ha3half
      have := Nat.two_pow_pos j; omega
    have hbnz : ((a3 >>> (1:Nat)) != (0#64)) = true := by rw [bne_iff_ne]; exact ha3half_ne
    have hkbnd' : d.toNat * 2^j < 2^64 := by
      have hle : d.toNat * 2^j ≤ d.toNat * 2^(j + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
      omega
    rcases bltu_cases a1 a2 with hbltu | hbltu
    · have ha1lt : a1.toNat < a2.toNat := bltu_true a1 a2 hbltu
      obtain ⟨b0, b1, b2, b3, τ, h0, h1, hT⟩ := ih a0 a1 (a2 >>> (1:Nat)) (a3 >>> (1:Nat))
        ⟨ha2half, ha3half, hkbnd'⟩ (mod_drop_pow a0.toNat (j + 1) hmod) hprog
        (by rw [ha2half, show 2 * (d.toNat * 2 ^ j) = d.toNat * 2 ^ (j + 1) from two_mul_pow_pred d.toNat (j + 1) hj1, ← hk2]; exact ha1lt)
      exact ⟨b0, b1, b2, b3, _, h0, h1, fun g m0 o =>
        ((((utrT_d8_e4 g a0 a1 a2 a3 r m0 o hbltu).seq (utrT_e4_e8 g a0 a1 a2 a3 r m0 o)).seq
          (utrT_e8_ec g a0 a1 a2 (a3 >>> (1:Nat)) r m0 o)).seq
          (utrT_ec_d8 g a0 a1 (a2 >>> (1:Nat)) (a3 >>> (1:Nat)) r m0 o hbnz)).seq (hT g m0 o)⟩
    · have hge : a2.toNat ≤ a1.toNat := bltu_false a1 a2 hbltu
      have ha2le : a2 ≤ a1 := BitVec.le_def.mpr hge
      have ha1sub : (a1 - a2).toNat = a1.toNat - a2.toNat := BitVec.toNat_sub_of_le ha2le
      have hora0 : (a0 ||| a3).toNat = a0.toNat + 2^(j + 1) := or_a3_toNat a0 a3 (j + 1) hk3 hmod
      obtain ⟨b0, b1, b2, b3, τ, h0, h1, hT⟩ := ih (a0 ||| a3) (a1 - a2) (a2 >>> (1:Nat))
        (a3 >>> (1:Nat)) ⟨ha2half, ha3half, hkbnd'⟩
        (by rw [hora0]; exact mod_add_pow a0.toNat (j + 1) hmod)
        (by rw [hora0, ha1sub, Nat.mul_add, hk2]; rw [hk2] at hge; omega)
        (by rw [ha2half, show 2 * (d.toNat * 2 ^ j) = d.toNat * 2 ^ (j + 1) from two_mul_pow_pred d.toNat (j + 1) hj1, ← hk2, ha1sub]; omega)
      exact ⟨b0, b1, b2, b3, _, h0, h1, fun g m0 o =>
        ((((((utrT_d8_dc g a0 a1 a2 a3 r m0 o hbltu).seq (utrT_dc_e0 g a0 a1 a2 a3 r m0 o)).seq
          (utrT_e0_e4 g a0 (a1 - a2) a2 a3 r m0 o)).seq
          (utrT_e4_e8 g (a0 ||| a3) (a1 - a2) a2 a3 r m0 o)).seq
          (utrT_e8_ec g (a0 ||| a3) (a1 - a2) a2 (a3 >>> (1:Nat)) r m0 o)).seq
          (utrT_ec_d8 g (a0 ||| a3) (a1 - a2) (a2 >>> (1:Nat)) (a3 >>> (1:Nat)) r m0 o hbnz)).seq
          (hT g m0 o)⟩

theorem one_cT : ((0#64) + sign_extend (m := 64) (0x001#12) : BitVec 64) = (1#64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem udivdi3_specT (n d r : BitVec 64) (hd : 0 < d.toNat) (halign : r.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ g m0 o, TripleT τ
      (fun c => ∃ a2old a3old, Ust g (0x800046ac#64) n d a2old a3old r m0 o c)
      (udivdi3_post g n d r m0 o) := by
  obtain ⟨a2f, a3f, τn, ⟨K, hk2, hk3, hkbnd⟩, hn2a2, hTn⟩ :=
    entry_normT d n ((0#64) + sign_extend (m := 64) (0xfff#12)) r hd
  obtain ⟨b0, b1, b2, b3, τd, hq, hr, hTd⟩ := div_loopT d n r hd K (0#64) n a2f a3f
    ⟨hk2, hk3, hkbnd⟩ (by simp) (by simp) hn2a2
  refine ⟨pcsC udivEntrySeg ++ τn ++ pcsC udivLiSeg ++ τd ++ pcsC udivRetSeg, fun g m0 o => ?_⟩
  have hpre : TripleT (pcsC udivEntrySeg)
      (fun c => ∃ a2old a3old, Ust g (0x800046ac#64) n d a2old a3old r m0 o c)
      (Ust g (0x800046c0#64) ((0#64) + sign_extend (m := 64) (0xfff#12)) n d (1#64) r m0 o) := by
    intro c hc
    obtain ⟨a2old, a3old, hSt⟩ := hc
    obtain ⟨vm, hmi⟩ := hSt.minstret
    have hbeq : (d == (0#64)) = false := by
      have hne : d ≠ 0#64 := by intro h; rw [h] at hd; simp at hd
      simpa using hne
    have facts : ChainFacts c.σ.mem c.σ.mem (mulRegs n d a2old a3old r) [] udivEntrySeg := by
      chain_facts hSt.loaded
      show (d + sign_extend (m := 64) (0x000#12) == 0#64) = false
      rw [sext_zero, BitVec.add_zero]; exact hbeq
    obtain ⟨c', res, hrun⟩ := segEval_selected_framedT udivEntrySeg _ [] _ vm (fun _ => False) mulKeep
      (mulRegs ((0#64) + sign_extend (m := 64) (0xfff#12)) n d (1#64) r) c hSt.good hSt.pc hmi hSt.held
      (by show KeysOK [10, 11, 12, 13, 1]; decide) facts
      (by show ChainOK _ [10, 11, 12, 13, 1] _; decide) hSt.tick (fun _ _ => rfl) (by decide)
      (by decide) ⟨rfl, congrArg some (show n + sign_extend (m := 64) (0x000#12) = n by
        rw [sext_zero]; exact BitVec.add_zero n), congrArg some (show d + sign_extend (m := 64) (0x000#12) = d by
        rw [sext_zero]; exact BitVec.add_zero d), congrArg some one_cT, rfl, trivial⟩
    exact ⟨c', hrun, hSt.of_seg res rfl⟩
  have hret : TripleT (pcsC udivRetSeg) (Ust g (0x800046f0#64) b0 b1 b2 b3 r m0 o)
      (udivdi3_post g n d r m0 o) := by
    intro c hSt
    obtain ⟨vm, hmi⟩ := hSt.minstret
    have facts : ChainFacts c.σ.mem c.σ.mem (mulRegs b0 b1 b2 b3 r) [] udivRetSeg := by
      chain_facts hSt.loaded
      exact ret_tgt_aligned r halign
    obtain ⟨c', res, hrun⟩ := segEval_selected_framedT udivRetSeg _ [] _ vm (fun _ => False) mulKeep
      (mulRegs b0 b1 b2 b3 r) c hSt.good hSt.pc hmi hSt.held
      (by show KeysOK [10, 11, 12, 13, 1]; decide) facts
      (by show ChainOK _ [10, 11, 12, 13, 1] _; decide) hSt.tick (fun _ _ => rfl) (by decide)
      (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
    have ha0eq : b0 = n / d := by apply BitVec.eq_of_toNat_eq; rw [hq, BitVec.toNat_udiv]
    have ha1eq : b1 = n % d := by apply BitVec.eq_of_toNat_eq; rw [hr, BitVec.toNat_umod]
    obtain ⟨h0, h1, h2, h3, hra, _⟩ := res.selected_regs
    exact ⟨c', hrun, res.good, res.mem_eq.trans hSt.mem, res.output.trans hSt.sailOut,
      res.pc.trans (congrArg some (ret_tgt r halign)), ha0eq ▸ h0, ha1eq ▸ h1, hra, res.tick,
      fun R hR => (res.reg_frame R (decide_eq_true hR)).trans (hSt.hframe R hR), ⟨b2, h2⟩, ⟨b3, h3⟩⟩
  exact (((hpre.seq (hTn g m0 o)).seq (utrT_d4_d8 g _ n a2f a3f r m0 o)).seq (hTd g m0 o)).seq hret

end Vsa.Sim
