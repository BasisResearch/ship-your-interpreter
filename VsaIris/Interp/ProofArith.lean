import VsaIris.Interp.HelperRun
import VsaIris.Interp.BinArm
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.DivSpec3
import VsaIris.Interp.SymInterp
import VsaIris.Interp.ArithRun

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.MemRepr

theorem mul_step (acc a2 a1 : BitVec 64) :
    acc + a2 * a1 = (if a1 &&& 1#64 = 0#64 then acc else acc + a2) + (a2 <<< 1) * (a1 >>> 1) := by
  rw [Vsa.Sim.invmul_bv a2 a1]
  split
  · rename_i h; rw [h]; simp
  · rename_i h
    have hm : (a1 &&& 1#64).toNat = a1.toNat % 2 := by
      rw [BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
    have : a1 &&& 1#64 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      have h3 : (a1 &&& 1#64).toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq (by simpa using h0))
      rw [hm] at h3 ⊢; show a1.toNat % 2 = 1; omega
    rw [this]; simp; rw [BitVec.add_assoc, BitVec.add_comm a2]

abbrev MulKeep (R R0 : Nat → BitVec 64) : Prop := ∀ z, z ≠ 10 → z ≠ 11 → z ≠ 12 → z ≠ 13 → R z = R0 z

theorem mul_loop {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (x y r : BitVec 64) (R0 : Nat → BitVec 64)
    (Mt : Mem) (hal : r.toNat % 4 = 0) (hr : R0 1 = r)
    (hk : ∀ R', R' 10 = x * y → MulKeep R' R0 → IW live Dt DA S Q r R' Mt) :
    ∀ n (R : Nat → BitVec 64), (R 11).toNat = n → R 10 + R 12 * R 11 = x * y → MulKeep R R0 →
      IW live Dt DA S Q 0x80004648#64 R Mt := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih R hn hinv hkp
  have h1 : R 1 = r := (hkp 1 (by decide) (by decide) (by decide) (by decide)).trans hr
  apply (step% it 0x80004648) hlive
  sym_run hlive at 0x80004648
  all_goals first
    | (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h1]; exact hal)
    | skip
  case hT.hT hb hz =>
    refine ih _ ?_ _ rfl ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hz ⊢
      rw [← hn]; exact Vsa.Sim.shr_lt _ (fun h0 => hz (by rw [h0]; rfl))
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [← hinv, mul_step (R 10) (R 12) (R 11)]; simp [hb]
    · intro z h10 h11 h12 h13
      simp only [upd_apply, h11, h12, h13, ite_false]; exact hkp z h10 h11 h12 h13
  case hF.hT hb hz =>
    refine ih _ ?_ _ rfl ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hz ⊢
      rw [← hn]; exact Vsa.Sim.shr_lt _ (fun h0 => hz (by rw [h0]; rfl))
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [← hinv, mul_step (R 10) (R 12) (R 11)]; simp [hb]
    · intro z h10 h11 h12 h13
      simp only [upd_apply, h10, h11, h12, h13, ite_false]; exact hkp z h10 h11 h12 h13
  case hT.hF.hk hb hz =>
    rw [h1]
    refine hk _ ?_ (fun z h10 h11 h12 h13 => ?_)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      have hz0 : R 11 >>> 1 = 0#64 := by simpa using hz
      rw [← hinv, mul_step (R 10) (R 12) (R 11), hz0]; simp [hb]
    · simp only [upd_apply, h11, h12, h13, ite_false]; exact hkp z h10 h11 h12 h13
  case hF.hF.hk hb hz =>
    rw [h1]
    refine hk _ ?_ (fun z h10 h11 h12 h13 => ?_)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      have hz0 : R 11 >>> 1 = 0#64 := by simpa using hz
      rw [← hinv, mul_step (R 10) (R 12) (R 11), hz0]; simp [hb]
    · simp only [upd_apply, h10, h11, h12, h13, ite_false]; exact hkp z h10 h11 h12 h13

theorem mul_iw {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (x y r : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (h10 : R 10 = x) (h11 : R 11 = y) (hr : R 1 = r) (hal : r.toNat % 4 = 0)
    (hk : ∀ R', R' 10 = x * y → MulKeep R' R → IW live Dt DA S Q r R' Mt) :
    IW live Dt DA S Q 0x80004640#64 R Mt := by
  apply (step% it 0x80004640) hlive
  apply (step% it 0x80004644) hlive
  refine mul_loop hlive x y r R Mt hal hr hk _ _ rfl ?_ ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h10, h11]; simp
  · intro z h10' h11' h12 h13
    simp only [upd_apply, h10', h12, ite_false]

theorem udiv_iw {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (n d r : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (hd : d ≠ 0#64) (h10 : R 10 = n) (h11 : R 11 = d) (hr : R 1 = r)
    (hal : r.toNat % 4 = 0)
    (hk : ∀ R', (R' 10).toNat = n.toNat / d.toNat → (R' 11).toNat = n.toNat % d.toNat →
      DivKeep R' R → IW live Dt DA S Q r R' Mt) :
    IW live Dt DA S Q 0x800046ac#64 R Mt :=
  swp_host_out (fun p hp => List.mem_append_left _ (arith_interp p hp))
    (udivH (fun p hp => hlive _ (arith_interp p hp)) n d r R Mt hd h10 h11 hr hal
      fun R' h1 h2 h3 => swp_host_in (hk R' h1 h2 h3))

theorem iw_jal {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {pc : BitVec 64} {R : Nat → BitVec 64}
    {Mt : Mem} (i : Nat) (code : List (BitVec 8)) (tgt : BitVec 64)
    (hexec : JalExec (vsaModel live) i code tgt)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText) (hpc : pc = BitVec.ofNat 64 i)
    (hk : IW live Dt DA S Q tgt (upd R 1 (BitVec.ofNat 64 (i + 4))) Mt) :
    IW live Dt DA S Q pc R Mt :=
  swp_jal i code tgt hexec (fun p hp => List.mem_append_left _ (hcode p hp)) (by decide) (by decide)
    hpc hk

theorem toNat_lt_of_toInt_nonneg {x : BitVec 64} (h : 0 ≤ x.toInt) : x.toNat < 2 ^ 63 := by
  rw [BitVec.toInt_eq_toNat_cond] at h; split at h <;> omega
theorem toNat_ge_of_toInt_neg {x : BitVec 64} (h : x.toInt < 0) : 2 ^ 63 ≤ x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at h; split at h <;> omega

theorem wrap_of_eq' {q : BitVec 64} {z : Int} (h : q.toInt = z) : q.toInt = Vsa.While.wrap64 z := by
  rw [← h, Vsa.While.wrap64_toInt]

theorem sdiv_nn (x y : BitVec 64) (hx : 0 ≤ x.toInt) (hy : 0 < y.toInt) :
    (x / y).toInt = Vsa.While.wrap64 (x.toInt.tdiv y.toInt) := by
  have hA := Vsa.Sim.mag_notop x (toNat_lt_of_toInt_nonneg hx)
  have hB := Vsa.Sim.mag_notop y (toNat_lt_of_toInt_nonneg (by omega))
  exact wrap_of_eq' (Vsa.Sim.res_div_same x y x y hA hB (by omega) (by omega)
    (Vsa.Sim.udiv_lt_of_not_overflow x y x y hA hB (by omega) (by omega) (by omega)))

theorem sdiv_mn (x y : BitVec 64) (hx : x.toInt < 0) (hy : 0 < y.toInt) :
    (0#64 - (0#64 - x) / y).toInt = Vsa.While.wrap64 (x.toInt.tdiv y.toInt) := by
  have hA := Vsa.Sim.mag_neg_top x (toNat_ge_of_toInt_neg hx)
  have hB := Vsa.Sim.mag_notop y (toNat_lt_of_toInt_nonneg (by omega))
  exact wrap_of_eq' (Vsa.Sim.res_div_mixed x y (0#64 - x) y hA hB (by omega) (by omega))

theorem sdiv_nm (x y : BitVec 64) (hx : 0 ≤ x.toInt) (hy : y.toInt < 0) :
    (0#64 - x / (0#64 - y)).toInt = Vsa.While.wrap64 (x.toInt.tdiv y.toInt) := by
  have hA := Vsa.Sim.mag_notop x (toNat_lt_of_toInt_nonneg hx)
  have hB := Vsa.Sim.mag_neg_top y (toNat_ge_of_toInt_neg hy)
  exact wrap_of_eq' (Vsa.Sim.res_div_mixed x y x (0#64 - y) hA hB (by omega) (by omega))

theorem sdiv_mm (x y : BitVec 64) (hx : x.toInt < 0) (hy : y.toInt < 0) :
    ((0#64 - x) / (0#64 - y)).toInt = Vsa.While.wrap64 (x.toInt.tdiv y.toInt) := by
  have hA := Vsa.Sim.mag_neg_top x (toNat_ge_of_toInt_neg hx)
  have hB := Vsa.Sim.mag_neg_top y (toNat_ge_of_toInt_neg hy)
  by_cases hov : x.toInt = -2^63 ∧ y.toInt = -1
  · obtain ⟨h1, h2⟩ := hov
    have ex : x = 0x8000000000000000#64 := BitVec.eq_of_toInt_eq (by rw [h1]; decide)
    have ey : y = 0xffffffffffffffff#64 := BitVec.eq_of_toInt_eq (by rw [h2]; decide)
    rw [h1, h2, Vsa.While.wrap64_tdiv_min, ex, ey]; decide
  · exact wrap_of_eq' (Vsa.Sim.res_div_same x y (0#64 - x) (0#64 - y) hA hB (by omega) (by omega)
      (Vsa.Sim.udiv_lt_of_not_overflow x y _ _ hA hB (by omega) (by omega) hov))

theorem smod_pos (x y B : BitVec 64) (hx : 0 ≤ x.toInt) (hB : B.toNat = y.toInt.natAbs) (hy : y.toInt ≠ 0) :
    (x % B).toInt = Vsa.While.wrap64 (x.toInt.tmod y.toInt) :=
  wrap_of_eq' (Vsa.Sim.res_pos x y x B (Vsa.Sim.mag_notop x (toNat_lt_of_toInt_nonneg hx)) hB hx hy)

theorem smod_neg (x y B : BitVec 64) (hx : x.toInt < 0) (hB : B.toNat = y.toInt.natAbs) (hy : y.toInt ≠ 0) :
    (0#64 - (0#64 - x) % B).toInt = Vsa.While.wrap64 (x.toInt.tmod y.toInt) :=
  wrap_of_eq' (Vsa.Sim.res_neg x y (0#64 - x) B (Vsa.Sim.mag_neg_top x (toNat_ge_of_toInt_neg hx)) hB hx hy)

theorem udiv_word {n d q : BitVec 64} (h : q.toNat = n.toNat / d.toNat) : q = n / d :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_udiv])

theorem umod_word {n d q : BitVec 64} (h : q.toNat = n.toNat % d.toNat) : q = n % d :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_umod])

theorem divdi3_iw {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (x y r : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (hy : y ≠ 0#64) (h10 : R 10 = x) (h11 : R 11 = y) (hr : R 1 = r)
    (hal : r.toNat % 4 = 0)
    (hk : ∀ R', (R' 10).toInt = Vsa.While.wrap64 (x.toInt.tdiv y.toInt) → SDivKeep R' R →
      IW live Dt DA S Q r R' Mt) :
    IW live Dt DA S Q 0x800046a4#64 R Mt := by
  have hy0 : y.toInt ≠ 0 := fun h => hy (BitVec.eq_of_toInt_eq (by simpa using h))
  sym_run hlive using [h10, h11] at 0x800046ac
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *)
  case hT.hT hx hyp =>
    rw [h10] at hx; rw [h11] at hyp
    refine iw_jal 0x8000471c _ _ ((step% jalx 0x8000471c) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
      (interp_code (by decide)) rfl ?_
    refine udiv_iw hlive (0#64 - x) y 0x80004720#64 _ Mt hy ?_ ?_ ?_ (by decide) (fun R' hq _ hkp => ?_)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h11
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have h5 : R' 5 = r := by
      rw [hkp 5 (by decide) (by decide) (by decide) (by decide)]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    sym_run hlive at 0x0
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · rw [h5]; exact hal
    · rw [h5]; refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [udiv_word hq]; exact sdiv_mn x y (by simpa using hx) (by simpa using hyp)
      · simp only [upd_apply, h10', ite_false]
        rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h1, h5', h10', ite_false]
  case hT.hF hx hyp =>
    rw [h10] at hx; rw [h11] at hyp
    refine udiv_iw hlive (0#64 - x) (0#64 - y) r _ Mt ?_ ?_ ?_ ?_ hal (fun R' hq _ hkp => ?_)
    · intro h0; apply hy; have := congrArg (0#64 - ·) h0; simpa using this
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    · refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · rw [udiv_word hq]
        exact sdiv_mm x y (by simpa using hx) (by have := hy0; simp at hyp; omega)
      · rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h10', h11', ite_false]
  case hF.hT hx hyp =>
    rw [h10] at hx; rw [h11] at hyp
    refine iw_jal 0x8000471c _ _ ((step% jalx 0x8000471c) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
      (interp_code (by decide)) rfl ?_
    refine udiv_iw hlive x (0#64 - y) 0x80004720#64 _ Mt ?_ ?_ ?_ ?_ (by decide) (fun R' hq _ hkp => ?_)
    · intro h0; apply hy; have := congrArg (0#64 - ·) h0; simpa using this
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have h5 : R' 5 = r := by
      rw [hkp 5 (by decide) (by decide) (by decide) (by decide)]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    sym_run hlive at 0x0
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · rw [h5]; exact hal
    · rw [h5]; refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [udiv_word hq]; exact sdiv_nm x y (by simpa using hx) (by simpa using hyp)
      · simp only [upd_apply, h10', ite_false]
        rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h1, h5', h11', ite_false]
  case hF.hF hx hyp =>
    rw [h10] at hx; rw [h11] at hyp
    refine udiv_iw hlive x y r _ Mt hy h10 h11 hr hal (fun R' hq _ hkp => ?_)
    refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => hkp z h10' h11' h12 h13)
    rw [udiv_word hq]
    exact sdiv_nn x y (by simpa using hx) (by have := hy0; simp at hyp; omega)

theorem moddi3_iw {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (x y r : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (hy : y ≠ 0#64) (h10 : R 10 = x) (h11 : R 11 = y) (hr : R 1 = r)
    (hal : r.toNat % 4 = 0)
    (hk : ∀ R', (R' 10).toInt = Vsa.While.wrap64 (x.toInt.tmod y.toInt) → SDivKeep R' R →
      IW live Dt DA S Q r R' Mt) :
    IW live Dt DA S Q 0x80004728#64 R Mt := by
  have hy0 : y.toInt ≠ 0 := fun h => hy (BitVec.eq_of_toInt_eq (by simpa using h))
  sym_run hlive using [h10, h11] at 0x800046ac
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *)
  case hT.hT hyp hx =>
    rw [h10] at hx; rw [h11] at hyp
    refine iw_jal 0x80004734 _ _ ((step% jalx 0x80004734) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
      (interp_code (by decide)) rfl ?_
    refine udiv_iw hlive (x) (0#64 - y) 0x80004738#64 _ Mt ?_ ?_ ?_ ?_ (by decide) (fun R' _ hm hkp => ?_)
    · intro h0; apply hy; have := congrArg (0#64 - ·) h0; simpa using this
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have h5 : R' 5 = r := by
      rw [hkp 5 (by decide) (by decide) (by decide) (by decide)]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    sym_run hlive at 0x0
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · rw [h5]; exact hal
    · rw [h5]; refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [umod_word hm]
        exact smod_pos x y (0#64 - y) (by simpa using hx) (Vsa.Sim.mag_neg_top y (toNat_ge_of_toInt_neg (by simpa using hyp))) hy0
      · simp only [upd_apply, h10', ite_false]
        rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h1, h5', h10', h11', ite_false]
  case hT.hF hyp hx =>
    rw [h10] at hx; rw [h11] at hyp
    refine iw_jal 0x8000474c _ _ ((step% jalx 0x8000474c) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
      (interp_code (by decide)) rfl ?_
    refine udiv_iw hlive (0#64 - x) (0#64 - y) 0x80004750#64 _ Mt ?_ ?_ ?_ ?_ (by decide) (fun R' _ hm hkp => ?_)
    · intro h0; apply hy; have := congrArg (0#64 - ·) h0; simpa using this
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have h5 : R' 5 = r := by
      rw [hkp 5 (by decide) (by decide) (by decide) (by decide)]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    sym_run hlive at 0x0
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · rw [h5]; exact hal
    · rw [h5]; refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [umod_word hm]
        exact smod_neg x y (0#64 - y) (by simpa using hx) (Vsa.Sim.mag_neg_top y (toNat_ge_of_toInt_neg (by simpa using hyp))) hy0
      · simp only [upd_apply, h10', ite_false]
        rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h1, h5', h10', h11', ite_false]
  case hF.hT hyp hx =>
    rw [h10] at hx; rw [h11] at hyp
    refine iw_jal 0x8000474c _ _ ((step% jalx 0x8000474c) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
      (interp_code (by decide)) rfl ?_
    refine udiv_iw hlive (0#64 - x) (y) 0x80004750#64 _ Mt ?_ ?_ ?_ ?_ (by decide) (fun R' _ hm hkp => ?_)
    · exact hy
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h11
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have h5 : R' 5 = r := by
      rw [hkp 5 (by decide) (by decide) (by decide) (by decide)]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    sym_run hlive at 0x0
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · rw [h5]; exact hal
    · rw [h5]; refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [umod_word hm]
        exact smod_neg x y (y) (by simpa using hx) (Vsa.Sim.mag_notop y (toNat_lt_of_toInt_nonneg (by simpa using hyp))) hy0
      · simp only [upd_apply, h10', ite_false]
        rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h1, h5', h10', h11', ite_false]
  case hF.hF hyp hx =>
    rw [h10] at hx; rw [h11] at hyp
    refine iw_jal 0x80004734 _ _ ((step% jalx 0x80004734) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
      (interp_code (by decide)) rfl ?_
    refine udiv_iw hlive (x) (y) 0x80004738#64 _ Mt ?_ ?_ ?_ ?_ (by decide) (fun R' _ hm hkp => ?_)
    · exact hy
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h11
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have h5 : R' 5 = r := by
      rw [hkp 5 (by decide) (by decide) (by decide) (by decide)]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    sym_run hlive at 0x0
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · rw [h5]; exact hal
    · rw [h5]; refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [umod_word hm]
        exact smod_pos x y (y) (by simpa using hx) (Vsa.Sim.mag_notop y (toNat_lt_of_toInt_nonneg (by simpa using hyp))) hy0
      · simp only [upd_apply, h10', ite_false]
        rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h1, h5', h10', h11', ite_false]

end VsaIris.Interp
