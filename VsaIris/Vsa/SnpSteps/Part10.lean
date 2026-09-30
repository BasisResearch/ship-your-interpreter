import VsaIris.Vsa.SnpRunDef
import VsaIris.Vsa.SymObs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def nx_80008534 : List BBlock := [{ body := [mkLine 0x80008534#64 0x000ccc03#32], term := none }]
def nx_80008538 : List BBlock := [{ body := [mkLine 0x80008538#64 0x06c00793#32], term := none }]
def nxT_8000853c : List BBlock := [⟨[], some (⟨0x8000853c#64, 0x32fc02e3#32, 0xe3#8, 0x02#8, 0xfc#8, 0x32#8, .br bop.BEQ true, 24, 15, 0xb24#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_8000853c : List BBlock := [⟨[], some (⟨0x8000853c#64, 0x32fc02e3#32, 0xe3#8, 0x02#8, 0xfc#8, 0x32#8, .br bop.BEQ false, 24, 15, 0xb24#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80008678 : List BBlock := [{ body := [mkLine 0x80008678#64 0x00813583#32], term := none }]
def nx_8000867c : List BBlock := [{ body := [mkLine 0x8000867c#64 0x0e010613#32], term := none }]
def nx_80008680 : List BBlock := [{ body := [mkLine 0x80008680#64 0x00040513#32], term := none }]
def nxT_80008688 : List BBlock := [⟨[], some (⟨0x80008688#64, 0xa8050863#32, 0x63#8, 0x08#8, 0x05#8, 0xa8#8, .br bop.BEQ true, 10, 0, 0x1290#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80008688 : List BBlock := [⟨[], some (⟨0x80008688#64, 0xa8050863#32, 0x63#8, 0x08#8, 0x05#8, 0xa8#8, .br bop.BEQ false, 10, 0, 0x1290#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem ntD_80008534 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 25) + sign_extend (m := 64) (0x000#12)).toNat 1)
    (hLDD : ∀ b ∈ accAddrs ((R 25) + sign_extend (m := 64) (0x000#12)).toNat 1, b ∈ DA)
    (hk : SnpW live Dt DA S Q 0x80008538#64 (upd R 24 (ldv .lbu Dt ((R 25) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80008534#64 R Mt :=
  swp_stepD nx_80008534 [24, 25] [bytesAt (imgM Dt) ((R 25) + sign_extend (m := 64) (0x000#12)).toNat 1] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008534 ChainFacts; chain_facts hm; exact ⟨hea, lpins1_img (fun b hb => dataReads_view hD b (hLDD b hb))⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 24 ∈ [24, 25])))) rfl hk

theorem nt_80008538 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000853c#64 (upd R 15 ((0#64) + sign_extend (m := 64) (0x06c#12))) Mt) :
    SnpW live Dt DA S Q 0x80008538#64 R Mt :=
  swp_stepD nx_80008538 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008538 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem nt_8000853c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 24) = (R 15) → SnpW live Dt DA S Q 0x80009060#64 R Mt) (hF : ¬ ((R 24) = (R 15)) → SnpW live Dt DA S Q 0x80008540#64 R Mt) :
    SnpW live Dt DA S Q 0x8000853c#64 R Mt := by
  by_cases hc : (R 24) = (R 15)
  · exact
    swp_stepD nxT_8000853c [15, 24] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_8000853c ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_8000853c [15, 24] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_8000853c ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80008678 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000867c#64 (upd R 11 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80008678#64 R Mt :=
  swp_stepD nx_80008678 [2, 11] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008678 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [2, 11])))) rfl hk

theorem nt_8000867c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008680#64 (upd R 12 ((R 2) + sign_extend (m := 64) (0x0e0#12))) Mt) :
    SnpW live Dt DA S Q 0x8000867c#64 R Mt :=
  swp_stepD nx_8000867c [2, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000867c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [2, 12])))) rfl hk

theorem nt_80008680 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008684#64 (upd R 10 ((R 8) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80008680#64 R Mt :=
  swp_stepD nx_80008680 [8, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008680 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [8, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalxn_80008684 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80008684 [0xef#8, 0x60#8, 0x40#8, 0x28#8], live p.1) :
    JalExec (vsaModel live) 0x80008684 [0xef#8, 0x60#8, 0x40#8, 0x28#8] 0x8000e908#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x80008684, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x80008685, .discard, 0x60#8) (by simp [codeFoot])
  have hb2 := hb (0x80008686, .discard, 0x40#8) (by simp [codeFoot])
  have hb3 := hb (0x80008687, .discard, 0x28#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x80008684#64) vm (0x284060ef#32) (0x006284#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80008684#64) 4)
      (0xef#8) (0x60#8) (0x40#8) (0x28#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0x284060ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80008684#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x8000e908#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x80008684#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x80008684 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem ntC_80008684 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e908#64 (upd R 1 (BitVec.ofNat 64 (0x80008684 + 4))) Mt) :
    SnpW live Dt DA S Q 0x80008684#64 R Mt :=
  swp_jal 0x80008684 [0xef#8, 0x60#8, 0x40#8, 0x28#8] 0x8000e908#64
    (jalxn_80008684 live fun p hp => hlive _ ((snp_code (by decide)) p hp))
    (fun p hp => List.mem_append_left _ ((snp_code (by decide)) p hp)) (by decide) (by decide) rfl hk

theorem nt_80008688 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 10) = (0#64) → SnpW live Dt DA S Q 0x80007918#64 R Mt) (hF : ¬ ((R 10) = (0#64)) → SnpW live Dt DA S Q 0x8000868c#64 R Mt) :
    SnpW live Dt DA S Q 0x80008688#64 R Mt := by
  by_cases hc : (R 10) = (0#64)
  · exact
    swp_stepD nxT_80008688 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80008688 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80008688 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80008688 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

end VsaIris.Sym
