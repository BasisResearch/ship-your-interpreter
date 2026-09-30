import VsaIris.Vsa.SnpRunDef
import VsaIris.Vsa.SymObs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def nx_80008310 : List BBlock := [{ body := [mkLine 0x80008310#64 0x000d0c93#32], term := none }]
def nx_80008314 : List BBlock := [{ body := [mkLine 0x80008314#64 0x00050413#32], term := none }]
def nxT_80008318 : List BBlock := [⟨[], some (⟨0x80008318#64, 0x0567f063#32, 0x63#8, 0xf0#8, 0x67#8, 0x05#8, .br bop.BGEU true, 15, 22, 0x40#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80008318 : List BBlock := [⟨[], some (⟨0x80008318#64, 0x0567f063#32, 0x63#8, 0xf0#8, 0x67#8, 0x05#8, .br bop.BGEU false, 15, 22, 0x40#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_8000831c : List BBlock := [{ body := [mkLine 0x8000831c#64 0x00a00593#32], term := none }]
def nx_80008320 : List BBlock := [{ body := [mkLine 0x80008320#64 0x00040513#32], term := none }]
def nx_80008328 : List BBlock := [{ body := [mkLine 0x80008328#64 0x0305051b#32], term := none }]
def nx_8000832c : List BBlock := [{ body := [mkLine 0x8000832c#64 0xfeac8fa3#32], term := none }]
def nx_80008330 : List BBlock := [{ body := [mkLine 0x80008330#64 0xfffc8d13#32], term := none }]
def nx_80008334 : List BBlock := [{ body := [mkLine 0x80008334#64 0x001b8b9b#32], term := none }]
def nxT_80008338 : List BBlock := [⟨[], some (⟨0x80008338#64, 0xfc0d82e3#32, 0xe3#8, 0x82#8, 0x0d#8, 0xfc#8, .br bop.BEQ true, 27, 0, 0x1fc4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80008338 : List BBlock := [⟨[], some (⟨0x80008338#64, 0xfc0d82e3#32, 0xe3#8, 0x82#8, 0x0d#8, 0xfc#8, .br bop.BEQ false, 27, 0, 0x1fc4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80008358 : List BBlock := [{ body := [mkLine 0x80008358#64 0x07013b03#32], term := none }]
def nx_8000835c : List BBlock := [{ body := [mkLine 0x8000835c#64 0x07413423#32], term := none }]
def nx_80008360 : List BBlock := [{ body := [mkLine 0x80008360#64 0x03813a03#32], term := none }]
def nx_80008364 : List BBlock := [{ body := [mkLine 0x80008364#64 0x02813303#32], term := none }]
def nx_80008368 : List BBlock := [{ body := [mkLine 0x80008368#64 0x41ab0b3b#32], term := none }]
def nx_8000836c : List BBlock := [{ body := [mkLine 0x8000836c#64 0x03713423#32], term := none }]
def nx_80008370 : List BBlock := [{ body := [mkLine 0x80008370#64 0x02013e03#32], term := none }]
def nx_80008374 : List BBlock := [{ body := [mkLine 0x80008374#64 0x03013b83#32], term := none }]
def nx_80008378 : List BBlock := [{ body := [mkLine 0x80008378#64 0x07813403#32], term := none }]
def nx_8000837c : List BBlock := [{ body := [mkLine 0x8000837c#64 0x000a081b#32], term := none }]
def nxT_80008380 : List BBlock := [⟨[], some (⟨0x80008380#64, 0x016a5463#32, 0x63#8, 0x54#8, 0x6a#8, 0x01#8, .br bop.BGE true, 20, 22, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80008380 : List BBlock := [⟨[], some (⟨0x80008380#64, 0x016a5463#32, 0x63#8, 0x54#8, 0x6a#8, 0x01#8, .br bop.BGE false, 20, 22, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80008384 : List BBlock := [{ body := [mkLine 0x80008384#64 0x000b081b#32], term := none }]
def nx_80008388 : List BBlock := [{ body := [mkLine 0x80008388#64 0x0a714f03#32], term := none }]
def nx_8000838c : List BBlock := [{ body := [mkLine 0x8000838c#64 0x00000f93#32], term := none }]
def nx_80008390 : List BBlock := [{ body := [mkLine 0x80008390#64 0x02013023#32], term := none }]
def nx_80008394 : List BBlock := [⟨[], some (⟨0x80008394#64, 0xd99ff06f#32, 0x6f#8, 0xf0#8, 0x9f#8, 0xd9#8, .j, 0, 0, 0x0#13, 0x1ffd98#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem nt_80008310 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008314#64 (upd R 25 ((R 26) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80008310#64 R Mt :=
  swp_stepD nx_80008310 [25, 26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008310 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 25 ∈ [25, 26])))) rfl hk

theorem nt_80008314 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008318#64 (upd R 8 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80008314#64 R Mt :=
  swp_stepD nx_80008314 [8, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008314 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8, 10])))) rfl hk

theorem nt_80008318 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 22).toNat ≤ (R 15).toNat → SnpW live Dt DA S Q 0x80008358#64 R Mt) (hF : ¬ ((R 22).toNat ≤ (R 15).toNat) → SnpW live Dt DA S Q 0x8000831c#64 R Mt) :
    SnpW live Dt DA S Q 0x80008318#64 R Mt := by
  by_cases hc : (R 22).toNat ≤ (R 15).toNat
  · exact
    swp_stepD nxT_80008318 [15, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80008318 ChainFacts; chain_facts hm; exact (guard_bgeu _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80008318 [15, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80008318 ChainFacts; chain_facts hm; exact (guard_false (guard_bgeu _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_8000831c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008320#64 (upd R 11 ((0#64) + sign_extend (m := 64) (0x00a#12))) Mt) :
    SnpW live Dt DA S Q 0x8000831c#64 R Mt :=
  swp_stepD nx_8000831c [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000831c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

theorem nt_80008320 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008324#64 (upd R 10 ((R 8) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80008320#64 R Mt :=
  swp_stepD nx_80008320 [8, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008320 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [8, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalxn_80008324 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80008324 [0xef#8, 0xc0#8, 0x0f#8, 0xbd#8], live p.1) :
    JalExec (vsaModel live) 0x80008324 [0xef#8, 0xc0#8, 0x0f#8, 0xbd#8] 0x800046f4#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x80008324, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x80008325, .discard, 0xc0#8) (by simp [codeFoot])
  have hb2 := hb (0x80008326, .discard, 0x0f#8) (by simp [codeFoot])
  have hb3 := hb (0x80008327, .discard, 0xbd#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x80008324#64) vm (0xbd0fc0ef#32) (0x1fc3d0#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80008324#64) 4)
      (0xef#8) (0xc0#8) (0x0f#8) (0xbd#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xbd0fc0ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80008324#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x800046f4#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x80008324#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x80008324 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem ntC_80008324 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800046f4#64 (upd R 1 (BitVec.ofNat 64 (0x80008324 + 4))) Mt) :
    SnpW live Dt DA S Q 0x80008324#64 R Mt :=
  swp_jal 0x80008324 [0xef#8, 0xc0#8, 0x0f#8, 0xbd#8] 0x800046f4#64
    (jalxn_80008324 live fun p hp => hlive _ ((snp_code (by decide)) p hp))
    (fun p hp => List.mem_append_left _ ((snp_code (by decide)) p hp)) (by decide) (by decide) rfl hk

theorem nt_80008328 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000832c#64 (upd R 10 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 10) + sign_extend (m := 64) (0x030#12)) 31 0))) Mt) :
    SnpW live Dt DA S Q 0x80008328#64 R Mt :=
  swp_stepD nx_80008328 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008328 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem nt_8000832c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOKb ((R 25) + sign_extend (m := 64) (0xfff#12)).toNat)
    (hS : ∀ b ∈ accAddrs ((R 25) + sign_extend (m := 64) (0xfff#12)).toNat 1, S b)
    (hk : SnpW live Dt DA S Q 0x80008330#64 R (writeLog Mt [(((R 25) + sign_extend (m := 64) (0xfff#12)).toNat, 1, (R 10))])) :
    SnpW live Dt DA S Q 0x8000832c#64 R Mt :=
  swp_stepD nx_8000832c [10, 25] [] [] (accAddrs ((R 25) + sign_extend (m := 64) (0xfff#12)).toNat 1) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000832c ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80008330 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008334#64 (upd R 26 ((R 25) + sign_extend (m := 64) (0xfff#12))) Mt) :
    SnpW live Dt DA S Q 0x80008330#64 R Mt :=
  swp_stepD nx_80008330 [25, 26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008330 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 26 ∈ [25, 26])))) rfl hk

theorem nt_80008334 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008338#64 (upd R 23 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 23) + sign_extend (m := 64) (0x001#12)) 31 0))) Mt) :
    SnpW live Dt DA S Q 0x80008334#64 R Mt :=
  swp_stepD nx_80008334 [23] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008334 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [23])))) rfl hk

theorem nt_80008338 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 27) = (0#64) → SnpW live Dt DA S Q 0x800082fc#64 R Mt) (hF : ¬ ((R 27) = (0#64)) → SnpW live Dt DA S Q 0x8000833c#64 R Mt) :
    SnpW live Dt DA S Q 0x80008338#64 R Mt := by
  by_cases hc : (R 27) = (0#64)
  · exact
    swp_stepD nxT_80008338 [27] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80008338 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80008338 [27] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80008338 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80008358 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000835c#64 (upd R 22 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x070#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80008358#64 R Mt :=
  swp_stepD nx_80008358 [2, 22] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008358 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [2, 22])))) rfl hk

theorem nt_8000835c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80008360#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x068#12)).toNat, 8, (R 20))])) :
    SnpW live Dt DA S Q 0x8000835c#64 R Mt :=
  swp_stepD nx_8000835c [2, 20] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000835c ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80008360 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80008364#64 (upd R 20 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x038#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80008360#64 R Mt :=
  swp_stepD nx_80008360 [2, 20] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008360 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [2, 20])))) rfl hk

theorem nt_80008364 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80008368#64 (upd R 6 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x028#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80008364#64 R Mt :=
  swp_stepD nx_80008364 [2, 6] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008364 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 6 ∈ [2, 6])))) rfl hk

theorem nt_80008368 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000836c#64 (upd R 22 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 22) 31 0) - (Sail.BitVec.extractLsb (R 26) 31 0)))) Mt) :
    SnpW live Dt DA S Q 0x80008368#64 R Mt :=
  swp_stepD nx_80008368 [22, 26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008368 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [22, 26])))) rfl hk

theorem nt_8000836c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80008370#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x028#12)).toNat, 8, (R 23))])) :
    SnpW live Dt DA S Q 0x8000836c#64 R Mt :=
  swp_stepD nx_8000836c [2, 23] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000836c ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80008370 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80008374#64 (upd R 28 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80008370#64 R Mt :=
  swp_stepD nx_80008370 [2, 28] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008370 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 28 ∈ [2, 28])))) rfl hk

theorem nt_80008374 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80008378#64 (upd R 23 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x030#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80008374#64 R Mt :=
  swp_stepD nx_80008374 [2, 23] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008374 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [2, 23])))) rfl hk

theorem nt_80008378 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000837c#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x078#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80008378#64 R Mt :=
  swp_stepD nx_80008378 [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008378 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem nt_8000837c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008380#64 (upd R 16 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 20) + sign_extend (m := 64) (0x000#12)) 31 0))) Mt) :
    SnpW live Dt DA S Q 0x8000837c#64 R Mt :=
  swp_stepD nx_8000837c [16, 20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000837c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 16 ∈ [16, 20])))) rfl hk

theorem nt_80008380 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 22).toInt ≤ (R 20).toInt → SnpW live Dt DA S Q 0x80008388#64 R Mt) (hF : ¬ ((R 22).toInt ≤ (R 20).toInt) → SnpW live Dt DA S Q 0x80008384#64 R Mt) :
    SnpW live Dt DA S Q 0x80008380#64 R Mt := by
  by_cases hc : (R 22).toInt ≤ (R 20).toInt
  · exact
    swp_stepD nxT_80008380 [20, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80008380 ChainFacts; chain_facts hm; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80008380 [20, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80008380 ChainFacts; chain_facts hm; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80008384 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008388#64 (upd R 16 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 22) + sign_extend (m := 64) (0x000#12)) 31 0))) Mt) :
    SnpW live Dt DA S Q 0x80008384#64 R Mt :=
  swp_stepD nx_80008384 [16, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008384 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 16 ∈ [16, 22])))) rfl hk

theorem nt_80008388 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1, S b)
    (hk : SnpW live Dt DA S Q 0x8000838c#64 (upd R 30 (ldv .lbu Mt ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80008388#64 R Mt :=
  swp_stepD nx_80008388 [2, 30] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008388 ChainFacts; chain_facts hm; exact ⟨hea, lpins1_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 30 ∈ [2, 30])))) rfl hk

theorem nt_8000838c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008390#64 (upd R 31 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x8000838c#64 R Mt :=
  swp_stepD nx_8000838c [31] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000838c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 31 ∈ [31])))) rfl hk

theorem nt_80008390 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80008394#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (0#64))])) :
    SnpW live Dt DA S Q 0x80008390#64 R Mt :=
  swp_stepD nx_80008390 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80008390 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80008394 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000812c#64 R Mt) :
    SnpW live Dt DA S Q 0x80008394#64 R Mt :=
  swp_stepD nx_80008394 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008394 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
