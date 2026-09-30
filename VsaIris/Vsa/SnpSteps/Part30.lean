import VsaIris.Vsa.SnpRunDef
import VsaIris.Vsa.SymObs
import Vsa.Sim.DecodeNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def nx_8001438c : List BBlock := [{ body := [mkLine 0x8001438c#64 0xfc010113#32], term := none }]
def nx_80014390 : List BBlock := [{ body := [mkLine 0x80014390#64 0x02913423#32], term := none }]
def nx_80014394 : List BBlock := [{ body := [mkLine 0x80014394#64 0x00c5a483#32], term := none }]
def nx_80014398 : List BBlock := [{ body := [mkLine 0x80014398#64 0x02813823#32], term := none }]
def nx_8001439c : List BBlock := [{ body := [mkLine 0x8001439c#64 0x02113c23#32], term := none }]
def nx_800143a0 : List BBlock := [{ body := [mkLine 0x800143a0#64 0x00058413#32], term := none }]
def nx_800143a4 : List BBlock := [{ body := [mkLine 0x800143a4#64 0x00060793#32], term := none }]
def nxT_800143a8 : List BBlock := [⟨[], some (⟨0x800143a8#64, 0x0496f663#32, 0x63#8, 0xf6#8, 0x96#8, 0x04#8, .br bop.BGEU true, 13, 9, 0x4c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_800143a8 : List BBlock := [⟨[], some (⟨0x800143a8#64, 0x0496f663#32, 0x63#8, 0xf6#8, 0x96#8, 0x04#8, .br bop.BGEU false, 13, 9, 0x4c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_800143ac : List BBlock := [{ body := [mkLine 0x800143ac#64 0x0006871b#32], term := none }]
def nx_800143b0 : List BBlock := [{ body := [mkLine 0x800143b0#64 0x00043503#32], term := none }]
def nx_800143b4 : List BBlock := [{ body := [mkLine 0x800143b4#64 0x00070493#32], term := none }]
def nx_800143b8 : List BBlock := [{ body := [mkLine 0x800143b8#64 0x00078593#32], term := none }]
def nx_800143bc : List BBlock := [{ body := [mkLine 0x800143bc#64 0x00048613#32], term := none }]
def nx_800143c4 : List BBlock := [{ body := [mkLine 0x800143c4#64 0x00c42703#32], term := none }]
def nx_800143c8 : List BBlock := [{ body := [mkLine 0x800143c8#64 0x00043783#32], term := none }]
def nx_800143cc : List BBlock := [{ body := [mkLine 0x800143cc#64 0x00000513#32], term := none }]
def nx_800143d0 : List BBlock := [{ body := [mkLine 0x800143d0#64 0x4097073b#32], term := none }]
def nx_800143d4 : List BBlock := [{ body := [mkLine 0x800143d4#64 0x009787b3#32], term := none }]
def nx_800143d8 : List BBlock := [{ body := [mkLine 0x800143d8#64 0x00e42623#32], term := none }]
def nx_800143dc : List BBlock := [{ body := [mkLine 0x800143dc#64 0x00f43023#32], term := none }]
def nx_800143e0 : List BBlock := [{ body := [mkLine 0x800143e0#64 0x03813083#32], term := none }]
def nx_800143e4 : List BBlock := [{ body := [mkLine 0x800143e4#64 0x03013403#32], term := none }]
def nx_800143e8 : List BBlock := [{ body := [mkLine 0x800143e8#64 0x02813483#32], term := none }]
def nx_800143ec : List BBlock := [{ body := [mkLine 0x800143ec#64 0x04010113#32], term := none }]
def nx_800143f0 : List BBlock := [⟨[], some (⟨0x800143f0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_800143f4 : List BBlock := [{ body := [mkLine 0x800143f4#64 0x01059703#32], term := none }]
def nx_800143f8 : List BBlock := [{ body := [mkLine 0x800143f8#64 0x00050893#32], term := none }]
def nx_800143fc : List BBlock := [{ body := [mkLine 0x800143fc#64 0x0005b503#32], term := none }]
def nx_80014400 : List BBlock := [{ body := [mkLine 0x80014400#64 0x48077613#32], term := none }]
def nxT_80014404 : List BBlock := [⟨[], some (⟨0x80014404#64, 0xfa060ae3#32, 0xe3#8, 0x0a#8, 0x06#8, 0xfa#8, .br bop.BEQ true, 12, 0, 0x1fb4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80014404 : List BBlock := [⟨[], some (⟨0x80014404#64, 0xfa060ae3#32, 0xe3#8, 0x0a#8, 0x06#8, 0xfa#8, .br bop.BEQ false, 12, 0, 0x1fb4#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem nt_8001438c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80014390#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0xfc0#12))) Mt) :
    SnpW live Dt DA S Q 0x8001438c#64 R Mt :=
  swp_stepD nx_8001438c [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8001438c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem nt_80014390 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80014394#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x028#12)).toNat, 8, (R 9))])) :
    SnpW live Dt DA S Q 0x80014390#64 R Mt :=
  swp_stepD nx_80014390 [2, 9] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80014390 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80014394 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x00c#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x00c#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x80014398#64 (upd R 9 (ldv .lw Mt ((R 11) + sign_extend (m := 64) (0x00c#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80014394#64 R Mt :=
  swp_stepD nx_80014394 [9, 11] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x00c#12)).toNat 4] (accAddrs ((R 11) + sign_extend (m := 64) (0x00c#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80014394 ChainFacts; chain_facts hm; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9, 11])))) rfl hk

theorem nt_80014398 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8001439c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x030#12)).toNat, 8, (R 8))])) :
    SnpW live Dt DA S Q 0x80014398#64 R Mt :=
  swp_stepD nx_80014398 [2, 8] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80014398 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8001439c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800143a0#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x038#12)).toNat, 8, (R 1))])) :
    SnpW live Dt DA S Q 0x8001439c#64 R Mt :=
  swp_stepD nx_8001439c [1, 2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8001439c ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800143a0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800143a4#64 (upd R 8 ((R 11) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x800143a0#64 R Mt :=
  swp_stepD nx_800143a0 [8, 11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143a0 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8, 11])))) rfl hk

theorem nt_800143a4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800143a8#64 (upd R 15 ((R 12) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x800143a4#64 R Mt :=
  swp_stepD nx_800143a4 [12, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143a4 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [12, 15])))) rfl hk

theorem nt_800143a8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 9).toNat ≤ (R 13).toNat → SnpW live Dt DA S Q 0x800143f4#64 R Mt) (hF : ¬ ((R 9).toNat ≤ (R 13).toNat) → SnpW live Dt DA S Q 0x800143ac#64 R Mt) :
    SnpW live Dt DA S Q 0x800143a8#64 R Mt := by
  by_cases hc : (R 9).toNat ≤ (R 13).toNat
  · exact
    swp_stepD nxT_800143a8 [9, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_800143a8 ChainFacts; chain_facts hm; exact (guard_bgeu _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_800143a8 [9, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_800143a8 ChainFacts; chain_facts hm; exact (guard_false (guard_bgeu _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_800143ac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800143b0#64 (upd R 14 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 13) + sign_extend (m := 64) (0x000#12)) 31 0))) Mt) :
    SnpW live Dt DA S Q 0x800143ac#64 R Mt :=
  swp_stepD nx_800143ac [13, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143ac ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [13, 14])))) rfl hk

theorem nt_800143b0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800143b4#64 (upd R 10 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800143b0#64 R Mt :=
  swp_stepD nx_800143b0 [8, 10] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143b0 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [8, 10])))) rfl hk

theorem nt_800143b4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800143b8#64 (upd R 9 ((R 14) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x800143b4#64 R Mt :=
  swp_stepD nx_800143b4 [9, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143b4 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9, 14])))) rfl hk

theorem nt_800143b8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800143bc#64 (upd R 11 ((R 15) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x800143b8#64 R Mt :=
  swp_stepD nx_800143b8 [11, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143b8 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11, 15])))) rfl hk

theorem nt_800143bc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800143c0#64 (upd R 12 ((R 9) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x800143bc#64 R Mt :=
  swp_stepD nx_800143bc [9, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143bc ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [9, 12])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalxn_800143c0 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x800143c0 [0xef#8, 0x20#8, 0x4f#8, 0xe0#8], live p.1) :
    JalExec (vsaModel live) 0x800143c0 [0xef#8, 0x20#8, 0x4f#8, 0xe0#8] 0x800069c4#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x800143c0, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x800143c1, .discard, 0x20#8) (by simp [codeFoot])
  have hb2 := hb (0x800143c2, .discard, 0x4f#8) (by simp [codeFoot])
  have hb3 := hb (0x800143c3, .discard, 0xe0#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x800143c0#64) vm (0xe04f20ef#32) (0x1f2604#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800143c0#64) 4)
      (0xef#8) (0x20#8) (0x4f#8) (0xe0#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xe04f20ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x800143c0#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x800069c4#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x800143c0#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x800143c0 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem ntC_800143c0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800069c4#64 (upd R 1 (BitVec.ofNat 64 (0x800143c0 + 4))) Mt) :
    SnpW live Dt DA S Q 0x800143c0#64 R Mt :=
  swp_jal 0x800143c0 [0xef#8, 0x20#8, 0x4f#8, 0xe0#8] 0x800069c4#64
    (jalxn_800143c0 live fun p hp => hlive _ ((snp_code (by decide)) p hp))
    (fun p hp => List.mem_append_left _ ((snp_code (by decide)) p hp)) (by decide) (by decide) rfl hk

theorem nt_800143c4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x00c#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x00c#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x800143c8#64 (upd R 14 (ldv .lw Mt ((R 8) + sign_extend (m := 64) (0x00c#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800143c4#64 R Mt :=
  swp_stepD nx_800143c4 [8, 14] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x00c#12)).toNat 4] (accAddrs ((R 8) + sign_extend (m := 64) (0x00c#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143c4 ChainFacts; chain_facts hm; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [8, 14])))) rfl hk

theorem nt_800143c8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800143cc#64 (upd R 15 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800143c8#64 R Mt :=
  swp_stepD nx_800143c8 [8, 15] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143c8 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [8, 15])))) rfl hk

theorem nt_800143cc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800143d0#64 (upd R 10 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x800143cc#64 R Mt :=
  swp_stepD nx_800143cc [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143cc ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem nt_800143d0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800143d4#64 (upd R 14 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 14) 31 0) - (Sail.BitVec.extractLsb (R 9) 31 0)))) Mt) :
    SnpW live Dt DA S Q 0x800143d0#64 R Mt :=
  swp_stepD nx_800143d0 [9, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143d0 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [9, 14])))) rfl hk

theorem nt_800143d4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800143d8#64 (upd R 15 ((R 15) + (R 9))) Mt) :
    SnpW live Dt DA S Q 0x800143d4#64 R Mt :=
  swp_stepD nx_800143d4 [9, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143d4 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [9, 15])))) rfl hk

theorem nt_800143d8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 8) + sign_extend (m := 64) (0x00c#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x00c#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x800143dc#64 R (writeLog Mt [(((R 8) + sign_extend (m := 64) (0x00c#12)).toNat, 4, (R 14))])) :
    SnpW live Dt DA S Q 0x800143d8#64 R Mt :=
  swp_stepD nx_800143d8 [8, 14] [] [] (accAddrs ((R 8) + sign_extend (m := 64) (0x00c#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800143d8 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800143dc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800143e0#64 R (writeLog Mt [(((R 8) + sign_extend (m := 64) (0x000#12)).toNat, 8, (R 15))])) :
    SnpW live Dt DA S Q 0x800143dc#64 R Mt :=
  swp_stepD nx_800143dc [8, 15] [] [] (accAddrs ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800143dc ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800143e0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800143e4#64 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x038#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800143e0#64 R Mt :=
  swp_stepD nx_800143e0 [1, 2] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143e0 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 1 ∈ [1, 2])))) rfl hk

theorem nt_800143e4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800143e8#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x030#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800143e4#64 R Mt :=
  swp_stepD nx_800143e4 [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143e4 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem nt_800143e8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800143ec#64 (upd R 9 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x028#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800143e8#64 R Mt :=
  swp_stepD nx_800143e8 [2, 9] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143e8 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [2, 9])))) rfl hk

theorem nt_800143ec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800143f0#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0x040#12))) Mt) :
    SnpW live Dt DA S Q 0x800143ec#64 R Mt :=
  swp_stepD nx_800143ec [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143ec ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem nt_800143f0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : SnpW live Dt DA S Q (R 1) R Mt) :
    SnpW live Dt DA S Q 0x800143f0#64 R Mt :=
  swp_stepD nx_800143f0 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143f0 ChainFacts; chain_facts hm; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800143f4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : SnpW live Dt DA S Q 0x800143f8#64 (upd R 14 (ldv .lh Mt ((R 11) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800143f4#64 R Mt :=
  swp_stepD nx_800143f4 [11, 14] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2] (accAddrs ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143f4 ChainFacts; chain_facts hm; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [11, 14])))) rfl hk

theorem nt_800143f8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800143fc#64 (upd R 17 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x800143f8#64 R Mt :=
  swp_stepD nx_800143f8 [10, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143f8 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 17 ∈ [10, 17])))) rfl hk

theorem nt_800143fc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80014400#64 (upd R 10 (ldv .ld Mt ((R 11) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800143fc#64 R Mt :=
  swp_stepD nx_800143fc [10, 11] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800143fc ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 11])))) rfl hk

theorem nt_80014400 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80014404#64 (upd R 12 ((R 14) &&& sign_extend (m := 64) (0x480#12))) Mt) :
    SnpW live Dt DA S Q 0x80014400#64 R Mt :=
  swp_stepD nx_80014400 [12, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80014400 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 14])))) rfl hk

theorem nt_80014404 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 12) = (0#64) → SnpW live Dt DA S Q 0x800143b8#64 R Mt) (hF : ¬ ((R 12) = (0#64)) → SnpW live Dt DA S Q 0x80014408#64 R Mt) :
    SnpW live Dt DA S Q 0x80014404#64 R Mt := by
  by_cases hc : (R 12) = (0#64)
  · exact
    swp_stepD nxT_80014404 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80014404 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80014404 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80014404 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

end VsaIris.Sym
