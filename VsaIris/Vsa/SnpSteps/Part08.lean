import VsaIris.Vsa.SnpRunDef
import VsaIris.Vsa.SymObs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def nx_80008130 : List BBlock := [{ body := [mkLine 0x80008130#64 0x0018081b#32], term := none }]
def nx_80008134 : List BBlock := [⟨[], some (⟨0x80008134#64, 0xf55ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf5#8, .j, 0, 0, 0x0#13, 0x1fff54#21, 0#12⟩ : TInstr)⟩]
def nx_800082c8 : List BBlock := [{ body := [mkLine 0x800082c8#64 0x15c10b13#32], term := none }]
def nx_800082cc : List BBlock := [{ body := [mkLine 0x800082cc#64 0x03713823#32], term := none }]
def nx_800082d0 : List BBlock := [{ body := [mkLine 0x800082d0#64 0x03413c23#32], term := none }]
def nx_800082d4 : List BBlock := [{ body := [mkLine 0x800082d4#64 0x06813c23#32], term := none }]
def nx_800082d8 : List BBlock := [{ body := [mkLine 0x800082d8#64 0x06813a03#32], term := none }]
def nx_800082dc : List BBlock := [{ body := [mkLine 0x800082dc#64 0x000b0c93#32], term := none }]
def nx_800082e0 : List BBlock := [{ body := [mkLine 0x800082e0#64 0x03c13023#32], term := none }]
def nx_800082e4 : List BBlock := [{ body := [mkLine 0x800082e4#64 0x02613423#32], term := none }]
def nx_800082e8 : List BBlock := [{ body := [mkLine 0x800082e8#64 0x00000b93#32], term := none }]
def nx_800082ec : List BBlock := [{ body := [mkLine 0x800082ec#64 0x40037d93#32], term := none }]
def nx_800082f0 : List BBlock := [{ body := [mkLine 0x800082f0#64 0x07613823#32], term := none }]
def nx_800082f4 : List BBlock := [{ body := [mkLine 0x800082f4#64 0x00070413#32], term := none }]
def nx_800082f8 : List BBlock := [⟨[], some (⟨0x800082f8#64, 0x0240006f#32, 0x6f#8, 0x00#8, 0x40#8, 0x02#8, .j, 0, 0, 0x0#13, 0x24#21, 0#12⟩ : TInstr)⟩]
def nx_800082fc : List BBlock := [{ body := [mkLine 0x800082fc#64 0x00040513#32], term := none }]
def nx_80008300 : List BBlock := [{ body := [mkLine 0x80008300#64 0x00a00593#32], term := none }]
def nx_80008308 : List BBlock := [{ body := [mkLine 0x80008308#64 0x00040b13#32], term := none }]
def nx_8000830c : List BBlock := [{ body := [mkLine 0x8000830c#64 0x00900793#32], term := none }]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem nt_80008130 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008134#64 (upd R 16 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 16) + sign_extend (m := 64) (0x001#12)) 31 0))) Mt) :
    SnpW live Dt DA S Q 0x80008130#64 R Mt :=
  swp_stepD nx_80008130 [16] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008130 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 16 ∈ [16])))) rfl hk

theorem nt_80008134 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008088#64 R Mt) :
    SnpW live Dt DA S Q 0x80008134#64 R Mt :=
  swp_stepD nx_80008134 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008134 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800082c8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800082cc#64 (upd R 22 ((R 2) + sign_extend (m := 64) (0x15c#12))) Mt) :
    SnpW live Dt DA S Q 0x800082c8#64 R Mt :=
  swp_stepD nx_800082c8 [2, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800082c8 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [2, 22])))) rfl hk

theorem nt_800082cc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800082d0#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x030#12)).toNat, 8, (R 23))])) :
    SnpW live Dt DA S Q 0x800082cc#64 R Mt :=
  swp_stepD nx_800082cc [2, 23] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800082cc ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800082d0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800082d4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x038#12)).toNat, 8, (R 20))])) :
    SnpW live Dt DA S Q 0x800082d0#64 R Mt :=
  swp_stepD nx_800082d0 [2, 20] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800082d0 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800082d4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800082d8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x078#12)).toNat, 8, (R 8))])) :
    SnpW live Dt DA S Q 0x800082d4#64 R Mt :=
  swp_stepD nx_800082d4 [2, 8] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800082d4 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800082d8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800082dc#64 (upd R 20 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x068#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800082d8#64 R Mt :=
  swp_stepD nx_800082d8 [2, 20] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800082d8 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [2, 20])))) rfl hk

theorem nt_800082dc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800082e0#64 (upd R 25 ((R 22) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x800082dc#64 R Mt :=
  swp_stepD nx_800082dc [22, 25] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800082dc ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 25 ∈ [22, 25])))) rfl hk

theorem nt_800082e0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800082e4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (R 28))])) :
    SnpW live Dt DA S Q 0x800082e0#64 R Mt :=
  swp_stepD nx_800082e0 [2, 28] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800082e0 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800082e4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800082e8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x028#12)).toNat, 8, (R 6))])) :
    SnpW live Dt DA S Q 0x800082e4#64 R Mt :=
  swp_stepD nx_800082e4 [2, 6] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800082e4 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800082e8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800082ec#64 (upd R 23 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x800082e8#64 R Mt :=
  swp_stepD nx_800082e8 [23] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800082e8 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [23])))) rfl hk

theorem nt_800082ec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800082f0#64 (upd R 27 ((R 6) &&& sign_extend (m := 64) (0x400#12))) Mt) :
    SnpW live Dt DA S Q 0x800082ec#64 R Mt :=
  swp_stepD nx_800082ec [6, 27] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800082ec ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 27 ∈ [6, 27])))) rfl hk

theorem nt_800082f0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800082f4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x070#12)).toNat, 8, (R 22))])) :
    SnpW live Dt DA S Q 0x800082f0#64 R Mt :=
  swp_stepD nx_800082f0 [2, 22] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800082f0 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800082f4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800082f8#64 (upd R 8 ((R 14) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x800082f4#64 R Mt :=
  swp_stepD nx_800082f4 [8, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800082f4 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8, 14])))) rfl hk

theorem nt_800082f8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000831c#64 R Mt) :
    SnpW live Dt DA S Q 0x800082f8#64 R Mt :=
  swp_stepD nx_800082f8 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800082f8 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800082fc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008300#64 (upd R 10 ((R 8) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x800082fc#64 R Mt :=
  swp_stepD nx_800082fc [8, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800082fc ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [8, 10])))) rfl hk

theorem nt_80008300 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008304#64 (upd R 11 ((0#64) + sign_extend (m := 64) (0x00a#12))) Mt) :
    SnpW live Dt DA S Q 0x80008300#64 R Mt :=
  swp_stepD nx_80008300 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008300 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalxn_80008304 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80008304 [0xef#8, 0xc0#8, 0x8f#8, 0xba#8], live p.1) :
    JalExec (vsaModel live) 0x80008304 [0xef#8, 0xc0#8, 0x8f#8, 0xba#8] 0x800046ac#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x80008304, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x80008305, .discard, 0xc0#8) (by simp [codeFoot])
  have hb2 := hb (0x80008306, .discard, 0x8f#8) (by simp [codeFoot])
  have hb3 := hb (0x80008307, .discard, 0xba#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x80008304#64) vm (0xba8fc0ef#32) (0x1fc3a8#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80008304#64) 4)
      (0xef#8) (0xc0#8) (0x8f#8) (0xba#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xba8fc0ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80008304#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x800046ac#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x80008304#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x80008304 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem ntC_80008304 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800046ac#64 (upd R 1 (BitVec.ofNat 64 (0x80008304 + 4))) Mt) :
    SnpW live Dt DA S Q 0x80008304#64 R Mt :=
  swp_jal 0x80008304 [0xef#8, 0xc0#8, 0x8f#8, 0xba#8] 0x800046ac#64
    (jalxn_80008304 live fun p hp => hlive _ ((snp_code (by decide)) p hp))
    (fun p hp => List.mem_append_left _ ((snp_code (by decide)) p hp)) (by decide) (by decide) rfl hk

theorem nt_80008308 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000830c#64 (upd R 22 ((R 8) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80008308#64 R Mt :=
  swp_stepD nx_80008308 [8, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008308 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [8, 22])))) rfl hk

theorem nt_8000830c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008310#64 (upd R 15 ((0#64) + sign_extend (m := 64) (0x009#12))) Mt) :
    SnpW live Dt DA S Q 0x8000830c#64 R Mt :=
  swp_stepD nx_8000830c [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000830c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

end VsaIris.Sym
