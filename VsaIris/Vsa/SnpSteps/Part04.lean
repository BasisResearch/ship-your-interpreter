import VsaIris.Vsa.SnpRunDef
import VsaIris.Vsa.SymObs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def nx_800079b0 : List BBlock := [{ body := [mkLine 0x800079b0#64 0x0f013783#32], term := none }]
def nxT_800079b4 : List BBlock := [⟨[], some (⟨0x800079b4#64, 0x00078463#32, 0x63#8, 0x84#8, 0x07#8, 0x00#8, .br bop.BEQ true, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_800079b4 : List BBlock := [⟨[], some (⟨0x800079b4#64, 0x00078463#32, 0x63#8, 0x84#8, 0x07#8, 0x00#8, .br bop.BEQ false, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_800079b8 : List BBlock := [⟨[], some (⟨0x800079b8#64, 0x4880206f#32, 0x6f#8, 0x20#8, 0x80#8, 0x48#8, .j, 0, 0, 0x0#13, 0x2488#21, 0#12⟩ : TInstr)⟩]
def nx_800079bc : List BBlock := [{ body := [mkLine 0x800079bc#64 0x00813783#32], term := none }]
def nx_800079c0 : List BBlock := [{ body := [mkLine 0x800079c0#64 0x0107d783#32], term := none }]
def nx_800079c4 : List BBlock := [{ body := [mkLine 0x800079c4#64 0x0407f793#32], term := none }]
def nx_800079c8 : List BBlock := [{ body := [mkLine 0x800079c8#64 0x23013903#32], term := none }]
def nx_800079cc : List BBlock := [{ body := [mkLine 0x800079cc#64 0x22813983#32], term := none }]
def nx_800079d0 : List BBlock := [{ body := [mkLine 0x800079d0#64 0x22013a03#32], term := none }]
def nx_800079d4 : List BBlock := [{ body := [mkLine 0x800079d4#64 0x21813a83#32], term := none }]
def nx_800079d8 : List BBlock := [{ body := [mkLine 0x800079d8#64 0x20813b83#32], term := none }]
def nx_800079dc : List BBlock := [{ body := [mkLine 0x800079dc#64 0x20013c03#32], term := none }]
def nx_800079e0 : List BBlock := [{ body := [mkLine 0x800079e0#64 0x1f813c83#32], term := none }]
def nx_800079e4 : List BBlock := [{ body := [mkLine 0x800079e4#64 0x1f013d03#32], term := none }]
def nx_800079e8 : List BBlock := [{ body := [mkLine 0x800079e8#64 0x1e813d83#32], term := none }]
def nxT_800079ec : List BBlock := [⟨[], some (⟨0x800079ec#64, 0x00078463#32, 0x63#8, 0x84#8, 0x07#8, 0x00#8, .br bop.BEQ true, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_800079ec : List BBlock := [⟨[], some (⟨0x800079ec#64, 0x00078463#32, 0x63#8, 0x84#8, 0x07#8, 0x00#8, .br bop.BEQ false, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_800079f4 : List BBlock := [{ body := [mkLine 0x800079f4#64 0x24813083#32], term := none }]
def nx_800079f8 : List BBlock := [{ body := [mkLine 0x800079f8#64 0x24013403#32], term := none }]
def nx_800079fc : List BBlock := [{ body := [mkLine 0x800079fc#64 0x01013503#32], term := none }]
def nx_80007a00 : List BBlock := [{ body := [mkLine 0x80007a00#64 0x23813483#32], term := none }]
def nx_80007a04 : List BBlock := [{ body := [mkLine 0x80007a04#64 0x21013b03#32], term := none }]
def nx_80007a08 : List BBlock := [{ body := [mkLine 0x80007a08#64 0x25010113#32], term := none }]
def nx_80007a0c : List BBlock := [⟨[], some (⟨0x80007a0c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem nt_800079b0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079b4#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079b0#64 R Mt :=
  swp_stepD nx_800079b0 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079b0 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem nt_800079b4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 15) = (0#64) → SnpW live Dt DA S Q 0x800079bc#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → SnpW live Dt DA S Q 0x800079b8#64 R Mt) :
    SnpW live Dt DA S Q 0x800079b4#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    swp_stepD nxT_800079b4 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_800079b4 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_800079b4 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_800079b4 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_800079b8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80009e40#64 R Mt) :
    SnpW live Dt DA S Q 0x800079b8#64 R Mt :=
  swp_stepD nx_800079b8 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079b8 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800079bc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079c0#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079bc#64 R Mt :=
  swp_stepD nx_800079bc [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079bc ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem nt_800079c0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : SnpW live Dt DA S Q 0x800079c4#64 (upd R 15 (ldv .lhu Mt ((R 15) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079c0#64 R Mt :=
  swp_stepD nx_800079c0 [15] [bytesAt (imgM Mt) ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 2] (accAddrs ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079c0 ChainFacts; chain_facts hm; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem nt_800079c4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800079c8#64 (upd R 15 ((R 15) &&& sign_extend (m := 64) (0x040#12))) Mt) :
    SnpW live Dt DA S Q 0x800079c4#64 R Mt :=
  swp_stepD nx_800079c4 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079c4 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem nt_800079c8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x230#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x230#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079cc#64 (upd R 18 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x230#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079c8#64 R Mt :=
  swp_stepD nx_800079c8 [2, 18] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x230#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x230#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079c8 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [2, 18])))) rfl hk

theorem nt_800079cc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x228#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x228#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079d0#64 (upd R 19 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x228#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079cc#64 R Mt :=
  swp_stepD nx_800079cc [2, 19] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x228#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x228#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079cc ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [2, 19])))) rfl hk

theorem nt_800079d0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x220#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x220#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079d4#64 (upd R 20 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x220#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079d0#64 R Mt :=
  swp_stepD nx_800079d0 [2, 20] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x220#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x220#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079d0 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [2, 20])))) rfl hk

theorem nt_800079d4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x218#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x218#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079d8#64 (upd R 21 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x218#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079d4#64 R Mt :=
  swp_stepD nx_800079d4 [2, 21] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x218#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x218#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079d4 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 21 ∈ [2, 21])))) rfl hk

theorem nt_800079d8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x208#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x208#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079dc#64 (upd R 23 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x208#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079d8#64 R Mt :=
  swp_stepD nx_800079d8 [2, 23] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x208#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x208#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079d8 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [2, 23])))) rfl hk

theorem nt_800079dc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x200#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x200#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079e0#64 (upd R 24 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x200#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079dc#64 R Mt :=
  swp_stepD nx_800079dc [2, 24] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x200#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x200#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079dc ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 24 ∈ [2, 24])))) rfl hk

theorem nt_800079e0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x1f8#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x1f8#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079e4#64 (upd R 25 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x1f8#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079e0#64 R Mt :=
  swp_stepD nx_800079e0 [2, 25] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x1f8#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x1f8#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079e0 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 25 ∈ [2, 25])))) rfl hk

theorem nt_800079e4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x1f0#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x1f0#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079e8#64 (upd R 26 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x1f0#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079e4#64 R Mt :=
  swp_stepD nx_800079e4 [2, 26] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x1f0#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x1f0#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079e4 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 26 ∈ [2, 26])))) rfl hk

theorem nt_800079e8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x1e8#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x1e8#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079ec#64 (upd R 27 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x1e8#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079e8#64 R Mt :=
  swp_stepD nx_800079e8 [2, 27] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x1e8#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x1e8#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079e8 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 27 ∈ [2, 27])))) rfl hk

theorem nt_800079ec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 15) = (0#64) → SnpW live Dt DA S Q 0x800079f4#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → SnpW live Dt DA S Q 0x800079f0#64 R Mt) :
    SnpW live Dt DA S Q 0x800079ec#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    swp_stepD nxT_800079ec [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_800079ec ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_800079ec [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_800079ec ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_800079f4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x248#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x248#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079f8#64 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x248#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079f4#64 R Mt :=
  swp_stepD nx_800079f4 [1, 2] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x248#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x248#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079f4 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 1 ∈ [1, 2])))) rfl hk

theorem nt_800079f8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x240#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x240#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079fc#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x240#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079f8#64 R Mt :=
  swp_stepD nx_800079f8 [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x240#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x240#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079f8 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem nt_800079fc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007a00#64 (upd R 10 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079fc#64 R Mt :=
  swp_stepD nx_800079fc [2, 10] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079fc ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [2, 10])))) rfl hk

theorem nt_80007a00 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x238#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x238#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007a04#64 (upd R 9 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x238#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80007a00#64 R Mt :=
  swp_stepD nx_80007a00 [2, 9] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x238#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x238#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007a00 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [2, 9])))) rfl hk

theorem nt_80007a04 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x210#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x210#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007a08#64 (upd R 22 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x210#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80007a04#64 R Mt :=
  swp_stepD nx_80007a04 [2, 22] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x210#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x210#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007a04 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [2, 22])))) rfl hk

theorem nt_80007a08 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007a0c#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0x250#12))) Mt) :
    SnpW live Dt DA S Q 0x80007a08#64 R Mt :=
  swp_stepD nx_80007a08 [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007a08 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem nt_80007a0c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : SnpW live Dt DA S Q (R 1) R Mt) :
    SnpW live Dt DA S Q 0x80007a0c#64 R Mt :=
  swp_stepD nx_80007a0c [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007a0c ChainFacts; chain_facts hm; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
