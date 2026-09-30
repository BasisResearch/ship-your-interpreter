import VsaIris.Vsa.SnpRunDef
import VsaIris.Vsa.SymObs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def nx_80007cd4 : List BBlock := [{ body := [mkLine 0x80007cd4#64 0x410e073b#32], term := none }]
def nxT_80007cd8 : List BBlock := [⟨[], some (⟨0x80007cd8#64, 0x76e040e3#32, 0xe3#8, 0x40#8, 0xe0#8, 0x76#8, .br bop.BLT true, 0, 14, 0xf60#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007cd8 : List BBlock := [⟨[], some (⟨0x80007cd8#64, 0x76e040e3#32, 0xe3#8, 0x40#8, 0xe0#8, 0x76#8, .br bop.BLT false, 0, 14, 0xf60#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80007cdc : List BBlock := [{ body := [mkLine 0x80007cdc#64 0x0a714703#32], term := none }]
def nxT_80007ce0 : List BBlock := [⟨[], some (⟨0x80007ce0#64, 0xb60712e3#32, 0xe3#8, 0x12#8, 0x07#8, 0xb6#8, .br bop.BNE true, 14, 0, 0x1b64#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007ce0 : List BBlock := [⟨[], some (⟨0x80007ce0#64, 0xb60712e3#32, 0xe3#8, 0x12#8, 0x07#8, 0xb6#8, .br bop.BNE false, 14, 0, 0x1b64#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80007ce4 : List BBlock := [{ body := [mkLine 0x80007ce4#64 0x416a0a3b#32], term := none }]
def nxT_80007ce8 : List BBlock := [⟨[], some (⟨0x80007ce8#64, 0xbd405ae3#32, 0xe3#8, 0x5a#8, 0x40#8, 0xbd#8, .br bop.BGE true, 0, 20, 0x1bd4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007ce8 : List BBlock := [⟨[], some (⟨0x80007ce8#64, 0xbd405ae3#32, 0xe3#8, 0x5a#8, 0x40#8, 0xbd#8, .br bop.BGE false, 0, 20, 0x1bd4#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem nt_80007cd4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007cd8#64 (upd R 14 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 28) 31 0) - (Sail.BitVec.extractLsb (R 16) 31 0)))) Mt) :
    SnpW live Dt DA S Q 0x80007cd4#64 R Mt :=
  swp_stepD nx_80007cd4 [14, 16, 28] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007cd4 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 16, 28])))) rfl hk

theorem nt_80007cd8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (0#64).toInt < (R 14).toInt → SnpW live Dt DA S Q 0x80008c38#64 R Mt) (hF : ¬ ((0#64).toInt < (R 14).toInt) → SnpW live Dt DA S Q 0x80007cdc#64 R Mt) :
    SnpW live Dt DA S Q 0x80007cd8#64 R Mt := by
  by_cases hc : (0#64).toInt < (R 14).toInt
  · exact
    swp_stepD nxT_80007cd8 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007cd8 ChainFacts; chain_facts hm; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007cd8 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007cd8 ChainFacts; chain_facts hm; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80007cdc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1, S b)
    (hk : SnpW live Dt DA S Q 0x80007ce0#64 (upd R 14 (ldv .lbu Mt ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80007cdc#64 R Mt :=
  swp_stepD nx_80007cdc [2, 14] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007cdc ChainFacts; chain_facts hm; exact ⟨hea, lpins1_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [2, 14])))) rfl hk

theorem nt_80007ce0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 14) ≠ (0#64) → SnpW live Dt DA S Q 0x80007844#64 R Mt) (hF : ¬ ((R 14) ≠ (0#64)) → SnpW live Dt DA S Q 0x80007ce4#64 R Mt) :
    SnpW live Dt DA S Q 0x80007ce0#64 R Mt := by
  by_cases hc : (R 14) ≠ (0#64)
  · exact
    swp_stepD nxT_80007ce0 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007ce0 ChainFacts; chain_facts hm; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007ce0 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007ce0 ChainFacts; chain_facts hm; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80007ce4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007ce8#64 (upd R 20 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 20) 31 0) - (Sail.BitVec.extractLsb (R 22) 31 0)))) Mt) :
    SnpW live Dt DA S Q 0x80007ce4#64 R Mt :=
  swp_stepD nx_80007ce4 [20, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007ce4 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [20, 22])))) rfl hk

theorem nt_80007ce8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 20).toInt ≤ (0#64).toInt → SnpW live Dt DA S Q 0x800078bc#64 R Mt) (hF : ¬ ((R 20).toInt ≤ (0#64).toInt) → SnpW live Dt DA S Q 0x80007cec#64 R Mt) :
    SnpW live Dt DA S Q 0x80007ce8#64 R Mt := by
  by_cases hc : (R 20).toInt ≤ (0#64).toInt
  · exact
    swp_stepD nxT_80007ce8 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007ce8 ChainFacts; chain_facts hm; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007ce8 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007ce8 ChainFacts; chain_facts hm; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

end VsaIris.Sym
