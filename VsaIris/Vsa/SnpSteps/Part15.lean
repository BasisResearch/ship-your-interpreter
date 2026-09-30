import VsaIris.Vsa.SnpRunDef
import VsaIris.Vsa.SymObs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def nx_80008ea4 : List BBlock := [{ body := [mkLine 0x80008ea4#64 0x0a714f03#32], term := none }]
def nx_80008ea8 : List BBlock := [{ body := [mkLine 0x80008ea8#64 0x00100813#32], term := none }]
def nx_80008eac : List BBlock := [{ body := [mkLine 0x80008eac#64 0x00000f93#32], term := none }]
def nx_80008eb0 : List BBlock := [{ body := [mkLine 0x80008eb0#64 0x00100b13#32], term := none }]
def nx_80008eb4 : List BBlock := [{ body := [mkLine 0x80008eb4#64 0x15b10d13#32], term := none }]
def nx_80008eb8 : List BBlock := [⟨[], some (⟨0x80008eb8#64, 0xa70ff06f#32, 0x6f#8, 0xf0#8, 0x0f#8, 0xa7#8, .j, 0, 0, 0x0#13, 0x1ff270#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem nt_80008ea4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1, S b)
    (hk : SnpW live Dt DA S Q 0x80008ea8#64 (upd R 30 (ldv .lbu Mt ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80008ea4#64 R Mt :=
  swp_stepD nx_80008ea4 [2, 30] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008ea4 ChainFacts; chain_facts hm; exact ⟨hea, lpins1_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 30 ∈ [2, 30])))) rfl hk

theorem nt_80008ea8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008eac#64 (upd R 16 ((0#64) + sign_extend (m := 64) (0x001#12))) Mt) :
    SnpW live Dt DA S Q 0x80008ea8#64 R Mt :=
  swp_stepD nx_80008ea8 [16] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008ea8 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 16 ∈ [16])))) rfl hk

theorem nt_80008eac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008eb0#64 (upd R 31 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80008eac#64 R Mt :=
  swp_stepD nx_80008eac [31] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008eac ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 31 ∈ [31])))) rfl hk

theorem nt_80008eb0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008eb4#64 (upd R 22 ((0#64) + sign_extend (m := 64) (0x001#12))) Mt) :
    SnpW live Dt DA S Q 0x80008eb0#64 R Mt :=
  swp_stepD nx_80008eb0 [22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008eb0 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [22])))) rfl hk

theorem nt_80008eb4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008eb8#64 (upd R 26 ((R 2) + sign_extend (m := 64) (0x15b#12))) Mt) :
    SnpW live Dt DA S Q 0x80008eb4#64 R Mt :=
  swp_stepD nx_80008eb4 [2, 26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008eb4 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 26 ∈ [2, 26])))) rfl hk

theorem nt_80008eb8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008128#64 R Mt) :
    SnpW live Dt DA S Q 0x80008eb8#64 R Mt :=
  swp_stepD nx_80008eb8 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008eb8 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
