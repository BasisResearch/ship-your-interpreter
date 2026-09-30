import VsaIris.Vsa.SnpRunDef
import VsaIris.Vsa.SymObs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def nx_80009060 : List BBlock := [{ body := [mkLine 0x80009060#64 0x001ccc03#32], term := none }]
def nx_80009064 : List BBlock := [{ body := [mkLine 0x80009064#64 0x02036313#32], term := none }]
def nx_80009068 : List BBlock := [{ body := [mkLine 0x80009068#64 0x001c8c93#32], term := none }]
def nx_8000906c : List BBlock := [⟨[], some (⟨0x8000906c#64, 0xf2cfe06f#32, 0x6f#8, 0xe0#8, 0xcf#8, 0xf2#8, .j, 0, 0, 0x0#13, 0x1fe72c#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem ntD_80009060 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 25) + sign_extend (m := 64) (0x001#12)).toNat 1)
    (hLDD : ∀ b ∈ accAddrs ((R 25) + sign_extend (m := 64) (0x001#12)).toNat 1, b ∈ DA)
    (hk : SnpW live Dt DA S Q 0x80009064#64 (upd R 24 (ldv .lbu Dt ((R 25) + sign_extend (m := 64) (0x001#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80009060#64 R Mt :=
  swp_stepD nx_80009060 [24, 25] [bytesAt (imgM Dt) ((R 25) + sign_extend (m := 64) (0x001#12)).toNat 1] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80009060 ChainFacts; chain_facts hm; exact ⟨hea, lpins1_img (fun b hb => dataReads_view hD b (hLDD b hb))⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 24 ∈ [24, 25])))) rfl hk

theorem nt_80009064 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80009068#64 (upd R 6 ((R 6) ||| sign_extend (m := 64) (0x020#12))) Mt) :
    SnpW live Dt DA S Q 0x80009064#64 R Mt :=
  swp_stepD nx_80009064 [6] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80009064 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 6 ∈ [6])))) rfl hk

theorem nt_80009068 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000906c#64 (upd R 25 ((R 25) + sign_extend (m := 64) (0x001#12))) Mt) :
    SnpW live Dt DA S Q 0x80009068#64 R Mt :=
  swp_stepD nx_80009068 [25] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80009068 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 25 ∈ [25])))) rfl hk

theorem nt_8000906c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007798#64 R Mt) :
    SnpW live Dt DA S Q 0x8000906c#64 R Mt :=
  swp_stepD nx_8000906c [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000906c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
