import VsaIris.Vsa.SnpRunDef
import VsaIris.Vsa.SymObs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def nx_800099c0 : List BBlock := [{ body := [mkLine 0x800099c0#64 0x20037693#32], term := none }]
def nxT_800099c4 : List BBlock := [⟨[], some (⟨0x800099c4#64, 0x46068263#32, 0x63#8, 0x82#8, 0x06#8, 0x46#8, .br bop.BEQ true, 13, 0, 0x464#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_800099c4 : List BBlock := [⟨[], some (⟨0x800099c4#64, 0x46068263#32, 0x63#8, 0x82#8, 0x06#8, 0x46#8, .br bop.BEQ false, 13, 0, 0x464#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem nt_800099c0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800099c4#64 (upd R 13 ((R 6) &&& sign_extend (m := 64) (0x200#12))) Mt) :
    SnpW live Dt DA S Q 0x800099c0#64 R Mt :=
  swp_stepD nx_800099c0 [6, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800099c0 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [6, 13])))) rfl hk

theorem nt_800099c4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 13) = (0#64) → SnpW live Dt DA S Q 0x80009e28#64 R Mt) (hF : ¬ ((R 13) = (0#64)) → SnpW live Dt DA S Q 0x800099c8#64 R Mt) :
    SnpW live Dt DA S Q 0x800099c4#64 R Mt := by
  by_cases hc : (R 13) = (0#64)
  · exact
    swp_stepD nxT_800099c4 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_800099c4 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_800099c4 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_800099c4 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

end VsaIris.Sym
