import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000b6a4 : List BBlock := [{ body := [mkLine 0x8000b6a4#64 0x000c4883#32], term := none }]
def ix_8000b6a8 : List BBlock := [{ body := [mkLine 0x8000b6a8#64 0x06c00793#32], term := none }]
def ixT_8000b6ac : List BBlock := [⟨[], some (⟨0x8000b6ac#64, 0x40f88ae3#32, 0xe3#8, 0x8a#8, 0xf8#8, 0x40#8, .br bop.BEQ true, 17, 15, 0xc14#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000b6ac : List BBlock := [⟨[], some (⟨0x8000b6ac#64, 0x40f88ae3#32, 0xe3#8, 0x8a#8, 0xf8#8, 0x40#8, .br bop.BEQ false, 17, 15, 0xc14#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem itD_8000b6a4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 24) + sign_extend (m := 64) (0x000#12)).toNat 1)
    (hLDD : ∀ b ∈ accAddrs ((R 24) + sign_extend (m := 64) (0x000#12)).toNat 1, b ∈ DA)
    (hk : NW live Dt DA S Q 0x8000b6a8#64 (upd R 17 (ldv .lbu Dt ((R 24) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000b6a4#64 R Mt :=
  swp_stepD ix_8000b6a4 [17, 24] [bytesAt (imgM Dt) ((R 24) + sign_extend (m := 64) (0x000#12)).toNat 1] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b6a4 ChainFacts; chain_facts hm; exact ⟨hea, lpins1_img (fun b hb => dataReads_view hD b (hLDD b hb))⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 17 ∈ [17, 24])))) rfl hk

theorem it_8000b6a8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b6ac#64 (upd R 15 ((0#64) + sign_extend (m := 64) (0x06c#12))) Mt) :
    NW live Dt DA S Q 0x8000b6a8#64 R Mt :=
  swp_stepD ix_8000b6a8 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b6a8 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_8000b6ac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 17) = (R 15) → NW live Dt DA S Q 0x8000c2c0#64 R Mt) (hF : ¬ ((R 17) = (R 15)) → NW live Dt DA S Q 0x8000b6b0#64 R Mt) :
    NW live Dt DA S Q 0x8000b6ac#64 R Mt := by
  by_cases hc : (R 17) = (R 15)
  · exact
    swp_stepD ixT_8000b6ac [15, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000b6ac ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000b6ac [15, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000b6ac ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

end VsaIris.Sym
