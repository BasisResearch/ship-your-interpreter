import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000c128 : List BBlock := [{ body := [mkLine 0x8000c128#64 0x0a714f03#32], term := none }]
def ix_8000c12c : List BBlock := [{ body := [mkLine 0x8000c12c#64 0x00100713#32], term := none }]
def ix_8000c130 : List BBlock := [{ body := [mkLine 0x8000c130#64 0x00000313#32], term := none }]
def ix_8000c134 : List BBlock := [{ body := [mkLine 0x8000c134#64 0x00100693#32], term := none }]
def ix_8000c138 : List BBlock := [{ body := [mkLine 0x8000c138#64 0x15b10c93#32], term := none }]
def ix_8000c13c : List BBlock := [⟨[], some (⟨0x8000c13c#64, 0xb04ff06f#32, 0x6f#8, 0xf0#8, 0x4f#8, 0xb0#8, .j, 0, 0, 0x0#13, 0x1ff304#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_8000c128 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1, S b)
    (hk : NW live Dt DA S Q 0x8000c12c#64 (upd R 30 (ldv .lbu Mt ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000c128#64 R Mt :=
  swp_stepD ix_8000c128 [2, 30] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000c128 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins1_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 30 ∈ [2, 30])))) rfl hk

theorem it_8000c12c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000c130#64 (upd R 14 ((0#64) + sign_extend (m := 64) (0x001#12))) Mt) :
    NW live Dt DA S Q 0x8000c12c#64 R Mt :=
  swp_stepD ix_8000c12c [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000c12c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem it_8000c130 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000c134#64 (upd R 6 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000c130#64 R Mt :=
  swp_stepD ix_8000c130 [6] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000c130 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 6 ∈ [6])))) rfl hk

theorem it_8000c134 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000c138#64 (upd R 13 ((0#64) + sign_extend (m := 64) (0x001#12))) Mt) :
    NW live Dt DA S Q 0x8000c134#64 R Mt :=
  swp_stepD ix_8000c134 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000c134 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13])))) rfl hk

theorem it_8000c138 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000c13c#64 (upd R 25 ((R 2) + sign_extend (m := 64) (0x15b#12))) Mt) :
    NW live Dt DA S Q 0x8000c138#64 R Mt :=
  swp_stepD ix_8000c138 [2, 25] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000c138 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 25 ∈ [2, 25])))) rfl hk

theorem it_8000c13c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b440#64 R Mt) :
    NW live Dt DA S Q 0x8000c13c#64 R Mt :=
  swp_stepD ix_8000c13c [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000c13c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
