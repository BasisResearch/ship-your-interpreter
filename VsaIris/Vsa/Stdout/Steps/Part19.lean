import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000c2c0 : List BBlock := [{ body := [mkLine 0x8000c2c0#64 0x001c4883#32], term := none }]
def ix_8000c2c4 : List BBlock := [{ body := [mkLine 0x8000c2c4#64 0x020a6a13#32], term := none }]
def ix_8000c2c8 : List BBlock := [{ body := [mkLine 0x8000c2c8#64 0x001c0c13#32], term := none }]
def ix_8000c2cc : List BBlock := [⟨[], some (⟨0x8000c2cc#64, 0xf54fe06f#32, 0x6f#8, 0xe0#8, 0x4f#8, 0xf5#8, .j, 0, 0, 0x0#13, 0x1fe754#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem itD_8000c2c0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 24) + sign_extend (m := 64) (0x001#12)).toNat 1)
    (hLDD : ∀ b ∈ accAddrs ((R 24) + sign_extend (m := 64) (0x001#12)).toNat 1, b ∈ DA)
    (hk : NW live Dt DA S Q 0x8000c2c4#64 (upd R 17 (ldv .lbu Dt ((R 24) + sign_extend (m := 64) (0x001#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000c2c0#64 R Mt :=
  swp_stepD ix_8000c2c0 [17, 24] [bytesAt (imgM Dt) ((R 24) + sign_extend (m := 64) (0x001#12)).toNat 1] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000c2c0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins1_img (fun b hb => dataReads_view hD b (hLDD b hb))⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 17 ∈ [17, 24])))) rfl hk

theorem it_8000c2c4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000c2c8#64 (upd R 20 ((R 20) ||| sign_extend (m := 64) (0x020#12))) Mt) :
    NW live Dt DA S Q 0x8000c2c4#64 R Mt :=
  swp_stepD ix_8000c2c4 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000c2c4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [20])))) rfl hk

theorem it_8000c2c8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000c2cc#64 (upd R 24 ((R 24) + sign_extend (m := 64) (0x001#12))) Mt) :
    NW live Dt DA S Q 0x8000c2c8#64 R Mt :=
  swp_stepD ix_8000c2c8 [24] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000c2c8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 24 ∈ [24])))) rfl hk

theorem it_8000c2cc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000aa20#64 R Mt) :
    NW live Dt DA S Q 0x8000c2cc#64 R Mt :=
  swp_stepD ix_8000c2cc [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000c2cc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
