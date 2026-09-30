import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000e0ac : List BBlock := [{ body := [mkLine 0x8000e0ac#64 0x0004bb03#32], term := none }]
def ix_8000e0b0 : List BBlock := [{ body := [mkLine 0x8000e0b0#64 0x0084b983#32], term := none }]
def ix_8000e0b4 : List BBlock := [{ body := [mkLine 0x8000e0b4#64 0x01048493#32], term := none }]
def ix_8000e0b8 : List BBlock := [⟨[], some (⟨0x8000e0b8#64, 0xf09ff06f#32, 0x6f#8, 0xf0#8, 0x9f#8, 0xf0#8, .j, 0, 0, 0x0#13, 0x1fff08#21, 0#12⟩ : TInstr)⟩]
def ix_8000e0bc : List BBlock := [{ body := [mkLine 0x8000e0bc#64 0x0004b983#32], term := none }]
def ix_8000e0c0 : List BBlock := [{ body := [mkLine 0x8000e0c0#64 0x0084b903#32], term := none }]
def ix_8000e0c4 : List BBlock := [{ body := [mkLine 0x8000e0c4#64 0x01048493#32], term := none }]
def ix_8000e0c8 : List BBlock := [⟨[], some (⟨0x8000e0c8#64, 0xe2dff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xe2#8, .j, 0, 0, 0x0#13, 0x1ffe2c#21, 0#12⟩ : TInstr)⟩]
def ix_8000e0cc : List BBlock := [{ body := [mkLine 0x8000e0cc#64 0x00000513#32], term := none }]
def ix_8000e0d0 : List BBlock := [⟨[], some (⟨0x8000e0d0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_8000e0ac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 9) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 9) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e0b0#64 (upd R 22 (ldv .ld Mt ((R 9) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e0ac#64 R Mt :=
  swp_stepD ix_8000e0ac [9, 22] [bytesAt (imgM Mt) ((R 9) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 9) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e0ac ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [9, 22])))) rfl hk

theorem it_8000e0b0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e0b4#64 (upd R 19 (ldv .ld Mt ((R 9) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e0b0#64 R Mt :=
  swp_stepD ix_8000e0b0 [9, 19] [bytesAt (imgM Mt) ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e0b0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [9, 19])))) rfl hk

theorem it_8000e0b4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e0b8#64 (upd R 9 ((R 9) + sign_extend (m := 64) (0x010#12))) Mt) :
    NW live Dt DA S Q 0x8000e0b4#64 R Mt :=
  swp_stepD ix_8000e0b4 [9] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e0b4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9])))) rfl hk

theorem it_8000e0b8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000dfc0#64 R Mt) :
    NW live Dt DA S Q 0x8000e0b8#64 R Mt :=
  swp_stepD ix_8000e0b8 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e0b8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000e0bc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 9) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 9) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e0c0#64 (upd R 19 (ldv .ld Mt ((R 9) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e0bc#64 R Mt :=
  swp_stepD ix_8000e0bc [9, 19] [bytesAt (imgM Mt) ((R 9) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 9) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e0bc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [9, 19])))) rfl hk

theorem it_8000e0c0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e0c4#64 (upd R 18 (ldv .ld Mt ((R 9) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e0c0#64 R Mt :=
  swp_stepD ix_8000e0c0 [9, 18] [bytesAt (imgM Mt) ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e0c0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [9, 18])))) rfl hk

theorem it_8000e0c4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e0c8#64 (upd R 9 ((R 9) + sign_extend (m := 64) (0x010#12))) Mt) :
    NW live Dt DA S Q 0x8000e0c4#64 R Mt :=
  swp_stepD ix_8000e0c4 [9] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e0c4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9])))) rfl hk

theorem it_8000e0c8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000def4#64 R Mt) :
    NW live Dt DA S Q 0x8000e0c8#64 R Mt :=
  swp_stepD ix_8000e0c8 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e0c8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000e0cc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e0d0#64 (upd R 10 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000e0cc#64 R Mt :=
  swp_stepD ix_8000e0cc [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e0cc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem it_8000e0d0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : NW live Dt DA S Q (R 1) R Mt) :
    NW live Dt DA S Q 0x8000e0d0#64 R Mt :=
  swp_stepD ix_8000e0d0 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e0d0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
