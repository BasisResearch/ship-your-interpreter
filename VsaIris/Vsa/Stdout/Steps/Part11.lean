import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000b32c : List BBlock := [{ body := [mkLine 0x8000b32c#64 0x01813783#32], term := none }]
def ix_8000b330 : List BBlock := [{ body := [mkLine 0x8000b330#64 0x0a0103a3#32], term := none }]
def ix_8000b334 : List BBlock := [{ body := [mkLine 0x8000b334#64 0x000a0e13#32], term := none }]
def ix_8000b338 : List BBlock := [{ body := [mkLine 0x8000b338#64 0x0007bc83#32], term := none }]
def ix_8000b33c : List BBlock := [{ body := [mkLine 0x8000b33c#64 0x00040e93#32], term := none }]
def ix_8000b340 : List BBlock := [{ body := [mkLine 0x8000b340#64 0x00878a13#32], term := none }]
def ixT_8000b344 : List BBlock := [⟨[], some (⟨0x8000b344#64, 0x780c8ee3#32, 0xe3#8, 0x8e#8, 0x0c#8, 0x78#8, .br bop.BEQ true, 25, 0, 0xf9c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000b344 : List BBlock := [⟨[], some (⟨0x8000b344#64, 0x780c8ee3#32, 0xe3#8, 0x8e#8, 0x0c#8, 0x78#8, .br bop.BEQ false, 25, 0, 0xf9c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000b348 : List BBlock := [{ body := [mkLine 0x8000b348#64 0x05300713#32], term := none }]
def ixT_8000b34c : List BBlock := [⟨[], some (⟨0x8000b34c#64, 0x00e89463#32, 0x63#8, 0x94#8, 0xe8#8, 0x00#8, .br bop.BNE true, 17, 14, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000b34c : List BBlock := [⟨[], some (⟨0x8000b34c#64, 0x00e89463#32, 0x63#8, 0x94#8, 0xe8#8, 0x00#8, .br bop.BNE false, 17, 14, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000b354 : List BBlock := [{ body := [mkLine 0x8000b354#64 0x010e7313#32], term := none }]
def ixT_8000b358 : List BBlock := [⟨[], some (⟨0x8000b358#64, 0x00030463#32, 0x63#8, 0x04#8, 0x03#8, 0x00#8, .br bop.BEQ true, 6, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000b358 : List BBlock := [⟨[], some (⟨0x8000b358#64, 0x00030463#32, 0x63#8, 0x04#8, 0x03#8, 0x00#8, .br bop.BEQ false, 6, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixT_8000b360 : List BBlock := [⟨[], some (⟨0x8000b360#64, 0x000b5463#32, 0x63#8, 0x54#8, 0x0b#8, 0x00#8, .br bop.BGE true, 22, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000b360 : List BBlock := [⟨[], some (⟨0x8000b360#64, 0x000b5463#32, 0x63#8, 0x54#8, 0x0b#8, 0x00#8, .br bop.BGE false, 22, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000b364 : List BBlock := [⟨[], some (⟨0x8000b364#64, 0x4550106f#32, 0x6f#8, 0x10#8, 0x50#8, 0x45#8, .j, 0, 0, 0x0#13, 0x1c54#21, 0#12⟩ : TInstr)⟩]
def ix_8000b3b4 : List BBlock := [{ body := [mkLine 0x8000b3b4#64 0x0006071b#32], term := none }]
def ixT_8000b3b8 : List BBlock := [⟨[], some (⟨0x8000b3b8#64, 0x00058463#32, 0x63#8, 0x84#8, 0x05#8, 0x00#8, .br bop.BEQ true, 11, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000b3b8 : List BBlock := [⟨[], some (⟨0x8000b3b8#64, 0x00058463#32, 0x63#8, 0x84#8, 0x05#8, 0x00#8, .br bop.BEQ false, 11, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000b3c0 : List BBlock := [{ body := [mkLine 0x8000b3c0#64 0x01413c23#32], term := none }]
def ix_8000b3c4 : List BBlock := [{ body := [mkLine 0x8000b3c4#64 0x00000b13#32], term := none }]
def ix_8000b3c8 : List BBlock := [{ body := [mkLine 0x8000b3c8#64 0x00000a13#32], term := none }]
def ix_8000b3cc : List BBlock := [{ body := [mkLine 0x8000b3cc#64 0x02013823#32], term := none }]
def ix_8000b3d0 : List BBlock := [{ body := [mkLine 0x8000b3d0#64 0x02013023#32], term := none }]
def ix_8000b3d4 : List BBlock := [{ body := [mkLine 0x8000b3d4#64 0x07300893#32], term := none }]
def ix_8000b3d8 : List BBlock := [⟨[], some (⟨0x8000b3d8#64, 0xedcff06f#32, 0x6f#8, 0xf0#8, 0xcf#8, 0xed#8, .j, 0, 0, 0x0#13, 0x1ff6dc#21, 0#12⟩ : TInstr)⟩]
def ix_8000b3ec : List BBlock := [{ body := [mkLine 0x8000b3ec#64 0x01813703#32], term := none }]
def ix_8000b3f0 : List BBlock := [{ body := [mkLine 0x8000b3f0#64 0x00073683#32], term := none }]
def ix_8000b3f4 : List BBlock := [{ body := [mkLine 0x8000b3f4#64 0x00f13c23#32], term := none }]
def ix_8000b3f8 : List BBlock := [{ body := [mkLine 0x8000b3f8#64 0x00068d13#32], term := none }]
def ixT_8000b3fc : List BBlock := [⟨[], some (⟨0x8000b3fc#64, 0xba06d6e3#32, 0xe3#8, 0xd6#8, 0x06#8, 0xba#8, .br bop.BGE true, 13, 0, 0x1bac#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000b3fc : List BBlock := [⟨[], some (⟨0x8000b3fc#64, 0xba06d6e3#32, 0xe3#8, 0xd6#8, 0x06#8, 0xba#8, .br bop.BGE false, 13, 0, 0x1bac#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000b400 : List BBlock := [{ body := [mkLine 0x8000b400#64 0x02d00793#32], term := none }]
def ix_8000b404 : List BBlock := [{ body := [mkLine 0x8000b404#64 0x0af103a3#32], term := none }]
def ix_8000b408 : List BBlock := [{ body := [mkLine 0x8000b408#64 0x41a00d33#32], term := none }]
def ixT_8000b40c : List BBlock := [⟨[], some (⟨0x8000b40c#64, 0x000b4463#32, 0x63#8, 0x44#8, 0x0b#8, 0x00#8, .br bop.BLT true, 22, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000b40c : List BBlock := [⟨[], some (⟨0x8000b40c#64, 0x000b4463#32, 0x63#8, 0x44#8, 0x0b#8, 0x00#8, .br bop.BLT false, 22, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000b414 : List BBlock := [{ body := [mkLine 0x8000b414#64 0x00900793#32], term := none }]
def ixT_8000b418 : List BBlock := [⟨[], some (⟨0x8000b418#64, 0x01a7f463#32, 0x63#8, 0xf4#8, 0xa7#8, 0x01#8, .br bop.BGEU true, 15, 26, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000b418 : List BBlock := [⟨[], some (⟨0x8000b418#64, 0x01a7f463#32, 0x63#8, 0xf4#8, 0xa7#8, 0x01#8, .br bop.BGEU false, 15, 26, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000b41c : List BBlock := [⟨[], some (⟨0x8000b41c#64, 0x6100106f#32, 0x6f#8, 0x10#8, 0x00#8, 0x61#8, .j, 0, 0, 0x0#13, 0x1610#21, 0#12⟩ : TInstr)⟩]
def ix_8000b420 : List BBlock := [{ body := [mkLine 0x8000b420#64 0x030d071b#32], term := none }]
def ix_8000b424 : List BBlock := [{ body := [mkLine 0x8000b424#64 0x14e10da3#32], term := none }]
def ix_8000b428 : List BBlock := [{ body := [mkLine 0x8000b428#64 0x000b071b#32], term := none }]
def ixT_8000b42c : List BBlock := [⟨[], some (⟨0x8000b42c#64, 0x4f605ee3#32, 0xe3#8, 0x5e#8, 0x60#8, 0x4f#8, .br bop.BGE true, 0, 22, 0xcfc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000b42c : List BBlock := [⟨[], some (⟨0x8000b42c#64, 0x4f605ee3#32, 0xe3#8, 0x5e#8, 0x60#8, 0x4f#8, .br bop.BGE false, 0, 22, 0xcfc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000b440 : List BBlock := [{ body := [mkLine 0x8000b440#64 0x02013023#32], term := none }]
def ixT_8000b444 : List BBlock := [⟨[], some (⟨0x8000b444#64, 0xb80f0ee3#32, 0xe3#8, 0x0e#8, 0x0f#8, 0xb8#8, .br bop.BEQ true, 30, 0, 0x1b9c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000b444 : List BBlock := [⟨[], some (⟨0x8000b444#64, 0xb80f0ee3#32, 0xe3#8, 0x0e#8, 0x0f#8, 0xb8#8, .br bop.BEQ false, 30, 0, 0x1b9c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000b448 : List BBlock := [{ body := [mkLine 0x8000b448#64 0x0017071b#32], term := none }]
def ix_8000b44c : List BBlock := [⟨[], some (⟨0x8000b44c#64, 0xb95ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xb9#8, .j, 0, 0, 0x0#13, 0x1ffb94#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_8000b32c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000b330#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000b32c#64 R Mt :=
  swp_stepD ix_8000b32c [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b32c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem it_8000b330 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOKb ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1, S b)
    (hk : NW live Dt DA S Q 0x8000b334#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat, 1, (0#64))])) :
    NW live Dt DA S Q 0x8000b330#64 R Mt :=
  swp_stepD ix_8000b330 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000b330 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000b334 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b338#64 (upd R 28 ((R 20) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000b334#64 R Mt :=
  swp_stepD ix_8000b334 [20, 28] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b334 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 28 ∈ [20, 28])))) rfl hk

theorem it_8000b338 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 15) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 15) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000b33c#64 (upd R 25 (ldv .ld Mt ((R 15) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000b338#64 R Mt :=
  swp_stepD ix_8000b338 [15, 25] [bytesAt (imgM Mt) ((R 15) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 15) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b338 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 25 ∈ [15, 25])))) rfl hk

theorem it_8000b33c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b340#64 (upd R 29 ((R 8) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000b33c#64 R Mt :=
  swp_stepD ix_8000b33c [8, 29] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b33c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 29 ∈ [8, 29])))) rfl hk

theorem it_8000b340 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b344#64 (upd R 20 ((R 15) + sign_extend (m := 64) (0x008#12))) Mt) :
    NW live Dt DA S Q 0x8000b340#64 R Mt :=
  swp_stepD ix_8000b340 [15, 20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b340 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [15, 20])))) rfl hk

theorem it_8000b344 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 25) = (0#64) → NW live Dt DA S Q 0x8000c2e0#64 R Mt) (hF : ¬ ((R 25) = (0#64)) → NW live Dt DA S Q 0x8000b348#64 R Mt) :
    NW live Dt DA S Q 0x8000b344#64 R Mt := by
  by_cases hc : (R 25) = (0#64)
  · exact
    swp_stepD ixT_8000b344 [25] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000b344 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000b344 [25] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000b344 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000b348 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b34c#64 (upd R 14 ((0#64) + sign_extend (m := 64) (0x053#12))) Mt) :
    NW live Dt DA S Q 0x8000b348#64 R Mt :=
  swp_stepD ix_8000b348 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b348 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem it_8000b34c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 17) ≠ (R 14) → NW live Dt DA S Q 0x8000b354#64 R Mt) (hF : ¬ ((R 17) ≠ (R 14)) → NW live Dt DA S Q 0x8000b350#64 R Mt) :
    NW live Dt DA S Q 0x8000b34c#64 R Mt := by
  by_cases hc : (R 17) ≠ (R 14)
  · exact
    swp_stepD ixT_8000b34c [14, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000b34c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000b34c [14, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000b34c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000b354 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b358#64 (upd R 6 ((R 28) &&& sign_extend (m := 64) (0x010#12))) Mt) :
    NW live Dt DA S Q 0x8000b354#64 R Mt :=
  swp_stepD ix_8000b354 [6, 28] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b354 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 6 ∈ [6, 28])))) rfl hk

theorem it_8000b358 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 6) = (0#64) → NW live Dt DA S Q 0x8000b360#64 R Mt) (hF : ¬ ((R 6) = (0#64)) → NW live Dt DA S Q 0x8000b35c#64 R Mt) :
    NW live Dt DA S Q 0x8000b358#64 R Mt := by
  by_cases hc : (R 6) = (0#64)
  · exact
    swp_stepD ixT_8000b358 [6] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000b358 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000b358 [6] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000b358 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000b360 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (0#64).toInt ≤ (R 22).toInt → NW live Dt DA S Q 0x8000b368#64 R Mt) (hF : ¬ ((0#64).toInt ≤ (R 22).toInt) → NW live Dt DA S Q 0x8000b364#64 R Mt) :
    NW live Dt DA S Q 0x8000b360#64 R Mt := by
  by_cases hc : (0#64).toInt ≤ (R 22).toInt
  · exact
    swp_stepD ixT_8000b360 [22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000b360 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000b360 [22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000b360 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000b364 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000cfb8#64 R Mt) :
    NW live Dt DA S Q 0x8000b364#64 R Mt :=
  swp_stepD ix_8000b364 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b364 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000b3b4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b3b8#64 (upd R 14 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 12) + sign_extend (m := 64) (0x000#12)) 31 0))) Mt) :
    NW live Dt DA S Q 0x8000b3b4#64 R Mt :=
  swp_stepD ix_8000b3b4 [12, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b3b4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [12, 14])))) rfl hk

theorem it_8000b3b8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 11) = (0#64) → NW live Dt DA S Q 0x8000b3c0#64 R Mt) (hF : ¬ ((R 11) = (0#64)) → NW live Dt DA S Q 0x8000b3bc#64 R Mt) :
    NW live Dt DA S Q 0x8000b3b8#64 R Mt := by
  by_cases hc : (R 11) = (0#64)
  · exact
    swp_stepD ixT_8000b3b8 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000b3b8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000b3b8 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000b3b8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000b3c0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000b3c4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 20))])) :
    NW live Dt DA S Q 0x8000b3c0#64 R Mt :=
  swp_stepD ix_8000b3c0 [2, 20] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000b3c0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000b3c4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b3c8#64 (upd R 22 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000b3c4#64 R Mt :=
  swp_stepD ix_8000b3c4 [22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b3c4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [22])))) rfl hk

theorem it_8000b3c8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b3cc#64 (upd R 20 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000b3c8#64 R Mt :=
  swp_stepD ix_8000b3c8 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b3c8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [20])))) rfl hk

theorem it_8000b3cc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000b3d0#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x030#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000b3cc#64 R Mt :=
  swp_stepD ix_8000b3cc [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000b3cc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000b3d0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000b3d4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000b3d0#64 R Mt :=
  swp_stepD ix_8000b3d0 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000b3d0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000b3d4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b3d8#64 (upd R 17 ((0#64) + sign_extend (m := 64) (0x073#12))) Mt) :
    NW live Dt DA S Q 0x8000b3d4#64 R Mt :=
  swp_stepD ix_8000b3d4 [17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b3d4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 17 ∈ [17])))) rfl hk

theorem it_8000b3d8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000aab4#64 R Mt) :
    NW live Dt DA S Q 0x8000b3d8#64 R Mt :=
  swp_stepD ix_8000b3d8 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b3d8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000b3ec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000b3f0#64 (upd R 14 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000b3ec#64 R Mt :=
  swp_stepD ix_8000b3ec [2, 14] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b3ec ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [2, 14])))) rfl hk

theorem it_8000b3f0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000b3f4#64 (upd R 13 (ldv .ld Mt ((R 14) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000b3f0#64 R Mt :=
  swp_stepD ix_8000b3f0 [13, 14] [bytesAt (imgM Mt) ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b3f0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13, 14])))) rfl hk

theorem it_8000b3f4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000b3f8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 15))])) :
    NW live Dt DA S Q 0x8000b3f4#64 R Mt :=
  swp_stepD ix_8000b3f4 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000b3f4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000b3f8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b3fc#64 (upd R 26 ((R 13) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000b3f8#64 R Mt :=
  swp_stepD ix_8000b3f8 [13, 26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b3f8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 26 ∈ [13, 26])))) rfl hk

theorem it_8000b3fc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (0#64).toInt ≤ (R 13).toInt → NW live Dt DA S Q 0x8000afa8#64 R Mt) (hF : ¬ ((0#64).toInt ≤ (R 13).toInt) → NW live Dt DA S Q 0x8000b400#64 R Mt) :
    NW live Dt DA S Q 0x8000b3fc#64 R Mt := by
  by_cases hc : (0#64).toInt ≤ (R 13).toInt
  · exact
    swp_stepD ixT_8000b3fc [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000b3fc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000b3fc [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000b3fc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000b400 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b404#64 (upd R 15 ((0#64) + sign_extend (m := 64) (0x02d#12))) Mt) :
    NW live Dt DA S Q 0x8000b400#64 R Mt :=
  swp_stepD ix_8000b400 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b400 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_8000b404 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOKb ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1, S b)
    (hk : NW live Dt DA S Q 0x8000b408#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat, 1, (R 15))])) :
    NW live Dt DA S Q 0x8000b404#64 R Mt :=
  swp_stepD ix_8000b404 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000b404 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000b408 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b40c#64 (upd R 26 ((0#64) - (R 26))) Mt) :
    NW live Dt DA S Q 0x8000b408#64 R Mt :=
  swp_stepD ix_8000b408 [26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b408 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 26 ∈ [26])))) rfl hk

theorem it_8000b40c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 22).toInt < (0#64).toInt → NW live Dt DA S Q 0x8000b414#64 R Mt) (hF : ¬ ((R 22).toInt < (0#64).toInt) → NW live Dt DA S Q 0x8000b410#64 R Mt) :
    NW live Dt DA S Q 0x8000b40c#64 R Mt := by
  by_cases hc : (R 22).toInt < (0#64).toInt
  · exact
    swp_stepD ixT_8000b40c [22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000b40c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000b40c [22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000b40c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000b414 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b418#64 (upd R 15 ((0#64) + sign_extend (m := 64) (0x009#12))) Mt) :
    NW live Dt DA S Q 0x8000b414#64 R Mt :=
  swp_stepD ix_8000b414 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b414 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_8000b418 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 26).toNat ≤ (R 15).toNat → NW live Dt DA S Q 0x8000b420#64 R Mt) (hF : ¬ ((R 26).toNat ≤ (R 15).toNat) → NW live Dt DA S Q 0x8000b41c#64 R Mt) :
    NW live Dt DA S Q 0x8000b418#64 R Mt := by
  by_cases hc : (R 26).toNat ≤ (R 15).toNat
  · exact
    swp_stepD ixT_8000b418 [15, 26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000b418 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bgeu _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000b418 [15, 26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000b418 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bgeu _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000b41c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca2c#64 R Mt) :
    NW live Dt DA S Q 0x8000b41c#64 R Mt :=
  swp_stepD ix_8000b41c [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b41c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000b420 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b424#64 (upd R 14 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 26) + sign_extend (m := 64) (0x030#12)) 31 0))) Mt) :
    NW live Dt DA S Q 0x8000b420#64 R Mt :=
  swp_stepD ix_8000b420 [14, 26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b420 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 26])))) rfl hk

theorem it_8000b424 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOKb ((R 2) + sign_extend (m := 64) (0x15b#12)).toNat)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x15b#12)).toNat 1, S b)
    (hk : NW live Dt DA S Q 0x8000b428#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x15b#12)).toNat, 1, (R 14))])) :
    NW live Dt DA S Q 0x8000b424#64 R Mt :=
  swp_stepD ix_8000b424 [2, 14] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x15b#12)).toNat 1) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000b424 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000b428 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b42c#64 (upd R 14 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 22) + sign_extend (m := 64) (0x000#12)) 31 0))) Mt) :
    NW live Dt DA S Q 0x8000b428#64 R Mt :=
  swp_stepD ix_8000b428 [14, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b428 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 22])))) rfl hk

theorem it_8000b42c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 22).toInt ≤ (0#64).toInt → NW live Dt DA S Q 0x8000c128#64 R Mt) (hF : ¬ ((R 22).toInt ≤ (0#64).toInt) → NW live Dt DA S Q 0x8000b430#64 R Mt) :
    NW live Dt DA S Q 0x8000b42c#64 R Mt := by
  by_cases hc : (R 22).toInt ≤ (0#64).toInt
  · exact
    swp_stepD ixT_8000b42c [22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000b42c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000b42c [22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000b42c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000b440 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000b444#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000b440#64 R Mt :=
  swp_stepD ix_8000b440 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000b440 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000b444 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 30) = (0#64) → NW live Dt DA S Q 0x8000afe0#64 R Mt) (hF : ¬ ((R 30) = (0#64)) → NW live Dt DA S Q 0x8000b448#64 R Mt) :
    NW live Dt DA S Q 0x8000b444#64 R Mt := by
  by_cases hc : (R 30) = (0#64)
  · exact
    swp_stepD ixT_8000b444 [30] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000b444 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000b444 [30] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000b444 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000b448 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b44c#64 (upd R 14 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 14) + sign_extend (m := 64) (0x001#12)) 31 0))) Mt) :
    NW live Dt DA S Q 0x8000b448#64 R Mt :=
  swp_stepD ix_8000b448 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b448 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem it_8000b44c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000afe0#64 R Mt) :
    NW live Dt DA S Q 0x8000b44c#64 R Mt :=
  swp_stepD ix_8000b44c [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000b44c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
