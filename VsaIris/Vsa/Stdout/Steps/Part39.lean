import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc
import Vsa.Sim.DecodeNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000e8cc : List BBlock := [{ body := [mkLine 0x8000e8cc#64 0x01063703#32], term := none }]
def ixT_8000e8d0 : List BBlock := [⟨[], some (⟨0x8000e8d0#64, 0x00071863#32, 0x63#8, 0x18#8, 0x07#8, 0x00#8, .br bop.BNE true, 14, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000e8d0 : List BBlock := [⟨[], some (⟨0x8000e8d0#64, 0x00071863#32, 0x63#8, 0x18#8, 0x07#8, 0x00#8, .br bop.BNE false, 14, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000e8d4 : List BBlock := [{ body := [mkLine 0x8000e8d4#64 0x00000513#32], term := none }]
def ix_8000e8d8 : List BBlock := [{ body := [mkLine 0x8000e8d8#64 0x00062423#32], term := none }]
def ix_8000e8dc : List BBlock := [⟨[], some (⟨0x8000e8dc#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000e8e0 : List BBlock := [{ body := [mkLine 0x8000e8e0#64 0xfe010113#32], term := none }]
def ix_8000e8e4 : List BBlock := [{ body := [mkLine 0x8000e8e4#64 0x00113c23#32], term := none }]
def ix_8000e8e8 : List BBlock := [{ body := [mkLine 0x8000e8e8#64 0x00c13423#32], term := none }]
def ix_8000e8f0 : List BBlock := [{ body := [mkLine 0x8000e8f0#64 0x00813783#32], term := none }]
def ix_8000e8f4 : List BBlock := [{ body := [mkLine 0x8000e8f4#64 0x01813083#32], term := none }]
def ix_8000e8f8 : List BBlock := [{ body := [mkLine 0x8000e8f8#64 0x0007b823#32], term := none }]
def ix_8000e8fc : List BBlock := [{ body := [mkLine 0x8000e8fc#64 0x0007a423#32], term := none }]
def ix_8000e900 : List BBlock := [{ body := [mkLine 0x8000e900#64 0x02010113#32], term := none }]
def ix_8000e904 : List BBlock := [⟨[], some (⟨0x8000e904#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000e9f8 : List BBlock := [{ body := [mkLine 0x8000e9f8#64 0xfe010113#32], term := none }]
def ix_8000e9fc : List BBlock := [{ body := [mkLine 0x8000e9fc#64 0x00113c23#32], term := none }]
def ix_8000ea00 : List BBlock := [{ body := [mkLine 0x8000ea00#64 0x01213023#32], term := none }]
def ixT_8000ea04 : List BBlock := [⟨[], some (⟨0x8000ea04#64, 0x0e058263#32, 0x63#8, 0x82#8, 0x05#8, 0x0e#8, .br bop.BEQ true, 11, 0, 0xe4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ea04 : List BBlock := [⟨[], some (⟨0x8000ea04#64, 0x0e058263#32, 0x63#8, 0x82#8, 0x05#8, 0x0e#8, .br bop.BEQ false, 11, 0, 0xe4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ea08 : List BBlock := [{ body := [mkLine 0x8000ea08#64 0x00813823#32], term := none }]
def ix_8000ea0c : List BBlock := [{ body := [mkLine 0x8000ea0c#64 0x00913423#32], term := none }]
def ix_8000ea10 : List BBlock := [{ body := [mkLine 0x8000ea10#64 0x00058413#32], term := none }]
def ix_8000ea14 : List BBlock := [{ body := [mkLine 0x8000ea14#64 0x00050493#32], term := none }]
def ixT_8000ea18 : List BBlock := [⟨[], some (⟨0x8000ea18#64, 0x00050663#32, 0x63#8, 0x06#8, 0x05#8, 0x00#8, .br bop.BEQ true, 10, 0, 0xc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ea18 : List BBlock := [⟨[], some (⟨0x8000ea18#64, 0x00050663#32, 0x63#8, 0x06#8, 0x05#8, 0x00#8, .br bop.BEQ false, 10, 0, 0xc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ea1c : List BBlock := [{ body := [mkLine 0x8000ea1c#64 0x04853783#32], term := none }]
def ixT_8000ea20 : List BBlock := [⟨[], some (⟨0x8000ea20#64, 0x10078063#32, 0x63#8, 0x80#8, 0x07#8, 0x10#8, .br bop.BEQ true, 15, 0, 0x100#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ea20 : List BBlock := [⟨[], some (⟨0x8000ea20#64, 0x10078063#32, 0x63#8, 0x80#8, 0x07#8, 0x10#8, .br bop.BEQ false, 15, 0, 0x100#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ea24 : List BBlock := [{ body := [mkLine 0x8000ea24#64 0x0b042783#32], term := none }]
def ix_8000ea28 : List BBlock := [{ body := [mkLine 0x8000ea28#64 0x01041703#32], term := none }]
def ix_8000ea2c : List BBlock := [{ body := [mkLine 0x8000ea2c#64 0x0017f793#32], term := none }]
def ixT_8000ea30 : List BBlock := [⟨[], some (⟨0x8000ea30#64, 0x0a079663#32, 0x63#8, 0x96#8, 0x07#8, 0x0a#8, .br bop.BNE true, 15, 0, 0xac#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ea30 : List BBlock := [⟨[], some (⟨0x8000ea30#64, 0x0a079663#32, 0x63#8, 0x96#8, 0x07#8, 0x0a#8, .br bop.BNE false, 15, 0, 0xac#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ea34 : List BBlock := [{ body := [mkLine 0x8000ea34#64 0x20077713#32], term := none }]
def ixT_8000ea38 : List BBlock := [⟨[], some (⟨0x8000ea38#64, 0x0e070863#32, 0x63#8, 0x08#8, 0x07#8, 0x0e#8, .br bop.BEQ true, 14, 0, 0xf0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ea38 : List BBlock := [⟨[], some (⟨0x8000ea38#64, 0x0e070863#32, 0x63#8, 0x08#8, 0x07#8, 0x0e#8, .br bop.BEQ false, 14, 0, 0xf0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ea3c : List BBlock := [{ body := [mkLine 0x8000ea3c#64 0x00040593#32], term := none }]
def ix_8000ea40 : List BBlock := [{ body := [mkLine 0x8000ea40#64 0x00048513#32], term := none }]
def ix_8000ea48 : List BBlock := [{ body := [mkLine 0x8000ea48#64 0x05043783#32], term := none }]
def ix_8000ea4c : List BBlock := [{ body := [mkLine 0x8000ea4c#64 0x00050913#32], term := none }]
def ixT_8000ea50 : List BBlock := [⟨[], some (⟨0x8000ea50#64, 0x00078a63#32, 0x63#8, 0x8a#8, 0x07#8, 0x00#8, .br bop.BEQ true, 15, 0, 0x14#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ea50 : List BBlock := [⟨[], some (⟨0x8000ea50#64, 0x00078a63#32, 0x63#8, 0x8a#8, 0x07#8, 0x00#8, .br bop.BEQ false, 15, 0, 0x14#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ea54 : List BBlock := [{ body := [mkLine 0x8000ea54#64 0x03043583#32], term := none }]
def ix_8000ea58 : List BBlock := [{ body := [mkLine 0x8000ea58#64 0x00048513#32], term := none }]
def ixT_8000ea60 : List BBlock := [⟨[], some (⟨0x8000ea60#64, 0x0a054063#32, 0x63#8, 0x40#8, 0x05#8, 0x0a#8, .br bop.BLT true, 10, 0, 0xa0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ea60 : List BBlock := [⟨[], some (⟨0x8000ea60#64, 0x0a054063#32, 0x63#8, 0x40#8, 0x05#8, 0x0a#8, .br bop.BLT false, 10, 0, 0xa0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ea64 : List BBlock := [{ body := [mkLine 0x8000ea64#64 0x01045783#32], term := none }]
def ix_8000ea68 : List BBlock := [{ body := [mkLine 0x8000ea68#64 0x0807f793#32], term := none }]
def ixT_8000ea6c : List BBlock := [⟨[], some (⟨0x8000ea6c#64, 0x0a079263#32, 0x63#8, 0x92#8, 0x07#8, 0x0a#8, .br bop.BNE true, 15, 0, 0xa4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ea6c : List BBlock := [⟨[], some (⟨0x8000ea6c#64, 0x0a079263#32, 0x63#8, 0x92#8, 0x07#8, 0x0a#8, .br bop.BNE false, 15, 0, 0xa4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ea70 : List BBlock := [{ body := [mkLine 0x8000ea70#64 0x05843583#32], term := none }]
def ixT_8000ea74 : List BBlock := [⟨[], some (⟨0x8000ea74#64, 0x00058c63#32, 0x63#8, 0x8c#8, 0x05#8, 0x00#8, .br bop.BEQ true, 11, 0, 0x18#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ea74 : List BBlock := [⟨[], some (⟨0x8000ea74#64, 0x00058c63#32, 0x63#8, 0x8c#8, 0x05#8, 0x00#8, .br bop.BEQ false, 11, 0, 0x18#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ea8c : List BBlock := [{ body := [mkLine 0x8000ea8c#64 0x07843583#32], term := none }]
def ixT_8000ea90 : List BBlock := [⟨[], some (⟨0x8000ea90#64, 0x00058863#32, 0x63#8, 0x88#8, 0x05#8, 0x00#8, .br bop.BEQ true, 11, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ea90 : List BBlock := [⟨[], some (⟨0x8000ea90#64, 0x00058863#32, 0x63#8, 0x88#8, 0x05#8, 0x00#8, .br bop.BEQ false, 11, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000eaa4 : List BBlock := [{ body := [mkLine 0x8000eaa4#64 0x0b042783#32], term := none }]
def ix_8000eaa8 : List BBlock := [{ body := [mkLine 0x8000eaa8#64 0x00041823#32], term := none }]
def ix_8000eaac : List BBlock := [{ body := [mkLine 0x8000eaac#64 0x0017f793#32], term := none }]
def ixT_8000eab0 : List BBlock := [⟨[], some (⟨0x8000eab0#64, 0x0a078463#32, 0x63#8, 0x84#8, 0x07#8, 0x0a#8, .br bop.BEQ true, 15, 0, 0xa8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000eab0 : List BBlock := [⟨[], some (⟨0x8000eab0#64, 0x0a078463#32, 0x63#8, 0x84#8, 0x07#8, 0x0a#8, .br bop.BEQ false, 15, 0, 0xa8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000eab4 : List BBlock := [{ body := [mkLine 0x8000eab4#64 0x0a043503#32], term := none }]
def ix_8000eac0 : List BBlock := [{ body := [mkLine 0x8000eac0#64 0x01813083#32], term := none }]
def ix_8000eac4 : List BBlock := [{ body := [mkLine 0x8000eac4#64 0x01013403#32], term := none }]
def ix_8000eac8 : List BBlock := [{ body := [mkLine 0x8000eac8#64 0x00813483#32], term := none }]
def ix_8000eacc : List BBlock := [{ body := [mkLine 0x8000eacc#64 0x00090513#32], term := none }]
def ix_8000ead0 : List BBlock := [{ body := [mkLine 0x8000ead0#64 0x00013903#32], term := none }]
def ix_8000ead4 : List BBlock := [{ body := [mkLine 0x8000ead4#64 0x02010113#32], term := none }]
def ix_8000ead8 : List BBlock := [⟨[], some (⟨0x8000ead8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000eb28 : List BBlock := [{ body := [mkLine 0x8000eb28#64 0x0a043503#32], term := none }]
def ix_8000eb30 : List BBlock := [{ body := [mkLine 0x8000eb30#64 0x01041783#32], term := none }]
def ixT_8000eb34 : List BBlock := [⟨[], some (⟨0x8000eb34#64, 0xf00794e3#32, 0xe3#8, 0x94#8, 0x07#8, 0xf0#8, .br bop.BNE true, 15, 0, 0x1f08#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000eb34 : List BBlock := [⟨[], some (⟨0x8000eb34#64, 0xf00794e3#32, 0xe3#8, 0x94#8, 0x07#8, 0xf0#8, .br bop.BNE false, 15, 0, 0x1f08#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000eb58 : List BBlock := [{ body := [mkLine 0x8000eb58#64 0x0a043503#32], term := none }]
def ix_8000eb60 : List BBlock := [⟨[], some (⟨0x8000eb60#64, 0xf55ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf5#8, .j, 0, 0, 0x0#13, 0x1fff54#21, 0#12⟩ : TInstr)⟩]
def ix_8000eb70 : List BBlock := [{ body := [mkLine 0x8000eb70#64 0x01059703#32], term := none }]
def ix_8000eb74 : List BBlock := [{ body := [mkLine 0x8000eb74#64 0xfd010113#32], term := none }]
def ix_8000eb78 : List BBlock := [{ body := [mkLine 0x8000eb78#64 0x02813023#32], term := none }]
def ix_8000eb7c : List BBlock := [{ body := [mkLine 0x8000eb7c#64 0x01313423#32], term := none }]
def ix_8000eb80 : List BBlock := [{ body := [mkLine 0x8000eb80#64 0x02113423#32], term := none }]
def ix_8000eb84 : List BBlock := [{ body := [mkLine 0x8000eb84#64 0x00877793#32], term := none }]
def ix_8000eb88 : List BBlock := [{ body := [mkLine 0x8000eb88#64 0x00058413#32], term := none }]
def ix_8000eb8c : List BBlock := [{ body := [mkLine 0x8000eb8c#64 0x00050993#32], term := none }]
def ixT_8000eb90 : List BBlock := [⟨[], some (⟨0x8000eb90#64, 0x12079263#32, 0x63#8, 0x92#8, 0x07#8, 0x12#8, .br bop.BNE true, 15, 0, 0x124#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000eb90 : List BBlock := [⟨[], some (⟨0x8000eb90#64, 0x12079263#32, 0x63#8, 0x92#8, 0x07#8, 0x12#8, .br bop.BNE false, 15, 0, 0x124#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000eb94 : List BBlock := [{ body := [mkLine 0x8000eb94#64 0x000017b7#32], term := none }]
def ix_8000eb98 : List BBlock := [{ body := [mkLine 0x8000eb98#64 0x80078793#32], term := none }]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_8000e8cc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 12) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 12) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e8d0#64 (upd R 14 (ldv .ld Mt ((R 12) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e8cc#64 R Mt :=
  swp_stepD ix_8000e8cc [12, 14] [bytesAt (imgM Mt) ((R 12) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 12) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e8cc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [12, 14])))) rfl hk

theorem it_8000e8d0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 14) ≠ (0#64) → NW live Dt DA S Q 0x8000e8e0#64 R Mt) (hF : ¬ ((R 14) ≠ (0#64)) → NW live Dt DA S Q 0x8000e8d4#64 R Mt) :
    NW live Dt DA S Q 0x8000e8d0#64 R Mt := by
  by_cases hc : (R 14) ≠ (0#64)
  · exact
    swp_stepD ixT_8000e8d0 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000e8d0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000e8d0 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000e8d0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000e8d4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e8d8#64 (upd R 10 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000e8d4#64 R Mt :=
  swp_stepD ix_8000e8d4 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e8d4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem it_8000e8d8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 12) + sign_extend (m := 64) (0x008#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 12) + sign_extend (m := 64) (0x008#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000e8dc#64 R (writeLog Mt [(((R 12) + sign_extend (m := 64) (0x008#12)).toNat, 4, (0#64))])) :
    NW live Dt DA S Q 0x8000e8d8#64 R Mt :=
  swp_stepD ix_8000e8d8 [12] [] [] (accAddrs ((R 12) + sign_extend (m := 64) (0x008#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000e8d8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000e8dc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : NW live Dt DA S Q (R 1) R Mt) :
    NW live Dt DA S Q 0x8000e8dc#64 R Mt :=
  swp_stepD ix_8000e8dc [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e8dc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000e8e0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e8e4#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0xfe0#12))) Mt) :
    NW live Dt DA S Q 0x8000e8e0#64 R Mt :=
  swp_stepD ix_8000e8e0 [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e8e0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem it_8000e8e4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e8e8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 1))])) :
    NW live Dt DA S Q 0x8000e8e4#64 R Mt :=
  swp_stepD ix_8000e8e4 [1, 2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000e8e4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000e8e8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e8ec#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 12))])) :
    NW live Dt DA S Q 0x8000e8e8#64 R Mt :=
  swp_stepD ix_8000e8e8 [2, 12] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000e8e8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000e8ec (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000e8ec [0xef#8, 0xf0#8, 0x0f#8, 0xda#8], live p.1) :
    JalExec (vsaModel live) 0x8000e8ec [0xef#8, 0xf0#8, 0x0f#8, 0xda#8] 0x8000de8c#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000e8ec, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000e8ed, .discard, 0xf0#8) (by simp [codeFoot])
  have hb2 := hb (0x8000e8ee, .discard, 0x0f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000e8ef, .discard, 0xda#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000e8ec#64) vm (0xda0ff0ef#32) (0x1ff5a0#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000e8ec#64) 4)
      (0xef#8) (0xf0#8) (0x0f#8) (0xda#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xda0ff0ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000e8ec#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x8000de8c#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000e8ec#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000e8ec + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000e8ec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000de8c#64 (upd R 1 (BitVec.ofNat 64 (0x8000e8ec + 4))) Mt) :
    NW live Dt DA S Q 0x8000e8ec#64 R Mt :=
  swp_jal 0x8000e8ec [0xef#8, 0xf0#8, 0x0f#8, 0xda#8] 0x8000de8c#64 (jalx_8000e8ec live (fun p hp => hlive _ (stdio_code_8000e8ec p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000e8ec p hp)) (by decide) (by decide) rfl hk

theorem it_8000e8f0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e8f4#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e8f0#64 R Mt :=
  swp_stepD ix_8000e8f0 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e8f0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem it_8000e8f4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e8f8#64 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e8f4#64 R Mt :=
  swp_stepD ix_8000e8f4 [1, 2] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e8f4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 1 ∈ [1, 2])))) rfl hk

theorem it_8000e8f8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e8fc#64 R (writeLog Mt [(((R 15) + sign_extend (m := 64) (0x010#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000e8f8#64 R Mt :=
  swp_stepD ix_8000e8f8 [15] [] [] (accAddrs ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000e8f8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000e8fc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 15) + sign_extend (m := 64) (0x008#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 15) + sign_extend (m := 64) (0x008#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000e900#64 R (writeLog Mt [(((R 15) + sign_extend (m := 64) (0x008#12)).toNat, 4, (0#64))])) :
    NW live Dt DA S Q 0x8000e8fc#64 R Mt :=
  swp_stepD ix_8000e8fc [15] [] [] (accAddrs ((R 15) + sign_extend (m := 64) (0x008#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000e8fc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000e900 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e904#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0x020#12))) Mt) :
    NW live Dt DA S Q 0x8000e900#64 R Mt :=
  swp_stepD ix_8000e900 [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e900 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem it_8000e904 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : NW live Dt DA S Q (R 1) R Mt) :
    NW live Dt DA S Q 0x8000e904#64 R Mt :=
  swp_stepD ix_8000e904 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e904 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000e9f8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e9fc#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0xfe0#12))) Mt) :
    NW live Dt DA S Q 0x8000e9f8#64 R Mt :=
  swp_stepD ix_8000e9f8 [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e9f8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem it_8000e9fc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ea00#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 1))])) :
    NW live Dt DA S Q 0x8000e9fc#64 R Mt :=
  swp_stepD ix_8000e9fc [1, 2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000e9fc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ea00 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ea04#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x000#12)).toNat, 8, (R 18))])) :
    NW live Dt DA S Q 0x8000ea00#64 R Mt :=
  swp_stepD ix_8000ea00 [2, 18] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ea00 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ea04 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 11) = (0#64) → NW live Dt DA S Q 0x8000eae8#64 R Mt) (hF : ¬ ((R 11) = (0#64)) → NW live Dt DA S Q 0x8000ea08#64 R Mt) :
    NW live Dt DA S Q 0x8000ea04#64 R Mt := by
  by_cases hc : (R 11) = (0#64)
  · exact
    swp_stepD ixT_8000ea04 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ea04 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ea04 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ea04 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ea08 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ea0c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 8))])) :
    NW live Dt DA S Q 0x8000ea08#64 R Mt :=
  swp_stepD ix_8000ea08 [2, 8] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ea08 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ea0c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ea10#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 9))])) :
    NW live Dt DA S Q 0x8000ea0c#64 R Mt :=
  swp_stepD ix_8000ea0c [2, 9] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ea0c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ea10 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ea14#64 (upd R 8 ((R 11) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ea10#64 R Mt :=
  swp_stepD ix_8000ea10 [8, 11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea10 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8, 11])))) rfl hk

theorem it_8000ea14 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ea18#64 (upd R 9 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ea14#64 R Mt :=
  swp_stepD ix_8000ea14 [9, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea14 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9, 10])))) rfl hk

theorem it_8000ea18 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 10) = (0#64) → NW live Dt DA S Q 0x8000ea24#64 R Mt) (hF : ¬ ((R 10) = (0#64)) → NW live Dt DA S Q 0x8000ea1c#64 R Mt) :
    NW live Dt DA S Q 0x8000ea18#64 R Mt := by
  by_cases hc : (R 10) = (0#64)
  · exact
    swp_stepD ixT_8000ea18 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ea18 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ea18 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ea18 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ea1c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 10) + sign_extend (m := 64) (0x048#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 10) + sign_extend (m := 64) (0x048#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ea20#64 (upd R 15 (ldv .ld Mt ((R 10) + sign_extend (m := 64) (0x048#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ea1c#64 R Mt :=
  swp_stepD ix_8000ea1c [10, 15] [bytesAt (imgM Mt) ((R 10) + sign_extend (m := 64) (0x048#12)).toNat 8] (accAddrs ((R 10) + sign_extend (m := 64) (0x048#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea1c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [10, 15])))) rfl hk

theorem it_8000ea20 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) = (0#64) → NW live Dt DA S Q 0x8000eb20#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → NW live Dt DA S Q 0x8000ea24#64 R Mt) :
    NW live Dt DA S Q 0x8000ea20#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    swp_stepD ixT_8000ea20 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ea20 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ea20 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ea20 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ea24 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000ea28#64 (upd R 15 (ldv .lw Mt ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ea24#64 R Mt :=
  swp_stepD ix_8000ea24 [8, 15] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4] (accAddrs ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea24 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [8, 15])))) rfl hk

theorem it_8000ea28 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000ea2c#64 (upd R 14 (ldv .lh Mt ((R 8) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ea28#64 R Mt :=
  swp_stepD ix_8000ea28 [8, 14] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2] (accAddrs ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea28 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [8, 14])))) rfl hk

theorem it_8000ea2c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ea30#64 (upd R 15 ((R 15) &&& sign_extend (m := 64) (0x001#12))) Mt) :
    NW live Dt DA S Q 0x8000ea2c#64 R Mt :=
  swp_stepD ix_8000ea2c [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea2c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_8000ea30 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) ≠ (0#64) → NW live Dt DA S Q 0x8000eadc#64 R Mt) (hF : ¬ ((R 15) ≠ (0#64)) → NW live Dt DA S Q 0x8000ea34#64 R Mt) :
    NW live Dt DA S Q 0x8000ea30#64 R Mt := by
  by_cases hc : (R 15) ≠ (0#64)
  · exact
    swp_stepD ixT_8000ea30 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ea30 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ea30 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ea30 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ea34 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ea38#64 (upd R 14 ((R 14) &&& sign_extend (m := 64) (0x200#12))) Mt) :
    NW live Dt DA S Q 0x8000ea34#64 R Mt :=
  swp_stepD ix_8000ea34 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea34 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem it_8000ea38 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 14) = (0#64) → NW live Dt DA S Q 0x8000eb28#64 R Mt) (hF : ¬ ((R 14) = (0#64)) → NW live Dt DA S Q 0x8000ea3c#64 R Mt) :
    NW live Dt DA S Q 0x8000ea38#64 R Mt := by
  by_cases hc : (R 14) = (0#64)
  · exact
    swp_stepD ixT_8000ea38 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ea38 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ea38 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ea38 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ea3c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ea40#64 (upd R 11 ((R 8) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ea3c#64 R Mt :=
  swp_stepD ix_8000ea3c [8, 11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea3c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [8, 11])))) rfl hk

theorem it_8000ea40 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ea44#64 (upd R 10 ((R 9) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ea40#64 R Mt :=
  swp_stepD ix_8000ea40 [9, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea40 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [9, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000ea44 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000ea44 [0xef#8, 0x00#8, 0xc0#8, 0x12#8], live p.1) :
    JalExec (vsaModel live) 0x8000ea44 [0xef#8, 0x00#8, 0xc0#8, 0x12#8] 0x8000eb70#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000ea44, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000ea45, .discard, 0x00#8) (by simp [codeFoot])
  have hb2 := hb (0x8000ea46, .discard, 0xc0#8) (by simp [codeFoot])
  have hb3 := hb (0x8000ea47, .discard, 0x12#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000ea44#64) vm (0x12c000ef#32) (0x00012c#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000ea44#64) 4)
      (0xef#8) (0x00#8) (0xc0#8) (0x12#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0x12c000ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000ea44#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x8000eb70#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000ea44#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000ea44 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000ea44 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000eb70#64 (upd R 1 (BitVec.ofNat 64 (0x8000ea44 + 4))) Mt) :
    NW live Dt DA S Q 0x8000ea44#64 R Mt :=
  swp_jal 0x8000ea44 [0xef#8, 0x00#8, 0xc0#8, 0x12#8] 0x8000eb70#64 (jalx_8000ea44 live (fun p hp => hlive _ (stdio_code_8000ea44 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000ea44 p hp)) (by decide) (by decide) rfl hk

theorem it_8000ea48 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x050#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x050#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ea4c#64 (upd R 15 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x050#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ea48#64 R Mt :=
  swp_stepD ix_8000ea48 [8, 15] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x050#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x050#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea48 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [8, 15])))) rfl hk

theorem it_8000ea4c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ea50#64 (upd R 18 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ea4c#64 R Mt :=
  swp_stepD ix_8000ea4c [10, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea4c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [10, 18])))) rfl hk

theorem it_8000ea50 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) = (0#64) → NW live Dt DA S Q 0x8000ea64#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → NW live Dt DA S Q 0x8000ea54#64 R Mt) :
    NW live Dt DA S Q 0x8000ea50#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    swp_stepD ixT_8000ea50 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ea50 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ea50 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ea50 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ea54 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ea58#64 (upd R 11 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x030#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ea54#64 R Mt :=
  swp_stepD ix_8000ea54 [8, 11] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x030#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x030#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea54 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [8, 11])))) rfl hk

theorem it_8000ea58 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ea5c#64 (upd R 10 ((R 9) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ea58#64 R Mt :=
  swp_stepD ix_8000ea58 [9, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea58 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [9, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem it_8000ea5c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (Sail.BitVec.update (R 15 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hk : NW live Dt DA S Q (Sail.BitVec.update (R 15 + sign_extend (m := 64) (0x000#12)) 0 0#1) (upd R 1 (BitVec.ofNat 64 (0x8000ea5c + 4))) Mt) :
    NW live Dt DA S Q 0x8000ea5c#64 R Mt :=
  swp_jalr 0x8000ea5c [0xe7#8, 0x80#8, 0x07#8, 0x00#8] [15] (Sail.BitVec.update (R 15 + sign_extend (m := 64) (0x000#12)) 0 0#1)
    (jalrStep_of_obs
      (fun q hq => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
        exact (show ∀ k ∈ [15], 1 ≤ k ∧ k ≤ 31 by decide) k hk)
      (fun p hp => hlive _ (stdio_code_8000ea5c p hp))
      (fun c hG hi hpc hRR hMR => by
      obtain ⟨vm, hmi⟩ := hG.minstret
      have hb0 := hMR (0x8000ea5c, .discard, 0xe7#8) (by simp [codeFoot])
      have hb1 := hMR (0x8000ea5d, .discard, 0x80#8) (by simp [codeFoot])
      have hb2 := hMR (0x8000ea5e, .discard, 0x07#8) (by simp [codeFoot])
      have hb3 := hMR (0x8000ea5f, .discard, 0x00#8) (by simp [codeFoot])
      obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
        stepObs_jalr c.σ c.tick c.steps (0x8000ea5c#64) vm (R 15) (0x000780e7#32) (0x000#12)
          (regidx.Regidx 0x0f#5) (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000ea5c#64) 4)
          (0xe7#8) (0x80#8) (0x07#8) (0x00#8)
          hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
          (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
          (Vsa.Sim.decodeW (w := 0x000780e7#32) (afterPrelude c.σ)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
          (rX_bits_x15 _ (R 15) (by rw [get?_afterNextPC c.σ (0x8000ea5c#64) _ (by decide) (by decide)]; exact hRR (15, Iris.DFrac.own 1, R 15) (by simp)))
          hal (by decide) (by decide) (by decide) (by decide) (by decide)
          (wX_bits_x1 _ (BitVec.addInt (0x8000ea5c#64) 4)) hi
      refine ⟨σ', i', vm, hs, hi', hG', hmem, ?_⟩
      rwa [show BitVec.addInt (0x8000ea5c#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000ea5c + 4) from by
        apply BitVec.eq_of_toNat_eq; decide] at hobs))
    (fun p hp => List.mem_append_left _ (stdio_code_8000ea5c p hp))
    (by decide) (by decide) (by decide) rfl hk

theorem it_8000ea60 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 10).toInt < (0#64).toInt → NW live Dt DA S Q 0x8000eb00#64 R Mt) (hF : ¬ ((R 10).toInt < (0#64).toInt) → NW live Dt DA S Q 0x8000ea64#64 R Mt) :
    NW live Dt DA S Q 0x8000ea60#64 R Mt := by
  by_cases hc : (R 10).toInt < (0#64).toInt
  · exact
    swp_stepD ixT_8000ea60 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ea60 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ea60 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ea60 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ea64 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000ea68#64 (upd R 15 (ldv .lhu Mt ((R 8) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ea64#64 R Mt :=
  swp_stepD ix_8000ea64 [8, 15] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2] (accAddrs ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea64 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [8, 15])))) rfl hk

theorem it_8000ea68 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ea6c#64 (upd R 15 ((R 15) &&& sign_extend (m := 64) (0x080#12))) Mt) :
    NW live Dt DA S Q 0x8000ea68#64 R Mt :=
  swp_stepD ix_8000ea68 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea68 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_8000ea6c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) ≠ (0#64) → NW live Dt DA S Q 0x8000eb10#64 R Mt) (hF : ¬ ((R 15) ≠ (0#64)) → NW live Dt DA S Q 0x8000ea70#64 R Mt) :
    NW live Dt DA S Q 0x8000ea6c#64 R Mt := by
  by_cases hc : (R 15) ≠ (0#64)
  · exact
    swp_stepD ixT_8000ea6c [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ea6c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ea6c [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ea6c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ea70 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x058#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x058#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ea74#64 (upd R 11 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x058#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ea70#64 R Mt :=
  swp_stepD ix_8000ea70 [8, 11] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x058#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x058#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea70 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [8, 11])))) rfl hk

theorem it_8000ea74 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 11) = (0#64) → NW live Dt DA S Q 0x8000ea8c#64 R Mt) (hF : ¬ ((R 11) = (0#64)) → NW live Dt DA S Q 0x8000ea78#64 R Mt) :
    NW live Dt DA S Q 0x8000ea74#64 R Mt := by
  by_cases hc : (R 11) = (0#64)
  · exact
    swp_stepD ixT_8000ea74 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ea74 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ea74 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ea74 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ea8c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x078#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x078#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ea90#64 (upd R 11 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x078#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ea8c#64 R Mt :=
  swp_stepD ix_8000ea8c [8, 11] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x078#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x078#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ea8c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [8, 11])))) rfl hk

theorem it_8000ea90 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 11) = (0#64) → NW live Dt DA S Q 0x8000eaa0#64 R Mt) (hF : ¬ ((R 11) = (0#64)) → NW live Dt DA S Q 0x8000ea94#64 R Mt) :
    NW live Dt DA S Q 0x8000ea90#64 R Mt := by
  by_cases hc : (R 11) = (0#64)
  · exact
    swp_stepD ixT_8000ea90 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ea90 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ea90 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ea90 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000eaa0 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000eaa0 [0xef#8, 0x70#8, 0x0f#8, 0xe8#8], live p.1) :
    JalExec (vsaModel live) 0x8000eaa0 [0xef#8, 0x70#8, 0x0f#8, 0xe8#8] 0x80006120#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000eaa0, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000eaa1, .discard, 0x70#8) (by simp [codeFoot])
  have hb2 := hb (0x8000eaa2, .discard, 0x0f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000eaa3, .discard, 0xe8#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000eaa0#64) vm (0xe80f70ef#32) (0x1f7680#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000eaa0#64) 4)
      (0xef#8) (0x70#8) (0x0f#8) (0xe8#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xe80f70ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000eaa0#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80006120#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000eaa0#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000eaa0 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000eaa0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80006120#64 (upd R 1 (BitVec.ofNat 64 (0x8000eaa0 + 4))) Mt) :
    NW live Dt DA S Q 0x8000eaa0#64 R Mt :=
  swp_jal 0x8000eaa0 [0xef#8, 0x70#8, 0x0f#8, 0xe8#8] 0x80006120#64 (jalx_8000eaa0 live (fun p hp => hlive _ (stdio_code_8000eaa0 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000eaa0 p hp)) (by decide) (by decide) rfl hk

theorem it_8000eaa4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000eaa8#64 (upd R 15 (ldv .lw Mt ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000eaa4#64 R Mt :=
  swp_stepD ix_8000eaa4 [8, 15] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4] (accAddrs ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eaa4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [8, 15])))) rfl hk

theorem it_8000eaa8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000eaac#64 R (writeLog Mt [(((R 8) + sign_extend (m := 64) (0x010#12)).toNat, 2, (0#64))])) :
    NW live Dt DA S Q 0x8000eaa8#64 R Mt :=
  swp_stepD ix_8000eaa8 [8] [] [] (accAddrs ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000eaa8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000eaac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000eab0#64 (upd R 15 ((R 15) &&& sign_extend (m := 64) (0x001#12))) Mt) :
    NW live Dt DA S Q 0x8000eaac#64 R Mt :=
  swp_stepD ix_8000eaac [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eaac ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_8000eab0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) = (0#64) → NW live Dt DA S Q 0x8000eb58#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → NW live Dt DA S Q 0x8000eab4#64 R Mt) :
    NW live Dt DA S Q 0x8000eab0#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    swp_stepD ixT_8000eab0 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000eab0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000eab0 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000eab0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000eab4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000eab8#64 (upd R 10 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000eab4#64 R Mt :=
  swp_stepD ix_8000eab4 [8, 10] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eab4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [8, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000eab8 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000eab8 [0xef#8, 0x80#8, 0x0f#8, 0xd2#8], live p.1) :
    JalExec (vsaModel live) 0x8000eab8 [0xef#8, 0x80#8, 0x0f#8, 0xd2#8] 0x80006fd8#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000eab8, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000eab9, .discard, 0x80#8) (by simp [codeFoot])
  have hb2 := hb (0x8000eaba, .discard, 0x0f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000eabb, .discard, 0xd2#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000eab8#64) vm (0xd20f80ef#32) (0x1f8520#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000eab8#64) 4)
      (0xef#8) (0x80#8) (0x0f#8) (0xd2#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xd20f80ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000eab8#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80006fd8#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000eab8#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000eab8 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000eab8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80006fd8#64 (upd R 1 (BitVec.ofNat 64 (0x8000eab8 + 4))) Mt) :
    NW live Dt DA S Q 0x8000eab8#64 R Mt :=
  swp_jal 0x8000eab8 [0xef#8, 0x80#8, 0x0f#8, 0xd2#8] 0x80006fd8#64 (jalx_8000eab8 live (fun p hp => hlive _ (stdio_code_8000eab8 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000eab8 p hp)) (by decide) (by decide) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000eabc (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000eabc [0xef#8, 0x70#8, 0xcf#8, 0xe6#8], live p.1) :
    JalExec (vsaModel live) 0x8000eabc [0xef#8, 0x70#8, 0xcf#8, 0xe6#8] 0x80006128#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000eabc, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000eabd, .discard, 0x70#8) (by simp [codeFoot])
  have hb2 := hb (0x8000eabe, .discard, 0xcf#8) (by simp [codeFoot])
  have hb3 := hb (0x8000eabf, .discard, 0xe6#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000eabc#64) vm (0xe6cf70ef#32) (0x1f766c#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000eabc#64) 4)
      (0xef#8) (0x70#8) (0xcf#8) (0xe6#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xe6cf70ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000eabc#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80006128#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000eabc#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000eabc + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000eabc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80006128#64 (upd R 1 (BitVec.ofNat 64 (0x8000eabc + 4))) Mt) :
    NW live Dt DA S Q 0x8000eabc#64 R Mt :=
  swp_jal 0x8000eabc [0xef#8, 0x70#8, 0xcf#8, 0xe6#8] 0x80006128#64 (jalx_8000eabc live (fun p hp => hlive _ (stdio_code_8000eabc p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000eabc p hp)) (by decide) (by decide) rfl hk

theorem it_8000eac0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000eac4#64 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000eac0#64 R Mt :=
  swp_stepD ix_8000eac0 [1, 2] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eac0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 1 ∈ [1, 2])))) rfl hk

theorem it_8000eac4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000eac8#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000eac4#64 R Mt :=
  swp_stepD ix_8000eac4 [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eac4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem it_8000eac8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000eacc#64 (upd R 9 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000eac8#64 R Mt :=
  swp_stepD ix_8000eac8 [2, 9] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eac8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [2, 9])))) rfl hk

theorem it_8000eacc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ead0#64 (upd R 10 ((R 18) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000eacc#64 R Mt :=
  swp_stepD ix_8000eacc [10, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eacc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 18])))) rfl hk

theorem it_8000ead0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ead4#64 (upd R 18 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ead0#64 R Mt :=
  swp_stepD ix_8000ead0 [2, 18] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ead0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [2, 18])))) rfl hk

theorem it_8000ead4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ead8#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0x020#12))) Mt) :
    NW live Dt DA S Q 0x8000ead4#64 R Mt :=
  swp_stepD ix_8000ead4 [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ead4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem it_8000ead8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : NW live Dt DA S Q (R 1) R Mt) :
    NW live Dt DA S Q 0x8000ead8#64 R Mt :=
  swp_stepD ix_8000ead8 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ead8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000eb28 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000eb2c#64 (upd R 10 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000eb28#64 R Mt :=
  swp_stepD ix_8000eb28 [8, 10] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eb28 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [8, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000eb2c (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000eb2c [0xef#8, 0x80#8, 0x4f#8, 0xcb#8], live p.1) :
    JalExec (vsaModel live) 0x8000eb2c [0xef#8, 0x80#8, 0x4f#8, 0xcb#8] 0x80006fe0#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000eb2c, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000eb2d, .discard, 0x80#8) (by simp [codeFoot])
  have hb2 := hb (0x8000eb2e, .discard, 0x4f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000eb2f, .discard, 0xcb#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000eb2c#64) vm (0xcb4f80ef#32) (0x1f84b4#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000eb2c#64) 4)
      (0xef#8) (0x80#8) (0x4f#8) (0xcb#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xcb4f80ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000eb2c#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80006fe0#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000eb2c#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000eb2c + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000eb2c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80006fe0#64 (upd R 1 (BitVec.ofNat 64 (0x8000eb2c + 4))) Mt) :
    NW live Dt DA S Q 0x8000eb2c#64 R Mt :=
  swp_jal 0x8000eb2c [0xef#8, 0x80#8, 0x4f#8, 0xcb#8] 0x80006fe0#64 (jalx_8000eb2c live (fun p hp => hlive _ (stdio_code_8000eb2c p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000eb2c p hp)) (by decide) (by decide) rfl hk

theorem it_8000eb30 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000eb34#64 (upd R 15 (ldv .lh Mt ((R 8) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000eb30#64 R Mt :=
  swp_stepD ix_8000eb30 [8, 15] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2] (accAddrs ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eb30 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [8, 15])))) rfl hk

theorem it_8000eb34 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) ≠ (0#64) → NW live Dt DA S Q 0x8000ea3c#64 R Mt) (hF : ¬ ((R 15) ≠ (0#64)) → NW live Dt DA S Q 0x8000eb38#64 R Mt) :
    NW live Dt DA S Q 0x8000eb34#64 R Mt := by
  by_cases hc : (R 15) ≠ (0#64)
  · exact
    swp_stepD ixT_8000eb34 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000eb34 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000eb34 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000eb34 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000eb58 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000eb5c#64 (upd R 10 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000eb58#64 R Mt :=
  swp_stepD ix_8000eb58 [8, 10] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x0a0#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eb58 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [8, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000eb5c (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000eb5c [0xef#8, 0x80#8, 0xcf#8, 0xc9#8], live p.1) :
    JalExec (vsaModel live) 0x8000eb5c [0xef#8, 0x80#8, 0xcf#8, 0xc9#8] 0x80006ff8#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000eb5c, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000eb5d, .discard, 0x80#8) (by simp [codeFoot])
  have hb2 := hb (0x8000eb5e, .discard, 0xcf#8) (by simp [codeFoot])
  have hb3 := hb (0x8000eb5f, .discard, 0xc9#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000eb5c#64) vm (0xc9cf80ef#32) (0x1f849c#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000eb5c#64) 4)
      (0xef#8) (0x80#8) (0xcf#8) (0xc9#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xc9cf80ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000eb5c#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80006ff8#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000eb5c#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000eb5c + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000eb5c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80006ff8#64 (upd R 1 (BitVec.ofNat 64 (0x8000eb5c + 4))) Mt) :
    NW live Dt DA S Q 0x8000eb5c#64 R Mt :=
  swp_jal 0x8000eb5c [0xef#8, 0x80#8, 0xcf#8, 0xc9#8] 0x80006ff8#64 (jalx_8000eb5c live (fun p hp => hlive _ (stdio_code_8000eb5c p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000eb5c p hp)) (by decide) (by decide) rfl hk

theorem it_8000eb60 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000eab4#64 R Mt) :
    NW live Dt DA S Q 0x8000eb60#64 R Mt :=
  swp_stepD ix_8000eb60 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eb60 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000eb70 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000eb74#64 (upd R 14 (ldv .lh Mt ((R 11) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000eb70#64 R Mt :=
  swp_stepD ix_8000eb70 [11, 14] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2] (accAddrs ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eb70 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [11, 14])))) rfl hk

theorem it_8000eb74 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000eb78#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0xfd0#12))) Mt) :
    NW live Dt DA S Q 0x8000eb74#64 R Mt :=
  swp_stepD ix_8000eb74 [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eb74 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem it_8000eb78 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000eb7c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (R 8))])) :
    NW live Dt DA S Q 0x8000eb78#64 R Mt :=
  swp_stepD ix_8000eb78 [2, 8] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000eb78 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000eb7c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000eb80#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 19))])) :
    NW live Dt DA S Q 0x8000eb7c#64 R Mt :=
  swp_stepD ix_8000eb7c [2, 19] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000eb7c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000eb80 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000eb84#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x028#12)).toNat, 8, (R 1))])) :
    NW live Dt DA S Q 0x8000eb80#64 R Mt :=
  swp_stepD ix_8000eb80 [1, 2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000eb80 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000eb84 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000eb88#64 (upd R 15 ((R 14) &&& sign_extend (m := 64) (0x008#12))) Mt) :
    NW live Dt DA S Q 0x8000eb84#64 R Mt :=
  swp_stepD ix_8000eb84 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eb84 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [14, 15])))) rfl hk

theorem it_8000eb88 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000eb8c#64 (upd R 8 ((R 11) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000eb88#64 R Mt :=
  swp_stepD ix_8000eb88 [8, 11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eb88 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8, 11])))) rfl hk

theorem it_8000eb8c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000eb90#64 (upd R 19 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000eb8c#64 R Mt :=
  swp_stepD ix_8000eb8c [10, 19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eb8c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [10, 19])))) rfl hk

theorem it_8000eb90 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) ≠ (0#64) → NW live Dt DA S Q 0x8000ecb4#64 R Mt) (hF : ¬ ((R 15) ≠ (0#64)) → NW live Dt DA S Q 0x8000eb94#64 R Mt) :
    NW live Dt DA S Q 0x8000eb90#64 R Mt := by
  by_cases hc : (R 15) ≠ (0#64)
  · exact
    swp_stepD ixT_8000eb90 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000eb90 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000eb90 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000eb90 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000eb94 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000eb98#64 (upd R 15 ((sign_extend (m := 64) ((0x00001#20) +++ (0x000#12))))) Mt) :
    NW live Dt DA S Q 0x8000eb94#64 R Mt :=
  swp_stepD ix_8000eb94 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eb94 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_8000eb98 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000eb9c#64 (upd R 15 ((R 15) + sign_extend (m := 64) (0x800#12))) Mt) :
    NW live Dt DA S Q 0x8000eb98#64 R Mt :=
  swp_stepD ix_8000eb98 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eb98 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

end VsaIris.Sym
