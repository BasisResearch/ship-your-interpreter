import VsaIris.Vsa.SnpRunDef
import VsaIris.Vsa.SymObs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def nx_8000782c : List BBlock := [{ body := [mkLine 0x8000782c#64 0x0f013603#32], term := none }]
def nx_80007830 : List BBlock := [{ body := [mkLine 0x80007830#64 0x08437293#32], term := none }]
def nx_80007834 : List BBlock := [{ body := [mkLine 0x80007834#64 0x00060513#32], term := none }]
def nxT_80007838 : List BBlock := [⟨[], some (⟨0x80007838#64, 0x48028e63#32, 0x63#8, 0x8e#8, 0x02#8, 0x48#8, .br bop.BEQ true, 5, 0, 0x49c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007838 : List BBlock := [⟨[], some (⟨0x80007838#64, 0x48028e63#32, 0x63#8, 0x8e#8, 0x02#8, 0x48#8, .br bop.BEQ false, 5, 0, 0x49c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80007844 : List BBlock := [{ body := [mkLine 0x80007844#64 0x0e812e83#32], term := none }]
def nx_80007848 : List BBlock := [{ body := [mkLine 0x80007848#64 0x00000d93#32], term := none }]
def nx_8000784c : List BBlock := [{ body := [mkLine 0x8000784c#64 0x0a710593#32], term := none }]
def nx_80007850 : List BBlock := [{ body := [mkLine 0x80007850#64 0x00160613#32], term := none }]
def nx_80007854 : List BBlock := [{ body := [mkLine 0x80007854#64 0x001e8e9b#32], term := none }]
def nx_80007858 : List BBlock := [{ body := [mkLine 0x80007858#64 0x00100793#32], term := none }]
def nx_8000785c : List BBlock := [{ body := [mkLine 0x8000785c#64 0x00bbb023#32], term := none }]
def nx_80007860 : List BBlock := [{ body := [mkLine 0x80007860#64 0x00fbb423#32], term := none }]
def nx_80007864 : List BBlock := [{ body := [mkLine 0x80007864#64 0x0ec13823#32], term := none }]
def nx_80007868 : List BBlock := [{ body := [mkLine 0x80007868#64 0x0fd12423#32], term := none }]
def nx_8000786c : List BBlock := [{ body := [mkLine 0x8000786c#64 0x00700593#32], term := none }]
def nx_80007870 : List BBlock := [{ body := [mkLine 0x80007870#64 0x010b8b93#32], term := none }]
def nxT_80007874 : List BBlock := [⟨[], some (⟨0x80007874#64, 0x29d5c663#32, 0x63#8, 0xc6#8, 0xd5#8, 0x29#8, .br bop.BLT true, 11, 29, 0x28c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007874 : List BBlock := [⟨[], some (⟨0x80007874#64, 0x29d5c663#32, 0x63#8, 0xc6#8, 0xd5#8, 0x29#8, .br bop.BLT false, 11, 29, 0x28c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxT_80007878 : List BBlock := [⟨[], some (⟨0x80007878#64, 0x020d8a63#32, 0x63#8, 0x8a#8, 0x0d#8, 0x02#8, .br bop.BEQ true, 27, 0, 0x34#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007878 : List BBlock := [⟨[], some (⟨0x80007878#64, 0x020d8a63#32, 0x63#8, 0x8a#8, 0x0d#8, 0x02#8, .br bop.BEQ false, 27, 0, 0x34#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_800078ac : List BBlock := [{ body := [mkLine 0x800078ac#64 0x08000713#32], term := none }]
def nxT_800078b0 : List BBlock := [⟨[], some (⟨0x800078b0#64, 0x48e28ce3#32, 0xe3#8, 0x8c#8, 0xe2#8, 0x48#8, .br bop.BEQ true, 5, 14, 0xc98#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_800078b0 : List BBlock := [⟨[], some (⟨0x800078b0#64, 0x48e28ce3#32, 0xe3#8, 0x8c#8, 0xe2#8, 0x48#8, .br bop.BEQ false, 5, 14, 0xc98#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_800078b4 : List BBlock := [{ body := [mkLine 0x800078b4#64 0x416a0a3b#32], term := none }]
def nxT_800078b8 : List BBlock := [⟨[], some (⟨0x800078b8#64, 0x43404a63#32, 0x63#8, 0x4a#8, 0x40#8, 0x43#8, .br bop.BLT true, 0, 20, 0x434#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_800078b8 : List BBlock := [⟨[], some (⟨0x800078b8#64, 0x43404a63#32, 0x63#8, 0x4a#8, 0x40#8, 0x43#8, .br bop.BLT false, 0, 20, 0x434#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_800078bc : List BBlock := [{ body := [mkLine 0x800078bc#64 0x10037713#32], term := none }]
def nxT_800078c0 : List BBlock := [⟨[], some (⟨0x800078c0#64, 0x54071063#32, 0x63#8, 0x10#8, 0x07#8, 0x54#8, .br bop.BNE true, 14, 0, 0x540#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_800078c0 : List BBlock := [⟨[], some (⟨0x800078c0#64, 0x54071063#32, 0x63#8, 0x10#8, 0x07#8, 0x54#8, .br bop.BNE false, 14, 0, 0x540#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_800078c4 : List BBlock := [{ body := [mkLine 0x800078c4#64 0x0e812783#32], term := none }]
def nx_800078c8 : List BBlock := [{ body := [mkLine 0x800078c8#64 0x01660633#32], term := none }]
def nx_800078cc : List BBlock := [{ body := [mkLine 0x800078cc#64 0x0ec13823#32], term := none }]
def nx_800078d0 : List BBlock := [{ body := [mkLine 0x800078d0#64 0x0017879b#32], term := none }]
def nx_800078d4 : List BBlock := [{ body := [mkLine 0x800078d4#64 0x01abb023#32], term := none }]
def nx_800078d8 : List BBlock := [{ body := [mkLine 0x800078d8#64 0x016bb423#32], term := none }]
def nx_800078dc : List BBlock := [{ body := [mkLine 0x800078dc#64 0x00700713#32], term := none }]
def nx_800078e0 : List BBlock := [{ body := [mkLine 0x800078e0#64 0x0ef12423#32], term := none }]
def nxT_800078e4 : List BBlock := [⟨[], some (⟨0x800078e4#64, 0x30f74863#32, 0x63#8, 0x48#8, 0xf7#8, 0x30#8, .br bop.BLT true, 14, 15, 0x310#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_800078e4 : List BBlock := [⟨[], some (⟨0x800078e4#64, 0x30f74863#32, 0x63#8, 0x48#8, 0xf7#8, 0x30#8, .br bop.BLT false, 14, 15, 0x310#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_800078e8 : List BBlock := [{ body := [mkLine 0x800078e8#64 0x010b8b93#32], term := none }]
def nx_800078ec : List BBlock := [{ body := [mkLine 0x800078ec#64 0x00437313#32], term := none }]
def nxT_800078f0 : List BBlock := [⟨[], some (⟨0x800078f0#64, 0x00030663#32, 0x63#8, 0x06#8, 0x03#8, 0x00#8, .br bop.BEQ true, 6, 0, 0xc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_800078f0 : List BBlock := [⟨[], some (⟨0x800078f0#64, 0x00030663#32, 0x63#8, 0x06#8, 0x03#8, 0x00#8, .br bop.BEQ false, 6, 0, 0xc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_800078fc : List BBlock := [{ body := [mkLine 0x800078fc#64 0x000e0793#32], term := none }]
def nxT_80007900 : List BBlock := [⟨[], some (⟨0x80007900#64, 0x010e5463#32, 0x63#8, 0x54#8, 0x0e#8, 0x01#8, .br bop.BGE true, 28, 16, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007900 : List BBlock := [⟨[], some (⟨0x80007900#64, 0x010e5463#32, 0x63#8, 0x54#8, 0x0e#8, 0x01#8, .br bop.BGE false, 28, 16, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80007904 : List BBlock := [{ body := [mkLine 0x80007904#64 0x00080793#32], term := none }]
def nx_80007908 : List BBlock := [{ body := [mkLine 0x80007908#64 0x01013703#32], term := none }]
def nx_8000790c : List BBlock := [{ body := [mkLine 0x8000790c#64 0x00e787bb#32], term := none }]
def nx_80007910 : List BBlock := [{ body := [mkLine 0x80007910#64 0x00f13823#32], term := none }]
def nxT_80007914 : List BBlock := [⟨[], some (⟨0x80007914#64, 0x560612e3#32, 0xe3#8, 0x12#8, 0x06#8, 0x56#8, .br bop.BNE true, 12, 0, 0xd64#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007914 : List BBlock := [⟨[], some (⟨0x80007914#64, 0x560612e3#32, 0xe3#8, 0x12#8, 0x06#8, 0x56#8, .br bop.BNE false, 12, 0, 0xd64#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80007918 : List BBlock := [{ body := [mkLine 0x80007918#64 0x02013783#32], term := none }]
def nx_8000791c : List BBlock := [{ body := [mkLine 0x8000791c#64 0x0e012423#32], term := none }]
def nxT_80007920 : List BBlock := [⟨[], some (⟨0x80007920#64, 0x00078863#32, 0x63#8, 0x88#8, 0x07#8, 0x00#8, .br bop.BEQ true, 15, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007920 : List BBlock := [⟨[], some (⟨0x80007920#64, 0x00078863#32, 0x63#8, 0x88#8, 0x07#8, 0x00#8, .br bop.BEQ false, 15, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80007930 : List BBlock := [{ body := [mkLine 0x80007930#64 0x000a8b93#32], term := none }]
def nx_80007934 : List BBlock := [⟨[], some (⟨0x80007934#64, 0xdedff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xde#8, .j, 0, 0, 0x0#13, 0x1ffdec#21, 0#12⟩ : TInstr)⟩]
def nx_80007960 : List BBlock := [{ body := [mkLine 0x80007960#64 0x00013783#32], term := none }]
def nx_80007964 : List BBlock := [{ body := [mkLine 0x80007964#64 0x00050a13#32], term := none }]
def nx_80007968 : List BBlock := [{ body := [mkLine 0x80007968#64 0x40fb0c3b#32], term := none }]
def nxT_8000796c : List BBlock := [⟨[], some (⟨0x8000796c#64, 0x040c0263#32, 0x63#8, 0x02#8, 0x0c#8, 0x04#8, .br bop.BEQ true, 24, 0, 0x44#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_8000796c : List BBlock := [⟨[], some (⟨0x8000796c#64, 0x040c0263#32, 0x63#8, 0x02#8, 0x0c#8, 0x04#8, .br bop.BEQ false, 24, 0, 0x44#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80007970 : List BBlock := [{ body := [mkLine 0x80007970#64 0x00013783#32], term := none }]
def nx_80007974 : List BBlock := [{ body := [mkLine 0x80007974#64 0x0f013703#32], term := none }]
def nx_80007978 : List BBlock := [{ body := [mkLine 0x80007978#64 0x018bb423#32], term := none }]
def nx_8000797c : List BBlock := [{ body := [mkLine 0x8000797c#64 0x00fbb023#32], term := none }]
def nx_80007980 : List BBlock := [{ body := [mkLine 0x80007980#64 0x0e812783#32], term := none }]
def nx_80007984 : List BBlock := [{ body := [mkLine 0x80007984#64 0x01870733#32], term := none }]
def nx_80007988 : List BBlock := [{ body := [mkLine 0x80007988#64 0x0ee13823#32], term := none }]
def nx_8000798c : List BBlock := [{ body := [mkLine 0x8000798c#64 0x0017879b#32], term := none }]
def nx_80007990 : List BBlock := [{ body := [mkLine 0x80007990#64 0x0ef12423#32], term := none }]
def nx_80007994 : List BBlock := [{ body := [mkLine 0x80007994#64 0x00700713#32], term := none }]
def nx_80007998 : List BBlock := [{ body := [mkLine 0x80007998#64 0x010b8b93#32], term := none }]
def nxT_8000799c : List BBlock := [⟨[], some (⟨0x8000799c#64, 0x06f74a63#32, 0x63#8, 0x4a#8, 0xf7#8, 0x06#8, .br bop.BLT true, 14, 15, 0x74#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_8000799c : List BBlock := [⟨[], some (⟨0x8000799c#64, 0x06f74a63#32, 0x63#8, 0x4a#8, 0xf7#8, 0x06#8, .br bop.BLT false, 14, 15, 0x74#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_800079a0 : List BBlock := [{ body := [mkLine 0x800079a0#64 0x01013783#32], term := none }]
def nx_800079a4 : List BBlock := [{ body := [mkLine 0x800079a4#64 0x018787bb#32], term := none }]
def nx_800079a8 : List BBlock := [{ body := [mkLine 0x800079a8#64 0x00f13823#32], term := none }]
def nxT_800079ac : List BBlock := [⟨[], some (⟨0x800079ac#64, 0xdc0a10e3#32, 0xe3#8, 0x10#8, 0x0a#8, 0xdc#8, .br bop.BNE true, 20, 0, 0x1dc0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_800079ac : List BBlock := [⟨[], some (⟨0x800079ac#64, 0xdc0a10e3#32, 0xe3#8, 0x10#8, 0x0a#8, 0xdc#8, .br bop.BNE false, 20, 0, 0x1dc0#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem nt_8000782c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007830#64 (upd R 12 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000782c#64 R Mt :=
  swp_stepD nx_8000782c [2, 12] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000782c ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [2, 12])))) rfl hk

theorem nt_80007830 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007834#64 (upd R 5 ((R 6) &&& sign_extend (m := 64) (0x084#12))) Mt) :
    SnpW live Dt DA S Q 0x80007830#64 R Mt :=
  swp_stepD nx_80007830 [5, 6] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007830 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 5 ∈ [5, 6])))) rfl hk

theorem nt_80007834 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007838#64 (upd R 10 ((R 12) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80007834#64 R Mt :=
  swp_stepD nx_80007834 [10, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007834 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 12])))) rfl hk

theorem nt_80007838 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 5) = (0#64) → SnpW live Dt DA S Q 0x80007cd4#64 R Mt) (hF : ¬ ((R 5) = (0#64)) → SnpW live Dt DA S Q 0x8000783c#64 R Mt) :
    SnpW live Dt DA S Q 0x80007838#64 R Mt := by
  by_cases hc : (R 5) = (0#64)
  · exact
    swp_stepD nxT_80007838 [5] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007838 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007838 [5] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007838 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80007844 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x80007848#64 (upd R 29 (ldv .lw Mt ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80007844#64 R Mt :=
  swp_stepD nx_80007844 [2, 29] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4] (accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007844 ChainFacts; chain_facts hm; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 29 ∈ [2, 29])))) rfl hk

theorem nt_80007848 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000784c#64 (upd R 27 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80007848#64 R Mt :=
  swp_stepD nx_80007848 [27] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007848 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 27 ∈ [27])))) rfl hk

theorem nt_8000784c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007850#64 (upd R 11 ((R 2) + sign_extend (m := 64) (0x0a7#12))) Mt) :
    SnpW live Dt DA S Q 0x8000784c#64 R Mt :=
  swp_stepD nx_8000784c [2, 11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000784c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [2, 11])))) rfl hk

theorem nt_80007850 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007854#64 (upd R 12 ((R 12) + sign_extend (m := 64) (0x001#12))) Mt) :
    SnpW live Dt DA S Q 0x80007850#64 R Mt :=
  swp_stepD nx_80007850 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007850 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12])))) rfl hk

theorem nt_80007854 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007858#64 (upd R 29 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 29) + sign_extend (m := 64) (0x001#12)) 31 0))) Mt) :
    SnpW live Dt DA S Q 0x80007854#64 R Mt :=
  swp_stepD nx_80007854 [29] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007854 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 29 ∈ [29])))) rfl hk

theorem nt_80007858 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000785c#64 (upd R 15 ((0#64) + sign_extend (m := 64) (0x001#12))) Mt) :
    SnpW live Dt DA S Q 0x80007858#64 R Mt :=
  swp_stepD nx_80007858 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007858 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem nt_8000785c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007860#64 R (writeLog Mt [(((R 23) + sign_extend (m := 64) (0x000#12)).toNat, 8, (R 11))])) :
    SnpW live Dt DA S Q 0x8000785c#64 R Mt :=
  swp_stepD nx_8000785c [11, 23] [] [] (accAddrs ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000785c ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007860 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 23) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 23) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007864#64 R (writeLog Mt [(((R 23) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 15))])) :
    SnpW live Dt DA S Q 0x80007860#64 R Mt :=
  swp_stepD nx_80007860 [15, 23] [] [] (accAddrs ((R 23) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80007860 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007864 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007868#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat, 8, (R 12))])) :
    SnpW live Dt DA S Q 0x80007864#64 R Mt :=
  swp_stepD nx_80007864 [2, 12] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80007864 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007868 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x8000786c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat, 4, (R 29))])) :
    SnpW live Dt DA S Q 0x80007868#64 R Mt :=
  swp_stepD nx_80007868 [2, 29] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80007868 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000786c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007870#64 (upd R 11 ((0#64) + sign_extend (m := 64) (0x007#12))) Mt) :
    SnpW live Dt DA S Q 0x8000786c#64 R Mt :=
  swp_stepD nx_8000786c [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000786c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

theorem nt_80007870 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007874#64 (upd R 23 ((R 23) + sign_extend (m := 64) (0x010#12))) Mt) :
    SnpW live Dt DA S Q 0x80007870#64 R Mt :=
  swp_stepD nx_80007870 [23] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007870 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [23])))) rfl hk

theorem nt_80007874 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 11).toInt < (R 29).toInt → SnpW live Dt DA S Q 0x80007b00#64 R Mt) (hF : ¬ ((R 11).toInt < (R 29).toInt) → SnpW live Dt DA S Q 0x80007878#64 R Mt) :
    SnpW live Dt DA S Q 0x80007874#64 R Mt := by
  by_cases hc : (R 11).toInt < (R 29).toInt
  · exact
    swp_stepD nxT_80007874 [11, 29] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007874 ChainFacts; chain_facts hm; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007874 [11, 29] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007874 ChainFacts; chain_facts hm; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80007878 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 27) = (0#64) → SnpW live Dt DA S Q 0x800078ac#64 R Mt) (hF : ¬ ((R 27) = (0#64)) → SnpW live Dt DA S Q 0x8000787c#64 R Mt) :
    SnpW live Dt DA S Q 0x80007878#64 R Mt := by
  by_cases hc : (R 27) = (0#64)
  · exact
    swp_stepD nxT_80007878 [27] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007878 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007878 [27] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007878 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_800078ac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800078b0#64 (upd R 14 ((0#64) + sign_extend (m := 64) (0x080#12))) Mt) :
    SnpW live Dt DA S Q 0x800078ac#64 R Mt :=
  swp_stepD nx_800078ac [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800078ac ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem nt_800078b0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 5) = (R 14) → SnpW live Dt DA S Q 0x80008548#64 R Mt) (hF : ¬ ((R 5) = (R 14)) → SnpW live Dt DA S Q 0x800078b4#64 R Mt) :
    SnpW live Dt DA S Q 0x800078b0#64 R Mt := by
  by_cases hc : (R 5) = (R 14)
  · exact
    swp_stepD nxT_800078b0 [5, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_800078b0 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_800078b0 [5, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_800078b0 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_800078b4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800078b8#64 (upd R 20 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 20) 31 0) - (Sail.BitVec.extractLsb (R 22) 31 0)))) Mt) :
    SnpW live Dt DA S Q 0x800078b4#64 R Mt :=
  swp_stepD nx_800078b4 [20, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800078b4 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [20, 22])))) rfl hk

theorem nt_800078b8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (0#64).toInt < (R 20).toInt → SnpW live Dt DA S Q 0x80007cec#64 R Mt) (hF : ¬ ((0#64).toInt < (R 20).toInt) → SnpW live Dt DA S Q 0x800078bc#64 R Mt) :
    SnpW live Dt DA S Q 0x800078b8#64 R Mt := by
  by_cases hc : (0#64).toInt < (R 20).toInt
  · exact
    swp_stepD nxT_800078b8 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_800078b8 ChainFacts; chain_facts hm; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_800078b8 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_800078b8 ChainFacts; chain_facts hm; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_800078bc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800078c0#64 (upd R 14 ((R 6) &&& sign_extend (m := 64) (0x100#12))) Mt) :
    SnpW live Dt DA S Q 0x800078bc#64 R Mt :=
  swp_stepD nx_800078bc [6, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800078bc ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [6, 14])))) rfl hk

theorem nt_800078c0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 14) ≠ (0#64) → SnpW live Dt DA S Q 0x80007e00#64 R Mt) (hF : ¬ ((R 14) ≠ (0#64)) → SnpW live Dt DA S Q 0x800078c4#64 R Mt) :
    SnpW live Dt DA S Q 0x800078c0#64 R Mt := by
  by_cases hc : (R 14) ≠ (0#64)
  · exact
    swp_stepD nxT_800078c0 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_800078c0 ChainFacts; chain_facts hm; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_800078c0 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_800078c0 ChainFacts; chain_facts hm; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_800078c4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x800078c8#64 (upd R 15 (ldv .lw Mt ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800078c4#64 R Mt :=
  swp_stepD nx_800078c4 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4] (accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800078c4 ChainFacts; chain_facts hm; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem nt_800078c8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800078cc#64 (upd R 12 ((R 12) + (R 22))) Mt) :
    SnpW live Dt DA S Q 0x800078c8#64 R Mt :=
  swp_stepD nx_800078c8 [12, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800078c8 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 22])))) rfl hk

theorem nt_800078cc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800078d0#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat, 8, (R 12))])) :
    SnpW live Dt DA S Q 0x800078cc#64 R Mt :=
  swp_stepD nx_800078cc [2, 12] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800078cc ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800078d0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800078d4#64 (upd R 15 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 15) + sign_extend (m := 64) (0x001#12)) 31 0))) Mt) :
    SnpW live Dt DA S Q 0x800078d0#64 R Mt :=
  swp_stepD nx_800078d0 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800078d0 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem nt_800078d4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800078d8#64 R (writeLog Mt [(((R 23) + sign_extend (m := 64) (0x000#12)).toNat, 8, (R 26))])) :
    SnpW live Dt DA S Q 0x800078d4#64 R Mt :=
  swp_stepD nx_800078d4 [23, 26] [] [] (accAddrs ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800078d4 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800078d8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 23) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 23) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800078dc#64 R (writeLog Mt [(((R 23) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 22))])) :
    SnpW live Dt DA S Q 0x800078d8#64 R Mt :=
  swp_stepD nx_800078d8 [22, 23] [] [] (accAddrs ((R 23) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800078d8 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800078dc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800078e0#64 (upd R 14 ((0#64) + sign_extend (m := 64) (0x007#12))) Mt) :
    SnpW live Dt DA S Q 0x800078dc#64 R Mt :=
  swp_stepD nx_800078dc [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800078dc ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem nt_800078e0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x800078e4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat, 4, (R 15))])) :
    SnpW live Dt DA S Q 0x800078e0#64 R Mt :=
  swp_stepD nx_800078e0 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800078e0 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800078e4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 14).toInt < (R 15).toInt → SnpW live Dt DA S Q 0x80007bf4#64 R Mt) (hF : ¬ ((R 14).toInt < (R 15).toInt) → SnpW live Dt DA S Q 0x800078e8#64 R Mt) :
    SnpW live Dt DA S Q 0x800078e4#64 R Mt := by
  by_cases hc : (R 14).toInt < (R 15).toInt
  · exact
    swp_stepD nxT_800078e4 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_800078e4 ChainFacts; chain_facts hm; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_800078e4 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_800078e4 ChainFacts; chain_facts hm; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_800078e8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800078ec#64 (upd R 23 ((R 23) + sign_extend (m := 64) (0x010#12))) Mt) :
    SnpW live Dt DA S Q 0x800078e8#64 R Mt :=
  swp_stepD nx_800078e8 [23] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800078e8 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [23])))) rfl hk

theorem nt_800078ec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800078f0#64 (upd R 6 ((R 6) &&& sign_extend (m := 64) (0x004#12))) Mt) :
    SnpW live Dt DA S Q 0x800078ec#64 R Mt :=
  swp_stepD nx_800078ec [6] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800078ec ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 6 ∈ [6])))) rfl hk

theorem nt_800078f0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 6) = (0#64) → SnpW live Dt DA S Q 0x800078fc#64 R Mt) (hF : ¬ ((R 6) = (0#64)) → SnpW live Dt DA S Q 0x800078f4#64 R Mt) :
    SnpW live Dt DA S Q 0x800078f0#64 R Mt := by
  by_cases hc : (R 6) = (0#64)
  · exact
    swp_stepD nxT_800078f0 [6] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_800078f0 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_800078f0 [6] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_800078f0 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_800078fc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007900#64 (upd R 15 ((R 28) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x800078fc#64 R Mt :=
  swp_stepD nx_800078fc [15, 28] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800078fc ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15, 28])))) rfl hk

theorem nt_80007900 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 16).toInt ≤ (R 28).toInt → SnpW live Dt DA S Q 0x80007908#64 R Mt) (hF : ¬ ((R 16).toInt ≤ (R 28).toInt) → SnpW live Dt DA S Q 0x80007904#64 R Mt) :
    SnpW live Dt DA S Q 0x80007900#64 R Mt := by
  by_cases hc : (R 16).toInt ≤ (R 28).toInt
  · exact
    swp_stepD nxT_80007900 [16, 28] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007900 ChainFacts; chain_facts hm; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007900 [16, 28] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007900 ChainFacts; chain_facts hm; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80007904 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007908#64 (upd R 15 ((R 16) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80007904#64 R Mt :=
  swp_stepD nx_80007904 [15, 16] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007904 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15, 16])))) rfl hk

theorem nt_80007908 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000790c#64 (upd R 14 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80007908#64 R Mt :=
  swp_stepD nx_80007908 [2, 14] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007908 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [2, 14])))) rfl hk

theorem nt_8000790c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007910#64 (upd R 15 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 15) 31 0) + (Sail.BitVec.extractLsb (R 14) 31 0)))) Mt) :
    SnpW live Dt DA S Q 0x8000790c#64 R Mt :=
  swp_stepD nx_8000790c [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000790c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [14, 15])))) rfl hk

theorem nt_80007910 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007914#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 15))])) :
    SnpW live Dt DA S Q 0x80007910#64 R Mt :=
  swp_stepD nx_80007910 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80007910 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007914 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 12) ≠ (0#64) → SnpW live Dt DA S Q 0x80008678#64 R Mt) (hF : ¬ ((R 12) ≠ (0#64)) → SnpW live Dt DA S Q 0x80007918#64 R Mt) :
    SnpW live Dt DA S Q 0x80007914#64 R Mt := by
  by_cases hc : (R 12) ≠ (0#64)
  · exact
    swp_stepD nxT_80007914 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007914 ChainFacts; chain_facts hm; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007914 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007914 ChainFacts; chain_facts hm; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80007918 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000791c#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80007918#64 R Mt :=
  swp_stepD nx_80007918 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007918 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem nt_8000791c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x80007920#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat, 4, (0#64))])) :
    SnpW live Dt DA S Q 0x8000791c#64 R Mt :=
  swp_stepD nx_8000791c [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000791c ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007920 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 15) = (0#64) → SnpW live Dt DA S Q 0x80007930#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → SnpW live Dt DA S Q 0x80007924#64 R Mt) :
    SnpW live Dt DA S Q 0x80007920#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    swp_stepD nxT_80007920 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007920 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007920 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007920 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80007930 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007934#64 (upd R 23 ((R 21) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80007930#64 R Mt :=
  swp_stepD nx_80007930 [21, 23] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007930 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [21, 23])))) rfl hk

theorem nt_80007934 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007720#64 R Mt) :
    SnpW live Dt DA S Q 0x80007934#64 R Mt :=
  swp_stepD nx_80007934 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007934 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007960 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007964#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80007960#64 R Mt :=
  swp_stepD nx_80007960 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007960 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem nt_80007964 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007968#64 (upd R 20 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80007964#64 R Mt :=
  swp_stepD nx_80007964 [10, 20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007964 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [10, 20])))) rfl hk

theorem nt_80007968 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000796c#64 (upd R 24 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 22) 31 0) - (Sail.BitVec.extractLsb (R 15) 31 0)))) Mt) :
    SnpW live Dt DA S Q 0x80007968#64 R Mt :=
  swp_stepD nx_80007968 [15, 22, 24] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007968 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 24 ∈ [15, 22, 24])))) rfl hk

theorem nt_8000796c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 24) = (0#64) → SnpW live Dt DA S Q 0x800079b0#64 R Mt) (hF : ¬ ((R 24) = (0#64)) → SnpW live Dt DA S Q 0x80007970#64 R Mt) :
    SnpW live Dt DA S Q 0x8000796c#64 R Mt := by
  by_cases hc : (R 24) = (0#64)
  · exact
    swp_stepD nxT_8000796c [24] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_8000796c ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_8000796c [24] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_8000796c ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80007970 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007974#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80007970#64 R Mt :=
  swp_stepD nx_80007970 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007970 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem nt_80007974 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007978#64 (upd R 14 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80007974#64 R Mt :=
  swp_stepD nx_80007974 [2, 14] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007974 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [2, 14])))) rfl hk

theorem nt_80007978 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 23) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 23) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000797c#64 R (writeLog Mt [(((R 23) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 24))])) :
    SnpW live Dt DA S Q 0x80007978#64 R Mt :=
  swp_stepD nx_80007978 [23, 24] [] [] (accAddrs ((R 23) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80007978 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000797c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007980#64 R (writeLog Mt [(((R 23) + sign_extend (m := 64) (0x000#12)).toNat, 8, (R 15))])) :
    SnpW live Dt DA S Q 0x8000797c#64 R Mt :=
  swp_stepD nx_8000797c [15, 23] [] [] (accAddrs ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000797c ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007980 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x80007984#64 (upd R 15 (ldv .lw Mt ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80007980#64 R Mt :=
  swp_stepD nx_80007980 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4] (accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007980 ChainFacts; chain_facts hm; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem nt_80007984 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007988#64 (upd R 14 ((R 14) + (R 24))) Mt) :
    SnpW live Dt DA S Q 0x80007984#64 R Mt :=
  swp_stepD nx_80007984 [14, 24] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007984 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 24])))) rfl hk

theorem nt_80007988 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000798c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat, 8, (R 14))])) :
    SnpW live Dt DA S Q 0x80007988#64 R Mt :=
  swp_stepD nx_80007988 [2, 14] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80007988 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000798c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007990#64 (upd R 15 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 15) + sign_extend (m := 64) (0x001#12)) 31 0))) Mt) :
    SnpW live Dt DA S Q 0x8000798c#64 R Mt :=
  swp_stepD nx_8000798c [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000798c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem nt_80007990 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x80007994#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat, 4, (R 15))])) :
    SnpW live Dt DA S Q 0x80007990#64 R Mt :=
  swp_stepD nx_80007990 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80007990 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007994 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007998#64 (upd R 14 ((0#64) + sign_extend (m := 64) (0x007#12))) Mt) :
    SnpW live Dt DA S Q 0x80007994#64 R Mt :=
  swp_stepD nx_80007994 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007994 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem nt_80007998 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000799c#64 (upd R 23 ((R 23) + sign_extend (m := 64) (0x010#12))) Mt) :
    SnpW live Dt DA S Q 0x80007998#64 R Mt :=
  swp_stepD nx_80007998 [23] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007998 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [23])))) rfl hk

theorem nt_8000799c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 14).toInt < (R 15).toInt → SnpW live Dt DA S Q 0x80007a10#64 R Mt) (hF : ¬ ((R 14).toInt < (R 15).toInt) → SnpW live Dt DA S Q 0x800079a0#64 R Mt) :
    SnpW live Dt DA S Q 0x8000799c#64 R Mt := by
  by_cases hc : (R 14).toInt < (R 15).toInt
  · exact
    swp_stepD nxT_8000799c [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_8000799c ChainFacts; chain_facts hm; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_8000799c [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_8000799c ChainFacts; chain_facts hm; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_800079a0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079a4#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800079a0#64 R Mt :=
  swp_stepD nx_800079a0 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079a0 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem nt_800079a4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800079a8#64 (upd R 15 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 15) 31 0) + (Sail.BitVec.extractLsb (R 24) 31 0)))) Mt) :
    SnpW live Dt DA S Q 0x800079a4#64 R Mt :=
  swp_stepD nx_800079a4 [15, 24] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800079a4 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15, 24])))) rfl hk

theorem nt_800079a8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800079ac#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 15))])) :
    SnpW live Dt DA S Q 0x800079a8#64 R Mt :=
  swp_stepD nx_800079a8 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800079a8 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800079ac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 20) ≠ (0#64) → SnpW live Dt DA S Q 0x8000776c#64 R Mt) (hF : ¬ ((R 20) ≠ (0#64)) → SnpW live Dt DA S Q 0x800079b0#64 R Mt) :
    SnpW live Dt DA S Q 0x800079ac#64 R Mt := by
  by_cases hc : (R 20) ≠ (0#64)
  · exact
    swp_stepD nxT_800079ac [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_800079ac ChainFacts; chain_facts hm; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_800079ac [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_800079ac ChainFacts; chain_facts hm; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

end VsaIris.Sym
