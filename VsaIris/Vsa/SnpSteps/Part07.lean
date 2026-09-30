import VsaIris.Vsa.SnpRunDef
import VsaIris.Vsa.SymObs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def nx_80007f50 : List BBlock := [{ body := [mkLine 0x80007f50#64 0x01913023#32], term := none }]
def nx_80007f54 : List BBlock := [{ body := [mkLine 0x80007f54#64 0x0a0103a3#32], term := none }]
def nx_80007f58 : List BBlock := [{ body := [mkLine 0x80007f58#64 0x0007bd03#32], term := none }]
def nx_80007f5c : List BBlock := [{ body := [mkLine 0x80007f5c#64 0x000d8e13#32], term := none }]
def nx_80007f60 : List BBlock := [{ body := [mkLine 0x80007f60#64 0x00878893#32], term := none }]
def nxT_80007f64 : List BBlock := [⟨[], some (⟨0x80007f64#64, 0x000d1463#32, 0x63#8, 0x14#8, 0x0d#8, 0x00#8, .br bop.BNE true, 26, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007f64 : List BBlock := [⟨[], some (⟨0x80007f64#64, 0x000d1463#32, 0x63#8, 0x14#8, 0x0d#8, 0x00#8, .br bop.BNE false, 26, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80007f6c : List BBlock := [{ body := [mkLine 0x80007f6c#64 0x05300713#32], term := none }]
def nxT_80007f70 : List BBlock := [⟨[], some (⟨0x80007f70#64, 0x00ec1463#32, 0x63#8, 0x14#8, 0xec#8, 0x00#8, .br bop.BNE true, 24, 14, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007f70 : List BBlock := [⟨[], some (⟨0x80007f70#64, 0x00ec1463#32, 0x63#8, 0x14#8, 0xec#8, 0x00#8, .br bop.BNE false, 24, 14, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80007f78 : List BBlock := [{ body := [mkLine 0x80007f78#64 0x01037f93#32], term := none }]
def nxT_80007f7c : List BBlock := [⟨[], some (⟨0x80007f7c#64, 0x000f8463#32, 0x63#8, 0x84#8, 0x0f#8, 0x00#8, .br bop.BEQ true, 31, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007f7c : List BBlock := [⟨[], some (⟨0x80007f7c#64, 0x000f8463#32, 0x63#8, 0x84#8, 0x0f#8, 0x00#8, .br bop.BEQ false, 31, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxT_80007f84 : List BBlock := [⟨[], some (⟨0x80007f84#64, 0x000a5463#32, 0x63#8, 0x54#8, 0x0a#8, 0x00#8, .br bop.BGE true, 20, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007f84 : List BBlock := [⟨[], some (⟨0x80007f84#64, 0x000a5463#32, 0x63#8, 0x54#8, 0x0a#8, 0x00#8, .br bop.BGE false, 20, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80007f88 : List BBlock := [⟨[], some (⟨0x80007f88#64, 0x6e90106f#32, 0x6f#8, 0x10#8, 0x90#8, 0x6e#8, .j, 0, 0, 0x0#13, 0x1ee8#21, 0#12⟩ : TInstr)⟩]
def nx_80007fe0 : List BBlock := [{ body := [mkLine 0x80007fe0#64 0x0007081b#32], term := none }]
def nxT_80007fe4 : List BBlock := [⟨[], some (⟨0x80007fe4#64, 0x00060463#32, 0x63#8, 0x04#8, 0x06#8, 0x00#8, .br bop.BEQ true, 12, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80007fe4 : List BBlock := [⟨[], some (⟨0x80007fe4#64, 0x00060463#32, 0x63#8, 0x04#8, 0x06#8, 0x00#8, .br bop.BEQ false, 12, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80007fec : List BBlock := [{ body := [mkLine 0x80007fec#64 0x01113c23#32], term := none }]
def nx_80007ff0 : List BBlock := [{ body := [mkLine 0x80007ff0#64 0x00000a13#32], term := none }]
def nx_80007ff4 : List BBlock := [{ body := [mkLine 0x80007ff4#64 0x02013c23#32], term := none }]
def nx_80007ff8 : List BBlock := [{ body := [mkLine 0x80007ff8#64 0x02013823#32], term := none }]
def nx_80007ffc : List BBlock := [{ body := [mkLine 0x80007ffc#64 0x02013023#32], term := none }]
def nx_80008000 : List BBlock := [{ body := [mkLine 0x80008000#64 0x07300c13#32], term := none }]
def nx_80008004 : List BBlock := [⟨[], some (⟨0x80008004#64, 0x829ff06f#32, 0x6f#8, 0xf0#8, 0x9f#8, 0x82#8, .j, 0, 0, 0x0#13, 0x1ff828#21, 0#12⟩ : TInstr)⟩]
def nx_80008008 : List BBlock := [{ body := [mkLine 0x80008008#64 0x01813783#32], term := none }]
def nx_8000800c : List BBlock := [{ body := [mkLine 0x8000800c#64 0x01913023#32], term := none }]
def nx_80008010 : List BBlock := [{ body := [mkLine 0x80008010#64 0x02037713#32], term := none }]
def nx_80008014 : List BBlock := [{ body := [mkLine 0x80008014#64 0x000d8e13#32], term := none }]
def nx_80008018 : List BBlock := [{ body := [mkLine 0x80008018#64 0x00878793#32], term := none }]
def nxT_8000801c : List BBlock := [⟨[], some (⟨0x8000801c#64, 0x0a071e63#32, 0x63#8, 0x1e#8, 0x07#8, 0x0a#8, .br bop.BNE true, 14, 0, 0xbc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_8000801c : List BBlock := [⟨[], some (⟨0x8000801c#64, 0x0a071e63#32, 0x63#8, 0x1e#8, 0x07#8, 0x0a#8, .br bop.BNE false, 14, 0, 0xbc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80008020 : List BBlock := [{ body := [mkLine 0x80008020#64 0x01037713#32], term := none }]
def nxT_80008024 : List BBlock := [⟨[], some (⟨0x80008024#64, 0x0a071a63#32, 0x63#8, 0x1a#8, 0x07#8, 0x0a#8, .br bop.BNE true, 14, 0, 0xb4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80008024 : List BBlock := [⟨[], some (⟨0x80008024#64, 0x0a071a63#32, 0x63#8, 0x1a#8, 0x07#8, 0x0a#8, .br bop.BNE false, 14, 0, 0xb4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80008028 : List BBlock := [{ body := [mkLine 0x80008028#64 0x01813703#32], term := none }]
def nx_8000802c : List BBlock := [{ body := [mkLine 0x8000802c#64 0x04037693#32], term := none }]
def nx_80008030 : List BBlock := [{ body := [mkLine 0x80008030#64 0x00072703#32], term := none }]
def nxT_80008034 : List BBlock := [⟨[], some (⟨0x80008034#64, 0x00069463#32, 0x63#8, 0x94#8, 0x06#8, 0x00#8, .br bop.BNE true, 13, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80008034 : List BBlock := [⟨[], some (⟨0x80008034#64, 0x00069463#32, 0x63#8, 0x94#8, 0x06#8, 0x00#8, .br bop.BNE false, 13, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80008038 : List BBlock := [⟨[], some (⟨0x80008038#64, 0x1890106f#32, 0x6f#8, 0x10#8, 0x90#8, 0x18#8, .j, 0, 0, 0x0#13, 0x1988#21, 0#12⟩ : TInstr)⟩]
def nxT_8000804c : List BBlock := [⟨[], some (⟨0x8000804c#64, 0x0a06c063#32, 0x63#8, 0xc0#8, 0x06#8, 0x0a#8, .br bop.BLT true, 13, 0, 0xa0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_8000804c : List BBlock := [⟨[], some (⟨0x8000804c#64, 0x0a06c063#32, 0x63#8, 0xc0#8, 0x06#8, 0x0a#8, .br bop.BLT false, 13, 0, 0xa0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxT_80008050 : List BBlock := [⟨[], some (⟨0x80008050#64, 0x0a0a4863#32, 0x63#8, 0x48#8, 0x0a#8, 0x0a#8, .br bop.BLT true, 20, 0, 0xb0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80008050 : List BBlock := [⟨[], some (⟨0x80008050#64, 0x0a0a4863#32, 0x63#8, 0x48#8, 0x0a#8, 0x0a#8, .br bop.BLT false, 20, 0, 0xb0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxT_80008088 : List BBlock := [⟨[], some (⟨0x80008088#64, 0x000f9463#32, 0x63#8, 0x94#8, 0x0f#8, 0x00#8, .br bop.BNE true, 31, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80008088 : List BBlock := [⟨[], some (⟨0x80008088#64, 0x000f9463#32, 0x63#8, 0x94#8, 0x0f#8, 0x00#8, .br bop.BNE false, 31, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_8000808c : List BBlock := [⟨[], some (⟨0x8000808c#64, 0x7a40206f#32, 0x6f#8, 0x20#8, 0x40#8, 0x7a#8, .j, 0, 0, 0x0#13, 0x27a4#21, 0#12⟩ : TInstr)⟩]
def nx_800080d8 : List BBlock := [{ body := [mkLine 0x800080d8#64 0x01813703#32], term := none }]
def nx_800080dc : List BBlock := [{ body := [mkLine 0x800080dc#64 0x00073683#32], term := none }]
def nx_800080e0 : List BBlock := [{ body := [mkLine 0x800080e0#64 0x00f13c23#32], term := none }]
def nx_800080e4 : List BBlock := [{ body := [mkLine 0x800080e4#64 0x00068713#32], term := none }]
def nxT_800080e8 : List BBlock := [⟨[], some (⟨0x800080e8#64, 0xf606d4e3#32, 0xe3#8, 0xd4#8, 0x06#8, 0xf6#8, .br bop.BGE true, 13, 0, 0x1f68#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_800080e8 : List BBlock := [⟨[], some (⟨0x800080e8#64, 0xf606d4e3#32, 0xe3#8, 0xd4#8, 0x06#8, 0xf6#8, .br bop.BGE false, 13, 0, 0x1f68#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_800080ec : List BBlock := [{ body := [mkLine 0x800080ec#64 0x02d00793#32], term := none }]
def nx_800080f0 : List BBlock := [{ body := [mkLine 0x800080f0#64 0x0af103a3#32], term := none }]
def nx_800080f4 : List BBlock := [{ body := [mkLine 0x800080f4#64 0x40e00733#32], term := none }]
def nxT_800080f8 : List BBlock := [⟨[], some (⟨0x800080f8#64, 0x000a4463#32, 0x63#8, 0x44#8, 0x0a#8, 0x00#8, .br bop.BLT true, 20, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_800080f8 : List BBlock := [⟨[], some (⟨0x800080f8#64, 0x000a4463#32, 0x63#8, 0x44#8, 0x0a#8, 0x00#8, .br bop.BLT false, 20, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80008100 : List BBlock := [{ body := [mkLine 0x80008100#64 0x00900793#32], term := none }]
def nxT_80008104 : List BBlock := [⟨[], some (⟨0x80008104#64, 0x1ce7e263#32, 0x63#8, 0xe2#8, 0xe7#8, 0x1c#8, .br bop.BLTU true, 15, 14, 0x1c4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80008104 : List BBlock := [⟨[], some (⟨0x80008104#64, 0x1ce7e263#32, 0x63#8, 0xe2#8, 0xe7#8, 0x1c#8, .br bop.BLTU false, 15, 14, 0x1c4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80008108 : List BBlock := [{ body := [mkLine 0x80008108#64 0x0307071b#32], term := none }]
def nx_8000810c : List BBlock := [{ body := [mkLine 0x8000810c#64 0x14e10da3#32], term := none }]
def nx_80008110 : List BBlock := [{ body := [mkLine 0x80008110#64 0x000a081b#32], term := none }]
def nxT_80008114 : List BBlock := [⟨[], some (⟨0x80008114#64, 0x594058e3#32, 0xe3#8, 0x58#8, 0x40#8, 0x59#8, .br bop.BGE true, 0, 20, 0xd90#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80008114 : List BBlock := [⟨[], some (⟨0x80008114#64, 0x594058e3#32, 0xe3#8, 0x58#8, 0x40#8, 0x59#8, .br bop.BGE false, 0, 20, 0xd90#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80008128 : List BBlock := [{ body := [mkLine 0x80008128#64 0x02013023#32], term := none }]
def nxT_8000812c : List BBlock := [⟨[], some (⟨0x8000812c#64, 0xf40f0ee3#32, 0xe3#8, 0x0e#8, 0x0f#8, 0xf4#8, .br bop.BEQ true, 30, 0, 0x1f5c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_8000812c : List BBlock := [⟨[], some (⟨0x8000812c#64, 0xf40f0ee3#32, 0xe3#8, 0x0e#8, 0x0f#8, 0xf4#8, .br bop.BEQ false, 30, 0, 0x1f5c#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem nt_80007f50 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007f54#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x000#12)).toNat, 8, (R 25))])) :
    SnpW live Dt DA S Q 0x80007f50#64 R Mt :=
  swp_stepD nx_80007f50 [2, 25] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80007f50 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007f54 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOKb ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1, S b)
    (hk : SnpW live Dt DA S Q 0x80007f58#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat, 1, (0#64))])) :
    SnpW live Dt DA S Q 0x80007f54#64 R Mt :=
  swp_stepD nx_80007f54 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80007f54 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007f58 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 15) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 15) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007f5c#64 (upd R 26 (ldv .ld Mt ((R 15) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80007f58#64 R Mt :=
  swp_stepD nx_80007f58 [15, 26] [bytesAt (imgM Mt) ((R 15) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 15) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007f58 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 26 ∈ [15, 26])))) rfl hk

theorem nt_80007f5c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007f60#64 (upd R 28 ((R 27) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80007f5c#64 R Mt :=
  swp_stepD nx_80007f5c [27, 28] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007f5c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 28 ∈ [27, 28])))) rfl hk

theorem nt_80007f60 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007f64#64 (upd R 17 ((R 15) + sign_extend (m := 64) (0x008#12))) Mt) :
    SnpW live Dt DA S Q 0x80007f60#64 R Mt :=
  swp_stepD nx_80007f60 [15, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007f60 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 17 ∈ [15, 17])))) rfl hk

theorem nt_80007f64 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 26) ≠ (0#64) → SnpW live Dt DA S Q 0x80007f6c#64 R Mt) (hF : ¬ ((R 26) ≠ (0#64)) → SnpW live Dt DA S Q 0x80007f68#64 R Mt) :
    SnpW live Dt DA S Q 0x80007f64#64 R Mt := by
  by_cases hc : (R 26) ≠ (0#64)
  · exact
    swp_stepD nxT_80007f64 [26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007f64 ChainFacts; chain_facts hm; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007f64 [26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007f64 ChainFacts; chain_facts hm; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80007f6c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007f70#64 (upd R 14 ((0#64) + sign_extend (m := 64) (0x053#12))) Mt) :
    SnpW live Dt DA S Q 0x80007f6c#64 R Mt :=
  swp_stepD nx_80007f6c [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007f6c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem nt_80007f70 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 24) ≠ (R 14) → SnpW live Dt DA S Q 0x80007f78#64 R Mt) (hF : ¬ ((R 24) ≠ (R 14)) → SnpW live Dt DA S Q 0x80007f74#64 R Mt) :
    SnpW live Dt DA S Q 0x80007f70#64 R Mt := by
  by_cases hc : (R 24) ≠ (R 14)
  · exact
    swp_stepD nxT_80007f70 [14, 24] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007f70 ChainFacts; chain_facts hm; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007f70 [14, 24] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007f70 ChainFacts; chain_facts hm; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80007f78 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007f7c#64 (upd R 31 ((R 6) &&& sign_extend (m := 64) (0x010#12))) Mt) :
    SnpW live Dt DA S Q 0x80007f78#64 R Mt :=
  swp_stepD nx_80007f78 [6, 31] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007f78 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 31 ∈ [6, 31])))) rfl hk

theorem nt_80007f7c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 31) = (0#64) → SnpW live Dt DA S Q 0x80007f84#64 R Mt) (hF : ¬ ((R 31) = (0#64)) → SnpW live Dt DA S Q 0x80007f80#64 R Mt) :
    SnpW live Dt DA S Q 0x80007f7c#64 R Mt := by
  by_cases hc : (R 31) = (0#64)
  · exact
    swp_stepD nxT_80007f7c [31] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007f7c ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007f7c [31] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007f7c ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80007f84 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (0#64).toInt ≤ (R 20).toInt → SnpW live Dt DA S Q 0x80007f8c#64 R Mt) (hF : ¬ ((0#64).toInt ≤ (R 20).toInt) → SnpW live Dt DA S Q 0x80007f88#64 R Mt) :
    SnpW live Dt DA S Q 0x80007f84#64 R Mt := by
  by_cases hc : (0#64).toInt ≤ (R 20).toInt
  · exact
    swp_stepD nxT_80007f84 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007f84 ChainFacts; chain_facts hm; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007f84 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007f84 ChainFacts; chain_facts hm; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80007f88 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80009e70#64 R Mt) :
    SnpW live Dt DA S Q 0x80007f88#64 R Mt :=
  swp_stepD nx_80007f88 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007f88 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007fe0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007fe4#64 (upd R 16 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 14) + sign_extend (m := 64) (0x000#12)) 31 0))) Mt) :
    SnpW live Dt DA S Q 0x80007fe0#64 R Mt :=
  swp_stepD nx_80007fe0 [14, 16] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007fe0 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 16 ∈ [14, 16])))) rfl hk

theorem nt_80007fe4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 12) = (0#64) → SnpW live Dt DA S Q 0x80007fec#64 R Mt) (hF : ¬ ((R 12) = (0#64)) → SnpW live Dt DA S Q 0x80007fe8#64 R Mt) :
    SnpW live Dt DA S Q 0x80007fe4#64 R Mt := by
  by_cases hc : (R 12) = (0#64)
  · exact
    swp_stepD nxT_80007fe4 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80007fe4 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80007fe4 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80007fe4 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80007fec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007ff0#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 17))])) :
    SnpW live Dt DA S Q 0x80007fec#64 R Mt :=
  swp_stepD nx_80007fec [2, 17] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80007fec ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007ff0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80007ff4#64 (upd R 20 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80007ff0#64 R Mt :=
  swp_stepD nx_80007ff0 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80007ff0 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [20])))) rfl hk

theorem nt_80007ff4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007ff8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x038#12)).toNat, 8, (0#64))])) :
    SnpW live Dt DA S Q 0x80007ff4#64 R Mt :=
  swp_stepD nx_80007ff4 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80007ff4 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007ff8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80007ffc#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x030#12)).toNat, 8, (0#64))])) :
    SnpW live Dt DA S Q 0x80007ff8#64 R Mt :=
  swp_stepD nx_80007ff8 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80007ff8 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80007ffc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80008000#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (0#64))])) :
    SnpW live Dt DA S Q 0x80007ffc#64 R Mt :=
  swp_stepD nx_80007ffc [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80007ffc ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80008000 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008004#64 (upd R 24 ((0#64) + sign_extend (m := 64) (0x073#12))) Mt) :
    SnpW live Dt DA S Q 0x80008000#64 R Mt :=
  swp_stepD nx_80008000 [24] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008000 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 24 ∈ [24])))) rfl hk

theorem nt_80008004 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000782c#64 R Mt) :
    SnpW live Dt DA S Q 0x80008004#64 R Mt :=
  swp_stepD nx_80008004 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008004 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80008008 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000800c#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80008008#64 R Mt :=
  swp_stepD nx_80008008 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008008 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem nt_8000800c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x80008010#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x000#12)).toNat, 8, (R 25))])) :
    SnpW live Dt DA S Q 0x8000800c#64 R Mt :=
  swp_stepD nx_8000800c [2, 25] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000800c ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80008010 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008014#64 (upd R 14 ((R 6) &&& sign_extend (m := 64) (0x020#12))) Mt) :
    SnpW live Dt DA S Q 0x80008010#64 R Mt :=
  swp_stepD nx_80008010 [6, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008010 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [6, 14])))) rfl hk

theorem nt_80008014 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008018#64 (upd R 28 ((R 27) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x80008014#64 R Mt :=
  swp_stepD nx_80008014 [27, 28] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008014 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 28 ∈ [27, 28])))) rfl hk

theorem nt_80008018 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000801c#64 (upd R 15 ((R 15) + sign_extend (m := 64) (0x008#12))) Mt) :
    SnpW live Dt DA S Q 0x80008018#64 R Mt :=
  swp_stepD nx_80008018 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008018 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem nt_8000801c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 14) ≠ (0#64) → SnpW live Dt DA S Q 0x800080d8#64 R Mt) (hF : ¬ ((R 14) ≠ (0#64)) → SnpW live Dt DA S Q 0x80008020#64 R Mt) :
    SnpW live Dt DA S Q 0x8000801c#64 R Mt := by
  by_cases hc : (R 14) ≠ (0#64)
  · exact
    swp_stepD nxT_8000801c [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_8000801c ChainFacts; chain_facts hm; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_8000801c [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_8000801c ChainFacts; chain_facts hm; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80008020 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008024#64 (upd R 14 ((R 6) &&& sign_extend (m := 64) (0x010#12))) Mt) :
    SnpW live Dt DA S Q 0x80008020#64 R Mt :=
  swp_stepD nx_80008020 [6, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008020 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [6, 14])))) rfl hk

theorem nt_80008024 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 14) ≠ (0#64) → SnpW live Dt DA S Q 0x800080d8#64 R Mt) (hF : ¬ ((R 14) ≠ (0#64)) → SnpW live Dt DA S Q 0x80008028#64 R Mt) :
    SnpW live Dt DA S Q 0x80008024#64 R Mt := by
  by_cases hc : (R 14) ≠ (0#64)
  · exact
    swp_stepD nxT_80008024 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80008024 ChainFacts; chain_facts hm; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80008024 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80008024 ChainFacts; chain_facts hm; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80008028 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000802c#64 (upd R 14 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80008028#64 R Mt :=
  swp_stepD nx_80008028 [2, 14] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008028 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [2, 14])))) rfl hk

theorem nt_8000802c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008030#64 (upd R 13 ((R 6) &&& sign_extend (m := 64) (0x040#12))) Mt) :
    SnpW live Dt DA S Q 0x8000802c#64 R Mt :=
  swp_stepD nx_8000802c [6, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000802c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [6, 13])))) rfl hk

theorem nt_80008030 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x80008034#64 (upd R 14 (ldv .lw Mt ((R 14) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80008030#64 R Mt :=
  swp_stepD nx_80008030 [14] [bytesAt (imgM Mt) ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 4] (accAddrs ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008030 ChainFacts; chain_facts hm; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem nt_80008034 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 13) ≠ (0#64) → SnpW live Dt DA S Q 0x8000803c#64 R Mt) (hF : ¬ ((R 13) ≠ (0#64)) → SnpW live Dt DA S Q 0x80008038#64 R Mt) :
    SnpW live Dt DA S Q 0x80008034#64 R Mt := by
  by_cases hc : (R 13) ≠ (0#64)
  · exact
    swp_stepD nxT_80008034 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80008034 ChainFacts; chain_facts hm; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80008034 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80008034 ChainFacts; chain_facts hm; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80008038 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800099c0#64 R Mt) :
    SnpW live Dt DA S Q 0x80008038#64 R Mt :=
  swp_stepD nx_80008038 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008038 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000804c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 13).toInt < (0#64).toInt → SnpW live Dt DA S Q 0x800080ec#64 R Mt) (hF : ¬ ((R 13).toInt < (0#64).toInt) → SnpW live Dt DA S Q 0x80008050#64 R Mt) :
    SnpW live Dt DA S Q 0x8000804c#64 R Mt := by
  by_cases hc : (R 13).toInt < (0#64).toInt
  · exact
    swp_stepD nxT_8000804c [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_8000804c ChainFacts; chain_facts hm; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_8000804c [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_8000804c ChainFacts; chain_facts hm; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80008050 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 20).toInt < (0#64).toInt → SnpW live Dt DA S Q 0x80008100#64 R Mt) (hF : ¬ ((R 20).toInt < (0#64).toInt) → SnpW live Dt DA S Q 0x80008054#64 R Mt) :
    SnpW live Dt DA S Q 0x80008050#64 R Mt := by
  by_cases hc : (R 20).toInt < (0#64).toInt
  · exact
    swp_stepD nxT_80008050 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80008050 ChainFacts; chain_facts hm; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80008050 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80008050 ChainFacts; chain_facts hm; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80008088 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 31) ≠ (0#64) → SnpW live Dt DA S Q 0x80008090#64 R Mt) (hF : ¬ ((R 31) ≠ (0#64)) → SnpW live Dt DA S Q 0x8000808c#64 R Mt) :
    SnpW live Dt DA S Q 0x80008088#64 R Mt := by
  by_cases hc : (R 31) ≠ (0#64)
  · exact
    swp_stepD nxT_80008088 [31] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80008088 ChainFacts; chain_facts hm; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80008088 [31] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80008088 ChainFacts; chain_facts hm; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_8000808c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000a830#64 R Mt) :
    SnpW live Dt DA S Q 0x8000808c#64 R Mt :=
  swp_stepD nx_8000808c [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000808c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800080d8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800080dc#64 (upd R 14 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800080d8#64 R Mt :=
  swp_stepD nx_800080d8 [2, 14] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800080d8 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [2, 14])))) rfl hk

theorem nt_800080dc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800080e0#64 (upd R 13 (ldv .ld Mt ((R 14) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x800080dc#64 R Mt :=
  swp_stepD nx_800080dc [13, 14] [bytesAt (imgM Mt) ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800080dc ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13, 14])))) rfl hk

theorem nt_800080e0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x800080e4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 15))])) :
    SnpW live Dt DA S Q 0x800080e0#64 R Mt :=
  swp_stepD nx_800080e0 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800080e0 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800080e4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800080e8#64 (upd R 14 ((R 13) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x800080e4#64 R Mt :=
  swp_stepD nx_800080e4 [13, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800080e4 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [13, 14])))) rfl hk

theorem nt_800080e8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (0#64).toInt ≤ (R 13).toInt → SnpW live Dt DA S Q 0x80008050#64 R Mt) (hF : ¬ ((0#64).toInt ≤ (R 13).toInt) → SnpW live Dt DA S Q 0x800080ec#64 R Mt) :
    SnpW live Dt DA S Q 0x800080e8#64 R Mt := by
  by_cases hc : (0#64).toInt ≤ (R 13).toInt
  · exact
    swp_stepD nxT_800080e8 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_800080e8 ChainFacts; chain_facts hm; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_800080e8 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_800080e8 ChainFacts; chain_facts hm; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_800080ec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800080f0#64 (upd R 15 ((0#64) + sign_extend (m := 64) (0x02d#12))) Mt) :
    SnpW live Dt DA S Q 0x800080ec#64 R Mt :=
  swp_stepD nx_800080ec [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800080ec ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem nt_800080f0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOKb ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1, S b)
    (hk : SnpW live Dt DA S Q 0x800080f4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat, 1, (R 15))])) :
    SnpW live Dt DA S Q 0x800080f0#64 R Mt :=
  swp_stepD nx_800080f0 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_800080f0 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_800080f4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x800080f8#64 (upd R 14 ((0#64) - (R 14))) Mt) :
    SnpW live Dt DA S Q 0x800080f4#64 R Mt :=
  swp_stepD nx_800080f4 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_800080f4 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem nt_800080f8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 20).toInt < (0#64).toInt → SnpW live Dt DA S Q 0x80008100#64 R Mt) (hF : ¬ ((R 20).toInt < (0#64).toInt) → SnpW live Dt DA S Q 0x800080fc#64 R Mt) :
    SnpW live Dt DA S Q 0x800080f8#64 R Mt := by
  by_cases hc : (R 20).toInt < (0#64).toInt
  · exact
    swp_stepD nxT_800080f8 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_800080f8 ChainFacts; chain_facts hm; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_800080f8 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_800080f8 ChainFacts; chain_facts hm; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80008100 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008104#64 (upd R 15 ((0#64) + sign_extend (m := 64) (0x009#12))) Mt) :
    SnpW live Dt DA S Q 0x80008100#64 R Mt :=
  swp_stepD nx_80008100 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008100 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem nt_80008104 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 15).toNat < (R 14).toNat → SnpW live Dt DA S Q 0x800082c8#64 R Mt) (hF : ¬ ((R 15).toNat < (R 14).toNat) → SnpW live Dt DA S Q 0x80008108#64 R Mt) :
    SnpW live Dt DA S Q 0x80008104#64 R Mt := by
  by_cases hc : (R 15).toNat < (R 14).toNat
  · exact
    swp_stepD nxT_80008104 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80008104 ChainFacts; chain_facts hm; exact (guard_bltu _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80008104 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80008104 ChainFacts; chain_facts hm; exact (guard_false (guard_bltu _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80008108 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000810c#64 (upd R 14 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 14) + sign_extend (m := 64) (0x030#12)) 31 0))) Mt) :
    SnpW live Dt DA S Q 0x80008108#64 R Mt :=
  swp_stepD nx_80008108 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008108 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem nt_8000810c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOKb ((R 2) + sign_extend (m := 64) (0x15b#12)).toNat)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x15b#12)).toNat 1, S b)
    (hk : SnpW live Dt DA S Q 0x80008110#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x15b#12)).toNat, 1, (R 14))])) :
    SnpW live Dt DA S Q 0x8000810c#64 R Mt :=
  swp_stepD nx_8000810c [2, 14] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x15b#12)).toNat 1) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000810c ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80008110 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80008114#64 (upd R 16 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 20) + sign_extend (m := 64) (0x000#12)) 31 0))) Mt) :
    SnpW live Dt DA S Q 0x80008110#64 R Mt :=
  swp_stepD nx_80008110 [16, 20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80008110 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 16 ∈ [16, 20])))) rfl hk

theorem nt_80008114 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 20).toInt ≤ (0#64).toInt → SnpW live Dt DA S Q 0x80008ea4#64 R Mt) (hF : ¬ ((R 20).toInt ≤ (0#64).toInt) → SnpW live Dt DA S Q 0x80008118#64 R Mt) :
    SnpW live Dt DA S Q 0x80008114#64 R Mt := by
  by_cases hc : (R 20).toInt ≤ (0#64).toInt
  · exact
    swp_stepD nxT_80008114 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80008114 ChainFacts; chain_facts hm; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80008114 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80008114 ChainFacts; chain_facts hm; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80008128 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000812c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (0#64))])) :
    SnpW live Dt DA S Q 0x80008128#64 R Mt :=
  swp_stepD nx_80008128 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80008128 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000812c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 30) = (0#64) → SnpW live Dt DA S Q 0x80008088#64 R Mt) (hF : ¬ ((R 30) = (0#64)) → SnpW live Dt DA S Q 0x80008130#64 R Mt) :
    SnpW live Dt DA S Q 0x8000812c#64 R Mt := by
  by_cases hc : (R 30) = (0#64)
  · exact
    swp_stepD nxT_8000812c [30] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_8000812c ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_8000812c [30] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_8000812c ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

end VsaIris.Sym
