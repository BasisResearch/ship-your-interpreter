import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000717c : List BBlock := [{ body := [mkLine 0x8000717c#64 0x000bb503#32], term := none }]
def ix_80007180 : List BBlock := [{ body := [mkLine 0x80007180#64 0x05813083#32], term := none }]
def ix_80007184 : List BBlock := [{ body := [mkLine 0x80007184#64 0x04013903#32], term := none }]
def ix_80007188 : List BBlock := [{ body := [mkLine 0x80007188#64 0x03013a03#32], term := none }]
def ix_8000718c : List BBlock := [{ body := [mkLine 0x8000718c#64 0x02013b03#32], term := none }]
def ix_80007190 : List BBlock := [{ body := [mkLine 0x80007190#64 0x01813b83#32], term := none }]
def ix_80007194 : List BBlock := [{ body := [mkLine 0x80007194#64 0x01013c03#32], term := none }]
def ix_80007198 : List BBlock := [{ body := [mkLine 0x80007198#64 0x06010113#32], term := none }]
def ix_8000719c : List BBlock := [⟨[], some (⟨0x8000719c#64, 0xe5dff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xe5#8, .j, 0, 0, 0x0#13, 0x1ffe5c#21, 0#12⟩ : TInstr)⟩]
def ix_8000a884 : List BBlock := [{ body := [mkLine 0x8000a884#64 0xdb010113#32], term := none }]
def ix_8000a888 : List BBlock := [{ body := [mkLine 0x8000a888#64 0x24113423#32], term := none }]
def ix_8000a88c : List BBlock := [{ body := [mkLine 0x8000a88c#64 0x24813023#32], term := none }]
def ix_8000a890 : List BBlock := [{ body := [mkLine 0x8000a890#64 0x23413023#32], term := none }]
def ix_8000a894 : List BBlock := [{ body := [mkLine 0x8000a894#64 0x21613823#32], term := none }]
def ix_8000a898 : List BBlock := [{ body := [mkLine 0x8000a898#64 0x00058a13#32], term := none }]
def ix_8000a89c : List BBlock := [{ body := [mkLine 0x8000a89c#64 0x00060b13#32], term := none }]
def ix_8000a8a0 : List BBlock := [{ body := [mkLine 0x8000a8a0#64 0x00d13c23#32], term := none }]
def ix_8000a8a4 : List BBlock := [{ body := [mkLine 0x8000a8a4#64 0x00050413#32], term := none }]
def ix_8000a8ac : List BBlock := [{ body := [mkLine 0x8000a8ac#64 0x00053783#32], term := none }]
def ix_8000a8b0 : List BBlock := [{ body := [mkLine 0x8000a8b0#64 0x00078513#32], term := none }]
def ix_8000a8b4 : List BBlock := [{ body := [mkLine 0x8000a8b4#64 0x04f13023#32], term := none }]
def ix_8000a8bc : List BBlock := [{ body := [mkLine 0x8000a8bc#64 0x02a13c23#32], term := none }]
def ix_8000a8c0 : List BBlock := [{ body := [mkLine 0x8000a8c0#64 0x00800613#32], term := none }]
def ix_8000a8c4 : List BBlock := [{ body := [mkLine 0x8000a8c4#64 0x0c810513#32], term := none }]
def ix_8000a8c8 : List BBlock := [{ body := [mkLine 0x8000a8c8#64 0x00000593#32], term := none }]
def ixT_8000a8d0 : List BBlock := [⟨[], some (⟨0x8000a8d0#64, 0x00040863#32, 0x63#8, 0x08#8, 0x04#8, 0x00#8, .br bop.BEQ true, 8, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000a8d0 : List BBlock := [⟨[], some (⟨0x8000a8d0#64, 0x00040863#32, 0x63#8, 0x08#8, 0x04#8, 0x00#8, .br bop.BEQ false, 8, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000a8d4 : List BBlock := [{ body := [mkLine 0x8000a8d4#64 0x04843783#32], term := none }]
def ixT_8000a8d8 : List BBlock := [⟨[], some (⟨0x8000a8d8#64, 0x00079463#32, 0x63#8, 0x94#8, 0x07#8, 0x00#8, .br bop.BNE true, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000a8d8 : List BBlock := [⟨[], some (⟨0x8000a8d8#64, 0x00079463#32, 0x63#8, 0x94#8, 0x07#8, 0x00#8, .br bop.BNE false, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000a8e0 : List BBlock := [{ body := [mkLine 0x8000a8e0#64 0x0b0a2703#32], term := none }]
def ix_8000a8e4 : List BBlock := [{ body := [mkLine 0x8000a8e4#64 0x010a1783#32], term := none }]
def ix_8000a8e8 : List BBlock := [{ body := [mkLine 0x8000a8e8#64 0x00177693#32], term := none }]
def ixT_8000a8ec : List BBlock := [⟨[], some (⟨0x8000a8ec#64, 0x3e068e63#32, 0x63#8, 0x8e#8, 0x06#8, 0x3e#8, .br bop.BEQ true, 13, 0, 0x3fc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000a8ec : List BBlock := [⟨[], some (⟨0x8000a8ec#64, 0x3e068e63#32, 0x63#8, 0x8e#8, 0x06#8, 0x3e#8, .br bop.BEQ false, 13, 0, 0x3fc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000a8fc : List BBlock := [{ body := [mkLine 0x8000a8fc#64 0xffffe6b7#32], term := none }]
def ix_8000a900 : List BBlock := [{ body := [mkLine 0x8000a900#64 0xfff68693#32], term := none }]
def ix_8000a904 : List BBlock := [{ body := [mkLine 0x8000a904#64 0x00002637#32], term := none }]
def ix_8000a908 : List BBlock := [{ body := [mkLine 0x8000a908#64 0x00d77733#32], term := none }]
def ix_8000a90c : List BBlock := [{ body := [mkLine 0x8000a90c#64 0x00c7e7b3#32], term := none }]
def ix_8000a910 : List BBlock := [{ body := [mkLine 0x8000a910#64 0x0aea2823#32], term := none }]
def ix_8000a914 : List BBlock := [{ body := [mkLine 0x8000a914#64 0x00fa1823#32], term := none }]
def ix_8000a918 : List BBlock := [{ body := [mkLine 0x8000a918#64 0x03271793#32], term := none }]
def ixT_8000a91c : List BBlock := [⟨[], some (⟨0x8000a91c#64, 0x0007d463#32, 0x63#8, 0xd4#8, 0x07#8, 0x00#8, .br bop.BGE true, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000a91c : List BBlock := [⟨[], some (⟨0x8000a91c#64, 0x0007d463#32, 0x63#8, 0xd4#8, 0x07#8, 0x00#8, .br bop.BGE false, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000a924 : List BBlock := [{ body := [mkLine 0x8000a924#64 0x010a1783#32], term := none }]
def ix_8000a928 : List BBlock := [{ body := [mkLine 0x8000a928#64 0x0087f713#32], term := none }]
def ixT_8000a92c : List BBlock := [⟨[], some (⟨0x8000a92c#64, 0x2a070063#32, 0x63#8, 0x00#8, 0x07#8, 0x2a#8, .br bop.BEQ true, 14, 0, 0x2a0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000a92c : List BBlock := [⟨[], some (⟨0x8000a92c#64, 0x2a070063#32, 0x63#8, 0x00#8, 0x07#8, 0x2a#8, .br bop.BEQ false, 14, 0, 0x2a0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000a930 : List BBlock := [{ body := [mkLine 0x8000a930#64 0x018a3703#32], term := none }]
def ixT_8000a934 : List BBlock := [⟨[], some (⟨0x8000a934#64, 0x28070c63#32, 0x63#8, 0x0c#8, 0x07#8, 0x28#8, .br bop.BEQ true, 14, 0, 0x298#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000a934 : List BBlock := [⟨[], some (⟨0x8000a934#64, 0x28070c63#32, 0x63#8, 0x0c#8, 0x07#8, 0x28#8, .br bop.BEQ false, 14, 0, 0x298#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000a938 : List BBlock := [{ body := [mkLine 0x8000a938#64 0x01a7f713#32], term := none }]
def ix_8000a93c : List BBlock := [{ body := [mkLine 0x8000a93c#64 0x00a00693#32], term := none }]
def ixT_8000a940 : List BBlock := [⟨[], some (⟨0x8000a940#64, 0x2ad70863#32, 0x63#8, 0x08#8, 0xd7#8, 0x2a#8, .br bop.BEQ true, 14, 13, 0x2b0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000a940 : List BBlock := [⟨[], some (⟨0x8000a940#64, 0x2ad70863#32, 0x63#8, 0x08#8, 0xd7#8, 0x2a#8, .br bop.BEQ false, 14, 13, 0x2b0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000a944 : List BBlock := [{ body := [mkLine 0x8000a944#64 0x21513c23#32], term := none }]
def ix_8000a948 : List BBlock := [{ body := [mkLine 0x8000a948#64 0x16010a93#32], term := none }]
def ix_8000a94c : List BBlock := [{ body := [mkLine 0x8000a94c#64 0x22913c23#32], term := none }]
def ix_8000a950 : List BBlock := [{ body := [mkLine 0x8000a950#64 0x23213823#32], term := none }]
def ix_8000a954 : List BBlock := [{ body := [mkLine 0x8000a954#64 0x23313423#32], term := none }]
def ix_8000a958 : List BBlock := [{ body := [mkLine 0x8000a958#64 0x21713423#32], term := none }]
def ix_8000a95c : List BBlock := [{ body := [mkLine 0x8000a95c#64 0x21813023#32], term := none }]
def ix_8000a960 : List BBlock := [{ body := [mkLine 0x8000a960#64 0x1f913c23#32], term := none }]
def ix_8000a964 : List BBlock := [{ body := [mkLine 0x8000a964#64 0x1fa13823#32], term := none }]
def ix_8000a968 : List BBlock := [{ body := [mkLine 0x8000a968#64 0x1fb13423#32], term := none }]
def ix_8000a96c : List BBlock := [{ body := [mkLine 0x8000a96c#64 0x0e013823#32], term := none }]
def ix_8000a970 : List BBlock := [{ body := [mkLine 0x8000a970#64 0x0e012423#32], term := none }]
def ix_8000a974 : List BBlock := [{ body := [mkLine 0x8000a974#64 0x0f513023#32], term := none }]
def ix_8000a978 : List BBlock := [{ body := [mkLine 0x8000a978#64 0x000a8b93#32], term := none }]
def ix_8000a97c : List BBlock := [{ body := [mkLine 0x8000a97c#64 0x02013423#32], term := none }]
def ix_8000a980 : List BBlock := [{ body := [mkLine 0x8000a980#64 0x04013423#32], term := none }]
def ix_8000a984 : List BBlock := [{ body := [mkLine 0x8000a984#64 0x04013823#32], term := none }]
def ix_8000a988 : List BBlock := [{ body := [mkLine 0x8000a988#64 0x06013023#32], term := none }]
def ix_8000a98c : List BBlock := [{ body := [mkLine 0x8000a98c#64 0x08013823#32], term := none }]
def ix_8000a990 : List BBlock := [{ body := [mkLine 0x8000a990#64 0x04013c23#32], term := none }]
def ix_8000a994 : List BBlock := [{ body := [mkLine 0x8000a994#64 0x00013823#32], term := none }]
def ix_8000a998 : List BBlock := [{ body := [mkLine 0x8000a998#64 0x28818493#32], term := none }]
def ix_8000a99c : List BBlock := [{ body := [mkLine 0x8000a99c#64 0x02500993#32], term := none }]
def ix_8000a9a0 : List BBlock := [{ body := [mkLine 0x8000a9a0#64 0x01000913#32], term := none }]
def ix_8000a9a4 : List BBlock := [{ body := [mkLine 0x8000a9a4#64 0x000b0c13#32], term := none }]
def ix_8000a9a8 : List BBlock := [{ body := [mkLine 0x8000a9a8#64 0x00813023#32], term := none }]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_8000717c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x80007180#64 (upd R 10 (ldv .ld Mt ((R 23) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000717c#64 R Mt :=
  swp_stepD ix_8000717c [10, 23] [bytesAt (imgM Mt) ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000717c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 23])))) rfl hk

theorem it_80007180 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x80007184#64 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x058#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x80007180#64 R Mt :=
  swp_stepD ix_80007180 [1, 2] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80007180 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 1 ∈ [1, 2])))) rfl hk

theorem it_80007184 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x80007188#64 (upd R 18 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x040#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x80007184#64 R Mt :=
  swp_stepD ix_80007184 [2, 18] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80007184 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [2, 18])))) rfl hk

theorem it_80007188 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000718c#64 (upd R 20 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x030#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x80007188#64 R Mt :=
  swp_stepD ix_80007188 [2, 20] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80007188 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [2, 20])))) rfl hk

theorem it_8000718c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x80007190#64 (upd R 22 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000718c#64 R Mt :=
  swp_stepD ix_8000718c [2, 22] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000718c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [2, 22])))) rfl hk

theorem it_80007190 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x80007194#64 (upd R 23 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x80007190#64 R Mt :=
  swp_stepD ix_80007190 [2, 23] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80007190 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [2, 23])))) rfl hk

theorem it_80007194 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x80007198#64 (upd R 24 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x80007194#64 R Mt :=
  swp_stepD ix_80007194 [2, 24] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80007194 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 24 ∈ [2, 24])))) rfl hk

theorem it_80007198 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000719c#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0x060#12))) Mt) :
    NW live Dt DA S Q 0x80007198#64 R Mt :=
  swp_stepD ix_80007198 [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80007198 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem it_8000719c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80006ff8#64 R Mt) :
    NW live Dt DA S Q 0x8000719c#64 R Mt :=
  swp_stepD ix_8000719c [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000719c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a884 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a888#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0xdb0#12))) Mt) :
    NW live Dt DA S Q 0x8000a884#64 R Mt :=
  swp_stepD ix_8000a884 [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a884 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem it_8000a888 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x248#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x248#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a88c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x248#12)).toNat, 8, (R 1))])) :
    NW live Dt DA S Q 0x8000a888#64 R Mt :=
  swp_stepD ix_8000a888 [1, 2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x248#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a888 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a88c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x240#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x240#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a890#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x240#12)).toNat, 8, (R 8))])) :
    NW live Dt DA S Q 0x8000a88c#64 R Mt :=
  swp_stepD ix_8000a88c [2, 8] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x240#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a88c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a890 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x220#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x220#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a894#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x220#12)).toNat, 8, (R 20))])) :
    NW live Dt DA S Q 0x8000a890#64 R Mt :=
  swp_stepD ix_8000a890 [2, 20] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x220#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a890 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a894 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x210#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x210#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a898#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x210#12)).toNat, 8, (R 22))])) :
    NW live Dt DA S Q 0x8000a894#64 R Mt :=
  swp_stepD ix_8000a894 [2, 22] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x210#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a894 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a898 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a89c#64 (upd R 20 ((R 11) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000a898#64 R Mt :=
  swp_stepD ix_8000a898 [11, 20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a898 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [11, 20])))) rfl hk

theorem it_8000a89c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a8a0#64 (upd R 22 ((R 12) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000a89c#64 R Mt :=
  swp_stepD ix_8000a89c [12, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a89c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [12, 22])))) rfl hk

theorem it_8000a8a0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a8a4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 13))])) :
    NW live Dt DA S Q 0x8000a8a0#64 R Mt :=
  swp_stepD ix_8000a8a0 [2, 13] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a8a0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a8a4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a8a8#64 (upd R 8 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000a8a4#64 R Mt :=
  swp_stepD ix_8000a8a4 [8, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a8a4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000a8a8 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000a8a8 [0xef#8, 0x50#8, 0x10#8, 0x1b#8], live p.1) :
    JalExec (vsaModel live) 0x8000a8a8 [0xef#8, 0x50#8, 0x10#8, 0x1b#8] 0x80010258#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000a8a8, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000a8a9, .discard, 0x50#8) (by simp [codeFoot])
  have hb2 := hb (0x8000a8aa, .discard, 0x10#8) (by simp [codeFoot])
  have hb3 := hb (0x8000a8ab, .discard, 0x1b#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000a8a8#64) vm (0x1b1050ef#32) (0x0059b0#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000a8a8#64) 4)
      (0xef#8) (0x50#8) (0x10#8) (0x1b#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0x1b1050ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000a8a8#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80010258#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000a8a8#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000a8a8 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000a8a8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80010258#64 (upd R 1 (BitVec.ofNat 64 (0x8000a8a8 + 4))) Mt) :
    NW live Dt DA S Q 0x8000a8a8#64 R Mt :=
  swp_jal 0x8000a8a8 [0xef#8, 0x50#8, 0x10#8, 0x1b#8] 0x80010258#64 (jalx_8000a8a8 live (fun p hp => hlive _ (stdio_code_8000a8a8 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000a8a8 p hp)) (by decide) (by decide) rfl hk

theorem it_8000a8ac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 10) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 10) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a8b0#64 (upd R 15 (ldv .ld Mt ((R 10) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000a8ac#64 R Mt :=
  swp_stepD ix_8000a8ac [10, 15] [bytesAt (imgM Mt) ((R 10) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 10) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a8ac ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [10, 15])))) rfl hk

theorem it_8000a8b0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a8b4#64 (upd R 10 ((R 15) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000a8b0#64 R Mt :=
  swp_stepD ix_8000a8b0 [10, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a8b0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 15])))) rfl hk

theorem it_8000a8b4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a8b8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x040#12)).toNat, 8, (R 15))])) :
    NW live Dt DA S Q 0x8000a8b4#64 R Mt :=
  swp_stepD ix_8000a8b4 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a8b4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000a8b8 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000a8b8 [0xef#8, 0xc0#8, 0x8f#8, 0xc3#8], live p.1) :
    JalExec (vsaModel live) 0x8000a8b8 [0xef#8, 0xc0#8, 0x8f#8, 0xc3#8] 0x80006cf0#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000a8b8, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000a8b9, .discard, 0xc0#8) (by simp [codeFoot])
  have hb2 := hb (0x8000a8ba, .discard, 0x8f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000a8bb, .discard, 0xc3#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000a8b8#64) vm (0xc38fc0ef#32) (0x1fc438#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000a8b8#64) 4)
      (0xef#8) (0xc0#8) (0x8f#8) (0xc3#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xc38fc0ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000a8b8#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80006cf0#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000a8b8#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000a8b8 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000a8b8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80006cf0#64 (upd R 1 (BitVec.ofNat 64 (0x8000a8b8 + 4))) Mt) :
    NW live Dt DA S Q 0x8000a8b8#64 R Mt :=
  swp_jal 0x8000a8b8 [0xef#8, 0xc0#8, 0x8f#8, 0xc3#8] 0x80006cf0#64 (jalx_8000a8b8 live (fun p hp => hlive _ (stdio_code_8000a8b8 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000a8b8 p hp)) (by decide) (by decide) rfl hk

theorem it_8000a8bc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a8c0#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x038#12)).toNat, 8, (R 10))])) :
    NW live Dt DA S Q 0x8000a8bc#64 R Mt :=
  swp_stepD ix_8000a8bc [2, 10] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a8bc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a8c0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a8c4#64 (upd R 12 ((0#64) + sign_extend (m := 64) (0x008#12))) Mt) :
    NW live Dt DA S Q 0x8000a8c0#64 R Mt :=
  swp_stepD ix_8000a8c0 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a8c0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12])))) rfl hk

theorem it_8000a8c4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a8c8#64 (upd R 10 ((R 2) + sign_extend (m := 64) (0x0c8#12))) Mt) :
    NW live Dt DA S Q 0x8000a8c4#64 R Mt :=
  swp_stepD ix_8000a8c4 [2, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a8c4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [2, 10])))) rfl hk

theorem it_8000a8c8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a8cc#64 (upd R 11 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000a8c8#64 R Mt :=
  swp_stepD ix_8000a8c8 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a8c8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000a8cc (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000a8cc [0xef#8, 0xc0#8, 0x0f#8, 0xa2#8], live p.1) :
    JalExec (vsaModel live) 0x8000a8cc [0xef#8, 0xc0#8, 0x0f#8, 0xa2#8] 0x80006aec#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000a8cc, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000a8cd, .discard, 0xc0#8) (by simp [codeFoot])
  have hb2 := hb (0x8000a8ce, .discard, 0x0f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000a8cf, .discard, 0xa2#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000a8cc#64) vm (0xa20fc0ef#32) (0x1fc220#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000a8cc#64) 4)
      (0xef#8) (0xc0#8) (0x0f#8) (0xa2#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xa20fc0ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000a8cc#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80006aec#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000a8cc#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000a8cc + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000a8cc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80006aec#64 (upd R 1 (BitVec.ofNat 64 (0x8000a8cc + 4))) Mt) :
    NW live Dt DA S Q 0x8000a8cc#64 R Mt :=
  swp_jal 0x8000a8cc [0xef#8, 0xc0#8, 0x0f#8, 0xa2#8] 0x80006aec#64 (jalx_8000a8cc live (fun p hp => hlive _ (stdio_code_8000a8cc p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000a8cc p hp)) (by decide) (by decide) rfl hk

theorem it_8000a8d0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 8) = (0#64) → NW live Dt DA S Q 0x8000a8e0#64 R Mt) (hF : ¬ ((R 8) = (0#64)) → NW live Dt DA S Q 0x8000a8d4#64 R Mt) :
    NW live Dt DA S Q 0x8000a8d0#64 R Mt := by
  by_cases hc : (R 8) = (0#64)
  · exact
    swp_stepD ixT_8000a8d0 [8] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000a8d0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000a8d0 [8] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000a8d0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000a8d4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x048#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x048#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a8d8#64 (upd R 15 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x048#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000a8d4#64 R Mt :=
  swp_stepD ix_8000a8d4 [8, 15] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x048#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x048#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a8d4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [8, 15])))) rfl hk

theorem it_8000a8d8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) ≠ (0#64) → NW live Dt DA S Q 0x8000a8e0#64 R Mt) (hF : ¬ ((R 15) ≠ (0#64)) → NW live Dt DA S Q 0x8000a8dc#64 R Mt) :
    NW live Dt DA S Q 0x8000a8d8#64 R Mt := by
  by_cases hc : (R 15) ≠ (0#64)
  · exact
    swp_stepD ixT_8000a8d8 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000a8d8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000a8d8 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000a8d8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000a8e0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000a8e4#64 (upd R 14 (ldv .lw Mt ((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000a8e0#64 R Mt :=
  swp_stepD ix_8000a8e0 [14, 20] [bytesAt (imgM Mt) ((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat 4] (accAddrs ((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a8e0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 20])))) rfl hk

theorem it_8000a8e4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000a8e8#64 (upd R 15 (ldv .lh Mt ((R 20) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000a8e4#64 R Mt :=
  swp_stepD ix_8000a8e4 [15, 20] [bytesAt (imgM Mt) ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2] (accAddrs ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a8e4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15, 20])))) rfl hk

theorem it_8000a8e8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a8ec#64 (upd R 13 ((R 14) &&& sign_extend (m := 64) (0x001#12))) Mt) :
    NW live Dt DA S Q 0x8000a8e8#64 R Mt :=
  swp_stepD ix_8000a8e8 [13, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a8e8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13, 14])))) rfl hk

theorem it_8000a8ec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 13) = (0#64) → NW live Dt DA S Q 0x8000ace8#64 R Mt) (hF : ¬ ((R 13) = (0#64)) → NW live Dt DA S Q 0x8000a8f0#64 R Mt) :
    NW live Dt DA S Q 0x8000a8ec#64 R Mt := by
  by_cases hc : (R 13) = (0#64)
  · exact
    swp_stepD ixT_8000a8ec [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000a8ec ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000a8ec [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000a8ec ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000a8fc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a900#64 (upd R 13 ((sign_extend (m := 64) ((0xffffe#20) +++ (0x000#12))))) Mt) :
    NW live Dt DA S Q 0x8000a8fc#64 R Mt :=
  swp_stepD ix_8000a8fc [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a8fc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13])))) rfl hk

theorem it_8000a900 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a904#64 (upd R 13 ((R 13) + sign_extend (m := 64) (0xfff#12))) Mt) :
    NW live Dt DA S Q 0x8000a900#64 R Mt :=
  swp_stepD ix_8000a900 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a900 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13])))) rfl hk

theorem it_8000a904 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a908#64 (upd R 12 ((sign_extend (m := 64) ((0x00002#20) +++ (0x000#12))))) Mt) :
    NW live Dt DA S Q 0x8000a904#64 R Mt :=
  swp_stepD ix_8000a904 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a904 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12])))) rfl hk

theorem it_8000a908 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a90c#64 (upd R 14 ((R 14) &&& (R 13))) Mt) :
    NW live Dt DA S Q 0x8000a908#64 R Mt :=
  swp_stepD ix_8000a908 [13, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a908 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [13, 14])))) rfl hk

theorem it_8000a90c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a910#64 (upd R 15 ((R 15) ||| (R 12))) Mt) :
    NW live Dt DA S Q 0x8000a90c#64 R Mt :=
  swp_stepD ix_8000a90c [12, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a90c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [12, 15])))) rfl hk

theorem it_8000a910 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000a914#64 R (writeLog Mt [(((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat, 4, (R 14))])) :
    NW live Dt DA S Q 0x8000a910#64 R Mt :=
  swp_stepD ix_8000a910 [14, 20] [] [] (accAddrs ((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a910 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a914 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hS : ∀ b ∈ accAddrs ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000a918#64 R (writeLog Mt [(((R 20) + sign_extend (m := 64) (0x010#12)).toNat, 2, (R 15))])) :
    NW live Dt DA S Q 0x8000a914#64 R Mt :=
  swp_stepD ix_8000a914 [15, 20] [] [] (accAddrs ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a914 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a918 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a91c#64 (upd R 15 (shift_bits_left (R 14) (Sail.BitVec.extractLsb (0x32#6) 5 0))) Mt) :
    NW live Dt DA S Q 0x8000a918#64 R Mt :=
  swp_stepD ix_8000a918 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a918 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [14, 15])))) rfl hk

theorem it_8000a91c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (0#64).toInt ≤ (R 15).toInt → NW live Dt DA S Q 0x8000a924#64 R Mt) (hF : ¬ ((0#64).toInt ≤ (R 15).toInt) → NW live Dt DA S Q 0x8000a920#64 R Mt) :
    NW live Dt DA S Q 0x8000a91c#64 R Mt := by
  by_cases hc : (0#64).toInt ≤ (R 15).toInt
  · exact
    swp_stepD ixT_8000a91c [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000a91c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000a91c [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000a91c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000a924 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000a928#64 (upd R 15 (ldv .lh Mt ((R 20) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000a924#64 R Mt :=
  swp_stepD ix_8000a924 [15, 20] [bytesAt (imgM Mt) ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2] (accAddrs ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a924 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15, 20])))) rfl hk

theorem it_8000a928 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a92c#64 (upd R 14 ((R 15) &&& sign_extend (m := 64) (0x008#12))) Mt) :
    NW live Dt DA S Q 0x8000a928#64 R Mt :=
  swp_stepD ix_8000a928 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a928 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 15])))) rfl hk

theorem it_8000a92c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 14) = (0#64) → NW live Dt DA S Q 0x8000abcc#64 R Mt) (hF : ¬ ((R 14) = (0#64)) → NW live Dt DA S Q 0x8000a930#64 R Mt) :
    NW live Dt DA S Q 0x8000a92c#64 R Mt := by
  by_cases hc : (R 14) = (0#64)
  · exact
    swp_stepD ixT_8000a92c [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000a92c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000a92c [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000a92c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000a930 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 20) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 20) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a934#64 (upd R 14 (ldv .ld Mt ((R 20) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000a930#64 R Mt :=
  swp_stepD ix_8000a930 [14, 20] [bytesAt (imgM Mt) ((R 20) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 20) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a930 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 20])))) rfl hk

theorem it_8000a934 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 14) = (0#64) → NW live Dt DA S Q 0x8000abcc#64 R Mt) (hF : ¬ ((R 14) = (0#64)) → NW live Dt DA S Q 0x8000a938#64 R Mt) :
    NW live Dt DA S Q 0x8000a934#64 R Mt := by
  by_cases hc : (R 14) = (0#64)
  · exact
    swp_stepD ixT_8000a934 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000a934 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000a934 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000a934 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000a938 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a93c#64 (upd R 14 ((R 15) &&& sign_extend (m := 64) (0x01a#12))) Mt) :
    NW live Dt DA S Q 0x8000a938#64 R Mt :=
  swp_stepD ix_8000a938 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a938 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 15])))) rfl hk

theorem it_8000a93c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a940#64 (upd R 13 ((0#64) + sign_extend (m := 64) (0x00a#12))) Mt) :
    NW live Dt DA S Q 0x8000a93c#64 R Mt :=
  swp_stepD ix_8000a93c [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a93c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13])))) rfl hk

theorem it_8000a940 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 14) = (R 13) → NW live Dt DA S Q 0x8000abf0#64 R Mt) (hF : ¬ ((R 14) = (R 13)) → NW live Dt DA S Q 0x8000a944#64 R Mt) :
    NW live Dt DA S Q 0x8000a940#64 R Mt := by
  by_cases hc : (R 14) = (R 13)
  · exact
    swp_stepD ixT_8000a940 [13, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000a940 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000a940 [13, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000a940 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000a944 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x218#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x218#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a948#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x218#12)).toNat, 8, (R 21))])) :
    NW live Dt DA S Q 0x8000a944#64 R Mt :=
  swp_stepD ix_8000a944 [2, 21] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x218#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a944 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a948 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a94c#64 (upd R 21 ((R 2) + sign_extend (m := 64) (0x160#12))) Mt) :
    NW live Dt DA S Q 0x8000a948#64 R Mt :=
  swp_stepD ix_8000a948 [2, 21] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a948 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 21 ∈ [2, 21])))) rfl hk

theorem it_8000a94c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x238#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x238#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a950#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x238#12)).toNat, 8, (R 9))])) :
    NW live Dt DA S Q 0x8000a94c#64 R Mt :=
  swp_stepD ix_8000a94c [2, 9] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x238#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a94c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a950 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x230#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x230#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a954#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x230#12)).toNat, 8, (R 18))])) :
    NW live Dt DA S Q 0x8000a950#64 R Mt :=
  swp_stepD ix_8000a950 [2, 18] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x230#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a950 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a954 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x228#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x228#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a958#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x228#12)).toNat, 8, (R 19))])) :
    NW live Dt DA S Q 0x8000a954#64 R Mt :=
  swp_stepD ix_8000a954 [2, 19] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x228#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a954 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a958 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x208#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x208#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a95c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x208#12)).toNat, 8, (R 23))])) :
    NW live Dt DA S Q 0x8000a958#64 R Mt :=
  swp_stepD ix_8000a958 [2, 23] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x208#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a958 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a95c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x200#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x200#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a960#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x200#12)).toNat, 8, (R 24))])) :
    NW live Dt DA S Q 0x8000a95c#64 R Mt :=
  swp_stepD ix_8000a95c [2, 24] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x200#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a95c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a960 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x1f8#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x1f8#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a964#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x1f8#12)).toNat, 8, (R 25))])) :
    NW live Dt DA S Q 0x8000a960#64 R Mt :=
  swp_stepD ix_8000a960 [2, 25] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x1f8#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a960 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a964 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x1f0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x1f0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a968#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x1f0#12)).toNat, 8, (R 26))])) :
    NW live Dt DA S Q 0x8000a964#64 R Mt :=
  swp_stepD ix_8000a964 [2, 26] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x1f0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a964 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a968 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x1e8#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x1e8#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a96c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x1e8#12)).toNat, 8, (R 27))])) :
    NW live Dt DA S Q 0x8000a968#64 R Mt :=
  swp_stepD ix_8000a968 [2, 27] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x1e8#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a968 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a96c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a970#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000a96c#64 R Mt :=
  swp_stepD ix_8000a96c [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a96c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a970 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000a974#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat, 4, (0#64))])) :
    NW live Dt DA S Q 0x8000a970#64 R Mt :=
  swp_stepD ix_8000a970 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a970 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a974 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0e0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0e0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a978#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0e0#12)).toNat, 8, (R 21))])) :
    NW live Dt DA S Q 0x8000a974#64 R Mt :=
  swp_stepD ix_8000a974 [2, 21] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0e0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a974 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a978 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a97c#64 (upd R 23 ((R 21) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000a978#64 R Mt :=
  swp_stepD ix_8000a978 [21, 23] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a978 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [21, 23])))) rfl hk

theorem it_8000a97c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a980#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x028#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000a97c#64 R Mt :=
  swp_stepD ix_8000a97c [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a97c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a980 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x048#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x048#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a984#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x048#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000a980#64 R Mt :=
  swp_stepD ix_8000a980 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x048#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a980 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a984 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a988#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x050#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000a984#64 R Mt :=
  swp_stepD ix_8000a984 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a984 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a988 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x060#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x060#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a98c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x060#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000a988#64 R Mt :=
  swp_stepD ix_8000a988 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x060#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a988 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a98c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x090#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x090#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a990#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x090#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000a98c#64 R Mt :=
  swp_stepD ix_8000a98c [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x090#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a98c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a990 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a994#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x058#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000a990#64 R Mt :=
  swp_stepD ix_8000a990 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a990 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a994 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a998#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x010#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000a994#64 R Mt :=
  swp_stepD ix_8000a994 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a994 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000a998 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a99c#64 (upd R 9 ((0x8001b510#64) + sign_extend (m := 64) (0x288#12))) Mt) :
    NW live Dt DA S Q 0x8000a998#64 R Mt :=
  swp_stepD ix_8000a998 [3, 9] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a998 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun _ => rfl) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [3, 9])))) rfl hk

theorem it_8000a99c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a9a0#64 (upd R 19 ((0#64) + sign_extend (m := 64) (0x025#12))) Mt) :
    NW live Dt DA S Q 0x8000a99c#64 R Mt :=
  swp_stepD ix_8000a99c [19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a99c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [19])))) rfl hk

theorem it_8000a9a0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a9a4#64 (upd R 18 ((0#64) + sign_extend (m := 64) (0x010#12))) Mt) :
    NW live Dt DA S Q 0x8000a9a0#64 R Mt :=
  swp_stepD ix_8000a9a0 [18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a9a0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [18])))) rfl hk

theorem it_8000a9a4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a9a8#64 (upd R 24 ((R 22) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000a9a4#64 R Mt :=
  swp_stepD ix_8000a9a4 [22, 24] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000a9a4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 24 ∈ [22, 24])))) rfl hk

theorem it_8000a9a8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000a9ac#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x000#12)).toNat, 8, (R 8))])) :
    NW live Dt DA S Q 0x8000a9a8#64 R Mt :=
  swp_stepD ix_8000a9a8 [2, 8] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000a9a8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
