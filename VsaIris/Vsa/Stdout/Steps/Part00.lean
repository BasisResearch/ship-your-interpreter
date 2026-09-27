import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ixT_8000003c : List BBlock := [⟨[], some (⟨0x8000003c#64, 0x02060463#32, 0x63#8, 0x04#8, 0x06#8, 0x02#8, .br bop.BEQ true, 12, 0, 0x28#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000003c : List BBlock := [⟨[], some (⟨0x8000003c#64, 0x02060463#32, 0x63#8, 0x04#8, 0x06#8, 0x02#8, .br bop.BEQ false, 12, 0, 0x28#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_80000040 : List BBlock := [{ body := [mkLine 0x80000040#64 0x10100713#32], term := none }]
def ix_80000044 : List BBlock := [{ body := [mkLine 0x80000044#64 0x00c586b3#32], term := none }]
def ix_80000048 : List BBlock := [{ body := [mkLine 0x80000048#64 0x03071713#32], term := none }]
def ix_8000004c : List BBlock := [{ body := [mkLine 0x8000004c#64 0x0005c783#32], term := none }]
def ix_80000050 : List BBlock := [{ body := [mkLine 0x80000050#64 0x00158593#32], term := none }]
def ix_80000054 : List BBlock := [{ body := [mkLine 0x80000054#64 0x00e7e7b3#32], term := none }]
def ix_80000058 : List BBlock := [{ body := [mkLine 0x80000058#64 0x0001b817#32], term := none }]
def ixT_80000060 : List BBlock := [⟨[], some (⟨0x80000060#64, 0xfed596e3#32, 0xe3#8, 0x96#8, 0xd5#8, 0xfe#8, .br bop.BNE true, 11, 13, 0x1fec#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_80000060 : List BBlock := [⟨[], some (⟨0x80000060#64, 0xfed596e3#32, 0xe3#8, 0x96#8, 0xd5#8, 0xfe#8, .br bop.BNE false, 11, 13, 0x1fec#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_80000064 : List BBlock := [{ body := [mkLine 0x80000064#64 0x00060513#32], term := none }]
def ix_80000068 : List BBlock := [⟨[], some (⟨0x80000068#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_80000098 : List BBlock := [{ body := [mkLine 0x80000098#64 0x00000513#32], term := none }]
def ix_8000009c : List BBlock := [⟨[], some (⟨0x8000009c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixS_80004640 : List BBlock := [{ body := [mkLine 0x80004640#64 0x00050613#32], term := none }]
def ixS_80004644 : List BBlock := [{ body := [mkLine 0x80004644#64 0x00000513#32], term := none }]
def ixS_80004648 : List BBlock := [{ body := [mkLine 0x80004648#64 0x0015f693#32], term := none }]
def ixTS_8000464c : List BBlock := [⟨[], some (⟨0x8000464c#64, 0x00068463#32, 0x63#8, 0x84#8, 0x06#8, 0x00#8, .br bop.BEQ true, 13, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixFS_8000464c : List BBlock := [⟨[], some (⟨0x8000464c#64, 0x00068463#32, 0x63#8, 0x84#8, 0x06#8, 0x00#8, .br bop.BEQ false, 13, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixS_80004650 : List BBlock := [{ body := [mkLine 0x80004650#64 0x00c50533#32], term := none }]
def ixS_80004654 : List BBlock := [{ body := [mkLine 0x80004654#64 0x0015d593#32], term := none }]
def ixS_80004658 : List BBlock := [{ body := [mkLine 0x80004658#64 0x00161613#32], term := none }]
def ixTS_8000465c : List BBlock := [⟨[], some (⟨0x8000465c#64, 0xfe0596e3#32, 0xe3#8, 0x96#8, 0x05#8, 0xfe#8, .br bop.BNE true, 11, 0, 0x1fec#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixFS_8000465c : List BBlock := [⟨[], some (⟨0x8000465c#64, 0xfe0596e3#32, 0xe3#8, 0x96#8, 0x05#8, 0xfe#8, .br bop.BNE false, 11, 0, 0x1fec#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixS_80004660 : List BBlock := [⟨[], some (⟨0x80004660#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000477c : List BBlock := [{ body := [mkLine 0x8000477c#64 0x4a01b783#32], term := none }]
def ixT_80004780 : List BBlock := [⟨[], some (⟨0x80004780#64, 0x00078463#32, 0x63#8, 0x84#8, 0x07#8, 0x00#8, .br bop.BEQ true, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_80004780 : List BBlock := [⟨[], some (⟨0x80004780#64, 0x00078463#32, 0x63#8, 0x84#8, 0x07#8, 0x00#8, .br bop.BEQ false, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_80005078 : List BBlock := [{ body := [mkLine 0x80005078#64 0xf9010113#32], term := none }]
def ix_8000507c : List BBlock := [{ body := [mkLine 0x8000507c#64 0x04913c23#32], term := none }]
def ix_80005080 : List BBlock := [{ body := [mkLine 0x80005080#64 0x00b13c23#32], term := none }]
def ix_80005084 : List BBlock := [{ body := [mkLine 0x80005084#64 0x00050493#32], term := none }]
def ix_80005088 : List BBlock := [{ body := [mkLine 0x80005088#64 0x00060593#32], term := none }]
def ix_8000508c : List BBlock := [{ body := [mkLine 0x8000508c#64 0x00068513#32], term := none }]
def ix_80005090 : List BBlock := [{ body := [mkLine 0x80005090#64 0x06813023#32], term := none }]
def ix_80005094 : List BBlock := [{ body := [mkLine 0x80005094#64 0x05213823#32], term := none }]
def ix_80005098 : List BBlock := [{ body := [mkLine 0x80005098#64 0x05313423#32], term := none }]
def ix_8000509c : List BBlock := [{ body := [mkLine 0x8000509c#64 0x00070413#32], term := none }]
def ix_800050a0 : List BBlock := [{ body := [mkLine 0x800050a0#64 0x00068993#32], term := none }]
def ix_800050a4 : List BBlock := [{ body := [mkLine 0x800050a4#64 0x06113423#32], term := none }]
def ix_800050a8 : List BBlock := [{ body := [mkLine 0x800050a8#64 0x00060913#32], term := none }]
def ix_800050b0 : List BBlock := [{ body := [mkLine 0x800050b0#64 0x01810713#32], term := none }]
def ix_800050b4 : List BBlock := [{ body := [mkLine 0x800050b4#64 0x00100793#32], term := none }]
def ix_800050b8 : List BBlock := [{ body := [mkLine 0x800050b8#64 0x02a13023#32], term := none }]
def ix_800050bc : List BBlock := [{ body := [mkLine 0x800050bc#64 0x02a13c23#32], term := none }]
def ix_800050c0 : List BBlock := [{ body := [mkLine 0x800050c0#64 0x02e13423#32], term := none }]
def ix_800050c4 : List BBlock := [{ body := [mkLine 0x800050c4#64 0x02f12823#32], term := none }]
def ix_800050c8 : List BBlock := [{ body := [mkLine 0x800050c8#64 0x00050693#32], term := none }]
def ixT_800050cc : List BBlock := [⟨[], some (⟨0x800050cc#64, 0x00048663#32, 0x63#8, 0x86#8, 0x04#8, 0x00#8, .br bop.BEQ true, 9, 0, 0xc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_800050cc : List BBlock := [⟨[], some (⟨0x800050cc#64, 0x00048663#32, 0x63#8, 0x86#8, 0x04#8, 0x00#8, .br bop.BEQ false, 9, 0, 0xc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_800050d0 : List BBlock := [{ body := [mkLine 0x800050d0#64 0x0484b783#32], term := none }]
def ixT_800050d4 : List BBlock := [⟨[], some (⟨0x800050d4#64, 0x16078463#32, 0x63#8, 0x84#8, 0x07#8, 0x16#8, .br bop.BEQ true, 15, 0, 0x168#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_800050d4 : List BBlock := [⟨[], some (⟨0x800050d4#64, 0x16078463#32, 0x63#8, 0x84#8, 0x07#8, 0x16#8, .br bop.BEQ false, 15, 0, 0x168#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_800050d8 : List BBlock := [{ body := [mkLine 0x800050d8#64 0x0b042783#32], term := none }]
def ix_800050dc : List BBlock := [{ body := [mkLine 0x800050dc#64 0x01041703#32], term := none }]
def ix_800050e0 : List BBlock := [{ body := [mkLine 0x800050e0#64 0x0017f613#32], term := none }]
def ixT_800050e4 : List BBlock := [⟨[], some (⟨0x800050e4#64, 0x06060263#32, 0x63#8, 0x02#8, 0x06#8, 0x06#8, .br bop.BEQ true, 12, 0, 0x64#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_800050e4 : List BBlock := [⟨[], some (⟨0x800050e4#64, 0x06060263#32, 0x63#8, 0x02#8, 0x06#8, 0x06#8, .br bop.BEQ false, 12, 0, 0x64#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_800050f0 : List BBlock := [{ body := [mkLine 0x800050f0#64 0xffffe637#32], term := none }]
def ix_800050f4 : List BBlock := [{ body := [mkLine 0x800050f4#64 0xfff60613#32], term := none }]
def ix_800050f8 : List BBlock := [{ body := [mkLine 0x800050f8#64 0x000025b7#32], term := none }]
def ix_800050fc : List BBlock := [{ body := [mkLine 0x800050fc#64 0x00c7f7b3#32], term := none }]
def ix_80005100 : List BBlock := [{ body := [mkLine 0x80005100#64 0x00b76733#32], term := none }]
def ix_80005104 : List BBlock := [{ body := [mkLine 0x80005104#64 0x0af42823#32], term := none }]
def ix_80005108 : List BBlock := [{ body := [mkLine 0x80005108#64 0x00e41823#32], term := none }]
def ix_8000510c : List BBlock := [{ body := [mkLine 0x8000510c#64 0x03279713#32], term := none }]
def ixT_80005110 : List BBlock := [⟨[], some (⟨0x80005110#64, 0x04075863#32, 0x63#8, 0x58#8, 0x07#8, 0x04#8, .br bop.BGE true, 14, 0, 0x50#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_80005110 : List BBlock := [⟨[], some (⟨0x80005110#64, 0x04075863#32, 0x63#8, 0x58#8, 0x07#8, 0x04#8, .br bop.BGE false, 14, 0, 0x50#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_8000003c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 12) = (0#64) → NW live Dt DA S Q 0x80000064#64 R Mt) (hF : ¬ ((R 12) = (0#64)) → NW live Dt DA S Q 0x80000040#64 R Mt) :
    NW live Dt DA S Q 0x8000003c#64 R Mt := by
  by_cases hc : (R 12) = (0#64)
  · exact
    swp_stepD ixT_8000003c [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000003c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000003c [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000003c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_80000040 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80000044#64 (upd R 14 ((0#64) + sign_extend (m := 64) (0x101#12))) Mt) :
    NW live Dt DA S Q 0x80000040#64 R Mt :=
  swp_stepD ix_80000040 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80000040 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem it_80000044 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80000048#64 (upd R 13 ((R 11) + (R 12))) Mt) :
    NW live Dt DA S Q 0x80000044#64 R Mt :=
  swp_stepD ix_80000044 [11, 12, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80000044 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [11, 12, 13])))) rfl hk

theorem it_80000048 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000004c#64 (upd R 14 (shift_bits_left (R 14) (Sail.BitVec.extractLsb (0x30#6) 5 0))) Mt) :
    NW live Dt DA S Q 0x80000048#64 R Mt :=
  swp_stepD ix_80000048 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80000048 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem it_8000004c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1, S b)
    (hk : NW live Dt DA S Q 0x80000050#64 (upd R 15 (ldv .lbu Mt ((R 11) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000004c#64 R Mt :=
  swp_stepD ix_8000004c [11, 15] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1] (accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000004c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins1_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [11, 15])))) rfl hk

theorem itD_8000004c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1)
    (hLDD : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1, b ∈ DA)
    (hk : NW live Dt DA S Q 0x80000050#64 (upd R 15 (ldv .lbu Dt ((R 11) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000004c#64 R Mt :=
  swp_stepD ix_8000004c [11, 15] [bytesAt (imgM Dt) ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000004c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins1_img (fun b hb => dataReads_view hD b (hLDD b hb))⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [11, 15])))) rfl hk

theorem it_80000050 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80000054#64 (upd R 11 ((R 11) + sign_extend (m := 64) (0x001#12))) Mt) :
    NW live Dt DA S Q 0x80000050#64 R Mt :=
  swp_stepD ix_80000050 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80000050 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

theorem it_80000054 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80000058#64 (upd R 15 ((R 15) ||| (R 14))) Mt) :
    NW live Dt DA S Q 0x80000054#64 R Mt :=
  swp_stepD ix_80000054 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80000054 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [14, 15])))) rfl hk

theorem it_80000058 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000005c#64 (upd R 16 ((0x80000058#64) + (sign_extend (m := 64) ((0x0001b#20) +++ (0x000#12))))) Mt) :
    NW live Dt DA S Q 0x80000058#64 R Mt :=
  swp_stepD ix_80000058 [16] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80000058 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 16 ∈ [16])))) rfl hk

theorem it_80000060 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 11) ≠ (R 13) → NW live Dt DA S Q 0x8000004c#64 R Mt) (hF : ¬ ((R 11) ≠ (R 13)) → NW live Dt DA S Q 0x80000064#64 R Mt) :
    NW live Dt DA S Q 0x80000060#64 R Mt := by
  by_cases hc : (R 11) ≠ (R 13)
  · exact
    swp_stepD ixT_80000060 [11, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_80000060 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_80000060 [11, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_80000060 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_80000064 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80000068#64 (upd R 10 ((R 12) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x80000064#64 R Mt :=
  swp_stepD ix_80000064 [10, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80000064 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 12])))) rfl hk

theorem it_80000068 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : NW live Dt DA S Q (R 1) R Mt) :
    NW live Dt DA S Q 0x80000068#64 R Mt :=
  swp_stepD ix_80000068 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80000068 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80000098 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000009c#64 (upd R 10 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x80000098#64 R Mt :=
  swp_stepD ix_80000098 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80000098 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem it_8000009c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : NW live Dt DA S Q (R 1) R Mt) :
    NW live Dt DA S Q 0x8000009c#64 R Mt :=
  swp_stepD ix_8000009c [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000009c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem itS_80004640 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80004644#64 (upd R 12 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x80004640#64 R Mt :=
  swp_stepD ixS_80004640 [10, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ixS_80004640 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [10, 12])))) rfl hk

theorem itS_80004644 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80004648#64 (upd R 10 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x80004644#64 R Mt :=
  swp_stepD ixS_80004644 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ixS_80004644 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem itS_80004648 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000464c#64 (upd R 13 ((R 11) &&& sign_extend (m := 64) (0x001#12))) Mt) :
    NW live Dt DA S Q 0x80004648#64 R Mt :=
  swp_stepD ixS_80004648 [11, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ixS_80004648 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [11, 13])))) rfl hk

theorem itS_8000464c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 13) = (0#64) → NW live Dt DA S Q 0x80004654#64 R Mt) (hF : ¬ ((R 13) = (0#64)) → NW live Dt DA S Q 0x80004650#64 R Mt) :
    NW live Dt DA S Q 0x8000464c#64 R Mt := by
  by_cases hc : (R 13) = (0#64)
  · exact
    swp_stepD ixTS_8000464c [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixTS_8000464c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixFS_8000464c [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixFS_8000464c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem itS_80004650 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80004654#64 (upd R 10 ((R 10) + (R 12))) Mt) :
    NW live Dt DA S Q 0x80004650#64 R Mt :=
  swp_stepD ixS_80004650 [10, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ixS_80004650 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 12])))) rfl hk

theorem itS_80004654 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80004658#64 (upd R 11 (shift_bits_right (R 11) (Sail.BitVec.extractLsb (0x01#6) 5 0))) Mt) :
    NW live Dt DA S Q 0x80004654#64 R Mt :=
  swp_stepD ixS_80004654 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ixS_80004654 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

theorem itS_80004658 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000465c#64 (upd R 12 (shift_bits_left (R 12) (Sail.BitVec.extractLsb (0x01#6) 5 0))) Mt) :
    NW live Dt DA S Q 0x80004658#64 R Mt :=
  swp_stepD ixS_80004658 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ixS_80004658 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12])))) rfl hk

theorem itS_8000465c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 11) ≠ (0#64) → NW live Dt DA S Q 0x80004648#64 R Mt) (hF : ¬ ((R 11) ≠ (0#64)) → NW live Dt DA S Q 0x80004660#64 R Mt) :
    NW live Dt DA S Q 0x8000465c#64 R Mt := by
  by_cases hc : (R 11) ≠ (0#64)
  · exact
    swp_stepD ixTS_8000465c [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixTS_8000465c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixFS_8000465c [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixFS_8000465c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem itS_80004660 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : NW live Dt DA S Q (R 1) R Mt) :
    NW live Dt DA S Q 0x80004660#64 R Mt :=
  swp_stepD ixS_80004660 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ixS_80004660 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_80004778 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80004778 [0xef#8, 0x20#8, 0x10#8, 0x13#8], live p.1) :
    JalExec (vsaModel live) 0x80004778 [0xef#8, 0x20#8, 0x10#8, 0x13#8] 0x800070a8#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x80004778, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x80004779, .discard, 0x20#8) (by simp [codeFoot])
  have hb2 := hb (0x8000477a, .discard, 0x10#8) (by simp [codeFoot])
  have hb3 := hb (0x8000477b, .discard, 0x13#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x80004778#64) vm (0x131020ef#32) (0x002930#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80004778#64) 4)
      (0xef#8) (0x20#8) (0x10#8) (0x13#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_131020ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80004778#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x800070a8#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x80004778#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x80004778 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_80004778 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x800070a8#64 (upd R 1 (BitVec.ofNat 64 (0x80004778 + 4))) Mt) :
    NW live Dt DA S Q 0x80004778#64 R Mt :=
  swp_jal 0x80004778 [0xef#8, 0x20#8, 0x10#8, 0x13#8] 0x800070a8#64 (jalx_80004778 live (fun p hp => hlive _ (stdio_code_80004778 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_80004778 p hp)) (by decide) (by decide) rfl hk

theorem it_8000477c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((0x8001b510#64) + sign_extend (m := 64) (0x4a0#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((0x8001b510#64) + sign_extend (m := 64) (0x4a0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x80004780#64 (upd R 15 (ldv .ld Mt ((0x8001b510#64) + sign_extend (m := 64) (0x4a0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000477c#64 R Mt :=
  swp_stepD ix_8000477c [3, 15] [bytesAt (imgM Mt) ((0x8001b510#64) + sign_extend (m := 64) (0x4a0#12)).toNat 8] (accAddrs ((0x8001b510#64) + sign_extend (m := 64) (0x4a0#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000477c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun _ => rfl) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [3, 15])))) rfl hk

theorem it_80004780 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) = (0#64) → NW live Dt DA S Q 0x80004788#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → NW live Dt DA S Q 0x80004784#64 R Mt) :
    NW live Dt DA S Q 0x80004780#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    swp_stepD ixT_80004780 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_80004780 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_80004780 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_80004780 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem it_80004784 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (Sail.BitVec.update (R 15 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hk : NW live Dt DA S Q (Sail.BitVec.update (R 15 + sign_extend (m := 64) (0x000#12)) 0 0#1) (upd R 1 (BitVec.ofNat 64 (0x80004784 + 4))) Mt) :
    NW live Dt DA S Q 0x80004784#64 R Mt :=
  swp_jalr 0x80004784 [0xe7#8, 0x80#8, 0x07#8, 0x00#8] [15] (Sail.BitVec.update (R 15 + sign_extend (m := 64) (0x000#12)) 0 0#1)
    (jalrStep_of_obs
      (fun q hq => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
        exact (show ∀ k ∈ [15], 1 ≤ k ∧ k ≤ 31 by decide) k hk)
      (fun p hp => hlive _ (stdio_code_80004784 p hp))
      (fun c hG hi hpc hRR hMR => by
      obtain ⟨vm, hmi⟩ := hG.minstret
      have hb0 := hMR (0x80004784, .discard, 0xe7#8) (by simp [codeFoot])
      have hb1 := hMR (0x80004785, .discard, 0x80#8) (by simp [codeFoot])
      have hb2 := hMR (0x80004786, .discard, 0x07#8) (by simp [codeFoot])
      have hb3 := hMR (0x80004787, .discard, 0x00#8) (by simp [codeFoot])
      obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
        stepObs_jalr c.σ c.tick c.steps (0x80004784#64) vm (R 15) (0x000780e7#32) (0x000#12)
          (regidx.Regidx 0x0f#5) (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80004784#64) 4)
          (0xe7#8) (0x80#8) (0x07#8) (0x00#8)
          hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
          (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
          (Vsa.Sim.DecodeTable.decode_000780e7 (afterPrelude c.σ)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
          (rX_bits_x15 _ (R 15) (by rw [get?_afterNextPC c.σ (0x80004784#64) _ (by decide) (by decide)]; exact hRR (15, Iris.DFrac.own 1, R 15) (by simp)))
          hal (by decide) (by decide) (by decide) (by decide) (by decide)
          (wX_bits_x1 _ (BitVec.addInt (0x80004784#64) 4)) hi
      refine ⟨σ', i', vm, hs, hi', hG', hmem, ?_⟩
      rwa [show BitVec.addInt (0x80004784#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x80004784 + 4) from by
        apply BitVec.eq_of_toNat_eq; decide] at hobs))
    (fun p hp => List.mem_append_left _ (stdio_code_80004784 p hp))
    (by decide) (by decide) (by decide) rfl hk

theorem it_80005078 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000507c#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0xf90#12))) Mt) :
    NW live Dt DA S Q 0x80005078#64 R Mt :=
  swp_stepD ix_80005078 [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80005078 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem it_8000507c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x80005080#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x058#12)).toNat, 8, (R 9))])) :
    NW live Dt DA S Q 0x8000507c#64 R Mt :=
  swp_stepD ix_8000507c [2, 9] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000507c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80005080 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x80005084#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 11))])) :
    NW live Dt DA S Q 0x80005080#64 R Mt :=
  swp_stepD ix_80005080 [2, 11] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80005080 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80005084 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80005088#64 (upd R 9 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x80005084#64 R Mt :=
  swp_stepD ix_80005084 [9, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80005084 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9, 10])))) rfl hk

theorem it_80005088 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000508c#64 (upd R 11 ((R 12) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x80005088#64 R Mt :=
  swp_stepD ix_80005088 [11, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80005088 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11, 12])))) rfl hk

theorem it_8000508c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80005090#64 (upd R 10 ((R 13) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000508c#64 R Mt :=
  swp_stepD ix_8000508c [10, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000508c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 13])))) rfl hk

theorem it_80005090 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x060#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x060#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x80005094#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x060#12)).toNat, 8, (R 8))])) :
    NW live Dt DA S Q 0x80005090#64 R Mt :=
  swp_stepD ix_80005090 [2, 8] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x060#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80005090 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80005094 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x80005098#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x050#12)).toNat, 8, (R 18))])) :
    NW live Dt DA S Q 0x80005094#64 R Mt :=
  swp_stepD ix_80005094 [2, 18] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80005094 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80005098 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x048#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x048#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000509c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x048#12)).toNat, 8, (R 19))])) :
    NW live Dt DA S Q 0x80005098#64 R Mt :=
  swp_stepD ix_80005098 [2, 19] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x048#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80005098 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000509c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x800050a0#64 (upd R 8 ((R 14) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000509c#64 R Mt :=
  swp_stepD ix_8000509c [8, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000509c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8, 14])))) rfl hk

theorem it_800050a0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x800050a4#64 (upd R 19 ((R 13) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x800050a0#64 R Mt :=
  swp_stepD ix_800050a0 [13, 19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800050a0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [13, 19])))) rfl hk

theorem it_800050a4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x800050a8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x068#12)).toNat, 8, (R 1))])) :
    NW live Dt DA S Q 0x800050a4#64 R Mt :=
  swp_stepD ix_800050a4 [1, 2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_800050a4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_800050a8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x800050ac#64 (upd R 18 ((R 12) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x800050a8#64 R Mt :=
  swp_stepD ix_800050a8 [12, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800050a8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [12, 18])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_800050ac (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x800050ac [0xef#8, 0xf0#8, 0x4f#8, 0xd9#8], live p.1) :
    JalExec (vsaModel live) 0x800050ac [0xef#8, 0xf0#8, 0x4f#8, 0xd9#8] 0x80004640#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x800050ac, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x800050ad, .discard, 0xf0#8) (by simp [codeFoot])
  have hb2 := hb (0x800050ae, .discard, 0x4f#8) (by simp [codeFoot])
  have hb3 := hb (0x800050af, .discard, 0xd9#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x800050ac#64) vm (0xd94ff0ef#32) (0x1ff594#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800050ac#64) 4)
      (0xef#8) (0xf0#8) (0x4f#8) (0xd9#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_d94ff0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x800050ac#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80004640#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x800050ac#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x800050ac + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_800050ac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80004640#64 (upd R 1 (BitVec.ofNat 64 (0x800050ac + 4))) Mt) :
    NW live Dt DA S Q 0x800050ac#64 R Mt :=
  swp_jal 0x800050ac [0xef#8, 0xf0#8, 0x4f#8, 0xd9#8] 0x80004640#64 (jalx_800050ac live (fun p hp => hlive _ (stdio_code_800050ac p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_800050ac p hp)) (by decide) (by decide) rfl hk

theorem it_800050b0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x800050b4#64 (upd R 14 ((R 2) + sign_extend (m := 64) (0x018#12))) Mt) :
    NW live Dt DA S Q 0x800050b0#64 R Mt :=
  swp_stepD ix_800050b0 [2, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800050b0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [2, 14])))) rfl hk

theorem it_800050b4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x800050b8#64 (upd R 15 ((0#64) + sign_extend (m := 64) (0x001#12))) Mt) :
    NW live Dt DA S Q 0x800050b4#64 R Mt :=
  swp_stepD ix_800050b4 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800050b4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_800050b8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x800050bc#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (R 10))])) :
    NW live Dt DA S Q 0x800050b8#64 R Mt :=
  swp_stepD ix_800050b8 [2, 10] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_800050b8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_800050bc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x800050c0#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x038#12)).toNat, 8, (R 10))])) :
    NW live Dt DA S Q 0x800050bc#64 R Mt :=
  swp_stepD ix_800050bc [2, 10] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_800050bc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_800050c0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x800050c4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x028#12)).toNat, 8, (R 14))])) :
    NW live Dt DA S Q 0x800050c0#64 R Mt :=
  swp_stepD ix_800050c0 [2, 14] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_800050c0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_800050c4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x800050c8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x030#12)).toNat, 4, (R 15))])) :
    NW live Dt DA S Q 0x800050c4#64 R Mt :=
  swp_stepD ix_800050c4 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_800050c4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_800050c8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x800050cc#64 (upd R 13 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x800050c8#64 R Mt :=
  swp_stepD ix_800050c8 [10, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800050c8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [10, 13])))) rfl hk

theorem it_800050cc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 9) = (0#64) → NW live Dt DA S Q 0x800050d8#64 R Mt) (hF : ¬ ((R 9) = (0#64)) → NW live Dt DA S Q 0x800050d0#64 R Mt) :
    NW live Dt DA S Q 0x800050cc#64 R Mt := by
  by_cases hc : (R 9) = (0#64)
  · exact
    swp_stepD ixT_800050cc [9] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_800050cc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_800050cc [9] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_800050cc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_800050d0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 9) + sign_extend (m := 64) (0x048#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 9) + sign_extend (m := 64) (0x048#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x800050d4#64 (upd R 15 (ldv .ld Mt ((R 9) + sign_extend (m := 64) (0x048#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x800050d0#64 R Mt :=
  swp_stepD ix_800050d0 [9, 15] [bytesAt (imgM Mt) ((R 9) + sign_extend (m := 64) (0x048#12)).toNat 8] (accAddrs ((R 9) + sign_extend (m := 64) (0x048#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800050d0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [9, 15])))) rfl hk

theorem it_800050d4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) = (0#64) → NW live Dt DA S Q 0x8000523c#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → NW live Dt DA S Q 0x800050d8#64 R Mt) :
    NW live Dt DA S Q 0x800050d4#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    swp_stepD ixT_800050d4 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_800050d4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_800050d4 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_800050d4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_800050d8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x800050dc#64 (upd R 15 (ldv .lw Mt ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x800050d8#64 R Mt :=
  swp_stepD ix_800050d8 [8, 15] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4] (accAddrs ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800050d8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [8, 15])))) rfl hk

theorem it_800050dc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x800050e0#64 (upd R 14 (ldv .lh Mt ((R 8) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x800050dc#64 R Mt :=
  swp_stepD ix_800050dc [8, 14] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2] (accAddrs ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800050dc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [8, 14])))) rfl hk

theorem it_800050e0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x800050e4#64 (upd R 12 ((R 15) &&& sign_extend (m := 64) (0x001#12))) Mt) :
    NW live Dt DA S Q 0x800050e0#64 R Mt :=
  swp_stepD ix_800050e0 [12, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800050e0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 15])))) rfl hk

theorem it_800050e4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 12) = (0#64) → NW live Dt DA S Q 0x80005148#64 R Mt) (hF : ¬ ((R 12) = (0#64)) → NW live Dt DA S Q 0x800050e8#64 R Mt) :
    NW live Dt DA S Q 0x800050e4#64 R Mt := by
  by_cases hc : (R 12) = (0#64)
  · exact
    swp_stepD ixT_800050e4 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_800050e4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_800050e4 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_800050e4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_800050f0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x800050f4#64 (upd R 12 ((sign_extend (m := 64) ((0xffffe#20) +++ (0x000#12))))) Mt) :
    NW live Dt DA S Q 0x800050f0#64 R Mt :=
  swp_stepD ix_800050f0 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800050f0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12])))) rfl hk

theorem it_800050f4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x800050f8#64 (upd R 12 ((R 12) + sign_extend (m := 64) (0xfff#12))) Mt) :
    NW live Dt DA S Q 0x800050f4#64 R Mt :=
  swp_stepD ix_800050f4 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800050f4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12])))) rfl hk

theorem it_800050f8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x800050fc#64 (upd R 11 ((sign_extend (m := 64) ((0x00002#20) +++ (0x000#12))))) Mt) :
    NW live Dt DA S Q 0x800050f8#64 R Mt :=
  swp_stepD ix_800050f8 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800050f8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

theorem it_800050fc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80005100#64 (upd R 15 ((R 15) &&& (R 12))) Mt) :
    NW live Dt DA S Q 0x800050fc#64 R Mt :=
  swp_stepD ix_800050fc [12, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800050fc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [12, 15])))) rfl hk

theorem it_80005100 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80005104#64 (upd R 14 ((R 14) ||| (R 11))) Mt) :
    NW live Dt DA S Q 0x80005100#64 R Mt :=
  swp_stepD ix_80005100 [11, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80005100 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [11, 14])))) rfl hk

theorem it_80005104 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x80005108#64 R (writeLog Mt [(((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat, 4, (R 15))])) :
    NW live Dt DA S Q 0x80005104#64 R Mt :=
  swp_stepD ix_80005104 [8, 15] [] [] (accAddrs ((R 8) + sign_extend (m := 64) (0x0b0#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80005104 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80005108 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000510c#64 R (writeLog Mt [(((R 8) + sign_extend (m := 64) (0x010#12)).toNat, 2, (R 14))])) :
    NW live Dt DA S Q 0x80005108#64 R Mt :=
  swp_stepD ix_80005108 [8, 14] [] [] (accAddrs ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 2) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80005108 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000510c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80005110#64 (upd R 14 (shift_bits_left (R 15) (Sail.BitVec.extractLsb (0x32#6) 5 0))) Mt) :
    NW live Dt DA S Q 0x8000510c#64 R Mt :=
  swp_stepD ix_8000510c [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000510c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 15])))) rfl hk

theorem it_80005110 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (0#64).toInt ≤ (R 14).toInt → NW live Dt DA S Q 0x80005160#64 R Mt) (hF : ¬ ((0#64).toInt ≤ (R 14).toInt) → NW live Dt DA S Q 0x80005114#64 R Mt) :
    NW live Dt DA S Q 0x80005110#64 R Mt := by
  by_cases hc : (0#64).toInt ≤ (R 14).toInt
  · exact
    swp_stepD ixT_80005110 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_80005110 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_80005110 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_80005110 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

end VsaIris.Sym
