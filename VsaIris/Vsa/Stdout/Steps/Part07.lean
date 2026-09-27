import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000ab8c : List BBlock := [{ body := [mkLine 0x8000ab8c#64 0x00070793#32], term := none }]
def ix_8000ab90 : List BBlock := [{ body := [mkLine 0x8000ab90#64 0x01013703#32], term := none }]
def ix_8000ab94 : List BBlock := [{ body := [mkLine 0x8000ab94#64 0x00e787bb#32], term := none }]
def ix_8000ab98 : List BBlock := [{ body := [mkLine 0x8000ab98#64 0x00f13823#32], term := none }]
def ixT_8000ab9c : List BBlock := [⟨[], some (⟨0x8000ab9c#64, 0x520614e3#32, 0xe3#8, 0x14#8, 0x06#8, 0x52#8, .br bop.BNE true, 12, 0, 0xd28#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ab9c : List BBlock := [⟨[], some (⟨0x8000ab9c#64, 0x520614e3#32, 0xe3#8, 0x14#8, 0x06#8, 0x52#8, .br bop.BNE false, 12, 0, 0xd28#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000aba0 : List BBlock := [{ body := [mkLine 0x8000aba0#64 0x02013783#32], term := none }]
def ix_8000aba4 : List BBlock := [{ body := [mkLine 0x8000aba4#64 0x0e012423#32], term := none }]
def ixT_8000aba8 : List BBlock := [⟨[], some (⟨0x8000aba8#64, 0x00078863#32, 0x63#8, 0x88#8, 0x07#8, 0x00#8, .br bop.BEQ true, 15, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000aba8 : List BBlock := [⟨[], some (⟨0x8000aba8#64, 0x00078863#32, 0x63#8, 0x88#8, 0x07#8, 0x00#8, .br bop.BEQ false, 15, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000abb8 : List BBlock := [{ body := [mkLine 0x8000abb8#64 0x000a8b93#32], term := none }]
def ix_8000abbc : List BBlock := [⟨[], some (⟨0x8000abbc#64, 0xdf5ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xdf#8, .j, 0, 0, 0x0#13, 0x1ffdf4#21, 0#12⟩ : TInstr)⟩]
def ix_8000abcc : List BBlock := [{ body := [mkLine 0x8000abcc#64 0x000a0593#32], term := none }]
def ix_8000abd0 : List BBlock := [{ body := [mkLine 0x8000abd0#64 0x00040513#32], term := none }]
def ixT_8000abd8 : List BBlock := [⟨[], some (⟨0x8000abd8#64, 0x00050463#32, 0x63#8, 0x04#8, 0x05#8, 0x00#8, .br bop.BEQ true, 10, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000abd8 : List BBlock := [⟨[], some (⟨0x8000abd8#64, 0x00050463#32, 0x63#8, 0x04#8, 0x05#8, 0x00#8, .br bop.BEQ false, 10, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000abe0 : List BBlock := [{ body := [mkLine 0x8000abe0#64 0x010a1783#32], term := none }]
def ix_8000abe4 : List BBlock := [{ body := [mkLine 0x8000abe4#64 0x00a00693#32], term := none }]
def ix_8000abe8 : List BBlock := [{ body := [mkLine 0x8000abe8#64 0x01a7f713#32], term := none }]
def ixT_8000abec : List BBlock := [⟨[], some (⟨0x8000abec#64, 0xd4d71ce3#32, 0xe3#8, 0x1c#8, 0xd7#8, 0xd4#8, .br bop.BNE true, 14, 13, 0x1d58#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000abec : List BBlock := [⟨[], some (⟨0x8000abec#64, 0xd4d71ce3#32, 0xe3#8, 0x1c#8, 0xd7#8, 0xd4#8, .br bop.BNE false, 14, 13, 0x1d58#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000abf0 : List BBlock := [{ body := [mkLine 0x8000abf0#64 0x012a1703#32], term := none }]
def ixT_8000abf4 : List BBlock := [⟨[], some (⟨0x8000abf4#64, 0xd40748e3#32, 0xe3#8, 0x48#8, 0x07#8, 0xd4#8, .br bop.BLT true, 14, 0, 0x1d50#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000abf4 : List BBlock := [⟨[], some (⟨0x8000abf4#64, 0xd40748e3#32, 0xe3#8, 0x48#8, 0x07#8, 0xd4#8, .br bop.BLT false, 14, 0, 0x1d50#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000abf8 : List BBlock := [{ body := [mkLine 0x8000abf8#64 0x0b0a2703#32], term := none }]
def ix_8000abfc : List BBlock := [{ body := [mkLine 0x8000abfc#64 0x00177713#32], term := none }]
def ixT_8000ac00 : List BBlock := [⟨[], some (⟨0x8000ac00#64, 0x00071863#32, 0x63#8, 0x18#8, 0x07#8, 0x00#8, .br bop.BNE true, 14, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ac00 : List BBlock := [⟨[], some (⟨0x8000ac00#64, 0x00071863#32, 0x63#8, 0x18#8, 0x07#8, 0x00#8, .br bop.BNE false, 14, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ac04 : List BBlock := [{ body := [mkLine 0x8000ac04#64 0x2007f793#32], term := none }]
def ixT_8000ac08 : List BBlock := [⟨[], some (⟨0x8000ac08#64, 0x00079463#32, 0x63#8, 0x94#8, 0x07#8, 0x00#8, .br bop.BNE true, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ac08 : List BBlock := [⟨[], some (⟨0x8000ac08#64, 0x00079463#32, 0x63#8, 0x94#8, 0x07#8, 0x00#8, .br bop.BNE false, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ac0c : List BBlock := [⟨[], some (⟨0x8000ac0c#64, 0x3e00206f#32, 0x6f#8, 0x20#8, 0x00#8, 0x3e#8, .j, 0, 0, 0x0#13, 0x23e0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ac10 : List BBlock := [{ body := [mkLine 0x8000ac10#64 0x01813683#32], term := none }]
def ix_8000ac14 : List BBlock := [{ body := [mkLine 0x8000ac14#64 0x000b0613#32], term := none }]
def ix_8000ac18 : List BBlock := [{ body := [mkLine 0x8000ac18#64 0x000a0593#32], term := none }]
def ix_8000ac1c : List BBlock := [{ body := [mkLine 0x8000ac1c#64 0x00040513#32], term := none }]
def ix_8000ac24 : List BBlock := [{ body := [mkLine 0x8000ac24#64 0x24813083#32], term := none }]
def ix_8000ac28 : List BBlock := [{ body := [mkLine 0x8000ac28#64 0x24013403#32], term := none }]
def ix_8000ac2c : List BBlock := [{ body := [mkLine 0x8000ac2c#64 0x00a13823#32], term := none }]
def ix_8000ac30 : List BBlock := [{ body := [mkLine 0x8000ac30#64 0x01013503#32], term := none }]
def ix_8000ac34 : List BBlock := [{ body := [mkLine 0x8000ac34#64 0x22013a03#32], term := none }]
def ix_8000ac38 : List BBlock := [{ body := [mkLine 0x8000ac38#64 0x21013b03#32], term := none }]
def ix_8000ac3c : List BBlock := [{ body := [mkLine 0x8000ac3c#64 0x25010113#32], term := none }]
def ix_8000ac40 : List BBlock := [⟨[], some (⟨0x8000ac40#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ac60 : List BBlock := [{ body := [mkLine 0x8000ac60#64 0x418c8d3b#32], term := none }]
def ix_8000ac64 : List BBlock := [{ body := [mkLine 0x8000ac64#64 0x00050b13#32], term := none }]
def ixT_8000ac68 : List BBlock := [⟨[], some (⟨0x8000ac68#64, 0x040d0063#32, 0x63#8, 0x00#8, 0x0d#8, 0x04#8, .br bop.BEQ true, 26, 0, 0x40#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ac68 : List BBlock := [⟨[], some (⟨0x8000ac68#64, 0x040d0063#32, 0x63#8, 0x00#8, 0x0d#8, 0x04#8, .br bop.BEQ false, 26, 0, 0x40#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ac6c : List BBlock := [{ body := [mkLine 0x8000ac6c#64 0x0f013703#32], term := none }]
def ix_8000ac70 : List BBlock := [{ body := [mkLine 0x8000ac70#64 0x0e812783#32], term := none }]
def ix_8000ac74 : List BBlock := [{ body := [mkLine 0x8000ac74#64 0x018bb023#32], term := none }]
def ix_8000ac78 : List BBlock := [{ body := [mkLine 0x8000ac78#64 0x01a70733#32], term := none }]
def ix_8000ac7c : List BBlock := [{ body := [mkLine 0x8000ac7c#64 0x0017879b#32], term := none }]
def ix_8000ac80 : List BBlock := [{ body := [mkLine 0x8000ac80#64 0x01abb423#32], term := none }]
def ix_8000ac84 : List BBlock := [{ body := [mkLine 0x8000ac84#64 0x0ee13823#32], term := none }]
def ix_8000ac88 : List BBlock := [{ body := [mkLine 0x8000ac88#64 0x0ef12423#32], term := none }]
def ix_8000ac8c : List BBlock := [{ body := [mkLine 0x8000ac8c#64 0x00700713#32], term := none }]
def ix_8000ac90 : List BBlock := [{ body := [mkLine 0x8000ac90#64 0x010b8b93#32], term := none }]
def ixT_8000ac94 : List BBlock := [⟨[], some (⟨0x8000ac94#64, 0x02f74a63#32, 0x63#8, 0x4a#8, 0xf7#8, 0x02#8, .br bop.BLT true, 14, 15, 0x34#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ac94 : List BBlock := [⟨[], some (⟨0x8000ac94#64, 0x02f74a63#32, 0x63#8, 0x4a#8, 0xf7#8, 0x02#8, .br bop.BLT false, 14, 15, 0x34#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ac98 : List BBlock := [{ body := [mkLine 0x8000ac98#64 0x01013783#32], term := none }]
def ix_8000ac9c : List BBlock := [{ body := [mkLine 0x8000ac9c#64 0x01a787bb#32], term := none }]
def ix_8000aca0 : List BBlock := [{ body := [mkLine 0x8000aca0#64 0x00f13823#32], term := none }]
def ixT_8000aca4 : List BBlock := [⟨[], some (⟨0x8000aca4#64, 0xd40b1ce3#32, 0xe3#8, 0x1c#8, 0x0b#8, 0xd4#8, .br bop.BNE true, 22, 0, 0x1d58#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000aca4 : List BBlock := [⟨[], some (⟨0x8000aca4#64, 0xd40b1ce3#32, 0xe3#8, 0x1c#8, 0x0b#8, 0xd4#8, .br bop.BNE false, 22, 0, 0x1d58#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000aca8 : List BBlock := [{ body := [mkLine 0x8000aca8#64 0x0f013783#32], term := none }]
def ix_8000acac : List BBlock := [{ body := [mkLine 0x8000acac#64 0x00013403#32], term := none }]
def ix_8000acb0 : List BBlock := [{ body := [mkLine 0x8000acb0#64 0x00813a03#32], term := none }]
def ixT_8000acb4 : List BBlock := [⟨[], some (⟨0x8000acb4#64, 0x00078463#32, 0x63#8, 0x84#8, 0x07#8, 0x00#8, .br bop.BEQ true, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000acb4 : List BBlock := [⟨[], some (⟨0x8000acb4#64, 0x00078463#32, 0x63#8, 0x84#8, 0x07#8, 0x00#8, .br bop.BEQ false, 15, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000acb8 : List BBlock := [⟨[], some (⟨0x8000acb8#64, 0x2e40206f#32, 0x6f#8, 0x20#8, 0x40#8, 0x2e#8, .j, 0, 0, 0x0#13, 0x22e4#21, 0#12⟩ : TInstr)⟩]
def ix_8000acbc : List BBlock := [{ body := [mkLine 0x8000acbc#64 0x010a1783#32], term := none }]
def ix_8000acc0 : List BBlock := [{ body := [mkLine 0x8000acc0#64 0x0e012423#32], term := none }]
def ix_8000acc4 : List BBlock := [⟨[], some (⟨0x8000acc4#64, 0x4350006f#32, 0x6f#8, 0x00#8, 0x50#8, 0x43#8, .j, 0, 0, 0x0#13, 0xc34#21, 0#12⟩ : TInstr)⟩]
def ix_8000ace8 : List BBlock := [{ body := [mkLine 0x8000ace8#64 0x2007f693#32], term := none }]
def ixT_8000acec : List BBlock := [⟨[], some (⟨0x8000acec#64, 0x24068c63#32, 0x63#8, 0x8c#8, 0x06#8, 0x24#8, .br bop.BEQ true, 13, 0, 0x258#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000acec : List BBlock := [⟨[], some (⟨0x8000acec#64, 0x24068c63#32, 0x63#8, 0x8c#8, 0x06#8, 0x24#8, .br bop.BEQ false, 13, 0, 0x258#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_8000ab8c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ab90#64 (upd R 15 ((R 14) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ab8c#64 R Mt :=
  swp_stepD ix_8000ab8c [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ab8c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [14, 15])))) rfl hk

theorem it_8000ab90 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ab94#64 (upd R 14 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ab90#64 R Mt :=
  swp_stepD ix_8000ab90 [2, 14] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ab90 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [2, 14])))) rfl hk

theorem it_8000ab94 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ab98#64 (upd R 15 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 15) 31 0) + (Sail.BitVec.extractLsb (R 14) 31 0)))) Mt) :
    NW live Dt DA S Q 0x8000ab94#64 R Mt :=
  swp_stepD ix_8000ab94 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ab94 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [14, 15])))) rfl hk

theorem it_8000ab98 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ab9c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 15))])) :
    NW live Dt DA S Q 0x8000ab98#64 R Mt :=
  swp_stepD ix_8000ab98 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ab98 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ab9c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 12) ≠ (0#64) → NW live Dt DA S Q 0x8000b8c4#64 R Mt) (hF : ¬ ((R 12) ≠ (0#64)) → NW live Dt DA S Q 0x8000aba0#64 R Mt) :
    NW live Dt DA S Q 0x8000ab9c#64 R Mt := by
  by_cases hc : (R 12) ≠ (0#64)
  · exact
    swp_stepD ixT_8000ab9c [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ab9c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ab9c [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ab9c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000aba0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000aba4#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000aba0#64 R Mt :=
  swp_stepD ix_8000aba0 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000aba0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem it_8000aba4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000aba8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat, 4, (0#64))])) :
    NW live Dt DA S Q 0x8000aba4#64 R Mt :=
  swp_stepD ix_8000aba4 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000aba4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000aba8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) = (0#64) → NW live Dt DA S Q 0x8000abb8#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → NW live Dt DA S Q 0x8000abac#64 R Mt) :
    NW live Dt DA S Q 0x8000aba8#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    swp_stepD ixT_8000aba8 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000aba8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000aba8 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000aba8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000abb8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000abbc#64 (upd R 23 ((R 21) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000abb8#64 R Mt :=
  swp_stepD ix_8000abb8 [21, 23] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000abb8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [21, 23])))) rfl hk

theorem it_8000abbc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a9b0#64 R Mt) :
    NW live Dt DA S Q 0x8000abbc#64 R Mt :=
  swp_stepD ix_8000abbc [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000abbc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000abcc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000abd0#64 (upd R 11 ((R 20) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000abcc#64 R Mt :=
  swp_stepD ix_8000abcc [11, 20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000abcc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11, 20])))) rfl hk

theorem it_8000abd0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000abd4#64 (upd R 10 ((R 8) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000abd0#64 R Mt :=
  swp_stepD ix_8000abd0 [8, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000abd0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [8, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000abd4 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000abd4 [0xef#8, 0x40#8, 0xc0#8, 0x65#8], live p.1) :
    JalExec (vsaModel live) 0x8000abd4 [0xef#8, 0x40#8, 0xc0#8, 0x65#8] 0x8000f230#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000abd4, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000abd5, .discard, 0x40#8) (by simp [codeFoot])
  have hb2 := hb (0x8000abd6, .discard, 0xc0#8) (by simp [codeFoot])
  have hb3 := hb (0x8000abd7, .discard, 0x65#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000abd4#64) vm (0x65c040ef#32) (0x00465c#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000abd4#64) 4)
      (0xef#8) (0x40#8) (0xc0#8) (0x65#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_65c040ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000abd4#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x8000f230#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000abd4#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000abd4 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000abd4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000f230#64 (upd R 1 (BitVec.ofNat 64 (0x8000abd4 + 4))) Mt) :
    NW live Dt DA S Q 0x8000abd4#64 R Mt :=
  swp_jal 0x8000abd4 [0xef#8, 0x40#8, 0xc0#8, 0x65#8] 0x8000f230#64 (jalx_8000abd4 live (fun p hp => hlive _ (stdio_code_8000abd4 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000abd4 p hp)) (by decide) (by decide) rfl hk

theorem it_8000abd8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 10) = (0#64) → NW live Dt DA S Q 0x8000abe0#64 R Mt) (hF : ¬ ((R 10) = (0#64)) → NW live Dt DA S Q 0x8000abdc#64 R Mt) :
    NW live Dt DA S Q 0x8000abd8#64 R Mt := by
  by_cases hc : (R 10) = (0#64)
  · exact
    swp_stepD ixT_8000abd8 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000abd8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000abd8 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000abd8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000abe0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000abe4#64 (upd R 15 (ldv .lh Mt ((R 20) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000abe0#64 R Mt :=
  swp_stepD ix_8000abe0 [15, 20] [bytesAt (imgM Mt) ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2] (accAddrs ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000abe0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15, 20])))) rfl hk

theorem it_8000abe4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000abe8#64 (upd R 13 ((0#64) + sign_extend (m := 64) (0x00a#12))) Mt) :
    NW live Dt DA S Q 0x8000abe4#64 R Mt :=
  swp_stepD ix_8000abe4 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000abe4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13])))) rfl hk

theorem it_8000abe8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000abec#64 (upd R 14 ((R 15) &&& sign_extend (m := 64) (0x01a#12))) Mt) :
    NW live Dt DA S Q 0x8000abe8#64 R Mt :=
  swp_stepD ix_8000abe8 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000abe8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 15])))) rfl hk

theorem it_8000abec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 14) ≠ (R 13) → NW live Dt DA S Q 0x8000a944#64 R Mt) (hF : ¬ ((R 14) ≠ (R 13)) → NW live Dt DA S Q 0x8000abf0#64 R Mt) :
    NW live Dt DA S Q 0x8000abec#64 R Mt := by
  by_cases hc : (R 14) ≠ (R 13)
  · exact
    swp_stepD ixT_8000abec [13, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000abec ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000abec [13, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000abec ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000abf0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 20) + sign_extend (m := 64) (0x012#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 20) + sign_extend (m := 64) (0x012#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000abf4#64 (upd R 14 (ldv .lh Mt ((R 20) + sign_extend (m := 64) (0x012#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000abf0#64 R Mt :=
  swp_stepD ix_8000abf0 [14, 20] [bytesAt (imgM Mt) ((R 20) + sign_extend (m := 64) (0x012#12)).toNat 2] (accAddrs ((R 20) + sign_extend (m := 64) (0x012#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000abf0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 20])))) rfl hk

theorem it_8000abf4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 14).toInt < (0#64).toInt → NW live Dt DA S Q 0x8000a944#64 R Mt) (hF : ¬ ((R 14).toInt < (0#64).toInt) → NW live Dt DA S Q 0x8000abf8#64 R Mt) :
    NW live Dt DA S Q 0x8000abf4#64 R Mt := by
  by_cases hc : (R 14).toInt < (0#64).toInt
  · exact
    swp_stepD ixT_8000abf4 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000abf4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000abf4 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000abf4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000abf8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000abfc#64 (upd R 14 (ldv .lw Mt ((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000abf8#64 R Mt :=
  swp_stepD ix_8000abf8 [14, 20] [bytesAt (imgM Mt) ((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat 4] (accAddrs ((R 20) + sign_extend (m := 64) (0x0b0#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000abf8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 20])))) rfl hk

theorem it_8000abfc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ac00#64 (upd R 14 ((R 14) &&& sign_extend (m := 64) (0x001#12))) Mt) :
    NW live Dt DA S Q 0x8000abfc#64 R Mt :=
  swp_stepD ix_8000abfc [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000abfc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem it_8000ac00 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 14) ≠ (0#64) → NW live Dt DA S Q 0x8000ac10#64 R Mt) (hF : ¬ ((R 14) ≠ (0#64)) → NW live Dt DA S Q 0x8000ac04#64 R Mt) :
    NW live Dt DA S Q 0x8000ac00#64 R Mt := by
  by_cases hc : (R 14) ≠ (0#64)
  · exact
    swp_stepD ixT_8000ac00 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ac00 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ac00 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ac00 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ac04 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ac08#64 (upd R 15 ((R 15) &&& sign_extend (m := 64) (0x200#12))) Mt) :
    NW live Dt DA S Q 0x8000ac04#64 R Mt :=
  swp_stepD ix_8000ac04 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac04 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_8000ac08 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) ≠ (0#64) → NW live Dt DA S Q 0x8000ac10#64 R Mt) (hF : ¬ ((R 15) ≠ (0#64)) → NW live Dt DA S Q 0x8000ac0c#64 R Mt) :
    NW live Dt DA S Q 0x8000ac08#64 R Mt := by
  by_cases hc : (R 15) ≠ (0#64)
  · exact
    swp_stepD ixT_8000ac08 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ac08 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ac08 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ac08 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ac0c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000cfec#64 R Mt) :
    NW live Dt DA S Q 0x8000ac0c#64 R Mt :=
  swp_stepD ix_8000ac0c [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac0c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ac10 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ac14#64 (upd R 13 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ac10#64 R Mt :=
  swp_stepD ix_8000ac10 [2, 13] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac10 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [2, 13])))) rfl hk

theorem it_8000ac14 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ac18#64 (upd R 12 ((R 22) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ac14#64 R Mt :=
  swp_stepD ix_8000ac14 [12, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac14 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 22])))) rfl hk

theorem it_8000ac18 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ac1c#64 (upd R 11 ((R 20) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ac18#64 R Mt :=
  swp_stepD ix_8000ac18 [11, 20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac18 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11, 20])))) rfl hk

theorem it_8000ac1c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ac20#64 (upd R 10 ((R 8) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ac1c#64 R Mt :=
  swp_stepD ix_8000ac1c [8, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac1c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [8, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000ac20 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000ac20 [0xef#8, 0x30#8, 0x80#8, 0x18#8], live p.1) :
    JalExec (vsaModel live) 0x8000ac20 [0xef#8, 0x30#8, 0x80#8, 0x18#8] 0x8000dda8#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000ac20, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000ac21, .discard, 0x30#8) (by simp [codeFoot])
  have hb2 := hb (0x8000ac22, .discard, 0x80#8) (by simp [codeFoot])
  have hb3 := hb (0x8000ac23, .discard, 0x18#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000ac20#64) vm (0x188030ef#32) (0x003188#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000ac20#64) 4)
      (0xef#8) (0x30#8) (0x80#8) (0x18#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_188030ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000ac20#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x8000dda8#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000ac20#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000ac20 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000ac20 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000dda8#64 (upd R 1 (BitVec.ofNat 64 (0x8000ac20 + 4))) Mt) :
    NW live Dt DA S Q 0x8000ac20#64 R Mt :=
  swp_jal 0x8000ac20 [0xef#8, 0x30#8, 0x80#8, 0x18#8] 0x8000dda8#64 (jalx_8000ac20 live (fun p hp => hlive _ (stdio_code_8000ac20 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000ac20 p hp)) (by decide) (by decide) rfl hk

theorem it_8000ac24 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x248#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x248#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ac28#64 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x248#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ac24#64 R Mt :=
  swp_stepD ix_8000ac24 [1, 2] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x248#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x248#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac24 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 1 ∈ [1, 2])))) rfl hk

theorem it_8000ac28 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x240#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x240#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ac2c#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x240#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ac28#64 R Mt :=
  swp_stepD ix_8000ac28 [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x240#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x240#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac28 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem it_8000ac2c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ac30#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 10))])) :
    NW live Dt DA S Q 0x8000ac2c#64 R Mt :=
  swp_stepD ix_8000ac2c [2, 10] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ac2c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ac30 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ac34#64 (upd R 10 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ac30#64 R Mt :=
  swp_stepD ix_8000ac30 [2, 10] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac30 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [2, 10])))) rfl hk

theorem it_8000ac34 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x220#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x220#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ac38#64 (upd R 20 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x220#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ac34#64 R Mt :=
  swp_stepD ix_8000ac34 [2, 20] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x220#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x220#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac34 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [2, 20])))) rfl hk

theorem it_8000ac38 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x210#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x210#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ac3c#64 (upd R 22 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x210#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ac38#64 R Mt :=
  swp_stepD ix_8000ac38 [2, 22] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x210#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x210#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac38 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [2, 22])))) rfl hk

theorem it_8000ac3c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ac40#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0x250#12))) Mt) :
    NW live Dt DA S Q 0x8000ac3c#64 R Mt :=
  swp_stepD ix_8000ac3c [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac3c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem it_8000ac40 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : NW live Dt DA S Q (R 1) R Mt) :
    NW live Dt DA S Q 0x8000ac40#64 R Mt :=
  swp_stepD ix_8000ac40 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac40 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ac60 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ac64#64 (upd R 26 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 25) 31 0) - (Sail.BitVec.extractLsb (R 24) 31 0)))) Mt) :
    NW live Dt DA S Q 0x8000ac60#64 R Mt :=
  swp_stepD ix_8000ac60 [24, 25, 26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac60 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 26 ∈ [24, 25, 26])))) rfl hk

theorem it_8000ac64 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ac68#64 (upd R 22 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ac64#64 R Mt :=
  swp_stepD ix_8000ac64 [10, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac64 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [10, 22])))) rfl hk

theorem it_8000ac68 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 26) = (0#64) → NW live Dt DA S Q 0x8000aca8#64 R Mt) (hF : ¬ ((R 26) = (0#64)) → NW live Dt DA S Q 0x8000ac6c#64 R Mt) :
    NW live Dt DA S Q 0x8000ac68#64 R Mt := by
  by_cases hc : (R 26) = (0#64)
  · exact
    swp_stepD ixT_8000ac68 [26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ac68 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ac68 [26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ac68 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ac6c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ac70#64 (upd R 14 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ac6c#64 R Mt :=
  swp_stepD ix_8000ac6c [2, 14] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac6c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [2, 14])))) rfl hk

theorem it_8000ac70 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000ac74#64 (upd R 15 (ldv .lw Mt ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ac70#64 R Mt :=
  swp_stepD ix_8000ac70 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4] (accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac70 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem it_8000ac74 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ac78#64 R (writeLog Mt [(((R 23) + sign_extend (m := 64) (0x000#12)).toNat, 8, (R 24))])) :
    NW live Dt DA S Q 0x8000ac74#64 R Mt :=
  swp_stepD ix_8000ac74 [23, 24] [] [] (accAddrs ((R 23) + sign_extend (m := 64) (0x000#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ac74 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ac78 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ac7c#64 (upd R 14 ((R 14) + (R 26))) Mt) :
    NW live Dt DA S Q 0x8000ac78#64 R Mt :=
  swp_stepD ix_8000ac78 [14, 26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac78 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 26])))) rfl hk

theorem it_8000ac7c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ac80#64 (upd R 15 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 15) + sign_extend (m := 64) (0x001#12)) 31 0))) Mt) :
    NW live Dt DA S Q 0x8000ac7c#64 R Mt :=
  swp_stepD ix_8000ac7c [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac7c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_8000ac80 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 23) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 23) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ac84#64 R (writeLog Mt [(((R 23) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 26))])) :
    NW live Dt DA S Q 0x8000ac80#64 R Mt :=
  swp_stepD ix_8000ac80 [23, 26] [] [] (accAddrs ((R 23) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ac80 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ac84 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ac88#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat, 8, (R 14))])) :
    NW live Dt DA S Q 0x8000ac84#64 R Mt :=
  swp_stepD ix_8000ac84 [2, 14] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ac84 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ac88 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000ac8c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat, 4, (R 15))])) :
    NW live Dt DA S Q 0x8000ac88#64 R Mt :=
  swp_stepD ix_8000ac88 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ac88 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ac8c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ac90#64 (upd R 14 ((0#64) + sign_extend (m := 64) (0x007#12))) Mt) :
    NW live Dt DA S Q 0x8000ac8c#64 R Mt :=
  swp_stepD ix_8000ac8c [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac8c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem it_8000ac90 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ac94#64 (upd R 23 ((R 23) + sign_extend (m := 64) (0x010#12))) Mt) :
    NW live Dt DA S Q 0x8000ac90#64 R Mt :=
  swp_stepD ix_8000ac90 [23] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac90 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [23])))) rfl hk

theorem it_8000ac94 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 14).toInt < (R 15).toInt → NW live Dt DA S Q 0x8000acc8#64 R Mt) (hF : ¬ ((R 14).toInt < (R 15).toInt) → NW live Dt DA S Q 0x8000ac98#64 R Mt) :
    NW live Dt DA S Q 0x8000ac94#64 R Mt := by
  by_cases hc : (R 14).toInt < (R 15).toInt
  · exact
    swp_stepD ixT_8000ac94 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ac94 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ac94 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ac94 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ac98 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ac9c#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ac98#64 R Mt :=
  swp_stepD ix_8000ac98 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac98 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem it_8000ac9c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000aca0#64 (upd R 15 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 15) 31 0) + (Sail.BitVec.extractLsb (R 26) 31 0)))) Mt) :
    NW live Dt DA S Q 0x8000ac9c#64 R Mt :=
  swp_stepD ix_8000ac9c [15, 26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ac9c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15, 26])))) rfl hk

theorem it_8000aca0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000aca4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 15))])) :
    NW live Dt DA S Q 0x8000aca0#64 R Mt :=
  swp_stepD ix_8000aca0 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000aca0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000aca4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 22) ≠ (0#64) → NW live Dt DA S Q 0x8000a9fc#64 R Mt) (hF : ¬ ((R 22) ≠ (0#64)) → NW live Dt DA S Q 0x8000aca8#64 R Mt) :
    NW live Dt DA S Q 0x8000aca4#64 R Mt := by
  by_cases hc : (R 22) ≠ (0#64)
  · exact
    swp_stepD ixT_8000aca4 [22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000aca4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000aca4 [22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000aca4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000aca8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000acac#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000aca8#64 R Mt :=
  swp_stepD ix_8000aca8 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x0f0#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000aca8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem it_8000acac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000acb0#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000acac#64 R Mt :=
  swp_stepD ix_8000acac [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000acac ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem it_8000acb0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000acb4#64 (upd R 20 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000acb0#64 R Mt :=
  swp_stepD ix_8000acb0 [2, 20] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000acb0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [2, 20])))) rfl hk

theorem it_8000acb4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) = (0#64) → NW live Dt DA S Q 0x8000acbc#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → NW live Dt DA S Q 0x8000acb8#64 R Mt) :
    NW live Dt DA S Q 0x8000acb4#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    swp_stepD ixT_8000acb4 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000acb4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000acb4 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000acb4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000acb8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000cf9c#64 R Mt) :
    NW live Dt DA S Q 0x8000acb8#64 R Mt :=
  swp_stepD ix_8000acb8 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000acb8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000acbc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000acc0#64 (upd R 15 (ldv .lh Mt ((R 20) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000acbc#64 R Mt :=
  swp_stepD ix_8000acbc [15, 20] [bytesAt (imgM Mt) ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2] (accAddrs ((R 20) + sign_extend (m := 64) (0x010#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000acbc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15, 20])))) rfl hk

theorem it_8000acc0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000acc4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat, 4, (0#64))])) :
    NW live Dt DA S Q 0x8000acc0#64 R Mt :=
  swp_stepD ix_8000acc0 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0e8#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000acc0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000acc4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b8f8#64 R Mt) :
    NW live Dt DA S Q 0x8000acc4#64 R Mt :=
  swp_stepD ix_8000acc4 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000acc4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ace8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000acec#64 (upd R 13 ((R 15) &&& sign_extend (m := 64) (0x200#12))) Mt) :
    NW live Dt DA S Q 0x8000ace8#64 R Mt :=
  swp_stepD ix_8000ace8 [13, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ace8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13, 15])))) rfl hk

theorem it_8000acec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 13) = (0#64) → NW live Dt DA S Q 0x8000af44#64 R Mt) (hF : ¬ ((R 13) = (0#64)) → NW live Dt DA S Q 0x8000acf0#64 R Mt) :
    NW live Dt DA S Q 0x8000acec#64 R Mt := by
  by_cases hc : (R 13) = (0#64)
  · exact
    swp_stepD ixT_8000acec [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000acec ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000acec [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000acec ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

end VsaIris.Sym
