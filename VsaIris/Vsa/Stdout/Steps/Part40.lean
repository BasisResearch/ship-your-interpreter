import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000eb9c : List BBlock := [{ body := [mkLine 0x8000eb9c#64 0x0085a683#32], term := none }]
def ix_8000eba0 : List BBlock := [{ body := [mkLine 0x8000eba0#64 0x00f767b3#32], term := none }]
def ix_8000eba4 : List BBlock := [{ body := [mkLine 0x8000eba4#64 0x00f59823#32], term := none }]
def ixT_8000eba8 : List BBlock := [⟨[], some (⟨0x8000eba8#64, 0x18d05c63#32, 0x63#8, 0x5c#8, 0xd0#8, 0x18#8, .br bop.BGE true, 0, 13, 0x198#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000eba8 : List BBlock := [⟨[], some (⟨0x8000eba8#64, 0x18d05c63#32, 0x63#8, 0x5c#8, 0xd0#8, 0x18#8, .br bop.BGE false, 0, 13, 0x198#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ec9c : List BBlock := [{ body := [mkLine 0x8000ec9c#64 0x02813083#32], term := none }]
def ix_8000eca0 : List BBlock := [{ body := [mkLine 0x8000eca0#64 0x02013403#32], term := none }]
def ix_8000eca4 : List BBlock := [{ body := [mkLine 0x8000eca4#64 0x00813983#32], term := none }]
def ix_8000eca8 : List BBlock := [{ body := [mkLine 0x8000eca8#64 0x00000513#32], term := none }]
def ix_8000ecac : List BBlock := [{ body := [mkLine 0x8000ecac#64 0x03010113#32], term := none }]
def ix_8000ecb0 : List BBlock := [⟨[], some (⟨0x8000ecb0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ecb4 : List BBlock := [{ body := [mkLine 0x8000ecb4#64 0x01213823#32], term := none }]
def ix_8000ecb8 : List BBlock := [{ body := [mkLine 0x8000ecb8#64 0x0185b903#32], term := none }]
def ixT_8000ecbc : List BBlock := [⟨[], some (⟨0x8000ecbc#64, 0x08090a63#32, 0x63#8, 0x0a#8, 0x09#8, 0x08#8, .br bop.BEQ true, 18, 0, 0x94#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ecbc : List BBlock := [⟨[], some (⟨0x8000ecbc#64, 0x08090a63#32, 0x63#8, 0x0a#8, 0x09#8, 0x08#8, .br bop.BEQ false, 18, 0, 0x94#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ecc0 : List BBlock := [{ body := [mkLine 0x8000ecc0#64 0x00913c23#32], term := none }]
def ix_8000ecc4 : List BBlock := [{ body := [mkLine 0x8000ecc4#64 0x0005b483#32], term := none }]
def ix_8000ecc8 : List BBlock := [{ body := [mkLine 0x8000ecc8#64 0x00377713#32], term := none }]
def ix_8000eccc : List BBlock := [{ body := [mkLine 0x8000eccc#64 0x0125b023#32], term := none }]
def ix_8000ecd0 : List BBlock := [{ body := [mkLine 0x8000ecd0#64 0x412484bb#32], term := none }]
def ix_8000ecd4 : List BBlock := [{ body := [mkLine 0x8000ecd4#64 0x00000793#32], term := none }]
def ixT_8000ecd8 : List BBlock := [⟨[], some (⟨0x8000ecd8#64, 0x00071463#32, 0x63#8, 0x14#8, 0x07#8, 0x00#8, .br bop.BNE true, 14, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ecd8 : List BBlock := [⟨[], some (⟨0x8000ecd8#64, 0x00071463#32, 0x63#8, 0x14#8, 0x07#8, 0x00#8, .br bop.BNE false, 14, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ecdc : List BBlock := [{ body := [mkLine 0x8000ecdc#64 0x0205a783#32], term := none }]
def ix_8000ece0 : List BBlock := [{ body := [mkLine 0x8000ece0#64 0x00f42623#32], term := none }]
def ixT_8000ece4 : List BBlock := [⟨[], some (⟨0x8000ece4#64, 0x00904863#32, 0x63#8, 0x48#8, 0x90#8, 0x00#8, .br bop.BLT true, 0, 9, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ece4 : List BBlock := [⟨[], some (⟨0x8000ece4#64, 0x00904863#32, 0x63#8, 0x48#8, 0x90#8, 0x00#8, .br bop.BLT false, 0, 9, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ece8 : List BBlock := [⟨[], some (⟨0x8000ece8#64, 0x0640006f#32, 0x6f#8, 0x00#8, 0x40#8, 0x06#8, .j, 0, 0, 0x0#13, 0x64#21, 0#12⟩ : TInstr)⟩]
def ix_8000ecec : List BBlock := [{ body := [mkLine 0x8000ecec#64 0x00a90933#32], term := none }]
def ixT_8000ecf0 : List BBlock := [⟨[], some (⟨0x8000ecf0#64, 0x04905e63#32, 0x63#8, 0x5e#8, 0x90#8, 0x04#8, .br bop.BGE true, 0, 9, 0x5c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ecf0 : List BBlock := [⟨[], some (⟨0x8000ecf0#64, 0x04905e63#32, 0x63#8, 0x5e#8, 0x90#8, 0x04#8, .br bop.BGE false, 0, 9, 0x5c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ecf4 : List BBlock := [{ body := [mkLine 0x8000ecf4#64 0x04043783#32], term := none }]
def ix_8000ecf8 : List BBlock := [{ body := [mkLine 0x8000ecf8#64 0x03043583#32], term := none }]
def ix_8000ecfc : List BBlock := [{ body := [mkLine 0x8000ecfc#64 0x00048693#32], term := none }]
def ix_8000ed00 : List BBlock := [{ body := [mkLine 0x8000ed00#64 0x00090613#32], term := none }]
def ix_8000ed04 : List BBlock := [{ body := [mkLine 0x8000ed04#64 0x00098513#32], term := none }]
def ix_8000ed0c : List BBlock := [{ body := [mkLine 0x8000ed0c#64 0x40a484bb#32], term := none }]
def ixT_8000ed10 : List BBlock := [⟨[], some (⟨0x8000ed10#64, 0xfca04ee3#32, 0xe3#8, 0x4e#8, 0xa0#8, 0xfc#8, .br bop.BLT true, 0, 10, 0x1fdc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ed10 : List BBlock := [⟨[], some (⟨0x8000ed10#64, 0xfca04ee3#32, 0xe3#8, 0x4e#8, 0xa0#8, 0xfc#8, .br bop.BLT false, 0, 10, 0x1fdc#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ed40 : List BBlock := [{ body := [mkLine 0x8000ed40#64 0x0705a683#32], term := none }]
def ixT_8000ed44 : List BBlock := [⟨[], some (⟨0x8000ed44#64, 0xe6d044e3#32, 0xe3#8, 0x44#8, 0xd0#8, 0xe6#8, .br bop.BLT true, 0, 13, 0x1e68#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ed44 : List BBlock := [⟨[], some (⟨0x8000ed44#64, 0xe6d044e3#32, 0xe3#8, 0x44#8, 0xd0#8, 0xe6#8, .br bop.BLT false, 0, 13, 0x1e68#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ed48 : List BBlock := [⟨[], some (⟨0x8000ed48#64, 0xf55ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf5#8, .j, 0, 0, 0x0#13, 0x1fff54#21, 0#12⟩ : TInstr)⟩]
def ix_8000ed4c : List BBlock := [{ body := [mkLine 0x8000ed4c#64 0x01813483#32], term := none }]
def ix_8000ed50 : List BBlock := [{ body := [mkLine 0x8000ed50#64 0x01013903#32], term := none }]
def ix_8000ed54 : List BBlock := [⟨[], some (⟨0x8000ed54#64, 0xf49ff06f#32, 0x6f#8, 0xf0#8, 0x9f#8, 0xf4#8, .j, 0, 0, 0x0#13, 0x1fff48#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_8000eb9c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x008#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x008#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000eba0#64 (upd R 13 (ldv .lw Mt ((R 11) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000eb9c#64 R Mt :=
  swp_stepD ix_8000eb9c [11, 13] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x008#12)).toNat 4] (accAddrs ((R 11) + sign_extend (m := 64) (0x008#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eb9c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [11, 13])))) rfl hk

theorem it_8000eba0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000eba4#64 (upd R 15 ((R 14) ||| (R 15))) Mt) :
    NW live Dt DA S Q 0x8000eba0#64 R Mt :=
  swp_stepD ix_8000eba0 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eba0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [14, 15])))) rfl hk

theorem it_8000eba4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000eba8#64 R (writeLog Mt [(((R 11) + sign_extend (m := 64) (0x010#12)).toNat, 2, (R 15))])) :
    NW live Dt DA S Q 0x8000eba4#64 R Mt :=
  swp_stepD ix_8000eba4 [11, 15] [] [] (accAddrs ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000eba4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000eba8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 13).toInt ≤ (0#64).toInt → NW live Dt DA S Q 0x8000ed40#64 R Mt) (hF : ¬ ((R 13).toInt ≤ (0#64).toInt) → NW live Dt DA S Q 0x8000ebac#64 R Mt) :
    NW live Dt DA S Q 0x8000eba8#64 R Mt := by
  by_cases hc : (R 13).toInt ≤ (0#64).toInt
  · exact
    swp_stepD ixT_8000eba8 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000eba8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000eba8 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000eba8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ec9c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000eca0#64 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x028#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ec9c#64 R Mt :=
  swp_stepD ix_8000ec9c [1, 2] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ec9c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 1 ∈ [1, 2])))) rfl hk

theorem it_8000eca0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000eca4#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000eca0#64 R Mt :=
  swp_stepD ix_8000eca0 [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eca0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem it_8000eca4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000eca8#64 (upd R 19 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000eca4#64 R Mt :=
  swp_stepD ix_8000eca4 [2, 19] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eca4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [2, 19])))) rfl hk

theorem it_8000eca8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ecac#64 (upd R 10 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000eca8#64 R Mt :=
  swp_stepD ix_8000eca8 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000eca8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem it_8000ecac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ecb0#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0x030#12))) Mt) :
    NW live Dt DA S Q 0x8000ecac#64 R Mt :=
  swp_stepD ix_8000ecac [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ecac ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem it_8000ecb0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : NW live Dt DA S Q (R 1) R Mt) :
    NW live Dt DA S Q 0x8000ecb0#64 R Mt :=
  swp_stepD ix_8000ecb0 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ecb0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ecb4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ecb8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 18))])) :
    NW live Dt DA S Q 0x8000ecb4#64 R Mt :=
  swp_stepD ix_8000ecb4 [2, 18] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ecb4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ecb8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ecbc#64 (upd R 18 (ldv .ld Mt ((R 11) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ecb8#64 R Mt :=
  swp_stepD ix_8000ecb8 [11, 18] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 11) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ecb8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [11, 18])))) rfl hk

theorem it_8000ecbc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 18) = (0#64) → NW live Dt DA S Q 0x8000ed50#64 R Mt) (hF : ¬ ((R 18) = (0#64)) → NW live Dt DA S Q 0x8000ecc0#64 R Mt) :
    NW live Dt DA S Q 0x8000ecbc#64 R Mt := by
  by_cases hc : (R 18) = (0#64)
  · exact
    swp_stepD ixT_8000ecbc [18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ecbc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ecbc [18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ecbc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ecc0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ecc4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 9))])) :
    NW live Dt DA S Q 0x8000ecc0#64 R Mt :=
  swp_stepD ix_8000ecc0 [2, 9] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ecc0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ecc4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ecc8#64 (upd R 9 (ldv .ld Mt ((R 11) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ecc4#64 R Mt :=
  swp_stepD ix_8000ecc4 [9, 11] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ecc4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9, 11])))) rfl hk

theorem it_8000ecc8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000eccc#64 (upd R 14 ((R 14) &&& sign_extend (m := 64) (0x003#12))) Mt) :
    NW live Dt DA S Q 0x8000ecc8#64 R Mt :=
  swp_stepD ix_8000ecc8 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ecc8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem it_8000eccc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ecd0#64 R (writeLog Mt [(((R 11) + sign_extend (m := 64) (0x000#12)).toNat, 8, (R 18))])) :
    NW live Dt DA S Q 0x8000eccc#64 R Mt :=
  swp_stepD ix_8000eccc [11, 18] [] [] (accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000eccc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ecd0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ecd4#64 (upd R 9 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 9) 31 0) - (Sail.BitVec.extractLsb (R 18) 31 0)))) Mt) :
    NW live Dt DA S Q 0x8000ecd0#64 R Mt :=
  swp_stepD ix_8000ecd0 [9, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ecd0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9, 18])))) rfl hk

theorem it_8000ecd4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ecd8#64 (upd R 15 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ecd4#64 R Mt :=
  swp_stepD ix_8000ecd4 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ecd4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_8000ecd8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 14) ≠ (0#64) → NW live Dt DA S Q 0x8000ece0#64 R Mt) (hF : ¬ ((R 14) ≠ (0#64)) → NW live Dt DA S Q 0x8000ecdc#64 R Mt) :
    NW live Dt DA S Q 0x8000ecd8#64 R Mt := by
  by_cases hc : (R 14) ≠ (0#64)
  · exact
    swp_stepD ixT_8000ecd8 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ecd8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ecd8 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ecd8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ecdc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x020#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x020#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000ece0#64 (upd R 15 (ldv .lw Mt ((R 11) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ecdc#64 R Mt :=
  swp_stepD ix_8000ecdc [11, 15] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x020#12)).toNat 4] (accAddrs ((R 11) + sign_extend (m := 64) (0x020#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ecdc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [11, 15])))) rfl hk

theorem it_8000ece0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 8) + sign_extend (m := 64) (0x00c#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x00c#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000ece4#64 R (writeLog Mt [(((R 8) + sign_extend (m := 64) (0x00c#12)).toNat, 4, (R 15))])) :
    NW live Dt DA S Q 0x8000ece0#64 R Mt :=
  swp_stepD ix_8000ece0 [8, 15] [] [] (accAddrs ((R 8) + sign_extend (m := 64) (0x00c#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ece0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ece4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (0#64).toInt < (R 9).toInt → NW live Dt DA S Q 0x8000ecf4#64 R Mt) (hF : ¬ ((0#64).toInt < (R 9).toInt) → NW live Dt DA S Q 0x8000ece8#64 R Mt) :
    NW live Dt DA S Q 0x8000ece4#64 R Mt := by
  by_cases hc : (0#64).toInt < (R 9).toInt
  · exact
    swp_stepD ixT_8000ece4 [9] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ece4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ece4 [9] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ece4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ece8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ed4c#64 R Mt) :
    NW live Dt DA S Q 0x8000ece8#64 R Mt :=
  swp_stepD ix_8000ece8 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ece8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ecec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ecf0#64 (upd R 18 ((R 18) + (R 10))) Mt) :
    NW live Dt DA S Q 0x8000ecec#64 R Mt :=
  swp_stepD ix_8000ecec [10, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ecec ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [10, 18])))) rfl hk

theorem it_8000ecf0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 9).toInt ≤ (0#64).toInt → NW live Dt DA S Q 0x8000ed4c#64 R Mt) (hF : ¬ ((R 9).toInt ≤ (0#64).toInt) → NW live Dt DA S Q 0x8000ecf4#64 R Mt) :
    NW live Dt DA S Q 0x8000ecf0#64 R Mt := by
  by_cases hc : (R 9).toInt ≤ (0#64).toInt
  · exact
    swp_stepD ixT_8000ecf0 [9] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ecf0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ecf0 [9] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ecf0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ecf4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x040#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x040#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ecf8#64 (upd R 15 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x040#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ecf4#64 R Mt :=
  swp_stepD ix_8000ecf4 [8, 15] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x040#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x040#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ecf4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [8, 15])))) rfl hk

theorem it_8000ecf8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ecfc#64 (upd R 11 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x030#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ecf8#64 R Mt :=
  swp_stepD ix_8000ecf8 [8, 11] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x030#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x030#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ecf8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [8, 11])))) rfl hk

theorem it_8000ecfc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ed00#64 (upd R 13 ((R 9) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ecfc#64 R Mt :=
  swp_stepD ix_8000ecfc [9, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ecfc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [9, 13])))) rfl hk

theorem it_8000ed00 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ed04#64 (upd R 12 ((R 18) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ed00#64 R Mt :=
  swp_stepD ix_8000ed00 [12, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ed00 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 18])))) rfl hk

theorem it_8000ed04 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ed08#64 (upd R 10 ((R 19) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ed04#64 R Mt :=
  swp_stepD ix_8000ed04 [10, 19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ed04 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 19])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem it_8000ed08 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (Sail.BitVec.update (R 15 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hk : NW live Dt DA S Q (Sail.BitVec.update (R 15 + sign_extend (m := 64) (0x000#12)) 0 0#1) (upd R 1 (BitVec.ofNat 64 (0x8000ed08 + 4))) Mt) :
    NW live Dt DA S Q 0x8000ed08#64 R Mt :=
  swp_jalr 0x8000ed08 [0xe7#8, 0x80#8, 0x07#8, 0x00#8] [15] (Sail.BitVec.update (R 15 + sign_extend (m := 64) (0x000#12)) 0 0#1)
    (jalrStep_of_obs
      (fun q hq => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
        exact (show ∀ k ∈ [15], 1 ≤ k ∧ k ≤ 31 by decide) k hk)
      (fun p hp => hlive _ (stdio_code_8000ed08 p hp))
      (fun c hG hi hpc hRR hMR => by
      obtain ⟨vm, hmi⟩ := hG.minstret
      have hb0 := hMR (0x8000ed08, .discard, 0xe7#8) (by simp [codeFoot])
      have hb1 := hMR (0x8000ed09, .discard, 0x80#8) (by simp [codeFoot])
      have hb2 := hMR (0x8000ed0a, .discard, 0x07#8) (by simp [codeFoot])
      have hb3 := hMR (0x8000ed0b, .discard, 0x00#8) (by simp [codeFoot])
      obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
        stepObs_jalr c.σ c.tick c.steps (0x8000ed08#64) vm (R 15) (0x000780e7#32) (0x000#12)
          (regidx.Regidx 0x0f#5) (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000ed08#64) 4)
          (0xe7#8) (0x80#8) (0x07#8) (0x00#8)
          hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
          (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
          (Vsa.Sim.decodeW (w := 0x000780e7#32) (afterPrelude c.σ)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
          (rX_bits_x15 _ (R 15) (by rw [get?_afterNextPC c.σ (0x8000ed08#64) _ (by decide) (by decide)]; exact hRR (15, Iris.DFrac.own 1, R 15) (by simp)))
          hal (by decide) (by decide) (by decide) (by decide) (by decide)
          (wX_bits_x1 _ (BitVec.addInt (0x8000ed08#64) 4)) hi
      refine ⟨σ', i', vm, hs, hi', hG', hmem, ?_⟩
      rwa [show BitVec.addInt (0x8000ed08#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000ed08 + 4) from by
        apply BitVec.eq_of_toNat_eq; decide] at hobs))
    (fun p hp => List.mem_append_left _ (stdio_code_8000ed08 p hp))
    (by decide) (by decide) (by decide) rfl hk

theorem it_8000ed0c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ed10#64 (upd R 9 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 9) 31 0) - (Sail.BitVec.extractLsb (R 10) 31 0)))) Mt) :
    NW live Dt DA S Q 0x8000ed0c#64 R Mt :=
  swp_stepD ix_8000ed0c [9, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ed0c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9, 10])))) rfl hk

theorem it_8000ed10 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (0#64).toInt < (R 10).toInt → NW live Dt DA S Q 0x8000ecec#64 R Mt) (hF : ¬ ((0#64).toInt < (R 10).toInt) → NW live Dt DA S Q 0x8000ed14#64 R Mt) :
    NW live Dt DA S Q 0x8000ed10#64 R Mt := by
  by_cases hc : (0#64).toInt < (R 10).toInt
  · exact
    swp_stepD ixT_8000ed10 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ed10 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ed10 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ed10 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ed40 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x070#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x070#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000ed44#64 (upd R 13 (ldv .lw Mt ((R 11) + sign_extend (m := 64) (0x070#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ed40#64 R Mt :=
  swp_stepD ix_8000ed40 [11, 13] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x070#12)).toNat 4] (accAddrs ((R 11) + sign_extend (m := 64) (0x070#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ed40 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [11, 13])))) rfl hk

theorem it_8000ed44 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (0#64).toInt < (R 13).toInt → NW live Dt DA S Q 0x8000ebac#64 R Mt) (hF : ¬ ((0#64).toInt < (R 13).toInt) → NW live Dt DA S Q 0x8000ed48#64 R Mt) :
    NW live Dt DA S Q 0x8000ed44#64 R Mt := by
  by_cases hc : (0#64).toInt < (R 13).toInt
  · exact
    swp_stepD ixT_8000ed44 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ed44 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ed44 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ed44 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ed48 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ec9c#64 R Mt) :
    NW live Dt DA S Q 0x8000ed48#64 R Mt :=
  swp_stepD ix_8000ed48 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ed48 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ed4c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ed50#64 (upd R 9 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ed4c#64 R Mt :=
  swp_stepD ix_8000ed4c [2, 9] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ed4c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [2, 9])))) rfl hk

theorem it_8000ed50 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ed54#64 (upd R 18 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ed50#64 R Mt :=
  swp_stepD ix_8000ed50 [2, 18] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ed50 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [2, 18])))) rfl hk

theorem it_8000ed54 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ec9c#64 R Mt) :
    NW live Dt DA S Q 0x8000ed54#64 R Mt :=
  swp_stepD ix_8000ed54 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ed54 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
