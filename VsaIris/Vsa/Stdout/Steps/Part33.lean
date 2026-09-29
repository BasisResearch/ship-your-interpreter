import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc
import Vsa.Sim.DecodeNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000dd00 : List BBlock := [{ body := [mkLine 0x8000dd00#64 0x00000a13#32], term := none }]
def ix_8000dd04 : List BBlock := [{ body := [mkLine 0x8000dd04#64 0x02013823#32], term := none }]
def ix_8000dd08 : List BBlock := [⟨[], some (⟨0x8000dd08#64, 0xdadfc06f#32, 0x6f#8, 0xc0#8, 0xdf#8, 0xda#8, .j, 0, 0, 0x0#13, 0x1fcdac#21, 0#12⟩ : TInstr)⟩]
def ix_8000dda8 : List BBlock := [{ body := [mkLine 0x8000dda8#64 0x0105d783#32], term := none }]
def ix_8000ddac : List BBlock := [{ body := [mkLine 0x8000ddac#64 0x0b05ae03#32], term := none }]
def ix_8000ddb0 : List BBlock := [{ body := [mkLine 0x8000ddb0#64 0x0125d303#32], term := none }]
def ix_8000ddb4 : List BBlock := [{ body := [mkLine 0x8000ddb4#64 0x0305b883#32], term := none }]
def ix_8000ddb8 : List BBlock := [{ body := [mkLine 0x8000ddb8#64 0x0405b803#32], term := none }]
def ix_8000ddbc : List BBlock := [{ body := [mkLine 0x8000ddbc#64 0xb1010113#32], term := none }]
def ix_8000ddc0 : List BBlock := [{ body := [mkLine 0x8000ddc0#64 0x40000713#32], term := none }]
def ix_8000ddc4 : List BBlock := [{ body := [mkLine 0x8000ddc4#64 0xffd7f793#32], term := none }]
def ix_8000ddc8 : List BBlock := [{ body := [mkLine 0x8000ddc8#64 0x4e813023#32], term := none }]
def ix_8000ddcc : List BBlock := [{ body := [mkLine 0x8000ddcc#64 0x4d213823#32], term := none }]
def ix_8000ddd0 : List BBlock := [{ body := [mkLine 0x8000ddd0#64 0x00058413#32], term := none }]
def ix_8000ddd4 : List BBlock := [{ body := [mkLine 0x8000ddd4#64 0x00050913#32], term := none }]
def ix_8000ddd8 : List BBlock := [{ body := [mkLine 0x8000ddd8#64 0x0d010593#32], term := none }]
def ix_8000dddc : List BBlock := [{ body := [mkLine 0x8000dddc#64 0x0b810513#32], term := none }]
def ix_8000dde0 : List BBlock := [{ body := [mkLine 0x8000dde0#64 0x4e113423#32], term := none }]
def ix_8000dde4 : List BBlock := [{ body := [mkLine 0x8000dde4#64 0x4c913c23#32], term := none }]
def ix_8000dde8 : List BBlock := [{ body := [mkLine 0x8000dde8#64 0x00d13423#32], term := none }]
def ix_8000ddec : List BBlock := [{ body := [mkLine 0x8000ddec#64 0x00060493#32], term := none }]
def ix_8000ddf0 : List BBlock := [{ body := [mkLine 0x8000ddf0#64 0x02f11423#32], term := none }]
def ix_8000ddf4 : List BBlock := [{ body := [mkLine 0x8000ddf4#64 0x0dc12423#32], term := none }]
def ix_8000ddf8 : List BBlock := [{ body := [mkLine 0x8000ddf8#64 0x02611523#32], term := none }]
def ix_8000ddfc : List BBlock := [{ body := [mkLine 0x8000ddfc#64 0x05113423#32], term := none }]
def ix_8000de00 : List BBlock := [{ body := [mkLine 0x8000de00#64 0x05013c23#32], term := none }]
def ix_8000de04 : List BBlock := [{ body := [mkLine 0x8000de04#64 0x00b13c23#32], term := none }]
def ix_8000de08 : List BBlock := [{ body := [mkLine 0x8000de08#64 0x02b13823#32], term := none }]
def ix_8000de0c : List BBlock := [{ body := [mkLine 0x8000de0c#64 0x02e12223#32], term := none }]
def ix_8000de10 : List BBlock := [{ body := [mkLine 0x8000de10#64 0x02e12c23#32], term := none }]
def ix_8000de14 : List BBlock := [{ body := [mkLine 0x8000de14#64 0x04012023#32], term := none }]
def ix_8000de1c : List BBlock := [{ body := [mkLine 0x8000de1c#64 0x00813683#32], term := none }]
def ix_8000de20 : List BBlock := [{ body := [mkLine 0x8000de20#64 0x00048613#32], term := none }]
def ix_8000de24 : List BBlock := [{ body := [mkLine 0x8000de24#64 0x01810593#32], term := none }]
def ix_8000de28 : List BBlock := [{ body := [mkLine 0x8000de28#64 0x00090513#32], term := none }]
def ix_8000de30 : List BBlock := [{ body := [mkLine 0x8000de30#64 0x00050493#32], term := none }]
def ixT_8000de34 : List BBlock := [⟨[], some (⟨0x8000de34#64, 0x04055063#32, 0x63#8, 0x50#8, 0x05#8, 0x04#8, .br bop.BGE true, 10, 0, 0x40#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000de34 : List BBlock := [⟨[], some (⟨0x8000de34#64, 0x04055063#32, 0x63#8, 0x50#8, 0x05#8, 0x04#8, .br bop.BGE false, 10, 0, 0x40#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000de38 : List BBlock := [{ body := [mkLine 0x8000de38#64 0x02815783#32], term := none }]
def ix_8000de3c : List BBlock := [{ body := [mkLine 0x8000de3c#64 0x0407f793#32], term := none }]
def ixT_8000de40 : List BBlock := [⟨[], some (⟨0x8000de40#64, 0x00078863#32, 0x63#8, 0x88#8, 0x07#8, 0x00#8, .br bop.BEQ true, 15, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000de40 : List BBlock := [⟨[], some (⟨0x8000de40#64, 0x00078863#32, 0x63#8, 0x88#8, 0x07#8, 0x00#8, .br bop.BEQ false, 15, 0, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_8000dd00 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000dd04#64 (upd R 20 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000dd00#64 R Mt :=
  swp_stepD ix_8000dd00 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000dd00 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [20])))) rfl hk

theorem it_8000dd04 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000dd08#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x030#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000dd04#64 R Mt :=
  swp_stepD ix_8000dd04 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000dd04 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000dd08 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000aab4#64 R Mt) :
    NW live Dt DA S Q 0x8000dd08#64 R Mt :=
  swp_stepD ix_8000dd08 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000dd08 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000dda8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000ddac#64 (upd R 15 (ldv .lhu Mt ((R 11) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000dda8#64 R Mt :=
  swp_stepD ix_8000dda8 [11, 15] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2] (accAddrs ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000dda8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [11, 15])))) rfl hk

theorem it_8000ddac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x0b0#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x0b0#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000ddb0#64 (upd R 28 (ldv .lw Mt ((R 11) + sign_extend (m := 64) (0x0b0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ddac#64 R Mt :=
  swp_stepD ix_8000ddac [11, 28] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x0b0#12)).toNat 4] (accAddrs ((R 11) + sign_extend (m := 64) (0x0b0#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ddac ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 28 ∈ [11, 28])))) rfl hk

theorem it_8000ddb0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x012#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x012#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000ddb4#64 (upd R 6 (ldv .lhu Mt ((R 11) + sign_extend (m := 64) (0x012#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ddb0#64 R Mt :=
  swp_stepD ix_8000ddb0 [6, 11] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x012#12)).toNat 2] (accAddrs ((R 11) + sign_extend (m := 64) (0x012#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ddb0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 6 ∈ [6, 11])))) rfl hk

theorem it_8000ddb4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ddb8#64 (upd R 17 (ldv .ld Mt ((R 11) + sign_extend (m := 64) (0x030#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ddb4#64 R Mt :=
  swp_stepD ix_8000ddb4 [11, 17] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x030#12)).toNat 8] (accAddrs ((R 11) + sign_extend (m := 64) (0x030#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ddb4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 17 ∈ [11, 17])))) rfl hk

theorem it_8000ddb8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x040#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x040#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ddbc#64 (upd R 16 (ldv .ld Mt ((R 11) + sign_extend (m := 64) (0x040#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ddb8#64 R Mt :=
  swp_stepD ix_8000ddb8 [11, 16] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x040#12)).toNat 8] (accAddrs ((R 11) + sign_extend (m := 64) (0x040#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ddb8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 16 ∈ [11, 16])))) rfl hk

theorem it_8000ddbc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ddc0#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0xb10#12))) Mt) :
    NW live Dt DA S Q 0x8000ddbc#64 R Mt :=
  swp_stepD ix_8000ddbc [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ddbc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem it_8000ddc0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ddc4#64 (upd R 14 ((0#64) + sign_extend (m := 64) (0x400#12))) Mt) :
    NW live Dt DA S Q 0x8000ddc0#64 R Mt :=
  swp_stepD ix_8000ddc0 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ddc0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem it_8000ddc4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ddc8#64 (upd R 15 ((R 15) &&& sign_extend (m := 64) (0xffd#12))) Mt) :
    NW live Dt DA S Q 0x8000ddc4#64 R Mt :=
  swp_stepD ix_8000ddc4 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ddc4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_8000ddc8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x4e0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x4e0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ddcc#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x4e0#12)).toNat, 8, (R 8))])) :
    NW live Dt DA S Q 0x8000ddc8#64 R Mt :=
  swp_stepD ix_8000ddc8 [2, 8] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x4e0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ddc8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ddcc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x4d0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x4d0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ddd0#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x4d0#12)).toNat, 8, (R 18))])) :
    NW live Dt DA S Q 0x8000ddcc#64 R Mt :=
  swp_stepD ix_8000ddcc [2, 18] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x4d0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ddcc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ddd0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ddd4#64 (upd R 8 ((R 11) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ddd0#64 R Mt :=
  swp_stepD ix_8000ddd0 [8, 11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ddd0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8, 11])))) rfl hk

theorem it_8000ddd4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ddd8#64 (upd R 18 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ddd4#64 R Mt :=
  swp_stepD ix_8000ddd4 [10, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ddd4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [10, 18])))) rfl hk

theorem it_8000ddd8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000dddc#64 (upd R 11 ((R 2) + sign_extend (m := 64) (0x0d0#12))) Mt) :
    NW live Dt DA S Q 0x8000ddd8#64 R Mt :=
  swp_stepD ix_8000ddd8 [2, 11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ddd8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [2, 11])))) rfl hk

theorem it_8000dddc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000dde0#64 (upd R 10 ((R 2) + sign_extend (m := 64) (0x0b8#12))) Mt) :
    NW live Dt DA S Q 0x8000dddc#64 R Mt :=
  swp_stepD ix_8000dddc [2, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000dddc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [2, 10])))) rfl hk

theorem it_8000dde0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x4e8#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x4e8#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000dde4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x4e8#12)).toNat, 8, (R 1))])) :
    NW live Dt DA S Q 0x8000dde0#64 R Mt :=
  swp_stepD ix_8000dde0 [1, 2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x4e8#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000dde0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000dde4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x4d8#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x4d8#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000dde8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x4d8#12)).toNat, 8, (R 9))])) :
    NW live Dt DA S Q 0x8000dde4#64 R Mt :=
  swp_stepD ix_8000dde4 [2, 9] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x4d8#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000dde4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000dde8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ddec#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 13))])) :
    NW live Dt DA S Q 0x8000dde8#64 R Mt :=
  swp_stepD ix_8000dde8 [2, 13] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000dde8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ddec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ddf0#64 (upd R 9 ((R 12) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ddec#64 R Mt :=
  swp_stepD ix_8000ddec [9, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ddec ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9, 12])))) rfl hk

theorem it_8000ddf0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 2)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000ddf4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x028#12)).toNat, 2, (R 15))])) :
    NW live Dt DA S Q 0x8000ddf0#64 R Mt :=
  swp_stepD ix_8000ddf0 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 2) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ddf0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ddf4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0c8#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0c8#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000ddf8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0c8#12)).toNat, 4, (R 28))])) :
    NW live Dt DA S Q 0x8000ddf4#64 R Mt :=
  swp_stepD ix_8000ddf4 [2, 28] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0c8#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ddf4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ddf8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x02a#12)).toNat 2)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x02a#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000ddfc#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x02a#12)).toNat, 2, (R 6))])) :
    NW live Dt DA S Q 0x8000ddf8#64 R Mt :=
  swp_stepD ix_8000ddf8 [2, 6] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x02a#12)).toNat 2) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ddf8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ddfc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x048#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x048#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000de00#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x048#12)).toNat, 8, (R 17))])) :
    NW live Dt DA S Q 0x8000ddfc#64 R Mt :=
  swp_stepD ix_8000ddfc [2, 17] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x048#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ddfc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000de00 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000de04#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x058#12)).toNat, 8, (R 16))])) :
    NW live Dt DA S Q 0x8000de00#64 R Mt :=
  swp_stepD ix_8000de00 [2, 16] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000de00 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000de04 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000de08#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 11))])) :
    NW live Dt DA S Q 0x8000de04#64 R Mt :=
  swp_stepD ix_8000de04 [2, 11] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000de04 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000de08 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000de0c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x030#12)).toNat, 8, (R 11))])) :
    NW live Dt DA S Q 0x8000de08#64 R Mt :=
  swp_stepD ix_8000de08 [2, 11] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000de08 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000de0c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x024#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x024#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000de10#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x024#12)).toNat, 4, (R 14))])) :
    NW live Dt DA S Q 0x8000de0c#64 R Mt :=
  swp_stepD ix_8000de0c [2, 14] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x024#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000de0c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000de10 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000de14#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x038#12)).toNat, 4, (R 14))])) :
    NW live Dt DA S Q 0x8000de10#64 R Mt :=
  swp_stepD ix_8000de10 [2, 14] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000de10 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000de14 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000de18#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x040#12)).toNat, 4, (0#64))])) :
    NW live Dt DA S Q 0x8000de14#64 R Mt :=
  swp_stepD ix_8000de14 [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000de14 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000de18 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000de18 [0xef#8, 0x90#8, 0x8f#8, 0x9b#8], live p.1) :
    JalExec (vsaModel live) 0x8000de18 [0xef#8, 0x90#8, 0x8f#8, 0x9b#8] 0x80006fd0#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000de18, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000de19, .discard, 0x90#8) (by simp [codeFoot])
  have hb2 := hb (0x8000de1a, .discard, 0x8f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000de1b, .discard, 0x9b#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000de18#64) vm (0x9b8f90ef#32) (0x1f91b8#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000de18#64) 4)
      (0xef#8) (0x90#8) (0x8f#8) (0x9b#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0x9b8f90ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000de18#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80006fd0#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000de18#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000de18 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000de18 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80006fd0#64 (upd R 1 (BitVec.ofNat 64 (0x8000de18 + 4))) Mt) :
    NW live Dt DA S Q 0x8000de18#64 R Mt :=
  swp_jal 0x8000de18 [0xef#8, 0x90#8, 0x8f#8, 0x9b#8] 0x80006fd0#64 (jalx_8000de18 live (fun p hp => hlive _ (stdio_code_8000de18 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000de18 p hp)) (by decide) (by decide) rfl hk

theorem it_8000de1c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000de20#64 (upd R 13 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000de1c#64 R Mt :=
  swp_stepD ix_8000de1c [2, 13] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000de1c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [2, 13])))) rfl hk

theorem it_8000de20 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000de24#64 (upd R 12 ((R 9) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000de20#64 R Mt :=
  swp_stepD ix_8000de20 [9, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000de20 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [9, 12])))) rfl hk

theorem it_8000de24 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000de28#64 (upd R 11 ((R 2) + sign_extend (m := 64) (0x018#12))) Mt) :
    NW live Dt DA S Q 0x8000de24#64 R Mt :=
  swp_stepD ix_8000de24 [2, 11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000de24 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [2, 11])))) rfl hk

theorem it_8000de28 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000de2c#64 (upd R 10 ((R 18) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000de28#64 R Mt :=
  swp_stepD ix_8000de28 [10, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000de28 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 18])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000de2c (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000de2c [0xef#8, 0xc0#8, 0x9f#8, 0xa5#8], live p.1) :
    JalExec (vsaModel live) 0x8000de2c [0xef#8, 0xc0#8, 0x9f#8, 0xa5#8] 0x8000a884#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000de2c, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000de2d, .discard, 0xc0#8) (by simp [codeFoot])
  have hb2 := hb (0x8000de2e, .discard, 0x9f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000de2f, .discard, 0xa5#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000de2c#64) vm (0xa59fc0ef#32) (0x1fca58#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000de2c#64) 4)
      (0xef#8) (0xc0#8) (0x9f#8) (0xa5#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xa59fc0ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000de2c#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x8000a884#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000de2c#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000de2c + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000de2c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000a884#64 (upd R 1 (BitVec.ofNat 64 (0x8000de2c + 4))) Mt) :
    NW live Dt DA S Q 0x8000de2c#64 R Mt :=
  swp_jal 0x8000de2c [0xef#8, 0xc0#8, 0x9f#8, 0xa5#8] 0x8000a884#64 (jalx_8000de2c live (fun p hp => hlive _ (stdio_code_8000de2c p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000de2c p hp)) (by decide) (by decide) rfl hk

theorem it_8000de30 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000de34#64 (upd R 9 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000de30#64 R Mt :=
  swp_stepD ix_8000de30 [9, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000de30 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9, 10])))) rfl hk

theorem it_8000de34 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (0#64).toInt ≤ (R 10).toInt → NW live Dt DA S Q 0x8000de74#64 R Mt) (hF : ¬ ((0#64).toInt ≤ (R 10).toInt) → NW live Dt DA S Q 0x8000de38#64 R Mt) :
    NW live Dt DA S Q 0x8000de34#64 R Mt := by
  by_cases hc : (0#64).toInt ≤ (R 10).toInt
  · exact
    swp_stepD ixT_8000de34 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000de34 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000de34 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000de34 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000de38 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000de3c#64 (upd R 15 (ldv .lhu Mt ((R 2) + sign_extend (m := 64) (0x028#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000de38#64 R Mt :=
  swp_stepD ix_8000de38 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 2] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000de38 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem it_8000de3c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000de40#64 (upd R 15 ((R 15) &&& sign_extend (m := 64) (0x040#12))) Mt) :
    NW live Dt DA S Q 0x8000de3c#64 R Mt :=
  swp_stepD ix_8000de3c [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000de3c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_8000de40 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) = (0#64) → NW live Dt DA S Q 0x8000de50#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → NW live Dt DA S Q 0x8000de44#64 R Mt) :
    NW live Dt DA S Q 0x8000de40#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    swp_stepD ixT_8000de40 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000de40 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000de40 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000de40 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

end VsaIris.Sym
