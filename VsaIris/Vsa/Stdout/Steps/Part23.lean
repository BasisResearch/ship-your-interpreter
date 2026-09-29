import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000ca2c : List BBlock := [{ body := [mkLine 0x8000ca2c#64 0x15c10693#32], term := none }]
def ix_8000ca30 : List BBlock := [{ body := [mkLine 0x8000ca30#64 0x07613823#32], term := none }]
def ix_8000ca34 : List BBlock := [{ body := [mkLine 0x8000ca34#64 0x00068d93#32], term := none }]
def ix_8000ca38 : List BBlock := [{ body := [mkLine 0x8000ca38#64 0x000d0b13#32], term := none }]
def ix_8000ca3c : List BBlock := [{ body := [mkLine 0x8000ca3c#64 0x400e7a13#32], term := none }]
def ix_8000ca40 : List BBlock := [{ body := [mkLine 0x8000ca40#64 0x06013d03#32], term := none }]
def ix_8000ca44 : List BBlock := [{ body := [mkLine 0x8000ca44#64 0x00000413#32], term := none }]
def ix_8000ca48 : List BBlock := [{ body := [mkLine 0x8000ca48#64 0x03d13023#32], term := none }]
def ix_8000ca4c : List BBlock := [{ body := [mkLine 0x8000ca4c#64 0x03713423#32], term := none }]
def ix_8000ca50 : List BBlock := [{ body := [mkLine 0x8000ca50#64 0x03113823#32], term := none }]
def ix_8000ca54 : List BBlock := [{ body := [mkLine 0x8000ca54#64 0x07c13423#32], term := none }]
def ix_8000ca58 : List BBlock := [{ body := [mkLine 0x8000ca58#64 0x06d13c23#32], term := none }]
def ix_8000ca5c : List BBlock := [⟨[], some (⟨0x8000ca5c#64, 0x0240006f#32, 0x6f#8, 0x00#8, 0x40#8, 0x02#8, .j, 0, 0, 0x0#13, 0x24#21, 0#12⟩ : TInstr)⟩]
def ix_8000ca60 : List BBlock := [{ body := [mkLine 0x8000ca60#64 0x000b0513#32], term := none }]
def ix_8000ca64 : List BBlock := [{ body := [mkLine 0x8000ca64#64 0x00a00593#32], term := none }]
def ix_8000ca6c : List BBlock := [{ body := [mkLine 0x8000ca6c#64 0x000b0b93#32], term := none }]
def ix_8000ca70 : List BBlock := [{ body := [mkLine 0x8000ca70#64 0x00900793#32], term := none }]
def ix_8000ca74 : List BBlock := [{ body := [mkLine 0x8000ca74#64 0x000c8d93#32], term := none }]
def ix_8000ca78 : List BBlock := [{ body := [mkLine 0x8000ca78#64 0x00050b13#32], term := none }]
def ixT_8000ca7c : List BBlock := [⟨[], some (⟨0x8000ca7c#64, 0x0377fe63#32, 0x63#8, 0xfe#8, 0x77#8, 0x03#8, .br bop.BGEU true, 15, 23, 0x3c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ca7c : List BBlock := [⟨[], some (⟨0x8000ca7c#64, 0x0377fe63#32, 0x63#8, 0xfe#8, 0x77#8, 0x03#8, .br bop.BGEU false, 15, 23, 0x3c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000ca80 : List BBlock := [{ body := [mkLine 0x8000ca80#64 0x00a00593#32], term := none }]
def ix_8000ca84 : List BBlock := [{ body := [mkLine 0x8000ca84#64 0x000b0513#32], term := none }]
def ix_8000ca8c : List BBlock := [{ body := [mkLine 0x8000ca8c#64 0x0305051b#32], term := none }]
def ix_8000ca90 : List BBlock := [{ body := [mkLine 0x8000ca90#64 0xfead8fa3#32], term := none }]
def ix_8000ca94 : List BBlock := [{ body := [mkLine 0x8000ca94#64 0xfffd8c93#32], term := none }]
def ix_8000ca98 : List BBlock := [{ body := [mkLine 0x8000ca98#64 0x0014041b#32], term := none }]
def ixT_8000ca9c : List BBlock := [⟨[], some (⟨0x8000ca9c#64, 0xfc0a02e3#32, 0xe3#8, 0x02#8, 0x0a#8, 0xfc#8, .br bop.BEQ true, 20, 0, 0x1fc4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000ca9c : List BBlock := [⟨[], some (⟨0x8000ca9c#64, 0xfc0a02e3#32, 0xe3#8, 0x02#8, 0x0a#8, 0xfc#8, .br bop.BEQ false, 20, 0, 0x1fc4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000cab8 : List BBlock := [{ body := [mkLine 0x8000cab8#64 0x07813683#32], term := none }]
def ix_8000cabc : List BBlock := [{ body := [mkLine 0x8000cabc#64 0x07013b03#32], term := none }]
def ix_8000cac0 : List BBlock := [{ body := [mkLine 0x8000cac0#64 0x02813b83#32], term := none }]
def ix_8000cac4 : List BBlock := [{ body := [mkLine 0x8000cac4#64 0x07a13023#32], term := none }]
def ix_8000cac8 : List BBlock := [{ body := [mkLine 0x8000cac8#64 0x02813423#32], term := none }]
def ix_8000cacc : List BBlock := [{ body := [mkLine 0x8000cacc#64 0x419686bb#32], term := none }]
def ix_8000cad0 : List BBlock := [{ body := [mkLine 0x8000cad0#64 0x02013e83#32], term := none }]
def ix_8000cad4 : List BBlock := [{ body := [mkLine 0x8000cad4#64 0x03013883#32], term := none }]
def ix_8000cad8 : List BBlock := [{ body := [mkLine 0x8000cad8#64 0x06813e03#32], term := none }]
def ix_8000cadc : List BBlock := [{ body := [mkLine 0x8000cadc#64 0x000b071b#32], term := none }]
def ixT_8000cae0 : List BBlock := [⟨[], some (⟨0x8000cae0#64, 0x3adb4663#32, 0x63#8, 0x46#8, 0xdb#8, 0x3a#8, .br bop.BLT true, 22, 13, 0x3ac#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000cae0 : List BBlock := [⟨[], some (⟨0x8000cae0#64, 0x3adb4663#32, 0x63#8, 0x46#8, 0xdb#8, 0x3a#8, .br bop.BLT false, 22, 13, 0x3ac#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000cae4 : List BBlock := [{ body := [mkLine 0x8000cae4#64 0x0a714f03#32], term := none }]
def ix_8000cae8 : List BBlock := [{ body := [mkLine 0x8000cae8#64 0x00000313#32], term := none }]
def ix_8000caec : List BBlock := [{ body := [mkLine 0x8000caec#64 0x02013023#32], term := none }]
def ix_8000caf0 : List BBlock := [⟨[], some (⟨0x8000caf0#64, 0x955fe06f#32, 0x6f#8, 0xe0#8, 0x5f#8, 0x95#8, .j, 0, 0, 0x0#13, 0x1fe954#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_8000ca2c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca30#64 (upd R 13 ((R 2) + sign_extend (m := 64) (0x15c#12))) Mt) :
    NW live Dt DA S Q 0x8000ca2c#64 R Mt :=
  swp_stepD ix_8000ca2c [2, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca2c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [2, 13])))) rfl hk

theorem it_8000ca30 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ca34#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x070#12)).toNat, 8, (R 22))])) :
    NW live Dt DA S Q 0x8000ca30#64 R Mt :=
  swp_stepD ix_8000ca30 [2, 22] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ca30 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ca34 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca38#64 (upd R 27 ((R 13) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ca34#64 R Mt :=
  swp_stepD ix_8000ca34 [13, 27] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca34 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 27 ∈ [13, 27])))) rfl hk

theorem it_8000ca38 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca3c#64 (upd R 22 ((R 26) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ca38#64 R Mt :=
  swp_stepD ix_8000ca38 [22, 26] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca38 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [22, 26])))) rfl hk

theorem it_8000ca3c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca40#64 (upd R 20 ((R 28) &&& sign_extend (m := 64) (0x400#12))) Mt) :
    NW live Dt DA S Q 0x8000ca3c#64 R Mt :=
  swp_stepD ix_8000ca3c [20, 28] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca3c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [20, 28])))) rfl hk

theorem it_8000ca40 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x060#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x060#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ca44#64 (upd R 26 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x060#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000ca40#64 R Mt :=
  swp_stepD ix_8000ca40 [2, 26] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x060#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x060#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca40 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 26 ∈ [2, 26])))) rfl hk

theorem it_8000ca44 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca48#64 (upd R 8 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ca44#64 R Mt :=
  swp_stepD ix_8000ca44 [8] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca44 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8])))) rfl hk

theorem it_8000ca48 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ca4c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (R 29))])) :
    NW live Dt DA S Q 0x8000ca48#64 R Mt :=
  swp_stepD ix_8000ca48 [2, 29] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ca48 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ca4c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ca50#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x028#12)).toNat, 8, (R 23))])) :
    NW live Dt DA S Q 0x8000ca4c#64 R Mt :=
  swp_stepD ix_8000ca4c [2, 23] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ca4c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ca50 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ca54#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x030#12)).toNat, 8, (R 17))])) :
    NW live Dt DA S Q 0x8000ca50#64 R Mt :=
  swp_stepD ix_8000ca50 [2, 17] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ca50 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ca54 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ca58#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x068#12)).toNat, 8, (R 28))])) :
    NW live Dt DA S Q 0x8000ca54#64 R Mt :=
  swp_stepD ix_8000ca54 [2, 28] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ca54 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ca58 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000ca5c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x078#12)).toNat, 8, (R 13))])) :
    NW live Dt DA S Q 0x8000ca58#64 R Mt :=
  swp_stepD ix_8000ca58 [2, 13] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ca58 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ca5c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca80#64 R Mt) :
    NW live Dt DA S Q 0x8000ca5c#64 R Mt :=
  swp_stepD ix_8000ca5c [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca5c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ca60 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca64#64 (upd R 10 ((R 22) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ca60#64 R Mt :=
  swp_stepD ix_8000ca60 [10, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca60 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 22])))) rfl hk

theorem it_8000ca64 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca68#64 (upd R 11 ((0#64) + sign_extend (m := 64) (0x00a#12))) Mt) :
    NW live Dt DA S Q 0x8000ca64#64 R Mt :=
  swp_stepD ix_8000ca64 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca64 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000ca68 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000ca68 [0xef#8, 0x70#8, 0x5f#8, 0xc4#8], live p.1) :
    JalExec (vsaModel live) 0x8000ca68 [0xef#8, 0x70#8, 0x5f#8, 0xc4#8] 0x800046ac#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000ca68, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000ca69, .discard, 0x70#8) (by simp [codeFoot])
  have hb2 := hb (0x8000ca6a, .discard, 0x5f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000ca6b, .discard, 0xc4#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000ca68#64) vm (0xc45f70ef#32) (0x1f7c44#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000ca68#64) 4)
      (0xef#8) (0x70#8) (0x5f#8) (0xc4#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xc45f70ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000ca68#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x800046ac#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000ca68#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000ca68 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000ca68 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x800046ac#64 (upd R 1 (BitVec.ofNat 64 (0x8000ca68 + 4))) Mt) :
    NW live Dt DA S Q 0x8000ca68#64 R Mt :=
  swp_jal 0x8000ca68 [0xef#8, 0x70#8, 0x5f#8, 0xc4#8] 0x800046ac#64 (jalx_8000ca68 live (fun p hp => hlive _ (stdio_code_8000ca68 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000ca68 p hp)) (by decide) (by decide) rfl hk

theorem it_8000ca6c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca70#64 (upd R 23 ((R 22) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ca6c#64 R Mt :=
  swp_stepD ix_8000ca6c [22, 23] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca6c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [22, 23])))) rfl hk

theorem it_8000ca70 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca74#64 (upd R 15 ((0#64) + sign_extend (m := 64) (0x009#12))) Mt) :
    NW live Dt DA S Q 0x8000ca70#64 R Mt :=
  swp_stepD ix_8000ca70 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca70 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_8000ca74 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca78#64 (upd R 27 ((R 25) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ca74#64 R Mt :=
  swp_stepD ix_8000ca74 [25, 27] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca74 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 27 ∈ [25, 27])))) rfl hk

theorem it_8000ca78 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca7c#64 (upd R 22 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ca78#64 R Mt :=
  swp_stepD ix_8000ca78 [10, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca78 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [10, 22])))) rfl hk

theorem it_8000ca7c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 23).toNat ≤ (R 15).toNat → NW live Dt DA S Q 0x8000cab8#64 R Mt) (hF : ¬ ((R 23).toNat ≤ (R 15).toNat) → NW live Dt DA S Q 0x8000ca80#64 R Mt) :
    NW live Dt DA S Q 0x8000ca7c#64 R Mt := by
  by_cases hc : (R 23).toNat ≤ (R 15).toNat
  · exact
    swp_stepD ixT_8000ca7c [15, 23] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ca7c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bgeu _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ca7c [15, 23] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ca7c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bgeu _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000ca80 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca84#64 (upd R 11 ((0#64) + sign_extend (m := 64) (0x00a#12))) Mt) :
    NW live Dt DA S Q 0x8000ca80#64 R Mt :=
  swp_stepD ix_8000ca80 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca80 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

theorem it_8000ca84 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca88#64 (upd R 10 ((R 22) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000ca84#64 R Mt :=
  swp_stepD ix_8000ca84 [10, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca84 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 22])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000ca88 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000ca88 [0xef#8, 0x70#8, 0xdf#8, 0xc6#8], live p.1) :
    JalExec (vsaModel live) 0x8000ca88 [0xef#8, 0x70#8, 0xdf#8, 0xc6#8] 0x800046f4#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000ca88, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000ca89, .discard, 0x70#8) (by simp [codeFoot])
  have hb2 := hb (0x8000ca8a, .discard, 0xdf#8) (by simp [codeFoot])
  have hb3 := hb (0x8000ca8b, .discard, 0xc6#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000ca88#64) vm (0xc6df70ef#32) (0x1f7c6c#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000ca88#64) 4)
      (0xef#8) (0x70#8) (0xdf#8) (0xc6#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0xc6df70ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000ca88#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x800046f4#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000ca88#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000ca88 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000ca88 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x800046f4#64 (upd R 1 (BitVec.ofNat 64 (0x8000ca88 + 4))) Mt) :
    NW live Dt DA S Q 0x8000ca88#64 R Mt :=
  swp_jal 0x8000ca88 [0xef#8, 0x70#8, 0xdf#8, 0xc6#8] 0x800046f4#64 (jalx_8000ca88 live (fun p hp => hlive _ (stdio_code_8000ca88 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000ca88 p hp)) (by decide) (by decide) rfl hk

theorem it_8000ca8c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca90#64 (upd R 10 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 10) + sign_extend (m := 64) (0x030#12)) 31 0))) Mt) :
    NW live Dt DA S Q 0x8000ca8c#64 R Mt :=
  swp_stepD ix_8000ca8c [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca8c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem it_8000ca90 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOKb ((R 27) + sign_extend (m := 64) (0xfff#12)).toNat)
    (hS : ∀ b ∈ accAddrs ((R 27) + sign_extend (m := 64) (0xfff#12)).toNat 1, S b)
    (hk : NW live Dt DA S Q 0x8000ca94#64 R (writeLog Mt [(((R 27) + sign_extend (m := 64) (0xfff#12)).toNat, 1, (R 10))])) :
    NW live Dt DA S Q 0x8000ca90#64 R Mt :=
  swp_stepD ix_8000ca90 [10, 27] [] [] (accAddrs ((R 27) + sign_extend (m := 64) (0xfff#12)).toNat 1) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000ca90 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000ca94 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca98#64 (upd R 25 ((R 27) + sign_extend (m := 64) (0xfff#12))) Mt) :
    NW live Dt DA S Q 0x8000ca94#64 R Mt :=
  swp_stepD ix_8000ca94 [25, 27] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca94 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 25 ∈ [25, 27])))) rfl hk

theorem it_8000ca98 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ca9c#64 (upd R 8 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 8) + sign_extend (m := 64) (0x001#12)) 31 0))) Mt) :
    NW live Dt DA S Q 0x8000ca98#64 R Mt :=
  swp_stepD ix_8000ca98 [8] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000ca98 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8])))) rfl hk

theorem it_8000ca9c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 20) = (0#64) → NW live Dt DA S Q 0x8000ca60#64 R Mt) (hF : ¬ ((R 20) = (0#64)) → NW live Dt DA S Q 0x8000caa0#64 R Mt) :
    NW live Dt DA S Q 0x8000ca9c#64 R Mt := by
  by_cases hc : (R 20) = (0#64)
  · exact
    swp_stepD ixT_8000ca9c [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000ca9c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000ca9c [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000ca9c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000cab8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cabc#64 (upd R 13 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x078#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000cab8#64 R Mt :=
  swp_stepD ix_8000cab8 [2, 13] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cab8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [2, 13])))) rfl hk

theorem it_8000cabc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cac0#64 (upd R 22 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x070#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000cabc#64 R Mt :=
  swp_stepD ix_8000cabc [2, 22] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cabc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [2, 22])))) rfl hk

theorem it_8000cac0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cac4#64 (upd R 23 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x028#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000cac0#64 R Mt :=
  swp_stepD ix_8000cac0 [2, 23] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cac0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [2, 23])))) rfl hk

theorem it_8000cac4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x060#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x060#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cac8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x060#12)).toNat, 8, (R 26))])) :
    NW live Dt DA S Q 0x8000cac4#64 R Mt :=
  swp_stepD ix_8000cac4 [2, 26] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x060#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000cac4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000cac8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cacc#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x028#12)).toNat, 8, (R 8))])) :
    NW live Dt DA S Q 0x8000cac8#64 R Mt :=
  swp_stepD ix_8000cac8 [2, 8] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000cac8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000cacc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000cad0#64 (upd R 13 (sign_extend (m := 64) ((Sail.BitVec.extractLsb (R 13) 31 0) - (Sail.BitVec.extractLsb (R 25) 31 0)))) Mt) :
    NW live Dt DA S Q 0x8000cacc#64 R Mt :=
  swp_stepD ix_8000cacc [13, 25] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cacc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13, 25])))) rfl hk

theorem it_8000cad0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cad4#64 (upd R 29 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000cad0#64 R Mt :=
  swp_stepD ix_8000cad0 [2, 29] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cad0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 29 ∈ [2, 29])))) rfl hk

theorem it_8000cad4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cad8#64 (upd R 17 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x030#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000cad4#64 R Mt :=
  swp_stepD ix_8000cad4 [2, 17] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cad4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 17 ∈ [2, 17])))) rfl hk

theorem it_8000cad8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cadc#64 (upd R 28 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x068#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000cad8#64 R Mt :=
  swp_stepD ix_8000cad8 [2, 28] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cad8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 28 ∈ [2, 28])))) rfl hk

theorem it_8000cadc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000cae0#64 (upd R 14 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 22) + sign_extend (m := 64) (0x000#12)) 31 0))) Mt) :
    NW live Dt DA S Q 0x8000cadc#64 R Mt :=
  swp_stepD ix_8000cadc [14, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cadc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 22])))) rfl hk

theorem it_8000cae0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 22).toInt < (R 13).toInt → NW live Dt DA S Q 0x8000ce8c#64 R Mt) (hF : ¬ ((R 22).toInt < (R 13).toInt) → NW live Dt DA S Q 0x8000cae4#64 R Mt) :
    NW live Dt DA S Q 0x8000cae0#64 R Mt := by
  by_cases hc : (R 22).toInt < (R 13).toInt
  · exact
    swp_stepD ixT_8000cae0 [13, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000cae0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000cae0 [13, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000cae0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000cae4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1, S b)
    (hk : NW live Dt DA S Q 0x8000cae8#64 (upd R 30 (ldv .lbu Mt ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000cae4#64 R Mt :=
  swp_stepD ix_8000cae4 [2, 30] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cae4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins1_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 30 ∈ [2, 30])))) rfl hk

theorem it_8000cae8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000caec#64 (upd R 6 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000cae8#64 R Mt :=
  swp_stepD ix_8000cae8 [6] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cae8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 6 ∈ [6])))) rfl hk

theorem it_8000caec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000caf0#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (0#64))])) :
    NW live Dt DA S Q 0x8000caec#64 R Mt :=
  swp_stepD ix_8000caec [2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000caec ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000caf0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b444#64 R Mt) :
    NW live Dt DA S Q 0x8000caf0#64 R Mt :=
  swp_stepD ix_8000caf0 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000caf0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
