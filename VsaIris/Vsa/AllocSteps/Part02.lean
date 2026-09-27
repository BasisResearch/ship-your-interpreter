import VsaIris.Vsa.AllocRun

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ax_80004bc8 : List BBlock := [{ body := [mkLine 0x80004bc8#64 0x4901b783#32], term := none }]
def axT_80004bcc : List BBlock := [⟨[], some (⟨0x80004bcc#64, 0x00d7f463#32, 0x63#8, 0xf4#8, 0xd7#8, 0x00#8, .br bop.BGEU true, 15, 13, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80004bcc : List BBlock := [⟨[], some (⟨0x80004bcc#64, 0x00d7f463#32, 0x63#8, 0xf4#8, 0xd7#8, 0x00#8, .br bop.BGEU false, 15, 13, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80004bd0 : List BBlock := [{ body := [mkLine 0x80004bd0#64 0x48d1b823#32], term := none }]
def ax_80004bd4 : List BBlock := [{ body := [mkLine 0x80004bd4#64 0x4881b783#32], term := none }]
def axT_80004bd8 : List BBlock := [⟨[], some (⟨0x80004bd8#64, 0x00d7f463#32, 0x63#8, 0xf4#8, 0xd7#8, 0x00#8, .br bop.BGEU true, 15, 13, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80004bd8 : List BBlock := [⟨[], some (⟨0x80004bd8#64, 0x00d7f463#32, 0x63#8, 0xf4#8, 0xd7#8, 0x00#8, .br bop.BGEU false, 15, 13, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80004bdc : List BBlock := [{ body := [mkLine 0x80004bdc#64 0x48d1b423#32], term := none }]
def ax_80004be0 : List BBlock := [{ body := [mkLine 0x80004be0#64 0x000e0793#32], term := none }]
def ax_80004be4 : List BBlock := [⟨[], some (⟨0x80004be4#64, 0x2240006f#32, 0x6f#8, 0x00#8, 0x40#8, 0x22#8, .j, 0, 0, 0x0#13, 0x224#21, 0#12⟩ : TInstr)⟩]
def ax_80004be8 : List BBlock := [{ body := [mkLine 0x80004be8#64 0x00883583#32], term := none }]
def ax_80004bec : List BBlock := [⟨[], some (⟨0x80004bec#64, 0xd7dff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xd7#8, .j, 0, 0, 0x0#13, 0x1ffd7c#21, 0#12⟩ : TInstr)⟩]
def ax_80004bf0 : List BBlock := [{ body := [mkLine 0x80004bf0#64 0x00176613#32], term := none }]
def ax_80004bf4 : List BBlock := [{ body := [mkLine 0x80004bf4#64 0x00c7b423#32], term := none }]
def ax_80004bf8 : List BBlock := [{ body := [mkLine 0x80004bf8#64 0x00e78733#32], term := none }]
def ax_80004bfc : List BBlock := [{ body := [mkLine 0x80004bfc#64 0x00f13423#32], term := none }]
def ax_80004c00 : List BBlock := [{ body := [mkLine 0x80004c00#64 0x0016e693#32], term := none }]
def ax_80004c04 : List BBlock := [{ body := [mkLine 0x80004c04#64 0x00e83823#32], term := none }]
def ax_80004c08 : List BBlock := [{ body := [mkLine 0x80004c08#64 0x00040513#32], term := none }]
def ax_80004c0c : List BBlock := [{ body := [mkLine 0x80004c0c#64 0x00d73423#32], term := none }]
def ax_80004c14 : List BBlock := [{ body := [mkLine 0x80004c14#64 0x00813783#32], term := none }]
def ax_80004c18 : List BBlock := [{ body := [mkLine 0x80004c18#64 0x01078513#32], term := none }]
def ax_80004c1c : List BBlock := [⟨[], some (⟨0x80004c1c#64, 0xc15ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xc1#8, .j, 0, 0, 0x0#13, 0x1ffc14#21, 0#12⟩ : TInstr)⟩]
def ax_80004c20 : List BBlock := [{ body := [mkLine 0x80004c20#64 0x0107b603#32], term := none }]
def ax_80004c24 : List BBlock := [{ body := [mkLine 0x80004c24#64 0x00d786b3#32], term := none }]
def ax_80004c28 : List BBlock := [{ body := [mkLine 0x80004c28#64 0x0086b703#32], term := none }]
def ax_80004c2c : List BBlock := [{ body := [mkLine 0x80004c2c#64 0x00b63c23#32], term := none }]
def ax_80004c30 : List BBlock := [{ body := [mkLine 0x80004c30#64 0x00c5b823#32], term := none }]
def ax_80004c34 : List BBlock := [{ body := [mkLine 0x80004c34#64 0x00176713#32], term := none }]
def ax_80004c38 : List BBlock := [{ body := [mkLine 0x80004c38#64 0x00040513#32], term := none }]
def ax_80004c3c : List BBlock := [{ body := [mkLine 0x80004c3c#64 0x00e6b423#32], term := none }]
def ax_80004c40 : List BBlock := [{ body := [mkLine 0x80004c40#64 0x00f13423#32], term := none }]
def ax_80004c48 : List BBlock := [{ body := [mkLine 0x80004c48#64 0x00813783#32], term := none }]
def ax_80004c4c : List BBlock := [{ body := [mkLine 0x80004c4c#64 0x05813083#32], term := none }]
def ax_80004c50 : List BBlock := [{ body := [mkLine 0x80004c50#64 0x05013403#32], term := none }]
def ax_80004c54 : List BBlock := [{ body := [mkLine 0x80004c54#64 0x01078513#32], term := none }]
def ax_80004c58 : List BBlock := [{ body := [mkLine 0x80004c58#64 0x06010113#32], term := none }]
def ax_80004c5c : List BBlock := [⟨[], some (⟨0x80004c5c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80004c60 : List BBlock := [{ body := [mkLine 0x80004c60#64 0x0186b783#32], term := none }]
def ax_80004c64 : List BBlock := [{ body := [mkLine 0x80004c64#64 0x0028889b#32], term := none }]
def axT_80004c68 : List BBlock := [⟨[], some (⟨0x80004c68#64, 0xc8f682e3#32, 0xe3#8, 0x82#8, 0xf6#8, 0xc8#8, .br bop.BEQ true, 13, 15, 0x1c84#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80004c68 : List BBlock := [⟨[], some (⟨0x80004c68#64, 0xc8f682e3#32, 0xe3#8, 0x82#8, 0xf6#8, 0xc8#8, .br bop.BEQ false, 13, 15, 0x1c84#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80004c70 : List BBlock := [{ body := [mkLine 0x80004c70#64 0x00935693#32], term := none }]
def ax_80004c74 : List BBlock := [{ body := [mkLine 0x80004c74#64 0x00400613#32], term := none }]
def axT_80004c78 : List BBlock := [⟨[], some (⟨0x80004c78#64, 0x16d67663#32, 0x63#8, 0x76#8, 0xd6#8, 0x16#8, .br bop.BGEU true, 12, 13, 0x16c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80004c78 : List BBlock := [⟨[], some (⟨0x80004c78#64, 0x16d67663#32, 0x63#8, 0x76#8, 0xd6#8, 0x16#8, .br bop.BGEU false, 12, 13, 0x16c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80004c7c : List BBlock := [{ body := [mkLine 0x80004c7c#64 0x01400613#32], term := none }]
def axT_80004c80 : List BBlock := [⟨[], some (⟨0x80004c80#64, 0x28d66e63#32, 0x63#8, 0x6e#8, 0xd6#8, 0x28#8, .br bop.BLTU true, 12, 13, 0x29c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80004c80 : List BBlock := [⟨[], some (⟨0x80004c80#64, 0x28d66e63#32, 0x63#8, 0x6e#8, 0xd6#8, 0x28#8, .br bop.BLTU false, 12, 13, 0x29c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80004c84 : List BBlock := [{ body := [mkLine 0x80004c84#64 0x00169513#32], term := none }]
def ax_80004c88 : List BBlock := [{ body := [mkLine 0x80004c88#64 0x0b85051b#32], term := none }]
def ax_80004c8c : List BBlock := [{ body := [mkLine 0x80004c8c#64 0x00351513#32], term := none }]
def ax_80004c90 : List BBlock := [{ body := [mkLine 0x80004c90#64 0x05b6861b#32], term := none }]
def ax_80004c94 : List BBlock := [{ body := [mkLine 0x80004c94#64 0x00a80533#32], term := none }]
def ax_80004c98 : List BBlock := [{ body := [mkLine 0x80004c98#64 0x00053683#32], term := none }]
def ax_80004c9c : List BBlock := [{ body := [mkLine 0x80004c9c#64 0xff050513#32], term := none }]
def axT_80004ca0 : List BBlock := [⟨[], some (⟨0x80004ca0#64, 0x00d51863#32, 0x63#8, 0x18#8, 0xd5#8, 0x00#8, .br bop.BNE true, 10, 13, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80004ca0 : List BBlock := [⟨[], some (⟨0x80004ca0#64, 0x00d51863#32, 0x63#8, 0x18#8, 0xd5#8, 0x00#8, .br bop.BNE false, 10, 13, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80004ca4 : List BBlock := [⟨[], some (⟨0x80004ca4#64, 0x1f40006f#32, 0x6f#8, 0x00#8, 0x40#8, 0x1f#8, .j, 0, 0, 0x0#13, 0x1f4#21, 0#12⟩ : TInstr)⟩]
def ax_80004ca8 : List BBlock := [{ body := [mkLine 0x80004ca8#64 0x0106b683#32], term := none }]
def axT_80004cac : List BBlock := [⟨[], some (⟨0x80004cac#64, 0x00d50863#32, 0x63#8, 0x08#8, 0xd5#8, 0x00#8, .br bop.BEQ true, 10, 13, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80004cac : List BBlock := [⟨[], some (⟨0x80004cac#64, 0x00d50863#32, 0x63#8, 0x08#8, 0xd5#8, 0x00#8, .br bop.BEQ false, 10, 13, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80004cb0 : List BBlock := [{ body := [mkLine 0x80004cb0#64 0x0086b603#32], term := none }]
def ax_80004cb4 : List BBlock := [{ body := [mkLine 0x80004cb4#64 0xffc67613#32], term := none }]
def axT_80004cb8 : List BBlock := [⟨[], some (⟨0x80004cb8#64, 0xfec368e3#32, 0xe3#8, 0x68#8, 0xc3#8, 0xfe#8, .br bop.BLTU true, 6, 12, 0x1ff0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80004cb8 : List BBlock := [⟨[], some (⟨0x80004cb8#64, 0xfec368e3#32, 0xe3#8, 0x68#8, 0xc3#8, 0xfe#8, .br bop.BLTU false, 6, 12, 0x1ff0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80004cbc : List BBlock := [{ body := [mkLine 0x80004cbc#64 0x0186b503#32], term := none }]
def ax_80004cc0 : List BBlock := [{ body := [mkLine 0x80004cc0#64 0x00a7bc23#32], term := none }]
def ax_80004cc4 : List BBlock := [{ body := [mkLine 0x80004cc4#64 0x00d7b823#32], term := none }]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem st_80004bc8 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hLDS : ∀ b ∈ accAddrs ((0x8001b510#64) + sign_extend (m := 64) (0x490#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004bcc#64 (upd R 15 (ldv .ld Mt ((0x8001b510#64) + sign_extend (m := 64) (0x490#12)).toNat)) Mt) :
    AW live S Q 0x80004bc8#64 R Mt :=
  swp_step ax_80004bc8 [3, 15] [bytesAt (imgM Mt) ((0x8001b510#64) + sign_extend (m := 64) (0x490#12)).toNat 8] (accAddrs ((0x8001b510#64) + sign_extend (m := 64) (0x490#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004bc8 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨(show LdOK ((0x8001b510#64) + sign_extend (m := 64) (0x490#12)).toNat 8 by decide), lpins8_img hLD⟩)
    (by decide) (by decide) (fun _ => rfl) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [3, 15])))) rfl hk

theorem st_80004bcc {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hT : (R 13).toNat ≤ (R 15).toNat → AW live S Q 0x80004bd4#64 R Mt) (hF : ¬ ((R 13).toNat ≤ (R 15).toNat) → AW live S Q 0x80004bd0#64 R Mt) :
    AW live S Q 0x80004bcc#64 R Mt := by
  by_cases hc : (R 13).toNat ≤ (R 15).toNat
  · exact
    swp_step axT_80004bcc [13, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axT_80004bcc ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_bgeu _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_step axF_80004bcc [13, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axF_80004bcc ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_false (guard_bgeu _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem st_80004bd0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hS : ∀ b ∈ accAddrs ((0x8001b510#64) + sign_extend (m := 64) (0x490#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004bd4#64 R (writeLog Mt [(((0x8001b510#64) + sign_extend (m := 64) (0x490#12)).toNat, 8, (R 13))])) :
    AW live S Q 0x80004bd0#64 R Mt :=
  swp_step ax_80004bd0 [3, 13] [] [] (accAddrs ((0x8001b510#64) + sign_extend (m := 64) (0x490#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80004bd0 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (show StOK ((0x8001b510#64) + sign_extend (m := 64) (0x490#12)).toNat 8 by decide))
    (by decide) (by decide) (fun _ => rfl) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004bd4 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hLDS : ∀ b ∈ accAddrs ((0x8001b510#64) + sign_extend (m := 64) (0x488#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004bd8#64 (upd R 15 (ldv .ld Mt ((0x8001b510#64) + sign_extend (m := 64) (0x488#12)).toNat)) Mt) :
    AW live S Q 0x80004bd4#64 R Mt :=
  swp_step ax_80004bd4 [3, 15] [bytesAt (imgM Mt) ((0x8001b510#64) + sign_extend (m := 64) (0x488#12)).toNat 8] (accAddrs ((0x8001b510#64) + sign_extend (m := 64) (0x488#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004bd4 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨(show LdOK ((0x8001b510#64) + sign_extend (m := 64) (0x488#12)).toNat 8 by decide), lpins8_img hLD⟩)
    (by decide) (by decide) (fun _ => rfl) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [3, 15])))) rfl hk

theorem st_80004bd8 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hT : (R 13).toNat ≤ (R 15).toNat → AW live S Q 0x80004be0#64 R Mt) (hF : ¬ ((R 13).toNat ≤ (R 15).toNat) → AW live S Q 0x80004bdc#64 R Mt) :
    AW live S Q 0x80004bd8#64 R Mt := by
  by_cases hc : (R 13).toNat ≤ (R 15).toNat
  · exact
    swp_step axT_80004bd8 [13, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axT_80004bd8 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_bgeu _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_step axF_80004bd8 [13, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axF_80004bd8 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_false (guard_bgeu _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem st_80004bdc {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hS : ∀ b ∈ accAddrs ((0x8001b510#64) + sign_extend (m := 64) (0x488#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004be0#64 R (writeLog Mt [(((0x8001b510#64) + sign_extend (m := 64) (0x488#12)).toNat, 8, (R 13))])) :
    AW live S Q 0x80004bdc#64 R Mt :=
  swp_step ax_80004bdc [3, 13] [] [] (accAddrs ((0x8001b510#64) + sign_extend (m := 64) (0x488#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80004bdc ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (show StOK ((0x8001b510#64) + sign_extend (m := 64) (0x488#12)).toNat 8 by decide))
    (by decide) (by decide) (fun _ => rfl) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004be0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004be4#64 (upd R 15 ((R 28) + sign_extend (m := 64) (0x000#12))) Mt) :
    AW live S Q 0x80004be0#64 R Mt :=
  swp_step ax_80004be0 [15, 28] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004be0 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15, 28])))) rfl hk

theorem st_80004be4 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004e08#64 R Mt) :
    AW live S Q 0x80004be4#64 R Mt :=
  swp_step ax_80004be4 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004be4 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => nomatch h) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004be8 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 16) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 16) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004bec#64 (upd R 11 (ldv .ld Mt ((R 16) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    AW live S Q 0x80004be8#64 R Mt :=
  swp_step ax_80004be8 [11, 16] [bytesAt (imgM Mt) ((R 16) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 16) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004be8 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11, 16])))) rfl hk

theorem st_80004bec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004968#64 R Mt) :
    AW live S Q 0x80004bec#64 R Mt :=
  swp_step ax_80004bec [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004bec ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => nomatch h) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004bf0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004bf4#64 (upd R 12 ((R 14) ||| sign_extend (m := 64) (0x001#12))) Mt) :
    AW live S Q 0x80004bf0#64 R Mt :=
  swp_step ax_80004bf0 [12, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004bf0 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 14])))) rfl hk

theorem st_80004bf4 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 15) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 15) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004bf8#64 R (writeLog Mt [(((R 15) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 12))])) :
    AW live S Q 0x80004bf4#64 R Mt :=
  swp_step ax_80004bf4 [12, 15] [] [] (accAddrs ((R 15) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80004bf4 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004bf8 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004bfc#64 (upd R 14 ((R 15) + (R 14))) Mt) :
    AW live S Q 0x80004bf8#64 R Mt :=
  swp_step ax_80004bf8 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004bf8 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 15])))) rfl hk

theorem st_80004bfc {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c00#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 15))])) :
    AW live S Q 0x80004bfc#64 R Mt :=
  swp_step ax_80004bfc [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80004bfc ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004c00 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c04#64 (upd R 13 ((R 13) ||| sign_extend (m := 64) (0x001#12))) Mt) :
    AW live S Q 0x80004c00#64 R Mt :=
  swp_step ax_80004c00 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c00 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13])))) rfl hk

theorem st_80004c04 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 16) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 16) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c08#64 R (writeLog Mt [(((R 16) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 14))])) :
    AW live S Q 0x80004c04#64 R Mt :=
  swp_step ax_80004c04 [14, 16] [] [] (accAddrs ((R 16) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80004c04 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004c08 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c0c#64 (upd R 10 ((R 8) + sign_extend (m := 64) (0x000#12))) Mt) :
    AW live S Q 0x80004c08#64 R Mt :=
  swp_step ax_80004c08 [8, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c08 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [8, 10])))) rfl hk

theorem st_80004c0c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 14) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c10#64 R (writeLog Mt [(((R 14) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 13))])) :
    AW live S Q 0x80004c0c#64 R Mt :=
  swp_step ax_80004c0c [13, 14] [] [] (accAddrs ((R 14) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80004c0c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_80004c10 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80004c10 [0xef#8, 0x00#8, 0x00#8, 0x46#8], live p.1) :
    JalExec (vsaModel live) 0x80004c10 [0xef#8, 0x00#8, 0x00#8, 0x46#8] 0x80005070#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x80004c10, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x80004c11, .discard, 0x00#8) (by simp [codeFoot])
  have hb2 := hb (0x80004c12, .discard, 0x00#8) (by simp [codeFoot])
  have hb3 := hb (0x80004c13, .discard, 0x46#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x80004c10#64) vm (0x460000ef#32) (0x000460#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80004c10#64) 4)
      (0xef#8) (0x00#8) (0x00#8) (0x46#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_460000ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80004c10#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80005070#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x80004c10#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x80004c10 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem st_80004c10 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80005070#64 (upd R VsaIris.ra (BitVec.ofNat 64 (0x80004c10 + 4))) Mt) :
    AW live S Q 0x80004c10#64 R Mt :=
  swp_jal 0x80004c10 [0xef#8, 0x00#8, 0x00#8, 0x46#8] 0x80005070#64
    (jalx_80004c10 live fun p hp => hlive _ (alloc_code_80004c10 p hp)) alloc_code_80004c10
    (by decide) (by decide) rfl hk

theorem st_80004c14 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c18#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    AW live S Q 0x80004c14#64 R Mt :=
  swp_step ax_80004c14 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c14 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem st_80004c18 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c1c#64 (upd R 10 ((R 15) + sign_extend (m := 64) (0x010#12))) Mt) :
    AW live S Q 0x80004c18#64 R Mt :=
  swp_step ax_80004c18 [10, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c18 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 15])))) rfl hk

theorem st_80004c1c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004830#64 R Mt) :
    AW live S Q 0x80004c1c#64 R Mt :=
  swp_step ax_80004c1c [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c1c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => nomatch h) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004c20 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c24#64 (upd R 12 (ldv .ld Mt ((R 15) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    AW live S Q 0x80004c20#64 R Mt :=
  swp_step ax_80004c20 [12, 15] [bytesAt (imgM Mt) ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c20 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 15])))) rfl hk

theorem st_80004c24 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c28#64 (upd R 13 ((R 15) + (R 13))) Mt) :
    AW live S Q 0x80004c24#64 R Mt :=
  swp_step ax_80004c24 [13, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c24 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13, 15])))) rfl hk

theorem st_80004c28 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 13) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 13) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c2c#64 (upd R 14 (ldv .ld Mt ((R 13) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    AW live S Q 0x80004c28#64 R Mt :=
  swp_step ax_80004c28 [13, 14] [bytesAt (imgM Mt) ((R 13) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 13) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c28 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [13, 14])))) rfl hk

theorem st_80004c2c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 12) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 12) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c30#64 R (writeLog Mt [(((R 12) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 11))])) :
    AW live S Q 0x80004c2c#64 R Mt :=
  swp_step ax_80004c2c [11, 12] [] [] (accAddrs ((R 12) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80004c2c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004c30 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c34#64 R (writeLog Mt [(((R 11) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 12))])) :
    AW live S Q 0x80004c30#64 R Mt :=
  swp_step ax_80004c30 [11, 12] [] [] (accAddrs ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80004c30 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004c34 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c38#64 (upd R 14 ((R 14) ||| sign_extend (m := 64) (0x001#12))) Mt) :
    AW live S Q 0x80004c34#64 R Mt :=
  swp_step ax_80004c34 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c34 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem st_80004c38 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c3c#64 (upd R 10 ((R 8) + sign_extend (m := 64) (0x000#12))) Mt) :
    AW live S Q 0x80004c38#64 R Mt :=
  swp_step ax_80004c38 [8, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c38 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [8, 10])))) rfl hk

theorem st_80004c3c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 13) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 13) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c40#64 R (writeLog Mt [(((R 13) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 14))])) :
    AW live S Q 0x80004c3c#64 R Mt :=
  swp_step ax_80004c3c [13, 14] [] [] (accAddrs ((R 13) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80004c3c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004c40 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c44#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 15))])) :
    AW live S Q 0x80004c40#64 R Mt :=
  swp_step ax_80004c40 [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80004c40 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_80004c44 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80004c44 [0xef#8, 0x00#8, 0xc0#8, 0x42#8], live p.1) :
    JalExec (vsaModel live) 0x80004c44 [0xef#8, 0x00#8, 0xc0#8, 0x42#8] 0x80005070#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x80004c44, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x80004c45, .discard, 0x00#8) (by simp [codeFoot])
  have hb2 := hb (0x80004c46, .discard, 0xc0#8) (by simp [codeFoot])
  have hb3 := hb (0x80004c47, .discard, 0x42#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x80004c44#64) vm (0x42c000ef#32) (0x00042c#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80004c44#64) 4)
      (0xef#8) (0x00#8) (0xc0#8) (0x42#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_42c000ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80004c44#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80005070#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x80004c44#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x80004c44 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem st_80004c44 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80005070#64 (upd R VsaIris.ra (BitVec.ofNat 64 (0x80004c44 + 4))) Mt) :
    AW live S Q 0x80004c44#64 R Mt :=
  swp_jal 0x80004c44 [0xef#8, 0x00#8, 0xc0#8, 0x42#8] 0x80005070#64
    (jalx_80004c44 live fun p hp => hlive _ (alloc_code_80004c44 p hp)) alloc_code_80004c44
    (by decide) (by decide) rfl hk

theorem st_80004c48 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c4c#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    AW live S Q 0x80004c48#64 R Mt :=
  swp_step ax_80004c48 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c48 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem st_80004c4c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c50#64 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x058#12)).toNat)) Mt) :
    AW live S Q 0x80004c4c#64 R Mt :=
  swp_step ax_80004c4c [1, 2] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c4c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 1 ∈ [1, 2])))) rfl hk

theorem st_80004c50 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c54#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x050#12)).toNat)) Mt) :
    AW live S Q 0x80004c50#64 R Mt :=
  swp_step ax_80004c50 [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c50 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem st_80004c54 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c58#64 (upd R 10 ((R 15) + sign_extend (m := 64) (0x010#12))) Mt) :
    AW live S Q 0x80004c54#64 R Mt :=
  swp_step ax_80004c54 [10, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c54 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 15])))) rfl hk

theorem st_80004c58 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c5c#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0x060#12))) Mt) :
    AW live S Q 0x80004c58#64 R Mt :=
  swp_step ax_80004c58 [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c58 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem st_80004c5c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : AW live S Q (R 1) R Mt) :
    AW live S Q 0x80004c5c#64 R Mt :=
  swp_step ax_80004c5c [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c5c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004c60 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 13) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 13) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c64#64 (upd R 15 (ldv .ld Mt ((R 13) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    AW live S Q 0x80004c60#64 R Mt :=
  swp_step ax_80004c60 [13, 15] [bytesAt (imgM Mt) ((R 13) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 13) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c60 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [13, 15])))) rfl hk

theorem st_80004c64 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c68#64 (upd R 17 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 17) + sign_extend (m := 64) (0x002#12)) 31 0))) Mt) :
    AW live S Q 0x80004c64#64 R Mt :=
  swp_step ax_80004c64 [17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c64 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 17 ∈ [17])))) rfl hk

theorem st_80004c68 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hT : (R 13) = (R 15) → AW live S Q 0x800048ec#64 R Mt) (hF : ¬ ((R 13) = (R 15)) → AW live S Q 0x80004c6c#64 R Mt) :
    AW live S Q 0x80004c68#64 R Mt := by
  by_cases hc : (R 13) = (R 15)
  · exact
    swp_step axT_80004c68 [13, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axT_80004c68 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_step axF_80004c68 [13, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axF_80004c68 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem st_80004c70 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c74#64 (upd R 13 (shift_bits_right (R 6) (Sail.BitVec.extractLsb (0x09#6) 5 0))) Mt) :
    AW live S Q 0x80004c70#64 R Mt :=
  swp_step ax_80004c70 [6, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c70 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [6, 13])))) rfl hk

theorem st_80004c74 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c78#64 (upd R 12 ((0#64) + sign_extend (m := 64) (0x004#12))) Mt) :
    AW live S Q 0x80004c74#64 R Mt :=
  swp_step ax_80004c74 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c74 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12])))) rfl hk

theorem st_80004c78 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hT : (R 13).toNat ≤ (R 12).toNat → AW live S Q 0x80004de4#64 R Mt) (hF : ¬ ((R 13).toNat ≤ (R 12).toNat) → AW live S Q 0x80004c7c#64 R Mt) :
    AW live S Q 0x80004c78#64 R Mt := by
  by_cases hc : (R 13).toNat ≤ (R 12).toNat
  · exact
    swp_step axT_80004c78 [12, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axT_80004c78 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_bgeu _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_step axF_80004c78 [12, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axF_80004c78 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_false (guard_bgeu _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem st_80004c7c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c80#64 (upd R 12 ((0#64) + sign_extend (m := 64) (0x014#12))) Mt) :
    AW live S Q 0x80004c7c#64 R Mt :=
  swp_step ax_80004c7c [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c7c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12])))) rfl hk

theorem st_80004c80 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hT : (R 12).toNat < (R 13).toNat → AW live S Q 0x80004f1c#64 R Mt) (hF : ¬ ((R 12).toNat < (R 13).toNat) → AW live S Q 0x80004c84#64 R Mt) :
    AW live S Q 0x80004c80#64 R Mt := by
  by_cases hc : (R 12).toNat < (R 13).toNat
  · exact
    swp_step axT_80004c80 [12, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axT_80004c80 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_bltu _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_step axF_80004c80 [12, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axF_80004c80 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_false (guard_bltu _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem st_80004c84 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c88#64 (upd R 10 (shift_bits_left (R 13) (Sail.BitVec.extractLsb (0x01#6) 5 0))) Mt) :
    AW live S Q 0x80004c84#64 R Mt :=
  swp_step ax_80004c84 [10, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c84 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 13])))) rfl hk

theorem st_80004c88 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c8c#64 (upd R 10 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 10) + sign_extend (m := 64) (0x0b8#12)) 31 0))) Mt) :
    AW live S Q 0x80004c88#64 R Mt :=
  swp_step ax_80004c88 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c88 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem st_80004c8c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c90#64 (upd R 10 (shift_bits_left (R 10) (Sail.BitVec.extractLsb (0x03#6) 5 0))) Mt) :
    AW live S Q 0x80004c8c#64 R Mt :=
  swp_step ax_80004c8c [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c8c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem st_80004c90 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c94#64 (upd R 12 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 13) + sign_extend (m := 64) (0x05b#12)) 31 0))) Mt) :
    AW live S Q 0x80004c90#64 R Mt :=
  swp_step ax_80004c90 [12, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c90 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 13])))) rfl hk

theorem st_80004c94 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004c98#64 (upd R 10 ((R 16) + (R 10))) Mt) :
    AW live S Q 0x80004c94#64 R Mt :=
  swp_step ax_80004c94 [10, 16] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c94 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 16])))) rfl hk

theorem st_80004c98 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 10) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 10) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004c9c#64 (upd R 13 (ldv .ld Mt ((R 10) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    AW live S Q 0x80004c98#64 R Mt :=
  swp_step ax_80004c98 [10, 13] [bytesAt (imgM Mt) ((R 10) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 10) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c98 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [10, 13])))) rfl hk

theorem st_80004c9c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004ca0#64 (upd R 10 ((R 10) + sign_extend (m := 64) (0xff0#12))) Mt) :
    AW live S Q 0x80004c9c#64 R Mt :=
  swp_step ax_80004c9c [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004c9c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem st_80004ca0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hT : (R 10) ≠ (R 13) → AW live S Q 0x80004cb0#64 R Mt) (hF : ¬ ((R 10) ≠ (R 13)) → AW live S Q 0x80004ca4#64 R Mt) :
    AW live S Q 0x80004ca0#64 R Mt := by
  by_cases hc : (R 10) ≠ (R 13)
  · exact
    swp_step axT_80004ca0 [10, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axT_80004ca0 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_step axF_80004ca0 [10, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axF_80004ca0 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem st_80004ca4 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004e98#64 R Mt) :
    AW live S Q 0x80004ca4#64 R Mt :=
  swp_step ax_80004ca4 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004ca4 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => nomatch h) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004ca8 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 13) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 13) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004cac#64 (upd R 13 (ldv .ld Mt ((R 13) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    AW live S Q 0x80004ca8#64 R Mt :=
  swp_step ax_80004ca8 [13] [bytesAt (imgM Mt) ((R 13) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 13) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004ca8 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13])))) rfl hk

theorem st_80004cac {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hT : (R 10) = (R 13) → AW live S Q 0x80004cbc#64 R Mt) (hF : ¬ ((R 10) = (R 13)) → AW live S Q 0x80004cb0#64 R Mt) :
    AW live S Q 0x80004cac#64 R Mt := by
  by_cases hc : (R 10) = (R 13)
  · exact
    swp_step axT_80004cac [10, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axT_80004cac ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_step axF_80004cac [10, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axF_80004cac ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem st_80004cb0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 13) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 13) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004cb4#64 (upd R 12 (ldv .ld Mt ((R 13) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    AW live S Q 0x80004cb0#64 R Mt :=
  swp_step ax_80004cb0 [12, 13] [bytesAt (imgM Mt) ((R 13) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 13) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004cb0 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 13])))) rfl hk

theorem st_80004cb4 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80004cb8#64 (upd R 12 ((R 12) &&& sign_extend (m := 64) (0xffc#12))) Mt) :
    AW live S Q 0x80004cb4#64 R Mt :=
  swp_step ax_80004cb4 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004cb4 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12])))) rfl hk

theorem st_80004cb8 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hT : (R 6).toNat < (R 12).toNat → AW live S Q 0x80004ca8#64 R Mt) (hF : ¬ ((R 6).toNat < (R 12).toNat) → AW live S Q 0x80004cbc#64 R Mt) :
    AW live S Q 0x80004cb8#64 R Mt := by
  by_cases hc : (R 6).toNat < (R 12).toNat
  · exact
    swp_step axT_80004cb8 [6, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axT_80004cb8 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_bltu _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_step axF_80004cb8 [6, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axF_80004cb8 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_false (guard_bltu _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem st_80004cbc {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 13) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 13) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004cc0#64 (upd R 10 (ldv .ld Mt ((R 13) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    AW live S Q 0x80004cbc#64 R Mt :=
  swp_step ax_80004cbc [10, 13] [bytesAt (imgM Mt) ((R 13) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 13) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80004cbc ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 13])))) rfl hk

theorem st_80004cc0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 15) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 15) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004cc4#64 R (writeLog Mt [(((R 15) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 10))])) :
    AW live S Q 0x80004cc0#64 R Mt :=
  swp_step ax_80004cc0 [10, 15] [] [] (accAddrs ((R 15) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80004cc0 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80004cc4 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : AW live S Q 0x80004cc8#64 R (writeLog Mt [(((R 15) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 13))])) :
    AW live S Q 0x80004cc4#64 R Mt :=
  swp_step ax_80004cc4 [13, 15] [] [] (accAddrs ((R 15) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80004cc4 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
