import VsaIris.Interp.IRun
import VsaIris.Vsa.SymObs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ixT_80004268 : List BBlock := [⟨[], some (⟨0x80004268#64, 0x06061a63#32, 0x63#8, 0x1a#8, 0x06#8, 0x06#8, .br bop.BNE true, 12, 0, 0x74#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_80004268 : List BBlock := [⟨[], some (⟨0x80004268#64, 0x06061a63#32, 0x63#8, 0x1a#8, 0x06#8, 0x06#8, .br bop.BNE false, 12, 0, 0x74#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000426c : List BBlock := [{ body := [mkLine 0x8000426c#64 0x01043603#32], term := none }]
def ixT_80004270 : List BBlock := [⟨[], some (⟨0x80004270#64, 0x02060c63#32, 0x63#8, 0x0c#8, 0x06#8, 0x02#8, .br bop.BEQ true, 12, 0, 0x38#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_80004270 : List BBlock := [⟨[], some (⟨0x80004270#64, 0x02060c63#32, 0x63#8, 0x0c#8, 0x06#8, 0x02#8, .br bop.BEQ false, 12, 0, 0x38#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_80004274 : List BBlock := [{ body := [mkLine 0x80004274#64 0x00098693#32], term := none }]
def ix_80004278 : List BBlock := [{ body := [mkLine 0x80004278#64 0x06810513#32], term := none }]
def ix_8000427c : List BBlock := [{ body := [mkLine 0x8000427c#64 0x00048593#32], term := none }]
def ix_80004284 : List BBlock := [{ body := [mkLine 0x80004284#64 0x06813683#32], term := none }]
def ix_80004288 : List BBlock := [{ body := [mkLine 0x80004288#64 0x07013703#32], term := none }]
def ix_8000428c : List BBlock := [{ body := [mkLine 0x8000428c#64 0x07813783#32], term := none }]
def ix_80004290 : List BBlock := [{ body := [mkLine 0x80004290#64 0x01010513#32], term := none }]
def ix_80004294 : List BBlock := [{ body := [mkLine 0x80004294#64 0x00d13823#32], term := none }]
def ix_80004298 : List BBlock := [{ body := [mkLine 0x80004298#64 0x00e13c23#32], term := none }]
def ix_8000429c : List BBlock := [{ body := [mkLine 0x8000429c#64 0x02f13023#32], term := none }]
def ixT_800042a4 : List BBlock := [⟨[], some (⟨0x800042a4#64, 0xde0506e3#32, 0xe3#8, 0x06#8, 0x05#8, 0xde#8, .br bop.BEQ true, 10, 0, 0x1dec#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_800042a4 : List BBlock := [⟨[], some (⟨0x800042a4#64, 0xde0506e3#32, 0xe3#8, 0x06#8, 0x05#8, 0xde#8, .br bop.BEQ false, 10, 0, 0x1dec#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_800042a8 : List BBlock := [{ body := [mkLine 0x800042a8#64 0x02043583#32], term := none }]
def ix_800042ac : List BBlock := [{ body := [mkLine 0x800042ac#64 0x00090693#32], term := none }]
def ix_800042b0 : List BBlock := [{ body := [mkLine 0x800042b0#64 0x00098613#32], term := none }]
def ix_800042b4 : List BBlock := [{ body := [mkLine 0x800042b4#64 0x00048513#32], term := none }]
def ix_800042bc : List BBlock := [{ body := [mkLine 0x800042bc#64 0x00100793#32], term := none }]
def ixT_800042c0 : List BBlock := [⟨[], some (⟨0x800042c0#64, 0xf8f51ee3#32, 0xe3#8, 0x1e#8, 0xf5#8, 0xf8#8, .br bop.BNE true, 10, 15, 0x1f9c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_800042c0 : List BBlock := [⟨[], some (⟨0x800042c0#64, 0xf8f51ee3#32, 0xe3#8, 0x1e#8, 0xf5#8, 0xf8#8, .br bop.BNE false, 10, 15, 0x1f9c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_800042c4 : List BBlock := [{ body := [mkLine 0x800042c4#64 0x00000513#32], term := none }]
def ix_800042c8 : List BBlock := [⟨[], some (⟨0x800042c8#64, 0xdd5ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xdd#8, .j, 0, 0, 0x0#13, 0x1ffdd4#21, 0#12⟩ : TInstr)⟩]
def ix_800042cc : List BBlock := [{ body := [mkLine 0x800042cc#64 0x01843403#32], term := none }]
def ixT_800042d0 : List BBlock := [⟨[], some (⟨0x800042d0#64, 0xd40412e3#32, 0xe3#8, 0x12#8, 0x04#8, 0xd4#8, .br bop.BNE true, 8, 0, 0x1d44#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_800042d0 : List BBlock := [⟨[], some (⟨0x800042d0#64, 0xd40412e3#32, 0xe3#8, 0x12#8, 0x04#8, 0xd4#8, .br bop.BNE false, 8, 0, 0x1d44#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_800042d4 : List BBlock := [{ body := [mkLine 0x800042d4#64 0x00000513#32], term := none }]
def ix_800042d8 : List BBlock := [⟨[], some (⟨0x800042d8#64, 0xdc5ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xdc#8, .j, 0, 0, 0x0#13, 0x1ffdc4#21, 0#12⟩ : TInstr)⟩]
def ix_800042dc : List BBlock := [{ body := [mkLine 0x800042dc#64 0x00098693#32], term := none }]
def ix_800042e0 : List BBlock := [{ body := [mkLine 0x800042e0#64 0x00048593#32], term := none }]
def ix_800042e4 : List BBlock := [{ body := [mkLine 0x800042e4#64 0x01010513#32], term := none }]
def ix_800042ec : List BBlock := [⟨[], some (⟨0x800042ec#64, 0xf81ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0xf8#8, .j, 0, 0, 0x0#13, 0x1fff80#21, 0#12⟩ : TInstr)⟩]
def ix_800042f0 : List BBlock := [{ body := [mkLine 0x800042f0#64 0x01010513#32], term := none }]
def ix_800042f8 : List BBlock := [⟨[], some (⟨0x800042f8#64, 0xe41ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0xe4#8, .j, 0, 0, 0x0#13, 0x1ffe40#21, 0#12⟩ : TInstr)⟩]
def ix_800042fc : List BBlock := [{ body := [mkLine 0x800042fc#64 0x06810513#32], term := none }]
def ix_80004304 : List BBlock := [⟨[], some (⟨0x80004304#64, 0xdedff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xde#8, .j, 0, 0, 0x0#13, 0x1ffdec#21, 0#12⟩ : TInstr)⟩]
def ix_800043ec : List BBlock := [{ body := [mkLine 0x800043ec#64 0xf5010113#32], term := none }]
def ix_800043f0 : List BBlock := [{ body := [mkLine 0x800043f0#64 0x00a13023#32], term := none }]
def ix_800043f4 : List BBlock := [{ body := [mkLine 0x800043f4#64 0x01050513#32], term := none }]
def ix_800043f8 : List BBlock := [{ body := [mkLine 0x800043f8#64 0x0a113423#32], term := none }]
def ix_800043fc : List BBlock := [{ body := [mkLine 0x800043fc#64 0x0a813023#32], term := none }]
def ix_80004400 : List BBlock := [{ body := [mkLine 0x80004400#64 0x08913c23#32], term := none }]
def ix_80004404 : List BBlock := [{ body := [mkLine 0x80004404#64 0x09213823#32], term := none }]
def ix_80004408 : List BBlock := [{ body := [mkLine 0x80004408#64 0x09313423#32], term := none }]
def ix_8000440c : List BBlock := [{ body := [mkLine 0x8000440c#64 0x09413023#32], term := none }]
def ix_80004410 : List BBlock := [{ body := [mkLine 0x80004410#64 0x07513c23#32], term := none }]
def ix_80004414 : List BBlock := [{ body := [mkLine 0x80004414#64 0x07613823#32], term := none }]
def ix_80004418 : List BBlock := [{ body := [mkLine 0x80004418#64 0x00b13c23#32], term := none }]
def ix_8000441c : List BBlock := [{ body := [mkLine 0x8000441c#64 0x00c13823#32], term := none }]
def ix_80004420 : List BBlock := [{ body := [mkLine 0x80004420#64 0x00d13423#32], term := none }]
def ixT_80004428 : List BBlock := [⟨[], some (⟨0x80004428#64, 0x0e051063#32, 0x63#8, 0x10#8, 0x05#8, 0x0e#8, .br bop.BNE true, 10, 0, 0xe0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_80004428 : List BBlock := [⟨[], some (⟨0x80004428#64, 0x0e051063#32, 0x63#8, 0x10#8, 0x05#8, 0x0e#8, .br bop.BNE false, 10, 0, 0xe0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000442c : List BBlock := [{ body := [mkLine 0x8000442c#64 0x01013783#32], term := none }]
def ix_80004430 : List BBlock := [{ body := [mkLine 0x80004430#64 0x00050a93#32], term := none }]
def ixT_80004434 : List BBlock := [⟨[], some (⟨0x80004434#64, 0x0ef05063#32, 0x63#8, 0x50#8, 0xf0#8, 0x0e#8, .br bop.BGE true, 0, 15, 0xe0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_80004434 : List BBlock := [⟨[], some (⟨0x80004434#64, 0x0ef05063#32, 0x63#8, 0x50#8, 0xf0#8, 0x0e#8, .br bop.BGE false, 0, 15, 0xe0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_80004438 : List BBlock := [{ body := [mkLine 0x80004438#64 0x01013783#32], term := none }]
def ix_8000443c : List BBlock := [{ body := [mkLine 0x8000443c#64 0x01813403#32], term := none }]
def ix_80004440 : List BBlock := [{ body := [mkLine 0x80004440#64 0x46018b13#32], term := none }]
def ix_80004444 : List BBlock := [{ body := [mkLine 0x80004444#64 0x00379913#32], term := none }]
def ix_80004448 : List BBlock := [{ body := [mkLine 0x80004448#64 0x01240933#32], term := none }]
def ix_8000444c : List BBlock := [{ body := [mkLine 0x8000444c#64 0x00300993#32], term := none }]
def ix_80004450 : List BBlock := [{ body := [mkLine 0x80004450#64 0x00100a13#32], term := none }]
def ix_80004454 : List BBlock := [⟨[], some (⟨0x80004454#64, 0x0380006f#32, 0x6f#8, 0x00#8, 0x80#8, 0x03#8, .j, 0, 0, 0x0#13, 0x38#21, 0#12⟩ : TInstr)⟩]
def ix_80004458 : List BBlock := [{ body := [mkLine 0x80004458#64 0x05810513#32], term := none }]
def ix_80004460 : List BBlock := [{ body := [mkLine 0x80004460#64 0x00013783#32], term := none }]
def ix_80004464 : List BBlock := [{ body := [mkLine 0x80004464#64 0x05810693#32], term := none }]
def ix_80004468 : List BBlock := [{ body := [mkLine 0x80004468#64 0x00048593#32], term := none }]
def ix_8000446c : List BBlock := [{ body := [mkLine 0x8000446c#64 0x0007b603#32], term := none }]
def ix_80004470 : List BBlock := [{ body := [mkLine 0x80004470#64 0x00078513#32], term := none }]
def ixT_80004478 : List BBlock := [⟨[], some (⟨0x80004478#64, 0x0d350463#32, 0x63#8, 0x04#8, 0x35#8, 0x0d#8, .br bop.BEQ true, 10, 19, 0xc8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_80004478 : List BBlock := [⟨[], some (⟨0x80004478#64, 0x0d350463#32, 0x63#8, 0x04#8, 0x35#8, 0x0d#8, .br bop.BEQ false, 10, 19, 0xc8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000447c : List BBlock := [{ body := [mkLine 0x8000447c#64 0xfff5051b#32], term := none }]
def ixT_80004480 : List BBlock := [⟨[], some (⟨0x80004480#64, 0x0eaa7263#32, 0x63#8, 0x72#8, 0xaa#8, 0x0e#8, .br bop.BGEU true, 20, 10, 0xe4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_80004480 : List BBlock := [⟨[], some (⟨0x80004480#64, 0x0eaa7263#32, 0x63#8, 0x72#8, 0xaa#8, 0x0e#8, .br bop.BGEU false, 20, 10, 0xe4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_80004484 : List BBlock := [{ body := [mkLine 0x80004484#64 0x00840413#32], term := none }]
def ixT_80004488 : List BBlock := [⟨[], some (⟨0x80004488#64, 0x09240663#32, 0x63#8, 0x06#8, 0x24#8, 0x09#8, .br bop.BEQ true, 8, 18, 0x8c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_80004488 : List BBlock := [⟨[], some (⟨0x80004488#64, 0x09240663#32, 0x63#8, 0x06#8, 0x24#8, 0x09#8, .br bop.BEQ false, 8, 18, 0x8c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000448c : List BBlock := [{ body := [mkLine 0x8000448c#64 0x00813783#32], term := none }]
def ix_80004490 : List BBlock := [{ body := [mkLine 0x80004490#64 0x00043483#32], term := none }]
def ixT_80004494 : List BBlock := [⟨[], some (⟨0x80004494#64, 0xfc0782e3#32, 0xe3#8, 0x82#8, 0x07#8, 0xfc#8, .br bop.BEQ true, 15, 0, 0x1fc4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_80004494 : List BBlock := [⟨[], some (⟨0x80004494#64, 0xfc0782e3#32, 0xe3#8, 0x82#8, 0x07#8, 0xfc#8, .br bop.BEQ false, 15, 0, 0x1fc4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_80004508 : List BBlock := [{ body := [mkLine 0x80004508#64 0x00013783#32], term := none }]
def ix_8000450c : List BBlock := [{ body := [mkLine 0x8000450c#64 0x00100a93#32], term := none }]
def ix_80004510 : List BBlock := [{ body := [mkLine 0x80004510#64 0x0007a423#32], term := none }]
def ix_80004514 : List BBlock := [{ body := [mkLine 0x80004514#64 0x0a813083#32], term := none }]
def ix_80004518 : List BBlock := [{ body := [mkLine 0x80004518#64 0x0a013403#32], term := none }]
def ix_8000451c : List BBlock := [{ body := [mkLine 0x8000451c#64 0x09813483#32], term := none }]
def ix_80004520 : List BBlock := [{ body := [mkLine 0x80004520#64 0x09013903#32], term := none }]
def ix_80004524 : List BBlock := [{ body := [mkLine 0x80004524#64 0x08813983#32], term := none }]
def ix_80004528 : List BBlock := [{ body := [mkLine 0x80004528#64 0x08013a03#32], term := none }]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_80004268 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hT : (R 12) ≠ (0#64) → IW live Dt DA S Q 0x800042dc#64 R Mt) (hF : ¬ ((R 12) ≠ (0#64)) → IW live Dt DA S Q 0x8000426c#64 R Mt) :
    IW live Dt DA S Q 0x80004268#64 R Mt := by
  by_cases hc : (R 12) ≠ (0#64)
  · exact
    swp_stepD ixT_80004268 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_80004268 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_80004268 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_80004268 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem itD_8000426c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDD : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 8, b ∈ DA)
    (hk : IW live Dt DA S Q 0x80004270#64 (upd R 12 (ldv .ld Dt ((R 8) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x8000426c#64 R Mt :=
  swp_stepD ix_8000426c [8, 12] [bytesAt (imgM Dt) ((R 8) + sign_extend (m := 64) (0x010#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000426c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img (fun b hb => dataReads_view hD b (hLDD b hb))⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [8, 12])))) rfl hk

theorem it_80004270 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hT : (R 12) = (0#64) → IW live Dt DA S Q 0x800042a8#64 R Mt) (hF : ¬ ((R 12) = (0#64)) → IW live Dt DA S Q 0x80004274#64 R Mt) :
    IW live Dt DA S Q 0x80004270#64 R Mt := by
  by_cases hc : (R 12) = (0#64)
  · exact
    swp_stepD ixT_80004270 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_80004270 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_80004270 [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_80004270 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_80004274 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004278#64 (upd R 13 ((R 19) + sign_extend (m := 64) (0x000#12))) Mt) :
    IW live Dt DA S Q 0x80004274#64 R Mt :=
  swp_stepD ix_80004274 [13, 19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004274 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13, 19])))) rfl hk

theorem it_80004278 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x8000427c#64 (upd R 10 ((R 2) + sign_extend (m := 64) (0x068#12))) Mt) :
    IW live Dt DA S Q 0x80004278#64 R Mt :=
  swp_stepD ix_80004278 [2, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004278 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [2, 10])))) rfl hk

theorem it_8000427c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004280#64 (upd R 11 ((R 9) + sign_extend (m := 64) (0x000#12))) Mt) :
    IW live Dt DA S Q 0x8000427c#64 R Mt :=
  swp_stepD ix_8000427c [9, 11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000427c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [9, 11])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_80004280 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80004280 [0xef#8, 0xe0#8, 0x5f#8, 0xee#8], live p.1) :
    JalExec (vsaModel live) 0x80004280 [0xef#8, 0xe0#8, 0x5f#8, 0xee#8] 0x80003164#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x80004280, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x80004281, .discard, 0xe0#8) (by simp [codeFoot])
  have hb2 := hb (0x80004282, .discard, 0x5f#8) (by simp [codeFoot])
  have hb3 := hb (0x80004283, .discard, 0xee#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x80004280#64) vm (0xee5fe0ef#32) (0x1feee4#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80004280#64) 4)
      (0xef#8) (0xe0#8) (0x5f#8) (0xee#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_ee5fe0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80004280#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80003164#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x80004280#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x80004280 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_80004284 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004288#64 (upd R 13 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x068#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x80004284#64 R Mt :=
  swp_stepD ix_80004284 [2, 13] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x068#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004284 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [2, 13])))) rfl hk

theorem it_80004288 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x8000428c#64 (upd R 14 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x070#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x80004288#64 R Mt :=
  swp_stepD ix_80004288 [2, 14] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004288 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [2, 14])))) rfl hk

theorem it_8000428c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004290#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x078#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x8000428c#64 R Mt :=
  swp_stepD ix_8000428c [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000428c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem it_80004290 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004294#64 (upd R 10 ((R 2) + sign_extend (m := 64) (0x010#12))) Mt) :
    IW live Dt DA S Q 0x80004290#64 R Mt :=
  swp_stepD ix_80004290 [2, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004290 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [2, 10])))) rfl hk

theorem it_80004294 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004298#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 13))])) :
    IW live Dt DA S Q 0x80004294#64 R Mt :=
  swp_stepD ix_80004294 [2, 13] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80004294 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80004298 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x8000429c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 14))])) :
    IW live Dt DA S Q 0x80004298#64 R Mt :=
  swp_stepD ix_80004298 [2, 14] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80004298 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000429c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x800042a0#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (R 15))])) :
    IW live Dt DA S Q 0x8000429c#64 R Mt :=
  swp_stepD ix_8000429c [2, 15] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000429c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_800042a0 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x800042a0 [0xef#8, 0xe0#8, 0xcf#8, 0xd8#8], live p.1) :
    JalExec (vsaModel live) 0x800042a0 [0xef#8, 0xe0#8, 0xcf#8, 0xd8#8] 0x8000282c#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x800042a0, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x800042a1, .discard, 0xe0#8) (by simp [codeFoot])
  have hb2 := hb (0x800042a2, .discard, 0xcf#8) (by simp [codeFoot])
  have hb3 := hb (0x800042a3, .discard, 0xd8#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x800042a0#64) vm (0xd8cfe0ef#32) (0x1fe58c#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800042a0#64) 4)
      (0xef#8) (0xe0#8) (0xcf#8) (0xd8#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_d8cfe0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x800042a0#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x8000282c#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x800042a0#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x800042a0 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_800042a4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hT : (R 10) = (0#64) → IW live Dt DA S Q 0x80004090#64 R Mt) (hF : ¬ ((R 10) = (0#64)) → IW live Dt DA S Q 0x800042a8#64 R Mt) :
    IW live Dt DA S Q 0x800042a4#64 R Mt := by
  by_cases hc : (R 10) = (0#64)
  · exact
    swp_stepD ixT_800042a4 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_800042a4 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_800042a4 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_800042a4 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem itD_800042a8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hLDD : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x020#12)).toNat 8, b ∈ DA)
    (hk : IW live Dt DA S Q 0x800042ac#64 (upd R 11 (ldv .ld Dt ((R 8) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x800042a8#64 R Mt :=
  swp_stepD ix_800042a8 [8, 11] [bytesAt (imgM Dt) ((R 8) + sign_extend (m := 64) (0x020#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042a8 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img (fun b hb => dataReads_view hD b (hLDD b hb))⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [8, 11])))) rfl hk

theorem it_800042ac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x800042b0#64 (upd R 13 ((R 18) + sign_extend (m := 64) (0x000#12))) Mt) :
    IW live Dt DA S Q 0x800042ac#64 R Mt :=
  swp_stepD ix_800042ac [13, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042ac ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13, 18])))) rfl hk

theorem it_800042b0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x800042b4#64 (upd R 12 ((R 19) + sign_extend (m := 64) (0x000#12))) Mt) :
    IW live Dt DA S Q 0x800042b0#64 R Mt :=
  swp_stepD ix_800042b0 [12, 19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042b0 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 19])))) rfl hk

theorem it_800042b4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x800042b8#64 (upd R 10 ((R 9) + sign_extend (m := 64) (0x000#12))) Mt) :
    IW live Dt DA S Q 0x800042b4#64 R Mt :=
  swp_stepD ix_800042b4 [9, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042b4 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [9, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_800042b8 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x800042b8 [0xef#8, 0xf0#8, 0x9f#8, 0xd2#8], live p.1) :
    JalExec (vsaModel live) 0x800042b8 [0xef#8, 0xf0#8, 0x9f#8, 0xd2#8] 0x80003fe0#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x800042b8, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x800042b9, .discard, 0xf0#8) (by simp [codeFoot])
  have hb2 := hb (0x800042ba, .discard, 0x9f#8) (by simp [codeFoot])
  have hb3 := hb (0x800042bb, .discard, 0xd2#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x800042b8#64) vm (0xd29ff0ef#32) (0x1ffd28#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800042b8#64) 4)
      (0xef#8) (0xf0#8) (0x9f#8) (0xd2#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_d29ff0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x800042b8#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80003fe0#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x800042b8#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x800042b8 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_800042bc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x800042c0#64 (upd R 15 ((0#64) + sign_extend (m := 64) (0x001#12))) Mt) :
    IW live Dt DA S Q 0x800042bc#64 R Mt :=
  swp_stepD ix_800042bc [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042bc ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem it_800042c0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hT : (R 10) ≠ (R 15) → IW live Dt DA S Q 0x8000425c#64 R Mt) (hF : ¬ ((R 10) ≠ (R 15)) → IW live Dt DA S Q 0x800042c4#64 R Mt) :
    IW live Dt DA S Q 0x800042c0#64 R Mt := by
  by_cases hc : (R 10) ≠ (R 15)
  · exact
    swp_stepD ixT_800042c0 [10, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_800042c0 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_800042c0 [10, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_800042c0 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_800042c4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x800042c8#64 (upd R 10 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    IW live Dt DA S Q 0x800042c4#64 R Mt :=
  swp_stepD ix_800042c4 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042c4 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem it_800042c8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x8000409c#64 R Mt) :
    IW live Dt DA S Q 0x800042c8#64 R Mt :=
  swp_stepD ix_800042c8 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042c8 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem itD_800042cc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDD : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x018#12)).toNat 8, b ∈ DA)
    (hk : IW live Dt DA S Q 0x800042d0#64 (upd R 8 (ldv .ld Dt ((R 8) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x800042cc#64 R Mt :=
  swp_stepD ix_800042cc [8] [bytesAt (imgM Dt) ((R 8) + sign_extend (m := 64) (0x018#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042cc ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img (fun b hb => dataReads_view hD b (hLDD b hb))⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8])))) rfl hk

theorem it_800042d0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hT : (R 8) ≠ (0#64) → IW live Dt DA S Q 0x80004014#64 R Mt) (hF : ¬ ((R 8) ≠ (0#64)) → IW live Dt DA S Q 0x800042d4#64 R Mt) :
    IW live Dt DA S Q 0x800042d0#64 R Mt := by
  by_cases hc : (R 8) ≠ (0#64)
  · exact
    swp_stepD ixT_800042d0 [8] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_800042d0 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_800042d0 [8] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_800042d0 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_800042d4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x800042d8#64 (upd R 10 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    IW live Dt DA S Q 0x800042d4#64 R Mt :=
  swp_stepD ix_800042d4 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042d4 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem it_800042d8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x8000409c#64 R Mt) :
    IW live Dt DA S Q 0x800042d8#64 R Mt :=
  swp_stepD ix_800042d8 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042d8 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_800042dc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x800042e0#64 (upd R 13 ((R 19) + sign_extend (m := 64) (0x000#12))) Mt) :
    IW live Dt DA S Q 0x800042dc#64 R Mt :=
  swp_stepD ix_800042dc [13, 19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042dc ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13, 19])))) rfl hk

theorem it_800042e0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x800042e4#64 (upd R 11 ((R 9) + sign_extend (m := 64) (0x000#12))) Mt) :
    IW live Dt DA S Q 0x800042e0#64 R Mt :=
  swp_stepD ix_800042e0 [9, 11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042e0 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [9, 11])))) rfl hk

theorem it_800042e4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x800042e8#64 (upd R 10 ((R 2) + sign_extend (m := 64) (0x010#12))) Mt) :
    IW live Dt DA S Q 0x800042e4#64 R Mt :=
  swp_stepD ix_800042e4 [2, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042e4 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [2, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_800042e8 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x800042e8 [0xef#8, 0xe0#8, 0xdf#8, 0xe7#8], live p.1) :
    JalExec (vsaModel live) 0x800042e8 [0xef#8, 0xe0#8, 0xdf#8, 0xe7#8] 0x80003164#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x800042e8, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x800042e9, .discard, 0xe0#8) (by simp [codeFoot])
  have hb2 := hb (0x800042ea, .discard, 0xdf#8) (by simp [codeFoot])
  have hb3 := hb (0x800042eb, .discard, 0xe7#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x800042e8#64) vm (0xe7dfe0ef#32) (0x1fee7c#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800042e8#64) 4)
      (0xef#8) (0xe0#8) (0xdf#8) (0xe7#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_e7dfe0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x800042e8#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80003164#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x800042e8#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x800042e8 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_800042ec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x8000426c#64 R Mt) :
    IW live Dt DA S Q 0x800042ec#64 R Mt :=
  swp_stepD ix_800042ec [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042ec ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_800042f0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x800042f4#64 (upd R 10 ((R 2) + sign_extend (m := 64) (0x010#12))) Mt) :
    IW live Dt DA S Q 0x800042f0#64 R Mt :=
  swp_stepD ix_800042f0 [2, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042f0 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [2, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_800042f4 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x800042f4 [0xef#8, 0xe0#8, 0x8f#8, 0xcf#8], live p.1) :
    JalExec (vsaModel live) 0x800042f4 [0xef#8, 0xe0#8, 0x8f#8, 0xcf#8] 0x800027ec#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x800042f4, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x800042f5, .discard, 0xe0#8) (by simp [codeFoot])
  have hb2 := hb (0x800042f6, .discard, 0x8f#8) (by simp [codeFoot])
  have hb3 := hb (0x800042f7, .discard, 0xcf#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x800042f4#64) vm (0xcf8fe0ef#32) (0x1fe4f8#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800042f4#64) 4)
      (0xef#8) (0xe0#8) (0x8f#8) (0xcf#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_cf8fe0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x800042f4#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x800027ec#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x800042f4#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x800042f4 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_800042f8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004138#64 R Mt) :
    IW live Dt DA S Q 0x800042f8#64 R Mt :=
  swp_stepD ix_800042f8 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042f8 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_800042fc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004300#64 (upd R 10 ((R 2) + sign_extend (m := 64) (0x068#12))) Mt) :
    IW live Dt DA S Q 0x800042fc#64 R Mt :=
  swp_stepD ix_800042fc [2, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800042fc ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [2, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_80004300 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80004300 [0xef#8, 0xe0#8, 0xcf#8, 0xce#8], live p.1) :
    JalExec (vsaModel live) 0x80004300 [0xef#8, 0xe0#8, 0xcf#8, 0xce#8] 0x800027ec#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x80004300, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x80004301, .discard, 0xe0#8) (by simp [codeFoot])
  have hb2 := hb (0x80004302, .discard, 0xcf#8) (by simp [codeFoot])
  have hb3 := hb (0x80004303, .discard, 0xce#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x80004300#64) vm (0xcecfe0ef#32) (0x1fe4ec#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80004300#64) 4)
      (0xef#8) (0xe0#8) (0xcf#8) (0xce#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_cecfe0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80004300#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x800027ec#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x80004300#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x80004300 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_80004304 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x800040f0#64 R Mt) :
    IW live Dt DA S Q 0x80004304#64 R Mt :=
  swp_stepD ix_80004304 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004304 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_800043ec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x800043f0#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0xf50#12))) Mt) :
    IW live Dt DA S Q 0x800043ec#64 R Mt :=
  swp_stepD ix_800043ec [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800043ec ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem it_800043f0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x800043f4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x000#12)).toNat, 8, (R 10))])) :
    IW live Dt DA S Q 0x800043f0#64 R Mt :=
  swp_stepD ix_800043f0 [2, 10] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_800043f0 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_800043f4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x800043f8#64 (upd R 10 ((R 10) + sign_extend (m := 64) (0x010#12))) Mt) :
    IW live Dt DA S Q 0x800043f4#64 R Mt :=
  swp_stepD ix_800043f4 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_800043f4 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem it_800043f8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0a8#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a8#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x800043fc#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0a8#12)).toNat, 8, (R 1))])) :
    IW live Dt DA S Q 0x800043f8#64 R Mt :=
  swp_stepD ix_800043f8 [1, 2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a8#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_800043f8 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_800043fc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x0a0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a0#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004400#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x0a0#12)).toNat, 8, (R 8))])) :
    IW live Dt DA S Q 0x800043fc#64 R Mt :=
  swp_stepD ix_800043fc [2, 8] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_800043fc ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80004400 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x098#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x098#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004404#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x098#12)).toNat, 8, (R 9))])) :
    IW live Dt DA S Q 0x80004400#64 R Mt :=
  swp_stepD ix_80004400 [2, 9] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x098#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80004400 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80004404 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x090#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x090#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004408#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x090#12)).toNat, 8, (R 18))])) :
    IW live Dt DA S Q 0x80004404#64 R Mt :=
  swp_stepD ix_80004404 [2, 18] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x090#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80004404 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80004408 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x088#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x088#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x8000440c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x088#12)).toNat, 8, (R 19))])) :
    IW live Dt DA S Q 0x80004408#64 R Mt :=
  swp_stepD ix_80004408 [2, 19] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x088#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80004408 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000440c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x080#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x080#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004410#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x080#12)).toNat, 8, (R 20))])) :
    IW live Dt DA S Q 0x8000440c#64 R Mt :=
  swp_stepD ix_8000440c [2, 20] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x080#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000440c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80004410 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004414#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x078#12)).toNat, 8, (R 21))])) :
    IW live Dt DA S Q 0x80004410#64 R Mt :=
  swp_stepD ix_80004410 [2, 21] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x078#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80004410 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80004414 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004418#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x070#12)).toNat, 8, (R 22))])) :
    IW live Dt DA S Q 0x80004414#64 R Mt :=
  swp_stepD ix_80004414 [2, 22] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x070#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80004414 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80004418 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x8000441c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 11))])) :
    IW live Dt DA S Q 0x80004418#64 R Mt :=
  swp_stepD ix_80004418 [2, 11] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80004418 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000441c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004420#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 12))])) :
    IW live Dt DA S Q 0x8000441c#64 R Mt :=
  swp_stepD ix_8000441c [2, 12] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000441c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80004420 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004424#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 13))])) :
    IW live Dt DA S Q 0x80004420#64 R Mt :=
  swp_stepD ix_80004420 [2, 13] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80004420 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_80004424 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80004424 [0xef#8, 0x20#8, 0x90#8, 0x3d#8], live p.1) :
    JalExec (vsaModel live) 0x80004424 [0xef#8, 0x20#8, 0x90#8, 0x3d#8] 0x80006ffc#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x80004424, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x80004425, .discard, 0x20#8) (by simp [codeFoot])
  have hb2 := hb (0x80004426, .discard, 0x90#8) (by simp [codeFoot])
  have hb3 := hb (0x80004427, .discard, 0x3d#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x80004424#64) vm (0x3d9020ef#32) (0x002bd8#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80004424#64) 4)
      (0xef#8) (0x20#8) (0x90#8) (0x3d#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_3d9020ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80004424#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80006ffc#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x80004424#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x80004424 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_80004428 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hT : (R 10) ≠ (0#64) → IW live Dt DA S Q 0x80004508#64 R Mt) (hF : ¬ ((R 10) ≠ (0#64)) → IW live Dt DA S Q 0x8000442c#64 R Mt) :
    IW live Dt DA S Q 0x80004428#64 R Mt := by
  by_cases hc : (R 10) ≠ (0#64)
  · exact
    swp_stepD ixT_80004428 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_80004428 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_80004428 [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_80004428 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000442c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004430#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x8000442c#64 R Mt :=
  swp_stepD ix_8000442c [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000442c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem it_80004430 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004434#64 (upd R 21 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    IW live Dt DA S Q 0x80004430#64 R Mt :=
  swp_stepD ix_80004430 [10, 21] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004430 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 21 ∈ [10, 21])))) rfl hk

theorem it_80004434 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hT : (R 15).toInt ≤ (0#64).toInt → IW live Dt DA S Q 0x80004514#64 R Mt) (hF : ¬ ((R 15).toInt ≤ (0#64).toInt) → IW live Dt DA S Q 0x80004438#64 R Mt) :
    IW live Dt DA S Q 0x80004434#64 R Mt := by
  by_cases hc : (R 15).toInt ≤ (0#64).toInt
  · exact
    swp_stepD ixT_80004434 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_80004434 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_80004434 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_80004434 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_80004438 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x8000443c#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x80004438#64 R Mt :=
  swp_stepD ix_80004438 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004438 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem it_8000443c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004440#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x8000443c#64 R Mt :=
  swp_stepD ix_8000443c [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000443c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem it_80004440 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004444#64 (upd R 22 ((0x8001b510#64) + sign_extend (m := 64) (0x460#12))) Mt) :
    IW live Dt DA S Q 0x80004440#64 R Mt :=
  swp_stepD ix_80004440 [3, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004440 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun _ => rfl) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [3, 22])))) rfl hk

theorem it_80004444 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004448#64 (upd R 18 (shift_bits_left (R 15) (Sail.BitVec.extractLsb (0x03#6) 5 0))) Mt) :
    IW live Dt DA S Q 0x80004444#64 R Mt :=
  swp_stepD ix_80004444 [15, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004444 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [15, 18])))) rfl hk

theorem it_80004448 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x8000444c#64 (upd R 18 ((R 8) + (R 18))) Mt) :
    IW live Dt DA S Q 0x80004448#64 R Mt :=
  swp_stepD ix_80004448 [8, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004448 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [8, 18])))) rfl hk

theorem it_8000444c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004450#64 (upd R 19 ((0#64) + sign_extend (m := 64) (0x003#12))) Mt) :
    IW live Dt DA S Q 0x8000444c#64 R Mt :=
  swp_stepD ix_8000444c [19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000444c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [19])))) rfl hk

theorem it_80004450 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004454#64 (upd R 20 ((0#64) + sign_extend (m := 64) (0x001#12))) Mt) :
    IW live Dt DA S Q 0x80004450#64 R Mt :=
  swp_stepD ix_80004450 [20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004450 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [20])))) rfl hk

theorem it_80004454 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x8000448c#64 R Mt) :
    IW live Dt DA S Q 0x80004454#64 R Mt :=
  swp_stepD ix_80004454 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004454 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80004458 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x8000445c#64 (upd R 10 ((R 2) + sign_extend (m := 64) (0x058#12))) Mt) :
    IW live Dt DA S Q 0x80004458#64 R Mt :=
  swp_stepD ix_80004458 [2, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004458 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [2, 10])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000445c (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000445c [0xef#8, 0xe0#8, 0x0f#8, 0xb9#8], live p.1) :
    JalExec (vsaModel live) 0x8000445c [0xef#8, 0xe0#8, 0x0f#8, 0xb9#8] 0x800027ec#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000445c, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000445d, .discard, 0xe0#8) (by simp [codeFoot])
  have hb2 := hb (0x8000445e, .discard, 0x0f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000445f, .discard, 0xb9#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000445c#64) vm (0xb90fe0ef#32) (0x1fe390#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000445c#64) 4)
      (0xef#8) (0xe0#8) (0x0f#8) (0xb9#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_b90fe0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000445c#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x800027ec#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000445c#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000445c + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_80004460 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004464#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x80004460#64 R Mt :=
  swp_stepD ix_80004460 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004460 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem it_80004464 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004468#64 (upd R 13 ((R 2) + sign_extend (m := 64) (0x058#12))) Mt) :
    IW live Dt DA S Q 0x80004464#64 R Mt :=
  swp_stepD ix_80004464 [2, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004464 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [2, 13])))) rfl hk

theorem it_80004468 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x8000446c#64 (upd R 11 ((R 9) + sign_extend (m := 64) (0x000#12))) Mt) :
    IW live Dt DA S Q 0x80004468#64 R Mt :=
  swp_stepD ix_80004468 [9, 11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004468 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [9, 11])))) rfl hk

theorem itD_8000446c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 15) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDD : ∀ b ∈ accAddrs ((R 15) + sign_extend (m := 64) (0x000#12)).toNat 8, b ∈ DA)
    (hk : IW live Dt DA S Q 0x80004470#64 (upd R 12 (ldv .ld Dt ((R 15) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x8000446c#64 R Mt :=
  swp_stepD ix_8000446c [12, 15] [bytesAt (imgM Dt) ((R 15) + sign_extend (m := 64) (0x000#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000446c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img (fun b hb => dataReads_view hD b (hLDD b hb))⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 15])))) rfl hk

theorem it_80004470 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004474#64 (upd R 10 ((R 15) + sign_extend (m := 64) (0x000#12))) Mt) :
    IW live Dt DA S Q 0x80004470#64 R Mt :=
  swp_stepD ix_80004470 [10, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004470 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 15])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_80004474 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80004474 [0xef#8, 0xf0#8, 0xdf#8, 0xb6#8], live p.1) :
    JalExec (vsaModel live) 0x80004474 [0xef#8, 0xf0#8, 0xdf#8, 0xb6#8] 0x80003fe0#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x80004474, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x80004475, .discard, 0xf0#8) (by simp [codeFoot])
  have hb2 := hb (0x80004476, .discard, 0xdf#8) (by simp [codeFoot])
  have hb3 := hb (0x80004477, .discard, 0xb6#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x80004474#64) vm (0xb6dff0ef#32) (0x1ffb6c#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80004474#64) 4)
      (0xef#8) (0xf0#8) (0xdf#8) (0xb6#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_b6dff0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80004474#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80003fe0#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x80004474#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x80004474 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_80004478 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hT : (R 10) = (R 19) → IW live Dt DA S Q 0x80004540#64 R Mt) (hF : ¬ ((R 10) = (R 19)) → IW live Dt DA S Q 0x8000447c#64 R Mt) :
    IW live Dt DA S Q 0x80004478#64 R Mt := by
  by_cases hc : (R 10) = (R 19)
  · exact
    swp_stepD ixT_80004478 [10, 19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_80004478 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_80004478 [10, 19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_80004478 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000447c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004480#64 (upd R 10 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 10) + sign_extend (m := 64) (0xfff#12)) 31 0))) Mt) :
    IW live Dt DA S Q 0x8000447c#64 R Mt :=
  swp_stepD ix_8000447c [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000447c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem it_80004480 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hT : (R 10).toNat ≤ (R 20).toNat → IW live Dt DA S Q 0x80004564#64 R Mt) (hF : ¬ ((R 10).toNat ≤ (R 20).toNat) → IW live Dt DA S Q 0x80004484#64 R Mt) :
    IW live Dt DA S Q 0x80004480#64 R Mt := by
  by_cases hc : (R 10).toNat ≤ (R 20).toNat
  · exact
    swp_stepD ixT_80004480 [10, 20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_80004480 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_bgeu _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_80004480 [10, 20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_80004480 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_false (guard_bgeu _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_80004484 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004488#64 (upd R 8 ((R 8) + sign_extend (m := 64) (0x008#12))) Mt) :
    IW live Dt DA S Q 0x80004484#64 R Mt :=
  swp_stepD ix_80004484 [8] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004484 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8])))) rfl hk

theorem it_80004488 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hT : (R 8) = (R 18) → IW live Dt DA S Q 0x80004514#64 R Mt) (hF : ¬ ((R 8) = (R 18)) → IW live Dt DA S Q 0x8000448c#64 R Mt) :
    IW live Dt DA S Q 0x80004488#64 R Mt := by
  by_cases hc : (R 8) = (R 18)
  · exact
    swp_stepD ixT_80004488 [8, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_80004488 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_80004488 [8, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_80004488 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000448c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004490#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x8000448c#64 R Mt :=
  swp_stepD ix_8000448c [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000448c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem itD_80004490 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDD : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8, b ∈ DA)
    (hk : IW live Dt DA S Q 0x80004494#64 (upd R 9 (ldv .ld Dt ((R 8) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x80004490#64 R Mt :=
  swp_stepD ix_80004490 [8, 9] [bytesAt (imgM Dt) ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004490 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img (fun b hb => dataReads_view hD b (hLDD b hb))⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [8, 9])))) rfl hk

theorem it_80004494 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hT : (R 15) = (0#64) → IW live Dt DA S Q 0x80004458#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → IW live Dt DA S Q 0x80004498#64 R Mt) :
    IW live Dt DA S Q 0x80004494#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    swp_stepD ixT_80004494 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_80004494 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_80004494 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_80004494 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_80004508 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x8000450c#64 (upd R 15 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x80004508#64 R Mt :=
  swp_stepD ix_80004508 [2, 15] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004508 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [2, 15])))) rfl hk

theorem it_8000450c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hk : IW live Dt DA S Q 0x80004510#64 (upd R 21 ((0#64) + sign_extend (m := 64) (0x001#12))) Mt) :
    IW live Dt DA S Q 0x8000450c#64 R Mt :=
  swp_stepD ix_8000450c [21] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000450c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 21 ∈ [21])))) rfl hk

theorem it_80004510 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : StOK ((R 15) + sign_extend (m := 64) (0x008#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 15) + sign_extend (m := 64) (0x008#12)).toNat 4, S b)
    (hk : IW live Dt DA S Q 0x80004514#64 R (writeLog Mt [(((R 15) + sign_extend (m := 64) (0x008#12)).toNat, 4, (0#64))])) :
    IW live Dt DA S Q 0x80004510#64 R Mt :=
  swp_stepD ix_80004510 [15] [] [] (accAddrs ((R 15) + sign_extend (m := 64) (0x008#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_80004510 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_80004514 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0a8#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a8#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004518#64 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x0a8#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x80004514#64 R Mt :=
  swp_stepD ix_80004514 [1, 2] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0a8#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a8#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004514 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 1 ∈ [1, 2])))) rfl hk

theorem it_80004518 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0a0#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a0#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x8000451c#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x0a0#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x80004518#64 R Mt :=
  swp_stepD ix_80004518 [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0a0#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a0#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004518 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem it_8000451c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x098#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x098#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004520#64 (upd R 9 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x098#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x8000451c#64 R Mt :=
  swp_stepD ix_8000451c [2, 9] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x098#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x098#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000451c ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [2, 9])))) rfl hk

theorem it_80004520 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x090#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x090#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004524#64 (upd R 18 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x090#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x80004520#64 R Mt :=
  swp_stepD ix_80004520 [2, 18] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x090#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x090#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004520 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [2, 18])))) rfl hk

theorem it_80004524 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x088#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x088#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x80004528#64 (upd R 19 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x088#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x80004524#64 R Mt :=
  swp_stepD ix_80004524 [2, 19] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x088#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x088#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004524 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [2, 19])))) rfl hk

theorem it_80004528 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x080#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x080#12)).toNat 8, S b)
    (hk : IW live Dt DA S Q 0x8000452c#64 (upd R 20 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x080#12)).toNat)) Mt) :
    IW live Dt DA S Q 0x80004528#64 R Mt :=
  swp_stepD ix_80004528 [2, 20] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x080#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x080#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_80004528 ChainFacts; chain_facts hm with "VsaIris.Sym.interp_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [2, 20])))) rfl hk

end VsaIris.Sym
