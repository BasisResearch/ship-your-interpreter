import VsaIris.Interp.BinPrelude
import VsaIris.Interp.ConcatArm
import VsaIris.Interp.BinArm
import VsaIris.Interp.ErrArm

/-!
String concatenation from the binary dispatch point, proved once for the total and partial specs.
The tail is generic in the WP, the final regime `ρ` (costs appear as `ρ.plus c`) and the
continuation `K`; the partial spec's aborts (stringify and allocation failure) are reached only
when `ρ = .uncounted`, through `hoom`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim
open VsaIris.VsaHeap VsaIris.Newlib

#ix_seg CatTail_run3 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret w1 kL kR : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 32 ≤ 0x100000000)
    (hx3 : aX.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64) (h9 : R 9 = sret) (h19 : R 19 = w1)
    (hop : ldv .lw m (aX + 8#64).toNat = 11#64)
    (hKL : ldv .ld Mt (s.toNat - 1088) = kL) (hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = kR) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x8000351c#64 R Mt
  by ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at 0x80003888

#ix_seg CatTail_run3b {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m : Mem} {DA : List Nat} {Mt : Mem}
    {R : Nat → BitVec 64} {s : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709550528#64) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x80003a20#64 R Mt
  by ix_run hlive using [h2, hsf] at 0x80003a40

#ix_seg CatTail_run4 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m : Mem} {DA : List Nat} {Mt : Mem}
    {R : Nat → BitVec 64} {s : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709550528#64) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x80003a44#64 R Mt
  by ix_run hlive using [h2, hsf] at 0x80003a68

#ix_seg CatTail_run5 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m : Mem} {DA : List Nat} {Mt : Mem}
    {R : Nat → BitVec 64} {s sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h9 : R 9 = sret) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x80003a6c#64 R Mt
  by ix_run hlive using [h9, hsf] at 0x80003a78

#ix_seg CatTail_run6 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m : Mem} {DA : List Nat} {Mt : Mem}
    {R : Nat → BitVec 64} {s sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h9 : R 9 = sret) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x80003a7c#64 R Mt
  by ix_run hlive using [h9, hsf] at 0x80003a84

#ix_seg CatTail_run7 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m : Mem} {DA : List Nat} {Mt : Mem}
    {R : Nat → BitVec 64} {s sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h9 : R 9 = sret) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x80003a88#64 R Mt
  by ix_run hlive using [h9, hsf] at 0x80003a90

#ix_seg CatTail_run8 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m : Mem} {DA : List Nat} {Mt : Mem}
    {R : Nat → BitVec 64} {s : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709550528#64) (hq : R 10 ≠ 0#64) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x80003a94#64 R Mt
  by ix_run hlive using [h2, hq, hsf] at 0x80003aa8

#ix_seg CatTail_run9 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m : Mem} {DA : List Nat} {Mt : Mem}
    {R : Nat → BitVec 64} {s sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h9 : R 9 = sret) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x80003aac#64 R Mt
  by ix_run hlive using [h9, hsf] at 0x80003ab4

#ix_seg CatTail_run10 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m : Mem} {DA : List Nat} {Mt : Mem}
    {R : Nat → BitVec 64} {s sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h9 : R 9 = sret) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x80003ab8#64 R Mt
  by ix_run hlive using [h9, hsf] at 0x80003abc

#ix_seg CatTail_run11 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m : Mem} {DA : List Nat} {Mt : Mem}
    {R : Nat → BitVec 64} {s sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h9 : R 9 = sret) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x80003ac0#64 R Mt
  by ix_run hlive using [h9, hsf] at 0x80003ac4

#ix_seg CatTail_run12 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m : Mem} {DA : List Nat} {Mt : Mem}
    {R : Nat → BitVec 64} {s sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h9 : R 9 = sret) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x80003ac8#64 R Mt
  by ix_run hlive using [h9, hsf] at 0x80003ad0

#ix_seg CatTail_run13 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s ret v8 v9 v18 v19 v20 v21 : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = s + 18446744073709550528#64)
    (hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18)
    (hS3 : ldv .ld Mt (s + 18446744073709550528#64 + 1048#64).toNat = v19)
    (hS4 : ldv .ld Mt (s + 18446744073709550528#64 + 1040#64).toNat = v20)
    (hS5 : ldv .ld Mt (s + 18446744073709550528#64 + 1032#64).toNat = v21) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x80003ad4#64 R Mt
  by ix_run hlive using [h2, hRA, hS0, hS1, hS2, hS3, hS4, hS5, hsf, hal]

#ix_seg CatTail_run8z {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m : Mem} {DA : List Nat} {Mt : Mem}
    {R : Nat → BitVec 64} {s : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709550528#64) (hq : R 10 = 0#64) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x80003a94#64 R Mt
  by ix_run hlive using [h2, hq, hsf] at 0x80003e28


open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

theorem Regime.plus_add' (ρ : Regime) (a b : Nat) : (ρ.plus a).plus b = ρ.plus (a + b) := by
  cases ρ <;> simp [Regime.plus, Nat.add_assoc]

syntax "cat_keep " "[" term,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| cat_keep [$hs,*]) => do
    let mut t ← `(tactic| (try ix_reg))
    for h in hs.getElems do
      let st ← `(tactic| (try rw [keep_reg $h (by decide)]))
      let sh ← `(tactic| (try rw [keep_helper $h (by decide) (by decide)]))
      t ← `(tactic| ($t; $st; $sh; (try ix_reg)))
    `(tactic| ($t; all_goals simp only [er2, er8, er9, er18, er19, er20, er21, er22, er23, er24,
      er25, er26, er27]))

set_option hygiene false in
macro "cat_mem" : tactic => `(tactic| (all_goals
  simp only [hl0, hl1, hl2, hq0', hq1, hq2]))

section
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

theorem ExitK.pure {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {s ret sret : BitVec 64} {rv R' : Nat → BitVec 64} {n : Nat} {v : Value}
    {Wd K : IProp GF} (h : ExitK Wp Φ N s ret sret rv n v Wd K) :
    PC ↦ᵣ ret ∗ ra ↦ᵣ ret ∗ regFile R' ∗ stackScratch s n ∗ valAt N sret.toNat v ∗ Wd ∗ K ∗
      ⌜KeepRegs calleeSaved rv R'⌝ ⊢ Wp.W Φ := by
  iintro ⟨Hpc, Hra, Hr, Hs, Hv, Hw, HK, %hk⟩
  iapply h R' hk
  iframe Hpc Hra Hr Hs Hv Hw HK

end

#ix_piece catTail_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    (Wp : MachWP (GF := GF) (vsaModel live)) (ρ : Regime) {N : NativeAddrs} {inp : Nat}
    (A : AllocSpecs live)
    (hsgy : ⊢ ∀ (p s : BitVec 64) (v : Value) (st : Store) (j : Nat) (H : List (Nat × Nat))
      (c : Nat) (o : String),
      helperSpecA (vsaModel live) Wp stringifyPC callerSaved (fun rv => rv 10 = p ∧ rv 2 = s)
        (stringifyPre N p s v st (ρ.plus j) H c o)
        (fun rv' => stringifyPost N p s v st (ρ.plus j) H o (rv' 10))
        iprop(⌜ρ = .uncounted⌝ ∗ abortRes N vsaLayoutP vsaRoomB inp s stringifyNeed ∗
          slot24 p.toNat))
    (hsl : ⊢ ∀ q x ρ H, strlenHeapSpec (GF := GF) (vsaModel live) Wp q x ρ H)
    (hmc : ⊢ memcpySpecOwned (GF := GF) (vsaModel live) Wp)
    (hsc : ⊢ ∀ d q y ρ H, strcpyHeapSpec (GF := GF) (vsaModel live) Wp d q y ρ H)
    (hvs : ⊢ ∀ p q x, valueStrSpec (GF := GF) (vsaModel live) N Wp p q x)
    (hd : CatDispSupply (GF := GF) N)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat}
    {aE s ret sret aX : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem} {st2 : St} {d : Nat}
    {l r : Expr} {lv rv' : Value} {w0 w1 w2 u0 u1 u2 : BitVec 64} {K : IProp GF}
    (g : ArmGeo s ret sret (evalNeed (.binary .add l r) d)) (hn : BinOpNode m P aX (binOpTok .add))
    (mid : BinMid s sret (BitVec.ofNat 64 inp) rv R Mt ret aX lv rv' w0 w1 w2 u0 u1 u2)
    (hcat : valTag lv = 3 ∨ valTag rv' = 3)
    (hexit : ExitK Wp Φ N s ret sret rv (evalNeed (.binary .add l r) d)
      (.str (lv.catDisplay st2.store ++ rv'.catDisplay st2.store))
      (world N vsaLayoutP vsaRoomB inp ρ st2 d) K)
    (hoom : ρ = .uncounted → ∃ Core, ErrEnv (GF := GF) N vsaLayoutP vsaRoomB inp live Core ∧
      AbortK Wp Φ inp Core s sret (evalNeed (.binary .add l r) d) K) :
    BinTail Wp Φ N (binArmF N P m env aE s (evalNeed (.binary .add l r) d) sret
      (world N vsaLayoutP vsaRoomB inp (ρ.plus (concatCost st2.store lv rv')) st2 d) K)
      R s Mt lv rv' w0 w1 w2 u0 u1 u2 by
  unfold BinTail binArmF evalArmF
  iintro ⟨⟨#Hv1, #Hv2⟩, ⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  ihave ⟨Hw, #Hbin, #Hat⟩ := world_allocText N vsaLayoutP vsaRoomB inp _ st2 d $$ Hw
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs' := g.lo; have hs2 := g.hi; have hs3 := g.al; have hsg := g.sg; have hneed := g.need
  have hal := g.ral
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hoff := g.off
  have htl := mid.tl; have htr := mid.tr; have hsv2 := mid.saved
  have hs4 := g.sg.le; have hslg := g.slg
  have er2 : R 2 = s + 18446744073709550528#64 := mid.r2; have er8 := mid.r8; have er9 := mid.r9; have er18 := mid.r18
  have er19 := mid.r19
  have er20 := mid.hi 20 (by decide); have er21 := mid.hi 21 (by decide)
  have er22 := mid.hi 22 (by decide); have er23 := mid.hi 23 (by decide)
  have er24 := mid.hi 24 (by decide); have er25 := mid.hi 25 (by decide)
  have er26 := mid.hi 26 (by decide); have er27 := mid.hi 27 (by decide)
  have hl0 : ldv .ld Mt (s.toNat - 1088 + 120) = w0 := by rw [← hoff 120 (by decide)]; exact mid.l0
  have hl1 : ldv .ld Mt (s.toNat - 1088 + 128) = w1 := by rw [← hoff 128 (by decide)]; exact mid.l1
  have hl2 : ldv .ld Mt (s.toNat - 1088 + 136) = w2 := by rw [← hoff 136 (by decide)]; exact mid.l2
  have hq0' : ldv .ld Mt (s.toNat - 1088 + 144) = u0 := by rw [← hoff 144 (by decide)]; exact mid.q0
  have hq1 : ldv .ld Mt (s.toNat - 1088 + 152) = u1 := by rw [← hoff 152 (by decide)]; exact mid.q1
  have hq2 : ldv .ld Mt (s.toNat - 1088 + 160) = u2 := by rw [← hoff 160 (by decide)]; exact mid.q2

  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.binary .add l r) d - 1088) (slot24 sret.toNat)
      (world N vsaLayoutP vsaRoomB inp (ρ.plus (concatCost st2.store lv rv')) st2 d)
      K ∗
      □ valOf N lv w0 w1 w2 ∗ □ valOf N rv' u0 u1 u2 ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [Hv1 Hv2]
    · iframe Hcode Hro Hfb Hst Hslot Hw; iexact Hk
    · iframe Hv1 Hbin Hat; iexact Hv2
  intro F'
  refine CatTail_run3 (aX := aX) (s := s) (sret := sret) (w1 := w1)
    (kL := BitVec.ofNat 64 (w0.toNat % 2 ^ 32)) (kR := BitVec.ofNat 64 (u0.toNat % 2 ^ 32))
    hlive hsf hs' hs2 hs3 hx1 hx2 hx3 ?_ ?_ ?_ ?_ hn.op ?_ ?_ ?_
  · cat_keep []
  · cat_keep []
  · cat_keep []
  · cat_keep []
  · rw [mid.tl]; exact mid.kl
  · rw [mid.tr]; exact mid.kr
  intros
  refine concat_route hlive ?_ fun _ => ?_
  · rcases hcat with h | h
    · right; ix_reg; rw [ofNat_lo32 (htl.trans h)]; decide
    · left; ix_reg; rw [ofNat_lo32 (htr.trans h)]; decide
  refine CatTail_run3b (s := s) hlive hsf hs' hs2 hs3 ?_ ?_
  · ix_reg; cat_keep []
  intros
  apply swp_closeM
  intro Mt3 hMt3
  have hcs3 : CatSaved Mt3 s ret rv :=
    ⟨by rw [hMt3]; ix_saved hsv2 using hoff, by rw [hMt3]; e2_fwd hoff; cat_keep []⟩
  have ha0 : ldv .ld Mt3 (s + 18446744073709550528#64 + 64#64).toNat = w0 := by
    rw [hMt3]; e2_fwd hoff; cat_mem
  have ha8 : ldv .ld Mt3 ((s + 18446744073709550528#64 + 64#64).toNat + 8) = w1 := by
    rw [hMt3]; e2_fwd hoff; cat_mem
  have ha16 : ldv .ld Mt3 ((s + 18446744073709550528#64 + 64#64).toNat + 16) = w2 := by
    rw [hMt3]; e2_fwd hoff; cat_mem
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #Hv1, #Hv2, #Hbin, #Hat⟩, Hms⟩

  unfold world worldE
  icases Hw with ⟨%H, %B, Hh, Hsto, Hcon, Hio, Hctx, %hB, #Hbw⟩
  ihave ⟨Hsto, #Hd1⟩ := dispRes_of_valOf hd st2.store B lv w0 w1 w2 $$ [Hsto Hv1]
  · iframe Hsto Hv1
  ihave ⟨Hsto, #Hd2⟩ := dispRes_of_valOf hd st2.store B rv' u0 u1 u2 $$ [Hsto Hv2]
  · iframe Hsto Hv2
  have hS64 : ∀ k, InExt ((s + 18446744073709550528#64 + 64#64).toNat, 24) k →
      InExt (s.toNat - 1088, 1088) k := by
    intro k hk; rw [hoff 64 (by decide)] at hk; simp only [VsaIris.InExt] at hk ⊢; omega
  ihave ⟨Hms, HA⟩ := ms_carveWords N hS64 ha0 ha8 ha16 $$ [Hms Hv1]
  · iframe Hms Hv1

  have hne := evalNeed_binary_rtErr .add l r d
  unfold Newlib.RtErr.rtErrNeed Newlib.snprintfNeed at hne
  have gS := evalCallGeom (nc := stringifyNeed) (o := 64) hsg
    (by unfold stringifyNeed Newlib.snprintfNeed; omega) (by decide) (by decide)
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow (s := s + 18446744073709550528#64)
    (n := evalNeed (.binary .add l r) d - 1088) (m := stringifyNeed) (by rw [hsf]; omega)
    (by unfold stringifyNeed Newlib.snprintfNeed; omega) $$ Hst
  rw [show concatCost st2.store lv rv' = stringifyCost st2.store rv' +
      catBufCost st2.store lv rv' + stringifyCost st2.store lv by unfold concatCost catBufCost; omega]
  ihave Hs1 := hsgy $$ %(s + 18446744073709550528#64 + 64#64) %(s + 18446744073709550528#64) %lv
    %st2.store %(stringifyCost st2.store rv' + catBufCost st2.store lv rv') %H
    %(stringifyCost st2.store lv) %st2.out
  iapply ms_callHelperA Wp (i := 0x80003a40)
    (jalx_80003a40 live (fun p hp => hlive _ (interp_code_80003a40 p hp)))
    interp_code_80003a40 (by decide)
  iframe Hs1 Hcode Hms
  isplitl []
  · ipureintro; exact ⟨by ix_reg, by ix_reg; cat_keep []⟩
  isplitl [HA Hh Hio Hcon Hst]
  · unfold stringifyPre stackAt; simp only [Regime.plus_add']
    iframe HA Hd1 Hbin Hh Hio Hcon Hst
    ipureintro; exact ⟨⟨gS.slotGeom, stringifyChg st2.store lv⟩, gS.child⟩
  isplit
  rotate_left
  · iintro ⟨%hρ, HA, Hsl⟩ HS
    obtain ⟨Core, hE, hab⟩ := hoom hρ
    unfold AbortK at hab
    ihave ⟨-, Hk⟩ := hab $$ Hk
    iapply Hk
    iframe Hslot
    iapply abortAt_of_stringify hE.core hsg (by unfold stringifyNeed Newlib.snprintfNeed; omega) hS64
    iframe HA Hsl HS Hslack
  iintro %R4 %hkeep4 Hpost Hms
  unfold stringifyPost stackAt
  icases Hpost with ⟨HA, Hx, %hf1, Hh, Hio, Hcon, Hst, -⟩
  ihave ⟨%M4, Hms, %hM4⟩ := ms_uncarveVal N hS64 $$ [Hms HA]
  · iframe Hms HA
  have hcs4 : CatSaved M4 s ret rv := hcs3.agree fun k h1 h2 =>
    hM4 k (by simp only [VsaIris.InExt]; omega)
      (by rw [hoff 64 (by decide)]; simp only [VsaIris.InExt]; omega)

#ix_piece catTail_p4 from catTail_p1 by

  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB (ρ.plus (stringifyCost st2.store rv' +
          catBufCost st2.store lv rv')) (((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H) ∗
        storeRepr N st2.store B ∗ consoleOwn st2.out ∗ Stdio.stdioOwn ∗
        interpCtxE inp d (errAny inp) ∗ strOwn (R4 10).toNat (strRender st2.store lv) ∗
        blockOwn ((s + 18446744073709550528#64).toNat - (evalNeed (.binary .add l r) d - 1088))
          (evalNeed (.binary .add l r) d - 1088 - stringifyNeed))
      K ∗
      □ valOf N rv' u0 u1 u2 ∗ □ dispRes st2.store rv' ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [Hv2 Hd2]
    · iframe Hcode Hro Hfb Hst Hslot Hh Hsto Hcon Hio Hctx Hx Hslack; iexact Hk
    · iframe Hv2 Hbin Hat; iexact Hd2
  intro F'
  refine CatTail_run4 (s := s) hlive hsf hs' hs2 hs3 ?_ ?_
  · cat_keep [hkeep4]
  intros
  apply swp_closeM
  intro Mt5 hMt5
  have hcs5 : CatSaved Mt5 s ret rv :=
    ⟨by rw [hMt5]; ix_saved hcs4.saved using hoff, by rw [hMt5]; e2_fwd hoff; exact hcs4.s5⟩
  have hb0 : ldv .ld Mt5 (s + 18446744073709550528#64 + 64#64).toNat = u0 := by
    rw [hMt5]; e2_fwd hoff; rw [ldv_agree (fun j hj => hM4 _ (by simp only [VsaIris.InExt]; omega)
      (by rw [hoff 64 (by decide)]; simp only [VsaIris.InExt]; omega))]
    rw [hMt3]; e2_fwd hoff; cat_mem
  have hb8 : ldv .ld Mt5 ((s + 18446744073709550528#64 + 64#64).toNat + 8) = u1 := by
    rw [hMt5]; e2_fwd hoff; rw [ldv_agree (fun j hj => hM4 _ (by simp only [VsaIris.InExt]; omega)
      (by rw [hoff 64 (by decide)]; simp only [VsaIris.InExt]; omega))]
    rw [hMt3]; e2_fwd hoff; cat_mem
  have hb16 : ldv .ld Mt5 ((s + 18446744073709550528#64 + 64#64).toNat + 16) = u2 := by
    rw [hMt5]; e2_fwd hoff; rw [ldv_agree (fun j hj => hM4 _ (by simp only [VsaIris.InExt]; omega)
      (by rw [hoff 64 (by decide)]; simp only [VsaIris.InExt]; omega))]
    rw [hMt3]; e2_fwd hoff; cat_mem
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hsto, Hcon, Hio, Hctx, Hx, Hslack⟩, Hk⟩, #Hv2,
    #Hd2, #Hbin, #Hat⟩, Hms⟩
  have hS64 : ∀ k, InExt ((s + 18446744073709550528#64 + 64#64).toNat, 24) k →
      InExt (s.toNat - 1088, 1088) k := by
    intro k hk; rw [hoff 64 (by decide)] at hk; simp only [VsaIris.InExt] at hk ⊢; omega
  ihave ⟨Hms, HA⟩ := ms_carveWords N hS64 hb0 hb8 hb16 $$ [Hms Hv2]
  · iframe Hms Hv2

  have gS := evalCallGeom (nc := stringifyNeed) (o := 64) hsg
    (by have := evalNeed_binary_rtErr .add l r d
        unfold Newlib.RtErr.rtErrNeed Newlib.snprintfNeed at this
        unfold stringifyNeed Newlib.snprintfNeed; omega) (by decide) (by decide)
  ihave Hs2 := hsgy $$ %(s + 18446744073709550528#64 + 64#64) %(s + 18446744073709550528#64) %rv'
    %st2.store %(catBufCost st2.store lv rv')
    %(((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H)
    %(stringifyCost st2.store rv') %st2.out
  iapply ms_callHelperA Wp (i := 0x80003a68)
    (jalx_80003a68 live (fun p hp => hlive _ (interp_code_80003a68 p hp)))
    interp_code_80003a68 (by decide)
  iframe Hs2 Hcode Hms
  isplitl []
  · ipureintro; exact ⟨by ix_reg, by ix_reg; cat_keep [hkeep4]⟩
  isplitl [HA Hh Hio Hcon Hst]
  · unfold stringifyPre stackAt; simp only [Regime.plus_add']
    rw [show catBufCost st2.store lv rv' + stringifyCost st2.store rv' =
      stringifyCost st2.store rv' + catBufCost st2.store lv rv' by omega]
    iframe HA Hd2 Hbin Hh Hio Hcon Hst
    ipureintro; exact ⟨⟨gS.slotGeom, stringifyChg st2.store rv'⟩, gS.child⟩
  isplit
  rotate_left
  · iintro ⟨%hρ, HA, Hsl⟩ HS
    obtain ⟨Core, hE, hab⟩ := hoom hρ
    unfold AbortK at hab
    ihave ⟨-, Hk⟩ := hab $$ Hk
    iapply Hk
    iframe Hslot
    iapply abortAt_of_stringify hE.core hsg (by unfold stringifyNeed Newlib.snprintfNeed; omega) hS64
    iframe HA Hsl HS Hslack
  iintro %R6 %hkeep6 Hpost Hms
  unfold stringifyPost stackAt
  icases Hpost with ⟨HA, Hy, %hf2, Hh, Hio, Hcon, Hst, -⟩
  ihave ⟨%M6, Hms, %hM6⟩ := ms_uncarveVal N hS64 $$ [Hms HA]
  · iframe Hms HA
  have hcs6 : CatSaved M6 s ret rv := hcs5.agree fun k h1 h2 =>
    hM6 k (by simp only [VsaIris.InExt]; omega)
      (by rw [hoff 64 (by decide)]; simp only [VsaIris.InExt]; omega)

#ix_piece catTail_p5 from catTail_p4 by

  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64) stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB (ρ.plus (catBufCost st2.store lv rv')) (((R6 10).toNat, (strRender st2.store rv').toList.length + 1) ::
          ((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H) ∗
        catRest N inp d st2 H B ∗ strOwn (R4 10).toNat (strRender st2.store lv) ∗ strOwn (R6 10).toNat (strRender st2.store rv') ∗ blockOwn ((s + 18446744073709550528#64).toNat - (evalNeed (.binary .add l r) d - 1088))
          (evalNeed (.binary .add l r) d - 1088 - stringifyNeed))
      K ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF catRest; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hsto Hcon Hio Hctx Hx Hy Hslack Hk
    iframe Hbin Hat; ipureintro; exact hB
  intro F'
  refine CatTail_run5 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · cat_keep [hkeep6, hkeep4]
  intros
  apply swp_closeM
  intro Mt7 hMt7
  have hcs7 : CatSaved Mt7 s ret rv := hcs6.eq hMt7
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hrest, Hx, Hy, Hslack⟩, Hk⟩, #Hbin, #Hat⟩, Hms⟩
  ihave Hsl1 := hsl $$ %(R4 10) %(strRender st2.store lv) %(ρ.plus (catBufCost st2.store lv rv')) %(((R6 10).toNat, (strRender st2.store rv').toList.length + 1) ::
          ((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H)
  iapply ms_callHelper Wp (i := 0x80003a78) (entry := strlenPC)
    (jalx_80003a78 live (fun p hp => hlive _ (interp_code_80003a78 p hp)))
    interp_code_80003a78 (by decide)
  unfold strlenHeapSpec
  iframe Hsl1 Hcode Hms
  isplitl []
  · ipureintro; ix_reg; ix_keep [hkeep6]
  isplitl [Hx Hh]
  · iframe Hbin Hx Hh; ipureintro; exact ⟨List.mem_cons_of_mem _ List.mem_cons_self, hf1.2⟩
  iintro %R8 %hkeep8 ⟨%hla, Hx, Hh⟩ Hms

#ix_piece catTail_p6 from catTail_p5 by

  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64) stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB (ρ.plus (catBufCost st2.store lv rv')) (((R6 10).toNat, (strRender st2.store rv').toList.length + 1) ::
          ((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H) ∗
        catRest N inp d st2 H B ∗ strOwn (R4 10).toNat (strRender st2.store lv) ∗ strOwn (R6 10).toNat (strRender st2.store rv') ∗ blockOwn ((s + 18446744073709550528#64).toNat - (evalNeed (.binary .add l r) d - 1088))
          (evalNeed (.binary .add l r) d - 1088 - stringifyNeed))
      K ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hrest Hx Hy Hslack Hk Hbin Hat
  intro F'
  refine CatTail_run6 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · cat_keep [hkeep8, hkeep6, hkeep4]
  intros
  apply swp_closeM
  intro Mt9 hMt9
  have hcs9 : CatSaved Mt9 s ret rv := hcs7.eq hMt9
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hrest, Hx, Hy, Hslack⟩, Hk⟩, #Hbin, #Hat⟩, Hms⟩
  ihave Hsl2 := hsl $$ %(R6 10) %(strRender st2.store rv') %(ρ.plus (catBufCost st2.store lv rv')) %(((R6 10).toNat, (strRender st2.store rv').toList.length + 1) ::
          ((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H)
  iapply ms_callHelper Wp (i := 0x80003a84) (entry := strlenPC)
    (jalx_80003a84 live (fun p hp => hlive _ (interp_code_80003a84 p hp)))
    interp_code_80003a84 (by decide)
  unfold strlenHeapSpec
  iframe Hsl2 Hcode Hms
  isplitl []
  · ipureintro; ix_reg; ix_keep [hkeep8]
  isplitl [Hy Hh]
  · iframe Hbin Hy Hh; ipureintro; exact ⟨List.mem_cons_self, hf2.2⟩
  iintro %R10 %hkeep10 ⟨%hlb, Hy, Hh⟩ Hms

#ix_piece catTail_p7 from catTail_p6 by

  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64) stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB (ρ.plus (catBufCost st2.store lv rv')) (((R6 10).toNat, (strRender st2.store rv').toList.length + 1) ::
          ((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H) ∗
        catRest N inp d st2 H B ∗ strOwn (R4 10).toNat (strRender st2.store lv) ∗ strOwn (R6 10).toNat (strRender st2.store rv') ∗ blockOwn ((s + 18446744073709550528#64).toNat - (evalNeed (.binary .add l r) d - 1088))
          (evalNeed (.binary .add l r) d - 1088 - stringifyNeed))
      K ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hrest Hx Hy Hslack Hk Hbin Hat
  intro F'
  refine CatTail_run7 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · cat_keep [hkeep10, hkeep8, hkeep6, hkeep4]
  intros
  apply swp_closeM
  intro Mt11 hMt11
  have hcs11 : CatSaved Mt11 s ret rv := hcs9.eq hMt11
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hrest, Hx, Hy, Hslack⟩, Hk⟩, #Hbin, #Hat⟩, Hms⟩
  have ha1 := fresh_arena hf1.1
  have ha2 := fresh_arena hf2.1
  have h18 : R10 18 = BitVec.ofNat 64 (strRender st2.store lv).length := by
    rw [hkeep10 18 (by decide) (by decide)]; ix_reg; exact hla
  have hN : (R10 18 + R10 10 + 1#64).toNat = (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1 := by
    rw [h18, hlb, ← String.length_toList, ← String.length_toList]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
  ihave ⟨Hslack2, Hst⟩ := stackScratch_narrow (s := (s + 18446744073709550528#64)) (n := stringifyNeed) (m := allocHeadroom)
    (by rw [hsf]; unfold stringifyNeed Newlib.snprintfNeed; omega)
    (by unfold stringifyNeed allocHeadroom Newlib.snprintfNeed; omega) $$ Hst
  iapply ms_callMallocN A Wp (i := 0x80003a90)
    (jalx_80003a90 live (fun p hp => hlive _ (interp_code_80003a90 p hp))) interp_code_80003a90
    (by decide) ρ (((R6 10).toNat, (strRender st2.store rv').toList.length + 1) ::
          ((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H) ((strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) (catBufCost st2.store lv rv')
    (catBufChg st2.store lv rv')
  iframe Hat Hcode Hms Hst
  isplitl []
  · ipureintro
    refine ⟨by ix_reg; exact hN, by ix_reg; cat_keep [hkeep10, hkeep8, hkeep6, hkeep4], ?_⟩
    exact ⟨by rw [hsf]; unfold Vsa.Sim.tohostAddr allocHeadroom; omega, by rw [hsf]; omega,
      by rw [hsf]; omega⟩
  isplitl [Hh]
  · iexact Hh
  iintro %R12 %hkeep12 Hst Hres Hms
  ihave Hst := stackScratch_widen (s := (s + 18446744073709550528#64)) (n := stringifyNeed) (m := allocHeadroom)
    (by rw [hsf]; unfold stringifyNeed Newlib.snprintfNeed; omega)
    (by unfold stringifyNeed allocHeadroom Newlib.snprintfNeed; omega) $$ [Hslack2 Hst]
  · iframe Hslack2 Hst
  unfold mallocRes
  icases Hres with (⟨%⟨hq0, hρ⟩, Hh0⟩ | ⟨%hf3, Hh, Hblk⟩)
  · obtain ⟨Core, hE, hab⟩ := hoom hρ
    unfold AbortK at hab
    subst hρ
    ihave ⟨#HE, Hk⟩ := hab $$ Hk
    ihave ⟨Herr, -⟩ := ErrnoOwn.heapRes_errno _ _ $$ Hh0
    ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
    · iframe Hcode Hro
    iapply wp_swpF Wp (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64) stringifyNeed (slot24 sret.toNat)
        iprop(Stdio.errnoOwn ∗ catRest N inp d st2 H B ∗ blockOwn ((s + 18446744073709550528#64).toNat - (evalNeed (.binary .add l r) d - 1088))
          (evalNeed (.binary .add l r) d - 1088 - stringifyNeed))
        iprop(abortAt Core s (evalNeed (.binary .add l r) d) ∗ slot24 sret.toNat -∗ Wp.W Φ) ∗
        binImg))
    rotate_left
    · unfold evalArmF; iframe Hdv Hms Hbin; iframe Hcode Hro Hfb Hst Hslot Herr Hrest Hslack Hk
    intro F'
    refine CatTail_run8z (s := s) hlive hsf hs' hs2 hs3 ?_ ?_ ?_
    · ix_reg; cat_keep [hkeep12, hkeep10, hkeep8, hkeep6, hkeep4]
    · ix_reg; exact hq0
    intros
    apply swp_closeF
    unfold F' evalArmF
    iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Herr, Hrest, Hslack⟩, Hk⟩, #Hbin⟩, Hms⟩
    unfold catRest
    icases Hrest with ⟨-, Hcon, Hio, -, -⟩
    ihave Hst := stackScratch_widen (s := (s + 18446744073709550528#64)) (n := evalNeed (.binary .add l r) d - 1088)
      (m := stringifyNeed) (by rw [hsf]; omega) (by unfold stringifyNeed Newlib.snprintfNeed; omega)
      $$ [Hslack Hst]
    · iframe Hslack Hst
    iapply ms_evalOom Wp hE hsg (by unfold fwriteNeed; omega)
    iframe Hcode Hbin Hms Hst Hio Herr Hcon
    isplitl []
    · ipureintro; ix_reg; cat_keep [hkeep12, hkeep10, hkeep8, hkeep6, hkeep4]
    iintro HA
    iapply Hk
    iframe HA Hslot

#ix_piece catTail_p8 from catTail_p7 by

  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64) stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB ρ (((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) ::
          (((R6 10).toNat, (strRender st2.store rv').toList.length + 1) ::
          ((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H)) ∗ blockOwn (R12 10).toNat ((strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) ∗
        catRest N inp d st2 H B ∗ strOwn (R4 10).toNat (strRender st2.store lv) ∗ strOwn (R6 10).toNat (strRender st2.store rv') ∗ blockOwn ((s + 18446744073709550528#64).toNat - (evalNeed (.binary .add l r) d - 1088))
          (evalNeed (.binary .add l r) d - 1088 - stringifyNeed))
      K ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hblk Hrest Hx Hy Hslack Hk Hbin Hat
  intro F'
  refine CatTail_run8 (s := s) hlive hsf hs' hs2 hs3 ?_ ?_ ?_
  · ix_reg; cat_keep [hkeep12, hkeep10, hkeep8, hkeep6, hkeep4]
  · ix_reg; exact fun h => hf3.1.nonzero (by rw [h]; rfl)
  intros
  apply swp_closeM
  intro Mt13 hMt13
  have hcs13 : CatSaved Mt13 s ret rv :=
    ⟨by rw [hMt13]; ix_saved hcs11.saved using hoff, by rw [hMt13]; e2_fwd hoff; exact hcs11.s5⟩
  have hs4 : ldv .ld Mt13 (s.toNat - 1088 + 1040) = rv 20 := by
    rw [hMt13]; e2_fwd hoff; cat_keep [hkeep12, hkeep10, hkeep8, hkeep6, hkeep4]
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hblk, Hrest, Hx, Hy, Hslack⟩, Hk⟩, #Hbin, #Hat⟩, Hms⟩
  have ha1 := fresh_arena hf1.1
  have ha2 := fresh_arena hf2.1
  have ha3 := fresh_arena hf3.1
  ihave ⟨Hb1, Hb2⟩ := blockOwn_split (R12 10).toNat ((strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) (strRender st2.store lv).toList.length ((R12 10).toNat + (strRender st2.store lv).toList.length) ((strRender st2.store rv').toList.length + 1)
    (by omega) rfl (by omega) $$ Hblk
  ihave ⟨%img1, %hc1, Hx1, Hx0⟩ := strOwn_cut (R4 10).toNat (strRender st2.store lv) $$ Hx
  iapply ms_callMemcpyOwned Wp hmc (i := 0x80003aa8)
    (jalx_80003aa8 live (fun p hp => hlive _ (interp_code_80003aa8 p hp))) interp_code_80003aa8
    (by decide) (dst := (R12 10)) (src := (R4 10)) (n := (strRender st2.store lv).toList.length) (img := img1)
    ⟨by omega, by omega, .inr (by unfold htifLo; omega)⟩ (by unfold htifLo; omega)
    ⟨by omega, by omega, .inr (by unfold htifLo; omega)⟩
  iframe Hcode Hbin Hms Hb1 Hx1
  isplitl []
  · ipureintro
    refine ⟨by ix_reg, by ix_reg; ix_keep [hkeep12, hkeep10, hkeep8, hkeep6], ?_⟩
    ix_reg; rw [hkeep12 18 (by decide) (by decide)]; ix_reg; rw [h18, String.length_toList]

#ix_piece catTail_p9 from catTail_p8 by

  iintro %R14 %hkeep14 %h14 Hd Hx1 Hms
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64) stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB ρ (((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) ::
          (((R6 10).toNat, (strRender st2.store rv').toList.length + 1) ::
          ((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H)) ∗ blockOwn ((R12 10).toNat + (strRender st2.store lv).toList.length) ((strRender st2.store rv').toList.length + 1) ∗
        ownImg (InExt ((R12 10).toNat, (strRender st2.store lv).toList.length)) (fun a => img1 (a - (R12 10).toNat + (R4 10).toNat)) ∗
        ownImg (InExt ((R4 10).toNat, (strRender st2.store lv).toList.length)) img1 ∗ ownImg (InExt ((R4 10).toNat + (strRender st2.store lv).toList.length, 1)) img1 ∗
        catRest N inp d st2 H B ∗ strOwn (R6 10).toNat (strRender st2.store rv') ∗ blockOwn ((s + 18446744073709550528#64).toNat - (evalNeed (.binary .add l r) d - 1088))
          (evalNeed (.binary .add l r) d - 1088 - stringifyNeed))
      K ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF
    iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hb2 Hd Hx1 Hx0 Hrest Hy Hslack Hk Hbin Hat
  intro F'
  refine CatTail_run9 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · cat_keep [hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4]
  intros
  apply swp_closeM
  intro Mt15 hMt15
  have hcs15 : CatSaved Mt15 s ret rv := hcs13.eq hMt15
  have hs4' : ldv .ld Mt15 (s.toNat - 1088 + 1040) = rv 20 := by rw [hMt15]; exact hs4
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hb2, Hd, Hx1, Hx0, Hrest, Hy, Hslack⟩, Hk⟩, #Hbin,
    #Hat⟩, Hms⟩
  have ha1 := fresh_arena hf1.1
  have ha2 := fresh_arena hf2.1
  have ha3 := fresh_arena hf3.1
  have hd : ((R12 10) + BitVec.ofNat 64 (strRender st2.store lv).toList.length).toNat = (R12 10).toNat + (strRender st2.store lv).toList.length := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
  ihave Hsc1 := hsc $$ %((R12 10) + BitVec.ofNat 64 (strRender st2.store lv).toList.length) %(R6 10) %(strRender st2.store rv') %ρ %(((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) ::
          (((R6 10).toNat, (strRender st2.store rv').toList.length + 1) ::
          ((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H))
  unfold strcpyHeapSpec
  iapply ms_callHelper Wp (i := 0x80003ab4) (entry := strcpyPC)
    (jalx_80003ab4 live (fun p hp => hlive _ (interp_code_80003ab4 p hp)))
    interp_code_80003ab4 (by decide)
  iframe Hsc1 Hcode Hms
  isplitl []
  · ipureintro
    refine ⟨?_, by ix_reg; ix_keep [hkeep14, hkeep12, hkeep10, hkeep8, hkeep6]⟩
    ix_reg; rw [hkeep14 8 (by decide) (by decide), hkeep14 18 (by decide) (by decide)]; ix_reg
    rw [hkeep12 18 (by decide) (by decide)]; ix_reg; rw [h18, String.length_toList]
  isplitl [Hb2 Hy Hh]
  · rw [hd]; iframe Hbin Hb2 Hy Hh
    ipureintro
    exact ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self, hf2.2⟩,
      ⟨by omega, by omega, .inr (by unfold htifLo; omega)⟩, by unfold htifLo; omega⟩
  iintro %R16 %hkeep16 ⟨⟨%img2, Hz, %hc2⟩, Hy, Hh⟩ Hms
  rw [hd] at hc2
  ihave Hs := ownImg_cat (q := (R12 10).toNat) (q1 := (R4 10).toNat) img1 img2 hc1 hc2 $$ [Hd Hz]
  · rw [hd]; iframe Hd Hz

#ix_piece catTail_p10 from catTail_p9 by

  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64) stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB ρ (((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) ::
          (((R6 10).toNat, (strRender st2.store rv').toList.length + 1) ::
          ((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H)) ∗ strOwn (R12 10).toNat ((strRender st2.store lv) ++ (strRender st2.store rv')) ∗
        ownImg (InExt ((R4 10).toNat, (strRender st2.store lv).toList.length)) img1 ∗ ownImg (InExt ((R4 10).toNat + (strRender st2.store lv).toList.length, 1)) img1 ∗
        catRest N inp d st2 H B ∗ strOwn (R6 10).toNat (strRender st2.store rv') ∗ blockOwn ((s + 18446744073709550528#64).toNat - (evalNeed (.binary .add l r) d - 1088))
          (evalNeed (.binary .add l r) d - 1088 - stringifyNeed))
      K ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF
    iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hs Hx1 Hx0 Hrest Hy Hslack Hk Hbin Hat
  intro F'
  refine CatTail_run10 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · cat_keep [hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4]
  intros
  apply swp_closeM
  intro Mt17 hMt17
  have hcs17 : CatSaved Mt17 s ret rv := hcs15.eq hMt17
  have hs4 : ldv .ld Mt17 (s.toNat - 1088 + 1040) = rv 20 := by rw [hMt17]; exact hs4'
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hs, Hx1, Hx0, Hrest, Hy, Hslack⟩, Hk⟩, #Hbin,
    #Hat⟩, Hms⟩
  ihave Hq1 := blockOwn_of_cut (R4 10).toNat (strRender st2.store lv).toList.length img1 img1 $$ [Hx1 Hx0]
  · iframe Hx1 Hx0
  ihave Hh := heapRes_congr (H := (((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) ::
          (((R6 10).toNat, (strRender st2.store rv').toList.length + 1) ::
          ((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H)))
    (H' := ((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: ((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) :: ((R6 10).toNat, (strRender st2.store rv').toList.length + 1) :: H)
    (List.perm_middle (l₁ := [((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1), ((R6 10).toNat, (strRender st2.store rv').toList.length + 1)])) $$ Hh
  ihave ⟨Hslack2, Hst⟩ := stackScratch_narrow (s := (s + 18446744073709550528#64)) (n := stringifyNeed) (m := allocHeadroom)
    (by rw [hsf]; unfold stringifyNeed Newlib.snprintfNeed; omega)
    (by unfold stringifyNeed allocHeadroom Newlib.snprintfNeed; omega) $$ Hst
  iapply ms_callFreeN A Wp (i := 0x80003abc)
    (jalx_80003abc live (fun p hp => hlive _ (interp_code_80003abc p hp))) interp_code_80003abc
    (by decide) ρ (((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) :: ((R6 10).toNat, (strRender st2.store rv').toList.length + 1) :: H) (R4 10) ((strRender st2.store lv).toList.length + 1)
  iframe Hat Hcode Hms Hst Hq1 Hh
  isplitl []
  · ipureintro
    refine ⟨by ix_reg; ix_keep [hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6],
      by ix_reg; cat_keep [hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4], ?_⟩
    exact ⟨by rw [hsf]; unfold Vsa.Sim.tohostAddr allocHeadroom; omega, by rw [hsf]; omega,
      by rw [hsf]; omega⟩
  iintro %R17 %hkeep17 Hst Hh Hms
  ihave Hst := stackScratch_widen (s := (s + 18446744073709550528#64)) (n := stringifyNeed) (m := allocHeadroom)
    (by rw [hsf]; unfold stringifyNeed Newlib.snprintfNeed; omega)
    (by unfold stringifyNeed allocHeadroom Newlib.snprintfNeed; omega) $$ [Hslack2 Hst]
  · iframe Hslack2 Hst

#ix_piece catTail_p11 from catTail_p10 by

  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64) stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB ρ
          (((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) :: ((R6 10).toNat, (strRender st2.store rv').toList.length + 1) :: H) ∗
        strOwn (R12 10).toNat ((strRender st2.store lv) ++ (strRender st2.store rv')) ∗ catRest N inp d st2 H B ∗ strOwn (R6 10).toNat (strRender st2.store rv') ∗ blockOwn ((s + 18446744073709550528#64).toNat - (evalNeed (.binary .add l r) d - 1088))
          (evalNeed (.binary .add l r) d - 1088 - stringifyNeed))
      K ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hs Hrest Hy Hslack Hk Hbin Hat
  intro F'
  refine CatTail_run11 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · cat_keep [hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4]
  intros
  apply swp_closeM
  intro Mt19 hMt19
  have hcs19 : CatSaved Mt19 s ret rv := hcs17.eq hMt19
  have hs4' : ldv .ld Mt19 (s.toNat - 1088 + 1040) = rv 20 := by rw [hMt19]; exact hs4
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hs, Hrest, Hy, Hslack⟩, Hk⟩, #Hbin, #Hat⟩, Hms⟩
  ihave ⟨%img3, %-, Hy1, Hy0⟩ := strOwn_cut (R6 10).toNat (strRender st2.store rv') $$ Hy
  ihave Hq2 := blockOwn_of_cut (R6 10).toNat (strRender st2.store rv').toList.length img3 img3 $$ [Hy1 Hy0]
  · iframe Hy1 Hy0
  ihave Hh := heapRes_congr (H := ((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) :: ((R6 10).toNat, (strRender st2.store rv').toList.length + 1) :: H)
    (H' := ((R6 10).toNat, (strRender st2.store rv').toList.length + 1) :: ((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) :: H)
    (List.Perm.swap ((R6 10).toNat, (strRender st2.store rv').toList.length + 1) ((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) H) $$ Hh
  ihave ⟨Hslack2, Hst⟩ := stackScratch_narrow (s := (s + 18446744073709550528#64)) (n := stringifyNeed) (m := allocHeadroom)
    (by rw [hsf]; unfold stringifyNeed Newlib.snprintfNeed; omega)
    (by unfold stringifyNeed allocHeadroom Newlib.snprintfNeed; omega) $$ Hst
  iapply ms_callFreeN A Wp (i := 0x80003ac4)
    (jalx_80003ac4 live (fun p hp => hlive _ (interp_code_80003ac4 p hp))) interp_code_80003ac4
    (by decide) ρ (((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) :: H) (R6 10) ((strRender st2.store rv').toList.length + 1)
  iframe Hat Hcode Hms Hst Hq2 Hh
  isplitl []
  · ipureintro
    refine ⟨by ix_reg; ix_keep [hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6],
      by ix_reg; cat_keep [hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4], ?_⟩
    exact ⟨by rw [hsf]; unfold Vsa.Sim.tohostAddr allocHeadroom; omega, by rw [hsf]; omega,
      by rw [hsf]; omega⟩
  iintro %R18 %hkeep18 Hst Hh Hms
  ihave Hst := stackScratch_widen (s := (s + 18446744073709550528#64)) (n := stringifyNeed) (m := allocHeadroom)
    (by rw [hsf]; unfold stringifyNeed Newlib.snprintfNeed; omega)
    (by unfold stringifyNeed allocHeadroom Newlib.snprintfNeed; omega) $$ [Hslack2 Hst]
  · iframe Hslack2 Hst

#ix_piece catTail_p12 from catTail_p11 by

  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64) stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB ρ (((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) :: H) ∗
        strOwn (R12 10).toNat ((strRender st2.store lv) ++ (strRender st2.store rv')) ∗ catRest N inp d st2 H B ∗ blockOwn ((s + 18446744073709550528#64).toNat - (evalNeed (.binary .add l r) d - 1088))
          (evalNeed (.binary .add l r) d - 1088 - stringifyNeed))
      K ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hs Hrest Hslack Hk Hbin Hat
  intro F'
  refine CatTail_run12 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · cat_keep [hkeep18, hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4]
  intros
  apply swp_closeM
  intro Mt21 hMt21
  have hcs21 : CatSaved Mt21 s ret rv := hcs19.eq hMt21
  have hs4 : ldv .ld Mt21 (s.toNat - 1088 + 1040) = rv 20 := by rw [hMt21]; exact hs4'
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hs, Hrest, Hslack⟩, Hk⟩, #Hbin, #Hat⟩, Hms⟩
  have hlen : ((strRender st2.store lv) ++ (strRender st2.store rv')).toList.length = (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length := by
    rw [String.toList_append, List.length_append]
  have hf3' : FreshBlock vsaLayoutP (((R6 10).toNat, (strRender st2.store rv').toList.length + 1) ::
          ((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H) (R12 10).toNat (((strRender st2.store lv) ++ (strRender st2.store rv')).toList.length + 1) := by
    rw [hlen]; exact hf3.1
  iapply Wp.fupd
  imod strAt_of_fresh hf3' $$ Hs with #Hs
  imodintro
  ihave Hvs := hvs $$ %sret %(R12 10) %((strRender st2.store lv) ++ (strRender st2.store rv'))
  unfold valueStrSpec
  iapply ms_callHelper Wp (i := 0x80003ad0)
    (jalx_80003ad0 live (fun p hp => hlive _ (interp_code_80003ad0 p hp)))
    interp_code_80003ad0 (by decide)
  iframe Hvs Hcode Hms
  isplitl []
  · ipureintro
    exact ⟨by ix_reg; cat_keep [hkeep18, hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6,
      hkeep4],
      by ix_reg; ix_keep [hkeep18, hkeep17, hkeep16, hkeep14, hkeep12]⟩
  isplitl [Hslot]
  · iframe Hslot Hs; ipureintro; exact ⟨hslg, fun h => hf3.1.nonzero h⟩
  iintro %R20 %hkeep20 Hval Hms

#ix_piece catTail_p13 from catTail_p12 by

  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := evalArmF P m env aE (s + 18446744073709550528#64) stringifyNeed
      (valAt N sret.toNat (.str ((strRender st2.store lv) ++ (strRender st2.store rv'))))
      iprop(heapRes vsaLayoutP vsaRoomB ρ (((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) :: H) ∗
        catRest N inp d st2 H B ∗ blockOwn ((s + 18446744073709550528#64).toNat - (evalNeed (.binary .add l r) d - 1088))
          (evalNeed (.binary .add l r) d - 1088 - stringifyNeed))
      K)
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hval Hh Hrest Hslack Hk
  intro F'
  refine CatTail_run13 (aX := aX) (s := s) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) (v19 := rv 19) (v20 := rv 20) (v21 := rv 21) hlive hsf hs' hs2 hs3 hal ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_
  · cat_keep [hkeep20, hkeep18, hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4]
  · rw [hoff _ (by decide)]; exact hcs21.saved.ra
  · rw [hoff _ (by decide)]; exact hcs21.saved.s0
  · rw [hoff _ (by decide)]; exact hcs21.saved.s1
  · rw [hoff _ (by decide)]; exact hcs21.saved.s2
  · rw [hoff _ (by decide)]; exact hcs21.saved.s3
  · rw [hoff _ (by decide)]; exact hs4
  · rw [hoff _ (by decide)]; exact hcs21.s5
  intros
  apply swp_closeF
  unfold F' evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hval, ⟨Hh, Hrest, Hslack⟩, Hk⟩, Hms⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave Hst := stackScratch_widen (s := (s + 18446744073709550528#64)) (n := evalNeed (.binary .add l r) d - 1088)
    (m := stringifyNeed) (by rw [hsf]; omega)
    (by have := evalNeed_binary_rtErr .add l r d
        unfold Newlib.RtErr.rtErrNeed Newlib.snprintfNeed at this
        unfold stringifyNeed Newlib.snprintfNeed; omega) $$ [Hslack Hst]
  · iframe Hslack Hst
  ihave Hst := evalFrame_join hsg.le hneed $$ [Hst HS]
  · iframe Hst HS
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  ihave Hw := world_of_catRest N inp d st2 ρ (H' := (((R12 10).toNat, (strRender st2.store lv).toList.length + (strRender st2.store rv').toList.length + 1) :: H))
    (fun b hb => List.mem_cons_of_mem _ hb) $$ [Hh Hrest]
  · iframe Hh Hrest
  rw [strRender_eq, strRender_eq] at *
  iapply hexit.pure
  iframe Hpc Hra Hregs Hst Hval Hw Hk
  ipureintro
  intro x hx
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans mid.sp.symm
  all_goals cat_keep [hkeep20, hkeep18, hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6,
    hkeep4]

#ix_chain catTail := [catTail_p1, catTail_p4, catTail_p5, catTail_p6, catTail_p7, catTail_p8,
  catTail_p9, catTail_p10, catTail_p11, catTail_p12, catTail_p13]

end VsaIris.Interp
