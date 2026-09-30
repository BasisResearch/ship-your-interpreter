import VsaIris.Interp.BinArm

/-!
Arm-level combinators shared by the `eval_expr` case proofs, for any `MachWP`
(total `twpW` or partial `wpW`).

* `ArmAt Wp Φ F pc R S Mt`: the frame `F` and the machine at `pc` suffice.
* `MRun`: a reflected machine segment in continuation form with a named post.
* `ArmAt.seg` / `ArmAt.run`: one machine segment under an `evalArmF` frame.
* `JalAt`: a generated `jal` site (exec lemma, code footprint, alignment).
* `ExitK`: what the arm's caller continuation accepts at the return;
  `ArmAt.finish` closes an arm at the return address.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-- A generated `jal` site calling `entry`. -/
structure JalAt (entry : BitVec 64) where
  i : Nat
  code : List (BitVec 8)
  exec : ∀ live : Nat → Prop, (∀ p ∈ interpText, live p.1) → JalExec (vsaModel live) i code entry
  mem : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText
  al : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0

/-- `jal_site% 0xX` builds the `JalAt` of the call at `X` (`step% jalx X`) and the image
    footprint `interp_code`. -/
macro "jal_site% " n:num : term =>
  `(({ i := _, code := _,
       exec := fun live h => (step% jalx $n) live (fun p hp => h _ ((interp_code (by decide)) p hp)),
       mem := interp_code (by decide), al := by decide } : JalAt _))

abbrev hiSaved : List Nat := [20, 21, 22, 23, 24, 25, 26, 27]

/-- Register frame kept by a machine segment: the stack pointer and `s4`–`s11`. -/
structure HiKeep (R R' : Nat → BitVec 64) : Prop where
  sp : R' 2 = R 2
  hi : ∀ x ∈ hiSaved, R' x = R x

theorem HiKeep.trans {R R' R'' : Nat → BitVec 64} (h1 : HiKeep R R') (h2 : HiKeep R' R'') :
    HiKeep R R'' := ⟨h2.sp.trans h1.sp, fun x hx => (h2.hi x hx).trans (h1.hi x hx)⟩

theorem hi_fRegs : ∀ x ∈ hiSaved, x ∈ fRegs := by decide

theorem hi_callee : ∀ x ∈ hiSaved, x ∈ calleeSaved := by decide

theorem mem_fRegs_of_hi {x : Nat} (hx : x ∈ hiSaved) : x ∈ fRegs := hi_fRegs x hx

theorem mem_callee_of_hi {x : Nat} (hx : x ∈ hiSaved) : x ∈ calleeSaved := hi_callee x hx

theorem HiKeep.of_helper {clob : List Nat} {R R' : Nat → BitVec 64}
    (h : ∀ x ∈ fRegs, x ∉ clob → R' x = R x) (h2 : 2 ∉ clob) (hc : ∀ x ∈ hiSaved, x ∉ clob) :
    HiKeep R R' :=
  ⟨h 2 (by decide) h2, fun x hx => h x (mem_fRegs_of_hi hx) (hc x hx)⟩

theorem HiKeep.of_keep {R R' : Nat → BitVec 64} (h : KeepRegs calleeSaved R R') : HiKeep R R' :=
  ⟨h 2 (by decide), fun x hx => h x (mem_callee_of_hi hx)⟩

theorem HiKeep.upd {R R' : Nat → BitVec 64} (h : HiKeep R R') {x : Nat} (v : BitVec 64)
    (hx : x ≠ 2) (hx' : x ∉ hiSaved) : HiKeep R (upd R' x v) :=
  ⟨by rw [upd_other _ _ (Ne.symm hx)]; exact h.sp, fun y hy => by
    rw [upd_other _ _ (fun e => hx' (by subst e; exact hy))]; exact h.hi y hy⟩

theorem HiKeep.helperRA {clob : List Nat} {R R' : Nat → BitVec 64}
    (h : ∀ x ∈ fRegs, x ∉ clob → R' x = R x) (h2 : 2 ∉ clob) (hc : ∀ x ∈ hiSaved, x ∉ clob)
    (v : BitVec 64) : HiKeep R (Sym.upd R' 1 v) :=
  (HiKeep.of_helper h h2 hc).upd (x := 1) v (by decide) (by decide)

/-- Post of a function epilogue: the saved registers are restored and `s4`–`s11` kept. -/
structure EpiPost (R R' : Nat → BitVec 64) (s ret v8 v9 v18 v19 : BitVec 64) : Prop where
  ra : R' 1 = ret
  sp : R' 2 = s
  s0 : R' 8 = v8
  s1 : R' 9 = v9
  s2 : R' 18 = v18
  s3 : R' 19 = v19
  hi : ∀ x ∈ hiSaved, R' x = R x

theorem EpiPost.keep {R R' rv : Nat → BitVec 64} {s ret : BitVec 64}
    (he : EpiPost R R' s ret (rv 8) (rv 9) (rv 18) (rv 19)) (hk : ∀ x ∈ hiSaved, R x = rv x)
    (hsp : rv 2 = s) : KeepRegs calleeSaved rv R' := by
  intro x hx
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | hx
  · exact he.sp.trans hsp.symm
  · exact he.s0
  · exact he.s1
  · exact he.s2
  · exact he.s3
  · have hx' : x ∈ hiSaved := by simp only [hiSaved, List.mem_cons, List.not_mem_nil]; omega
    exact (he.hi x hx').trans (hk x hx')

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The frame `F` and the machine at `pc` suffice for `Wp.W Φ`. -/
abbrev ArmAt (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (F : IProp GF)
    (pc : BitVec 64) (R : Nat → BitVec 64) (S : Nat → Prop) (Mt : Mem) : Prop :=
  F ∗ ms pc R S Mt ⊢ Wp.W Φ

/-- A reflected machine segment from `pc` to `pc'` in continuation form. -/
def MRun (live : Nat → Prop) (m : Mem) (DA : List Nat) (S : Nat → Prop) (pc pc' : BitVec 64)
    (R : Nat → BitVec 64) (Mt : Mem) (Post : (Nat → BitVec 64) → Mem → Prop) : Prop :=
  ∀ Q, (∀ R' Mt', Post R' Mt' → IW live m DA S Q pc' R' Mt') → IW live m DA S Q pc R Mt

theorem ArmAt.seg (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s' : BitVec 64} {n' : Nat} {Out Wd K : IProp GF}
    {DA : List Nat} (hv : ∀ a ∈ DA, P a ∧ (m[a]?).isSome = true) {S : Nat → Prop}
    {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (h : IW live m DA S (RunK Wp Φ (evalArmF P m env aE s' n' Out Wd K) S) pc R Mt) :
    ArmAt Wp Φ (evalArmF P m env aE s' n' Out Wd K) pc R S Mt := by
  unfold ArmAt
  iintro ⟨HF, Hms⟩
  ihave #Hdv : roOwn roR (interpText ++ dataOf m DA) $$ [HF]
  · unfold evalArmF; icases HF with ⟨#Hcode, #Hro, -⟩
    iapply roOwn_data hv; iframe Hcode Hro
  iapply wp_swpF Wp h
  iframe Hdv HF Hms

theorem ArmAt.run (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s' : BitVec 64} {n' : Nat} {Out Wd K : IProp GF}
    {DA : List Nat} (hv : ∀ a ∈ DA, P a ∧ (m[a]?).isSome = true) {S : Nat → Prop}
    {pc pc' : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {Post : (Nat → BitVec 64) → Mem → Prop}
    (hrun : MRun live m DA S pc pc' R Mt Post)
    (hk : ∀ R' Mt', Post R' Mt' → ArmAt Wp Φ (evalArmF P m env aE s' n' Out Wd K) pc' R' S Mt') :
    ArmAt Wp Φ (evalArmF P m env aE s' n' Out Wd K) pc R S Mt :=
  ArmAt.seg Wp hv (hrun _ fun R' Mt' hp => swp_closeF Wp (hk R' Mt' hp))

/-- Call a helper whose spec is `helperSpec`, from an arm frame whose output resource is
`Out`; the helper consumes `Pre` (split from `Out` by `hpre`) and its post rebuilds `Out'`. -/
theorem ArmAt.callHelper (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {entry : BitVec 64} (J : JalAt entry) (hlive : ∀ p ∈ interpText, live p.1)
    {clob : List Nat} {pins : (Nat → BitVec 64) → Prop} {Pre : IProp GF}
    {Post : (Nat → BitVec 64) → IProp GF}
    (hspec : ⊢ helperSpec (vsaModel live) Wp entry clob pins Pre Post)
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s' : BitVec 64} {n' : Nat} {Out Wd K : IProp GF}
    {Out' : (Nat → BitVec 64) → IProp GF}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} (hpins : pins R)
    (hpre : Out ∗ Wd ∗ K ⊢ Pre ∗ Wd ∗ K) (hpost : ∀ R', Post R' ⊢ Out' R')
    (hk : ∀ R', (∀ x ∈ fRegs, x ∉ clob → R' x = R x) →
      ArmAt Wp Φ (evalArmF P m env aE s' n' (Out' R') Wd K) (BitVec.ofNat 64 (J.i + 4))
        (upd R' 1 (BitVec.ofNat 64 (J.i + 4))) S Mt) :
    ArmAt Wp Φ (evalArmF P m env aE s' n' Out Wd K) (BitVec.ofNat 64 J.i) R S Mt := by
  unfold ArmAt
  iintro ⟨HF, Hms⟩
  unfold evalArmF
  icases HF with ⟨#Hcode, #Hro, #Hfb, Hst, Ho, Hw, HK⟩
  ihave ⟨HPre, Hw, HK⟩ := hpre $$ [Ho Hw HK]
  · iframe Ho Hw HK
  ihave Hsp := hspec
  iapply ms_callHelper Wp (J.exec live hlive) J.mem J.al
  iframe Hsp Hcode Hms HPre
  isplitl []
  · ipureintro; exact hpins
  iintro %R' %hkeep HPost Hms
  ihave HO := hpost R' $$ HPost
  iapply hk R' hkeep
  iframe Hms
  unfold evalArmF
  iframe Hcode Hro Hfb Hst HO Hw HK

/-- Call a helper with a pure post and a persistent precondition read off the frame. -/
theorem ArmAt.callHelperPure (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {entry : BitVec 64} (J : JalAt entry) (hlive : ∀ p ∈ interpText, live p.1)
    {clob : List Nat} {pins : (Nat → BitVec 64) → Prop} {Pre : IProp GF}
    {φ : (Nat → BitVec 64) → Prop}
    (hspec : ⊢ helperSpec (vsaModel live) Wp entry clob pins Pre (fun R' => iprop(⌜φ R'⌝)))
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s' : BitVec 64} {n' : Nat} {Out Wd K : IProp GF}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} (hpins : pins R)
    (hpre : Wd ∗ K ⊢ Wd ∗ K ∗ Pre)
    (hk : ∀ R', (∀ x ∈ fRegs, x ∉ clob → R' x = R x) → φ R' →
      ArmAt Wp Φ (evalArmF P m env aE s' n' Out Wd K) (BitVec.ofNat 64 (J.i + 4))
        (upd R' 1 (BitVec.ofNat 64 (J.i + 4))) S Mt) :
    ArmAt Wp Φ (evalArmF P m env aE s' n' Out Wd K) (BitVec.ofNat 64 J.i) R S Mt := by
  unfold ArmAt
  iintro ⟨HF, Hms⟩
  unfold evalArmF
  icases HF with ⟨#Hcode, #Hro, #Hfb, Hst, Ho, Hw, HK⟩
  ihave ⟨Hw, HK, HPre⟩ := hpre $$ [Hw HK]
  · iframe Hw HK
  ihave Hsp := hspec
  iapply ms_callHelper Wp (J.exec live hlive) J.mem J.al
  iframe Hsp Hcode Hms HPre
  isplitl []
  · ipureintro; exact hpins
  iintro %R' %hkeep %hφ Hms
  iapply hk R' hkeep hφ
  iframe Hms
  unfold evalArmF
  iframe Hcode Hro Hfb Hst Ho Hw HK

/-- `value_bool` from an arm frame whose output is the empty result slot. -/
theorem ArmAt.callBool (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} (J : JalAt valueBoolPC) (hlive : ∀ p ∈ interpText, live p.1)
    (hvb : ⊢ ∀ p b, valueBoolSpec (vsaModel live) N Wp p b)
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s' : BitVec 64} {n' : Nat} {Wd K : IProp GF}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {sret b : BitVec 64}
    (h10 : R 10 = sret) (h11 : R 11 = b) (hslg : SlotGeom sret)
    (hk : ∀ R', (∀ x ∈ fRegs, x ∉ [11, 15] → R' x = R x) →
      ArmAt Wp Φ (evalArmF P m env aE s' n' (valAt N sret.toNat (.bool (b != 0#64))) Wd K)
        (BitVec.ofNat 64 (J.i + 4)) (upd R' 1 (BitVec.ofNat 64 (J.i + 4))) S Mt) :
    ArmAt Wp Φ (evalArmF P m env aE s' n' (slot24 sret.toNat) Wd K) (BitVec.ofNat 64 J.i) R S Mt :=
  ArmAt.callHelper Wp J hlive (Out' := fun _ => valAt N sret.toNat (.bool (b != 0#64)))
    (Pre := iprop(slot24 sret.toNat ∗ ⌜SlotGeom sret⌝))
    (by iintro; ihave H := hvb $$ %sret %b; unfold valueBoolSpec; iexact H) (pins := fun rv => rv 10 = sret ∧ rv 11 = b) ⟨h10, h11⟩
    (by iintro ⟨Ho, Hw, HK⟩; iframe Ho Hw HK; ipureintro; exact hslg) (fun _ => .rfl) hk

/-- `value_int` from an arm frame whose output is the empty result slot. -/
theorem ArmAt.callInt (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} (J : JalAt 0x8000280c#64) (hlive : ∀ p ∈ interpText, live p.1)
    (hvi : ⊢ ∀ p n, valueIntSpec (vsaModel live) N Wp p n)
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s' : BitVec 64} {n' : Nat} {Wd K : IProp GF}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {sret : BitVec 64} {res : Int}
    (h10 : R 10 = sret) (h11 : (R 11).toInt = res) (hslg : SlotGeom sret)
    (hk : ∀ R', (∀ x ∈ fRegs, x ∉ [15] → R' x = R x) →
      ArmAt Wp Φ (evalArmF P m env aE s' n' (valAt N sret.toNat (.int res)) Wd K)
        (BitVec.ofNat 64 (J.i + 4)) (upd R' 1 (BitVec.ofNat 64 (J.i + 4))) S Mt) :
    ArmAt Wp Φ (evalArmF P m env aE s' n' (slot24 sret.toNat) Wd K) (BitVec.ofNat 64 J.i) R S Mt :=
  ArmAt.callHelper Wp J hlive (Out' := fun _ => valAt N sret.toNat (.int res))
    (Pre := iprop(slot24 sret.toNat ∗ ⌜SlotGeom sret⌝))
    (Post := fun _ => valAt N sret.toNat (.int (R 11).toInt))
    (by iintro; ihave H := hvi $$ %sret %(R 11); unfold valueIntSpec; iexact H)
    (pins := fun rv => rv 10 = sret ∧ rv 11 = R 11) ⟨h10, rfl⟩
    (by iintro ⟨Ho, Hw, HK⟩; iframe Ho Hw HK; ipureintro; exact hslg)
    (fun _ => h11 ▸ .rfl) hk

/-- What the arm's caller continuation `K` accepts at the return. -/
def ExitK (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (s ret sret : BitVec 64) (rv : Nat → BitVec 64) (n : Nat) (v : Value) (Wd K : IProp GF) :
    Prop :=
  ∀ R', KeepRegs calleeSaved rv R' →
    PC ↦ᵣ ret ∗ ra ↦ᵣ ret ∗ regFile R' ∗ stackScratch s n ∗ valAt N sret.toNat v ∗ Wd ∗ K ⊢
      Wp.W Φ

theorem ArmAt.finish (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {s ret sret : BitVec 64} {rv R' : Nat → BitVec 64} {n : Nat} {v : Value}
    {Wd K : IProp GF} (hexit : ExitK Wp Φ N s ret sret rv n v Wd K)
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE : BitVec 64} {Mt : Mem}
    (hn : n ≤ s.toNat) (hneed : 1088 ≤ n) (h1 : R' 1 = ret) (hkeep : KeepRegs calleeSaved rv R') :
    ArmAt Wp Φ (evalArmF P m env aE (evalSP s) (n - 1088) (valAt N sret.toNat v) Wd K) ret R'
      (InExt (s.toNat - 1088, 1088)) Mt := by
  unfold ArmAt evalArmF
  iintro ⟨⟨-, -, -, Hst, Hval, Hw, Hk⟩, Hms⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave Hst := evalFrame_join hn hneed $$ [Hst HS]
  · iframe Hst HS
  ihave Hra := ptsto_eq h1 $$ Hra
  iapply hexit R' hkeep
  iframe Hpc Hra Hregs Hst Hval Hw Hk

end

end VsaIris.Interp
