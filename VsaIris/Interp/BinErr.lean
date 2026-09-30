import VsaIris.Interp.BinPrelude
import VsaIris.Interp.ErrArm

/-!
The runtime type-error tail shared by every operator arm: the offending value is copied to
the frame slot `+64`, `value_kind_name` names its kind, and `rt_err` reports
`fmt(operator, kind)` and aborts. `binErrTail` is proved once for any `MachWP`; an operator
supplies its two `jal` sites and the reflected staging segment between them (`RtRun`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-- State at the `value_kind_name` call of a type-error path. -/
structure ErrPost (R R' : Nat → BitVec 64) (Mt' : Mem) (s w opn : BitVec 64) : Prop where
  a0 : R' 10 = evalSP s + 64#64
  sp : R' 2 = R 2
  s2 : R' 18 = R 18
  slot : ldv .ld Mt' (evalSP s + 64#64).toNat = w
  opn : ldv .ld Mt' (s.toNat - 1088) = opn

/-- Post of the staging segment between `value_kind_name` and `rt_err`. -/
structure RtPost (R R' : Nat → BitVec 64) (opn : BitVec 64) : Prop where
  a0 : R' 10 = R 18
  a2 : R' 12 = 0x800193f0#64
  a3 : R' 13 = opn
  a4 : R' 14 = R 10
  sp : R' 2 = R 2

/-- The reflected staging segment of an error block, from `pc` to the `rt_err` call `pc'`. -/
def RtRun (pc pc' : BitVec 64) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {DA : List Nat} {s ret sret : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {n : Nat}
    {opn : BitVec 64},
    ArmGeo s ret sret n → R 2 = evalSP s → ldv .ld Mt (s.toNat - 1088) = opn →
    MRun live m DA (InExt (s.toNat - 1088, 1088)) pc pc' R Mt (fun R' _ => RtPost R R' opn)

set_option hygiene false in
macro "rt_run" : tactic => `(tactic| (
  intro live hlive m DA s ret sret R Mt n opn g h2 hop Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have h2' : R 2 = s + 18446744073709550528#64 := h2
  clear g h2
  ix_run hlive using [h2', hop, hsf]
  refine hk _ _ ⟨by ix_reg, by ix_reg, by ix_reg, by ix_reg, by ix_reg⟩))

/-- The operator name at `opn` is a C string in the read-only data. -/
def OpName (opn : BitVec 64) : Prop :=
  ∀ {R : Nat → Prop} {rd : Nat → BitVec 8}, (∀ a, rodataDom a → R a ∧ rd a = rodataByte a) →
    ∃ t, CStrCov R rd opn.toNat t

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

theorem binErrTail (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    (hE : ErrEnv N L Room inp live Core)
    (hvk : ⊢ ∀ p Mt v, valueKindNameSpec (vsaModel live) Wp p Mt v)
    (KN : JalAt valueKindNamePC) (RT : JalAt RtErr.rtErrEntry)
    (hrt : RtRun (BitVec.ofNat 64 (KN.i + 4)) (BitVec.ofNat 64 RT.i))
    {opn : BitVec 64} (hopn : OpName opn)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat} {aE s ret sret : BitVec 64}
    {n : Nat} {R : Nat → BitVec 64} {Mt : Mem} {DA : List Nat} {ρ : Regime} {st : St} {d : Nat}
    {K : IProp GF} {v : Value} {w : BitVec 64}
    (g : ArmGeo s ret sret n) (hn : 1088 + RtErr.rtErrNeed ≤ n)
    (hv : ∀ a ∈ DA, P a ∧ (m[a]?).isSome = true)
    (h10 : R 10 = evalSP s + 64#64) (h18 : R 18 = BitVec.ofNat 64 inp) (h2 : R 2 = evalSP s)
    (hw : ldv .ld Mt (evalSP s + 64#64).toNat = w) (htag : w.toNat % 2 ^ 32 = valTag v)
    (hop : ldv .ld Mt (s.toNat - 1088) = opn)
    (hab : AbortK Wp Φ inp Core s sret n K) :
    ArmAt Wp Φ (evalArmF P m env aE (evalSP s) (n - 1088) (slot24 sret.toNat)
      (world N L Room inp ρ st d) K) (BitVec.ofNat 64 KN.i) R (InExt (s.toNat - 1088, 1088)) Mt := by
  unfold AbortK at hab
  have hoff := g.off
  have hsf := g.sf
  have hS64 : ∀ k, InExt ((evalSP s + 64#64).toNat, 24) k → InExt (s.toNat - 1088, 1088) k := by
    intro k hk; rw [hoff 64 (by decide)] at hk; simp only [VsaIris.InExt] at hk ⊢; omega
  have fin : ∀ (R4 : Nat → BitVec 64) (M4 : Mem),
      (∀ x ∈ fRegs, x ∉ [10, 14, 15] → R4 x = R x) → R4 10 = kindNamePtr v →
      ldv .ld M4 (s.toNat - 1088) = opn →
      ArmAt Wp Φ (evalArmF P m env aE (evalSP s) (n - 1088) (slot24 sret.toNat)
        (world N L Room inp ρ st d) K) (BitVec.ofNat 64 (KN.i + 4))
        (upd R4 1 (BitVec.ofNat 64 (KN.i + 4))) (InExt (s.toNat - 1088, 1088)) M4 := by
    intro R4 M4 hkeep4 hk4 hop4
    have e2 : upd R4 1 (BitVec.ofNat 64 (KN.i + 4)) 2 = evalSP s := by
      rw [upd_other R4 _ (show (2 : Nat) ≠ 1 by decide), hkeep4 2 (by decide) (by decide), h2]
    refine ArmAt.run Wp hv (hrt hlive g e2 hop4) fun R5 _ p5 => ?_
    have hR : RtErrEvalAt R5 inp (R5 11) 0x800193f0#64 opn (kindNamePtr v) s := {
      h10 := by rw [p5.a0, upd_other R4 _ (show (18 : Nat) ≠ 1 by decide),
        hkeep4 18 (by decide) (by decide), h18]
      h11 := rfl
      h12 := p5.a2
      h13 := p5.a3
      h14 := by rw [p5.a4, upd_other R4 _ (show (10 : Nat) ≠ 1 by decide), hk4]
      h2 := p5.sp.trans e2 }
    unfold ArmAt evalArmF
    iintro ⟨⟨#Hcode, -, -, Hst, Hslot, Hw, HK⟩, Hms⟩
    ihave ⟨#HE, Hab⟩ := hab $$ HK
    ihave #Himg := errCtx_img inp $$ HE
    ihave #Hrd := readable_rodata $$ Himg
    iapply ms_rtErrEval Wp hE (RT.exec live hlive) RT.mem
      (Sro := rodataDom) (rd := rodataByte) (fmt := 0x800193f0#64) (x1 := opn)
      (x2 := kindNamePtr v)
      (readable_rodata_fmt (fun hro => operand_fmt hro (hopn hro) (kindName_cstr hro v))) g.sg hn
    iframe Hcode HE Hrd Hms Hst Hw
    isplitl []
    · ipureintro; exact hR
    iintro HA
    iapply Hab
    iframe HA Hslot
  unfold ArmAt
  iintro ⟨HF, Hms⟩
  ihave #Hcode : codeRes $$ [HF]
  · unfold evalArmF; icases HF with ⟨#Hc, -⟩; iexact Hc
  iapply ms_callKindName Wp hvk (KN.exec live hlive) KN.mem KN.al (v := v) hS64
    (evalSlotGeom g.sg g.need (o := 64) (by decide) (by decide)) hw htag
  iframe Hcode Hms
  isplitl []
  · ipureintro; exact h10
  iintro %R4 %M4 %hkeep4 %hk4 %hag4 Hms
  have hop4 : ldv .ld M4 (s.toNat - 1088) = opn := by
    rw [ldv_agree (fun j hj => hag4 _ (by simp only [VsaIris.InExt]; omega))]; exact hop
  iapply fin R4 M4 hkeep4 hk4 hop4
  iframe HF Hms

end

end VsaIris.Interp
