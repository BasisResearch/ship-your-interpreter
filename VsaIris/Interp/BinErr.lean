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

/-- Where an error block finds its operator name: spilled at the frame base, or a constant
materialised by the staging code. -/
def opnSlot (s : BitVec 64) (Mt : Mem) (opn : BitVec 64) : Prop := ldv .ld Mt (s.toNat - 1088) = opn
def opnConst (c : BitVec 64) (_s : BitVec 64) (_Mt : Mem) (opn : BitVec 64) : Prop := opn = c

theorem opnSlot_agree {s : BitVec 64} {Mt M' : Mem} {opn : BitVec 64}
    (h : ∀ k, InExt (s.toNat - 1088, 1088) k → imgM M' k = imgM Mt k) (ho : opnSlot s Mt opn) :
    opnSlot s M' opn := by
  unfold opnSlot at *
  rw [ldv_agree (fun j hj => h _ (by simp only [VsaIris.InExt]; omega))]; exact ho

/-- State at the `value_kind_name` call of a type-error path. -/
structure ErrPost (src : BitVec 64 → Mem → BitVec 64 → Prop) (R R' : Nat → BitVec 64) (Mt' : Mem)
    (s w opn : BitVec 64) : Prop where
  a0 : R' 10 = evalSP s + 64#64
  sp : R' 2 = R 2
  s2 : R' 18 = R 18
  slot : ldv .ld Mt' (evalSP s + 64#64).toNat = w
  opn : src s Mt' opn

/-- Post of the staging segment between `value_kind_name` and `rt_err`. -/
structure RtPost (R R' : Nat → BitVec 64) (opn : BitVec 64) : Prop where
  a0 : R' 10 = R 18
  a2 : R' 12 = 0x800193f0#64
  a3 : R' 13 = opn
  a4 : R' 14 = R 10
  sp : R' 2 = R 2

/-- The reflected staging segment of an error block, from `pc` to the `rt_err` call `pc'`. -/
def RtRun (pc pc' : BitVec 64) (src : BitVec 64 → Mem → BitVec 64 → Prop) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {DA : List Nat} {s ret sret : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {n : Nat}
    {opn : BitVec 64},
    ArmGeo s ret sret n → R 2 = evalSP s → src s Mt opn →
    MRun live m DA (InExt (s.toNat - 1088, 1088)) pc pc' R Mt (fun R' _ => RtPost R R' opn)

set_option hygiene false in
macro "rt_run" : tactic => `(tactic| (
  intro live hlive m DA s ret sret R Mt n opn g h2 hop Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have h2' : R 2 = s + 18446744073709550528#64 := h2
  clear g h2
  simp only [opnSlot, opnConst] at hop
  try subst hop
  ix_run hlive using [h2', hsf]
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
    {src : BitVec 64 → Mem → BitVec 64 → Prop}
    (hrt : RtRun (BitVec.ofNat 64 (KN.i + 4)) (BitVec.ofNat 64 RT.i) src)
    (hsrc : ∀ {s : BitVec 64} {Mt M' : Mem} {opn : BitVec 64},
      (∀ k, InExt (s.toNat - 1088, 1088) k → imgM M' k = imgM Mt k) → src s Mt opn → src s M' opn)
    {opn : BitVec 64} (hopn : OpName opn)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat} {aE s ret sret : BitVec 64}
    {n : Nat} {R : Nat → BitVec 64} {Mt : Mem} {DA : List Nat} {ρ : Regime} {st : St} {d : Nat}
    {K : IProp GF} {v : Value} {w : BitVec 64}
    (g : ArmGeo s ret sret n) (hn : 1088 + RtErr.rtErrNeed ≤ n)
    (hv : ∀ a ∈ DA, P a ∧ (m[a]?).isSome = true)
    (h10 : R 10 = evalSP s + 64#64) (h18 : R 18 = BitVec.ofNat 64 inp) (h2 : R 2 = evalSP s)
    (hw : ldv .ld Mt (evalSP s + 64#64).toNat = w) (htag : w.toNat % 2 ^ 32 = valTag v)
    (hop : src s Mt opn)
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
      src s M4 opn →
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
  iapply fin R4 M4 hkeep4 hk4 (hsrc hag4 hop)
  iframe HF Hms

end

theorem ofNat_valTag_ne {v : Value} {k : Nat} (h : valTag v ≠ k) (hk : k < 2 ^ 31) :
    BitVec.ofNat 64 (valTag v) ≠ BitVec.ofNat 64 k := fun e => h (by
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := valTag_lt v; omega),
    Nat.mod_eq_of_lt (by omega)] at this
  exact this)

/-- A reflected type-error path of operator `op`, from the dispatch to the `value_kind_name`
call at `kn`, selected by the kind predicate `hyp`, naming the left or right operand. -/
def BinErrRun (op : BinOp) (kn : BitVec 64) (src : BitVec 64 → Mem → BitVec 64 → Prop)
    (opn : BitVec 64) (left : Bool) (hyp : Value → Value → Prop) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem}
    {lv rv' : Value} {w0 w1 w2 u0 u1 u2 : BitVec 64} {n : Nat},
    ArmGeo s ret sret n → BinOpNode m P aX (binOpTok op) →
    BinMid s sret inp rv R Mt ret aX lv rv' w0 w1 w2 u0 u1 u2 → hyp lv rv' →
    MRun live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) 0x8000351c#64 kn R Mt
      (fun R' Mt' => ErrPost src R R' Mt' s (if left then w0 else u0) opn)

/-- The spilled kinds and the branch facts of a type-error path. -/
structure ErrFacts (lv rv' : Value) (kl kr : BitVec 64) (A B : Prop) : Prop where
  kl : BitVec.ofNat 64 (valTag lv) = kl
  kr : BitVec.ofNat 64 (valTag rv') = kr
  a : A
  b : B

/-- Left operand not an integer. -/
abbrev errIntL (lv _rv' : Value) : Prop := valTag lv ≠ 2
/-- Left an integer, right not. -/
abbrev errIntR (lv rv' : Value) : Prop := valTag lv = 2 ∧ valTag rv' ≠ 2

theorem errIntL_facts {lv rv' : Value} (h : errIntL lv rv') :
    ErrFacts lv rv' (BitVec.ofNat 64 (valTag lv)) (BitVec.ofNat 64 (valTag rv'))
      (BitVec.ofNat 64 (valTag lv) ≠ 2#64) True :=
  ⟨rfl, rfl, ofNat_valTag_ne h (by decide), trivial⟩

theorem errIntR_facts {lv rv' : Value} (h : errIntR lv rv') :
    ErrFacts lv rv' 2#64 (BitVec.ofNat 64 (valTag rv')) (BitVec.ofNat 64 (valTag rv') ≠ 2#64) True :=
  ⟨by rw [h.1], rfl, ofNat_valTag_ne h.2 (by decide), trivial⟩

set_option hygiene false in
macro "bin_err_pre " facts:ident pc:num : tactic => `(tactic| (
  intro live hlive m P aX s ret sret inp rv R Mt lv rv' w0 w1 w2 u0 u1 u2 n g hn mid hyp Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hop := hn.op
  have h8 := mid.r8; have h9 := mid.r9; have h19 := mid.r19
  have h2 : R 2 = s + 18446744073709550528#64 := mid.r2
  have F := $facts hyp
  have hKL := mid.kl.trans F.kl
  have hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = _ := mid.kr.trans F.kr
  have hA := F.a
  have hB := F.b
  have hL0 : ldv .ld Mt (s + 18446744073709550528#64 + 120#64).toNat = w0 := mid.l0
  have hQ0 : ldv .ld Mt (s + 18446744073709550528#64 + 144#64).toNat = u0 := mid.q0
  clear g hn mid hyp F
  simp only [binOpTok, opnSlot, opnConst, Bool.false_eq_true, ↓reduceIte] at hop hk ⊢
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at $pc))

set_option hygiene false in
macro "bin_err_mid " pc:num : tactic => `(tactic| (
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at $pc))

set_option hygiene false in
macro "bin_err_post " pc:num : tactic => `(tactic| (
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at $pc
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hL0' : ldv .ld Mt (s.toNat - 1088 + 120) = w0 := by rw [← hoff 120 (by decide)]; exact hL0
  have hQ0' : ldv .ld Mt (s.toNat - 1088 + 144) = u0 := by rw [← hoff 144 (by decide)]; exact hQ0
  refine hk _ _ ⟨by ix_reg, by ix_reg, by ix_reg, by e2_fwd hoff <;> simp only [hL0', hQ0'],
    by simp only [opnSlot, opnConst] <;> first | rfl | (e2_fwd hoff <;> rfl)⟩))

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

theorem BinTail.drop {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {F : IProp GF} {R : Nat → BitVec 64} {s : BitVec 64} {Mt : Mem}
    {lv rv' : Value} {w0 w1 w2 u0 u1 u2 : BitVec 64}
    (h : ArmAt Wp Φ F 0x8000351c#64 R (InExt (s.toNat - 1088, 1088)) Mt) :
    BinTail Wp Φ N F R s Mt lv rv' w0 w1 w2 u0 u1 u2 := by
  unfold BinTail
  iintro ⟨-, HF, Hms⟩
  iapply h
  iframe HF Hms

/-- A type-error arm: the operator's error path, then the shared error tail. -/
theorem binErrArm {op : BinOp} {src : BitVec 64 → Mem → BitVec 64 → Prop} {opn : BitVec 64}
    {left : Bool} {hyp : Value → Value → Prop}
    (KN : JalAt valueKindNamePC) (RT : JalAt RtErr.rtErrEntry)
    (herr : BinErrRun op (BitVec.ofNat 64 KN.i) src opn left hyp)
    (hrt : RtRun (BitVec.ofNat 64 (KN.i + 4)) (BitVec.ofNat 64 RT.i) src)
    (hsrc : ∀ {s : BitVec 64} {Mt M' : Mem} {opn : BitVec 64},
      (∀ k, InExt (s.toNat - 1088, 1088) k → imgM M' k = imgM Mt k) → src s Mt opn → src s M' opn)
    (hopn : OpName opn) (Wp : MachWP (GF := GF) (vsaModel live))
    (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    (hE : ErrEnv N L Room inp live Core)
    (hvk : ⊢ ∀ p Mt v, valueKindNameSpec (vsaModel live) Wp p Mt v)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat}
    {aE s ret sret aX : BitVec 64} {d : Nat} {l r : Expr} {rv R : Nat → BitVec 64} {Mt : Mem}
    {ρ : Regime} {st : St} {lv rv' : Value} {w0 w1 w2 u0 u1 u2 : BitVec 64} {K : IProp GF}
    (g : ArmGeo s ret sret (evalNeed (.binary op l r) d)) (hn : BinOpNode m P aX (binOpTok op))
    (mid : BinMid s sret (BitVec.ofNat 64 inp) rv R Mt ret aX lv rv' w0 w1 w2 u0 u1 u2)
    (h : hyp lv rv')
    (hab : AbortK Wp Φ inp Core s sret (evalNeed (.binary op l r) d) K) :
    BinTail Wp Φ N (binArmF N P m env aE s (evalNeed (.binary op l r) d) sret
      (world N L Room inp ρ st d) K) R s Mt lv rv' w0 w1 w2 u0 u1 u2 :=
  BinTail.drop (ArmAt.run Wp hn.view (herr hlive g hn mid h) fun _ _ p =>
    binErrTail Wp hlive hE hvk KN RT hrt hsrc hopn g (evalNeed_binary_rtErr _ _ _ _) hn.view
      (v := if left then lv else rv') p.a0 (p.s2.trans mid.r18) (p.sp.trans mid.r2) p.slot
      (by cases left <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;>
        first | exact mid.tl | exact mid.tr) p.opn hab)

end

/-- State at an `rt_err` call reporting a fixed message `fmt` (no operands). -/
structure PlainErrPost (R R' : Nat → BitVec 64) (fmt : BitVec 64) : Prop where
  a0 : R' 10 = R 18
  a2 : R' 12 = fmt
  a3 : R' 13 = 0#64
  a4 : R' 14 = 0#64
  sp : R' 2 = R 2

/-- The division-by-zero path of `op`, from the dispatch to its `rt_err` call at `rt`. -/
def ZeroRun (op : BinOp) (rt fmt : BitVec 64) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem}
    {a b : Int} {w0 w1 w2 u0 u1 u2 : BitVec 64} {n : Nat},
    ArmGeo s ret sret n → BinOpNode m P aX (binOpTok op) →
    BinMid s sret inp rv R Mt ret aX (.int a) (.int b) w0 w1 w2 u0 u1 u2 → u1 = 0#64 →
    MRun live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) 0x8000351c#64 rt R Mt
      (fun R' _ => PlainErrPost R R' fmt)

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- A fixed-message runtime error arm (division by zero). -/
theorem binZeroArm {op : BinOp} {fmt : BitVec 64} (RT : JalAt RtErr.rtErrEntry)
    (hz : ZeroRun op (BitVec.ofNat 64 RT.i) fmt)
    (hfmt : FmtArgsOK (fun a => rodataDom a ∨ False) rodataByte fmt [0#64, 0#64])
    (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    (hE : ErrEnv N L Room inp live Core)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat}
    {aE s ret sret aX : BitVec 64} {d : Nat} {l r : Expr} {rv R : Nat → BitVec 64} {Mt : Mem}
    {ρ : Regime} {st : St} {a : Int} {w0 w1 w2 u0 u1 u2 : BitVec 64} {K : IProp GF}
    (g : ArmGeo s ret sret (evalNeed (.binary op l r) d)) (hn : BinOpNode m P aX (binOpTok op))
    (mid : BinMid s sret (BitVec.ofNat 64 inp) rv R Mt ret aX (.int a) (.int 0) w0 w1 w2 u0 u1 u2)
    (hab : AbortK Wp Φ inp Core s sret (evalNeed (.binary op l r) d) K) :
    BinTail Wp Φ N (binArmF N P m env aE s (evalNeed (.binary op l r) d) sret
      (world N L Room inp ρ st d) K) R s Mt (.int a) (.int 0) w0 w1 w2 u0 u1 u2 := by
  unfold AbortK at hab
  refine BinTail.ints fun _ h2 => ?_
  have hu : u1 = 0#64 := BitVec.eq_of_toInt_eq (by rw [h2]; rfl)
  refine ArmAt.run Wp hn.view (hz hlive g hn mid hu) fun R' _ p => ?_
  have hR : RtErrEvalAt R' inp (R' 11) fmt 0#64 0#64 s :=
    ⟨p.a0.trans mid.r18, rfl, p.a2, p.a3, p.a4, p.sp.trans mid.r2⟩
  unfold ArmAt evalArmF
  iintro ⟨⟨#Hcode, -, -, Hst, Hslot, Hw, HK⟩, Hms⟩
  ihave ⟨#HE, Hab⟩ := hab $$ HK
  ihave #Himg := errCtx_img inp $$ HE
  ihave #Hrd := readable_rodata $$ Himg
  iapply ms_rtErrEval Wp hE (RT.exec live hlive) RT.mem (Sro := rodataDom) (rd := rodataByte)
    hfmt g.sg (evalNeed_binary_rtErr _ _ _ _)
  iframe Hcode HE Hrd Hms Hst Hw
  isplitl []
  · ipureintro; exact hR
  iintro HA
  iapply Hab
  iframe HA Hslot

end

end VsaIris.Interp
