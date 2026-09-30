import VsaIris.Interp.CatTail
import VsaIris.Interp.IntOpArm
import VsaIris.Interp.BinPreludeP

/-!
`+`: the total concatenation spec and the partial spec (integer sum, concatenation, both type
errors) from the binary preludes, the generic concatenation tail `catTail`, `intOpTail .add`
and `binErrArm`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib VsaIris.VsaHeap
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

/-- Neither operand a string, the left one not an integer. -/
abbrev errAddL (lv rv' : Value) : Prop := valTag rv' ≠ 3 ∧ valTag lv ≠ 2 ∧ valTag lv ≠ 3
/-- Left an integer, the right neither an integer nor a string. -/
abbrev errAddR (lv rv' : Value) : Prop := valTag lv = 2 ∧ valTag rv' ≠ 2 ∧ valTag rv' ≠ 3

theorem tag_ne3 {v : Value} (h : valTag v ≠ 3) :
    BitVec.ofNat 64 (valTag v) + 18446744073709551613#64 ≠ 0#64 := by
  cases v <;> simp only [valTag] at h ⊢ <;> first | exact absurd rfl h | decide

theorem errAddL_facts {lv rv' : Value} (h : errAddL lv rv') :
    ErrFacts lv rv' (BitVec.ofNat 64 (valTag lv)) (BitVec.ofNat 64 (valTag rv'))
      (BitVec.ofNat 64 (valTag lv) ≠ 2#64 ∧ BitVec.ofNat 64 (valTag lv) + 18446744073709551613#64 ≠ 0#64)
      (BitVec.ofNat 64 (valTag rv') + 18446744073709551613#64 ≠ 0#64) :=
  let ⟨h3, h2, h3'⟩ := h
  ⟨rfl, rfl, ⟨ofNat_valTag_ne h2 (by decide), tag_ne3 h3'⟩, tag_ne3 h3⟩

theorem errAddR_facts {lv rv' : Value} (h : errAddR lv rv') :
    ErrFacts lv rv' 2#64 (BitVec.ofNat 64 (valTag rv'))
      (BitVec.ofNat 64 (valTag rv') ≠ 2#64 ∧ BitVec.ofNat 64 (valTag rv') + 18446744073709551613#64 ≠ 0#64)
      True :=
  let ⟨hl, h2, h3⟩ := h
  ⟨by rw [hl], rfl, ⟨ofNat_valTag_ne h2 (by decide), tag_ne3 h3⟩, trivial⟩

set_option hygiene false in
/-- `bin_err_pre` with the spilled kinds generalized (the `+` dispatch compares them with 3). -/
macro "add_err_pre " facts:ident pc:num : tactic => `(tactic| (
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
  generalize BitVec.ofNat 64 (valTag rv') = kR at hKR hA hB
  generalize BitVec.ofNat 64 (valTag lv) = kL at hKL hA hB
  obtain ⟨hA1, hA2⟩ := hA
  simp only [binOpTok, opnSlot, opnConst, Bool.false_eq_true, ↓reduceIte] at hop hk ⊢
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at $pc))

#ix_seg AddErrL1 : BinErrRun .add (BitVec.ofNat 64 0x80003d3c) (opnConst (BitVec.ofNat 64 0x800193e8))
    (BitVec.ofNat 64 0x800193e8) true errAddL by
  add_err_pre errAddL_facts 0x80003888
#ix_piece AddErrL2 from AddErrL1 by bin_err_mid 0x80003df8
#ix_piece AddErrL3 from AddErrL2 by bin_err_post 0x80003d3c
#ix_tree AddErrL := AddErrL1 [AddErrL2 [AddErrL3]]

#ix_seg AddErrR1 : BinErrRun .add (BitVec.ofNat 64 0x80003d3c) (opnConst (BitVec.ofNat 64 0x800193e8))
    (BitVec.ofNat 64 0x800193e8) false errAddR by
  add_err_pre errAddR_facts 0x80003888
#ix_piece AddErrR2 from AddErrR1 by bin_err_mid 0x80003d18
#ix_piece AddErrR3 from AddErrR2 by bin_err_post 0x80003d3c
#ix_tree AddErrR := AddErrR1 [AddErrR2 [AddErrR3]]

theorem addRt : RtRun (BitVec.ofNat 64 0x80003d40) (BitVec.ofNat 64 0x80003d5c)
    (opnConst (BitVec.ofNat 64 0x800193e8)) := by rt_run

theorem addOpName : OpName 0x800193e8#64 :=
  fun hro => rodata_cstrV hro 0x800193e8#64 1 (by decide) (by decide)

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

omit I in
/-- A non-aborting helper spec serves every abort resource. -/
theorem helperSpec_A {M : MachineModel} {Wp : MachWP (GF := GF) M} {entry : BitVec 64}
    {clob : List Nat} {pins : (Nat → BitVec 64) → Prop} {Pre : IProp GF}
    {Post : (Nat → BitVec 64) → IProp GF} {A : IProp GF} :
    helperSpec M Wp entry clob pins Pre Post ⊢ helperSpecA M Wp entry clob pins Pre Post A := by
  unfold helperSpec helperSpecA fnSpecW fnSpecAbort
  iintro #H %rv !> %r %Φ Hpc Hra HP HK
  iapply H $$ %rv %r %Φ Hpc Hra HP
  iapply and_elim_l $$ HK

omit I in
/-- An aborting helper spec, weakened along its abort resource. -/
theorem helperSpecA_weaken {M : MachineModel} {Wp : MachWP (GF := GF) M} {entry : BitVec 64}
    {clob : List Nat} {pins : (Nat → BitVec 64) → Prop} {Pre : IProp GF}
    {Post : (Nat → BitVec 64) → IProp GF} {A A' : IProp GF} (h : A' ⊢ A) :
    helperSpecA M Wp entry clob pins Pre Post A' ⊢ helperSpecA M Wp entry clob pins Pre Post A := by
  unfold helperSpecA fnSpecAbort
  iintro #H %rv !> %r %Φ Hpc Hra HP HK
  iapply H $$ %rv %r %Φ Hpc Hra HP
  isplit
  · iapply and_elim_l $$ HK
  · iintro HA
    ihave HK := and_elim_r $$ HK
    iapply HK
    iapply h $$ HA

theorem concatT (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 st2 : St} {d env : Nat} {l r : Expr} {lv rv' : Value} {nl nr : Nat}
    (Dl : EvalECost st d env l st1 lv nl) (Dr : EvalECost st1 d env r st2 rv' nr)
    (D : EvalECost st d env (.binary .add l r) st2
      (.str (lv.catDisplay st2.store ++ rv'.catDisplay st2.store))
      (nl + nr + binOpCost st2.store .add lv rv'))
    (hl : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env l st1 lv nl Dl)
    (hr : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st1 d env r st2 rv' nr Dr)
    (hL : L = vsaLayoutP) (hRoom : Room = vsaRoomB)
    (hcat : valTag lv = 3 ∨ valTag rv' = 3) (A : AllocSpecs live)
    (hsgy : ⊢ ∀ p s v st k H c o, stringifySpecT (GF := GF) (vsaModel live) N
      (twpW (vsaModel live)) p s v st k H c o)
    (hsl : ⊢ ∀ q x ρ H, strlenHeapSpec (GF := GF) (vsaModel live) (twpW (vsaModel live)) q x ρ H)
    (hmc : ⊢ memcpySpecOwned (GF := GF) (vsaModel live) (twpW (vsaModel live)))
    (hsc : ⊢ ∀ d q y ρ H, strcpyHeapSpec (GF := GF) (vsaModel live) (twpW (vsaModel live)) d q y ρ H)
    (hvs : ⊢ ∀ p q x, valueStrSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p q x)
    (hd : CatDispSupply (GF := GF) N) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.binary .add l r) st2
        (.str (lv.catDisplay st2.store ++ rv'.catDisplay st2.store))
        (nl + nr + binOpCost st2.store .add lv rv') D := by
  subst hL hRoom
  refine binPreludeTc hlive Dl Dr D hl hr
    fun k Φ sret aE aX s ret rv R P m Mt w0 w1 w2 u0 u1 u2 K g hn mid hexit => ?_
  rw [binOpCost_concat hcat]
  refine catTail hlive (twpW _) (.counted k) A ?_ hsl hmc hsc hvs hd g hn mid hcat hexit
    (fun h => by cases h)
  iintro %p %s' %v %st' %j %H %c %o
  ihave Hs := hsgy $$ %p %s' %v %st' %(k + j) %H %c %o
  unfold stringifySpecT
  simp only [Regime.plus_counted]
  iapply helperSpec_A $$ Hs

theorem addP (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {l r : Expr}
    (hE : ErrEnv (GF := GF) N L Room inp live Core)
    (hvi : ⊢ ∀ p n, valueIntSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p n)
    (hL : L = vsaLayoutP) (hRoom : Room = vsaRoomB) (A : AllocSpecs live)
    (hsgy : ⊢ ∀ p s v st ρ H c o, stringifySpecP (GF := GF) (vsaModel live) N
      (wpW (vsaModel live)) inp p s v st ρ H c o)
    (hsl : ⊢ ∀ q x ρ H, strlenHeapSpec (GF := GF) (vsaModel live) (wpW (vsaModel live)) q x ρ H)
    (hmc : ⊢ memcpySpecOwned (GF := GF) (vsaModel live) (wpW (vsaModel live)))
    (hsc : ⊢ ∀ d q y ρ H, strcpyHeapSpec (GF := GF) (vsaModel live) (wpW (vsaModel live)) d q y ρ H)
    (hvs : ⊢ ∀ p q x, valueStrSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p q x)
    (hd : CatDispSupply (GF := GF) N)
    (hvk : ⊢ ∀ p Mt v, valueKindNameSpec (GF := GF) (vsaModel live) (wpW (vsaModel live)) p Mt v) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (GF := GF) (vsaModel live) N L Room inp Core st d env (.binary .add l r) := by
  subst hL hRoom
  refine binPreludeP hlive
    fun Φ sret aE aX s ret rv R P m Mt w0 w1 w2 u0 u1 u2 st1 st2 lv rv' K _ _ g hn mid hexit hab => ?_
  rcases addRows lv rv' with ⟨a, b, rfl, rfl⟩ | hcat | hL | ⟨a, rfl, hR, hR3⟩
  · exact intOpTail .add (wpW _) hlive hvi g hn mid trivial (hexit _ rfl)
  · refine catTail hlive (wpW _) .uncounted A ?_ hsl hmc hsc hvs hd g hn mid hcat
      (hexit _ (binOpSem_concat hcat)) (fun _ => ⟨Core, hE, hab⟩)
    iintro %p %s' %v %st' %j %H %c %o
    ihave Hs := hsgy $$ %p %s' %v %st' %Regime.uncounted %H %c %o
    unfold stringifySpecP
    simp only [Regime.plus_uncounted]
    iapply helperSpecA_weaken (A' := iprop(abortRes N vsaLayoutP vsaRoomB inp s' stringifyNeed ∗
      slot24 p.toNat)) ?_ $$ Hs
    iintro H
    iframe H
  · exact binErrArm (jal_site% 0x80003d3c) (jal_site% 0x80003d5c) AddErrL addRt opnConst_agree
      addOpName (wpW _) hlive hE hvk g hn mid hL hab
  · exact binErrArm (jal_site% 0x80003d3c) (jal_site% 0x80003d5c) AddErrR addRt opnConst_agree
      addOpName (wpW _) hlive hE hvk g hn mid ⟨rfl, hR, hR3⟩ hab

end

end VsaIris.Interp
