import VsaIris.Interp.Case.{ARM}T
import VsaIris.Interp.Case.{LONG}P

/-!
# `{ARM}`, partial mode (family `logShort`, INTERP_DESIGN.md §6, §4.2)

`caseP_{ARM}`: the short-circuit row of `.logical {LOP} l r` in partial mode.
It continues the branch `caseP_{LONG}` exports (`hx_1`: the left value's
truthiness is `{TRU}`) from the state after `value_truthy`
(`#ix_piece … from {LONG}P_p2 at 2`), and finishes as in total mode (the run
lemmas `{ARM}T_run*`) with the derivation `EvalE.{CTOR}`. `caseP_{OPN}`
closes the operator: the long row with its export discharged by this one.
Template: `scripts/iris_arms/templates/logShort_P.lean`.
-/

namespace VsaIris.Interp
open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

#ix_piece {ARM}P_p3 from {LONG}P_p2 at 2 by
  -- the left value's truthiness is {TRU}: the result is decided
  have htl' : lv.truthy = {TRU} := by simpa using htl
  rw [htl'] at hbit
  -- run 3: the branch on the bit, stage `value_bool` of the constant
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.logical {LOP} l r) d - 1088) (slot24 sret.toNat)
      (world N L Room inp .uncounted st1 d)
      iprop((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v', ⌜EvalE st d env (.logical {LOP} l r) st' v'⌝ ∗
          evalPost N L Room inp .uncounted st' d (.logical {LOP} l r) v' sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt Core s (evalNeed (.logical {LOP} l r) d) ∗ slot24 sret.toNat -∗
          (wpW (vsaModel live)).W Φ)) ∗
      evalSpecsP (vsaModel live) N L Room inp Core))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [IH]
    · iframe Hcode Hro Hfb Hst Hslot Hw; iexact Hk
    · iexact IH
  intro F'
  refine iw_regFact (k := 10) (v := {BIT}#64) (by ix_reg; exact hbit) ?_
  refine {ARM}T_run3 (aX := aX) (s := s) hlive hsf hs' hs2 hs3 ?_ ?_
  · ix_reg; ix_keep [hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt3 hMt3
  have hsv3 : EvalSaved3 Mt3 s ret (rv 8) (rv 9) (rv 18) := by rw [hMt3]; exact hsv2'
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #IH⟩, Hms⟩
  -- value_bool
  ihave Hvb := hvb $$ %sret %({RB}#64)
  unfold valueBoolSpec
  iapply ms_callHelper (wpW _) (i := 0x{J3})
    (jalx_{J3} live (fun p hp => hlive _ (interp_code_{J3} p hp)))
    interp_code_{J3} (by decide)
  iframe Hvb Hcode Hms
  isplitl []
  · ipureintro; exact ⟨by ix_keep [hkeep2, hkeep1], by ix_reg⟩
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact hslg
  iintro %R3 %hkeep3 Hval Hms
  rw [show ({RB}#64 != 0#64) = {RES} from rfl]

#ix_piece {ARM}P_p4 from {ARM}P_p3 by
  -- run 4: the epilogue
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.logical {LOP} l r) d - 1088) (valAt N sret.toNat (.bool {RES}))
      (world N L Room inp .uncounted st1 d)
      iprop((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v', ⌜EvalE st d env (.logical {LOP} l r) st' v'⌝ ∗
          evalPost N L Room inp .uncounted st' d (.logical {LOP} l r) v' sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt Core s (evalNeed (.logical {LOP} l r) d) ∗ slot24 sret.toNat -∗
          (wpW (vsaModel live)).W Φ)) ∗
      evalSpecsP (vsaModel live) N L Room inp Core))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [IH]
    · iframe Hcode Hro Hfb Hst Hval Hw; iexact Hk
    · iexact IH
  intro F'
  refine {ARM}T_run4 (aX := aX) (s := s) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) hlive hsf hs' hs2 hs3 hal ?_ ?_ ?_ ?_ ?_ ?_
  · ix_keep [hkeep3, hkeep2, hkeep1]
  · rw [hoff _ (by decide)]; exact hsv3.ra
  · rw [hoff _ (by decide)]; exact hsv3.s0
  · rw [hoff _ (by decide)]; exact hsv3.s1
  · rw [hoff _ (by decide)]; exact hsv3.s2
  intros
  apply swp_closeF
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hval, Hw, Hk⟩, #IH⟩, Hms⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave Hst := evalFrame_join hsg.le hneed $$ [Hst HS]
  · iframe Hst HS
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  ihave Hk := and_elim_l $$ Hk
  iapply Hk $$ Hpc Hra
  iexists st1, (.bool {RES})
  isplitl []
  · ipureintro; exact EvalE.{CTOR} st d env l r st1 lv hEl htl'
  unfold evalPost
  iexists _
  iframe Hregs Hst Hval Hw
  ipureintro
  intro x hx
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals ix_keep [hkeep3, hkeep2, hkeep1]

#ix_chain caseP_{ARM} := [{ARM}P_p3, {ARM}P_p4]

/-- **`eval_expr` on `.logical {LOP} l r`, partial mode**: both outcomes of the
left operand's truthiness. -/
theorem caseP_{OPN} {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {l r : Expr}
    (hvt : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p v)
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p b) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ⊢
      evalSpecP_body (GF := GF) (vsaModel live) N L Room inp Core st d env (.logical {LOP} l r) :=
  caseP_{LONG} (st := st) (d := d) (env := env) hlive hvt hvb
    (caseP_{ARM} (st := st) (d := d) (env := env) hlive hvt hvb)

end VsaIris.Interp
