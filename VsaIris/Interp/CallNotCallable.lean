import VsaIris.Interp.CallNativeSeg
import VsaIris.Interp.ErrArm
import VsaIris.Interp.CallErr

/-!
# Calling a value that is not a function (lane E4)

`interp.c:176-178`: a callee that is neither a native nor a closure
(`null`, a boolean, an integer, a string) is a runtime error,
`runtime_error(in, line, "cannot call a %s value", value_kind_name(callee), 0)`.
At the kind dispatch the two kind tests fall through to `0x80003da4`, which
copies the callee to `sp+64` and calls `value_kind_name` on it (E2's
`ms_callKindName`); then `runtime_error` (E2's `ms_rtErrEval`) aborts.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While

-- Run X1: the kind tests fall through, the callee copied to `sp+64` (its
-- first word's low half rewritten from the kind), `s3`-`s6` spilled; stop at
-- the `jal value_kind_name`.
#ix_seg CallX_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s w0 w1 w2 : BitVec 64} {k : Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 28 ≤ 0x100000000)
    (hx3 : aX.toNat + 28 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64)
    (hW0 : ldv .ld Mt (s + 18446744073709550528#64 + 96#64).toNat = w0)
    (hW1 : ldv .ld Mt (s + 18446744073709550528#64 + 104#64).toNat = w1)
    (hW2 : ldv .ld Mt (s + 18446744073709550528#64 + 112#64).toNat = w2)
    (hK : ldv .lw Mt (s + 18446744073709550528#64 + 96#64).toNat = BitVec.ofNat 64 k)
    (hk5 : BitVec.ofNat 64 k ≠ 5#64) (hk4 : BitVec.ofNat 64 k ≠ 4#64) :
    IW live m (callView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x80003254#64 R Mt
  by ix_run hlive using [h8, h2, hW0, hW1, hW2, hK, hk5, hk4, hsf] at 0x80003dcc

-- Run X2: after `value_kind_name`, stage `runtime_error(in, line, fmt, name, 0)`.
#ix_seg CallX_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {DA : List Nat} {S : Nat → Prop} :
    IW live m DA S Q 0x80003dd0#64 R Mt
  by ix_run hlive at 0x80003de8


open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.RuntimeRepr

/-- A doubleword load's low half after a word store at its address is the
stored word's. -/
theorem ldv_ld_lo32_store4 (Mt : Mem) (a : Nat) (v : BitVec 64) :
    (ldv .ld (writeLog Mt [(a, 4, v)]) a).toNat % 2 ^ 32 = v.toNat % 2 ^ 32 := by
  rw [ldv_ld_imgW, imgW_lo32, imgLE_store4_hit]

/-- The values that are not callable: neither a native nor a closure. -/
def NotCallable : Value → Prop
  | .native _ => False
  | .closure _ => False
  | _ => True

theorem notCallable_tag {v : Value} (h : NotCallable v) :
    valTag v < 4 ∧ BitVec.ofNat 64 (valTag v) ≠ 5#64 ∧ BitVec.ofNat 64 (valTag v) ≠ 4#64 := by
  cases v <;> simp_all [NotCallable, valTag] <;> decide

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- **Calling a value that is not a function**, for either WP: from the kind
dispatch, `value_kind_name` then `runtime_error`, which aborts with the
arm's `abortAt Core s n`. -/
theorem callNotCallable (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {Core : IProp GF} (hE : ErrEnv N L Room inp live Core)
    (hvk : ⊢ ∀ p Mt v, valueKindNameSpec (GF := GF) (vsaModel live) Wp p Mt v)
    {ρ : Regime} {st2 : St} {d : Nat} {fv : Value} {fe : Expr} {args : List Expr}
    {s aX sret ret w0 w1 w2 : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem} {n argc : Nat}
    (hnc : NotCallable fv) (hsg : StackGeom s n) (hn : 1088 + RtErr.rtErrNeed ≤ n)
    (hcall : CallAt R Mt s aX sret (BitVec.ofNat 64 inp) ret rv w0 w1 w2 argc) :
    codeRes ∗ errCtx inp ∗ □ astEG aX.toNat (.call fe args) ∗ □ valOf N fv w0 w1 w2 ∗
      ms 0x80003254#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗ world N L Room inp ρ st2 d ∗
      (abortAt Core s n -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hs' : 0x87800000 + 1088 ≤ s.toNat := by unfold RtErr.rtErrNeed snprintfNeed at hn; omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have hoff := evalSP_off (s := s) hsf (by omega)
  obtain ⟨hk4', hk5, hk4⟩ := notCallable_tag hnc
  iintro ⟨#Hcode, #HE, #Hast, #Hv, Hms, Hst, Hw, Hab⟩
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨aF, hnd, -, -⟩ := callNode_of_repr hrepr hgeo
  ihave %htag := valOf_tag N fv w0 w1 w2 $$ Hv
  ihave #Hdv := roOwn_data hnd.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(codeRes ∗ errCtx inp ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗
      world N L Room inp ρ st2 d ∗ (abortAt Core s n -∗ Wp.W Φ)))
  rotate_left
  · iframe Hdv Hms Hcode HE Hst Hw; iexact Hab
  intro F'
  refine CallX_run1 (k := valTag fv) (w0 := w0) (w1 := w1) (w2 := w2) hlive hsf hs' hs2 hs3
    hnd.lo hnd.hi hnd.off hcall.s0 hcall.sp ?_ ?_ ?_ ?_ hk5 hk4 ?_
  · rw [hoff 96 (by decide)]; exact hcall.w0
  · rw [hoff 104 (by decide)]; exact hcall.w1
  · rw [hoff 112 (by decide)]; exact hcall.w2
  · rw [hoff 96 (by decide)]; exact ldv_lw_of_ld hcall.w0 htag (by omega)
  intro vl _ _
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  unfold F'
  iintro ⟨⟨#Hcode, #HE, Hst, Hw, Hab⟩, Hms⟩
  have h64 : ldv .ld Mt1 (s + 18446744073709550528#64 + 64#64).toNat =
      R1 15 := by subst hR1 hMt1; ix_fwd; ix_reg
  have htag' : (R1 15).toNat % 2 ^ 32 = valTag fv := by
    subst hR1; ix_reg
    rw [ldv_ld_lo32_store4, BitVec.toNat_ofNat]; omega
  iapply ms_callKindName Wp hvk (jalx_80003dcc live (fun p hp => hlive _ (interp_code_80003dcc p hp)))
    interp_code_80003dcc (by decide) (S := InExt (s.toNat - 1088, 1088)) (v := fv)
    (fun k hk => by rw [hoff 64 (by decide)] at hk; simp only [InExt] at hk ⊢; omega)
    (evalSlotGeom hsg (by omega) (by decide) (by decide)) h64 htag'
  iframe Hcode Hms
  isplitl []
  · ipureintro; subst hR1; ix_reg
  iintro %R2 %M2 %hk2 %h10 %_ Hms
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ []) (F := iprop(codeRes ∗ errCtx inp ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗
      world N L Room inp ρ st2 d ∗ (abortAt Core s n -∗ Wp.W Φ)))
  rotate_left
  · rw [hro]; iframe Hcode Hms HE Hst Hw; iexact Hab
  intro F'
  refine CallX_run2 (m := ∅) (DA := []) hlive ?_
  apply swp_closeRM
  intro R3 M3 hR3 hM3
  unfold F'
  iintro ⟨⟨#Hcode, #HE, Hst, Hw, Hab⟩, Hms⟩
  ihave #Himg := errCtx_img inp $$ HE
  ihave #Hrd := readable_rodata $$ Himg
  iapply ms_rtErrEval Wp hE (jalx_80003de8 live (fun p hp => hlive _ (interp_code_80003de8 p hp)))
    interp_code_80003de8
    (readable_rodata_fmt (fun hro => notCallable_fmt hro (kindName_cstr hro fv) 0#64)) hsg hn
    (R := R3) (line := vl)
  iframe Hcode HE Hrd Hms Hst Hw Hab
  ipureintro
  have k18 := hk2 18 (by decide) (by decide)
  have k23 := hk2 23 (by decide) (by decide)
  subst hR3
  refine ⟨?_, ?_, by ix_reg, by ix_reg; exact h10, by ix_reg, ?_⟩
  · ix_reg; rw [k18]; subst hR1; ix_reg; exact hcall.s2
  · ix_reg; rw [k23]; subst hR1; ix_reg
  · ix_reg; rw [hk2 2 (by decide) (by decide)]; subst hR1; ix_reg; exact hcall.sp

end

end VsaIris.Interp
