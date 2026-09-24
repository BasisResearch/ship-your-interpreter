import VsaIris.Interp.CallArm

/-!
# The call arm's prefix, total mode (lane E4)

Every call row starts the same way: the prologue and kind dispatch, the callee
into `sp+96`, the count test, the argument loop (E6's `evalArgsT_body`), up
to the kind dispatch at `0x80003254`. `callPrefixT` runs it and hands its
continuation the reached state (`CallAt`): the callee's three words with their
meaning, the arguments' words (`argVals`), the frame's spills, the stack
below the lowered `sp` and the world after both.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- A load reads only its window. -/
theorem ldv_eqOn (k : MKind) {Mt Mt' : Mem} {a : Nat}
    (h : ∀ j, j < widthOfM k → imgM Mt (a + j) = imgM Mt' (a + j)) : ldv k Mt a = ldv k Mt' a := by
  unfold ldv bytesAt
  congr 1
  apply List.map_congr_left
  intro j hj
  exact h j (List.mem_range.1 hj)

/-- A doubleword of the frame outside the argument loop's writes survives it. -/
theorem ldv_untouched {s : BitVec 64} {Mt Mt' : Mem} (h : Untouched (InExt (s.toNat - 1088, 1088))
    (argsW s) Mt Mt') {o : Nat} (ho : (96 ≤ o ∧ o + 8 ≤ 240) ∨ (1008 ≤ o ∧ o + 8 ≤ 1088)) :
    ldv .ld Mt' (s.toNat - 1088 + o) = ldv .ld Mt (s.toNat - 1088 + o) :=
  ldv_eqOn .ld fun j hj => h _ (by simp only [InExt, widthOfM] at *; omega)
    (by simp only [argsW, argsBase, InExt, widthOfM] at *; omega)

/-- **The state at the kind dispatch** (`0x80003254`) after the prefix: the
registers (`s0` the node, `s1` the result slot, `s2 = in`, `a5 = argc`, the
other callee-saved registers the caller's), the callee's words at `sp+96`,
and the frame's spills (the return address and `s0`-`s2` of the prologue,
`s7` of the count test). -/
structure CallAt (R : Nat → BitVec 64) (Mt : Mem) (s aX sret inp ret : BitVec 64)
    (rv : Nat → BitVec 64) (w0 w1 w2 : BitVec 64) (argc : Nat) : Prop where
  sp : R 2 = s + 18446744073709550528#64
  s0 : R 8 = aX
  s1 : R 9 = sret
  s2 : R 18 = inp
  a5 : R 15 = BitVec.ofNat 64 argc
  keep : ∀ x ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], R x = rv x
  w0 : ldv .ld Mt (s.toNat - 1088 + 96) = w0
  w1 : ldv .ld Mt (s.toNat - 1088 + 104) = w1
  w2 : ldv .ld Mt (s.toNat - 1088 + 112) = w2
  ra : ldv .ld Mt (s.toNat - 1088 + 1080) = ret
  sv8 : ldv .ld Mt (s.toNat - 1088 + 1072) = rv 8
  sv9 : ldv .ld Mt (s.toNat - 1088 + 1064) = rv 9
  sv18 : ldv .ld Mt (s.toNat - 1088 + 1056) = rv 18
  sv23 : ldv .ld Mt (s.toNat - 1088 + 1016) = rv 23


theorem Expr.bodiesBoundList_mem {P : Nat} : ∀ {es : List Expr} {e : Expr},
    Expr.bodiesBoundList P es = true → e ∈ es → e.bodiesBound P = true
  | _ :: _, _, h, .head _ => by simp only [Expr.bodiesBoundList, Bool.and_eq_true] at h; exact h.1
  | _ :: _, _, h, .tail _ hm => by
    simp only [Expr.bodiesBoundList, Bool.and_eq_true] at h; exact Expr.bodiesBoundList_mem h.2 hm

/-- The prologue's spills an arm without `s3` carries (the return address and
`s0`-`s2`, `EvalSaved` without `s3`). -/
structure CallSaved (Mt : Mem) (s ret v8 v9 v18 : BitVec 64) : Prop where
  ra : ldv .ld Mt (s.toNat - 1088 + 1080) = ret
  s0 : ldv .ld Mt (s.toNat - 1088 + 1072) = v8
  s1 : ldv .ld Mt (s.toNat - 1088 + 1064) = v9
  s2 : ldv .ld Mt (s.toNat - 1088 + 1056) = v18

theorem CallSaved.store {Mt : Mem} {s ret v8 v9 v18 : BitVec 64}
    (h : CallSaved Mt s ret v8 v9 v18) {a w : Nat} (v : BitVec 64)
    (ha : a + w ≤ s.toNat - 1088 + 1056) :
    CallSaved (writeLog Mt [(a, w, v)]) s ret v8 v9 v18 :=
  ⟨by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.ra,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s0,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s1,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s2⟩

theorem CallSaved.slotWrite {Mt : Mem} {s ret v8 v9 v18 : BitVec 64}
    (h : CallSaved Mt s ret v8 v9 v18) {a : Nat} (w0 w1 w2 : BitVec 64)
    (ha : a + 24 ≤ s.toNat - 1088 + 1056) :
    CallSaved (slotWrite Mt a w0 w1 w2) s ret v8 v9 v18 :=
  ((h.store w0 (by omega)).store w1 (by omega)).store w2 (by omega)

/-- The lowered `sp`'s stack region. -/
theorem stackGeom_evalSP {s : BitVec 64} {n : Nat} (hsg : StackGeom s n) (h : 1088 ≤ n)
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088) :
    StackGeom (s + 18446744073709550528#64) (n - 1088) := by
  have h1 := hsg.le; have h2 := hsg.lo; have h3 := hsg.hi; have h4 := hsg.al
  refine ⟨by rw [hsf]; omega, by rw [hsf]; omega, by rw [hsf]; omega, by rw [hsf]; omega⟩

/-- `CallAt` from the state before the argument loop (`Mt2`, the loop's
entry memory) and the loop's frame fact. -/
theorem CallAt.of_untouched {R : Nat → BitVec 64} {Mt Mt2 : Mem} {s aX sret inp ret : BitVec 64}
    {rv : Nat → BitVec 64} {w0 w1 w2 : BitVec 64} {argc : Nat}
    (hU : Untouched (InExt (s.toNat - 1088, 1088)) (argsW s) Mt2 Mt)
    (h2 : R 2 = s + 18446744073709550528#64) (h8 : R 8 = aX) (h9 : R 9 = sret) (h18 : R 18 = inp)
    (h15 : R 15 = BitVec.ofNat 64 argc) (hk : ∀ x ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], R x = rv x)
    (m0 : ldv .ld Mt2 (s.toNat - 1088 + 96) = w0) (m1 : ldv .ld Mt2 (s.toNat - 1088 + 104) = w1)
    (m2 : ldv .ld Mt2 (s.toNat - 1088 + 112) = w2) (mra : ldv .ld Mt2 (s.toNat - 1088 + 1080) = ret)
    (m8 : ldv .ld Mt2 (s.toNat - 1088 + 1072) = rv 8) (m9 : ldv .ld Mt2 (s.toNat - 1088 + 1064) = rv 9)
    (m18 : ldv .ld Mt2 (s.toNat - 1088 + 1056) = rv 18)
    (m23 : ldv .ld Mt2 (s.toNat - 1088 + 1016) = rv 23) :
    CallAt R Mt s aX sret inp ret rv w0 w1 w2 argc :=
  ⟨h2, h8, h9, h18, h15, hk,
    (ldv_untouched hU (o := 96) (by omega)).trans m0, (ldv_untouched hU (o := 104) (by omega)).trans m1,
    (ldv_untouched hU (o := 112) (by omega)).trans m2, (ldv_untouched hU (o := 1080) (by omega)).trans mra,
    (ldv_untouched hU (o := 1072) (by omega)).trans m8, (ldv_untouched hU (o := 1064) (by omega)).trans m9,
    (ldv_untouched hU (o := 1056) (by omega)).trans m18, (ldv_untouched hU (o := 1016) (by omega)).trans m23⟩

section Prefix

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- The continuation of the call prefix, total mode: the state at the kind
dispatch. -/
def CallK254T (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (Φ : Nat × String → IProp GF) (k : Nat) (st2 : St) (d : Nat) (fv : Value) (vs : List Value)
    (s aX sret ret : BitVec 64) (rv : Nat → BitVec 64) (argc m' : Nat) : IProp GF :=
  iprop(∀ (R : Nat → BitVec 64) (Mt : Mem) (w0 w1 w2 : BitVec 64),
    ⌜CallAt R Mt s aX sret (BitVec.ofNat 64 inp) ret rv w0 w1 w2 argc⌝ -∗ □ valOf N fv w0 w1 w2 -∗
    argVals N (imgM Mt) (argsBase s) 0 vs -∗ ms 0x80003254#64 R (InExt (s.toNat - 1088, 1088)) Mt -∗
    stackScratch (s + 18446744073709550528#64) m' -∗ world N L Room inp (.counted k) st2 d -∗
    (twpW (vsaModel live)).W Φ)

end Prefix

end VsaIris.Interp

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.RuntimeRepr

#ix_piece callPrefixT_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 st2 : St} {d env : Nat} {f : Expr} {args : List Expr} {fv : Value} {vs : List Value}
    {nf na : Nat}
    (Df : EvalECost st d env f st1 fv nf) (hlen : args.length ≤ maxArgs)
    (Da : EvalArgsCost st1 d env args st2 vs na)
    (hf : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env f st1 fv nf Df)
    (ha : evalArgsT_body (GF := GF) live N L Room inp st1 d env args st2 vs na)
    {Φ : Nat × String → IProp GF} {k : Nat} {sret aE aX s ret : BitVec 64} {rv : Nat → BitVec 64}
    (hregs : EvalRegs rv sret (BitVec.ofNat 64 inp) aX aE s)
    (hsg : StackGeom s (evalNeed (.call f args) d))
    (hbb : (Expr.call f args).bodiesBound perCallBudget = true) (hal : ret.toNat % 4 = 0) :
    PC ↦ᵣ evalEntryPC ∗ ra ↦ᵣ ret ∗ regFile rv ∗ codeRes ∗ □ astEG aX.toNat (.call f args) ∗
      □ frameAt env aE.toNat ∗ stackScratch s (evalNeed (.call f args) d) ∗
      world N L Room inp (.counted (k + (nf + na))) st d ∗
      CallK254T live N L Room inp Φ k st2 d fv vs s aX sret ret rv args.length
        (evalNeed (.call f args) d - 1088)
    ⊢ (twpW (vsaModel live)).W Φ by
  iintro ⟨Hpc, Hra, Hregs, #Hcode, #Hast, #Hfb, Hst, Hw, Hk⟩
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨aF, hn, hrf, haF⟩ := callNode_of_repr hrepr hgeo
  have hneed : 1088 ≤ evalNeed (.call f args) d := by
    have := Expr.stackNeed_ge (.call f args); unfold evalNeed stackBudget; unfold evalFrame at this; omega
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hs' : 0x87800000 + 1088 ≤ s.toNat := by omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have gF := evalCallGeom (o := 96) hsg
    (by have := evalNeed_call_fn f args d; unfold evalFrame at this; omega) (by decide) (by decide)
  obtain ⟨hbf, hba⟩ := Expr.bodiesBound_call hbb
  have hFt : (BitVec.ofNat 64 aF).toNat = aF := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haF]
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hoff := evalSP_off (s := s) hsf (by omega)
  ihave ⟨Hst, HF⟩ := stackScratch_frame (f := 1088#64) hsg.le hneed $$ Hst
  rw [hsF, hsf, show (1088#64).toNat = 1088 from rfl]
  ihave ⟨%Mt0, Hms⟩ := ms_intro $$ [Hpc Hra Hregs HF]
  · iframe Hpc Hra Hregs; unfold blockOwn; iexact HF
  -- run 1: prologue, kind dispatch, stage the callee
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (s + 18446744073709550528#64) (evalNeed (.call f args) d - 1088) ∗
      world N L Room inp (.counted (k + (nf + na))) st d ∗
      CallK254T live N L Room inp Φ k st2 d fv vs s aX sret ret rv args.length
        (evalNeed (.call f args) d - 1088)))
  rotate_left
  · iframe Hdv Hms Hcode Hro Hfb Hst Hw; iexact Hk
  intro F'
  unfold evalEntryPC
  refine Call_run1 hlive hsf hs' hs2 hs3 hx1 hx2 hx3 (by ix_reg; exact hregs.a0)
    (by ix_reg; exact hregs.a1) (by ix_reg; exact hregs.a2) (by ix_reg; exact hregs.a3)
    (by ix_reg; exact hregs.sp) hn.kind hn.kindu hn.callee ?_
  intros
  apply swp_closeM
  intro Mt1 hMt1
  have hA1 : ldv .ld Mt1 (s.toNat - 1088) = aE := by subst hMt1; ix_fwd
  have hsv1 : CallSaved Mt1 s ret (rv 8) (rv 9) (rv 18) := by
    subst hMt1; constructor <;> (ix_fwd using [hoff]; ix_reg)
  unfold F'
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hw, Hk⟩, Hms⟩
  -- the callee
  ihave Hf := hf
  rw [show k + (nf + na) = k + na + nf by omega]
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x800031bc)
    (jalx_800031bc live (fun p hp => hlive _ (interp_code_800031bc p hp)))
    interp_code_800031bc (by decide) Df (k := k + na) (slot := s + 18446744073709550528#64 + 96#64)
    (aC := BitVec.ofNat 64 aF) (aE := aE) (s := s + 18446744073709550528#64)
    (m := evalNeed (.call f args) d - 1088)
    gF.child gF.fits gF.below gF.slotGeom hbf
  iframe Hf Hcode Hfb Hms Hst Hw
  isplitl []
  · ipureintro
    refine ⟨⟨by ix_reg, by ix_reg; exact hregs.a1, by ix_reg, by ix_reg; exact hregs.a3,
      by ix_reg⟩, fun b hb => ?_⟩
    have g1 := gF.slot; have g2 := gF.sp; simp only [VsaIris.InExt, evalSP] at hb g1 g2 ⊢; omega
  isplitl []
  · imodintro; rw [hFt]; iapply astEG_of_view hrf hgeo $$ Hro
  iintro %R1 %w0 %w1 %w2 %hkeep1 #Hv1 Hms Hst Hw

#ix_piece callPrefixT_p2 from callPrefixT_p1 by
  -- run 2: the count test, spill `s7`, `a6 = 0`, `blez`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (s + 18446744073709550528#64) (evalNeed (.call f args) d - 1088) ∗
      world N L Room inp (.counted (k + na)) st1 d ∗ □ valOf N fv w0 w1 w2 ∗
      CallK254T live N L Room inp Φ k st2 d fv vs s aX sret ret rv args.length
        (evalNeed (.call f args) d - 1088)))
  rotate_left
  · iframe Hdv Hms Hcode Hro Hfb Hst Hw Hv1; iexact Hk
  intro F'
  have hsmall := hn.small
  have hct : (BitVec.ofNat 64 args.length).toInt = args.length := ofNat_toInt_small hsmall
  refine Call_run2 (aE := aE) hlive hsf hs' hs2 hs3 hx1 hx2 hx3 ?_ ?_ hn.cnt ?_ ?_ ?_ ?_
  · ix_keep [hkeep1]
  · ix_keep [hkeep1]
  · rw [show s.toNat - 1088 = (s + 18446744073709550528#64 + 0#64).toNat by rw [BitVec.add_zero, hsf]]
    ix_fwd; rw [BitVec.add_zero, hsf]; exact hA1
  · -- more than 32 arguments: not this derivation's
    intro hc; exfalso
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
    rw [hct] at hc; unfold maxArgs at hlen
    have : ((32#64 : BitVec 64).toInt : Int) = 32 := by decide
    omega
  all_goals
    intro _ hz
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hz
    rw [hct] at hz
    intros
    apply swp_closeRM
    intro R2 Mt2 hR2 hMt2
    unfold F'
    iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hw, #Hv1, Hk⟩, Hms⟩
  rotate_left


#ix_piece callPrefixT_p3 from callPrefixT_p2 by
  -- the argument loop
  have h00 : ((0#64 : BitVec 64).toInt : Int) = 0 := by decide
  have hne : args ≠ [] := fun h => by subst h; simp at hz
  have hsv2 : CallSaved Mt2 s ret (rv 8) (rv 9) (rv 18) := by
    rw [hMt2]
    refine (hsv1.slotWrite w0 w1 w2 ?_).store _ ?_
    · rw [hoff 96 (by decide)]; omega
    · rw [hoff 1016 (by decide)]; omega
  have hm0 : ldv .ld Mt2 (s.toNat - 1088 + 96) = w0 := by rw [← hoff 96 (by decide), hMt2]; ix_fwd
  have hm1 : ldv .ld Mt2 (s.toNat - 1088 + 104) = w1 := by rw [← hoff 104 (by decide), hMt2]; ix_fwd
  have hm2 : ldv .ld Mt2 (s.toNat - 1088 + 112) = w2 := by rw [← hoff 112 (by decide), hMt2]; ix_fwd
  have hm23 : ldv .ld Mt2 (s.toNat - 1088 + 1016) = rv 23 := by
    rw [← hoff 1016 (by decide), hMt2]; ix_fwd; ix_keep [hkeep1]
  have hk2 : ∀ x ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], R2 x = rv x := by
    intro x hx
    have hx' : x = 19 ∨ x = 20 ∨ x = 21 ∨ x = 22 ∨ x = 23 ∨ x = 24 ∨ x = 25 ∨ x = 26 ∨ x = 27 := by
      simpa using hx
    clear hx
    subst hR2
    rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_keep [hkeep1]
  have hr2 : R2 2 = s + 18446744073709550528#64 := by subst hR2; ix_keep [hkeep1]
  have hr8 : R2 8 = aX := by subst hR2; ix_keep [hkeep1]
  have hr9 : R2 9 = sret := by subst hR2; ix_keep [hkeep1]
  have hr18 : R2 18 = BitVec.ofNat 64 inp := by subst hR2; ix_keep [hkeep1]
  have hr15 : R2 15 = BitVec.ofNat 64 args.length := by subst hR2; ix_reg
  ihave #Hast := astEG_of_view hrepr hgeo $$ Hro
  have hall : ∀ x ∈ args, evalNeed x d ≤ evalNeed (.call f args) d - 1088 ∧
      x.bodiesBound perCallBudget = true := fun x hx =>
    ⟨by have := evalNeed_call_arg (f := f) hx d; unfold evalFrame at this; omega,
     Expr.bodiesBoundList_mem hba hx⟩
  have hhead : ArgsHead R2 s aX (BitVec.ofNat 64 inp) aE 0 args.length :=
    ⟨hr2, hr8, hr18, by subst hR2; ix_reg, by subst hR2; ix_reg <;> rfl, hr15⟩
  iapply ha Φ k 0 f args [] aX aE s R2 Mt2 (evalNeed (.call f args) d - 1088) hne
    List.drop_zero.symm rfl hlen hhead ⟨hsf, hs', hs2, hs3⟩
    (stackGeom_evalSP hsg hneed hsf) hall
  iframe Hms Hcode Hast Hfb Hst Hw
  isplitl []
  · unfold argVals; iempintro
  simp only [List.nil_append]
  iintro %R' %Mt' %⟨hk', h16, hU⟩ Hms Hargs Hst Hw
  have hkR : ∀ x ∈ [2, 8, 9, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], R' x = R2 x :=
    fun x hx => hk' x ((by decide : ∀ y ∈ [2, 8, 9, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
      y ∈ argsKeep) x hx)
  have hcall : CallAt R' Mt' s aX sret (BitVec.ofNat 64 inp) ret rv w0 w1 w2 args.length :=
    CallAt.of_untouched hU ((hkR 2 (by decide)).trans hr2) ((hkR 8 (by decide)).trans hr8)
      ((hkR 9 (by decide)).trans hr9) ((hkR 18 (by decide)).trans hr18)
      ((hkR 15 (by decide)).trans hr15)
      (fun x hx => (hkR x ((by decide : ∀ y ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27],
        y ∈ [2, 8, 9, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) x hx)).trans (hk2 x hx))
      hm0 hm1 hm2 hsv2.ra hsv2.s0 hsv2.s1 hsv2.s2 hm23
  unfold CallK254T
  iapply Hk $$ %R' %Mt' %w0 %w1 %w2 %hcall Hv1 Hargs Hms Hst Hw

#ix_piece callPrefixT_p2b from callPrefixT_p2 at 2 by
  -- no arguments: straight to the dispatch
  have h00 : ((0#64 : BitVec 64).toInt : Int) = 0 := by decide
  have hnil : args = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hnil
  cases Da
  have hcall : CallAt R2 Mt2 s aX sret (BitVec.ofNat 64 inp) ret rv w0 w1 w2 0 := by
    have hsv2 : CallSaved Mt2 s ret (rv 8) (rv 9) (rv 18) := by
      rw [hMt2]
      refine (hsv1.slotWrite w0 w1 w2 ?_).store _ ?_
      · rw [hoff 96 (by decide)]; omega
      · rw [hoff 1016 (by decide)]; omega
    subst hR2
    refine CallAt.of_untouched (Untouched.refl _ _ _) (by ix_keep [hkeep1]) (by ix_keep [hkeep1])
      (by ix_keep [hkeep1]) (by ix_keep [hkeep1]) (by ix_reg; rfl) ?_ ?_ ?_ ?_
      hsv2.ra hsv2.s0 hsv2.s1 hsv2.s2 ?_
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_keep [hkeep1]
    · rw [← hoff 96 (by decide), hMt2]; ix_fwd
    · rw [← hoff 104 (by decide), hMt2]; ix_fwd
    · rw [← hoff 112 (by decide), hMt2]; ix_fwd
    · rw [← hoff 1016 (by decide), hMt2]; ix_fwd; ix_keep [hkeep1]
  unfold CallK254T
  iapply Hk $$ %R2 %Mt2 %w0 %w1 %w2 %hcall Hv1 [] Hms Hst Hw
  unfold argVals; iempintro

#ix_chain callPrefixT_c := [callPrefixT_p1, callPrefixT_p2, callPrefixT_p3]

/-- **The call prefix, total mode**: from `eval_expr`'s entry on a call node,
with the callee's spec at its derivation and the argument loop's motive (E6),
the arm reaches the kind dispatch `0x80003254` (`CallK254T`: `CallAt`, the
callee's words and meaning, the arguments' words, the stack below the
lowered `sp`, the world after both). -/
theorem callPrefixT {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 st2 : St} {d env : Nat} {f : Expr} {args : List Expr} {fv : Value} {vs : List Value}
    {nf na : Nat}
    (Df : EvalECost st d env f st1 fv nf) (hlen : args.length ≤ maxArgs)
    (Da : EvalArgsCost st1 d env args st2 vs na)
    (hf : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env f st1 fv nf Df)
    (ha : evalArgsT_body (GF := GF) live N L Room inp st1 d env args st2 vs na)
    {Φ : Nat × String → IProp GF} {k : Nat} {sret aE aX s ret : BitVec 64} {rv : Nat → BitVec 64}
    (hregs : EvalRegs rv sret (BitVec.ofNat 64 inp) aX aE s)
    (hsg : StackGeom s (evalNeed (.call f args) d))
    (hbb : (Expr.call f args).bodiesBound perCallBudget = true) (hal : ret.toNat % 4 = 0) :
    PC ↦ᵣ evalEntryPC ∗ ra ↦ᵣ ret ∗ regFile rv ∗ codeRes ∗ □ astEG aX.toNat (.call f args) ∗
      □ frameAt env aE.toNat ∗ stackScratch s (evalNeed (.call f args) d) ∗
      world N L Room inp (.counted (k + (nf + na))) st d ∗
      CallK254T live N L Room inp Φ k st2 d fv vs s aX sret ret rv args.length
        (evalNeed (.call f args) d - 1088)
    ⊢ (twpW (vsaModel live)).W Φ := by
  exact callPrefixT_c hlive Df hlen Da hf ha hregs hsg hbb hal
    (callPrefixT_p2b hlive Df hlen Da hf ha hregs hsg hbb hal)
