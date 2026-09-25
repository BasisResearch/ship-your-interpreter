import VsaIris.Interp.CallPrefix

/-!
# The call arm's shared runs as segment lemmas (lane E4)

The two runs of the call prefix, for either WP, each with its end state named
(CLAUDE.md law 6): `callSegA` (entry to the callee's `jal`, `CallA`) and
`callSegB` (after the callee to the argument count's three exits, `CallB`).
The total and partial prefixes (`CallPrefix.lean`, `CallPrefixP.lean`) are
these two plus the mode's child calls.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.RuntimeRepr

/-- The state at the callee's `jal` (`0x800031bc`). -/
structure CallA (R : Nat → BitVec 64) (Mt : Mem) (s aX aF aE sret inp ret : BitVec 64)
    (rv : Nat → BitVec 64) : Prop where
  args : EvalRegs R (s + 18446744073709550528#64 + 96#64) inp aF aE (s + 18446744073709550528#64)
  s0 : R 8 = aX
  s1 : R 9 = sret
  s2 : R 18 = inp
  keep : ∀ x ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], R x = rv x
  saved : CallSaved Mt s ret (rv 8) (rv 9) (rv 18)
  env : ldv .ld Mt (s.toNat - 1088) = aE

/-- The state after the count test (`blt`, the `s7` spill, `li a6,0`): the
callee-saved registers as at the `jal` (so as the callee returned them), `a3`
the frame pointer, `a5` the count, `a6 = 0`; the memory the callee's plus
the `s7` spill. -/
structure CallB (R R1 : Nat → BitVec 64) (Mt Mt1 : Mem) (s aE : BitVec 64) (argc : Nat) : Prop where
  keep : ∀ x ∈ calleeSaved, R x = R1 x
  a3 : R 13 = aE
  a5 : R 15 = BitVec.ofNat 64 argc
  a6 : R 16 = 0#64
  mem : Mt = writeLog Mt1 [((s + 18446744073709550528#64 + 1016#64).toNat, 8, R1 23)]

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
variable {live : Nat → Prop}

/-- **Run 1**, for either WP: prologue, kind dispatch, the callee staged. -/
theorem callSegA (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {m Mt0 : Mem} {P : Nat → Prop} {rv : Nat → BitVec 64}
    {s aX aF aE sret inp ret : BitVec 64} {argc : Nat}
    (hregs : EvalRegs rv sret inp aX aE s) (hn : CallNode m P aX aF argc) (hfg : EvalFrameG s) :
    roOwn roR (interpText ++ dataOf m (callView aX.toNat)) ∗
      ms evalEntryPC (upd rv 1 ret) (InExt (s.toNat - 1088, 1088)) Mt0 ∗
      (∀ R1 Mt1, ⌜CallA R1 Mt1 s aX aF aE sret inp ret rv ∧ R1 1 = ret⌝ -∗
        ms 0x800031bc#64 R1 (InExt (s.toNat - 1088, 1088)) Mt1 -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  have hsf := hfg.sf; have hs' := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  have hoff := evalSP_off (s := s) hsf (by omega)
  iintro ⟨#Hdv, Hms, Hk⟩
  iapply wp_swpF Wp (F := iprop(∀ R1 Mt1, ⌜CallA R1 Mt1 s aX aF aE sret inp ret rv ∧ R1 1 = ret⌝ -∗
        ms 0x800031bc#64 R1 (InExt (s.toNat - 1088, 1088)) Mt1 -∗ Wp.W Φ))
  rotate_left
  · iframe Hdv Hms; iexact Hk
  intro F'
  unfold evalEntryPC
  refine Call_run1 hlive hsf hs' hs2 hs3 hn.lo hn.hi hn.off (by ix_reg; exact hregs.a0)
    (by ix_reg; exact hregs.a1) (by ix_reg; exact hregs.a2) (by ix_reg; exact hregs.a3)
    (by ix_reg; exact hregs.sp) hn.kind hn.kindu hn.callee ?_
  intros
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  have hA : CallA R1 Mt1 s aX aF aE sret inp ret rv ∧ R1 1 = ret := by
    subst hR1
    refine ⟨⟨⟨by ix_reg, by ix_reg <;> exact hregs.a1, by ix_reg, by ix_reg <;> exact hregs.a3,
      by ix_reg⟩, by ix_reg, by ix_reg <;> exact hregs.a0, by ix_reg <;> exact hregs.a1, ?_, ?_, ?_⟩,
      by ix_reg⟩
    · intro x hx
      have hx' : x = 19 ∨ x = 20 ∨ x = 21 ∨ x = 22 ∨ x = 23 ∨ x = 24 ∨ x = 25 ∨ x = 26 ∨ x = 27 := by
        simpa using hx
      rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
    · subst hMt1; constructor <;> (ix_fwd using [hoff]; ix_reg)
    · subst hMt1; ix_fwd
  unfold F'
  iintro ⟨Hk, Hms⟩
  iapply Hk $$ %R1 %Mt1 %hA Hms

/-- **Run 2**, for either WP: the count test, the `s7` spill, `a6 = 0`, and
the three exits (the error at `0x80003fb0`, no arguments to `0x80003254`,
the loop head `0x800031dc`) as an additive triple. -/
theorem callSegB (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {m Mt1 : Mem} {P : Nat → Prop} {R1 : Nat → BitVec 64}
    {s aX aF aE : BitVec 64} {argc : Nat}
    (hn : CallNode m P aX aF argc) (hfg : EvalFrameG s)
    (h8 : R1 8 = aX) (h2 : R1 2 = s + 18446744073709550528#64)
    (hA : ldv .ld Mt1 (s.toNat - 1088) = aE) :
    roOwn roR (interpText ++ dataOf m (callView aX.toNat)) ∗
      ms 0x800031c0#64 R1 (InExt (s.toNat - 1088, 1088)) Mt1 ∗
      ((∀ R2 Mt2, ⌜32 < argc ∧ (∀ x, x ≠ 14 → x ≠ 15 → R2 x = R1 x) ∧ Mt2 = Mt1⌝ -∗
          ms 0x80003fb0#64 R2 (InExt (s.toNat - 1088, 1088)) Mt2 -∗ Wp.W Φ) ∧
       (∀ R2 Mt2, ⌜argc = 0 ∧ CallB R2 R1 Mt2 Mt1 s aE argc⌝ -∗
          ms 0x80003254#64 R2 (InExt (s.toNat - 1088, 1088)) Mt2 -∗ Wp.W Φ) ∧
       (∀ R2 Mt2, ⌜0 < argc ∧ argc ≤ 32 ∧ CallB R2 R1 Mt2 Mt1 s aE argc⌝ -∗
          ms 0x800031dc#64 R2 (InExt (s.toNat - 1088, 1088)) Mt2 -∗ Wp.W Φ))
    ⊢ Wp.W Φ := by
  have hsf := hfg.sf; have hs' := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hsmall := hn.small
  have hct : (BitVec.ofNat 64 argc).toInt = argc := ofNat_toInt_small hsmall
  have h32 : ((32#64 : BitVec 64).toInt : Int) = 32 := by decide
  have h00 : ((0#64 : BitVec 64).toInt : Int) = 0 := by decide
  iintro ⟨#Hdv, Hms, Hk⟩
  iapply wp_swpF Wp (F := iprop((∀ R2 Mt2, ⌜32 < argc ∧ (∀ x, x ≠ 14 → x ≠ 15 → R2 x = R1 x) ∧
          Mt2 = Mt1⌝ -∗ ms 0x80003fb0#64 R2 (InExt (s.toNat - 1088, 1088)) Mt2 -∗ Wp.W Φ) ∧
       (∀ R2 Mt2, ⌜argc = 0 ∧ CallB R2 R1 Mt2 Mt1 s aE argc⌝ -∗
          ms 0x80003254#64 R2 (InExt (s.toNat - 1088, 1088)) Mt2 -∗ Wp.W Φ) ∧
       (∀ R2 Mt2, ⌜0 < argc ∧ argc ≤ 32 ∧ CallB R2 R1 Mt2 Mt1 s aE argc⌝ -∗
          ms 0x800031dc#64 R2 (InExt (s.toNat - 1088, 1088)) Mt2 -∗ Wp.W Φ)))
  rotate_left
  · iframe Hdv Hms; iexact Hk
  intro F'
  refine Call_run2 (aE := aE) hlive hsf hs' hs2 hs3 hn.lo hn.hi hn.off h8 h2 hn.cnt ?_ ?_ ?_ ?_
  · exact hA
  · intro hc
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
    rw [hct] at hc
    intros
    apply swp_closeRM
    intro R2 Mt2 hR2 hMt2
    unfold F'
    iintro ⟨Hk, Hms⟩
    ihave Hk := and_elim_l $$ Hk
    iapply Hk $$ %R2 %Mt2 %⟨by omega, fun x h14 h15 => by subst hR2; simp only [upd_apply, if_neg h14, if_neg h15], hMt2⟩ Hms
  · intro hc hz
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc hz
    rw [hct] at hc hz
    intros
    apply swp_closeRM
    intro R2 Mt2 hR2 hMt2
    unfold F'
    iintro ⟨Hk, Hms⟩
    ihave Hk := and_elim_r $$ Hk
    ihave Hk := and_elim_l $$ Hk
    iapply Hk $$ %R2 %Mt2 %⟨by omega, ?_⟩ Hms
    subst hR2
    refine ⟨fun x hx => ?_, by ix_reg, by ix_reg, by ix_reg, hMt2⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  · intro hc hz
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc hz
    rw [hct] at hc hz
    intros
    apply swp_closeRM
    intro R2 Mt2 hR2 hMt2
    unfold F'
    iintro ⟨Hk, Hms⟩
    ihave Hk := and_elim_r $$ Hk
    ihave Hk := and_elim_r $$ Hk
    iapply Hk $$ %R2 %Mt2 %⟨by omega, by omega, ?_⟩ Hms
    subst hR2
    refine ⟨fun x hx => ?_, by ix_reg, by ix_reg, by ix_reg, hMt2⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg


/-- **The state at the kind dispatch, from the segments' end states**: the
state at the callee's `jal` (`CallA`), the callee's kept registers and result
words, the count test (`CallB`), and the argument loop (its kept registers,
the frame outside its writes). -/
theorem CallAt.of_seg {R1 R1' R2 R : Nat → BitVec 64} {Mt1 Mt2 Mt : Mem}
    {s aX aF aE sret inp ret w0 w1 w2 : BitVec 64} {rv : Nat → BitVec 64} {argc : Nat}
    (hfg : EvalFrameG s) (hA : CallA R1 Mt1 s aX aF aE sret inp ret rv)
    (hkeep1 : KeepRegs calleeSaved R1 R1')
    (hB : CallB R2 (upd R1' 1 (BitVec.ofNat 64 (0x800031bc + 4))) Mt2
      (slotWrite Mt1 (s + 18446744073709550528#64 + 96#64).toNat w0 w1 w2) s aE argc)
    (hU : Untouched (InExt (s.toNat - 1088, 1088)) (argsW s) Mt2 Mt)
    (hk : ∀ x ∈ argsKeep, R x = R2 x) :
    CallAt R Mt s aX sret inp ret rv w0 w1 w2 argc := by
  have hsf := hfg.sf
  have hoff := evalSP_off (s := s) hsf (by have := hfg.hi; omega)
  have kr : ∀ x ∈ calleeSaved, R x = R1 x := fun x hx => by
    rw [hk x ((by decide : ∀ y ∈ calleeSaved, y ∈ argsKeep) x hx), hB.keep x hx, upd_apply,
      if_neg ((by decide : ∀ y ∈ calleeSaved, y ≠ 1) x hx), hkeep1 x hx]
  have hsv : CallSaved Mt2 s ret (rv 8) (rv 9) (rv 18) := by
    rw [hB.mem]
    refine (hA.saved.slotWrite w0 w1 w2 ?_).store _ ?_
    · rw [hoff 96 (by decide)]; have := hfg.lo; omega
    · rw [hoff 1016 (by decide)]; have := hfg.lo; omega
  refine CallAt.of_untouched hU ((kr 2 (by decide)).trans hA.args.sp) ((kr 8 (by decide)).trans hA.s0)
    ((kr 9 (by decide)).trans hA.s1) ((kr 18 (by decide)).trans hA.s2)
    ((hk 15 (by decide)).trans hB.a5)
    (fun x hx => (kr x ((by decide : ∀ y ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], y ∈ calleeSaved)
      x hx)).trans (hA.keep x hx)) ?_ ?_ ?_ hsv.ra hsv.s0 hsv.s1 hsv.s2 ?_
  · rw [← hoff 96 (by decide), hB.mem]; ix_fwd
  · rw [← hoff 104 (by decide), hB.mem]; ix_fwd
  · rw [← hoff 112 (by decide), hB.mem]; ix_fwd
  · rw [← hoff 1016 (by decide), hB.mem]; ix_fwd
    ix_reg; rw [hkeep1 23 (by decide)]; exact hA.keep 23 (by decide)

end

end VsaIris.Interp

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

-- The too-many-arguments error: the line (havoc), `runtime_error(in, line,
-- "too many arguments (max 32)", 0, 0)` staged, `s3`-`s7` spilled.
#ix_seg Call_runTM {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 28 ≤ 0x100000000)
    (hx3 : aX.toNat + 28 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64) :
    IW live m (callView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x80003fb0#64 R Mt
  by ix_run hlive using [h8, h2, hsf] at 0x80003fdc

end VsaIris.Interp
