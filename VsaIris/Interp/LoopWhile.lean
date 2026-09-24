import VsaIris.Interp.LoopKit

/-!
# The `while` loop (lane E6), both modes

INTERP_DESIGN.md §4.3; statements in `SpecLoop.lean` (`whileT_body`,
`whileP_body`). The loop head is `0x8000403c` inside `exec_stmt`'s frame.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- The bytes of a `while` node a run reads: the condition and body pointers. -/
abbrev whileView (a : Nat) : List Nat := accAddrs (a + 8) 16

#ix_seg WhileLoop_runA {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s pC : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 24 ≤ 0x100000000)
    (hx3 : aS.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h2 : R 2 = s + 18446744073709551440#64)
    (hc : ldv .ld m (aS + 8#64).toNat = pC) :
    IW live m (whileView aS.toNat) (execS s) Q 0x8000403c#64 R Mt
  by ix_run hlive using [h8, h2, hc] at 0x8000404c

#ix_seg WhileLoop_runB {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709551440#64) :
    IW live m [] (execS s) Q 0x80004050#64 R Mt
  by ix_run hlive using [h2, hsf] at 0x8000406c

#ix_seg WhileLoop_runC {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s pB : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 24 ≤ 0x100000000)
    (hx3 : aS.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (hb : ldv .ld m (aS + 16#64).toNat = pB) :
    IW live m (whileView aS.toNat) (execS s) Q 0x80004070#64 R Mt
  by ix_run hlive using [h8, hb] at 0x80004084 0x8000409c

#ix_seg WhileLoop_runD {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} :
    IW live m [] (execS s) Q 0x80004088#64 R Mt
  by ix_run hlive at 0x8000403c 0x8000409c 0x80004150

/-- What a `while` node gives the runs: the condition and body pointers, its
placement and its view. -/
structure WhileNode (m : Mem) (P : Nat → Prop) (aS pC pB : BitVec 64) : Prop where
  cond : ldv .ld m (aS + 8#64).toNat = pC
  body : ldv .ld m (aS + 16#64).toNat = pB
  lo : 0x80000000 ≤ aS.toNat
  hi : aS.toNat + 24 ≤ 0x100000000
  off : aS.toNat + 24 ≤ Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 16 ≤ aS.toNat
  view : ∀ a ∈ whileView aS.toNat, P a ∧ (m[a]?).isSome

/-- A `while` node's facts, from its representation over a geometric view. -/
theorem whileNode_of_repr {m : Mem} {P : Nat → Prop} {aS : BitVec 64} {c : Expr} {b : Stmt}
    (h : StmtReprWithin m P aS.toNat (.whileStmt c b)) (hg : ∀ k, P k → ReadOK k) :
    ∃ pc pb : Nat, WhileNode m P aS (BitVec.ofNat 64 pc) (BitVec.ofNat 64 pb) ∧
      ExprReprWithin m P pc c ∧ StmtReprWithin m P pb b ∧ pc < 2 ^ 64 ∧ pb < 2 ^ 64 := by
  cases h with
  | whileS h4 c4 hc cc hrc hb cb hrb =>
    rename_i pc pb
    have g0 := hg _ (c4 0 (by omega)); have g3 := hg _ (c4 3 (by omega))
    have g8 := hg _ (cc 0 (by omega)); have g23 := hg _ (cb 7 (by omega))
    have e8 : (aS + 8#64).toNat = aS.toNat + 8 := by
      have := g23.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e16 : (aS + 16#64).toNat = aS.toNat + 16 := by
      have := g23.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine ⟨pc, pb, ⟨?_, ?_, g0.lo, ?_, ?_, ?_⟩, hrc, hrb, readLE_lt hc, readLE_lt hb⟩
    · rw [e8]; exact ldv_ld_read64 hc
    · rw [e16]; exact ldv_ld_read64 hb
    · have := g23.hi; simp only [Nat.add_zero] at *; omega
    · have h0 := g0.off; have h3 := g3.off; have h8' := g8.off; have h23 := g23.off
      simp only [Nat.add_zero] at *; omega
    · intro a ha
      simp only [mem_accAddrs_iff] at ha
      by_cases hj : a < aS.toNat + 16
      · obtain ⟨j, rfl⟩ : ∃ j, a = aS.toNat + 8 + j := ⟨a - (aS.toNat + 8), by omega⟩
        exact ⟨cc j (by omega), isSome_of_readLE hc (by omega)⟩
      · obtain ⟨j, rfl⟩ : ∃ j, a = aS.toNat + 16 + j := ⟨a - (aS.toNat + 16), by omega⟩
        exact ⟨cb j (by omega), isSome_of_readLE hb (by omega)⟩

/-- Where the `while` loop goes after its body returned `status`: out on
`break` (shared epilogue, `a0 = 0`) or a returned value (the `ret`
epilogue), back to the head otherwise. -/
def whileNext : Status → BitVec 64
  | .brk => 0x8000409c#64
  | .ret _ => 0x80004150#64
  | _ => 0x8000403c#64

/-- `a0` after the status routing: `0` on `break`, the status otherwise. -/
def whileA0 : Status → BitVec 64
  | .brk => 0#64
  | st => statusCode st

/-! ## The runs' glue, for either WP -/

section Glue

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {inp : Nat}

omit I in
/-- **Run A**: from the loop head to the condition's `jal eval_expr`
(`0x8000404c`), the result slot `sp+80` in `a0`. -/
theorem whileStage (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {c : Expr} {b : Stmt} {aS aEnv aRet s : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem} (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv) :
    ms 0x8000403c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.whileStmt c b) ∗
      (∀ (R1 : Nat → BitVec 64) (aC : BitVec 64),
        ⌜EvalRegs R1 (s + 18446744073709551440#64 + 80#64) (BitVec.ofNat 64 inp) aC aEnv
            (s + 18446744073709551440#64) ∧ KeepRegs calleeSaved R R1⌝ -∗
        □ astEG aC.toNat c -∗ ms 0x8000404c#64 R1 (execS s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, Hk⟩
  ihave ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩ := astSG_elim _ _ $$ Hast
  obtain ⟨pc, pb, hn, hrc, -, hpc, -⟩ := whileNode_of_repr hrepr hgeo
  have hPt : (BitVec.ofNat 64 pc).toNat = pc := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc]
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(roOn P m ∗ (∀ (R1 : Nat → BitVec 64) (aC : BitVec 64),
        ⌜EvalRegs R1 (s + 18446744073709551440#64 + 80#64) (BitVec.ofNat 64 inp) aC aEnv
            (s + 18446744073709551440#64) ∧ KeepRegs calleeSaved R R1⌝ -∗
        □ astEG aC.toNat c -∗ ms 0x8000404c#64 R1 (execS s) Mt -∗ Wp.W Φ)))
  rotate_left
  · iframe Hdv Hms Hro; iexact Hk
  intro F'
  refine WhileLoop_runA hlive hn.lo hn.hi hn.off hh.s0 hh.sp hn.cond ?_
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨#Hro, Hk⟩, Hms⟩
  iapply Hk $$ %_ %(BitVec.ofNat 64 pc) %⟨⟨by ix_reg, by ix_reg; exact hh.s1, by ix_reg,
    by ix_reg; exact hh.s3, by ix_reg; exact hh.sp⟩, by keep_upd⟩ [] Hms
  imodintro; rw [hPt]; iapply astEG_of_view hrc hgeo $$ Hro

/-- **Run B and `value_truthy`**: from the condition's return (its three
words in the slot `sp+80`, meaning `v`), the copy to `sp+16` and the helper;
the truthiness bit in `a0` at the branch `0x80004070`. -/
theorem whileCopy (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N Wp p v)
    {Φ : Nat × String → IProp GF} {v : Value} {w0 w1 w2 : BitVec 64} {s : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem} (hfg : ExecFrameGeom s) (hsp : R 2 = s + 18446744073709551440#64) :
    ms (BitVec.ofNat 64 (0x8000404c + 4)) R (execS s)
        (slotWrite Mt (s + 18446744073709551440#64 + 80#64).toNat w0 w1 w2) ∗ codeRes ∗
      □ valOf N v w0 w1 w2 ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = (if v.truthy then 1#64 else 0#64) ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x80004070#64 R' (execS s) Mt' -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, #Hv, Hk⟩
  have hs80 := execSlot hfg (o := 80) (by omega) rfl
  have hs16 := execSlot hfg (o := 16) (by omega) rfl
  have hoff := execSP_off hfg
  ihave #Hdv := roOwn_code (m := Mt) $$ Hcode
  iapply wp_swpF Wp (F := iprop(codeRes ∗ □ valOf N v w0 w1 w2 ∗ ∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = (if v.truthy then 1#64 else 0#64) ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x80004070#64 R' (execS s) Mt' -∗ Wp.W Φ))
  rotate_left
  · iframe Hdv Hms Hcode Hv; iexact Hk
  intro F'
  refine WhileLoop_runB hlive hfg.sf hfg.lo hfg.hi hfg.al hsp ?_
  intros
  apply swp_closeRM
  intro R3 Mt3 hR3 hMt3
  unfold F'
  iintro ⟨⟨#Hcode, #Hv, Hk⟩, Hms⟩
  have e0 : imgW (imgM Mt3) (s + 18446744073709551440#64 + 16#64).toNat = w0 := by
    rw [← ldv_ld_imgW, hMt3]; ix_fwd using [hoff]
  have e8 : imgW (imgM Mt3) ((s + 18446744073709551440#64 + 16#64).toNat + 8) = w1 := by
    rw [← ldv_ld_imgW, hMt3]; ix_fwd using [hoff]
  have e16 : imgW (imgM Mt3) ((s + 18446744073709551440#64 + 16#64).toNat + 16) = w2 := by
    rw [← ldv_ld_imgW, hMt3]; ix_fwd using [hoff]
  ihave Ht := htr $$ %(s + 18446744073709551440#64 + 16#64) %v
  iapply ms_truthyCall Wp (N := N) (R := R3) (Mt := Mt3) (v := v) (i := 0x8000406c)
    (jalx_8000406c live (fun p hp => hlive _ (interp_code_8000406c p hp)))
    interp_code_8000406c (by decide) (execSlot_in hs16 (by omega)) (by rw [hR3]; ix_reg) hs16.geo
  iframe Ht Hcode Hms
  isplitl []
  · imodintro; unfold valImg; rw [e0, e8, e16]; iexact Hv
  iintro %R4 %Mt4 %⟨hkeep4, htr4, hag4⟩ Hms
  iapply Hk $$ %_ %Mt4 %⟨?_, by ix_reg; exact htr4, ?_⟩ Hms
  · refine KeepRegs.upd_right (KeepRegs.trans ?_ (KeepRegs.of_helper hkeep4 (by decide))) (by decide) _
    rw [hR3]; keep_upd
  · refine Untouched.trans (Untouched.slotWrite hs80 (by omega) (by omega) Mt w0 w1 w2) ?_
    refine Untouched.trans ?_
      (fun a ha hw => hag4 a ha fun hin => hw (execSlot_W hs16 (Nat.le_refl _) (by omega) a hin))
    rw [hMt3]
    exact Untouched.trans (Untouched.trans (Untouched.store hfg (o := 16) (Nat.le_refl _) (by omega) _ _)
      (Untouched.store hfg (o := 24) (by omega) (by omega) _ _))
      (Untouched.store hfg (o := 32) (by omega) (by omega) _ _)

omit I in
/-- **Run C, false side**: a false condition leaves normally (`a0 = 0`). -/
theorem whileExitFalse (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {c : Expr} {b : Stmt} {aS s : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem} (hs0 : R 8 = aS) (h10 : R 10 = 0#64) :
    ms 0x80004070#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.whileStmt c b) ∗
      (ms 0x8000409c#64 (upd R 10 0#64) (execS s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, Hk⟩
  ihave ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩ := astSG_elim _ _ $$ Hast
  obtain ⟨pc, pb, hn, -, -, -, -⟩ := whileNode_of_repr hrepr hgeo
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(ms 0x8000409c#64 (upd R 10 0#64) (execS s) Mt -∗ Wp.W Φ))
  rotate_left
  · iframe Hdv Hms; iexact Hk
  intro F'
  refine WhileLoop_runC (s := s) hlive hn.lo hn.hi hn.off hs0 hn.body ?_ (fun h => absurd h10 h)
  intro _
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨Hk, Hms⟩
  iapply Hk $$ Hms

omit I in
/-- **Run C, true side**: a true condition stages the body's
`jal exec_stmt` (`0x80004084`) with the arm's own `ret` slot. -/
theorem whileStageBody (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {c : Expr} {b : Stmt} {aS aEnv aRet s : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem} (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv)
    (h10 : R 10 ≠ 0#64) :
    ms 0x80004070#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.whileStmt c b) ∗
      (∀ (R1 : Nat → BitVec 64) (aB : BitVec 64),
        ⌜ExecRegs R1 (BitVec.ofNat 64 inp) aB aEnv aRet (s + 18446744073709551440#64) ∧
          KeepRegs calleeSaved R R1⌝ -∗
        □ astSG aB.toNat b -∗ ms 0x80004084#64 R1 (execS s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, Hk⟩
  ihave ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩ := astSG_elim _ _ $$ Hast
  obtain ⟨pc, pb, hn, -, hrb, -, hpb⟩ := whileNode_of_repr hrepr hgeo
  have hPt : (BitVec.ofNat 64 pb).toNat = pb := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpb]
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(roOn P m ∗ (∀ (R1 : Nat → BitVec 64) (aB : BitVec 64),
        ⌜ExecRegs R1 (BitVec.ofNat 64 inp) aB aEnv aRet (s + 18446744073709551440#64) ∧
          KeepRegs calleeSaved R R1⌝ -∗
        □ astSG aB.toNat b -∗ ms 0x80004084#64 R1 (execS s) Mt -∗ Wp.W Φ)))
  rotate_left
  · iframe Hdv Hms Hro; iexact Hk
  intro F'
  refine WhileLoop_runC (s := s) hlive hn.lo hn.hi hn.off hh.s0 hn.body (fun h => absurd h h10) ?_
  intro _
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨#Hro, Hk⟩, Hms⟩
  iapply Hk $$ %_ %(BitVec.ofNat 64 pb) %⟨⟨by ix_reg; exact hh.s1, by ix_reg, by ix_reg; exact hh.s3,
    by ix_reg; exact hh.s2, by ix_reg; exact hh.sp⟩, by keep_upd⟩ [] Hms
  imodintro; rw [hPt]; iapply astSG_of_view hrb hgeo $$ Hro

omit I in
/-- **Run D, the status routing** (`bne a0,1`, `beq a0,3`) after the body
returned `status` in `a0`. -/
theorem whileRoute (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {status : Status} {s : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem} (h10 : R 10 = statusCode status) :
    ms (BitVec.ofNat 64 (0x80004084 + 4)) R (execS s) Mt ∗ codeRes ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs calleeSaved R R' ∧ R' 10 = whileA0 status⌝ -∗
        ms (whileNext status) R' (execS s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, Hk⟩
  ihave #Hdv := roOwn_code (m := Mt) $$ Hcode
  iapply wp_swpF Wp (F := iprop(∀ R' : Nat → BitVec 64,
      ⌜KeepRegs calleeSaved R R' ∧ R' 10 = whileA0 status⌝ -∗
        ms (whileNext status) R' (execS s) Mt -∗ Wp.W Φ))
  rotate_left
  · iframe Hdv Hms; iexact Hk
  intro F'
  refine WhileLoop_runD (s := s) hlive ?_ ?_ ?_
  · -- `a0 = 3`: a returned value
    intro _ hc3
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc3
    intros
    apply swp_closeF
    unfold F'
    cases status with
    | ret rv =>
      simp only [whileNext, whileA0]
      iintro ⟨Hk, Hms⟩
      iapply Hk $$ %_ %⟨by keep_upd, by ix_reg; exact h10⟩ Hms
    | _ => exfalso; rw [h10] at hc3; simp [statusCode] at hc3
  · -- `a0 ∈ {0, 2}`: back to the head
    intro h1 hc3
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc3 h1
    intros
    apply swp_closeF
    unfold F'
    cases status with
    | normal | cont =>
      simp only [whileNext, whileA0]
      iintro ⟨Hk, Hms⟩
      iapply Hk $$ %_ %⟨by keep_upd, by ix_reg; exact h10⟩ Hms
    | brk => exfalso; exact h1 h10
    | ret _ => exfalso; exact hc3 h10
  · -- `a0 = 1`: break
    intro h1
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, Decidable.not_not] at h1
    intros
    apply swp_closeF
    unfold F'
    cases status with
    | brk =>
      simp only [whileNext, whileA0]
      iintro ⟨Hk, Hms⟩
      iapply Hk $$ %_ %⟨by keep_upd, by ix_reg⟩ Hms
    | _ => exfalso; rw [h10] at h1; simp [statusCode] at h1

end Glue

/-! ## Total mode -/

section Cond

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- **The `while` condition, total mode**: from the loop head, the condition
into `sp+80` (its derivation `Dc`), the copy to `sp+16`, `value_truthy`; the
state at the branch `0x80004070` has the truthiness bit in `a0`. -/
theorem whileCondT (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {st : St} {d env : Nat} {c : Expr} {b : Stmt} {st' : St} {v : Value} {nc k : Nat}
    (Dc : EvalECost st d env c st' v nc)
    (hc : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env c st' v nc Dc)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p v)
    {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {m' : Nat}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv) (hfg : ExecFrameGeom s)
    (hsg : StackGeom (s + 18446744073709551440#64) m') (hfit : evalNeed c d ≤ m')
    (hcb : c.bodiesBound perCallBudget = true) :
    ms 0x8000403c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.whileStmt c b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      world N L Room inp (.counted (k + nc)) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = (if v.truthy then 1#64 else 0#64) ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x80004070#64 R' (execS s) Mt' -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)
    ⊢ (twpW (vsaModel live)).W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hw, Hk⟩
  iapply whileStage (twpW _) hlive hh
  iframe Hms Hcode Hast
  iintro %R1 %aC %⟨hregs, hk1⟩ #Hac Hms
  ihave Hc := hc
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x8000404c)
    (jalx_8000404c live (fun p hp => hlive _ (interp_code_8000404c p hp)))
    interp_code_8000404c (by decide) Dc (k := k) (hsg.narrow hfit) hfit hsg.le
    (execSlot hfg (o := 80) (by omega) rfl).geo hcb
  iframe Hc Hcode Hac Hfr Hms Hst Hw
  isplitl []
  · ipureintro; exact ⟨hregs, execSlot_in (execSlot hfg (o := 80) (by omega) rfl) (by omega)⟩
  iintro %R2 %w0 %w1 %w2 %hk2 #Hv Hms Hst Hw
  iapply whileCopy (twpW _) (R := upd R2 1 (BitVec.ofNat 64 (0x8000404c + 4))) hlive htr hfg
    (by ix_reg; rw [keep_reg hk2 (by decide)]; exact hregs.sp)
  iframe Hms Hcode Hv
  iintro %R3 %Mt3 %⟨hk3, h30, hut⟩ Hms
  iapply Hk $$ %R3 %Mt3 %⟨KeepRegs.trans (KeepRegs.trans hk1 (hk2.calleeSaved_upd (by decide) _)) hk3,
    h30, hut⟩ Hms Hst Hw

/-- **The `while` body, total mode**: from the branch `0x80004070` with a true
condition, the body through `exec_stmt` (its derivation `Db`) and the status
routing (`bne a0,1`, `beq a0,3`). The frame bytes are unchanged. -/
theorem whileBodyT (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {st : St} {d env : Nat} {c : Expr} {b : Stmt} {st' : St} {status : Status} {nb k : Nat}
    (Db : ExecSCost st d env b st' status nb)
    (hb : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env b st' status nb Db)
    {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {m' : Nat}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv)
    (hsg : StackGeom (s + 18446744073709551440#64) m') (hfit : execNeed b d ≤ m')
    (hbb : b.bodiesBound perCallBudget = true) (hslg : SlotGeom aRet) (h10 : R 10 ≠ 0#64) :
    ms 0x80004070#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.whileStmt c b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp (.counted (k + nb)) st d ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs calleeSaved R R' ∧ R' 10 = whileA0 status⌝ -∗
        ms (whileNext status) R' (execS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N aRet.toNat status -∗ world N L Room inp (.counted k) st' d -∗
        (twpW (vsaModel live)).W Φ)
    ⊢ (twpW (vsaModel live)).W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, Hk⟩
  iapply whileStageBody (twpW _) hlive hh h10
  iframe Hms Hcode Hast
  iintro %R1 %aB %⟨hregs, hk1⟩ #Hab Hms
  ihave Hb := hb
  iapply ms_callExecT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80004084)
    (jalx_80004084 live (fun p hp => hlive _ (interp_code_80004084 p hp)))
    interp_code_80004084 (by decide) Db (k := k) (hsg.narrow hfit) hfit hsg.le hslg hbb
  iframe Hb Hcode Hab Hfr Hms Hst Hslot Hw
  isplitl []
  · ipureintro; exact hregs
  iintro %R2 %⟨hk2, h20⟩ Hms Hst Hret Hw
  iapply whileRoute (twpW _) (R := upd R2 1 (BitVec.ofNat 64 (0x80004084 + 4))) hlive
    (by ix_reg; exact h20)
  iframe Hms Hcode
  iintro %R3 %⟨hk3, h30⟩ Hms
  iapply Hk $$ %R3 %⟨KeepRegs.trans (KeepRegs.trans hk1 (hk2.calleeSaved_upd (by decide) _)) hk3,
    h30⟩ Hms Hst Hret Hw

end Cond

/-! ## Total mode: one lemma per `ExecSCost` `while` constructor -/

section Total

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- `whileFalse`: the condition is false; the loop leaves normally. -/
theorem whileT_false (hlive : ∀ p ∈ interpText, live p.1)
    {st : St} {d env : Nat} {c : Expr} {b : Stmt} {st' : St} {v : Value} {nc : Nat}
    (Dc : EvalECost st d env c st' v nc) (hv : v.truthy = false)
    (hc : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env c st' v nc Dc)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p v) :
    whileT_body (GF := GF) live N L Room inp st d env c b st' .normal nc := by
  intro Φ k aS aEnv aRet s R Mt m' hh hfg hsg hfits hslg
  simp only [loopExit]
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, Hk⟩
  iapply whileCondT (b := b) hlive Dc hc htr hh hfg hsg hfits.cond hfits.condB
  iframe Hms Hcode Hast Hfr Hst Hw
  iintro %R1 %Mt1 %⟨hk1, h10, hut⟩ Hms Hst Hw
  rw [hv] at h10
  ihave ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩ := astSG_elim _ _ $$ Hast
  obtain ⟨pc, pb, hn, -, -, -, -⟩ := whileNode_of_repr hrepr hgeo
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp (.counted k) st' d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode .normal ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x8000409c#64 R' (execS s) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat .normal -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms Hst Hslot Hw; iexact Hk
  intro F'
  refine WhileLoop_runC (s := s) hlive hn.lo hn.hi hn.off ((hk1 8 (by decide)).trans hh.s0) hn.body
    ?_ (fun h => absurd (by simpa using h10) h)
  intro _
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨Hst, Hslot, Hw, Hk⟩, Hms⟩
  simp only [statusRet_normal]
  iapply Hk $$ %_ %Mt1 %⟨hk1.calleeSaved_upd (by decide) _, by ix_reg; rfl, hut⟩ Hms Hst Hslot Hw

/-- `whileBreak`: the condition holds and the body breaks; the loop leaves
normally. -/
theorem whileT_break (hlive : ∀ p ∈ interpText, live p.1)
    {st : St} {d env : Nat} {c : Expr} {b : Stmt} {st' st'' : St} {v : Value} {nc nb : Nat}
    (Dc : EvalECost st d env c st' v nc) (hv : v.truthy = true)
    (Db : ExecSCost st' d env b st'' .brk nb)
    (hc : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env c st' v nc Dc)
    (hb : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st' d env b st'' .brk nb Db)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p v) :
    whileT_body (GF := GF) live N L Room inp st d env c b st'' .normal (nc + nb) := by
  intro Φ k aS aEnv aRet s R Mt m' hh hfg hsg hfits hslg
  simp only [loopExit]
  rw [show k + (nc + nb) = k + nb + nc by omega]
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, Hk⟩
  iapply whileCondT (b := b) hlive Dc hc htr hh hfg hsg hfits.cond hfits.condB
  iframe Hms Hcode Hast Hfr Hst Hw
  iintro %R1 %Mt1 %⟨hk1, h10, hut⟩ Hms Hst Hw
  rw [hv] at h10
  iapply whileBodyT (c := c) hlive Db hb (hh.keep hk1) hsg hfits.body hfits.bodyB hslg
    (by rw [h10]; decide)
  iframe Hms Hcode Hast Hfr Hst Hslot Hw
  iintro %R2 %⟨hk2, h20⟩ Hms Hst Hret Hw
  simp only [whileNext, whileA0, statusRet_normal, statusRet_brk]
  iapply Hk $$ %R2 %Mt1 %⟨KeepRegs.trans hk1 hk2, h20, hut⟩ Hms Hst Hret Hw

/-- `whileRet`: the condition holds and the body returns a value; the loop
leaves through the `ret` epilogue. -/
theorem whileT_ret (hlive : ∀ p ∈ interpText, live p.1)
    {st : St} {d env : Nat} {c : Expr} {b : Stmt} {st' st'' : St} {v rv : Value} {nc nb : Nat}
    (Dc : EvalECost st d env c st' v nc) (hv : v.truthy = true)
    (Db : ExecSCost st' d env b st'' (.ret rv) nb)
    (hc : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env c st' v nc Dc)
    (hb : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st' d env b st'' (.ret rv) nb Db)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p v) :
    whileT_body (GF := GF) live N L Room inp st d env c b st'' (.ret rv) (nc + nb) := by
  intro Φ k aS aEnv aRet s R Mt m' hh hfg hsg hfits hslg
  simp only [loopExit]
  rw [show k + (nc + nb) = k + nb + nc by omega]
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, Hk⟩
  iapply whileCondT (b := b) hlive Dc hc htr hh hfg hsg hfits.cond hfits.condB
  iframe Hms Hcode Hast Hfr Hst Hw
  iintro %R1 %Mt1 %⟨hk1, h10, hut⟩ Hms Hst Hw
  rw [hv] at h10
  iapply whileBodyT (c := c) hlive Db hb (hh.keep hk1) hsg hfits.body hfits.bodyB hslg
    (by rw [h10]; decide)
  iframe Hms Hcode Hast Hfr Hst Hslot Hw
  iintro %R2 %⟨hk2, h20⟩ Hms Hst Hret Hw
  simp only [whileNext, whileA0, statusRet_normal, statusRet_brk]
  iapply Hk $$ %R2 %Mt1 %⟨KeepRegs.trans hk1 hk2, h20, hut⟩ Hms Hst Hret Hw

/-- `whileLoop`: the condition holds, the body completes normally or
continues, and the loop runs again from the head (the motive of the
recursive premise, `hr`). -/
theorem whileT_loop (hlive : ∀ p ∈ interpText, live p.1)
    {st : St} {d env : Nat} {c : Expr} {b : Stmt} {st₁ st₂ st₃ : St} {v : Value}
    {status status' : Status} {nc nb nr : Nat}
    (Dc : EvalECost st d env c st₁ v nc) (hv : v.truthy = true)
    (Db : ExecSCost st₁ d env b st₂ status nb) (hst : status = .normal ∨ status = .cont)
    (hc : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env c st₁ v nc Dc)
    (hb : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st₁ d env b st₂ status nb Db)
    (hr : whileT_body (GF := GF) live N L Room inp st₂ d env c b st₃ status' nr)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p v) :
    whileT_body (GF := GF) live N L Room inp st d env c b st₃ status' (nc + nb + nr) := by
  intro Φ k aS aEnv aRet s R Mt m' hh hfg hsg hfits hslg
  rw [show k + (nc + nb + nr) = k + nr + nb + nc by omega]
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, Hk⟩
  iapply whileCondT (b := b) hlive Dc hc htr hh hfg hsg hfits.cond hfits.condB
  iframe Hms Hcode Hast Hfr Hst Hw
  iintro %R1 %Mt1 %⟨hk1, h10, hut⟩ Hms Hst Hw
  rw [hv] at h10
  iapply whileBodyT (c := c) hlive Db hb (hh.keep hk1) hsg hfits.body hfits.bodyB hslg
    (by rw [h10]; decide)
  iframe Hms Hcode Hast Hfr Hst Hslot Hw
  iintro %R2 %⟨hk2, -⟩ Hms Hst Hret Hw
  rcases hst with rfl | rfl <;>
  · simp only [whileNext]
    simp only [statusRet_normal, statusRet_cont]
    iapply hr Φ k aS aEnv aRet s R2 Mt1 m' ((hh.keep hk1).keep hk2) hfg hsg hfits hslg
    iframe Hms Hcode Hast Hfr Hst Hret Hw
    iintro %R3 %Mt3 %⟨hk3, h30, hut3⟩ Hms Hst Hret Hw
    iapply Hk $$ %R3 %Mt3 %⟨KeepRegs.trans (KeepRegs.trans hk1 hk2) hk3, h30, hut.trans hut3⟩
      Hms Hst Hret Hw

end Total

/-! ## Partial mode: Löb -/

section Partial

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- **The `while` condition, partial mode**: as `whileCondT`, through the Löb
hypothesis; the condition's `jal` also strips the later of `X`. The
continuation pair `K ∧ A` is used by both branches and handed on. -/
theorem whileCondP (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p v)
    {Core X K : IProp GF} {st : St} {d env : Nat} {c : Expr} {b : Stmt}
    {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {m' : Nat}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv) (hfg : ExecFrameGeom s)
    (hsg : StackGeom (s + 18446744073709551440#64) m') (hfit : evalNeed c d ≤ m')
    (hcb : c.bodiesBound perCallBudget = true) :
    ms 0x8000403c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.whileStmt c b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      world N L Room inp .uncounted st d ∗ evalSpecsP (vsaModel live) N L Room inp Core ∗ ▷ X ∗
      (K ∧ (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ ownSet (execS s) byteAny) -∗
        (wpW (vsaModel live)).W Φ)) ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (v : Value), ⌜EvalE st d env c st' v⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = (if v.truthy then 1#64 else 0#64) ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x80004070#64 R' (execS s) Mt' -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        world N L Room inp .uncounted st' d -∗ X -∗
        (K ∧ (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ ownSet (execS s) byteAny) -∗
          (wpW (vsaModel live)).W Φ)) -∗ (wpW (vsaModel live)).W Φ)
    ⊢ (wpW (vsaModel live)).W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hw, #HE, HX, HK, Hk⟩
  iapply whileStage (wpW _) hlive hh
  iframe Hms Hcode Hast
  iintro %R1 %aC %⟨hregs, hk1⟩ #Hac Hms
  ihave Hc := evalSpecsP_at (N := N) (L := L) (Room := Room) (inp := inp) Core st d env c $$ HE
  iapply ms_callEvalPx (N := N) (L := L) (Room := Room) (inp := inp) (X := X) (Kret := K) (i := 0x8000404c)
    (jalx_8000404c live (fun p hp => hlive _ (interp_code_8000404c p hp)))
    interp_code_8000404c (by decide) (hsg.narrow hfit) hfit hsg.le
    (execSlot hfg (o := 80) (by omega) rfl).geo hcb
  iframe Hc HX Hcode Hac Hfr Hms Hst Hw HK
  isplitl []
  · ipureintro; exact ⟨hregs, execSlot_in (execSlot hfg (o := 80) (by omega) rfl) (by omega)⟩
  iintro %R2 %w0 %w1 %w2 %st' %v %hE %hk2 #Hv Hms Hst Hw HX HK
  iapply whileCopy (wpW _) (R := upd R2 1 (BitVec.ofNat 64 (0x8000404c + 4))) hlive htr hfg
    (by ix_reg; rw [keep_reg hk2 (by decide)]; exact hregs.sp)
  iframe Hms Hcode Hv
  iintro %R3 %Mt3 %⟨hk3, h30, hut⟩ Hms
  iapply Hk $$ %R3 %Mt3 %st' %v %hE
    %⟨KeepRegs.trans (KeepRegs.trans hk1 (hk2.calleeSaved_upd (by decide) _)) hk3, h30, hut⟩
    Hms Hst Hw HX HK

/-- **The `while` body, partial mode**: as `whileBodyT`, through the Löb
hypothesis for `exec_stmt`. -/
theorem whileBodyP (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {Core K : IProp GF} {st : St} {d env : Nat} {c : Expr} {b : Stmt}
    {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {m' : Nat}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv)
    (hsg : StackGeom (s + 18446744073709551440#64) m') (hfit : execNeed b d ≤ m')
    (hbb : b.bodiesBound perCallBudget = true) (hslg : SlotGeom aRet) (h10 : R 10 ≠ 0#64) :
    ms 0x80004070#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.whileStmt c b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp .uncounted st d ∗
      execSpecsP (vsaModel live) N L Room inp Core ∗
      (K ∧ (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
        ownSet (execS s) byteAny) -∗ (wpW (vsaModel live)).W Φ)) ∗
      (∀ (R' : Nat → BitVec 64) (st' : St) (status : Status), ⌜ExecS st d env b st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = whileA0 status⌝ -∗
        ms (whileNext status) R' (execS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N aRet.toNat status -∗ world N L Room inp .uncounted st' d -∗
        (K ∧ (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (execS s) byteAny) -∗ (wpW (vsaModel live)).W Φ)) -∗ (wpW (vsaModel live)).W Φ)
    ⊢ (wpW (vsaModel live)).W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, #HS, HK, Hk⟩
  iapply whileStageBody (wpW _) hlive hh h10
  iframe Hms Hcode Hast
  iintro %R1 %aB %⟨hregs, hk1⟩ #Hab Hms
  ihave Hb := execSpecsP_at (N := N) (L := L) (Room := Room) (inp := inp) Core st d env b $$ HS
  iapply ms_callExecP (N := N) (L := L) (Room := Room) (inp := inp) (Kret := K) (i := 0x80004084)
    (jalx_80004084 live (fun p hp => hlive _ (interp_code_80004084 p hp)))
    interp_code_80004084 (by decide) (hsg.narrow hfit) hfit hsg.le hslg hbb
  iframe Hb Hcode Hab Hfr Hms Hst Hslot Hw HK
  isplitl []
  · ipureintro; exact hregs
  iintro %R2 %st' %status %hE %⟨hk2, h20⟩ Hms Hst Hret Hw HK
  iapply whileRoute (wpW _) (R := upd R2 1 (BitVec.ofNat 64 (0x80004084 + 4))) hlive
    (by ix_reg; exact h20)
  iframe Hms Hcode
  iintro %R3 %⟨hk3, h30⟩ Hms
  iapply Hk $$ %R3 %st' %status %hE
    %⟨KeepRegs.trans (KeepRegs.trans hk1 (hk2.calleeSaved_upd (by decide) _)) hk3, h30⟩
    Hms Hst Hret Hw HK

/-- `whileP_body` as one Iris proposition: the statement Löb is taken over. -/
abbrev whilePI (Core : IProp GF) (d env : Nat) (c : Expr) (b : Stmt) : IProp GF :=
  iprop(∀ (Φ : Nat × String → IProp GF) (st : St) (aS aEnv aRet s : BitVec 64)
      (R : Nat → BitVec 64) (Mt : Mem) (m' : Nat),
    ⌜StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv ∧ ExecFrameGeom s ∧
      StackGeom (s + 18446744073709551440#64) m' ∧ WhileFits d c b m' ∧ SlotGeom aRet⌝ -∗
    (ms 0x8000403c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.whileStmt c b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp .uncounted st d ∗
      evalSpecsP (vsaModel live) N L Room inp Core ∗ execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ExecS st d env (.whileStmt c b) st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms (loopExit status) R' (execS s) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (execS s) byteAny) -∗ (wpW (vsaModel live)).W Φ))) -∗
    (wpW (vsaModel live)).W Φ)

/-- **The `while` loop, partial mode, by Löb**: one iteration from the head
(condition, then exit or body), the next iteration through the Löb
hypothesis, whose later the condition's `jal` pays. -/
theorem whilePI_loeb (hlive : ∀ p ∈ interpText, live p.1)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p v)
    (Core : IProp GF) (d env : Nat) (c : Expr) (b : Stmt) :
    ⊢ whilePI (GF := GF) (live := live) (N := N) (L := L) (Room := Room) (inp := inp) Core d env c b := by
  iapply loeb_wand
  imodintro
  iintro Hlob
  iintro %Φ %st %aS %aEnv %aRet %s %R %Mt %m' %⟨hh, hfg, hsg, hfits, hslg⟩
    ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, #HE, #HS, HK⟩
  iapply whileCondP (X := whilePI (GF := GF) (live := live) (N := N) (L := L) (Room := Room)
      (inp := inp) Core d env c b)
    (K := iprop(slot24 aRet.toNat ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ExecS st d env (.whileStmt c b) st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms (loopExit status) R' (execS s) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (execS s) byteAny) -∗ (wpW (vsaModel live)).W Φ))))
    hlive htr hh hfg hsg hfits.cond hfits.condB
  iframe Hms Hcode Hast Hfr Hst Hw HE Hlob
  isplitl [HK Hslot]
  · isplit
    · iframe Hslot HK
    · iintro ⟨HA, HO⟩
      ihave HK := and_elim_r $$ HK
      iapply HK $$ [HA Hslot HO]
      iframe HA Hslot HO
  iintro %R1 %Mt1 %st1 %v %hE1 %⟨hk1, h10, hut1⟩ Hms Hst Hw HX HK
  ihave ⟨Hslot, HK⟩ := and_elim_l $$ HK
  cases hv : v.truthy with
  | false =>
    -- the condition is false: leave normally
    rw [hv] at h10
    iapply whileExitFalse (wpW _) (b := b) (c := c) hlive ((hk1 8 (by decide)).trans hh.s0)
      (by simpa using h10)
    iframe Hms Hcode Hast
    iintro Hms
    ihave HK := and_elim_l $$ HK
    rw [← loopExit_normal, ← statusRet_normal (GF := GF) N]
    iapply HK $$ %_ %Mt1 %st1 %.normal %(ExecS.whileFalse _ _ _ _ _ _ _ hE1 hv)
      %⟨hk1.calleeSaved_upd (by decide) _, by ix_reg; rfl, hut1⟩ Hms Hst Hslot Hw
  | true =>
    rw [hv] at h10
    have hh1 := hh.keep hk1
    iapply whileBodyP (c := c) (K := iprop(whilePI (GF := GF) (live := live) (N := N) (L := L)
        (Room := Room) (inp := inp) Core d env c b ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ExecS st d env (.whileStmt c b) st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms (loopExit status) R' (execS s) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (execS s) byteAny) -∗ (wpW (vsaModel live)).W Φ))))
      hlive hh1 hsg hfits.body hfits.bodyB hslg (by rw [h10]; decide)
    iframe Hms Hcode Hast Hfr Hst Hslot Hw HS
    isplitl [HK HX]
    · isplit
      · iframe HX HK
      · iapply and_elim_r $$ HK
    iintro %R2 %st2 %status %hE2 %⟨hk2, h20⟩ Hms Hst Hret Hw HK
    ihave ⟨HX, HK⟩ := and_elim_l $$ HK
    cases status with
    | brk =>
      simp only [whileNext, whileA0]
      ihave HK := and_elim_l $$ HK
      rw [← loopExit_normal, statusRet_brk, ← statusRet_normal (GF := GF) N]
      iapply HK $$ %R2 %Mt1 %st2 %.normal %(ExecS.whileBreak _ _ _ _ _ _ _ _ hE1 hv hE2)
        %⟨KeepRegs.trans hk1 hk2, h20, hut1⟩ Hms Hst Hret Hw
    | ret rv =>
      simp only [whileNext, whileA0]
      ihave HK := and_elim_l $$ HK
      rw [← loopExit_ret rv]
      iapply HK $$ %R2 %Mt1 %st2 %(.ret rv) %(ExecS.whileRet _ _ _ _ _ _ _ _ _ hE1 hv hE2)
        %⟨KeepRegs.trans hk1 hk2, h20, hut1⟩ Hms Hst Hret Hw
    | normal | cont =>
      simp only [whileNext, whileA0, statusRet_normal, statusRet_cont]
      iapply HX $$ %Φ %st2 %aS %aEnv %aRet %s %R2 %Mt1 %m'
        %⟨hh1.keep hk2, hfg, hsg, hfits, hslg⟩
      iframe Hms Hcode Hast Hfr Hst Hret Hw HE HS
      isplit
      · iintro %R3 %Mt3 %st3 %status3 %hE3 %⟨hk3, h30, hut3⟩ Hms Hst Hret Hw
        ihave HK := and_elim_l $$ HK
        iapply HK $$ %R3 %Mt3 %st3 %status3
          %(ExecS.whileLoop _ _ _ _ _ _ _ _ _ _ _ hE1 hv hE2 (by first | exact .inl rfl | exact .inr rfl) hE3)
          %⟨KeepRegs.trans (KeepRegs.trans hk1 hk2) hk3, h30, hut1.trans hut3⟩ Hms Hst Hret Hw
      · iapply and_elim_r $$ HK

/-- **The `while` loop, partial mode** (`whileP_body`), for every loop. -/
theorem whileP_all (hlive : ∀ p ∈ interpText, live p.1)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p v)
    (Core : IProp GF) (d env : Nat) (c : Expr) (b : Stmt) :
    whileP_body (GF := GF) live N L Room inp Core d env c b := by
  intro Φ st aS aEnv aRet s R Mt m' hh hfg hsg hfits hslg
  have H := whilePI_loeb (L := L) (Room := Room) (inp := inp) hlive htr Core d env c b
  iintro Hpre
  ihave H := H
  iapply H $$ %Φ %st %aS %aEnv %aRet %s %R %Mt %m' %⟨hh, hfg, hsg, hfits, hslg⟩ Hpre

end Partial

end VsaIris.Interp
