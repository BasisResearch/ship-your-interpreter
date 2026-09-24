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
    {aS s : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709551440#64) :
    IW live m (whileView aS.toNat) (execS s) Q 0x80004050#64 R Mt
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
    {aS s : BitVec 64} :
    IW live m (whileView aS.toNat) (execS s) Q 0x80004088#64 R Mt
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
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨pc, pb, hn, hrc, -, hpc, -⟩ := whileNode_of_repr hrepr hgeo
  have hs80 := execSlot hfg (o := 80) (by omega) rfl
  have hs16 := execSlot hfg (o := 16) (by omega) rfl
  have hoff := execSP_off hfg
  have hPt : (BitVec.ofNat 64 pc).toNat = pc := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc]
  -- run A: stage the condition
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(codeRes ∗ roOn P m ∗ frameAt env aEnv.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗ world N L Room inp (.counted (k + nc)) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = (if v.truthy then 1#64 else 0#64) ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x80004070#64 R' (execS s) Mt' -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms Hcode Hro Hfr Hst Hw; iexact Hk
  intro F'
  refine WhileLoop_runA hlive hn.lo hn.hi hn.off hh.s0 hh.sp hn.cond ?_
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨#Hcode, #Hro, #Hfr, Hst, Hw, Hk⟩, Hms⟩
  -- the condition
  ihave Hc := hc
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x8000404c)
    (jalx_8000404c live (fun p hp => hlive _ (interp_code_8000404c p hp)))
    interp_code_8000404c (by decide) Dc (k := k)
    (slot := s + 18446744073709551440#64 + 80#64) (aC := BitVec.ofNat 64 pc) (aE := aEnv)
    (s := s + 18446744073709551440#64) (m := m') (hsg.narrow hfit) hfit hsg.le hs80.geo hcb
  iframe Hc Hcode Hfr Hms Hst Hw
  isplitl []
  · ipureintro
    refine ⟨⟨by ix_reg, by ix_reg; exact hh.s1, by ix_reg, by ix_reg; exact hh.s3,
      by ix_reg; exact hh.sp⟩, execSlot_in hs80 (by omega)⟩
  isplitl []
  · imodintro; rw [hPt]; iapply astEG_of_view hrc hgeo $$ Hro
  iintro %R1 %w0 %w1 %w2 %hkeep1 #Hv Hms Hst Hw
  clear hrepr
  -- run B: copy the value to `sp+16`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(codeRes ∗ □ valOf N v w0 w1 w2 ∗
      stackScratch (s + 18446744073709551440#64) m' ∗ world N L Room inp (.counted k) st' d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = (if v.truthy then 1#64 else 0#64) ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x80004070#64 R' (execS s) Mt' -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms Hcode Hv Hst Hw; iexact Hk
  intro F'
  refine WhileLoop_runB (aS := aS) hlive hfg.sf hfg.lo hfg.hi hfg.al ?_ ?_
  · ix_reg; rw [keep_reg hkeep1 (by decide)]; ix_reg; exact hh.sp
  intros
  apply swp_closeRM
  intro R3 Mt3 hR3 hMt3
  unfold F'
  iintro ⟨⟨#Hcode, #Hv, Hst, Hw, Hk⟩, Hms⟩
  have e0 : imgW (imgM Mt3) (s + 18446744073709551440#64 + 16#64).toNat = w0 := by
    rw [← ldv_ld_imgW, hMt3]; ix_fwd using [hoff]
  have e8 : imgW (imgM Mt3) ((s + 18446744073709551440#64 + 16#64).toNat + 8) = w1 := by
    rw [← ldv_ld_imgW, hMt3]; ix_fwd using [hoff]
  have e16 : imgW (imgM Mt3) ((s + 18446744073709551440#64 + 16#64).toNat + 16) = w2 := by
    rw [← ldv_ld_imgW, hMt3]; ix_fwd using [hoff]
  -- `value_truthy` on the copy
  ihave Ht := htr $$ %(s + 18446744073709551440#64 + 16#64) %v
  iapply ms_truthyCall (twpW _) (N := N) (R := R3) (Mt := Mt3) (v := v) (i := 0x8000406c)
    (jalx_8000406c live (fun p hp => hlive _ (interp_code_8000406c p hp)))
    interp_code_8000406c (by decide) (execSlot_in hs16 (by omega)) (by rw [hR3]; ix_reg) hs16.geo
  iframe Ht Hcode Hms
  isplitl []
  · imodintro; unfold valImg; rw [e0, e8, e16]; iexact Hv
  iintro %R4 %Mt4 %⟨hkeep4, htr4, hag4⟩ Hms
  iapply Hk $$ %_ %Mt4 %⟨?_, by ix_reg; exact htr4, ?_⟩ Hms Hst Hw
  · intro x hx
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      ((try ix_reg); rw [keep_helper hkeep4 (by decide) (by decide)]; (try ix_reg);
       rw [hR3]; (try ix_reg); rw [keep_reg hkeep1 (by decide)]; (try ix_reg))
  · refine Untouched.trans (Untouched.slotWrite hs80 (by omega) (by omega) Mt w0 w1 w2) ?_
    refine Untouched.trans ?_ (fun a ha hw => hag4 a ha fun hin => hw (execSlot_W hs16 (Nat.le_refl _) (by omega) a hin))
    rw [hMt3]
    exact Untouched.trans (Untouched.trans (Untouched.store hfg (o := 16) (Nat.le_refl _) (by omega) _ _)
      (Untouched.store hfg (o := 24) (by omega) (by omega) _ _))
      (Untouched.store hfg (o := 32) (by omega) (by omega) _ _)

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

/-- **The `while` body, total mode**: from the branch `0x80004070` with a true
condition, the body through `exec_stmt` (its derivation `Db`) and the status
routing (`bne a0,1`, `beq a0,3`). The frame bytes are unchanged. -/
theorem whileBodyT (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {st : St} {d env : Nat} {c : Expr} {b : Stmt} {st' : St} {status : Status} {nb k : Nat}
    (Db : ExecSCost st d env b st' status nb)
    (hb : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env b st' status nb Db)
    {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {m' : Nat}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv) (hfg : ExecFrameGeom s)
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
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨pc, pb, hn, -, hrb, -, hpb⟩ := whileNode_of_repr hrepr hgeo
  have hPt : (BitVec.ofNat 64 pb).toNat = pb := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpb]
  -- run C: the branch, stage the body
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(codeRes ∗ roOn P m ∗ frameAt env aEnv.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted (k + nb)) st d ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs calleeSaved R R' ∧ R' 10 = whileA0 status⌝ -∗
        ms (whileNext status) R' (execS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N aRet.toNat status -∗ world N L Room inp (.counted k) st' d -∗
        (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms Hcode Hro Hfr Hst Hslot Hw; iexact Hk
  intro F'
  refine WhileLoop_runC (s := s) hlive hn.lo hn.hi hn.off hh.s0 hn.body (fun h => absurd h h10) ?_
  intro _
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨#Hcode, #Hro, #Hfr, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- the body
  ihave Hb := hb
  iapply ms_callExecT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80004084)
    (jalx_80004084 live (fun p hp => hlive _ (interp_code_80004084 p hp)))
    interp_code_80004084 (by decide) Db (k := k) (aS := BitVec.ofNat 64 pb) (aE := aEnv)
    (aRet := aRet) (s := s + 18446744073709551440#64) (m := m')
    (hsg.narrow hfit) hfit hsg.le hslg hbb
  iframe Hb Hcode Hfr Hms Hst Hslot Hw
  isplitl []
  · ipureintro
    exact ⟨by ix_reg; exact hh.s1, by ix_reg, by ix_reg; exact hh.s3, by ix_reg; exact hh.s2,
      by ix_reg; exact hh.sp⟩
  isplitl []
  · imodintro; rw [hPt]; unfold astSG; iexists P, m; iframe Hro; ipureintro; exact ⟨hrb, hgeo⟩
  iintro %R1 %⟨hkeep1, hst1⟩ Hms Hst Hret Hw
  -- run D: the status routing
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(stackScratch (s + 18446744073709551440#64) m' ∗
      statusRet N aRet.toNat status ∗ world N L Room inp (.counted k) st' d ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs calleeSaved R R' ∧ R' 10 = whileA0 status⌝ -∗
        ms (whileNext status) R' (execS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N aRet.toNat status -∗ world N L Room inp (.counted k) st' d -∗
        (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms Hst Hret Hw; iexact Hk
  intro F'
  have hR1 : KeepRegs calleeSaved R (upd R1 1 (BitVec.ofNat 64 (2147500164 + 4))) := by
    intro x hx
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      ((try ix_reg); rw [keep_reg hkeep1 (by decide)]; (try ix_reg))
  have hk5 : ∀ (R' : Nat → BitVec 64), (∀ x ∈ calleeSaved, R' x = upd R1 1 (BitVec.ofNat 64 (2147500164 + 4)) x) →
      KeepRegs calleeSaved R R' := fun R' h x hx => (h x hx).trans (hR1 x hx)
  refine WhileLoop_runD (aS := aS) (s := s) hlive ?_ ?_ ?_
  · -- `a0 = 3`: a returned value
    intro _ hc3
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc3
    intros
    apply swp_closeF
    unfold F'
    cases status with
    | ret rv =>
      simp only [whileNext, whileA0]
      iintro ⟨⟨Hst, Hret, Hw, Hk⟩, Hms⟩
      iapply Hk $$ %_ %⟨hk5 _ ?_, ?_⟩ Hms Hst Hret Hw
      · intro x hx
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
      · ix_reg; exact hst1
    | _ => exfalso; rw [hst1] at hc3; simp [statusCode] at hc3
  · -- `a0 ∈ {0, 2}`: back to the head
    intro h1 hc3
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc3 h1
    intros
    apply swp_closeF
    unfold F'
    cases status with
    | normal | cont =>
      simp only [whileNext, whileA0]
      iintro ⟨⟨Hst, Hret, Hw, Hk⟩, Hms⟩
      iapply Hk $$ %_ %⟨hk5 _ ?_, ?_⟩ Hms Hst Hret Hw
      · intro x hx
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
      · ix_reg; exact hst1
    | brk => exfalso; exact h1 hst1
    | ret _ => exfalso; exact hc3 hst1
  · -- `a0 = 1`: break
    intro h1
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, Decidable.not_not] at h1
    intros
    apply swp_closeF
    unfold F'
    cases status with
    | brk =>
      simp only [whileNext, whileA0]
      iintro ⟨⟨Hst, Hret, Hw, Hk⟩, Hms⟩
      iapply Hk $$ %_ %⟨hk5 _ ?_, ?_⟩ Hms Hst Hret Hw
      · intro x hx
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
      · ix_reg
    | _ => exfalso; rw [hst1] at h1; simp [statusCode] at h1

end Cond

/-! ## Total mode: one lemma per `ExecSCost` `while` constructor -/

section Total

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

omit I in
theorem statusRet_brk [InterpGS GF] (N : NativeAddrs) (a : Nat) :
    statusRet (GF := GF) N a .brk = slot24 a := rfl

omit I in
theorem statusRet_cont [InterpGS GF] (N : NativeAddrs) (a : Nat) :
    statusRet (GF := GF) N a .cont = slot24 a := rfl

theorem KeepRegs.calleeSaved_upd {R R' : Nat → BitVec 64} (h : KeepRegs calleeSaved R R')
    {x : Nat} (hx : x ∉ calleeSaved) (w : BitVec 64) : KeepRegs calleeSaved R (upd R' x w) :=
  fun y hy => by
    have hne : y ≠ x := fun e => hx (e ▸ hy)
    rw [upd_apply, ite_eq_right_iff.mpr (fun h => absurd h hne)]; exact h y hy

/-- The loop head's registers survive a run that keeps the callee-saved ones. -/
theorem StmtHead.keep {R R' : Nat → BitVec 64} {s aS inp aRet aEnv : BitVec 64}
    (h : StmtHead R s aS inp aRet aEnv) (hk : KeepRegs calleeSaved R R') :
    StmtHead R' s aS inp aRet aEnv :=
  ⟨(hk 2 (by decide)).trans h.sp, (hk 8 (by decide)).trans h.s0,
    (hk 9 (by decide)).trans h.s1, (hk 18 (by decide)).trans h.s2,
    (hk 19 (by decide)).trans h.s3⟩

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
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
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
  iapply whileBodyT (c := c) hlive Db hb (hh.keep hk1) hfg hsg hfits.body hfits.bodyB hslg
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
  iapply whileBodyT (c := c) hlive Db hb (hh.keep hk1) hfg hsg hfits.body hfits.bodyB hslg
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
  iapply whileBodyT (c := c) hlive Db hb (hh.keep hk1) hfg hsg hfits.body hfits.bodyB hslg
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

end VsaIris.Interp
