import VsaIris.Interp.SeqLoop

/-!
# `seqLoop`, closure-body site (INTERP_DESIGN.md §4.3)

The call arm of `eval_expr` runs a closure's body statements with the loop
`0x80003354`..`0x80003350`: the head loads the statement pointer from the body
node (`a6`, spilled at `sp+0`), the `jal exec_stmt` at `0x80003374` lends the
result slot `sp+144`, then `beqz a0` continues (reload `a6`, `s0 += 1`, `bge`
leaves) or leaves on an abrupt status. The motives and cases follow the block
site (`SeqLoop.lean`); the differences are the frame (`eval_expr`'s, the slot
carved out: `closureS`), the index register (`s0`, callee-saved: `closureKeep`)
and the two exits (`closureExit`).
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- The closure body loop's owned frame bytes: `eval_expr`'s frame without
the result slot `sp+144`, which the loop lends each statement. -/
abbrev closureS (s : BitVec 64) : Nat → Prop :=
  fun b => InExt (s.toNat - 1088, 1088) b ∧ ¬ InExt (s.toNat - 1088 + 144, 24) b

#ix_seg ClosureLoop_runA {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aB s arr pS : BitVec 64} {idx count : Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aB.toNat) (hx2 : aB.toNat + 24 ≤ 0x100000000)
    (hx3 : aB.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aB.toNat)
    (ha1 : 0x80000000 ≤ arr.toNat) (ha2 : arr.toNat + 8 * count ≤ 0x100000000)
    (ha3 : arr.toNat + 8 * count ≤ tohostAddr ∨ tohostAddr + 16 ≤ arr.toNat)
    (hidx : idx < count) (hc : count < 2 ^ 31)
    (h16 : R 16 = aB) (h8 : R 8 = BitVec.ofNat 64 idx) (h2 : R 2 = s + 18446744073709550528#64)
    (harr : ldv .ld m (aB + 8#64).toNat = arr)
    (hel : ldv .ld m (arr + BitVec.ofNat 64 idx <<< 3).toNat = pS) :
    IW live m (blockView aB.toNat arr.toNat count) (closureS s) Q 0x80003354#64 R Mt
  by ix_run hlive using [h16, h8, h2, harr, hel, hsf, closureS] at 0x80003374


#ix_seg ClosureLoop_runB {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aB s arr sc : BitVec 64} {idx count : Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aB.toNat) (hx2 : aB.toNat + 24 ≤ 0x100000000)
    (hx3 : aB.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aB.toNat)
    (hidx : idx < count) (hc : count < 2 ^ 31)
    (h8 : R 8 = BitVec.ofNat 64 idx) (h2 : R 2 = s + 18446744073709550528#64) (h10 : R 10 = sc)
    (hb : ldv .ld Mt (s.toNat - 1088) = aB)
    (hcnt : ldv .lw m (aB + 16#64).toNat = BitVec.ofNat 64 count) :
    IW live m (blockView aB.toNat arr.toNat count) (closureS s) Q 0x80003378#64 R Mt
  by ix_run hlive using [h8, h2, h10, hb, hcnt, hsf, closureS] at 0x80003354 0x80003954 0x8000337c


/-- The loop head's registers: the body node (`a6`), the index (`s0`), the
interpreter (`s2`), the closure scope's frame pointer (`s3`), the lowered
`sp`. -/
structure ClosureHead (R : Nat → BitVec 64) (s aB inp aEnv : BitVec 64) (idx : Nat) : Prop where
  sp : R 2 = s + 18446744073709550528#64
  a6 : R 16 = aB
  s0 : R 8 = BitVec.ofNat 64 idx
  s2 : R 18 = inp
  s3 : R 19 = aEnv

/-- `eval_expr`'s entry `sp` with its 1088-byte frame below it. -/
structure EvalFrameG (s : BitVec 64) : Prop where
  sf : (s + 18446744073709550528#64).toNat = s.toNat - 1088
  lo : 0x87800000 + 1088 ≤ s.toNat
  hi : s.toNat ≤ 0x88000000
  al : s.toNat % 16 = 0

/-- What the closure loop keeps: every callee-saved register but the index `s0`. -/
abbrev closureKeep : List Nat := [2, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The loop's exits: the depth decrement on a normal end, the status routing
otherwise. -/
def closureExit (status : Status) : BitVec 64 :=
  if status = .normal then 0x80003954#64 else 0x8000337c#64

theorem closureExit_normal : closureExit .normal = 0x80003954#64 := rfl
theorem closureExit_abrupt {status : Status} (h : status ≠ .normal) :
    closureExit status = 0x8000337c#64 := by simp [closureExit, h]

section Motive

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- **The closure body loop, total mode**: the motive of `ExecSeqCost` at the
closure-body site of the call arm. As `blockSeqT_body`, over `eval_expr`'s
frame: the result slot `sp+144` is lent to each statement, the index lives in
`s0` (so every callee-saved register but `s0` is kept), and the loop leaves at
the depth decrement `0x80003954` on a normal end or at `0x8000337c` on an
abrupt status (`closureExit`). -/
def closureSeqT_body (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (st : St) (d inner : Nat) (ss : List Vsa.While.Stmt) (st' : St) (status : Status)
    (n : Nat) (_D : ExecSeqCost st d inner ss st' status n) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (k idx count : Nat) (aB arr aEnv s : BitVec 64)
    (R : Nat → BitVec 64) (Mt m : Mem) (P : Nat → Prop) (all : List Vsa.While.Stmt) (m' : Nat)
    (Inv : Mem → Prop) (F : IProp GF),
    ss ≠ [] → ss = all.drop idx → BlockNode m P aB arr count all →
    ClosureHead R s aB (BitVec.ofNat 64 inp) aEnv idx → EvalFrameG s →
    StackGeom (s + 18446744073709550528#64) m' →
    (∀ x ∈ all, execNeed x d ≤ m' ∧ x.bodiesBound perCallBudget = true) → SlotGeom (s + 18446744073709550528#64 + 144#64) →
    Inv Mt → (∀ M, Inv M → Inv (writeLog M [(s.toNat - 1088, 8, aB)])) →
    (F ∗ ms 0x80003354#64 R (closureS s) Mt ∗ codeRes ∗ roOn P m ∗
      □ frameAt inner aEnv.toNat ∗ stackScratch (s + 18446744073709550528#64) m' ∗
      slot24 (s + 18446744073709550528#64 + 144#64).toNat ∗ world N L Room inp (.counted (k + n)) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs closureKeep R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms (closureExit status) R' (closureS s) Mt' -∗
        stackScratch (s + 18446744073709550528#64) m' -∗ statusRet N (s + 18446744073709550528#64 + 144#64).toNat status -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)
      ⊢ (twpW (vsaModel live)).W Φ)

/-- **The closure body loop, partial mode** (as `blockSeqP_body`). -/
def closureSeqP_body (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (Core : IProp GF) (d inner : Nat) (ss : List Vsa.While.Stmt) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (st : St) (idx count : Nat) (aB arr aEnv s : BitVec 64)
    (R : Nat → BitVec 64) (Mt m : Mem) (P : Nat → Prop) (all : List Vsa.While.Stmt) (m' : Nat)
    (Inv : Mem → Prop) (F : IProp GF),
    ss ≠ [] → ss = all.drop idx → BlockNode m P aB arr count all →
    ClosureHead R s aB (BitVec.ofNat 64 inp) aEnv idx → EvalFrameG s →
    StackGeom (s + 18446744073709550528#64) m' →
    (∀ x ∈ all, execNeed x d ≤ m' ∧ x.bodiesBound perCallBudget = true) → SlotGeom (s + 18446744073709550528#64 + 144#64) →
    Inv Mt → (∀ M, Inv M → Inv (writeLog M [(s.toNat - 1088, 8, aB)])) →
    (F ∗ ms 0x80003354#64 R (closureS s) Mt ∗ codeRes ∗ roOn P m ∗
      □ frameAt inner aEnv.toNat ∗ stackScratch (s + 18446744073709550528#64) m' ∗
      slot24 (s + 18446744073709550528#64 + 144#64).toNat ∗ world N L Room inp .uncounted st d ∗
      execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ExecSeq st d inner ss st' status⌝ -∗
        ⌜KeepRegs closureKeep R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms (closureExit status) R' (closureS s) Mt' -∗
        stackScratch (s + 18446744073709550528#64) m' -∗ statusRet N (s + 18446744073709550528#64 + 144#64).toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709550528#64) m' ∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat ∗
          ownSet (closureS s) byteAny) -∗ (wpW (vsaModel live)).W Φ))
      ⊢ (wpW (vsaModel live)).W Φ)

theorem closureSeqT_nil (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (st : St) (d inner : Nat) :
    closureSeqT_body (GF := GF) live N L Room inp st d inner [] st .normal 0 (.nil st d inner) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd rfl h

theorem closureSeqP_nil (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (Core : IProp GF) (d inner : Nat) :
    closureSeqP_body (GF := GF) live N L Room inp Core d inner [] :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd rfl h

end Motive

/-! ## The cases -/

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr

#ix_piece closureSeqT_consNormal_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
    [I : InterpGS GF] {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d inner : Nat} {sm : Vsa.While.Stmt} {ss : List Vsa.While.Stmt} {st' st'' : St}
    {status : Status} {n1 n2 : Nat}
    (D1 : ExecSCost st d inner sm st' .normal n1) (D2 : ExecSeqCost st' d inner ss st'' status n2)
    (h1 : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st d inner sm st' .normal n1 D1)
    (h2 : closureSeqT_body (GF := GF) live N L Room inp st' d inner ss st'' status n2 D2) :
    closureSeqT_body (GF := GF) live N L Room inp st d inner (sm :: ss) st'' status (n1 + n2)
      (.consNormal st d inner sm ss st' st'' status n1 n2 D1 D2) by
  intro Φ k idx count aB arr aEnv s R Mt m P all m' Inv F _ hdrop hbn hbh hfg hsg' hall hslg
    hinv hInv
  obtain ⟨hl, hat, hrest⟩ := drop_cons_facts hdrop
  have hcount : all.length = count := stmtArray_length hbn.repr
  obtain ⟨p, hp, hsp⟩ := stmtArray_get hbn.repr idx hl
  rw [hat] at hsp
  have hpl : p < 2 ^ 64 := readLE_lt hp
  have hpt : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hidx : idx < count := hcount ▸ hl
  have hel : ldv .ld m (arr + BitVec.ofNat 64 idx <<< 3).toNat = BitVec.ofNat 64 p := by
    rw [arr_elem_addr hbn.ahi hidx]; exact ldv_ld_read64 hp
  obtain ⟨hneed, hbb⟩ := hall sm (hat ▸ List.getElem_mem hl)
  iintro ⟨HF, Hms, #Hcode, #Hro, #Hfr, Hst, Hslot, Hw, Hk⟩
  -- the head run: load the statement, spill the index
  ihave #Hdv := roOwn_data hbn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗ frameAt inner aEnv.toNat ∗
      stackScratch (s + 18446744073709550528#64) m' ∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat ∗
      world N L Room inp (.counted (k + (n1 + n2))) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs closureKeep R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms (closureExit status) R' (closureS s) Mt' -∗
        stackScratch (s + 18446744073709550528#64) m' -∗ statusRet N (s + 18446744073709550528#64 + 144#64).toNat status -∗
        world N L Room inp (.counted k) st'' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hslot Hw; iexact Hk
  intro F'
  refine ClosureLoop_runA (pS := BitVec.ofNat 64 p) hlive hfg.sf hfg.lo hfg.hi hfg.al hbn.lo hbn.hi hbn.off
    hbn.alo hbn.ahi hbn.aoff hidx hbn.small hbh.a6 hbh.s0 hbh.sp hbn.arrw hel ?_
  intros
  apply swp_closeM
  intro Mt1 hMt1
  have hinv1 : Inv Mt1 := by rw [hMt1]; exact hInv _ hinv
  unfold F'
  iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- the statement
  ihave H1 := h1
  rw [show k + (n1 + n2) = k + n2 + n1 by omega]
  iapply ms_callExecT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80003374)
    (jalx_80003374 live (fun p hp => hlive _ (interp_code_80003374 p hp)))
    interp_code_80003374 (by decide) D1 (k := k + n2) (aS := BitVec.ofNat 64 p) (aE := aEnv)
    (aRet := s + 18446744073709550528#64 + 144#64) (s := s + 18446744073709550528#64) (m := m')
    (hsg'.narrow hneed) hneed hsg'.le hslg hbb
  iframe H1 Hcode Hfr Hms Hst Hslot Hw
  isplitl []
  · ipureintro
    exact ⟨by ix_reg; exact hbh.s2, by ix_reg, by ix_reg; exact hbh.s3, by ix_reg,
      by ix_reg; exact hbh.sp⟩
  isplitl []
  · imodintro; rw [hpt]; unfold astSG; iexists P, m; iframe Hro; ipureintro; exact ⟨hsp, hbn.geo⟩
  iintro %R' %⟨hkeep, hst0⟩ Hms Hst Hret Hw
  rw [statusRet_normal]

#ix_piece closureSeqT_consNormal_p2 from closureSeqT_consNormal_p1 by
  -- the status test and the back edge
  ihave #Hdv := roOwn_data hbn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗ frameAt inner aEnv.toNat ∗
      stackScratch (s + 18446744073709550528#64) m' ∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat ∗
      world N L Room inp (.counted (k + n2)) st' d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs closureKeep R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms (closureExit status) R' (closureS s) Mt' -∗
        stackScratch (s + 18446744073709550528#64) m' -∗ statusRet N (s + 18446744073709550528#64 + 144#64).toNat status -∗
        world N L Room inp (.counted k) st'' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hret Hw; iexact Hk
  intro F'
  have hR1 : KeepRegs calleeSaved R (upd R' 1 (BitVec.ofNat 64 (2147496820 + 4))) := by
    keep_split
    all_goals ix_keep [hkeep]
  refine ClosureLoop_runB (sc := 0#64) (arr := arr) hlive hfg.sf hfg.lo hfg.hi hfg.al hbn.lo hbn.hi
    hbn.off hidx hbn.small ((hR1 8 (by decide)).trans hbh.s0) ((hR1 2 (by decide)).trans hbh.sp)
    (by ix_reg; exact hst0) (by rw [hMt1]; ix_fwd) hbn.cntw ?_ ?_ ?_
  · -- the last statement: the loop leaves normally
    intro _ hc
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, idx_succ,
      sext32_ofNat_toInt (show idx + 1 < 2 ^ 31 by have := hbn.small; omega),
      ofNat_toInt_small hbn.small] at hc
    intros
    apply swp_closeF
    cases ss with
    | cons s2 ss2 =>
      exfalso
      obtain ⟨hl2, -, -⟩ := drop_cons_facts hrest
      omega
    | nil =>
      cases D2
      unfold F'
      iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hret, Hw, Hk⟩, Hms⟩
      rw [statusRet_normal, closureExit_normal]
      iapply Hk $$ %_ %Mt1 %⟨?_, by ix_reg; exact hst0, hinv1⟩ HF Hms Hst Hret Hw
      refine KeepRegs.trans (hR1.sub (by decide)) ?_
      keep_split
      all_goals ix_reg

  · -- more statements: the tail's loop
    intro _ hc
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, idx_succ,
      sext32_ofNat_toInt (show idx + 1 < 2 ^ 31 by have := hbn.small; omega),
      ofNat_toInt_small hbn.small] at hc
    intros
    apply swp_closeRM
    intro R2 Mt2 hR2 hMt2
    subst hMt2
    cases ss with
    | nil => exfalso; have := List.drop_eq_nil_iff.mp hrest.symm; omega
    | cons s2 ss2 =>
      refine .trans ?_ (h2 Φ k (idx + 1) count aB arr aEnv s R2 Mt2 m P all m' Inv F
        (List.cons_ne_nil _ _) hrest hbn ?_ hfg hsg' hall hslg hinv1 hInv)
      · unfold F'
        iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hret, Hw, Hk⟩, Hms⟩
        iframe HF Hms Hcode Hro Hfr Hst Hret Hw
        iintro %R'' %Mt'' %⟨hk'', hst'', hinv''⟩ HF Hms Hst Hret Hw
        iapply Hk $$ %R'' %Mt'' %⟨KeepRegs.trans (KeepRegs.trans (KeepRegs.sub (ks := calleeSaved) ?_ (by decide)) ?_) hk'', hst'', hinv''⟩ HF Hms Hst Hret Hw
        · exact hR1
        · keep_split
          all_goals (rw [hR2]; ix_reg)
      · rw [hR2]
        exact ⟨by ix_reg; exact (hR1 2 (by decide)).trans hbh.sp, by ix_reg,
          by ix_reg; exact idx_succ idx, by ix_reg; exact (hR1 18 (by decide)).trans hbh.s2,
          by ix_reg; exact (hR1 19 (by decide)).trans hbh.s3⟩
  · -- an abrupt status: not this derivation's
    intro hc; exfalso; apply hc; ix_reg; exact hst0
#ix_chain closureSeqT_consNormal := [closureSeqT_consNormal_p1, closureSeqT_consNormal_p2]


#ix_piece closureSeqT_consAbrupt_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
    [I : InterpGS GF] {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d inner : Nat} {sm : Vsa.While.Stmt} {ss : List Vsa.While.Stmt} {st' st'' : St}
    {status : Status} {n : Nat}
    (D1 : ExecSCost st d inner sm st' status n) (hne : status ≠ .normal)
    (h1 : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st d inner sm st' status n D1) :
    closureSeqT_body (GF := GF) live N L Room inp st d inner (sm :: ss) st' status n
      (.consAbrupt st d inner sm ss st' status n D1 hne) by
  intro Φ k idx count aB arr aEnv s R Mt m P all m' Inv F _ hdrop hbn hbh hfg hsg' hall hslg
    hinv hInv
  obtain ⟨hl, hat, hrest⟩ := drop_cons_facts hdrop
  have hcount : all.length = count := stmtArray_length hbn.repr
  obtain ⟨p, hp, hsp⟩ := stmtArray_get hbn.repr idx hl
  rw [hat] at hsp
  have hpl : p < 2 ^ 64 := readLE_lt hp
  have hpt : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hidx : idx < count := hcount ▸ hl
  have hel : ldv .ld m (arr + BitVec.ofNat 64 idx <<< 3).toNat = BitVec.ofNat 64 p := by
    rw [arr_elem_addr hbn.ahi hidx]; exact ldv_ld_read64 hp
  obtain ⟨hneed, hbb⟩ := hall sm (hat ▸ List.getElem_mem hl)
  iintro ⟨HF, Hms, #Hcode, #Hro, #Hfr, Hst, Hslot, Hw, Hk⟩
  -- the head run: load the statement, spill the index
  ihave #Hdv := roOwn_data hbn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗ frameAt inner aEnv.toNat ∗
      stackScratch (s + 18446744073709550528#64) m' ∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat ∗
      world N L Room inp (.counted (k + n)) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs closureKeep R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms (closureExit status) R' (closureS s) Mt' -∗
        stackScratch (s + 18446744073709550528#64) m' -∗ statusRet N (s + 18446744073709550528#64 + 144#64).toNat status -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hslot Hw; iexact Hk
  intro F'
  refine ClosureLoop_runA (pS := BitVec.ofNat 64 p) hlive hfg.sf hfg.lo hfg.hi hfg.al hbn.lo hbn.hi hbn.off
    hbn.alo hbn.ahi hbn.aoff hidx hbn.small hbh.a6 hbh.s0 hbh.sp hbn.arrw hel ?_
  intros
  apply swp_closeM
  intro Mt1 hMt1
  have hinv1 : Inv Mt1 := by rw [hMt1]; exact hInv _ hinv
  unfold F'
  iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- the statement
  ihave H1 := h1
  iapply ms_callExecT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80003374)
    (jalx_80003374 live (fun p hp => hlive _ (interp_code_80003374 p hp)))
    interp_code_80003374 (by decide) D1 (k := k) (aS := BitVec.ofNat 64 p) (aE := aEnv)
    (aRet := s + 18446744073709550528#64 + 144#64) (s := s + 18446744073709550528#64) (m := m')
    (hsg'.narrow hneed) hneed hsg'.le hslg hbb
  iframe H1 Hcode Hfr Hms Hst Hslot Hw
  isplitl []
  · ipureintro
    exact ⟨by ix_reg; exact hbh.s2, by ix_reg, by ix_reg; exact hbh.s3, by ix_reg,
      by ix_reg; exact hbh.sp⟩
  isplitl []
  · imodintro; rw [hpt]; unfold astSG; iexists P, m; iframe Hro; ipureintro; exact ⟨hsp, hbn.geo⟩
  iintro %R' %⟨hkeep, hst0⟩ Hms Hst Hret Hw


#ix_piece closureSeqT_consAbrupt_p2 from closureSeqT_consAbrupt_p1 by
  -- the status test: an abrupt status leaves the loop
  ihave #Hdv := roOwn_data hbn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗ frameAt inner aEnv.toNat ∗
      stackScratch (s + 18446744073709550528#64) m' ∗ statusRet N (s + 18446744073709550528#64 + 144#64).toNat status ∗
      world N L Room inp (.counted k) st' d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs closureKeep R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms (closureExit status) R' (closureS s) Mt' -∗
        stackScratch (s + 18446744073709550528#64) m' -∗ statusRet N (s + 18446744073709550528#64 + 144#64).toNat status -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hret Hw; iexact Hk
  intro F'
  have hR1 : KeepRegs calleeSaved R (upd R' 1 (BitVec.ofNat 64 (2147496820 + 4))) := by
    keep_split
    all_goals ix_keep [hkeep]
  have hsc : statusCode status ≠ 0#64 := by cases status <;> simp_all [statusCode]
  refine ClosureLoop_runB (sc := statusCode status) (arr := arr) hlive hfg.sf hfg.lo hfg.hi hfg.al hbn.lo
    hbn.hi hbn.off hidx hbn.small ((hR1 8 (by decide)).trans hbh.s0) ((hR1 2 (by decide)).trans hbh.sp)
    (by ix_reg; exact hst0) (by rw [hMt1]; ix_fwd) hbn.cntw ?_ ?_ ?_
  · intro hc0; exfalso; apply hsc; rw [← hst0]; revert hc0; ix_reg; exact id
  · intro hc0; exfalso; apply hsc; rw [← hst0]; revert hc0; ix_reg; exact id
  · intro _
    intros
    apply swp_closeF
    unfold F'
    iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hret, Hw, Hk⟩, Hms⟩
    rw [closureExit_abrupt hne]
    iapply Hk $$ %_ %Mt1 %⟨hR1.sub (by decide), by ix_reg; exact hst0, hinv1⟩ HF Hms Hst Hret Hw

#ix_chain closureSeqT_consAbrupt := [closureSeqT_consAbrupt_p1, closureSeqT_consAbrupt_p2]



#ix_piece closureSeqP_cons_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
    [I : InterpGS GF] {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {d inner : Nat} {sm : Vsa.While.Stmt} {ss : List Vsa.While.Stmt}
    (ih : closureSeqP_body (GF := GF) live N L Room inp Core d inner ss) :
    closureSeqP_body (GF := GF) live N L Room inp Core d inner (sm :: ss) by
  intro Φ st idx count aB arr aEnv s R Mt m P all m' Inv F _ hdrop hbn hbh hfg hsg' hall hslg
    hinv hInv
  obtain ⟨hl, hat, hrest⟩ := drop_cons_facts hdrop
  have hcount : all.length = count := stmtArray_length hbn.repr
  obtain ⟨p, hp, hsp⟩ := stmtArray_get hbn.repr idx hl
  rw [hat] at hsp
  have hpl : p < 2 ^ 64 := readLE_lt hp
  have hpt : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hidx : idx < count := hcount ▸ hl
  have hel : ldv .ld m (arr + BitVec.ofNat 64 idx <<< 3).toNat = BitVec.ofNat 64 p := by
    rw [arr_elem_addr hbn.ahi hidx]; exact ldv_ld_read64 hp
  obtain ⟨hneed, hbb⟩ := hall sm (hat ▸ List.getElem_mem hl)
  iintro ⟨HF, Hms, #Hcode, #Hro, #Hfr, Hst, Hslot, Hw, #IH, HK⟩
  ihave #Hdv := roOwn_data hbn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗ frameAt inner aEnv.toNat ∗
      stackScratch (s + 18446744073709550528#64) m' ∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat ∗
      world N L Room inp .uncounted st d ∗ execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ExecSeq st d inner (sm :: ss) st' status⌝ -∗
        ⌜KeepRegs closureKeep R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms (closureExit status) R' (closureS s) Mt' -∗
        stackScratch (s + 18446744073709550528#64) m' -∗ statusRet N (s + 18446744073709550528#64 + 144#64).toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709550528#64) m' ∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat ∗
          ownSet (closureS s) byteAny) -∗ (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hslot Hw IH; iexact HK
  intro F'
  refine ClosureLoop_runA (pS := BitVec.ofNat 64 p) hlive hfg.sf hfg.lo hfg.hi hfg.al hbn.lo hbn.hi hbn.off
    hbn.alo hbn.ahi hbn.aoff hidx hbn.small hbh.a6 hbh.s0 hbh.sp hbn.arrw hel ?_
  intros
  apply swp_closeM
  intro Mt1 hMt1
  have hinv1 : Inv Mt1 := by rw [hMt1]; exact hInv _ hinv
  unfold F'
  iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hslot, Hw, #IH, HK⟩, Hms⟩
  -- the statement, through the Löb hypothesis
  ihave H1 := execSpecsP_at Core st d inner sm $$ IH
  iapply ms_callExecP (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80003374)
    (jalx_80003374 live (fun p hp => hlive _ (interp_code_80003374 p hp)))
    interp_code_80003374 (by decide) (Core := Core) (st := st) (d := d) (env := inner) (sm := sm)
    (aS := BitVec.ofNat 64 p) (aE := aEnv) (aRet := s + 18446744073709550528#64 + 144#64) (s := s + 18446744073709550528#64)
    (m := m') (Kret := iprop(∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ExecSeq st d inner (sm :: ss) st' status⌝ -∗
        ⌜KeepRegs closureKeep R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms (closureExit status) R' (closureS s) Mt' -∗
        stackScratch (s + 18446744073709550528#64) m' -∗ statusRet N (s + 18446744073709550528#64 + 144#64).toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ))
    (hsg'.narrow hneed) hneed hsg'.le hslg hbb
  iframe H1 Hcode Hfr Hms Hst Hslot Hw HK
  isplitl []
  · ipureintro
    exact ⟨by ix_reg; exact hbh.s2, by ix_reg, by ix_reg; exact hbh.s3, by ix_reg,
      by ix_reg; exact hbh.sp⟩
  isplitl []
  · imodintro; rw [hpt]; unfold astSG; iexists P, m; iframe Hro; ipureintro; exact ⟨hsp, hbn.geo⟩
  iintro %R' %st' %status %hE %⟨hkeep, hst0⟩ Hms Hst Hret Hw HK

#ix_piece closureSeqP_cons_p2 from closureSeqP_cons_p1 by
  -- the status test and the back edge
  ihave #Hdv := roOwn_data hbn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗ frameAt inner aEnv.toNat ∗
      stackScratch (s + 18446744073709550528#64) m' ∗ statusRet N (s + 18446744073709550528#64 + 144#64).toNat status ∗
      world N L Room inp .uncounted st' d ∗ execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st'' : St) (status' : Status),
        ⌜ExecSeq st d inner (sm :: ss) st'' status'⌝ -∗
        ⌜KeepRegs closureKeep R R' ∧ R' 10 = statusCode status' ∧ Inv Mt'⌝ -∗ F -∗
        ms (closureExit status') R' (closureS s) Mt' -∗
        stackScratch (s + 18446744073709550528#64) m' -∗ statusRet N (s + 18446744073709550528#64 + 144#64).toNat status' -∗
        world N L Room inp .uncounted st'' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709550528#64) m' ∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat ∗
          ownSet (closureS s) byteAny) -∗ (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hret Hw IH; iexact HK
  intro F'
  have hR1 : KeepRegs calleeSaved R (upd R' 1 (BitVec.ofNat 64 (2147496820 + 4))) := by
    keep_split
    all_goals ix_keep [hkeep]
  refine ClosureLoop_runB (sc := statusCode status) (arr := arr) hlive hfg.sf hfg.lo hfg.hi hfg.al hbn.lo
    hbn.hi hbn.off hidx hbn.small ((hR1 8 (by decide)).trans hbh.s0) ((hR1 2 (by decide)).trans hbh.sp)
    (by ix_reg; exact hst0) (by rw [hMt1]; ix_fwd) hbn.cntw ?_ ?_ ?_
  · -- normal, the last statement: the loop leaves normally
    intro hc0 hc
    have hn : status = .normal := statusCode_eq_zero (by rw [← hst0]; revert hc0; ix_reg; exact id)
    subst hn
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, idx_succ,
      sext32_ofNat_toInt (show idx + 1 < 2 ^ 31 by have := hbn.small; omega),
      ofNat_toInt_small hbn.small] at hc
    intros
    apply swp_closeF
    cases ss with
    | cons s2 ss2 =>
      exfalso
      obtain ⟨hl2, -, -⟩ := drop_cons_facts hrest
      omega
    | nil =>
      unfold F'
      iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hret, Hw, #IH, HK⟩, Hms⟩
      ihave HK := and_elim_l $$ HK
      rw [← closureExit_normal] at *
      iapply HK $$ %_ %Mt1 %st' %Status.normal
        %(ExecSeq.consNormal _ _ _ _ _ _ _ _ hE (ExecSeq.nil _ _ _))
        %⟨KeepRegs.trans (hR1.sub (by decide)) ?_, by ix_reg; exact hst0, hinv1⟩ HF Hms Hst Hret Hw
      keep_split
      all_goals ix_reg
  · -- normal, more statements: the tail's loop
    intro hc0 hc
    have hn : status = .normal := statusCode_eq_zero (by rw [← hst0]; revert hc0; ix_reg; exact id)
    subst hn
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, idx_succ,
      sext32_ofNat_toInt (show idx + 1 < 2 ^ 31 by have := hbn.small; omega),
      ofNat_toInt_small hbn.small] at hc
    intros
    apply swp_closeRM
    intro R2 Mt2 hR2 hMt2
    subst hMt2
    cases ss with
    | nil => exfalso; have := List.drop_eq_nil_iff.mp hrest.symm; omega
    | cons s2 ss2 =>
      refine .trans ?_ (ih Φ st' (idx + 1) count aB arr aEnv s R2 Mt2 m P all m' Inv F
        (List.cons_ne_nil _ _) hrest hbn ?_ hfg hsg' hall hslg hinv1 hInv)
      · unfold F'
        iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hret, Hw, #IH, HK⟩, Hms⟩
        rw [statusRet_normal]
        iframe HF Hms Hcode Hro Hfr Hst Hret Hw IH
        have hR2' : KeepRegs closureKeep R R2 := by
          refine KeepRegs.trans (hR1.sub (by decide)) ?_
          keep_split
          all_goals (rw [hR2]; ix_reg)
        isplit
        · iintro %R'' %Mt'' %st'' %status'' %hE2 %⟨hk'', hst'', hinv''⟩ HF Hms Hst Hret Hw
          ihave HK := and_elim_l $$ HK
          iapply HK $$ %R'' %Mt'' %st'' %status'' %(ExecSeq.consNormal _ _ _ _ _ _ _ _ hE hE2)
            %⟨KeepRegs.trans hR2' hk'', hst'', hinv''⟩ HF Hms Hst Hret Hw
        · ihave HK := and_elim_r $$ HK
          iexact HK
      · rw [hR2]
        exact ⟨by ix_reg; exact (hR1 2 (by decide)).trans hbh.sp, by ix_reg,
          by ix_reg; exact idx_succ idx, by ix_reg; exact (hR1 18 (by decide)).trans hbh.s2,
          by ix_reg; exact (hR1 19 (by decide)).trans hbh.s3⟩
  · -- an abrupt status leaves the loop
    intro hc
    have hne : status ≠ .normal := by
      intro e; apply hc; ix_reg; rw [hst0, e]; rfl
    intros
    apply swp_closeF
    unfold F'
    iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hret, Hw, #IH, HK⟩, Hms⟩
    ihave HK := and_elim_l $$ HK
    iapply HK $$ %_ %Mt1 %st' %status %(ExecSeq.consAbrupt _ _ _ _ _ _ _ hE hne)
      %⟨hR1.sub (by decide), by ix_reg; exact hst0, hinv1⟩ HF [Hms] Hst Hret Hw
    rw [closureExit_abrupt hne]; iexact Hms

#ix_chain closureSeqP_cons := [closureSeqP_cons_p1, closureSeqP_cons_p2]



/-- **The closure body loop, partial mode, for every statement list.** -/
theorem closureSeqP_all {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
    [I : InterpGS GF] {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1) (N : NativeAddrs)
    (L : DlLayout) (Room : RoomPred) (inp : Nat) (Core : IProp GF) (d inner : Nat) :
    ∀ ss, closureSeqP_body (GF := GF) live N L Room inp Core d inner ss
  | [] => closureSeqP_nil live N L Room inp Core d inner
  | _ :: ss => closureSeqP_cons hlive (closureSeqP_all hlive N L Room inp Core d inner ss)

end VsaIris.Interp
