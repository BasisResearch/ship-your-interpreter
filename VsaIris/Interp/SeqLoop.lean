import VsaIris.Interp.Arm

/-!
# `seqLoop`: the statement-sequence loop (INTERP_DESIGN.md §4.3), block site

`exec_stmt`'s block arm runs its statements with a do-while loop
(`0x800041a4`..`0x800041dc`): the head loads the statement pointer and spills
the index (`sp+8`), the `jal exec_stmt` at `0x800041c4`, then `bnez a0` leaves
on an abrupt status and `blt` loops while statements remain. The loop is
stated as the recursor motive of `ExecSeqCost` (`blockSeqT_body`, total mode),
proved case by case (`blockSeqT_consNormal`, `blockSeqT_consAbrupt`); the
recursor supplies the induction.

The two runs are `#ix_seg` lemmas (`BlockLoop_runA`: head to the call;
`BlockLoop_runB`: status test and back edge, three outcomes).
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- The bytes of a block node (statement array pointer and count) and its
statement array a run reads. -/
abbrev blockView (a arr count : Nat) : List Nat := accAddrs (a + 8) 12 ++ accAddrs arr (8 * count)

/-- The loop head's registers: the node, the interpreter, the `ret` slot, the
inner frame pointer, the lowered `sp`, the index. -/
structure BlockHead (R : Nat → BitVec 64) (s aS inp aRet aInner : BitVec 64) (idx : Nat) : Prop where
  sp : R 2 = s + 18446744073709551440#64
  s0 : R 8 = aS
  s1 : R 9 = inp
  s2 : R 18 = aRet
  s3 : R 19 = aInner
  a6 : R 16 = BitVec.ofNat 64 idx

/-- An element of a represented statement array. -/
theorem stmtArray_get {m : Mem} {P : Nat → Prop} :
    ∀ {a n : Nat} {ss : List Vsa.While.Stmt}, StmtArrayReprWithin m P a n ss →
      ∀ j (h : j < ss.length), ∃ p, read64 m (a + 8 * j) = some p ∧ StmtReprWithin m P p ss[j]
  | _, _, _, .nil, j, h => absurd h (by simp)
  | _, _, _, .cons hp _ hs hrest, 0, _ => ⟨_, by simpa using hp, hs⟩
  | a, _, _, .cons _ _ _ hrest, j + 1, h => by
    obtain ⟨p, hp, hs⟩ := stmtArray_get hrest j (by simpa using h)
    exact ⟨p, by rw [show a + 8 * (j + 1) = a + 8 + 8 * j by omega]; exact hp, hs⟩

theorem stmtArray_length {m : Mem} {P : Nat → Prop} :
    ∀ {a n : Nat} {ss : List Vsa.While.Stmt}, StmtArrayReprWithin m P a n ss → ss.length = n
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ _ _ hrest => by simp [stmtArray_length hrest]

/-- `addi` then `sext.w` of a small index: the next index. -/
theorem idx_succ (idx : Nat) : BitVec.ofNat 64 idx + 1#64 = BitVec.ofNat 64 (idx + 1) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem sext32_ofNat_toInt {a : Nat} (h : a < 2 ^ 31) :
    (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a))).toInt = a := by
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  have e : (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a)).toNat = a := by
    simp [BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_zero]; omega
  rw [BitVec.toInt_eq_toNat_cond, e]; simp; omega

theorem ofNat_toInt_small {a : Nat} (h : a < 2 ^ 31) : (BitVec.ofNat 64 a).toInt = a := by
  rw [BitVec.toInt_eq_toNat_cond]; simp; omega

#ix_seg BlockLoop_runA {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s arr pS : BitVec 64} {idx count : Nat}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 24 ≤ 0x100000000)
    (hx3 : aS.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (ha1 : 0x80000000 ≤ arr.toNat) (ha2 : arr.toNat + 8 * count ≤ 0x100000000)
    (ha3 : arr.toNat + 8 * count ≤ tohostAddr ∨ tohostAddr + 16 ≤ arr.toNat)
    (hidx : idx < count) (hc : count < 2 ^ 31)
    (h8 : R 8 = aS) (h16 : R 16 = BitVec.ofNat 64 idx) (h2 : R 2 = s + 18446744073709551440#64)
    (harr : ldv .ld m (aS + 8#64).toNat = arr)
    (hel : ldv .ld m (arr + BitVec.ofNat 64 idx <<< 3).toNat = pS) :
    IW live m (blockView aS.toNat arr.toNat count) (InExt (s.toNat - 176, 176)) Q 0x800041a4#64 R Mt
  by ix_run hlive using [h8, h16, h2, harr, hel, hsf] at 0x800041c4


#ix_seg BlockLoop_runB {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s arr sc : BitVec 64} {idx count : Nat}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 24 ≤ 0x100000000)
    (hx3 : aS.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (hidx : idx < count) (hc : count < 2 ^ 31)
    (h8 : R 8 = aS) (h2 : R 2 = s + 18446744073709551440#64) (h10 : R 10 = sc)
    (hi : ldv .ld Mt (s + 18446744073709551440#64 + 8#64).toNat = BitVec.ofNat 64 idx)
    (hcnt : ldv .lw m (aS + 16#64).toNat = BitVec.ofNat 64 count) :
    IW live m (blockView aS.toNat arr.toNat count) (InExt (s.toNat - 176, 176)) Q 0x800041c8#64 R Mt
  by ix_run hlive using [h8, h2, h10, hi, hcnt, hsf] at 0x800041a4 0x8000409c


/-- A block node over a geometric view: its array pointer and count reads,
placement, and the represented statement array. -/
structure BlockNode (m : Mem) (P : Nat → Prop) (aS arr : BitVec 64) (count : Nat)
    (all : List Vsa.While.Stmt) : Prop where
  arrw : ldv .ld m (aS + 8#64).toNat = arr
  cntw : ldv .lw m (aS + 16#64).toNat = BitVec.ofNat 64 count
  lo : 0x80000000 ≤ aS.toNat
  hi : aS.toNat + 24 ≤ 0x100000000
  off : aS.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat
  alo : 0x80000000 ≤ arr.toNat
  ahi : arr.toNat + 8 * count ≤ 0x100000000
  aoff : arr.toNat + 8 * count ≤ tohostAddr ∨ tohostAddr + 16 ≤ arr.toNat
  small : count < 2 ^ 31
  repr : StmtArrayReprWithin m P arr.toNat count all
  geo : ∀ k, P k → ReadOK k
  view : ∀ a ∈ blockView aS.toNat arr.toNat count, P a ∧ (m[a]?).isSome

/-- `exec_stmt`'s entry `sp` with its 176-byte frame below it. -/
structure ExecFrameGeom (s : BitVec 64) : Prop where
  sf : (s + 18446744073709551440#64).toNat = s.toNat - 176
  lo : 0x87800000 + 176 ≤ s.toNat
  hi : s.toNat ≤ 0x88000000
  al : s.toNat % 16 = 0

theorem drop_cons_facts {α : Type} {all : List α} {idx : Nat} {x : α} {xs : List α}
    (h : x :: xs = all.drop idx) : ∃ hl : idx < all.length, all[idx] = x ∧ xs = all.drop (idx + 1) := by
  have hl : idx < all.length := by
    refine Classical.byContradiction fun hc => ?_
    rw [List.drop_eq_nil_of_le (by omega)] at h
    cases h
  rw [List.drop_eq_getElem_cons hl] at h
  injection h with h1 h2
  exact ⟨hl, h1.symm, h2⟩

theorem KeepRegs.trans {ks : List Nat} {R R' R'' : Nat → BitVec 64} (h1 : KeepRegs ks R R')
    (h2 : KeepRegs ks R' R'') : KeepRegs ks R R'' := fun x hx => (h2 x hx).trans (h1 x hx)

/-- A statement pointer's address in the array (`slli`/`add` of the index). -/
theorem arr_elem_addr {arr : BitVec 64} {idx count : Nat} (h : arr.toNat + 8 * count ≤ 0x100000000)
    (hi : idx < count) : (arr + BitVec.ofNat 64 idx <<< 3).toNat = arr.toNat + 8 * idx := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  have : idx % 2 ^ 64 = idx := Nat.mod_eq_of_lt (by omega)
  rw [this, Nat.shiftLeft_eq, show (2 : Nat) ^ 3 = 8 by rfl]
  rw [Nat.mod_eq_of_lt (a := idx * 8) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- A child's stack geometry inside the region below the lowered `sp`. -/
theorem StackGeom.narrow {s : BitVec 64} {m n : Nat} (h : StackGeom s m) (hn : n ≤ m) :
    StackGeom s n :=
  ⟨by have := h.le; omega, by have := h.lo; omega, h.hi, h.al, h.top⟩

section Motive

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- **The block loop, total mode**: the motive of `ExecSeqCost` at the block
site. From the loop head with the statements `ss` (a nonempty suffix of the
block's array `all`, from index `idx`), the loop runs them against the
derivation and leaves at the epilogue (`0x8000409c`) with the status in `a0`,
the `ret` slot as `statusRet`, the callee-saved registers kept, and the
frame invariant `Inv` (which the index spill at `sp+8` preserves). `F` is
the arm's frame, handed through. -/
def blockSeqT_body (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (st : St) (d inner : Nat) (ss : List Vsa.While.Stmt) (st' : St) (status : Status)
    (n : Nat) (_D : ExecSeqCost st d inner ss st' status n) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (k idx count : Nat) (aS arr aRet aInner s : BitVec 64)
    (R : Nat → BitVec 64) (Mt m : Mem) (P : Nat → Prop) (all : List Vsa.While.Stmt) (m' : Nat)
    (Inv : Mem → Prop) (F : IProp GF),
    ss ≠ [] → ss = all.drop idx → BlockNode m P aS arr count all →
    BlockHead R s aS (BitVec.ofNat 64 inp) aRet aInner idx → ExecFrameGeom s →
    StackGeom (s + 18446744073709551440#64) m' →
    (∀ x ∈ all, execNeed x d ≤ m' ∧ x.bodiesBound perCallBudget = true) → SlotGeom aRet →
    Inv Mt → (∀ M v, Inv M → Inv (writeLog M [((s + 18446744073709551440#64 + 8#64).toNat, 8, v)])) →
    (F ∗ ms 0x800041a4#64 R (InExt (s.toNat - 176, 176)) Mt ∗ codeRes ∗ roOn P m ∗
      □ frameAt inner aInner.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp (.counted (k + n)) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms 0x8000409c#64 R' (InExt (s.toNat - 176, 176)) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)
      ⊢ (twpW (vsaModel live)).W Φ)

/-- The empty sequence never reaches the loop head (the arm's `blez` skips the
loop): the motive holds vacuously. -/
theorem blockSeqT_nil (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (st : St) (d inner : Nat) :
    blockSeqT_body (GF := GF) live N L Room inp st d inner [] st .normal 0 (.nil st d inner) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd rfl h

/-- **The block loop, partial mode**: by structure on the statements `ss`
(the outcomes are not known in advance). Each statement runs through the Löb
hypothesis `execSpecsP`; the loop leaves at the epilogue with SOME outcome
and its derivation `ExecSeq`, or aborts, handing its abort continuation the
stack below the lowered `sp`, the `ret` slot and the frame bytes. The two
continuations are an additive pair (INTERP_DESIGN.md §10.1). -/
def blockSeqP_body (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (Core : IProp GF) (d inner : Nat) (ss : List Vsa.While.Stmt) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (st : St) (idx count : Nat) (aS arr aRet aInner s : BitVec 64)
    (R : Nat → BitVec 64) (Mt m : Mem) (P : Nat → Prop) (all : List Vsa.While.Stmt) (m' : Nat)
    (Inv : Mem → Prop) (F : IProp GF),
    ss ≠ [] → ss = all.drop idx → BlockNode m P aS arr count all →
    BlockHead R s aS (BitVec.ofNat 64 inp) aRet aInner idx → ExecFrameGeom s →
    StackGeom (s + 18446744073709551440#64) m' →
    (∀ x ∈ all, execNeed x d ≤ m' ∧ x.bodiesBound perCallBudget = true) → SlotGeom aRet →
    Inv Mt → (∀ M v, Inv M → Inv (writeLog M [((s + 18446744073709551440#64 + 8#64).toNat, 8, v)])) →
    (F ∗ ms 0x800041a4#64 R (InExt (s.toNat - 176, 176)) Mt ∗ codeRes ∗ roOn P m ∗
      □ frameAt inner aInner.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp .uncounted st d ∗
      execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ExecSeq st d inner ss st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms 0x8000409c#64 R' (InExt (s.toNat - 176, 176)) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (InExt (s.toNat - 176, 176)) byteAny) -∗ (wpW (vsaModel live)).W Φ))
      ⊢ (wpW (vsaModel live)).W Φ)

theorem blockSeqP_nil (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (Core : IProp GF) (d inner : Nat) :
    blockSeqP_body (GF := GF) live N L Room inp Core d inner [] :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd rfl h

theorem statusCode_eq_zero {status : Status} (h : statusCode status = 0#64) : status = .normal := by
  cases status <;> simp_all [statusCode]

end Motive

/-! ## The cases (proof pieces, one declaration each) -/

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr

#ix_piece blockSeqT_consNormal_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
    [I : InterpGS GF] {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d inner : Nat} {sm : Vsa.While.Stmt} {ss : List Vsa.While.Stmt} {st' st'' : St}
    {status : Status} {n1 n2 : Nat}
    (D1 : ExecSCost st d inner sm st' .normal n1) (D2 : ExecSeqCost st' d inner ss st'' status n2)
    (h1 : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st d inner sm st' .normal n1 D1)
    (h2 : blockSeqT_body (GF := GF) live N L Room inp st' d inner ss st'' status n2 D2) :
    blockSeqT_body (GF := GF) live N L Room inp st d inner (sm :: ss) st'' status (n1 + n2)
      (.consNormal st d inner sm ss st' st'' status n1 n2 D1 D2) by
  intro Φ k idx count aS arr aRet aInner s R Mt m P all m' Inv F _ hdrop hbn hbh hfg hsg' hall hslg
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
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗ frameAt inner aInner.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted (k + (n1 + n2))) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms 0x8000409c#64 R' (InExt (s.toNat - 176, 176)) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp (.counted k) st'' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hslot Hw; iexact Hk
  intro F'
  refine BlockLoop_runA (pS := BitVec.ofNat 64 p) hlive hfg.sf hfg.lo hfg.hi hfg.al hbn.lo hbn.hi hbn.off
    hbn.alo hbn.ahi hbn.aoff hidx hbn.small hbh.s0 hbh.a6 hbh.sp hbn.arrw hel ?_
  intros
  apply swp_closeM
  intro Mt1 hMt1
  have hinv1 : Inv Mt1 := by rw [hMt1]; exact hInv _ _ hinv
  unfold F'
  iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- the statement
  ihave H1 := h1
  rw [show k + (n1 + n2) = k + n2 + n1 by omega]
  iapply ms_callExecT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x800041c4)
    (jalx_800041c4 live (fun p hp => hlive _ (interp_code_800041c4 p hp)))
    interp_code_800041c4 (by decide) D1 (k := k + n2) (aS := BitVec.ofNat 64 p) (aE := aInner)
    (aRet := aRet) (s := s + 18446744073709551440#64) (m := m')
    (hsg'.narrow hneed) hneed hsg'.le hslg hbb
  iframe H1 Hcode Hfr Hms Hst Hslot Hw
  isplitl []
  · ipureintro
    exact ⟨by ix_reg; exact hbh.s1, by ix_reg, by ix_reg; exact hbh.s3, by ix_reg; exact hbh.s2,
      by ix_reg; exact hbh.sp⟩
  isplitl []
  · imodintro; rw [hpt]; unfold astSG; iexists P, m; iframe Hro; ipureintro; exact ⟨hsp, hbn.geo⟩
  iintro %R' %⟨hkeep, hst0⟩ Hms Hst Hret Hw
  rw [statusRet_normal]

#ix_piece blockSeqT_consNormal_p2 from blockSeqT_consNormal_p1 by
  -- the status test and the back edge
  ihave #Hdv := roOwn_data hbn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗ frameAt inner aInner.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted (k + n2)) st' d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms 0x8000409c#64 R' (InExt (s.toNat - 176, 176)) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp (.counted k) st'' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hret Hw; iexact Hk
  intro F'
  have hR1 : KeepRegs calleeSaved R (upd R' 1 (BitVec.ofNat 64 (2147500484 + 4))) := by
    intro x hx
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      ix_keep [hkeep]
  refine BlockLoop_runB (sc := 0#64) (arr := arr) hlive hfg.sf hfg.lo hfg.hi hfg.al hbn.lo hbn.hi
    hbn.off hidx hbn.small ((hR1 8 (by decide)).trans hbh.s0) ((hR1 2 (by decide)).trans hbh.sp)
    (by ix_reg; exact hst0) (by rw [hMt1]; ix_fwd) hbn.cntw ?_ ?_ ?_
  · -- an abrupt status: not this derivation's
    intro hc; exfalso; apply hc; ix_reg; exact hst0
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
      refine .trans ?_ (h2 Φ k (idx + 1) count aS arr aRet aInner s R2 Mt2 m P all m' Inv F
        (List.cons_ne_nil _ _) hrest hbn ?_ hfg hsg' hall hslg hinv1 hInv)
      · unfold F'
        iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hret, Hw, Hk⟩, Hms⟩
        iframe HF Hms Hcode Hro Hfr Hst Hret Hw
        iintro %R'' %Mt'' %⟨hk'', hst'', hinv''⟩ HF Hms Hst Hret Hw
        iapply Hk $$ %R'' %Mt'' %⟨KeepRegs.trans (KeepRegs.trans ?_ ?_) hk'', hst'', hinv''⟩ HF Hms Hst Hret Hw
        · exact hR1
        · intro x hx
          simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
          rw [hR2]
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
      · rw [hR2]
        exact ⟨by ix_reg; exact (hR1 2 (by decide)).trans hbh.sp, by ix_reg; exact (hR1 8 (by decide)).trans hbh.s0,
          by ix_reg; exact (hR1 9 (by decide)).trans hbh.s1, by ix_reg; exact (hR1 18 (by decide)).trans hbh.s2,
          by ix_reg; exact (hR1 19 (by decide)).trans hbh.s3, by ix_reg; exact idx_succ idx⟩
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
      rw [statusRet_normal]
      iapply Hk $$ %_ %Mt1 %⟨?_, by ix_reg; rfl, hinv1⟩ HF Hms Hst Hret Hw
      refine KeepRegs.trans hR1 ?_
      intro x hx
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg

#ix_chain blockSeqT_consNormal := [blockSeqT_consNormal_p1, blockSeqT_consNormal_p2]


#ix_piece blockSeqT_consAbrupt_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
    [I : InterpGS GF] {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d inner : Nat} {sm : Vsa.While.Stmt} {ss : List Vsa.While.Stmt} {st' st'' : St}
    {status : Status} {n : Nat}
    (D1 : ExecSCost st d inner sm st' status n) (hne : status ≠ .normal)
    (h1 : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st d inner sm st' status n D1) :
    blockSeqT_body (GF := GF) live N L Room inp st d inner (sm :: ss) st' status n
      (.consAbrupt st d inner sm ss st' status n D1 hne) by
  intro Φ k idx count aS arr aRet aInner s R Mt m P all m' Inv F _ hdrop hbn hbh hfg hsg' hall hslg
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
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗ frameAt inner aInner.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted (k + n)) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms 0x8000409c#64 R' (InExt (s.toNat - 176, 176)) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hslot Hw; iexact Hk
  intro F'
  refine BlockLoop_runA (pS := BitVec.ofNat 64 p) hlive hfg.sf hfg.lo hfg.hi hfg.al hbn.lo hbn.hi hbn.off
    hbn.alo hbn.ahi hbn.aoff hidx hbn.small hbh.s0 hbh.a6 hbh.sp hbn.arrw hel ?_
  intros
  apply swp_closeM
  intro Mt1 hMt1
  have hinv1 : Inv Mt1 := by rw [hMt1]; exact hInv _ _ hinv
  unfold F'
  iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- the statement
  ihave H1 := h1
  iapply ms_callExecT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x800041c4)
    (jalx_800041c4 live (fun p hp => hlive _ (interp_code_800041c4 p hp)))
    interp_code_800041c4 (by decide) D1 (k := k) (aS := BitVec.ofNat 64 p) (aE := aInner)
    (aRet := aRet) (s := s + 18446744073709551440#64) (m := m')
    (hsg'.narrow hneed) hneed hsg'.le hslg hbb
  iframe H1 Hcode Hfr Hms Hst Hslot Hw
  isplitl []
  · ipureintro
    exact ⟨by ix_reg; exact hbh.s1, by ix_reg, by ix_reg; exact hbh.s3, by ix_reg; exact hbh.s2,
      by ix_reg; exact hbh.sp⟩
  isplitl []
  · imodintro; rw [hpt]; unfold astSG; iexists P, m; iframe Hro; ipureintro; exact ⟨hsp, hbn.geo⟩
  iintro %R' %⟨hkeep, hst0⟩ Hms Hst Hret Hw


#ix_piece blockSeqT_consAbrupt_p2 from blockSeqT_consAbrupt_p1 by
  -- the status test: an abrupt status leaves the loop
  ihave #Hdv := roOwn_data hbn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗ frameAt inner aInner.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗ statusRet N aRet.toNat status ∗
      world N L Room inp (.counted k) st' d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms 0x8000409c#64 R' (InExt (s.toNat - 176, 176)) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hret Hw; iexact Hk
  intro F'
  have hR1 : KeepRegs calleeSaved R (upd R' 1 (BitVec.ofNat 64 (2147500484 + 4))) := by
    intro x hx
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      ix_keep [hkeep]
  have hsc : statusCode status ≠ 0#64 := by cases status <;> simp_all [statusCode]
  refine BlockLoop_runB (sc := statusCode status) (arr := arr) hlive hfg.sf hfg.lo hfg.hi hfg.al hbn.lo
    hbn.hi hbn.off hidx hbn.small ((hR1 8 (by decide)).trans hbh.s0) ((hR1 2 (by decide)).trans hbh.sp)
    (by ix_reg; exact hst0) (by rw [hMt1]; ix_fwd) hbn.cntw ?_ ?_ ?_
  · intro _
    intros
    apply swp_closeF
    unfold F'
    iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hret, Hw, Hk⟩, Hms⟩
    iapply Hk $$ %_ %Mt1 %⟨hR1, by ix_reg; exact hst0, hinv1⟩ HF Hms Hst Hret Hw
  · intro hc; exfalso; apply hc; ix_reg; rw [hst0]; exact hsc
  · intro hc; exfalso; apply hc; ix_reg; rw [hst0]; exact hsc

#ix_chain blockSeqT_consAbrupt := [blockSeqT_consAbrupt_p1, blockSeqT_consAbrupt_p2]



#ix_piece blockSeqP_cons_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
    [I : InterpGS GF] {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {d inner : Nat} {sm : Vsa.While.Stmt} {ss : List Vsa.While.Stmt}
    (ih : blockSeqP_body (GF := GF) live N L Room inp Core d inner ss) :
    blockSeqP_body (GF := GF) live N L Room inp Core d inner (sm :: ss) by
  intro Φ st idx count aS arr aRet aInner s R Mt m P all m' Inv F _ hdrop hbn hbh hfg hsg' hall hslg
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
  iapply wp_swpF (wpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗ frameAt inner aInner.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
      world N L Room inp .uncounted st d ∗ execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ExecSeq st d inner (sm :: ss) st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms 0x8000409c#64 R' (InExt (s.toNat - 176, 176)) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (InExt (s.toNat - 176, 176)) byteAny) -∗ (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hslot Hw IH; iexact HK
  intro F'
  refine BlockLoop_runA (pS := BitVec.ofNat 64 p) hlive hfg.sf hfg.lo hfg.hi hfg.al hbn.lo hbn.hi hbn.off
    hbn.alo hbn.ahi hbn.aoff hidx hbn.small hbh.s0 hbh.a6 hbh.sp hbn.arrw hel ?_
  intros
  apply swp_closeM
  intro Mt1 hMt1
  have hinv1 : Inv Mt1 := by rw [hMt1]; exact hInv _ _ hinv
  unfold F'
  iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hslot, Hw, #IH, HK⟩, Hms⟩
  -- the statement, through the Löb hypothesis
  ihave H1 := execSpecsP_at Core st d inner sm $$ IH
  iapply ms_callExecP (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x800041c4)
    (jalx_800041c4 live (fun p hp => hlive _ (interp_code_800041c4 p hp)))
    interp_code_800041c4 (by decide) (Core := Core) (st := st) (d := d) (env := inner) (sm := sm)
    (aS := BitVec.ofNat 64 p) (aE := aInner) (aRet := aRet) (s := s + 18446744073709551440#64)
    (m := m') (Kret := iprop(∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ExecSeq st d inner (sm :: ss) st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧ Inv Mt'⌝ -∗ F -∗
        ms 0x8000409c#64 R' (InExt (s.toNat - 176, 176)) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ))
    (hsg'.narrow hneed) hneed hsg'.le hslg hbb
  iframe H1 Hcode Hfr Hms Hst Hslot Hw HK
  isplitl []
  · ipureintro
    exact ⟨by ix_reg; exact hbh.s1, by ix_reg, by ix_reg; exact hbh.s3, by ix_reg; exact hbh.s2,
      by ix_reg; exact hbh.sp⟩
  isplitl []
  · imodintro; rw [hpt]; unfold astSG; iexists P, m; iframe Hro; ipureintro; exact ⟨hsp, hbn.geo⟩
  iintro %R' %st' %status %hE %⟨hkeep, hst0⟩ Hms Hst Hret Hw HK

#ix_piece blockSeqP_cons_p2 from blockSeqP_cons_p1 by
  -- the status test and the back edge
  ihave #Hdv := roOwn_data hbn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗ frameAt inner aInner.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗ statusRet N aRet.toNat status ∗
      world N L Room inp .uncounted st' d ∗ execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st'' : St) (status' : Status),
        ⌜ExecSeq st d inner (sm :: ss) st'' status'⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status' ∧ Inv Mt'⌝ -∗ F -∗
        ms 0x8000409c#64 R' (InExt (s.toNat - 176, 176)) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status' -∗
        world N L Room inp .uncounted st'' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (InExt (s.toNat - 176, 176)) byteAny) -∗ (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hret Hw IH; iexact HK
  intro F'
  have hR1 : KeepRegs calleeSaved R (upd R' 1 (BitVec.ofNat 64 (2147500484 + 4))) := by
    intro x hx
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      ix_keep [hkeep]
  refine BlockLoop_runB (sc := statusCode status) (arr := arr) hlive hfg.sf hfg.lo hfg.hi hfg.al hbn.lo
    hbn.hi hbn.off hidx hbn.small ((hR1 8 (by decide)).trans hbh.s0) ((hR1 2 (by decide)).trans hbh.sp)
    (by ix_reg; exact hst0) (by rw [hMt1]; ix_fwd) hbn.cntw ?_ ?_ ?_
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
      %⟨hR1, by ix_reg; exact hst0, hinv1⟩ HF Hms Hst Hret Hw
  · -- normal, more statements: the tail's loop
    intro hc0 hc
    have hn : status = .normal := statusCode_eq_zero
      (Classical.byContradiction fun hne => hc0 (by ix_reg; rw [hst0]; exact hne))
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
      refine .trans ?_ (ih Φ st' (idx + 1) count aS arr aRet aInner s R2 Mt2 m P all m' Inv F
        (List.cons_ne_nil _ _) hrest hbn ?_ hfg hsg' hall hslg hinv1 hInv)
      · unfold F'
        iintro ⟨⟨HF, #Hcode, #Hro, #Hfr, Hst, Hret, Hw, #IH, HK⟩, Hms⟩
        rw [statusRet_normal]
        iframe HF Hms Hcode Hro Hfr Hst Hret Hw IH
        have hR2' : KeepRegs calleeSaved R R2 := by
          refine KeepRegs.trans hR1 ?_
          intro x hx
          simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
          rw [hR2]
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
        isplit
        · iintro %R'' %Mt'' %st'' %status'' %hE2 %⟨hk'', hst'', hinv''⟩ HF Hms Hst Hret Hw
          ihave HK := and_elim_l $$ HK
          iapply HK $$ %R'' %Mt'' %st'' %status'' %(ExecSeq.consNormal _ _ _ _ _ _ _ _ hE hE2)
            %⟨KeepRegs.trans hR2' hk'', hst'', hinv''⟩ HF Hms Hst Hret Hw
        · ihave HK := and_elim_r $$ HK
          iexact HK
      · rw [hR2]
        exact ⟨by ix_reg; exact (hR1 2 (by decide)).trans hbh.sp, by ix_reg; exact (hR1 8 (by decide)).trans hbh.s0,
          by ix_reg; exact (hR1 9 (by decide)).trans hbh.s1, by ix_reg; exact (hR1 18 (by decide)).trans hbh.s2,
          by ix_reg; exact (hR1 19 (by decide)).trans hbh.s3, by ix_reg; exact idx_succ idx⟩
  · -- normal, the last statement: the loop leaves normally
    intro hc0 hc
    have hn : status = .normal := statusCode_eq_zero
      (Classical.byContradiction fun hne => hc0 (by ix_reg; rw [hst0]; exact hne))
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
      iapply HK $$ %_ %Mt1 %st' %Status.normal
        %(ExecSeq.consNormal _ _ _ _ _ _ _ _ hE (ExecSeq.nil _ _ _))
        %⟨KeepRegs.trans hR1 ?_, by ix_reg; rfl, hinv1⟩ HF Hms Hst Hret Hw
      intro x hx
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg

#ix_chain blockSeqP_cons := [blockSeqP_cons_p1, blockSeqP_cons_p2]


/-- **The block loop, partial mode, for every statement list** (structural
induction; each statement through the Löb hypothesis). -/
theorem blockSeqP_all {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1) (N : NativeAddrs) (L : DlLayout)
    (Room : RoomPred) (inp : Nat) (Core : IProp GF) (d inner : Nat) :
    ∀ ss, blockSeqP_body (GF := GF) live N L Room inp Core d inner ss
  | [] => blockSeqP_nil live N L Room inp Core d inner
  | _ :: ss => blockSeqP_cons hlive (blockSeqP_all hlive N L Room inp Core d inner ss)

end VsaIris.Interp
