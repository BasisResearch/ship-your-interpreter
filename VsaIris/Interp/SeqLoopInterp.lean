import VsaIris.Interp.SeqLoop

/-!
# `seqLoop`, `interp_run` site (INTERP_DESIGN.md §4.3, §4.4)

`interp_run`'s statement loop (`0x8000448c`..`0x80004488`): a cursor `s0`
walks the program's statement array to the bound `s2`; `main` passes
`repl = 0` (`0x800045e0 li a3,0`), so each iteration initializes the result
slot `sp+88` with `value_null`, calls `exec_stmt` in the global frame
(`in->globals`, read from `in` spilled at `sp+0`), and routes the status:
`ret` to `0x80004540`, `brk`/`cont` to `0x80004564` (the two runtime errors),
the program's end to the epilogue `0x80004514`, otherwise the next statement.
The loop owns neither the statement array nor `in->globals`: the runs read
them through one merged view `Dt` (`InterpData`). The frame bytes are not
written by the loop, so the tracking memory is the same at every exit.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- The `interp_run` loop's owned frame bytes: its 176-byte frame without the
result slot `sp+88`, which the loop lends each statement. -/
abbrev interpS (s : BitVec 64) : Nat → Prop :=
  fun b => InExt (s.toNat - 176, 176) b ∧ ¬ InExt (s.toNat - 176 + 88, 24) b

/-- The bytes an `interp_run` iteration reads that it does not own: the
statement array and `in->globals`. -/
abbrev interpView (arr count inp : Nat) : List Nat := accAddrs arr (8 * count) ++ accAddrs inp 8

#ix_seg InterpLoop_runA {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Dt Mt : Mem} {R : Nat → BitVec 64}
    {s arr pS : BitVec 64} {idx count inp : Nat}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (ha1 : 0x80000000 ≤ arr.toNat) (ha2 : arr.toNat + 8 * count ≤ 0x100000000)
    (ha3 : arr.toNat + 8 * count ≤ tohostAddr ∨ tohostAddr + 16 ≤ arr.toNat)
    (hidx : idx < count) (hc : count < 2 ^ 31)
    (h8 : R 8 = arr + BitVec.ofNat 64 (8 * idx)) (h2 : R 2 = s + 18446744073709551440#64)
    (hflag : ldv .ld Mt (s + 18446744073709551440#64 + 8#64).toNat = 0#64)
    (hel : ldv .ld Dt (arr + BitVec.ofNat 64 (8 * idx)).toNat = pS) :
    IW live Dt (interpView arr.toNat count inp) (interpS s) Q 0x8000448c#64 R Mt
  by ix_run hlive using [h8, h2, hflag, hel, hsf, interpS] at 0x8000445c


#ix_seg InterpLoop_runH {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Dt Mt : Mem} {R : Nat → BitVec 64}
    {s arr g : BitVec 64} {count inp : Nat}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hi1 : 0x80000000 ≤ inp) (hi2 : inp + 8 ≤ 0x100000000)
    (hi3 : inp + 8 ≤ tohostAddr ∨ tohostAddr + 16 ≤ inp)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hin : ldv .ld Mt (s.toNat - 176) = BitVec.ofNat 64 inp)
    (hg : ldv .ld Dt inp = g) :
    IW live Dt (interpView arr.toNat count inp) (interpS s) Q 0x80004460#64 R Mt
  by ix_run hlive using [h2, hin, hg, hsf, interpS,
    show (BitVec.ofNat 64 inp).toNat = inp from by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]
    at 0x80004474


#ix_seg InterpLoop_runB {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Dt Mt : Mem} {R : Nat → BitVec 64}
    {s arr sc : BitVec 64} {idx count inp : Nat}
    (h10 : R 10 = sc) (h19 : R 19 = 3#64) (h20 : R 20 = 1#64)
    (h8 : R 8 = arr + BitVec.ofNat 64 (8 * idx)) (h18 : R 18 = arr + BitVec.ofNat 64 (8 * count)) :
    IW live Dt (interpView arr.toNat count inp) (interpS s) Q 0x80004478#64 R Mt
  by ix_run hlive using [h10, h19, h20, h8, h18] at 0x8000448c 0x80004514 0x80004540 0x80004564


/-- The loop head's registers: the cursor, the array's end, the status
constants `3` and `1`, the lowered `sp`. -/
structure InterpHead (R : Nat → BitVec 64) (s arr : BitVec 64) (idx count : Nat) : Prop where
  sp : R 2 = s + 18446744073709551440#64
  cur : R 8 = arr + BitVec.ofNat 64 (8 * idx)
  bnd : R 18 = arr + BitVec.ofNat 64 (8 * count)
  s3 : R 19 = 3#64
  s4 : R 20 = 1#64

/-- The merged view the runs read: the statement array (agreeing with the
AST view `m`) and `in->globals`, with their placement. -/
structure InterpData (Dt m : Mem) (P : Nat → Prop) (arr : BitVec 64) (count inp : Nat)
    (g : BitVec 64) (all : List Vsa.While.Stmt) : Prop where
  agree : ∀ a, arr.toNat ≤ a → a < arr.toNat + 8 * count → imgM Dt a = imgM m a
  glob : ldv .ld Dt inp = g
  alo : 0x80000000 ≤ arr.toNat
  ahi : arr.toNat + 8 * count ≤ 0x100000000
  aoff : arr.toNat + 8 * count ≤ tohostAddr ∨ tohostAddr + 16 ≤ arr.toNat
  ilo : 0x80000000 ≤ inp
  ihi : inp + 8 ≤ 0x100000000
  ioff : inp + 8 ≤ tohostAddr ∨ tohostAddr + 16 ≤ inp
  small : count < 2 ^ 31
  repr : StmtArrayReprWithin m P arr.toNat count all
  geo : ∀ k, P k → ReadOK k

/-- The frame words the loop reads: the `repl` flag (`0`) and `in`. -/
structure InterpFrame (Mt : Mem) (s : BitVec 64) (inp : Nat) : Prop where
  flag : ldv .ld Mt (s + 18446744073709551440#64 + 8#64).toNat = 0#64
  inp : ldv .ld Mt (s.toNat - 176) = BitVec.ofNat 64 inp

/-- What the loop keeps: the callee-saved registers but the cursor `s0` and
the statement pointer `s1`. -/
abbrev interpKeep : List Nat := [2, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The loop's exits by status: the epilogue, the `ret` error, the
`brk`/`cont` error. -/
def interpExit : Status → BitVec 64
  | .normal => 0x80004514#64
  | .ret _ => 0x80004540#64
  | _ => 0x80004564#64

/-- A load from the statement array, through the merged view. -/
theorem InterpData.elem {Dt m : Mem} {P : Nat → Prop} {arr g : BitVec 64} {count inp : Nat}
    {all : List Vsa.While.Stmt} (h : InterpData Dt m P arr count inp g all) {idx p : Nat}
    (hi : idx < count) (hp : read64 m (arr.toNat + 8 * idx) = some p) :
    ldv .ld Dt (arr + BitVec.ofNat 64 (8 * idx)).toNat = BitVec.ofNat 64 p := by
  have ha : (arr + BitVec.ofNat 64 (8 * idx)).toNat = arr.toNat + 8 * idx := by
    have := h.ahi; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [ha, ← ldv_ld_read64 hp]
  show bytesVal .ld (bytesAt (imgM Dt) _ 8) = bytesVal .ld (bytesAt (imgM m) _ 8)
  rw [bytesAt8, bytesAt8]
  rw [h.agree _ (by omega) (by omega), h.agree _ (by omega) (by omega), h.agree _ (by omega) (by omega),
    h.agree _ (by omega) (by omega), h.agree _ (by omega) (by omega), h.agree _ (by omega) (by omega),
    h.agree _ (by omega) (by omega), h.agree _ (by omega) (by omega)]

/-- The cursor after `addi s0,s0,8` meets the bound exactly at the end. -/
theorem cursor_step {arr : BitVec 64} {idx count : Nat} (h : arr.toNat + 8 * count ≤ 0x100000000)
    (hi : idx < count) :
    (arr + BitVec.ofNat 64 (8 * idx) + 8#64 = arr + BitVec.ofNat 64 (8 * count) ↔ idx + 1 = count) ∧
      arr + BitVec.ofNat 64 (8 * idx) + 8#64 = arr + BitVec.ofNat 64 (8 * (idx + 1)) := by
  have e : arr + BitVec.ofNat 64 (8 * idx) + 8#64 = arr + BitVec.ofNat 64 (8 * (idx + 1)) := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
  refine ⟨?_, e⟩
  rw [e]
  constructor
  · intro h'
    have := congrArg BitVec.toNat h'
    simp [BitVec.toNat_add] at this
    omega
  · intro h'; subst h'; rfl


theorem interpExit_normal : interpExit .normal = 0x80004514#64 := rfl
theorem interpExit_ret (v : Value) : interpExit (.ret v) = 0x80004540#64 := rfl
theorem interpExit_brk : interpExit .brk = 0x80004564#64 := rfl
theorem interpExit_cont : interpExit .cont = 0x80004564#64 := rfl

section Motive

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- **The `interp_run` loop, total mode**: the motive of `ExecSeqCost` at the
`interp_run` site. From the loop head with the program's statements `ss` (a
nonempty suffix of the array `all`, from index `idx`), in the global frame
`genv` (`in->globals = g`), the loop runs them against the derivation and
leaves at `interpExit status` with the `ret` slot `sp+88` as `statusRet` and
the registers `interpKeep` kept; the frame bytes are unchanged. -/
def interpSeqT_body (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (st : St) (d genv : Nat) (ss : List Vsa.While.Stmt) (st' : St) (status : Status)
    (n : Nat) (_D : ExecSeqCost st d genv ss st' status n) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (k idx count : Nat) (s arr g : BitVec 64)
    (R : Nat → BitVec 64) (Mt Dt m : Mem) (P : Nat → Prop) (all : List Vsa.While.Stmt) (m' : Nat)
    (F : IProp GF),
    ss ≠ [] → ss = all.drop idx → InterpData Dt m P arr count inp g all →
    InterpHead R s arr idx count → ExecFrameGeom s → InterpFrame Mt s inp →
    StackGeom (s + 18446744073709551440#64) m' →
    (∀ x ∈ all, execNeed x d ≤ m' ∧ x.bodiesBound perCallBudget = true) →
    SlotGeom (s + 18446744073709551440#64 + 88#64) →
    (F ∗ ms 0x8000448c#64 R (interpS s) Mt ∗ codeRes ∗ roOn P m ∗
      roOwn roR (interpText ++ dataOf Dt (interpView arr.toNat count inp)) ∗ □ frameAt genv g.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 (s + 18446744073709551440#64 + 88#64).toNat ∗ world N L Room inp (.counted (k + n)) st d ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs interpKeep R R'⌝ -∗ F -∗
        ms (interpExit status) R' (interpS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N (s + 18446744073709551440#64 + 88#64).toNat status -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)
      ⊢ (twpW (vsaModel live)).W Φ)

theorem interpSeqT_nil (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (st : St) (d genv : Nat) :
    interpSeqT_body (GF := GF) live N L Room inp st d genv [] st .normal 0 (.nil st d genv) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd rfl h

/-- **The `interp_run` loop, partial mode** (structural in the program's
statements, each through the Löb hypothesis; as `blockSeqP_body`). -/
def interpSeqP_body (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (Core : IProp GF) (d genv : Nat) (ss : List Vsa.While.Stmt) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (st : St) (idx count : Nat) (s arr g : BitVec 64)
    (R : Nat → BitVec 64) (Mt Dt m : Mem) (P : Nat → Prop) (all : List Vsa.While.Stmt) (m' : Nat)
    (F : IProp GF),
    ss ≠ [] → ss = all.drop idx → InterpData Dt m P arr count inp g all →
    InterpHead R s arr idx count → ExecFrameGeom s → InterpFrame Mt s inp →
    StackGeom (s + 18446744073709551440#64) m' →
    (∀ x ∈ all, execNeed x d ≤ m' ∧ x.bodiesBound perCallBudget = true) →
    SlotGeom (s + 18446744073709551440#64 + 88#64) →
    (F ∗ ms 0x8000448c#64 R (interpS s) Mt ∗ codeRes ∗ roOn P m ∗
      roOwn roR (interpText ++ dataOf Dt (interpView arr.toNat count inp)) ∗ □ frameAt genv g.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 (s + 18446744073709551440#64 + 88#64).toNat ∗ world N L Room inp .uncounted st d ∗
      execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (st' : St) (status : Status),
        ⌜ExecSeq st d genv ss st' status⌝ -∗ ⌜KeepRegs interpKeep R R'⌝ -∗ F -∗
        ms (interpExit status) R' (interpS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N (s + 18446744073709551440#64 + 88#64).toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗
          slot24 (s + 18446744073709551440#64 + 88#64).toNat ∗ ownSet (interpS s) byteAny) -∗
          (wpW (vsaModel live)).W Φ))
      ⊢ (wpW (vsaModel live)).W Φ)

theorem interpSeqP_nil (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (Core : IProp GF) (d genv : Nat) :
    interpSeqP_body (GF := GF) live N L Room inp Core d genv [] :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd rfl h

end Motive

/-! ## The cases -/

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr

#ix_piece interpSeqT_consNormal_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
    [I : InterpGS GF] {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d genv : Nat} {sm : Vsa.While.Stmt} {ss : List Vsa.While.Stmt} {st' st'' : St}
    {status : Status} {n1 n2 : Nat}
    (D1 : ExecSCost st d genv sm st' .normal n1) (D2 : ExecSeqCost st' d genv ss st'' status n2)
    (h1 : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st d genv sm st' .normal n1 D1)
    (h2 : interpSeqT_body (GF := GF) live N L Room inp st' d genv ss st'' status n2 D2)
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p) :
    interpSeqT_body (GF := GF) live N L Room inp st d genv (sm :: ss) st'' status (n1 + n2)
      (.consNormal st d genv sm ss st' st'' status n1 n2 D1 D2) by
  intro Φ k idx count s arr g R Mt Dt m P all m' F _ hdrop hdat hh hfg hfr hsg' hall hslg
  obtain ⟨hl, hat, hrest⟩ := drop_cons_facts hdrop
  have hcount : all.length = count := stmtArray_length hdat.repr
  obtain ⟨p, hp, hsp⟩ := stmtArray_get hdat.repr idx hl
  rw [hat] at hsp
  have hpl : p < 2 ^ 64 := readLE_lt hp
  have hpt : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hidx : idx < count := hcount ▸ hl
  have hel := hdat.elem hidx hp
  obtain ⟨hneed, hbb⟩ := hall sm (hat ▸ List.getElem_mem hl)
  iintro ⟨HF, Hms, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hslot, Hw, Hk⟩
  -- the head: the flag is clear, the statement pointer
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗
      roOwn roR (interpText ++ dataOf Dt (interpView arr.toNat count inp)) ∗ frameAt genv g.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 (s + 18446744073709551440#64 + 88#64).toNat ∗
      world N L Room inp (.counted (k + (n1 + n2))) st d ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs interpKeep R R'⌝ -∗ F -∗
        ms (interpExit status) R' (interpS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N (s + 18446744073709551440#64 + 88#64).toNat status -∗
        world N L Room inp (.counted k) st'' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hslot Hw; iexact Hk
  intro F'
  refine InterpLoop_runA (pS := BitVec.ofNat 64 p) (inp := inp) hlive hfg.sf hfg.lo hfg.hi hfg.al
    hdat.alo hdat.ahi hdat.aoff hidx hdat.small hh.cur hh.sp hfr.flag hel ?_
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- value_null into the result slot
  ihave Hvn := hvn $$ %(s + 18446744073709551440#64 + 88#64)
  unfold valueNullSpec
  iapply ms_callHelper (twpW _) (i := 0x8000445c)
    (jalx_8000445c live (fun p hp => hlive _ (interp_code_8000445c p hp)))
    interp_code_8000445c (by decide)
  iframe Hvn Hcode Hms
  isplitl []
  · ipureintro; ix_reg
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact hslg
  iintro %R1 %hkeep1 Hval Hms
  ihave Hslot := valAt_slot $$ Hval
  -- stage exec_stmt: the interpreter, the statement, the global frame, the slot
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗
      roOwn roR (interpText ++ dataOf Dt (interpView arr.toNat count inp)) ∗ frameAt genv g.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 (s + 18446744073709551440#64 + 88#64).toNat ∗
      world N L Room inp (.counted (k + (n1 + n2))) st d ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs interpKeep R R'⌝ -∗ F -∗
        ms (interpExit status) R' (interpS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N (s + 18446744073709551440#64 + 88#64).toNat status -∗
        world N L Room inp (.counted k) st'' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hslot Hw; iexact Hk
  intro F'
  have hsp1 : upd R1 1 (BitVec.ofNat 64 (2147501148 + 4)) 2 = s + 18446744073709551440#64 := by
    ix_reg; rw [keep_helper hkeep1 (by decide) (by decide)]; ix_reg; exact hh.sp
  refine InterpLoop_runH (arr := arr) (count := count) (g := g) hlive hfg.sf hfg.lo hfg.hi hfg.al
    hdat.ilo hdat.ihi hdat.ioff hsp1 hfr.inp hdat.glob ?_
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- the statement
  ihave H1 := h1
  rw [show k + (n1 + n2) = k + n2 + n1 by omega]
  iapply ms_callExecT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80004474)
    (jalx_80004474 live (fun p hp => hlive _ (interp_code_80004474 p hp)))
    interp_code_80004474 (by decide) D1 (k := k + n2) (aS := BitVec.ofNat 64 p) (aE := g)
    (aRet := s + 18446744073709551440#64 + 88#64) (s := s + 18446744073709551440#64) (m := m')
    (hsg'.narrow hneed) hneed hsg'.le hslg hbb
  iframe H1 Hcode Hfr Hms Hst Hslot Hw
  isplitl []
  · ipureintro
    exact ⟨by ix_reg, by ix_reg; rw [keep_helper hkeep1 (by decide) (by decide)]; ix_reg, by ix_reg,
      by ix_reg, by ix_reg; rw [keep_helper hkeep1 (by decide) (by decide)]; ix_reg; exact hh.sp⟩
  isplitl []
  · imodintro; rw [hpt]; unfold astSG; iexists P, m; iframe Hro; ipureintro; exact ⟨hsp, hdat.geo⟩
  iintro %R' %⟨hkeep, hst0⟩ Hms Hst Hret Hw
  rw [statusRet_normal]

#ix_piece interpSeqT_consNormal_p2 from interpSeqT_consNormal_p1 by
  -- the status routing and the back edge
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗
      roOwn roR (interpText ++ dataOf Dt (interpView arr.toNat count inp)) ∗ frameAt genv g.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 (s + 18446744073709551440#64 + 88#64).toNat ∗
      world N L Room inp (.counted (k + n2)) st' d ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs interpKeep R R'⌝ -∗ F -∗
        ms (interpExit status) R' (interpS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N (s + 18446744073709551440#64 + 88#64).toNat status -∗
        world N L Room inp (.counted k) st'' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hret Hw; iexact Hk
  intro F'
  have hR1 : KeepRegs interpKeep R (upd R' 1 (BitVec.ofNat 64 (2147501172 + 4))) := by
    keep_split
    all_goals ix_keep [hkeep, hkeep1]
  have e10 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 10 = 0#64 := by ix_reg; exact hst0
  have e19 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 19 = 3#64 := (hR1 19 (by decide)).trans hh.s3
  have e20 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 20 = 1#64 := (hR1 20 (by decide)).trans hh.s4
  have e18 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 18 = arr + BitVec.ofNat 64 (8 * count) :=
    (hR1 18 (by decide)).trans hh.bnd
  have e8 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 8 = arr + BitVec.ofNat 64 (8 * idx) := by
    ix_keep [hkeep, hkeep1]; exact hh.cur
  have e2 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 2 = s + 18446744073709551440#64 :=
    (hR1 2 (by decide)).trans hh.sp
  obtain ⟨hstep, hnext⟩ := cursor_step (arr := arr) hdat.ahi hidx
  have e18r : R' 18 = arr + BitVec.ofNat 64 (8 * count) := by simpa [upd_apply] using e18
  have e20r : R' 20 = 1#64 := by simpa [upd_apply] using e20
  refine InterpLoop_runB (sc := 0#64) (idx := idx) hlive e10 e19 e20 e8 e18 ?_ ?_ ?_ ?_
  · -- `ret`: not this derivation's
    intro hc; exfalso; rw [e10, e19] at hc; exact absurd hc (by decide)
  · -- `brk`/`cont`: not this derivation's
    intro _ hc; exfalso
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, e20r] at hc
    exact absurd hc (by decide)
  · -- the program's end: the loop leaves normally
    intro _ _ hc
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, e18r] at hc
    have hend := hstep.1 hc
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
      iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hret, Hw, Hk⟩, Hms⟩
      rw [statusRet_normal, interpExit_normal]
      iapply Hk $$ %_ %?_ HF Hms Hst Hret Hw
      refine KeepRegs.trans hR1 ?_
      keep_split
      all_goals ix_reg
  · -- more statements: the tail's loop
    intro _ _ hc
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, e18r] at hc
    have hmore : idx + 1 ≠ count := fun e => hc (hstep.2 e)
    intros
    apply swp_closeRM
    intro R2 Mt2 hR2 hMt2
    subst hMt2
    cases ss with
    | nil => exfalso; have := List.drop_eq_nil_iff.mp hrest.symm; omega
    | cons s2 ss2 =>
      refine .trans ?_ (h2 Φ k (idx + 1) count s arr g R2 Mt2 Dt m P all m' F
        (List.cons_ne_nil _ _) hrest hdat ?_ hfg hfr hsg' hall hslg)
      · unfold F'
        iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hret, Hw, Hk⟩, Hms⟩
        iframe HF Hms Hcode Hro Hdv Hfr Hst Hret Hw
        iintro %R'' %hk'' HF Hms Hst Hret Hw
        iapply Hk $$ %R'' %(KeepRegs.trans (KeepRegs.trans hR1 ?_) hk'') HF Hms Hst Hret Hw
        keep_split
        all_goals (rw [hR2]; ix_reg)
      · rw [hR2]
        exact ⟨by ix_reg; exact e2, by ix_reg; exact hnext, by ix_reg; exact e18,
          by ix_reg; exact e19, by ix_reg; exact e20⟩

#ix_chain interpSeqT_consNormal := [interpSeqT_consNormal_p1, interpSeqT_consNormal_p2]


#ix_piece interpSeqT_consAbrupt_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
    [I : InterpGS GF] {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d genv : Nat} {sm : Vsa.While.Stmt} {ss : List Vsa.While.Stmt} {st' : St}
    {status : Status} {n : Nat}
    (D1 : ExecSCost st d genv sm st' status n) (hne : status ≠ .normal)
    (h1 : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st d genv sm st' status n D1)
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p) :
    interpSeqT_body (GF := GF) live N L Room inp st d genv (sm :: ss) st' status n
      (.consAbrupt st d genv sm ss st' status n D1 hne) by
  intro Φ k idx count s arr g R Mt Dt m P all m' F _ hdrop hdat hh hfg hfr hsg' hall hslg
  obtain ⟨hl, hat, hrest⟩ := drop_cons_facts hdrop
  have hcount : all.length = count := stmtArray_length hdat.repr
  obtain ⟨p, hp, hsp⟩ := stmtArray_get hdat.repr idx hl
  rw [hat] at hsp
  have hpl : p < 2 ^ 64 := readLE_lt hp
  have hpt : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hidx : idx < count := hcount ▸ hl
  have hel := hdat.elem hidx hp
  obtain ⟨hneed, hbb⟩ := hall sm (hat ▸ List.getElem_mem hl)
  iintro ⟨HF, Hms, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hslot, Hw, Hk⟩
  -- the head: the flag is clear, the statement pointer
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗
      roOwn roR (interpText ++ dataOf Dt (interpView arr.toNat count inp)) ∗ frameAt genv g.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 (s + 18446744073709551440#64 + 88#64).toNat ∗
      world N L Room inp (.counted (k + n)) st d ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs interpKeep R R'⌝ -∗ F -∗
        ms (interpExit status) R' (interpS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N (s + 18446744073709551440#64 + 88#64).toNat status -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hslot Hw; iexact Hk
  intro F'
  refine InterpLoop_runA (pS := BitVec.ofNat 64 p) (inp := inp) hlive hfg.sf hfg.lo hfg.hi hfg.al
    hdat.alo hdat.ahi hdat.aoff hidx hdat.small hh.cur hh.sp hfr.flag hel ?_
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- value_null into the result slot
  ihave Hvn := hvn $$ %(s + 18446744073709551440#64 + 88#64)
  unfold valueNullSpec
  iapply ms_callHelper (twpW _) (i := 0x8000445c)
    (jalx_8000445c live (fun p hp => hlive _ (interp_code_8000445c p hp)))
    interp_code_8000445c (by decide)
  iframe Hvn Hcode Hms
  isplitl []
  · ipureintro; ix_reg
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact hslg
  iintro %R1 %hkeep1 Hval Hms
  ihave Hslot := valAt_slot $$ Hval
  -- stage exec_stmt: the interpreter, the statement, the global frame, the slot
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗
      roOwn roR (interpText ++ dataOf Dt (interpView arr.toNat count inp)) ∗ frameAt genv g.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 (s + 18446744073709551440#64 + 88#64).toNat ∗
      world N L Room inp (.counted (k + n)) st d ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs interpKeep R R'⌝ -∗ F -∗
        ms (interpExit status) R' (interpS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N (s + 18446744073709551440#64 + 88#64).toNat status -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hslot Hw; iexact Hk
  intro F'
  have hsp1 : upd R1 1 (BitVec.ofNat 64 (2147501148 + 4)) 2 = s + 18446744073709551440#64 := by
    ix_reg; rw [keep_helper hkeep1 (by decide) (by decide)]; ix_reg; exact hh.sp
  refine InterpLoop_runH (arr := arr) (count := count) (g := g) hlive hfg.sf hfg.lo hfg.hi hfg.al
    hdat.ilo hdat.ihi hdat.ioff hsp1 hfr.inp hdat.glob ?_
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- the statement
  ihave H1 := h1
  iapply ms_callExecT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80004474)
    (jalx_80004474 live (fun p hp => hlive _ (interp_code_80004474 p hp)))
    interp_code_80004474 (by decide) D1 (k := k) (aS := BitVec.ofNat 64 p) (aE := g)
    (aRet := s + 18446744073709551440#64 + 88#64) (s := s + 18446744073709551440#64) (m := m')
    (hsg'.narrow hneed) hneed hsg'.le hslg hbb
  iframe H1 Hcode Hfr Hms Hst Hslot Hw
  isplitl []
  · ipureintro
    exact ⟨by ix_reg, by ix_reg; rw [keep_helper hkeep1 (by decide) (by decide)]; ix_reg, by ix_reg,
      by ix_reg, by ix_reg; rw [keep_helper hkeep1 (by decide) (by decide)]; ix_reg; exact hh.sp⟩
  isplitl []
  · imodintro; rw [hpt]; unfold astSG; iexists P, m; iframe Hro; ipureintro; exact ⟨hsp, hdat.geo⟩
  iintro %R' %⟨hkeep, hst0⟩ Hms Hst Hret Hw


#ix_piece interpSeqT_consAbrupt_p2 from interpSeqT_consAbrupt_p1 by
  -- the status routing: an abrupt status leaves to its error
  iapply wp_swpF (twpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗
      roOwn roR (interpText ++ dataOf Dt (interpView arr.toNat count inp)) ∗ frameAt genv g.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗
      statusRet N (s + 18446744073709551440#64 + 88#64).toNat status ∗
      world N L Room inp (.counted k) st' d ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs interpKeep R R'⌝ -∗ F -∗
        ms (interpExit status) R' (interpS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N (s + 18446744073709551440#64 + 88#64).toNat status -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hret Hw; iexact Hk
  intro F'
  have hR1 : KeepRegs interpKeep R (upd R' 1 (BitVec.ofNat 64 (2147501172 + 4))) := by
    keep_split
    all_goals ix_keep [hkeep, hkeep1]
  have e10 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 10 = statusCode status := by ix_reg; exact hst0
  have e19 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 19 = 3#64 := (hR1 19 (by decide)).trans hh.s3
  have e20 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 20 = 1#64 := (hR1 20 (by decide)).trans hh.s4
  have e18 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 18 = arr + BitVec.ofNat 64 (8 * count) :=
    (hR1 18 (by decide)).trans hh.bnd
  have e8 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 8 = arr + BitVec.ofNat 64 (8 * idx) := by
    ix_keep [hkeep, hkeep1]; exact hh.cur
  have e20r : R' 20 = 1#64 := by simpa [upd_apply] using e20
  refine InterpLoop_runB (sc := statusCode status) (idx := idx) hlive e10 e19 e20 e8 e18 ?_ ?_ ?_ ?_
  · -- `ret`
    intro hc
    rw [e10, e19] at hc
    cases status with
    | ret v =>
      intros
      apply swp_closeF
      unfold F'
      iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hret, Hw, Hk⟩, Hms⟩
      rw [interpExit_ret]
      iapply Hk $$ %_ %hR1 HF Hms Hst Hret Hw
    | _ => exfalso; exact absurd hc (by decide)
  · -- `brk`/`cont`
    intro hc0 hc
    rw [e10, e19] at hc0
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, e20r] at hc
    cases status with
    | brk =>
      intros
      apply swp_closeF
      unfold F'
      iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hret, Hw, Hk⟩, Hms⟩
      rw [interpExit_brk]
      iapply Hk $$ %_ %?_ HF Hms Hst Hret Hw
      refine KeepRegs.trans hR1 ?_
      keep_split
      all_goals ix_reg
    | cont =>
      intros
      apply swp_closeF
      unfold F'
      iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hret, Hw, Hk⟩, Hms⟩
      rw [interpExit_cont]
      iapply Hk $$ %_ %?_ HF Hms Hst Hret Hw
      refine KeepRegs.trans hR1 ?_
      keep_split
      all_goals ix_reg
    | ret v => exact absurd rfl hc0
    | normal => exact absurd rfl hne
  · intro hc0 hc _
    exfalso
    rw [e10, e19] at hc0
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, e20r] at hc
    cases status <;> first | exact absurd rfl hne | exact absurd rfl hc0 | exact hc (by decide)
  · intro hc0 hc _
    exfalso
    rw [e10, e19] at hc0
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, e20r] at hc
    cases status <;> first | exact absurd rfl hne | exact absurd rfl hc0 | exact hc (by decide)

#ix_chain interpSeqT_consAbrupt := [interpSeqT_consAbrupt_p1, interpSeqT_consAbrupt_p2]


#ix_piece interpSeqP_cons_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
    [I : InterpGS GF] {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {d genv : Nat} {sm : Vsa.While.Stmt} {ss : List Vsa.While.Stmt}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p)
    (ih : interpSeqP_body (GF := GF) live N L Room inp Core d genv ss) :
    interpSeqP_body (GF := GF) live N L Room inp Core d genv (sm :: ss) by
  intro Φ st idx count s arr g R Mt Dt m P all m' F _ hdrop hdat hh hfg hfr hsg' hall hslg
  obtain ⟨hl, hat, hrest⟩ := drop_cons_facts hdrop
  have hcount : all.length = count := stmtArray_length hdat.repr
  obtain ⟨p, hp, hsp⟩ := stmtArray_get hdat.repr idx hl
  rw [hat] at hsp
  have hpl : p < 2 ^ 64 := readLE_lt hp
  have hpt : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hidx : idx < count := hcount ▸ hl
  have hel := hdat.elem hidx hp
  obtain ⟨hneed, hbb⟩ := hall sm (hat ▸ List.getElem_mem hl)
  iintro ⟨HF, Hms, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hslot, Hw, #IH, HK⟩
  iapply wp_swpF (wpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗
      roOwn roR (interpText ++ dataOf Dt (interpView arr.toNat count inp)) ∗ frameAt genv g.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 (s + 18446744073709551440#64 + 88#64).toNat ∗ world N L Room inp .uncounted st d ∗
      execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (st' : St) (status : Status),
        ⌜ExecSeq st d genv (sm :: ss) st' status⌝ -∗ ⌜KeepRegs interpKeep R R'⌝ -∗ F -∗
        ms (interpExit status) R' (interpS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N (s + 18446744073709551440#64 + 88#64).toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗
          slot24 (s + 18446744073709551440#64 + 88#64).toNat ∗ ownSet (interpS s) byteAny) -∗
          (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hslot Hw IH; iexact HK
  intro F'
  refine InterpLoop_runA (pS := BitVec.ofNat 64 p) (inp := inp) hlive hfg.sf hfg.lo hfg.hi hfg.al
    hdat.alo hdat.ahi hdat.aoff hidx hdat.small hh.cur hh.sp hfr.flag hel ?_
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hslot, Hw, #IH, HK⟩, Hms⟩
  ihave Hvn := hvn $$ %(s + 18446744073709551440#64 + 88#64)
  unfold valueNullSpec
  iapply ms_callHelper (wpW _) (i := 0x8000445c)
    (jalx_8000445c live (fun p hp => hlive _ (interp_code_8000445c p hp)))
    interp_code_8000445c (by decide)
  iframe Hvn Hcode Hms
  isplitl []
  · ipureintro; ix_reg
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact hslg
  iintro %R1 %hkeep1 Hval Hms
  ihave Hslot := valAt_slot $$ Hval
  iapply wp_swpF (wpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗
      roOwn roR (interpText ++ dataOf Dt (interpView arr.toNat count inp)) ∗ frameAt genv g.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 (s + 18446744073709551440#64 + 88#64).toNat ∗ world N L Room inp .uncounted st d ∗
      execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (st' : St) (status : Status),
        ⌜ExecSeq st d genv (sm :: ss) st' status⌝ -∗ ⌜KeepRegs interpKeep R R'⌝ -∗ F -∗
        ms (interpExit status) R' (interpS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N (s + 18446744073709551440#64 + 88#64).toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗
          slot24 (s + 18446744073709551440#64 + 88#64).toNat ∗ ownSet (interpS s) byteAny) -∗
          (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hslot Hw IH; iexact HK
  intro F'
  have hsp1 : upd R1 1 (BitVec.ofNat 64 (2147501148 + 4)) 2 = s + 18446744073709551440#64 := by
    ix_reg; rw [keep_helper hkeep1 (by decide) (by decide)]; ix_reg; exact hh.sp
  refine InterpLoop_runH (arr := arr) (count := count) (g := g) hlive hfg.sf hfg.lo hfg.hi hfg.al
    hdat.ilo hdat.ihi hdat.ioff hsp1 hfr.inp hdat.glob ?_
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hslot, Hw, #IH, HK⟩, Hms⟩
  ihave H1 := execSpecsP_at Core st d genv sm $$ IH
  iapply ms_callExecP (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80004474)
    (jalx_80004474 live (fun p hp => hlive _ (interp_code_80004474 p hp)))
    interp_code_80004474 (by decide) (Core := Core) (st := st) (d := d) (env := genv) (sm := sm)
    (aS := BitVec.ofNat 64 p) (aE := g)
    (aRet := s + 18446744073709551440#64 + 88#64) (s := s + 18446744073709551440#64) (m := m')
    (Kret := iprop(∀ (R' : Nat → BitVec 64) (st' : St) (status : Status),
        ⌜ExecSeq st d genv (sm :: ss) st' status⌝ -∗ ⌜KeepRegs interpKeep R R'⌝ -∗ F -∗
        ms (interpExit status) R' (interpS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N (s + 18446744073709551440#64 + 88#64).toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ))
    (hsg'.narrow hneed) hneed hsg'.le hslg hbb
  iframe H1 Hcode Hfr Hms Hst Hslot Hw HK
  isplitl []
  · ipureintro
    exact ⟨by ix_reg, by ix_reg; rw [keep_helper hkeep1 (by decide) (by decide)]; ix_reg, by ix_reg,
      by ix_reg, by ix_reg; rw [keep_helper hkeep1 (by decide) (by decide)]; ix_reg; exact hh.sp⟩
  isplitl []
  · imodintro; rw [hpt]; unfold astSG; iexists P, m; iframe Hro; ipureintro; exact ⟨hsp, hdat.geo⟩
  iintro %R' %st' %status %hE %⟨hkeep, hst0⟩ Hms Hst Hret Hw HK


#ix_piece interpSeqP_cons_p2 from interpSeqP_cons_p1 by
  iapply wp_swpF (wpW _) (F := iprop(F ∗ codeRes ∗ roOn P m ∗
      roOwn roR (interpText ++ dataOf Dt (interpView arr.toNat count inp)) ∗ frameAt genv g.toNat ∗
      stackScratch (s + 18446744073709551440#64) m' ∗
      statusRet N (s + 18446744073709551440#64 + 88#64).toNat status ∗
      world N L Room inp .uncounted st' d ∗ execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (st'' : St) (status' : Status),
        ⌜ExecSeq st d genv (sm :: ss) st'' status'⌝ -∗ ⌜KeepRegs interpKeep R R'⌝ -∗ F -∗
        ms (interpExit status') R' (interpS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N (s + 18446744073709551440#64 + 88#64).toNat status' -∗
        world N L Room inp .uncounted st'' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗
          slot24 (s + 18446744073709551440#64 + 88#64).toNat ∗ ownSet (interpS s) byteAny) -∗
          (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms HF Hcode Hro Hfr Hst Hret Hw IH; iexact HK
  intro F'
  have hR1 : KeepRegs interpKeep R (upd R' 1 (BitVec.ofNat 64 (2147501172 + 4))) := by
    keep_split
    all_goals ix_keep [hkeep, hkeep1]
  have e10 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 10 = statusCode status := by ix_reg; exact hst0
  have e19 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 19 = 3#64 := (hR1 19 (by decide)).trans hh.s3
  have e20 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 20 = 1#64 := (hR1 20 (by decide)).trans hh.s4
  have e18 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 18 = arr + BitVec.ofNat 64 (8 * count) :=
    (hR1 18 (by decide)).trans hh.bnd
  have e8 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 8 = arr + BitVec.ofNat 64 (8 * idx) := by
    ix_keep [hkeep, hkeep1]; exact hh.cur
  have e2 : upd R' 1 (BitVec.ofNat 64 (2147501172 + 4)) 2 = s + 18446744073709551440#64 :=
    (hR1 2 (by decide)).trans hh.sp
  have e18r : R' 18 = arr + BitVec.ofNat 64 (8 * count) := by simpa [upd_apply] using e18
  have e20r : R' 20 = 1#64 := by simpa [upd_apply] using e20
  obtain ⟨hstep, hnext⟩ := cursor_step (arr := arr) hdat.ahi hidx
  refine InterpLoop_runB (sc := statusCode status) (idx := idx) hlive e10 e19 e20 e8 e18 ?_ ?_ ?_ ?_
  · -- `ret`: the loop leaves with it
    intro hc
    rw [e10, e19] at hc
    have hne : status ≠ .normal := by intro e; subst e; exact absurd hc (by decide)
    intros
    apply swp_closeF
    unfold F'
    iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hret, Hw, #IH, HK⟩, Hms⟩
    ihave HK := and_elim_l $$ HK
    cases status with
    | ret v =>
      rw [← interpExit_ret v] at *
      iapply HK $$ %_ %st' %(Status.ret v) %(ExecSeq.consAbrupt _ _ _ _ _ _ _ hE hne) %hR1 HF Hms Hst Hret Hw
    | _ => exfalso; exact absurd hc (by decide)
  · -- `brk`/`cont`: the loop leaves with it
    intro hc0 hc
    rw [e10, e19] at hc0
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, e20r] at hc
    have hne : status ≠ .normal := by intro e; subst e; exact absurd hc (by decide)
    intros
    apply swp_closeF
    unfold F'
    iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hret, Hw, #IH, HK⟩, Hms⟩
    ihave HK := and_elim_l $$ HK
    have hR1' : KeepRegs interpKeep R (upd (upd R' 1 (BitVec.ofNat 64 (2147501172 + 4))) 10
        (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (statusCode status + 18446744073709551615#64)))) := by
      refine KeepRegs.trans hR1 ?_
      keep_split
      all_goals ix_reg
    cases status with
    | brk =>
      rw [← interpExit_brk] at *
      iapply HK $$ %_ %st' %Status.brk %(ExecSeq.consAbrupt _ _ _ _ _ _ _ hE hne) %hR1' HF Hms Hst Hret Hw
    | cont =>
      rw [← interpExit_cont] at *
      iapply HK $$ %_ %st' %Status.cont %(ExecSeq.consAbrupt _ _ _ _ _ _ _ hE hne) %hR1' HF Hms Hst Hret Hw
    | ret v => exact absurd rfl hc0
    | normal => exact absurd rfl hne
  · -- the program's end
    intro hc0 hc hend
    rw [e10, e19] at hc0
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, e20r, e18r] at hc hend
    have hn : status = .normal := by
      cases status <;> first | rfl | exact absurd rfl hc0 | exact absurd (by decide) hc
    subst hn
    have hlast := hstep.1 hend
    intros
    apply swp_closeF
    cases ss with
    | cons s2 ss2 =>
      exfalso
      obtain ⟨hl2, -, -⟩ := drop_cons_facts hrest
      omega
    | nil =>
      unfold F'
      iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hret, Hw, #IH, HK⟩, Hms⟩
      ihave HK := and_elim_l $$ HK
      rw [← interpExit_normal] at *
      iapply HK $$ %_ %st' %Status.normal
        %(ExecSeq.consNormal _ _ _ _ _ _ _ _ hE (ExecSeq.nil _ _ _)) %?_ HF Hms Hst Hret Hw
      refine KeepRegs.trans hR1 ?_
      keep_split
      all_goals ix_reg
  · -- more statements: the tail's loop
    intro hc0 hc hend
    rw [e10, e19] at hc0
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, e20r, e18r] at hc hend
    have hn : status = .normal := by
      cases status <;> first | rfl | exact absurd rfl hc0 | exact absurd (by decide) hc
    subst hn
    have hmore : idx + 1 ≠ count := fun e => hend (hstep.2 e)
    intros
    apply swp_closeRM
    intro R2 Mt2 hR2 hMt2
    subst hMt2
    cases ss with
    | nil => exfalso; have := List.drop_eq_nil_iff.mp hrest.symm; omega
    | cons s2 ss2 =>
      refine .trans ?_ (ih Φ st' (idx + 1) count s arr g R2 Mt2 Dt m P all m' F
        (List.cons_ne_nil _ _) hrest hdat ?_ hfg hfr hsg' hall hslg)
      · unfold F'
        iintro ⟨⟨HF, #Hcode, #Hro, #Hdv, #Hfr, Hst, Hret, Hw, #IH, HK⟩, Hms⟩
        rw [statusRet_normal]
        iframe HF Hms Hcode Hro Hdv Hfr Hst Hret Hw IH
        have hR2' : KeepRegs interpKeep R R2 := by
          refine KeepRegs.trans hR1 ?_
          keep_split
          all_goals (rw [hR2]; ix_reg)
        isplit
        · iintro %R'' %st'' %status'' %hE2 %hk'' HF Hms Hst Hret Hw
          ihave HK := and_elim_l $$ HK
          iapply HK $$ %R'' %st'' %status'' %(ExecSeq.consNormal _ _ _ _ _ _ _ _ hE hE2)
            %(KeepRegs.trans hR2' hk'') HF Hms Hst Hret Hw
        · ihave HK := and_elim_r $$ HK
          iexact HK
      · rw [hR2]
        exact ⟨by ix_reg; exact e2, by ix_reg; exact hnext, by ix_reg; exact e18,
          by ix_reg; exact e19, by ix_reg; exact e20⟩

#ix_chain interpSeqP_cons := [interpSeqP_cons_p1, interpSeqP_cons_p2]

/-- **The `interp_run` loop, partial mode, for every program.** -/
theorem interpSeqP_all {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
    [I : InterpGS GF] {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p)
    (L : DlLayout) (Room : RoomPred) (inp : Nat) (Core : IProp GF) (d genv : Nat) :
    ∀ ss, interpSeqP_body (GF := GF) live N L Room inp Core d genv ss
  | [] => interpSeqP_nil live N L Room inp Core d genv
  | _ :: ss => interpSeqP_cons hlive hvn (interpSeqP_all hlive hvn L Room inp Core d genv ss)

end VsaIris.Interp
