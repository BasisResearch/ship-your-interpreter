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

end Motive

end VsaIris.Interp
