import Vsa.Sim.SeqSuffixGround

namespace Vsa.Sim

open LeanRV64DExecutable
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

private theorem stmtArrayRepr_count {m : Mem} {a n : Nat} {ss : List Stmt}
    (h : StmtArrayRepr m a n ss) : n = ss.length := by
  induction ss generalizing a n with
  | nil => cases h; rfl
  | cons s ss ih =>
      cases h with
      | cons _ _ htail => simpa using congrArg Nat.succ (ih htail)

/-- A nonempty hereditary statement array occupies its exact contiguous
pointer range. The empty array has no address or alignment obligation. -/
theorem stmtsIn_range {m : Mem} {lo hi a : Nat} {ss : List Stmt}
    (h : StmtsIn m lo hi a ss) (hne : ss ≠ []) :
    lo ≤ a ∧ a + 8 * ss.length ≤ hi := by
  induction ss generalizing a with
  | nil => exact False.elim (hne rfl)
  | cons s ss ih =>
      obtain ⟨hcell, _, htail⟩ := h
      refine ⟨hcell.lo_le, ?_⟩
      cases hs : ss with
      | nil => simpa [hs] using hcell.hi_ge
      | cons t ts =>
          have hrange := ih htail (by rw [hs]; intro he; cases he)
          rw [hs] at hrange
          simp only [List.length_cons] at *
          omega

/-- Construct every child ground bundle from one parent's hereditary region.
The array reads determine each child; no per-tail geometry oracle is used. -/
theorem SeqSuffixGround.of_parent_array
    {m : Mem} {SL : StackLayout} {A : Arena} {sp sp' aRet : BitVec 64}
    {d aParent a n : Nat} {parent : Stmt} {ss : List Stmt}
    (hparent : ExecGround m SL A sp aRet aParent parent)
    (hsp : sp'.toNat ≤ sp.toNat)
    (harray : StmtArrayRepr m a n ss) :
    (∀ lo hi, StmtIn m lo hi aParent parent → StmtsIn m lo hi a ss) →
    StackOK SL sp' (Stmt.stackNeedList ss + (maxCallDepth - d) * perCallBudget + 1088) →
    Stmt.bodiesBoundList perCallBudget ss = true →
    SeqSuffixGround m SL A sp' aRet d a ss := by
  induction ss generalizing a n with
  | nil =>
      intro _ _ _
      exact .nil
  | cons s ss ih =>
    cases harray with
    | @cons _ p _ _ _ hread hrepr htail =>
      intro hproj hbudget hbodies
      have hb : Stmt.bodiesBound perCallBudget s = true ∧
          Stmt.bodiesBoundList perCallBudget ss = true := by
        simpa only [Stmt.bodiesBoundList, Bool.and_eq_true] using hbodies
      have hheadBudget : StackOK SL sp'
          (s.stackNeed + (maxCallDepth - d) * perCallBudget + 1088) :=
        StackOK.mono (by
          simpa only [Stmt.stackNeedList] using
            Nat.add_le_add_right (Nat.add_le_add_right
              (Nat.le_max_left s.stackNeed (Stmt.stackNeedList ss)) _) _) hbudget
      have htailBudget : StackOK SL sp'
          (Stmt.stackNeedList ss + (maxCallDepth - d) * perCallBudget + 1088) :=
        StackOK.mono (by
          simpa only [Stmt.stackNeedList] using
            Nat.add_le_add_right (Nat.add_le_add_right
              (Nat.le_max_right s.stackNeed (Stmt.stackNeedList ss)) _) _) hbudget
      refine .cons hread
        { stmt := hrepr
          ground := hparent.child_sameRet
            (fun lo hi hin => (hproj lo hi hin).2.1 p hread) hsp
          stackBudget := hheadBudget
          bodies := hb.1 } ?_
      exact ih htail (fun lo hi hin => (hproj lo hi hin).2.2) htailBudget hb.2

/-- The parent's AST separation protects its pointer array across a child.
This also applies to arrays projected from closure bodies. -/
theorem seqArrayReadSafe_of_region
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet : BitVec 64}
    {aParent a lo hi : Nat} {parent : Stmt} {ss : List Stmt}
    (hspec : StmtRegionSpec m SL A aRet.toNat aParent parent lo hi)
    (harray : StmtsIn m lo hi a ss) (hsp : sp.toNat ≤ SL.hi) :
    SeqArrayReadSafe SL A sp aRet a ss.length := by
  intro k hk
  cases ss with
  | nil =>
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hk
      omega
  | cons s ss =>
      have hrange := stmtsIn_range harray (by intro he; cases he)
      have hlo : lo ≤ k := Nat.le_trans hrange.1 hk.1
      have hhi : k < hi := Nat.lt_of_lt_of_le hk.2 hrange.2
      refine ⟨?_, ?_, ?_⟩
      · intro hstack
        rcases hspec.stack_disjoint with hd | hd <;> omega
      · intro hArena
        rcases hspec.arena_disjoint with hd | hd <;> omega
      · intro hret
        rcases hspec.ret_disjoint with hd | hd <;> omega

/-- A parent block's actual header reads select the whole initial suffix.
The signed count bound follows from the represented array fitting in RAM. -/
theorem ExecGround.blockSuffix
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet : BitVec 64}
    {d aBlock : Nat} {ss : List Stmt}
    (hparent : ExecGround m SL A sp aRet aBlock (.block ss))
    (hstmt : StmtRepr m aBlock (.block ss))
    (hbudget : StackOK SL sp
      ((Stmt.block ss).stackNeed + (maxCallDepth - d) * perCallBudget + 1088))
    (hbodies : Stmt.bodiesBound perCallBudget (.block ss) = true) :
    ∃ base, read64 m (aBlock + 8) = some base ∧
      read32 m (aBlock + 16) = some ss.length ∧ ss.length < 2^31 ∧
      SeqSuffixGround m SL A (sp - 176#64) aRet d base ss ∧
      SeqArrayReadSafe SL A (sp - 176#64) aRet base ss.length := by
  have hchildBudget : StackOK SL (sp - 176#64)
      (Stmt.stackNeedList ss + (maxCallDepth - d) * perCallBudget + 1088) :=
    StackOK.child (by decide) (by
      simp only [Stmt.stackNeed, execFrame, BitVec.toNat_ofNat]
      omega) hbudget
  have hsp176 : 176 ≤ sp.toNat := by
    have hh := hbudget.1
    simp only [Stmt.stackNeed, execFrame] at hh
    omega
  have hchildLe : (sp - 176#64).toNat ≤ sp.toNat := by
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]
      exact hsp176)]
    exact Nat.sub_le _ _
  cases hstmt with
  | block _ hbase hcount harray =>
      have hlen := stmtArrayRepr_count harray
      have hproj (lo hi : Nat) (hin : StmtIn m lo hi aBlock (.block ss)) :=
        hin.2 _ hbase
      have hsuffix := SeqSuffixGround.of_parent_array hparent hchildLe harray
        hproj hchildBudget hbodies
      obtain ⟨lo, hi, hspec⟩ := hparent.ast.region
      have hnodes := hproj lo hi hspec.nodes
      have hcountBound : ss.length < 2^31 := by
        cases ss with
        | nil => decide
        | cons s ss =>
            have hrange := stmtsIn_range hnodes (by intro he; cases he)
            have hhi := hspec.hi_ram
            omega
      exact ⟨_, hbase, by simpa only [hlen] using hcount, hcountBound, hsuffix,
        seqArrayReadSafe_of_region hspec hnodes hchildBudget.2.1⟩

#print axioms SeqSuffixGround.of_parent_array
#print axioms ExecGround.blockSuffix

end Vsa.Sim
