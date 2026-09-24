import VsaIris.Interp.ExecArm
import VsaIris.Interp.SpecLoop
import VsaIris.Interp.ExecEnv

/-!
# `exec_stmt`'s `while` and `for` arms: dispatch to the loop head, exits (lane E5)

The loops are E6's (`SpecLoop.lean`: `whileT_body`/`whileP_body` at
`0x8000403c`, `execInitT_body` at `0x8000423c`, `forLoopT_body` at
`0x8000426c`). The arms: the kind dispatch to the loop head (the jump table
lands the `while` tag on its head), the for arm's `env_new`, and the exits
`loopExit status` (`wp_loopExit`: the shared exit or the `ret` epilogue).
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

/-- A `while` statement node: its tag. -/
theorem whileNode_of {m : Mem} {P : Nat → Prop} {aS : BitVec 64} {c : Vsa.While.Expr}
    {b : Vsa.While.Stmt} (h : StmtReprWithin m P aS.toNat (.whileStmt c b))
    (hg : ∀ k, P k → Interp.ReadOK k) : StmtNode m P aS 4 4 := by
  cases h with
  | whileS h4 c4 _ _ _ _ _ _ => exact stmtNode_of hg h4 c4 (by decide) (Or.inl rfl) (fun j h1 h2 => by omega)

#ix_seg WhileArm_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 4 ≤ 0x100000000)
    (hx3 : aS.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (hk : ldv .lw m aS.toNat = 4#64) (hku : ldv .lwu m aS.toNat = 4#64) :
    IW live m (stmtView aS.toNat 4) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by rw [← upd_eq_self h16]
     ix_run hlive using [h8, h14, hk, hku] at 0x8000403c

section Exit

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- **A loop's exit**, for either WP: at `loopExit status` (E6) with the
status in `a0`, the frame outside the loops' scratch words unchanged (so the
spills hold), the arm returns through the shared exit or the `ret` epilogue. -/
theorem wp_loopExit (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {ρ : Regime} {st' : St} {d : Nat} {sm : Stmt} {status : Status}
    {aRet s ret v8 v9 v18 v19 : BitVec 64} {R0 R1 R' : Nat → BitVec 64} {Mt Mt' : Mem}
    (hsg : StackGeom s (execNeed sm d)) (hal : ret.toNat % 4 = 0)
    (h2 : R1 2 = execSP s) (hk1 : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R0 R1)
    (hsv : ExecSaved Mt s ret v8 v9 v18 v19)
    (hk : KeepRegs calleeSaved R1 R') (h10 : R' 10 = statusCode status)
    (hu : Untouched (execS s) (execW s) Mt Mt') :
    codeRes ∗ ms (loopExit status) R' (InExt (s.toNat - 176, 176)) Mt' ∗
      stackScratch (execSP s) (execNeed sm d - 176) ∗
      statusRet N aRet.toNat status ∗ world N L Room inp ρ st' d ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st' d sm status aRet s R0 ret v8 v9 v18 v19
    ⊢ Wp.W Φ := by
  obtain ⟨hfg, _⟩ := execFrameGeom_of hsg
  have hsv' : ExecSaved Mt' s ret v8 v9 v18 v19 := by
    have := hfg.lo
    exact hsv.congrHi (fun x h1 h2 => hu x (by simp only [execS, InExt]; omega)
      (by simp only [execW, InExt]; omega)) (by omega)
  have h2' : R' 2 = execSP s := (hk 2 (by decide)).trans h2
  have hsub : ∀ x ∈ [20, 21, 22, 23, 24, 25, 26, 27], x ∈ calleeSaved := by decide
  have hk' : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R0 R' :=
    fun x hx => (hk x (hsub x hx)).trans (hk1 x hx)
  cases status with
  | ret v =>
    exact wp_execEpiRet hlive Wp hsg hal h2' hsv' hk'
  | normal => exact wp_execEpi hlive Wp hsg hal h2' h10 hsv' hk'
  | brk => exact wp_execEpi hlive Wp hsg hal h2' h10 hsv' hk'
  | cont => exact wp_execEpi hlive Wp hsg hal h2' h10 hsv' hk'

end Exit

/-- The stack below the lowered `sp`, as the loops state it. -/
theorem StackGeom.lower {s : BitVec 64} {n : Nat} (h : StackGeom s n) (hn : 176 ≤ n)
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176) :
    StackGeom (s + 18446744073709551440#64) (n - 176) := by
  have h1 := h.le; have h2 := h.lo; have h3 := h.hi; have h4 := h.al
  simp only [Vsa.Sim.LayoutInstance.stackSL] at h2 h3
  refine ⟨by rw [hsf]; omega, ?_, ?_, ?_⟩ <;> rw [hsf] <;>
    (try simp only [Vsa.Sim.LayoutInstance.stackSL]) <;> omega

/-- What the `while` loop needs of the arm's lowered stack. -/
theorem whileFits_of {c : Vsa.While.Expr} {b : Vsa.While.Stmt} {d : Nat}
    (hbb : (Vsa.While.Stmt.whileStmt c b).bodiesBound Vsa.While.perCallBudget = true) :
    WhileFits d c b (execNeed (.whileStmt c b) d - 176) := by
  simp only [Vsa.While.Stmt.bodiesBound, Bool.and_eq_true] at hbb
  have h1 := execNeed_while_cond c b d; have h2 := execNeed_while_body c b d
  unfold Vsa.While.execFrame at h1 h2
  exact ⟨by omega, hbb.1, by omega, hbb.2⟩

/-- The loop head's registers after the dispatch run. -/
theorem stmtHead_of_disp {R R1 : Nat → BitVec 64} {inp aS aE aRet s : BitVec 64}
    (hd : DispRegs R inp aS aE aRet s) (h2 : R1 2 = R 2) (h8 : R1 8 = R 8) (h9 : R1 9 = R 9)
    (h18 : R1 18 = R 18) (h19 : R1 19 = R 19) : StmtHead R1 s aS inp aRet aE :=
  ⟨h2.trans hd.sp, h8.trans hd.s0, h9.trans hd.s1, h18.trans hd.s2, h19.trans hd.s3⟩

/-- A `for` statement node: its tag. -/
theorem forNode_of {m : Mem} {P : Nat → Prop} {aS : BitVec 64} {i : Option Vsa.While.Stmt}
    {c st : Option Vsa.While.Expr} {b : Vsa.While.Stmt}
    (h : StmtReprWithin m P aS.toNat (.forStmt i c st b))
    (hg : ∀ k, P k → Interp.ReadOK k) : StmtNode m P aS 5 4 := by
  cases h with
  | forS h5 c5 _ _ _ _ _ _ => exact stmtNode_of hg h5 c5 (by decide) (Or.inl rfl) (fun j h1 h2 => by omega)

#ix_seg ForArm_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 4 ≤ 0x100000000)
    (hx3 : aS.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (hk : ldv .lw m aS.toNat = 5#64) (hku : ldv .lwu m aS.toNat = 5#64) :
    IW live m (stmtView aS.toNat 4) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by rw [← upd_eq_self h16]
     ix_run hlive using [h8, h14, hk, hku] at 0x80004238

/-- What the `for` loop and its init need of the arm's lowered stack. -/
theorem forFits_of {i : Option Vsa.While.Stmt} {c st : Option Vsa.While.Expr} {b : Vsa.While.Stmt}
    {d : Nat} (hbb : (Vsa.While.Stmt.forStmt i c st b).bodiesBound Vsa.While.perCallBudget = true) :
    ForFits d c st b (execNeed (.forStmt i c st b) d - 176) ∧
      (∀ x, i = some x → execNeed x d ≤ execNeed (.forStmt i c st b) d - 176 ∧
        x.bodiesBound Vsa.While.perCallBudget = true) := by
  simp only [Vsa.While.Stmt.bodiesBound, Bool.and_eq_true] at hbb
  obtain ⟨⟨⟨hi, hc⟩, hs⟩, hb⟩ := hbb
  refine ⟨⟨fun x hx => ⟨?_, ?_⟩, fun x hx => ⟨?_, ?_⟩, ?_, hb⟩, fun x hx => ⟨?_, ?_⟩⟩
  · have := execNeed_for_cond hx i st b d; unfold Vsa.While.execFrame at this; omega
  · subst hx; simpa [Vsa.While.Expr.bodiesBoundOpt] using hc
  · have := execNeed_for_step hx i c b d; unfold Vsa.While.execFrame at this; omega
  · subst hx; simpa [Vsa.While.Expr.bodiesBoundOpt] using hs
  · have := execNeed_for_body i c st b d; unfold Vsa.While.execFrame at this; omega
  · have := execNeed_for_init hx c st b d; unfold Vsa.While.execFrame at this; omega
  · subst hx; simpa [Vsa.While.Stmt.bodiesBoundOpt] using hi

end VsaIris.Interp
