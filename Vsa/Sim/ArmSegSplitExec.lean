import Vsa.Sim.ExecRecCommon
import Vsa.Sim.ExecEntry
import Vsa.Sim.StepCount

/-!
# `ArmSegSplitExec` — the `jal exec_stmt`→child-`ExecEntry` marshalling twin (Task #76, Half A.1)

`ArmSegSplit.evalEntry_of_jalPrefix` is the shared jal→child-`EvalEntry` marshalling
fact for the recursive `jal eval_expr` seam.  This file is its **exec_stmt twin**:
`execEntry_of_jalPrefix` — from an arm state at a recursive `jal exec_stmt` PC with
the child statement's ABI arguments staged (`a0 = aInterp`, `a1 = aStmt`,
`a2 = aEnv`, `a3 = aRet`, `sp` lowered), one `jal` step lands at the child's rich
`ExecEntry`.  It is `armTail_rec_es` (`ExecRecCommon.lean`) truncated *before* its IH
application, exactly as `evalEntry_of_jalPrefix` truncates `armTail_rec` — except the
landed post is `ExecEntry` (a child STATEMENT sub-call) rather than `EvalEntry`.

## What the jal step supplies vs. what must be premises (the exec-side audit)

`ExecEntry` (`Vsa/Sim/ExecEntry.lean`) mirrors `EvalEntry` with statement-specific
differences that shape the premise bundle:

* **Supplied by the jal step** (via `sigmaPost_jal`): `good`, `tick`, `pc`
  (= `execStmtEntry`, via `hjaltgt`), `a0`/`a1`/`a2`/`a3` (the four staged args —
  note `a3` is the RETSLOT, absent on the eval side), `ra` (= link `retPC`),
  `spReg` (= lowered `sp - hdrm`), `minstret`, `mem` (= `mcall`), `out`, `frame`,
  `spill_defined` (FOUR spills: s0/s1/s2/s3, not three).
* **Must be premises of the arm-head bundle**: the child-frame GEOMETRY at the
  lowered `sp` — `stackOK` for the lowered sp with `176 + 1088` headroom (statement
  frame + one eval frame), the child `Stmt` node's `StmtRepr`/alignment/RAM/
  disjointness at `aStmt`, `StoreRepr` + its survival clause (NO sret carve-out —
  `ExecEntry.store_survives` frames only `[SL.lo, sp)`), and the `exec_stmt`
  code-region disjointness re-checked against the lowered `sp`.

So `execEntry_of_jalPrefix` is the ONE reusable exec-side seam; the statement-arm
classes whose recursion goes into a child STATEMENT (`stmtIfThen`/`stmtIfElse`/
`stmtWhileBody`/`stmtForInit`/`flBody`) instantiate it after their own arm-head
staging span establishes the bundle.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- **The exec-side jal→child-`ExecEntry` marshalling fact.**

From an arm config `c` at the recursive `jal exec_stmt` PC `callPC`, with the child
statement's ABI arguments staged (`a0 = aInterp`, `a1 = aStmt`, `a2 = aEnv`,
`a3 = aRet`, `sp` lowered to `sp - hdrm`), one `jal` step reaches a config
satisfying the child's `ExecEntry` at node `s`, sub-frame `sp - hdrm`, link `retPC`.

Delivered as `LandedN 1 c (fun c' => ExecEntry … s … c')`: the divergence-fold shape
(one machine step ≥, control AT the child entry, child NOT returned).  The
sub-ghosts are the post-`jal` register file, `sp_sub := sp - hdrm`, `m0_sub :=
mcall`.  `hdrm` is left abstract (each statement arm lowers `sp` by its own frame
size); the geometry premises are stated over the lowered `sp - hdrm`.

`armTail_rec_es` truncated before its `hIH` call, retargeted to `ExecEntry`. -/
theorem execEntry_of_jalPrefix
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (s : Stmt)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21) (hdrm : BitVec 64)
    (sp aInterp aStmt aEnv aRet : BitVec 64)
    (out0 : Array String) (mcall : Mem)
    (c : Config)
    (hjaltgt : (callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 execStmtEntry)
    (hlink : (BitVec.addInt callPC 4) = retPC)
    (hretAl : retPC.toNat % 4 = 0)
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4)))
    (hpre :
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some callPC ∧
        c.σ.regs.get? Register.x10 = some aInterp ∧
        c.σ.regs.get? Register.x11 = some aStmt ∧
        c.σ.regs.get? Register.x12 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aRet ∧
        c.σ.regs.get? Register.x2 = some (sp - hdrm) ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        ((∃ w, c.σ.regs.get? Register.x8 = some w) ∧
         (∃ w, c.σ.regs.get? Register.x9 = some w) ∧
         (∃ w, c.σ.regs.get? Register.x18 = some w) ∧
         (∃ w, c.σ.regs.get? Register.x19 = some w)) ∧
        c.σ.sailOutput = out0 ∧
        String.join out0.toList = st.out ∧
        c.σ.mem = mcall ∧
        Exec_stmtLoaded mcall ∧
        StmtRepr mcall aStmt.toNat s ∧
        StoreRepr mcall N A φf φc st.store ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < (sp - hdrm).toNat) → mcall[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        aStmt.toNat % 8 = 0 ∧
        0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aStmt.toNat ∧
        (aStmt.toNat + 16 ≤ SL.lo ∨ (sp - hdrm).toNat ≤ aStmt.toNat) ∧
        StackOK SL (sp - hdrm) (176 + 1088) ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        ((sp - hdrm).toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo) ∧
        -- ITEM ZERO B1: the child statement's recursion-sound budget at the
        -- lowered `sp`, its `.fn`-bodies bound, and the store-bodies invariant.
        StackOK SL (sp - hdrm)
          (s.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Stmt.bodiesBound Vsa.While.perCallBudget s = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget) :
    LandedN 1 c (fun c' =>
      ExecEntry (fun R => c'.σ.regs.get? R) N A SL φf φc st d env s
        (sp - hdrm) retPC aInterp aStmt aEnv aRet mcall c') := by
  obtain ⟨hG, htick, hpc, ha0, ha1, ha2, ha3, hsp, ⟨vmi, hmi⟩,
    ⟨⟨w8, hw8⟩, ⟨w9, hw9⟩, ⟨w18, hw18⟩, ⟨w19, hw19⟩⟩,
    hout, houtStr, hmemc, hcodeS, hstmtR, hstore, hstoreSurv,
    hstAl, hstLo, hstHi, hstWin, hstStk,
    hstackOK, hSLlo, hSLhiRam, hSLwin, hcodeStk,
    hstackBudget, hstmtBodies, hstoreBodies⟩ := hpre
  -- ============ callPC: jal exec_stmt → PC := execStmtEntry, x1 := retPC ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    hjalSite c.σ c.tick c.steps vmi hG hpc hmi (hmemc ▸ hcodeS) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = mcall := by rw [hmem1]; exact hmemc
  have hpc1 : σ1.regs.get? Register.PC = some (BitVec.ofNat 64 execStmtEntry) := by
    have := obs_jalT_pc hobs1; rwa [hjaltgt] at this
  have hlink1 : σ1.regs.get? Register.x1 = some retPC := by
    have := obs_jalT_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hlink] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some aInterp := obs_jalT_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 : σ1.regs.get? Register.x11 = some aStmt := obs_jalT_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have ha2_1 : σ1.regs.get? Register.x12 = some aEnv := obs_jalT_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2
  have ha3_1 : σ1.regs.get? Register.x13 = some aRet := obs_jalT_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - hdrm) := obs_jalT_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  have hx8_1 : σ1.regs.get? Register.x8 = some w8 :=
    obs_jalT_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw8
  have hx9_1 : σ1.regs.get? Register.x9 = some w9 :=
    obs_jalT_other hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw9
  have hx18_1 : σ1.regs.get? Register.x18 = some w18 :=
    obs_jalT_other hobs1 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw18
  have hx19_1 : σ1.regs.get? Register.x19 = some w19 :=
    obs_jalT_other hobs1 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw19
  obtain ⟨vmi1, hmi1⟩ := obs_jalT_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by
    rw [hobs1.out, sailOutput_sigmaPost_jal]; exact hout
  -- ============ the sub-call's ExecEntry at ⟨σ1, i1, steps+1⟩ ============
  refine ⟨1, ⟨σ1, i1, c.steps + 1⟩, Nat.le_refl _,
    StepsN.succ hstep1 (StepsN.zero _), ?_⟩
  · exact
      { good := hG1
        tick := hi1
        pc := hpc1
        a0 := ha0_1
        a1 := ha1_1
        a2 := ha2_1
        a3 := ha3_1
        ra := hlink1
        ra_align := hretAl
        spReg := hsp_1
        stackOK := hstackOK
        stackBudget := hstackBudget
        stmt_bodies := hstmtBodies
        store_bodies := hstoreBodies
        minstret := ⟨vmi1, hmi1⟩
        mem := hmem1e
        code := by show Exec_stmtLoaded σ1.mem; rw [hmem1e]; exact hcodeS
        stmt := by
          show StmtRepr σ1.mem aStmt.toNat s; rw [hmem1e]; exact hstmtR
        store := by
          show StoreRepr σ1.mem N A φf φc st.store; rw [hmem1e]; exact hstore
        store_survives := by
          intro m' hag
          refine hstoreSurv m' (fun k hk1 => ?_)
          have := hag k hk1
          rw [hmem1e] at this; exact this
        out := by
          show Machine.output σ1 = st.out
          simp only [Vsa.Machine.output]; rw [hout1]; exact houtStr
        frame := fun _ _ => rfl
        code_stack_disjoint := hcodeStk
        stack_ram := ⟨hSLlo, hSLhiRam⟩
        stack_win := hSLwin
        stmt_stack_disjoint := hstStk
        stmt_align := hstAl
        stmt_ram := ⟨hstLo, hstHi⟩
        stmt_win := hstWin
        spill_defined := ⟨⟨w8, hx8_1⟩, ⟨w9, hx9_1⟩, ⟨w18, hx18_1⟩, ⟨w19, hx19_1⟩⟩ }

#print axioms execEntry_of_jalPrefix

end Vsa.Sim
