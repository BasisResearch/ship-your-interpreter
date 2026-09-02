import Vsa.Sim.ExecExprRet
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 statement RECURSION multiplier: `armTail_rec_es`

The `exec_stmt`-frame analog of `armTail_rec` (`EvalRecCommon.lean`). Where
`armTail_rec` is hardwired for the `eval_expr` frame (caller `sp` lowered by 1088,
sub-result buffer below the frame, outer sret in `x9`), `armTail_rec_es` is the
statement-frame version: the caller's `sp` is lowered by **176**, the sub-result
buffer `subsret` lives **inside** the frame at `sp' + 16` (so inside the stack
window `[SL.lo, sp)`, unlike `eval_expr`'s below-frame buffer), and the five
callee-saved spills are ra/s0/s1/s2/s3 at `sp-{8,16,24,32,40}`.

`armTail_rec_es` takes the machine state right at the `jal eval_expr` PC
(`callPC`), with the sub-call's arguments already staged (`a0 = subsret`,
`a1 = aInterp`, `a2 = aOperand`, `sp` lowered), threads the `jal`, applies the
sub-derivation induction hypothesis (`EvalIH`), and repackages its `EvalExitD`
into `SubExecReturn` (the state a recursive statement arm holds after the call).

The setup instructions BEFORE the `jal` (`ld a2,8(s0)`, `addi a0,sp,16`, the two
`mv`s — differing between the `expr` and `ret` arms) are threaded by each arm
from its `ExecArmEntryK` entry to this `callPC` precondition; `armTail_rec_es`
itself starts at the `jal`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- `Exec_stmtLoaded` transfers along byte agreement on the code region
`[0x80003fe0, 0x80004308)` (13 chunks). The mirror of `loaded_eval_expr_agreeP`
for the statement function's text. -/
theorem loaded_exec_stmt_agreeP (m m' : Mem)
    (ha : ∀ a, (0x80003fe0 ≤ a ∧ a < 0x80004308) → m[a]? = m'[a]?)
    (h : Exec_stmtLoaded m) : Exec_stmtLoaded m' := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [exec_stmtChunk0] at c0 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk1] at c1 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk2] at c2 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk3] at c3 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk4] at c4 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk5] at c5 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk6] at c6 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk7] at c7 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk8] at c8 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk9] at c9 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk10] at c10 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk11] at c11 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk12] at c12 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])

/-! ## `armTail_rec_es` — `jal eval_expr` ≫ IH ⇒ `SubExecReturn`

From the machine state at the `jal eval_expr` PC (`callPC`), with the sub-call's
ABI arguments staged (`a0 = subsret`, `a1 = aInterp`, `a2 = aOperand`, `sp` lowered
by 176), one `jal` step lands at `eval_expr`'s entry with link `retPC = callPC+4`;
the sub-call's `EvalEntry` is assembled from the arm state, the `EvalIH` is
applied, and its `EvalExitD` is repackaged into `SubExecReturn`.

`garm` is the arm-entry register frame (post-`execBlockA`, before the setup
clobbers of `a0/a1/a2/a3`): `x8 = aStmt`, `x9 = aInterp`, `x18 = aRet`,
`x19 = aEnv`, `x2 = sp`. The setup only clobbers caller-saved `a*` registers, so
every callee-saved register still reads `garm R`. -/
theorem armTail_rec_es
    (garm : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr) (vsub : Value)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r aRet subsret aInterp aOperand : BitVec 64)
    (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (mcall : Mem)
    -- target arithmetic (fixed by the arm, `decide`-able concretely):
    (hjaltgt : (callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 evalExprEntry)
    (hlink : (BitVec.addInt callPC 4) = retPC)
    (hretAl : retPC.toNat % 4 = 0)
    -- the per-arm `jal eval_expr` site step:
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4)))
    -- the induction hypothesis for the sub-derivation:
    (hIH : EvalIH st d env esub st' vsub) :
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some callPC ∧
        c.σ.regs.get? Register.x10 = some subsret ∧          -- a0 = sub-sret
        c.σ.regs.get? Register.x11 = some aInterp ∧          -- a1 = interp*
        c.σ.regs.get? Register.x12 = some aOperand ∧         -- a2 = operand node
        c.σ.regs.get? Register.x18 = some aRet ∧             -- s2 = retslot (survives)
        c.σ.regs.get? Register.x2 = some (sp - 176#64) ∧     -- sp lowered
        (∃ w, c.σ.regs.get? Register.x8 = some w) ∧          -- s0 defined (Stmt*)
        (∃ w, c.σ.regs.get? Register.x9 = some w) ∧          -- s1 defined (interp*)
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        c.σ.sailOutput = out0 ∧
        String.join out0.toList = st.out ∧
        c.σ.mem = mcall ∧
        Exec_stmtLoaded mcall ∧ Eval_exprLoaded mcall ∧
        Value_intLoaded mcall ∧ IntSlotPinned mcall ∧
        ExprRepr mcall aOperand.toNat esub ∧
        StoreRepr mcall N A φf φc st.store ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mcall[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        -- callee-saved regs (excl s0/s1/s2/s3/sp) still read the arm frame `garm`
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x19 == R) = false →
          (Register.x2 == R) = false → c.σ.regs.get? R = garm R) ∧
        garm Register.x8 = some v8 ∧ garm Register.x9 = some v9 ∧
        garm Register.x18 = some v18 ∧ garm Register.x19 = some v19 ∧
        garm Register.x2 = some sp ∧
        read64 mcall (sp.toNat - 8) = some r.toNat ∧
        read64 mcall (sp.toNat - 16) = some v8.toNat ∧
        read64 mcall (sp.toNat - 24) = some v9.toNat ∧
        read64 mcall (sp.toNat - 32) = some v18.toNat ∧
        read64 mcall (sp.toNat - 40) = some v19.toNat ∧
        -- operand-node geometry (the sub-call's `aExpr`):
        aOperand.toNat % 8 = 0 ∧
        0x80000000 ≤ aOperand.toNat ∧ aOperand.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aOperand.toNat ∧
        (aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aOperand.toNat) ∧
        -- sub-result buffer geometry: `sp' + 16 = sp - 160`, inside the frame,
        -- ABOVE the frame base `sp - 176` (so disjoint from the sub-call's own
        -- stack window `[SL.lo, sp - 176)`) and below the five spills (lowest is
        -- s3 @ sp-40):
        subsret.toNat % 8 = 0 ∧
        sp.toNat - 176 ≤ subsret.toNat ∧ subsret.toNat + 24 ≤ sp.toNat - 40 ∧
        -- stack geometry: statement frame (176) + recursive headroom (one eval
        -- frame, 2176 below sp'), 16-alignment:
        SL.lo + 2352 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        sp.toNat ≤ 0x100000000 ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        r.toNat % 4 = 0 ∧
        -- code/table/arena region disjointness (eval_expr code region, value_int
        -- code, expr jump-table, arena):
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧
        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        -- exec_stmt code region `[0x80003fe0, 0x80004308)` disjointness (for the
        -- survival of `Exec_stmtLoaded` across the sub-call):
        (sp.toNat ≤ 0x80003fe0 ∨ 0x80004308 ≤ SL.lo) ∧
        (A.hi ≤ 0x80003fe0 ∨ 0x80004308 ≤ A.lo) ∧
        -- ITEM ZERO B1: child EXPRESSION budget at the lowered `sp - 176` (the
        -- statement frame), `.fn`-bodies bound, store-bodies invariant.
        StackOK SL (sp - 176#64)
          (esub.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget esub = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget)
      (SubExecReturn garm N A SL φf φc st.store.frames.size st.store.closures.size
        st' vsub sp r aRet subsret retPC
        r v8 v9 v18 v19 mcall mcall) := by
  intro c hpre
  obtain ⟨hG, htick, hpc, ha0, hx11, hx12, hs2, hsp, ⟨wx8, hwx8⟩, ⟨wx9, hwx9⟩, ⟨vmi, hmi⟩, hout, houtStr, hmemc,
    hcodeS, hcode, hviCode, hslot, hsubexpr, hstore, hstoreSurv, hframe,
    hgx8, hgx9, hgx18, hgx19, hgx2,
    hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hopAl, hopLo, hopHi, hopWin, hopStk,
    hssAl, hssLo, hssHi,
    hsproom, hspSLhi, hsp16, hsphi, hSLlo, hSLhiRam, hSLwin, hraAl,
    hcodeStk, hviStk, htableStk, harenaStk, harenaCode, hexecCodeStk, hexecArenaCode,
    hstackBudget, hexprBodies, hstoreBodies⟩ := hpre
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp176 : 176 ≤ sp.toNat := by omega
  have hspsub : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
    rw [h176]; have := sp.isLt; omega
  -- ============ callPC: jal eval_expr → PC := evalExprEntry, x1 := retPC ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    hjalSite c.σ c.tick c.steps vmi hG hpc hmi (hmemc ▸ hcodeS) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = mcall := by rw [hmem1]; exact hmemc
  have hpc1 : σ1.regs.get? Register.PC = some (BitVec.ofNat 64 evalExprEntry) := by
    have := obs_jalT_pc hobs1; rwa [hjaltgt] at this
  have hlink1 : σ1.regs.get? Register.x1 = some retPC := by
    have := obs_jalT_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hlink] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some subsret := obs_jalT_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hx11_1 : σ1.regs.get? Register.x11 = some aInterp := obs_jalT_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11
  have hx12_1 : σ1.regs.get? Register.x12 = some aOperand := obs_jalT_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 176#64) := obs_jalT_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  have hs2_1 : σ1.regs.get? Register.x18 = some aRet := obs_jalT_other hobs1 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs2
  obtain ⟨vmi1, hmi1⟩ := obs_jalT_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by
    rw [hobs1.out, sailOutput_sigmaPost_jal]; exact hout
  -- spill-defined for the sub-EvalEntry: s0/s1/s2 present at σ1 (the `jal` writes
  -- only x1/PC/minstret, so the callee-saved regs pass through unchanged).
  have hx8_1 : σ1.regs.get? Register.x8 = some wx8 :=
    obs_jalT_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hwx8
  have hx9_1 : σ1.regs.get? Register.x9 = some wx9 :=
    obs_jalT_other hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hwx9
  -- ============ the sub-call's EvalEntry at ⟨σ1, i1, steps+1⟩ ============
  -- The sub-call `aEnv` = aInterp (a1); `sret` = subsret; sp lowered to sp-176.
  have hEntry : EvalEntry (fun R => σ1.regs.get? R) N A SL φf φc st d env esub
      (sp - 176#64) retPC subsret aInterp aOperand mcall ⟨σ1, i1, c.steps + 1⟩ :=
    { good := hG1
      tick := hi1
      pc := hpc1
      a0 := ha0_1
      a1 := hx11_1
      a2 := hx12_1
      ra := hlink1
      ra_align := hretAl
      spReg := hsp_1
      stackOK := ⟨by rw [hspsub]; omega, by rw [hspsub]; omega, by rw [hspsub]; omega⟩
      stackBudget := hstackBudget
      expr_bodies := hexprBodies
      store_bodies := hstoreBodies
      minstret := ⟨vmi1, hmi1⟩
      mem := hmem1e
      code := by show Eval_exprLoaded σ1.mem; rw [hmem1e]; exact hcode
      expr := by rw [hmem1e]; exact hsubexpr
      store := by rw [hmem1e]; exact hstore
      store_survives := by
        -- wave 47e: the child's WIDENED footprint = the parent's (same `SL`);
        -- the sub-sret window sits inside `[SL.lo, SL.hi)`, so it is absorbed.
        intro m' hag
        refine hstoreSurv m' (fun k hk1 => ?_)
        have hk2' : ¬ (subsret.toNat ≤ k ∧ k < subsret.toNat + 24) := by
          intro ⟨ha, hb⟩; exact hk1 ⟨by omega, by omega⟩
        have := hag k hk1 hk2'
        rwa [hmem1e] at this
      out := by
        show Vsa.Machine.output σ1 = st.out
        simp only [Vsa.Machine.output]; rw [hout1]; exact houtStr
      frame := fun _ _ => rfl
      code_stack_disjoint := by
        rcases hcodeStk with h | h
        · left; rw [hspsub]; omega
        · right; exact h
      expr_stack_disjoint := by
        rcases hopStk with h | h
        · left; exact h
        · right; rw [hspsub]; omega
      expr_align := hopAl
      expr_ram := ⟨hopLo, hopHi⟩
      expr_win := hopWin
      sret_align := hssAl
      sret_ram := ⟨by omega, by omega⟩
      sret_win := by omega
      sret_vicode_disjoint := by
        rcases hviStk with h | h
        · right; omega
        · left; omega
      sret_stack_disjoint := by right; rw [hspsub]; omega
      sret_evalcode_disjoint := by
        rcases hcodeStk with h | h
        · left; omega
        · right; omega
      vicode_stack_disjoint := by
        rcases hviStk with h | h
        · left; exact h
        · right; rw [hspsub]; omega
      stack_ram := ⟨hSLlo, hSLhiRam⟩
      stack_win := hSLwin
      value_int_code := by rw [hmem1e]; exact hviCode
      int_slot := by rw [hmem1e]; exact hslot
      table_stack_disjoint := by
        rcases htableStk with h | h
        · left; exact h
        · right; rw [hspsub]; omega
      spill_defined := ⟨⟨wx8, hx8_1⟩, ⟨wx9, hx9_1⟩, ⟨aRet, hs2_1⟩⟩ }
  -- ============ the sub-call (the induction hypothesis) ============
  obtain ⟨c2, hs2', hExit, hpres, φf', φc', hpf', hpc', hsurvSL⟩ :=
    hIH (fun R => σ1.regs.get? R) N A SL φf φc (sp - 176#64) retPC subsret aInterp aOperand mcall
      ⟨σ1, i1, c.steps + 1⟩ hEntry
  -- PC back at the link (ret target of an aligned retPC)
  have hpcRet : c2.σ.regs.get? Register.PC = some retPC := by
    rw [hExit.pc, ret_tgt retPC hretAl]
  -- x1 back at the link `retPC` (eval_expr restores ra to its entry ra = retPC)
  have hx1_2 : c2.σ.regs.get? Register.x1 = some retPC := hExit.ra
  -- frame composition helper
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  -- callee-saved regs at c2 = arm frame `garm` (excl s0/s1/s2/s3/sp).
  have hframe2 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x19 == R) = false →
      (Register.x2 == R) = false → c2.σ.regs.get? R = garm R := by
    intro R hR he8 he9 he18 he19 he2
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have hx1R : (Register.x1 == R) = false := abi_ne' (by decide) hab
    have f2 : c2.σ.regs.get? R = σ1.regs.get? R := hExit.frame R hR'
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_jal _ _ _ _ _ _ R hmiR hpcR hx1R hnpcR hmiiR)
    rw [f2, f1]; exact hframe R hR' he8 he9 he18 he19 he2
  -- s2 (x18 = aRet) survives (callee-saved, restored to sub-entry = arm value)
  have hs2_2 : c2.σ.regs.get? Register.x18 = some aRet := by
    have f2 : c2.σ.regs.get? Register.x18 = σ1.regs.get? Register.x18 :=
      hExit.frame Register.x18 (by decide)
    rw [f2]; exact hs2_1
  -- memory agreement outside (stack-window ∪ arena) — subsret ⊂ stack window
  have hmemFrame2 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
      ¬ (A.lo ≤ a ∧ a < A.hi) →
      (subsret.toNat ≤ a ∧ a < subsret.toNat + 24) ∨ c2.σ.mem[a]? = mcall[a]? := by
    intro a h1 h2
    have := hExit.memFrame a (by rw [hspsub]; intro ⟨ha, hb⟩; exact h1 ⟨ha, by omega⟩) h2
    rcases this with hin | heq
    · left; exact hin
    · right; exact heq
  -- spill slots survive the sub-call (top 40 bytes of the frame: outside the sub
  -- window [subsret, subsret+24) ⊂ [SL.lo, sp-40), outside arena, above subsret+24)
  have hAgTop : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) mcall c2.σ.mem := by
    intro k hk
    have := hExit.memFrame k
      (by rw [hspsub]; intro ⟨_, hb⟩; omega) (by rcases harenaStk with h | h <;> omega)
    rcases this with hin | heq
    · exact absurd hin (by omega)
    · exact heq.symm
  have hslotRa2 : read64 c2.σ.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotRa
  have hslotS02 : read64 c2.σ.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotS0
  have hslotS12 : read64 c2.σ.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotS1
  have hslotS22 : read64 c2.σ.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotS2
  have hslotS32 : read64 c2.σ.mem (sp.toNat - 40) = some v19.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => by omega)]; exact hslotS3
  -- exec_stmt's code survives (code region outside stack-window/arena)
  have hcodeS2 : Exec_stmtLoaded c2.σ.mem := by
    refine loaded_exec_stmt_agreeP mcall c2.σ.mem (fun a ha => ?_) hcodeS
    have := hExit.memFrame a
      (by rw [hspsub]; rcases hexecCodeStk with h | h <;> intro ⟨p, q⟩ <;> omega)
      (by rcases hexecArenaCode with h | h <;> omega)
    rcases this with hin | heq
    · exact absurd hin (by rcases hexecCodeStk with h | h <;> omega)
    · exact heq.symm
  -- mem framed to `m0 := mcall` outside the stack window (identity here since the
  -- pre-call memory IS the arm-entry memory).
  refine ⟨c2, (Steps.single hstep1).trans hs2',
    hExit.good, hExit.tick, hpcRet, hx1_2, hExit.spReg, hs2_2, hExit.minstret,
    hExit.out, hframe2, hgx8, hgx9, hgx18, hgx19, hgx2,
    hExit.result,
    ⟨φf', φc', hpf', hpc', hsurvSL c2.σ.mem (fun _ _ => rfl)⟩,
    hcodeS2, hslotRa2, hslotS02, hslotS12, hslotS22, hslotS32,
    ⟨by omega, by omega⟩, hmemFrame2, hpres, fun a _ => rfl⟩

/-! ## `execExprGlue` — discharging `execExprSim`'s `hGlue` via `armTail_rec_es`

The `expr`-arm setup (`ld a2,8(s0)`, `addi a0,sp,16`, `mv a3,s3`, `mv a1,s1`) run
from the arm entry `0x80004170` to the `jal eval_expr` at `0x80004180`, then
`armTail_rec_es` for the sub-call. Produces the `SubExecReturn` at the link PC
`0x80004184` that `execExprSim`'s tail consumes. The `ExecArmEntryK` residuals not
already carried by that predicate — the sub-expression `ExprRepr`, the operand
pointer read, the `eval_expr`/`value_int` code + jump-table pin, the recursion
headroom and arena/code disjointness, and the store-window survival — are passed
explicitly (they are the genuine spec/geometry facts, in `ExecEntry` on the caller
side; here they are named residuals). -/
theorem execExprGlue
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr) (v : Value)
    (sp r aInterp aStmt aEnv aRet aOperand : BitVec 64) (m0 : Mem) (out0 : Array String)
    (hIH : EvalIH st d env e st' v)
    -- the sub-expression node (`stmt->expr`, `ld a2,8(s0)`):
    (hop : ∀ ment : Mem, (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
      read64 ment (aStmt.toNat + 8) = some aOperand.toNat)
    (hsubexpr : ∀ ment : Mem, (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
      ExprRepr ment aOperand.toNat e)
    -- `Stmt` node geometry (8-aligned 16-byte RAM slot above HTIF), for the
    -- `ld a2,8(s0)` load-region checks:
    (hstmtAl : aStmt.toNat % 8 = 0)
    (hstmtLo : 0x80000000 ≤ aStmt.toNat) (hstmtHi : aStmt.toNat + 16 ≤ 0x100000000)
    (hstmtWin : tohostAddr + 16 ≤ aStmt.toNat)
    -- the code residuals (survive on the stack-window complement):
    (hevalcode : ∀ ment : Mem, (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
      Eval_exprLoaded ment)
    (hvicode : ∀ ment : Mem, (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
      Value_intLoaded ment)
    (hslotP : ∀ ment : Mem, (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
      IntSlotPinned ment)
    -- the store-window survival (as in `ExecEntry.store_survives`):
    (hstoreSurv : ∀ ment : Mem, (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
      ∀ m' : Mem, (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ment[k]? = m'[k]?) →
        StoreRepr m' N A φf φc st.store)
    -- operand-node geometry:
    (hopAl : aOperand.toNat % 8 = 0)
    (hopLo : 0x80000000 ≤ aOperand.toNat) (hopHi : aOperand.toNat + 16 ≤ 0x100000000)
    (hopWin : tohostAddr + 16 ≤ aOperand.toNat)
    (hopStk : aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aOperand.toNat)
    -- recursion headroom + region disjointness:
    (hsproom : SL.lo + 2352 ≤ sp.toNat) (hspSLhi : sp.toNat ≤ SL.hi) (hsp16 : sp.toNat % 16 = 0)
    (hSLlo : 0x80000000 ≤ SL.lo) (hSLhi : SL.hi ≤ 0x100000000) (hSLwin : tohostAddr + 16 ≤ SL.lo)
    (hcodeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo)
    (hviStk : (0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c)
    (htableStk : (0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58)
    (harenaStk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)
    (hexecArenaCode : A.hi ≤ 0x80003fe0 ∨ 0x80004308 ≤ A.lo)
    (hexecCodeStk : sp.toNat ≤ 0x80003fe0 ∨ 0x80004308 ≤ SL.lo)
    -- ITEM ZERO B1: child EXPRESSION budget at the lowered `sp - 176` (the
    -- statement frame), `.fn`-bodies bound, store-bodies invariant (forwarded
    -- to `armTail_rec_es`).
    (hstackBudget : StackOK SL (sp - 176#64)
      (e.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088))
    (hexprBodies : Expr.bodiesBound Vsa.While.perCallBudget e = true)
    (hstoreBodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget) :
    Triple
      (fun c => ∃ ment v8 v9 v18 v19,
        ExecArmEntryK g N A SL φf φc st execArmExpr sp r aInterp aStmt aEnv aRet
          v8 v9 v18 v19 out0 m0 ment c)
      (fun c => ∃ subsret v1 v8 v9 v18 v19 mcall,
        SubExecReturn g N A SL φf φc st.store.frames.size st.store.closures.size
          st' v
          sp r aRet subsret (0x80004184#64) v1 v8 v9 v18 v19 m0 mcall c) := by
  intro c hpre
  obtain ⟨ment, v8, v9, v18, v19, hArm⟩ := hpre
  obtain ⟨hG, htick, hpc, hx8, hx9, hx19, hx18, hsp, hra, ⟨vmi, hmi⟩, hout, houtStr,
    hmem, hcodeS, hstore, hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hgx8, hgx9, hgx18, hgx19, hgx2, hframe, hmemframe,
    hsp176, hsphi, hsplo, hspwin, hsp8, hraAl⟩ := hArm
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hspsub : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
    rw [h176]; have := sp.isLt; omega
  -- concrete facts on `ment` from the memFrame:
  have hopM : read64 ment (aStmt.toNat + 8) = some aOperand.toNat := hop ment hmemframe
  have hsubexprM : ExprRepr ment aOperand.toNat e := hsubexpr ment hmemframe
  have hevalM : Eval_exprLoaded ment := hevalcode ment hmemframe
  have hviM : Value_intLoaded ment := hvicode ment hmemframe
  have hslotPM : IntSlotPinned ment := hslotP ment hmemframe
  -- operand-pointer byte reassembly (for the `ld a2,8(s0)`):
  have haddr8 : (aStmt + sign_extend (m := 64) (0x008#12)).toNat = aStmt.toNat + 8 := by
    rw [BitVec.toNat_add]
    have hv : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
    rw [hv]; omega
  obtain ⟨pb0, pb1, pb2, pb3, pb4, pb5, pb6, pb7, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hpsext⟩ :=
    spill_roundtrip_ee ment (aStmt.toNat + 8) aOperand hopM
  -- ============ 0x80004170: ld a2,8(s0) → x12 := aOperand ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80004170_es c.σ c.tick c.steps (0x80004170#64) vmi aStmt pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
      hG hpc hmi hx8 (hmem ▸ hcodeS) rfl
      (by rw [haddr8]; omega) (by rw [haddr8]; omega)
      (by rw [haddr8, htoh]; right; omega) (by rw [haddr8]; omega)
      (by rw [haddr8, hmem]; exact hp0) (by rw [haddr8, hmem]; exact hp1)
      (by rw [haddr8, hmem]; exact hp2) (by rw [haddr8, hmem]; exact hp3)
      (by rw [haddr8, hmem]; exact hp4) (by rw [haddr8, hmem]; exact hp5)
      (by rw [haddr8, hmem]; exact hp6) (by rw [haddr8, hmem]; exact hp7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80004174#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80004170#64) 4 = (0x80004174#64 : BitVec 64) from by decide] at this
  have hx12_1 : σ1.regs.get? Register.x12 = some aOperand := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hpsext] at this
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  have hx19_1 : σ1.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs1 Register.x19 (by decide) hx19
  have hx9_1 : σ1.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs1 Register.x9 (by decide) hx9
  have hx8_1 : σ1.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs1 Register.x8 (by decide) hx8
  have hx18_1 : σ1.regs.get? Register.x18 = some aRet := obs_alu_other' hobs1 Register.x18 (by decide) hx18
  have hra_1 : σ1.regs.get? Register.x1 = some r := obs_alu_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  have hcode1 : Exec_stmtLoaded σ1.mem := by rw [hmem1e]; exact hcodeS
  -- ============ 0x80004174: addi a0,sp,16 → x10 := (sp-176)+16 = subsret ============
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80004174_es σ1 i1 (c.steps + 1) (0x80004174#64) vmi1 (sp - 176#64)
      hG1 hpc1 hmi1 hsp_1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x80004178#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80004174#64) 4 = (0x80004178#64 : BitVec 64) from by decide] at this
  have hx10_2 : σ2.regs.get? Register.x10 = some ((sp - 176#64) + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  have hx19_2 : σ2.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs2 Register.x19 (by decide) hx19_1
  have hx9_2 : σ2.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs2 Register.x9 (by decide) hx9_1
  have hx8_2 : σ2.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs2 Register.x8 (by decide) hx8_1
  have hx18_2 : σ2.regs.get? Register.x18 = some aRet := obs_alu_other' hobs2 Register.x18 (by decide) hx18_1
  have hx12_2 : σ2.regs.get? Register.x12 = some aOperand := obs_alu_other' hobs2 Register.x12 (by decide) hx12_1
  have hra_2 : σ2.regs.get? Register.x1 = some r := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  have hcode2 : Exec_stmtLoaded σ2.mem := by rw [hmem2e]; exact hcodeS
  -- ============ 0x80004178: mv a3,s3 (addi a3,s3,0) → x13 := aEnv ============
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_80004178_es σ2 i2 (c.steps + 1 + 1) (0x80004178#64) vmi2 aEnv
      hG2 hpc2 hmi2 hx19_2 hcode2 rfl hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  have hmem3e : σ3.mem = ment := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x8000417c#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80004178#64) 4 = (0x8000417c#64 : BitVec 64) from by decide] at this
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs3 Register.x2 (by decide) hsp_2
  have hx9_3 : σ3.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs3 Register.x9 (by decide) hx9_2
  have hx8_3 : σ3.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs3 Register.x8 (by decide) hx8_2
  have hx18_3 : σ3.regs.get? Register.x18 = some aRet := obs_alu_other' hobs3 Register.x18 (by decide) hx18_2
  have hx12_3 : σ3.regs.get? Register.x12 = some aOperand := obs_alu_other' hobs3 Register.x12 (by decide) hx12_2
  have hx10_3 : σ3.regs.get? Register.x10 = some ((sp - 176#64) + sign_extend (m := 64) (0x010#12)) := obs_alu_other' hobs3 Register.x10 (by decide) hx10_2
  have hra_3 : σ3.regs.get? Register.x1 = some r := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_alu]; exact hout2
  have hcode3 : Exec_stmtLoaded σ3.mem := by rw [hmem3e]; exact hcodeS
  -- ============ 0x8000417c: mv a1,s1 (addi a1,s1,0) → x11 := aInterp ============
  obtain ⟨σ4, i4, hs4', hi4, hG4, hmem4, hobs4⟩ :=
    site_8000417c_es σ3 i3 (c.steps + 1 + 1 + 1) (0x8000417c#64) vmi3 aInterp
      hG3 hpc3 hmi3 hx9_3 hcode3 rfl hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4'
  have hmem4e : σ4.mem = ment := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x80004180#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x8000417c#64) 4 = (0x80004180#64 : BitVec 64) from by decide] at this
  have hx11_4 : σ4.regs.get? Register.x11 = some aInterp := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (aInterp + sign_extend (m := 64) (0x000#12)) = aInterp from by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]; simp only [show (sign_extend (m := 64) (0x000#12) : BitVec 64).toNat = 0 from by decide]; have := aInterp.isLt; omega] at this
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs4 Register.x2 (by decide) hsp_3
  have hx8_4 : σ4.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs4 Register.x8 (by decide) hx8_3
  have hx18_4 : σ4.regs.get? Register.x18 = some aRet := obs_alu_other' hobs4 Register.x18 (by decide) hx18_3
  have hx12_4 : σ4.regs.get? Register.x12 = some aOperand := obs_alu_other' hobs4 Register.x12 (by decide) hx12_3
  have hx10_4 : σ4.regs.get? Register.x10 = some ((sp - 176#64) + sign_extend (m := 64) (0x010#12)) := obs_alu_other' hobs4 Register.x10 (by decide) hx10_3
  have hx9_4 : σ4.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs4 Register.x9 (by decide) hx9_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hout4 : σ4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_alu]; exact hout3
  have hcode4 : Exec_stmtLoaded σ4.mem := by rw [hmem4e]; exact hcodeS
  -- callee-saved frame at σ4 (excl s0/s1/s2/s3/sp): the four `addi/mv/ld` write
  -- only x12/x10/x13/x11 (all caller-saved); the entry frame reads back to `g`.
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have hframe4 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x19 == R) = false →
      (Register.x2 == R) = false → σ4.regs.get? R = g R := by
    intro R hR he8 he9 he18 he19 he2
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have a : ∀ {σa σb : MState} {pc vm : BitVec 64} {rd : Register} {vv : RegisterType rd},
        ReadsLikePost σb (sigmaPost_alu σa pc vm rd vv) → (rd == R) = false →
        σb.regs.get? R = σa.regs.get? R := fun ho hrd =>
      (ho.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hrd hnpcR hmiiR)
    have h12 : (Register.x12 == R) = false := abi_ne' (by decide) hab
    have h10 : (Register.x10 == R) = false := abi_ne' (by decide) hab
    have h13 : (Register.x13 == R) = false := abi_ne' (by decide) hab
    have h11 : (Register.x11 == R) = false := abi_ne' (by decide) hab
    exact ((a hobs4 h11).trans ((a hobs3 h13).trans ((a hobs2 h10).trans (a hobs1 h12)))).trans
      (hframe R hR' he8 he9 he18 he19 he2)
  -- ============ 0x80004180: armTail_rec_es (jal eval_expr ≫ IH) → SubExecReturn ===
  have hsubval : ((sp - 176#64) + sign_extend (m := 64) (0x010#12)).toNat = sp.toNat - 160 := by
    rw [BitVec.toNat_add, hspsub]
    have hv : (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 := by decide
    rw [hv]; have := sp.isLt; omega
  obtain ⟨c5, hs5, hpost⟩ :=
    armTail_rec_es g N A SL φf φc st st' d env e v
      (0x80004180#64) (0x80004184#64) (0x1fefe4#21)
      sp r aRet ((sp - 176#64) + sign_extend (m := 64) (0x010#12)) aInterp aOperand v8 v9 v18 v19 out0 ment
      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (by decide)
      (fun σ i u vmiσ hGσ hpcσ hmiσ hcodeσ hiσ =>
        site_80004180_es σ i u (0x80004180#64) vmiσ hGσ hpcσ hmiσ hcodeσ rfl hiσ)
      hIH
      ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩
      ⟨hG4, hi4, hpc4, hx10_4, hx11_4, hx12_4, hx18_4, hsp_4,
        ⟨aStmt, hx8_4⟩, ⟨aInterp, hx9_4⟩, ⟨vmi4, hmi4⟩, hout4, houtStr,
        hmem4e, (hmem4e ▸ hcode4), (hmem4e ▸ hevalM), (hmem4e ▸ hviM), (hmem4e ▸ hslotPM),
        (hmem4e ▸ hsubexprM), (hmem4e ▸ hstore),
        (hstoreSurv ment hmemframe),
        hframe4, hgx8, hgx9, hgx18, hgx19, hgx2,
        (hmem4e ▸ hslotRa), (hmem4e ▸ hslotS0), (hmem4e ▸ hslotS1), (hmem4e ▸ hslotS2), (hmem4e ▸ hslotS3),
        hopAl, hopLo, hopHi, hopWin, hopStk,
        (by rw [hsubval]; omega), (by rw [hsubval]; omega), (by rw [hsubval]; omega),
        hsproom, hspSLhi, hsp16, (by omega), hSLlo, hSLhi, hSLwin, hraAl,
        hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
        hexecCodeStk, hexecArenaCode,
        hstackBudget, hexprBodies, hstoreBodies⟩
  -- `armTail_rec_es` yields `SubExecReturn … m0:=ment mcall:=ment` (last clause
  -- `ment = ment`); repackage to the TRUE entry `m0` (last clause `ment = m0`,
  -- which is exactly `hmemframe`), everything else being `m0`-independent.
  obtain ⟨cp, htp, hpcP, hraP, hspP, hs2P, hmiP, houtP, hframeP,
    hg8P, hg9P, hg18P, hg19P, hg2P, hvalP, hstoreP, hcodeP,
    hraSp, hs0Sp, hs1Sp, hs2Sp, hs3Sp, hwinP, hmemFrP, hmemExtP, _hbaseP⟩ := hpost
  refine ⟨c5,
    (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
      ((Steps.single hstep4).trans hs5))),
    ⟨(sp - 176#64) + sign_extend (m := 64) (0x010#12), r, v8, v9, v18, v19, ment,
      cp, htp, hpcP, hraP, hspP, hs2P, hmiP, houtP, hframeP,
      hg8P, hg9P, hg18P, hg19P, hg2P, hvalP, hstoreP, hcodeP,
      hraSp, hs0Sp, hs1Sp, hs2Sp, hs3Sp, hwinP, hmemFrP, hmemExtP, hmemframe⟩⟩

/-! ## `execExprSimC` — `ExecS.expr` with `hGlue` DISCHARGED by `execExprGlue`

The full `ExecS.expr` simulation Triple, no longer carrying the opaque `hGlue`
Triple premise of `execExprSim` (`ExecExprRet.lean`): the recursion glue is
supplied by `execExprGlue` (`= armTail_rec_es` + the arm setup), so the residuals
are now the CONCRETE named spec/geometry facts `execExprGlue` needs beyond the
`execBlockA` geometry. (`ExecArmEntryK` does not carry the sub-expression's
`ExprRepr`/operand-pointer/`eval_expr`-code/headroom facts — the fully
unconditional form needs `ExecEntry`/`execBlockA` widened to propagate them, a
`RESIDUAL`; here they are the honest per-case premises, exactly as the
expression-side recursive cases carry their operand-repr residual.) -/
theorem execExprSimC
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr) (v : Value)
    (sp r aInterp aStmt aEnv aRet aOperand : BitVec 64) (m0 : Mem) (out0 : Array String)
    (hSpec : ExecS st d env (.expr e) st' .normal)
    (hIH : EvalIH st d env e st' v)
    (hslot : StmtSlotPinned 0 execArmExpr m0)
    (htableStk0 : stmtJumpTableBase + 4 * 0 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 0)
    -- the `execExprGlue` residuals:
    (hop : ∀ ment : Mem, (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
      read64 ment (aStmt.toNat + 8) = some aOperand.toNat)
    (hsubexpr : ∀ ment : Mem, (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
      ExprRepr ment aOperand.toNat e)
    (hstmtAl : aStmt.toNat % 8 = 0)
    (hstmtLo : 0x80000000 ≤ aStmt.toNat) (hstmtHi : aStmt.toNat + 16 ≤ 0x100000000)
    (hstmtWin : tohostAddr + 16 ≤ aStmt.toNat)
    (hevalcode : ∀ ment : Mem, (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
      Eval_exprLoaded ment)
    (hvicode : ∀ ment : Mem, (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
      Value_intLoaded ment)
    (hslotP : ∀ ment : Mem, (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
      IntSlotPinned ment)
    (hstoreSurv : ∀ ment : Mem, (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
      ∀ m' : Mem, (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ment[k]? = m'[k]?) →
        StoreRepr m' N A φf φc st.store)
    (hopAl : aOperand.toNat % 8 = 0)
    (hopLo : 0x80000000 ≤ aOperand.toNat) (hopHi : aOperand.toNat + 16 ≤ 0x100000000)
    (hopWin : tohostAddr + 16 ≤ aOperand.toNat)
    (hopStk : aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aOperand.toNat)
    (hsproom : SL.lo + 2352 ≤ sp.toNat) (hspSLhi : sp.toNat ≤ SL.hi) (hsp16 : sp.toNat % 16 = 0)
    (hSLlo : 0x80000000 ≤ SL.lo) (hSLhi : SL.hi ≤ 0x100000000) (hSLwin : tohostAddr + 16 ≤ SL.lo)
    (hcodeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo)
    (hviStk : (0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c)
    (htableStk : (0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58)
    (harenaStk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)
    (hexecArenaCode : A.hi ≤ 0x80003fe0 ∨ 0x80004308 ≤ A.lo)
    (hexecCodeStk : sp.toNat ≤ 0x80003fe0 ∨ 0x80004308 ≤ SL.lo)
    -- ITEM ZERO B1: the `execExprGlue` budget residuals (child expression
    -- budget at the statement frame, `.fn`-bodies bound, store-bodies).
    (hstackBudget : StackOK SL (sp - 176#64)
      (e.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088))
    (hexprBodies : Expr.bodiesBound Vsa.While.perCallBudget e = true)
    (hstoreBodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget) :
    ExecExprSimGoal g N A SL φf φc st st' d env e v
      sp r aInterp aStmt aEnv aRet m0 out0 :=
  execExprSim g N A SL φf φc st st' d env e v sp r aInterp aStmt aEnv aRet m0 out0
    hSpec hIH hslot htableStk0
    (fun hIH' =>
      execExprGlue g N A SL φf φc st st' d env e v sp r aInterp aStmt aEnv aRet aOperand m0 out0
        hIH' hop hsubexpr hstmtAl hstmtLo hstmtHi hstmtWin hevalcode hvicode hslotP hstoreSurv
        hopAl hopLo hopHi hopWin hopStk hsproom hspSLhi hsp16 hSLlo hSLhi hSLwin
        hcodeStk hviStk htableStk harenaStk harenaCode hexecArenaCode hexecCodeStk
        hstackBudget hexprBodies hstoreBodies)

end Vsa.Sim
