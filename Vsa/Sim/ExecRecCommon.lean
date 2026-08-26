import Vsa.Sim.ExecExprRet

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
          (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → mcall[k]? = m'[k]?) →
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
        (A.hi ≤ 0x80003fe0 ∨ 0x80004308 ≤ A.lo))
      (SubExecReturn garm N A SL φf φc st' vsub sp r aRet subsret retPC
        r v8 v9 v18 v19 mcall mcall) := by
  intro c hpre
  obtain ⟨hG, htick, hpc, ha0, hx11, hx12, hs2, hsp, ⟨wx8, hwx8⟩, ⟨wx9, hwx9⟩, ⟨vmi, hmi⟩, hout, houtStr, hmemc,
    hcodeS, hcode, hviCode, hslot, hsubexpr, hstore, hstoreSurv, hframe,
    hgx8, hgx9, hgx18, hgx19, hgx2,
    hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hopAl, hopLo, hopHi, hopWin, hopStk,
    hssAl, hssLo, hssHi,
    hsproom, hspSLhi, hsp16, hsphi, hSLlo, hSLhiRam, hSLwin, hraAl,
    hcodeStk, hviStk, htableStk, harenaStk, harenaCode, hexecCodeStk, hexecArenaCode⟩ := hpre
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
      minstret := ⟨vmi1, hmi1⟩
      mem := hmem1e
      code := by show Eval_exprLoaded σ1.mem; rw [hmem1e]; exact hcode
      expr := by rw [hmem1e]; exact hsubexpr
      store := by rw [hmem1e]; exact hstore
      store_survives := by
        intro m' hag
        refine hstoreSurv m' (fun k hk1 => ?_)
        have hk1' : ¬ (SL.lo ≤ k ∧ k < (sp - 176#64).toNat) := by
          rw [hspsub]; intro ⟨ha, hb⟩; exact hk1 ⟨ha, by omega⟩
        have hk2' : ¬ (subsret.toNat ≤ k ∧ k < subsret.toNat + 24) := by
          intro ⟨ha, hb⟩; exact hk1 ⟨by omega, by omega⟩
        have := hag k hk1' hk2'
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

end Vsa.Sim
