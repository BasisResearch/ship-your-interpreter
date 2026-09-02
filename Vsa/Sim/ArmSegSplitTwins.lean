import Vsa.Sim.ArmSegSplitNonEval
import Vsa.Sim.ArmSegSplitExecEval

/-!
# `ArmSegSplitTwins` — the bridge twins for the remaining non-eval child fields (Wave 44)

The wave-43 lane machine-checked (observations `nonevalchild-remaining-8-shape-map`,
`ifstmt-then-else-tail-redispatch-not-jal`) that 8 of the 11 `NonEvalChildStages`
fields plus `flStep` do NOT fit the landed pre-bundles.  This file builds the three
bridge twins that carry the honest machine shapes:

* **§1 (twin 1 — tail re-dispatch).**  The `.ifStmt` then/else arms reach the child
  via `ld s0,16/24(s0); j/bnez 0x80004014` — a TAIL re-dispatch to the POST-PROLOGUE
  dispatch head in the SAME `exec_stmt` frame, never a fresh `jal exec_stmt`.
  `SEntryC` (via `ExecEntry.pc`) hard-pins the child entry PC at `execStmtEntry =
  0x80003fe0`, which the tail route never revisits — the frozen `ApproxArmResid`
  field CONCLUSION `LandedN 1 c (SEntryC · st' d env t)` is therefore
  machine-unreachable on the if-arms.  The machine-checked obstruction core is
  `sEntryC_pins_entry_pc` / `sEntryC_false_at_dispatchHead` (§1.1).  The honest
  twin is `ExecDispatchEntry` (the named-field post-prologue dispatch-head entry at
  `execStmtDispatchHead = 0x80004014`) + `execEntry_of_jTailRedispatch` (§1.3), fed
  by the terminator-agnostic hop `GRegsHopInto` (§1.2, instantiable from `j`
  (`sigmaPost_jump_x0`) AND taken-branch (`sigmaPost_branch_taken`) site obs — the
  `bnez`-entered else arm rides the same twin).

  **AMENDMENT PLAN (reported, not applied — not signature-free):** re-seat the
  three tail fields on `SDispatchC`:
  - `ApproxArmReseat.SEntryC` → `∃ …, ExecEntry … ∨ ExecDispatchEntry …` (or the
    fold's `stmtIfThen`/`stmtIfElse` recursion target → `SDispatchC`), with
    `sEntryC_drives` supplying the fresh-call disjunct via the 14-instr prologue
    seg `0x80003fe0 → 0x80004010` (a `#derive_case` span, unbuilt).
  - `stmtWhileLoop` is the THIRD tail shape: `bne a0,a5,0x80004034` re-enters the
    WHILE-ARM head `0x80004034` (post-dispatch, not the dispatch head — no
    `a4`/`a6` re-materialization on that path), so its amended target is a
    while-arm entry (or the dispatch-head entry once the fold recursion is
    re-seated so the loop-back rides the arm-head block); NOT covered by
    `ExecDispatchEntry`.
  - Consumers to re-thread (grep `SEntryC`): `ArmStagesWave34` (29 refs, forbidden
    this wave), `ArmSegSplitEval` (27), `ArmSegSplitSqEntry` (14),
    `ArmSegSplitExecEval` (11), `ArmStagesPartial` (5), `ApproxArmResidGapAssembly`
    (2), rows `StmtWhileBody/StmtForInit/StmtExpr/StmtWhileCond/StmtVarInit/
    StmtRet/StmtIfCond` ArmStagePre files.

* **§2 (twin 2 — branch/fallthrough/jalr SegEntry entry).**  `SegPreBundle`
  hardcodes a static-`jal`-site premise (`callPC + jalImm = entryPC` + a
  `sigmaPost_jal` site), but `callArgs`/`argsTail`/`callC`/`stmtForLoop`/`flLoop`
  enter their interior control points by fallthrough/`j`/`jalr` — no jal targets
  them.  `SegPreBundleB` replaces the jal model with the terminator-agnostic
  one-step hop `StepInto` (any step landing at `entryPC` preserving mem/out —
  `j`, taken/not-taken branch, `jalr`, or plain fallthrough).  `SegPreBundle`
  strictly refines it (`segPreBundleB_of_jal`), and the five `*_splitB` theorems
  conclude the EXACT frozen `ApproxArmResid` field types (those are fine — the
  `AEntryC`/`CEntryC`/`FEntryC` bundles anchor on `SegEntry` at a GHOST interior
  PC, no jal pin).

* **§3 (twin 3 — `flStep_split'`).**  `flStep` evaluates the for-STEP expr via
  `jal eval_expr @0x800042e8` sited in `exec_stmt`'s text (the EXEC frame,
  sp-176), but `ArmSegSplitEval.flStep_split` hardcodes the eval-frame
  `JalPreBundle` (whose `hjalSite` is `Eval_exprLoaded`-typed — the falsity-#7
  class, wave-40 precedent).  `flStep_split'` is the exec-frame twin typed to
  `ExecJalPreBundle`, finishing through `execEvalEntry_of_jalPrefix`; its
  conclusion is the exact `ApproxArmResid.flStep` field type.  The
  `ArmStages.flStep` STAGING premise (`ApproxArmResidGapAssembly`) is still
  `JalPreBundle`-typed; re-typing it to `ExecJalPreBundle` breaks
  `armStages_mk`/`divFamily_of_armStageComponents`/`divFamily_wave34/40/42`
  premise types (not signature-free) — the wave-45 assembly consumes
  `flStep_split'` directly when building `ApproxArmResidGap`.

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
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr
  EvalE EvalArgs ForCond ExecInit ExecStep ExecS)
open Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.Scaffold (SegEntry)
open Vsa.Sim.ApproxArmReseat

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

/-! ## §1.1. The tail-re-dispatch obstruction core (Law 4, machine-checked)

`SEntryC` demands a full `ExecEntry`, whose `pc` field literally pins
`execStmtEntry = 0x80003fe0`.  The if-then arm's actual terminator is
`j 0x80004014` (word `0xde5ff06f @ 0x80004230`), the else arm's is
`bnez s0,0x80004014` (`@ 0x800042d0`): both land at the post-prologue dispatch
head, and the child re-dispatch never revisits `0x80003fe0` (a fresh `jal
exec_stmt` with the CHILD node happens only for grandchildren).  So any config on
the tail route fails `SEntryC` — pinned here once, decidably. -/

/- `execStmtDispatchHead` / `ExecDispatchEntry` / `SDispatchC` MOVED UPSTREAM to
`Vsa/Sim/ApproxArmReseat.lean` (wave-45 dedup): the amended 3-way `SEntryC`
disjunction needs them at its own def site.  This file consumes them through
`open Vsa.Sim.ApproxArmReseat`. -/

/-- **`SFreshC` pins the entry PC** (wave-45 RESTATEMENT of the obstruction
destructurer over the fresh-call disjunct: the amended `SEntryC` no longer pins
a single PC — exactly the amendment's point).  Any `SFreshC` config sits AT
`execStmtEntry`.  Name kept from the pre-amendment statement (check_all). -/
theorem sEntryC_pins_entry_pc (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (s : Stmt) (h : SFreshC c st d env s) :
    c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 execStmtEntry) := by
  obtain ⟨g, N, A, SL, φf, φc, sp, r, aI, aS, aE, aR, m0, hE⟩ := h
  exact hE.pc

/-- **The obstruction core** (wave-45 RESTATEMENT over `SFreshC`): a config at
the dispatch head (`0x80004014`, where the tail re-dispatch of
`stmtIfThen`/`stmtIfElse` actually lands) can NEVER satisfy the FRESH-call
entry — this is the machine fact that forced the `SEntryC` 3-way amendment
(the amended `SEntryC` reaches such configs via its `SDispatchC` disjunct). -/
theorem sEntryC_false_at_dispatchHead (c : Config) (st : SpecSt) (d : Nat)
    (env : Addr) (s : Stmt)
    (hpc : c.σ.regs.get? Register.PC =
      some (BitVec.ofNat 64 execStmtDispatchHead)) :
    ¬ SFreshC c st d env s := by
  intro h
  have h2 := sEntryC_pins_entry_pc c st d env s h
  rw [hpc] at h2
  exact absurd (Option.some.inj h2) (by decide)

#print axioms sEntryC_false_at_dispatchHead

/-! ## §1.2. The terminator-agnostic hops

`StepInto` — ONE machine step lands at a target PC preserving mem/out (all the
light `SegEntry` needs).  `GRegsHopInto` strengthens it with the non-noise
register frame (what the rich dispatch-head entry needs).  Both are instantiable
from the three terminator obs classes (`sigmaPost_jump_x0`,
`sigmaPost_branch_taken`, `sigmaPost_branch_nottaken`) via the `BlockTerm`
`pc_*_bt`/`mi_*_bt`/`frame_term_*_bt` consumers — and from a `jal` site obs
(`segPreBundleB_of_jal` below), so the jal model is a strict special case. -/

/-- **One step into `tgtPC`, mem/out-preserving.**  The light hop: what a
`SegEntry` landing needs from its entry step (`good`/`tick`/`pc`/`mem`/`out`),
with the terminator class abstracted away. -/
def StepInto (tgtPC : Nat) (σ : MState) : Prop :=
  ∀ (i u : Nat), i < 2 →
    ∃ (σ1 : MState) (i1 : Nat),
      Step ⟨σ, i, u⟩ ⟨σ1, i1, u + 1⟩ ∧ i1 < 2 ∧ GoodState σ1 ∧ σ1.mem = σ.mem ∧
      σ1.regs.get? Register.PC = some (BitVec.ofNat 64 tgtPC) ∧
      (∃ w, σ1.regs.get? Register.minstret = some w) ∧
      σ1.sailOutput = σ.sailOutput

/-- **One step into `tgtPC`, mem/out/GPR-preserving.**  The rich hop: `StepInto`
plus the full non-noise register frame (a terminator writes no GPR, so `j`/taken
`bnez`/`bne` all satisfy it — via `frame_term_*_bt`). -/
def GRegsHopInto (tgtPC : Nat) (σ : MState) : Prop :=
  ∀ (i u : Nat), i < 2 →
    ∃ (σ1 : MState) (i1 : Nat),
      Step ⟨σ, i, u⟩ ⟨σ1, i1, u + 1⟩ ∧ i1 < 2 ∧ GoodState σ1 ∧ σ1.mem = σ.mem ∧
      σ1.regs.get? Register.PC = some (BitVec.ofNat 64 tgtPC) ∧
      (∃ w, σ1.regs.get? Register.minstret = some w) ∧
      σ1.sailOutput = σ.sailOutput ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        σ1.regs.get? R = σ.regs.get? R)

/-- The rich hop is a light hop. -/
theorem StepInto.of_gregsHop {tgtPC : Nat} {σ : MState}
    (h : GRegsHopInto tgtPC σ) : StepInto tgtPC σ := by
  intro i u hi
  obtain ⟨σ1, i1, hs, hi1, hG1, hmem1, hpc1, hmi1, hout1, _⟩ := h i u hi
  exact ⟨σ1, i1, hs, hi1, hG1, hmem1, hpc1, hmi1, hout1⟩

/-- **`j`-site ⇒ rich hop.**  A `sigmaPost_jump_x0` site obs (the `#derive_case`
`TKind.j` class) at `σ` instantiates `GRegsHopInto tgt` — PC via `pc_jx0_bt`,
minstret via `mi_jx0_bt`, register frame via `frame_term_jx0_bt`, out via
`sailOutput_sigmaPost_jump_x0`. -/
theorem gregsHopInto_of_jx0Site (tgtPC : Nat) (σ : MState) (jPC vmi : BitVec 64)
    (hmi : σ.regs.get? Register.minstret = some vmi)
    (hsite : ∀ (i u : Nat), i < 2 →
      ∃ (σ1 : MState) (i1 : Nat),
        Step ⟨σ, i, u⟩ ⟨σ1, i1, u + 1⟩ ∧ i1 < 2 ∧ GoodState σ1 ∧ σ1.mem = σ.mem ∧
        ReadsLikePost σ1 (sigmaPost_jump_x0 σ jPC vmi (BitVec.ofNat 64 tgtPC))) :
    GRegsHopInto tgtPC σ := by
  intro i u hi
  obtain ⟨σ1, i1, hs, hi1, hG1, hmem1, hobs⟩ := hsite i u hi
  refine ⟨σ1, i1, hs, hi1, hG1, hmem1, pc_jx0_bt hobs, mi_jx0_bt hobs, ?_,
    fun R hn => frame_term_jx0_bt hobs R hn⟩
  rw [hobs.out, sailOutput_sigmaPost_jump_x0]

/-- **Taken-branch site ⇒ rich hop.**  A `sigmaPost_branch_taken` site obs whose
target arithmetic lands at `tgtPC` (the `bnez s0,0x80004014` else route and the
`bne a0,a5,…` loop-backs) instantiates `GRegsHopInto tgt`. -/
theorem gregsHopInto_of_branchTakenSite (tgtPC : Nat) (σ : MState)
    (bPC vmi : BitVec 64) (imm : BitVec 13)
    (htgt : bPC + sign_extend (m := 64) imm = BitVec.ofNat 64 tgtPC)
    (hmi : σ.regs.get? Register.minstret = some vmi)
    (hsite : ∀ (i u : Nat), i < 2 →
      ∃ (σ1 : MState) (i1 : Nat),
        Step ⟨σ, i, u⟩ ⟨σ1, i1, u + 1⟩ ∧ i1 < 2 ∧ GoodState σ1 ∧ σ1.mem = σ.mem ∧
        ReadsLikePost σ1 (sigmaPost_branch_taken σ bPC vmi imm)) :
    GRegsHopInto tgtPC σ := by
  intro i u hi
  obtain ⟨σ1, i1, hs, hi1, hG1, hmem1, hobs⟩ := hsite i u hi
  refine ⟨σ1, i1, hs, hi1, hG1, hmem1, ?_, mi_btaken_bt hobs, ?_,
    fun R hn => frame_term_btaken_bt hobs R hn⟩
  · have := pc_btaken_bt hobs; rwa [htgt] at this
  · rw [hobs.out, sailOutput_sigmaPost_branch_taken]

/-- **`jalr`-site ⇒ light hop.**  A `sigmaPost_jalr` site obs whose bit-0-cleared
indirect target is `tgtPC` (the closure-dispatch callee-body entry of `callC`)
instantiates `StepInto tgtPC`.  `jalr` WRITES its link register, so only the
light (GPR-free) hop holds — exactly what `SegPreBundleB` needs. -/
theorem stepInto_of_jalrSite (tgtPC : Nat) (σ : MState) (jrPC vmi : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (hmi : σ.regs.get? Register.minstret = some vmi)
    (hsite : ∀ (i u : Nat), i < 2 →
      ∃ (σ1 : MState) (i1 : Nat),
        Step ⟨σ, i, u⟩ ⟨σ1, i1, u + 1⟩ ∧ i1 < 2 ∧ GoodState σ1 ∧ σ1.mem = σ.mem ∧
        ReadsLikePost σ1
          (sigmaPost_jalr σ jrPC vmi (BitVec.ofNat 64 tgtPC) rd_reg link)) :
    StepInto tgtPC σ := by
  intro i u hi
  obtain ⟨σ1, i1, hs, hi1, hG1, hmem1, hobs⟩ := hsite i u hi
  refine ⟨σ1, i1, hs, hi1, hG1, hmem1, ?_, ?_, hobs.out⟩
  · exact readback σ1 _ hobs Register.PC (by decide) (by decide) (by decide)
      (by
        show ((((sigma3_jalr σ jrPC (BitVec.ofNat 64 tgtPC) rd_reg link).regs.insert
            Register.PC (BitVec.ofNat 64 tgtPC)).insert Register.minstret
            (BitVec.addInt vmi 1))).get? Register.PC = _
        rw [Std.ExtDHashMap.get?_insert]
        simp only [show (Register.minstret == Register.PC) = false from by decide,
          dif_neg, reduceCtorEq, not_false_eq_true]
        rw [Std.ExtDHashMap.get?_insert_self])
  · refine ⟨BitVec.addInt vmi 1, readback σ1 _ hobs Register.minstret
      (w := BitVec.addInt vmi 1) (by decide) (by decide) (by decide) ?_⟩
    show ((((sigma3_jalr σ jrPC (BitVec.ofNat 64 tgtPC) rd_reg link).regs.insert
        Register.PC (BitVec.ofNat 64 tgtPC)).insert Register.minstret
        (BitVec.addInt vmi 1))).get? Register.minstret = _
    rw [Std.ExtDHashMap.get?_insert_self]

#print axioms gregsHopInto_of_jx0Site
#print axioms gregsHopInto_of_branchTakenSite
#print axioms stepInto_of_jalrSite

/-! ## §1.3. `ExecDispatchEntry` — the honest tail-re-dispatch child entry

The post-prologue dispatch-head state at `0x80004014`: the child statement staged
in the SAME frame (`s0 = aStmt` — the tail route reloads it from the parent node;
`s1`/`s3`/`s2` still carry interp/env/retslot from the prologue), the jump-table
base re-materialized (`a4 = stmtJumpTableBase`, `a6 = 8` — the if-arm re-executes
`li a6,8; auipc/addi a4` at `0x8000421c..0x80004224` before its terminator), `sp`
ALREADY lowered (`stackOK … 1088`: the exec frame is live, only the eval headroom
remains).  Mirrors `ExecEntry` minus the call-boundary fields (`a0-a3`/`ra`: the
frame's `ra` slot belongs to the PARENT call and is untouched by the tail). -/

/- `ExecDispatchEntry` / `SDispatchC` formerly defined HERE — MOVED UPSTREAM to
`Vsa/Sim/ApproxArmReseat.lean` (wave-45 dedup, the amended `SEntryC`'s second
disjunct).  Consumed below through `open Vsa.Sim.ApproxArmReseat`. -/

/-- **The tail-re-dispatch marshalling twin** (of `execEntry_of_jalPrefix`).

From a config `c` at the arm's tail terminator (the `j 0x80004014` / taken
`bnez … 0x80004014`) with the CHILD node already reloaded into `s0` and the
dispatch registers re-materialized, ONE terminator step lands at the child's
`ExecDispatchEntry` — same frame, no fresh jal, no prologue. -/
theorem execEntry_of_jTailRedispatch
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt)
    (spD aInterp aStmt aEnv aRet : BitVec 64)
    (out0 : Array String) (mcall : Mem)
    (c : Config)
    (hhop : GRegsHopInto execStmtDispatchHead c.σ)
    (hpre :
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.x8 = some aStmt ∧
        c.σ.regs.get? Register.x9 = some aInterp ∧
        c.σ.regs.get? Register.x18 = some aRet ∧
        c.σ.regs.get? Register.x19 = some aEnv ∧
        c.σ.regs.get? Register.x16 = some (8#64) ∧
        c.σ.regs.get? Register.x14 = some (BitVec.ofNat 64 stmtJumpTableBase) ∧
        c.σ.regs.get? Register.x2 = some spD ∧
        c.σ.sailOutput = out0 ∧
        String.join out0.toList = st.out ∧
        c.σ.mem = mcall ∧
        Exec_stmtLoaded mcall ∧
        StmtRepr mcall aStmt.toNat s ∧
        StoreRepr mcall N A φf φc st.store ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mcall[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        aStmt.toNat % 8 = 0 ∧
        0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aStmt.toNat ∧
        (aStmt.toNat + 16 ≤ SL.lo ∨ spD.toNat ≤ aStmt.toNat) ∧
        StackOK SL spD 1088 ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        (spD.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo)) :
    LandedN 1 c (fun c' =>
      ExecDispatchEntry (fun R => c'.σ.regs.get? R) N A SL φf φc st d env s
        spD aInterp aStmt aEnv aRet mcall c') := by
  obtain ⟨hG, htick, hs0, hs1, hs2, hs3, ha6, ha4, hsp,
    hout, houtStr, hmemc, hcodeS, hstmtR, hstore, hstoreSurv,
    hstAl, hstLo, hstHi, hstWin, hstStk, hstackOK,
    hSLlo, hSLhiRam, hSLwin, hcodeStk⟩ := hpre
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hpc1, hmi1, hout1, hfr1⟩ :=
    hhop c.tick c.steps htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = mcall := by rw [hmem1]; exact hmemc
  refine ⟨1, ⟨σ1, i1, c.steps + 1⟩, Nat.le_refl _,
    StepsN.succ hstep1 (StepsN.zero _), ?_⟩
  · exact
      { good := hG1
        tick := hi1
        pc := hpc1
        s0 := (hfr1 Register.x8 (by decide)).trans hs0
        s1 := (hfr1 Register.x9 (by decide)).trans hs1
        s2 := (hfr1 Register.x18 (by decide)).trans hs2
        s3 := (hfr1 Register.x19 (by decide)).trans hs3
        a6 := (hfr1 Register.x16 (by decide)).trans ha6
        a4 := (hfr1 Register.x14 (by decide)).trans ha4
        spReg := (hfr1 Register.x2 (by decide)).trans hsp
        stackOK := hstackOK
        minstret := hmi1
        mem := hmem1e
        code := by show Exec_stmtLoaded σ1.mem; rw [hmem1e]; exact hcodeS
        stmt := by show StmtRepr σ1.mem aStmt.toNat s; rw [hmem1e]; exact hstmtR
        store := by
          show StoreRepr σ1.mem N A φf φc st.store; rw [hmem1e]; exact hstore
        store_survives := by
          intro m' hag
          refine hstoreSurv m' (fun k hk1 => ?_)
          have := hag k hk1
          rw [hmem1e] at this; exact this
        out := by
          show Machine.output σ1 = st.out
          simp only [Vsa.Machine.output]; rw [hout1, hout]; exact houtStr
        frame := fun _ _ => rfl
        code_stack_disjoint := hcodeStk
        stack_ram := ⟨hSLlo, hSLhiRam⟩
        stack_win := hSLwin
        stmt_stack_disjoint := hstStk
        stmt_align := hstAl
        stmt_ram := ⟨hstLo, hstHi⟩
        stmt_win := hstWin }

#print axioms execEntry_of_jTailRedispatch

-- discipline: allow(R7-conj-tower-def) `ExecStmtTailPreBundle` is the SANCTIONED
-- ∃-ghost LANDING BUNDLE for the tail twin (same precedent as `ExecStmtPreBundle`);
-- carries layout DATA a `structure : Prop` cannot project.  Its named destructurer
-- is `landedN_sDispatchC_of_preBundle`.
/-- **The tail twin's PRE-bundle, as a config predicate over the child statement
`s`.**  State at the arm's tail terminator with the child reloaded and the
dispatch registers staged — the `ExecStmtPreBundle` counterpart for arms with NO
fresh `jal exec_stmt`.  The staging suppliers for the (amended) `stmtIfThen`/
`stmtIfElse` fields land HERE. -/
def ExecStmtTailPreBundle (s : Stmt) (c' : Config) (st : SpecSt) (d : Nat)
    (env : Addr) : Prop :=
  ∃ (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (spD aInterp aStmt aEnv aRet : BitVec 64)
    (out0 : Array String) (mcall : Mem),
    GRegsHopInto execStmtDispatchHead c'.σ ∧
    GoodState c'.σ ∧ c'.tick < 2 ∧
    c'.σ.regs.get? Register.x8 = some aStmt ∧
    c'.σ.regs.get? Register.x9 = some aInterp ∧
    c'.σ.regs.get? Register.x18 = some aRet ∧
    c'.σ.regs.get? Register.x19 = some aEnv ∧
    c'.σ.regs.get? Register.x16 = some (8#64) ∧
    c'.σ.regs.get? Register.x14 = some (BitVec.ofNat 64 stmtJumpTableBase) ∧
    c'.σ.regs.get? Register.x2 = some spD ∧
    c'.σ.sailOutput = out0 ∧
    String.join out0.toList = st.out ∧
    c'.σ.mem = mcall ∧
    Exec_stmtLoaded mcall ∧
    StmtRepr mcall aStmt.toNat s ∧
    StoreRepr mcall N A φf φc st.store ∧
    (∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mcall[k]? = m'[k]?) →
      StoreRepr m' N A φf φc st.store) ∧
    aStmt.toNat % 8 = 0 ∧
    0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 16 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ aStmt.toNat ∧
    (aStmt.toNat + 16 ≤ SL.lo ∨ spD.toNat ≤ aStmt.toNat) ∧
    StackOK SL spD 1088 ∧
    0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
    (spD.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo)

/-- **The tail pre-bundle drives into `SDispatchC`.**  One terminator step, via
`execEntry_of_jTailRedispatch`, then the layout ghosts wrap existentially.  The
`SDispatchC` counterpart of `landedN_sEntryC_of_preBundle`. -/
theorem landedN_sDispatchC_of_preBundle
    (s : Stmt) (c' : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (h : ExecStmtTailPreBundle s c' st d env) :
    LandedN 1 c' (fun c'' => SDispatchC c'' st d env s) := by
  obtain ⟨N, A, SL, φf, φc, spD, aInterp, aStmt, aEnv, aRet, out0, mcall,
    hhop, hrest⟩ := h
  have hDE := execEntry_of_jTailRedispatch N A SL φf φc st d env s
    spD aInterp aStmt aEnv aRet out0 mcall c' hhop hrest
  exact LandedN.weaken hDE (fun c'' hEntry =>
    ⟨fun R => c''.σ.regs.get? R, N, A, SL, φf, φc,
      spD, aInterp, aStmt, aEnv, aRet, mcall, hEntry⟩)

#print axioms landedN_sDispatchC_of_preBundle

/-- **Generic tail-child split** — the `execChildSplit_of_stage` counterpart for
the tail route, targeting `SDispatchC` (the AMENDED field shape; consumable once
the `SEntryC` amendment lands). -/
theorem execTailChildSplit_of_stage
    (child : Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (hstaged : LandedN 1 c (fun c' => ExecStmtTailPreBundle child c' st d env)) :
    LandedN 1 c (fun c' => SDispatchC c' st d env child) :=
  LandedN.weakenCount (by omega : 1 ≤ 1 + 1)
    (LandedN.bind hstaged
      (fun c' hpb => landedN_sDispatchC_of_preBundle child c' st d env hpb))

#print axioms execTailChildSplit_of_stage

/-- **`stmtIfThen` tail split (amended-shape).**  Exactly `stmtIfThen_split` with
the conclusion re-seated on `SDispatchC` — the machine-true statement the
amendment plan adopts for the `.ifStmt` then arm. -/
theorem stmtIfThen_splitT (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config)
    (st st' : SpecSt) (d : Nat) (env : Addr) (v : Value)
    (hstage : EvalE st d env cnd st' v → v.truthy = true →
      SEntryC c st d env (.ifStmt cnd t e) →
      LandedN 1 c (fun c' => ExecStmtTailPreBundle t c' st' d env)) :
    EvalE st d env cnd st' v → v.truthy = true →
    SEntryC c st d env (.ifStmt cnd t e) →
    LandedN 1 c (fun c' => SDispatchC c' st' d env t) :=
  fun hE ht hSE => execTailChildSplit_of_stage t c st' d env (hstage hE ht hSE)

#print axioms stmtIfThen_splitT

/-- **`stmtIfElse` tail split (amended-shape).**  The else arm rides the SAME
twin via its taken-`bnez` hop (`gregsHopInto_of_branchTakenSite`). -/
theorem stmtIfElse_splitT (cnd : Expr) (t e : Stmt) (c : Config)
    (st st' : SpecSt) (d : Nat) (env : Addr) (v : Value)
    (hstage : EvalE st d env cnd st' v → v.truthy = false →
      SEntryC c st d env (.ifStmt cnd t (some e)) →
      LandedN 1 c (fun c' => ExecStmtTailPreBundle e c' st' d env)) :
    EvalE st d env cnd st' v → v.truthy = false →
    SEntryC c st d env (.ifStmt cnd t (some e)) →
    LandedN 1 c (fun c' => SDispatchC c' st' d env e) :=
  fun hE hf hSE => execTailChildSplit_of_stage e c st' d env (hstage hE hf hSE)

#print axioms stmtIfElse_splitT

/-! ## §2. `SegPreBundleB` — the terminator-agnostic SegEntry pre-bundle

`SegPreBundle`'s jal-site model (`callPC + jalImm = entryPC` + `sigmaPost_jal`)
does not match the interior entries of `callArgs`/`argsTail`/`callC`/
`stmtForLoop`/`flLoop` (fallthrough/`j`/`jalr` targets — no static jal aims at
them).  `SegPreBundleB` carries the light hop `StepInto` instead; everything a
`SegEntry` needs survives ANY mem/out-preserving step. -/

-- discipline: allow(R7-conj-tower-def) `SegPreBundleB` is the SANCTIONED ∃-ghost
-- LANDING BUNDLE variant of `SegPreBundle` (same precedent); consumers go through
-- the named destructurers below.
/-- **The terminator-agnostic SegEntry PRE-bundle.**  `SegPreBundle` with the
static-jal-site premise replaced by the abstract one-step hop `StepInto entryPC`
(satisfiable by `j`/branch/`jalr`/fallthrough site obs — and by the jal model,
`segPreBundleB_of_jal`). -/
def SegPreBundleB (entryPC : Nat) (c' : Config) (st : SpecSt)
    (d dLeft aLeft : Nat) : Prop :=
  ∃ (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat) (mcall : Mem),
    StepInto entryPC c'.σ ∧
    GoodState c'.σ ∧ c'.tick < 2 ∧
    c'.σ.mem = mcall ∧
    Exec_stmtLoaded mcall ∧
    StoreRepr mcall N A φf φc st.store ∧
    Machine.output c'.σ = st.out ∧
    d + dLeft = Vsa.While.maxCallDepth ∧
    A.lo + aLeft ≤ A.hi

/-- **The jal model is a strict special case**: every `SegPreBundle` is a
`SegPreBundleB` (the jal step IS a mem/out-preserving step into its target). -/
theorem segPreBundleB_of_jal (entryPC : Nat) (c' : Config) (st : SpecSt)
    (d dLeft aLeft : Nat)
    (h : SegPreBundle entryPC c' st d dLeft aLeft) :
    SegPreBundleB entryPC c' st d dLeft aLeft := by
  obtain ⟨N, A, SLb, φf, φc, callPC, jalImm, mcall, hjaltgt, hjalSite,
    hG, htick, hpc, ⟨w, hmi⟩, hmemc, hcodeS, hstore, hout, hdepth, harena⟩ := h
  refine ⟨N, A, φf, φc, mcall, ?_, hG, htick, hmemc, hcodeS, hstore, hout,
    hdepth, harena⟩
  intro i u hi
  obtain ⟨σ1, i1, hs, hi1, hG1, hmem1, hobs⟩ :=
    hjalSite c'.σ i u w hG hpc hmi (hmemc ▸ hcodeS) hi
  refine ⟨σ1, i1, hs, hi1, hG1, hmem1, ?_, obs_jalT_minstret hobs, ?_⟩
  · have := obs_jalT_pc hobs; rwa [hjaltgt] at this
  · rw [hobs.out, sailOutput_sigmaPost_jal]

#print axioms segPreBundleB_of_jal

/-- **The B pre-bundle drives into a `SegEntry`** — the twin of
`landedN_segEntry_of_preBundle`, over the abstract hop. -/
theorem landedN_segEntry_of_preBundleB
    (entryPC : Nat) (c' : Config) (st : SpecSt) (d dLeft aLeft : Nat)
    (SL : StackLayout)
    (h : SegPreBundleB entryPC c' st d dLeft aLeft) :
    LandedN 1 c' (fun c'' =>
      ∃ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat) (m0 : Mem),
        SegEntry g N A SL φf φc st d dLeft aLeft entryPC m0 c'') := by
  obtain ⟨N, A, φf, φc, mcall, hhop, hG, htick, hmemc, hcodeS, hstore, hout,
    hdepth, harena⟩ := h
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hpc1, hmi1, hout1⟩ :=
    hhop c'.tick c'.steps htick
  have hstep1 : Step c' ⟨σ1, i1, c'.steps + 1⟩ := by cases c'; exact hs1'
  have hmem1e : σ1.mem = mcall := by rw [hmem1]; exact hmemc
  refine ⟨1, ⟨σ1, i1, c'.steps + 1⟩, Nat.le_refl _,
    StepsN.succ hstep1 (StepsN.zero _), ?_⟩
  · exact ⟨fun R => σ1.regs.get? R, N, A, φf, φc, mcall,
      { good := hG1
        tick := hi1
        pc := hpc1
        store := by
          show StoreRepr σ1.mem N A φf φc st.store; rw [hmem1e]; exact hstore
        out := by
          show Machine.output σ1 = st.out
          simp only [Vsa.Machine.output]; rw [hout1]
          simpa only [Vsa.Machine.output] using hout
        mem := hmem1e
        frame := fun _ _ => rfl
        depth_budget := hdepth
        arena_budget := harena }⟩

#print axioms landedN_segEntry_of_preBundleB

/-- **B pre-bundle ⇒ `AEntryC`** (twin of `landedN_aEntryC_of_preBundle`). -/
theorem landedN_aEntryC_of_preBundleB
    (es : List Expr) (argLoopPC : Nat) (c' : Config) (st : SpecSt)
    (d dLeft aLeft : Nat) (env : Addr) (SL : StackLayout)
    (h : SegPreBundleB argLoopPC c' st d dLeft aLeft) :
    LandedN 1 c' (fun c'' => AEntryC c'' st d env es) := by
  have hSE := landedN_segEntry_of_preBundleB argLoopPC c' st d dLeft aLeft SL h
  exact LandedN.weaken hSE (fun c'' hEntry => by
    obtain ⟨g, N', A', φf', φc', m0, hSeg⟩ := hEntry
    exact ⟨g, N', A', SL, φf', φc', dLeft, aLeft, argLoopPC, m0, hSeg⟩)

#print axioms landedN_aEntryC_of_preBundleB

/-- **B pre-bundle ⇒ `CEntryC`** (twin of `landedN_cEntryC_of_preBundle`). -/
theorem landedN_cEntryC_of_preBundleB
    (fv : Value) (vs : List Value) (calleeBodyPC : Nat) (c' : Config) (st : SpecSt)
    (d dLeft aLeft : Nat) (SL : StackLayout)
    (h : SegPreBundleB calleeBodyPC c' st d dLeft aLeft) :
    LandedN 1 c' (fun c'' => CEntryC c'' st d fv vs) := by
  have hSE := landedN_segEntry_of_preBundleB calleeBodyPC c' st d dLeft aLeft SL h
  exact LandedN.weaken hSE (fun c'' hEntry => by
    obtain ⟨g, N', A', φf', φc', m0, hSeg⟩ := hEntry
    exact ⟨g, N', A', SL, φf', φc', dLeft, aLeft, calleeBodyPC, m0, hSeg⟩)

#print axioms landedN_cEntryC_of_preBundleB

/-- **B pre-bundle ⇒ `FEntryC`** (twin of `landedN_fEntryC_of_preBundle`). -/
theorem landedN_fEntryC_of_preBundleB
    (cnd step : Option Expr) (b : Stmt) (forCondPC : Nat) (c' : Config)
    (st : SpecSt) (d dLeft aLeft : Nat) (env : Addr) (SL : StackLayout)
    (h : SegPreBundleB forCondPC c' st d dLeft aLeft) :
    LandedN 1 c' (fun c'' => FEntryC c'' st d env cnd step b) := by
  have hSE := landedN_segEntry_of_preBundleB forCondPC c' st d dLeft aLeft SL h
  exact LandedN.weaken hSE (fun c'' hEntry => by
    obtain ⟨g, N', A', φf', φc', m0, hSeg⟩ := hEntry
    exact ⟨g, N', A', SL, φf', φc', dLeft, aLeft, forCondPC, m0, hSeg⟩)

#print axioms landedN_fEntryC_of_preBundleB

/-! ### The generic B split combinators + the 5 field splits

Each `*_splitB` concludes the EXACT frozen `ApproxArmResid` field type (the
`AEntryC`/`CEntryC`/`FEntryC` conclusions are jal-free — only the STAGING bundle
changes), so the wave-45 assembly can feed them straight into the
`ApproxArmResidGap` literal in place of the jal-typed `*_split` outputs. -/

/-- Generic args-child split over the B bundle. -/
theorem argsChildSplit_of_stageB
    (es : List Expr) (argLoopPC : Nat) (c : Config) (st : SpecSt)
    (d dLeft aLeft : Nat) (env : Addr) (SL : StackLayout)
    (hstaged : LandedN 1 c (fun c' => SegPreBundleB argLoopPC c' st d dLeft aLeft)) :
    LandedN 1 c (fun c' => AEntryC c' st d env es) :=
  LandedN.weakenCount (by omega : 1 ≤ 1 + 1)
    (LandedN.bind hstaged
      (fun c' hpb => landedN_aEntryC_of_preBundleB es argLoopPC c' st d dLeft aLeft env SL hpb))

/-- Generic callee-child split over the B bundle. -/
theorem calleeChildSplit_of_stageB
    (fv : Value) (vs : List Value) (calleeBodyPC : Nat) (c : Config) (st : SpecSt)
    (d dLeft aLeft : Nat) (SL : StackLayout)
    (hstaged : LandedN 1 c (fun c' => SegPreBundleB calleeBodyPC c' st d dLeft aLeft)) :
    LandedN 1 c (fun c' => CEntryC c' st d fv vs) :=
  LandedN.weakenCount (by omega : 1 ≤ 1 + 1)
    (LandedN.bind hstaged
      (fun c' hpb => landedN_cEntryC_of_preBundleB fv vs calleeBodyPC c' st d dLeft aLeft SL hpb))

/-- Generic for-child split over the B bundle. -/
theorem forChildSplit_of_stageB
    (cnd step : Option Expr) (b : Stmt) (forCondPC : Nat) (c : Config)
    (st : SpecSt) (d dLeft aLeft : Nat) (env : Addr) (SL : StackLayout)
    (hstaged : LandedN 1 c (fun c' => SegPreBundleB forCondPC c' st d dLeft aLeft)) :
    LandedN 1 c (fun c' => FEntryC c' st d env cnd step b) :=
  LandedN.weakenCount (by omega : 1 ≤ 1 + 1)
    (LandedN.bind hstaged
      (fun c' hpb => landedN_fEntryC_of_preBundleB cnd step b forCondPC c' st d dLeft aLeft env SL hpb))

#print axioms argsChildSplit_of_stageB
#print axioms calleeChildSplit_of_stageB
#print axioms forChildSplit_of_stageB

/-- **`callArgs` field (B).**  The frozen `ApproxArmResid.callArgs` conclusion
from a fallthrough-entered staging (the post-f-eval arg-loop head). -/
theorem callArgs_splitB (f : Expr) (args : List Expr) (c : Config) (st st' : SpecSt)
    (d : Nat) (env : Addr) (fv : Value) (argLoopPC dLeft aLeft : Nat) (SL : StackLayout)
    (hstage : EvalE st d env f st' fv → EEntryC c st d env (.call f args) →
      LandedN 1 c (fun c' => SegPreBundleB argLoopPC c' st' d dLeft aLeft)) :
    EvalE st d env f st' fv → EEntryC c st d env (.call f args) →
    LandedN 1 c (fun c' => AEntryC c' st' d env args) :=
  fun hE hEE => argsChildSplit_of_stageB args argLoopPC c st' d dLeft aLeft env SL (hstage hE hEE)

#print axioms callArgs_splitB

/-- **`argsTail` field (B).**  The `j`-back arg-loop re-entry. -/
theorem argsTail_splitB (e : Expr) (es : List Expr) (c : Config) (st st' : SpecSt)
    (d : Nat) (env : Addr) (v : Value) (argLoopPC dLeft aLeft : Nat) (SL : StackLayout)
    (hstage : EvalE st d env e st' v → AEntryC c st d env (e :: es) →
      LandedN 1 c (fun c' => SegPreBundleB argLoopPC c' st' d dLeft aLeft)) :
    EvalE st d env e st' v → AEntryC c st d env (e :: es) →
    LandedN 1 c (fun c' => AEntryC c' st' d env es) :=
  fun hE hAE => argsChildSplit_of_stageB es argLoopPC c st' d dLeft aLeft env SL (hstage hE hAE)

#print axioms argsTail_splitB

/-- **`callC` field (B).**  The `jalr`-entered callee body head. -/
theorem callC_splitB (f : Expr) (args : List Expr) (c : Config) (st st' st'' : SpecSt)
    (d : Nat) (env : Addr) (fv : Value) (vs : List Value)
    (calleeBodyPC dLeft aLeft : Nat) (SL : StackLayout)
    (hstage : EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
      EEntryC c st d env (.call f args) →
      LandedN 1 c (fun c' => SegPreBundleB calleeBodyPC c' st'' d dLeft aLeft)) :
    EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
    EEntryC c st d env (.call f args) →
    LandedN 1 c (fun c' => CEntryC c' st'' d fv vs) :=
  fun hE hA hEE =>
    calleeChildSplit_of_stageB fv vs calleeBodyPC c st'' d dLeft aLeft SL (hstage hE hA hEE)

#print axioms callC_splitB

/-- **`stmtForLoop` field (B).**  The `j 0x8000426c` (post-init) / taken-`beqz`
(no-init) for-cond entry. -/
theorem stmtForLoop_splitB (init : Option Stmt) (cnd step : Option Expr) (b : Stmt)
    (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (store' : Store) (outer : Addr)
    (forCondPC dLeft aLeft : Nat) (SL : StackLayout)
    (hstage : st.store.allocFrame (some env) = (store', outer) →
      ExecInit ⟨store', st.out⟩ d outer init st' →
      SEntryC c st d env (.forStmt init cnd step b) →
      LandedN 1 c (fun c' => SegPreBundleB forCondPC c' st' d dLeft aLeft)) :
    st.store.allocFrame (some env) = (store', outer) →
    ExecInit ⟨store', st.out⟩ d outer init st' →
    SEntryC c st d env (.forStmt init cnd step b) →
    LandedN 1 c (fun c' => FEntryC c' st' d outer cnd step b) :=
  fun hAlloc hInit hSE =>
    forChildSplit_of_stageB cnd step b forCondPC c st' d dLeft aLeft outer SL
      (hstage hAlloc hInit hSE)

#print axioms stmtForLoop_splitB

/-- **`flLoop` field (B).**  The post-step `j 0x8000426c` for-cond re-entry. -/
theorem flLoop_splitB (cnd : Option Expr) (step : Option Expr) (b : Stmt)
    (c : Config) (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr) (status : Status)
    (forCondPC dLeft aLeft : Nat) (SL : StackLayout)
    (hstage : ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
      FEntryC c st d env cnd step b →
      LandedN 1 c (fun c' => SegPreBundleB forCondPC c' st''' d dLeft aLeft)) :
    ForCond st d env cnd st' → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
    FEntryC c st d env cnd step b →
    LandedN 1 c (fun c' => FEntryC c' st''' d env cnd step b) :=
  fun hFC hEx hst hStep hFE =>
    forChildSplit_of_stageB cnd step b forCondPC c st''' d dLeft aLeft env SL
      (hstage hFC hEx hst hStep hFE)

#print axioms flLoop_splitB

/-! ## §3. `flStep_split'` — the exec-frame flStep twin

The lone `flStep` field of `ApproxArmResid` (`... → FEntryC cnd (some e) b →
LandedN 1 (EEntryC e)`) with its staging re-typed to `ExecJalPreBundle` (the
`Exec_stmtLoaded`-sited jal seam, wave-40 falsity-#7 class) — the honest type for
the for-STEP arm's `jal eval_expr @0x800042e8` in the EXEC frame. -/

/-- **`flStep` field split (exec twin).**  Exactly `flStep_split` with the
staging residual landing at `ExecJalPreBundle` and
`execEvalChildSplit_of_stage` finishing. -/
theorem flStep_split' (cnd : Option Expr) (e : Expr) (b : Stmt) (status : Status)
    (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr)
    (hstage : ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → FEntryC c st d env cnd (some e) b →
      LandedN 1 c (fun c' => ExecJalPreBundle e c' st'' d env)) :
    ForCond st d env cnd st' → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → FEntryC c st d env cnd (some e) b →
    LandedN 1 c (fun c' => EEntryC c' st'' d env e) :=
  fun hFC hEx hst hFE =>
    execEvalChildSplit_of_stage e c st'' d env (hstage hFC hEx hst hFE)

#print axioms flStep_split'

end Vsa.Sim
