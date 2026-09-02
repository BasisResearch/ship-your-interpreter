import Vsa.Sim.ArmSegSplitSqEntry
import Vsa.Sim.rows.LoopHeadDispatch

/-!
# `SeqHeadStages` — the `seqHead` supplier from `loopHeadDispatch_span` (Task #81 item 5)

`ArmSegSplitSqEntry.seqHead_split` closes the `seqHead` field of `ApproxArmResidGap`
MODULO the `SeqHeadStagePre` residual: from the sequence loop head
`SqEntryC Reflect c st d env (s :: ss)`, a ≥ 1-step run reaches a config carrying
`ExecEntry ... st d env s`.  `rows.LoopHeadDispatch.loopHeadDispatch_span` ALREADY
builds that machine run — the interp_run loop-head → `exec_stmt`-entry dispatch prefix
(dispatch head ≫ value_null ≫ arg-setup ≫ jal exec_stmt).  This file plugs the span
straight into the `SeqHeadStagePre` shape, so the `seqHead` field reduces to the
span's already-built inputs, closing item 5's "check seqHead_split's stage premise
first — it may close from loopHeadDispatch_span directly".

## Two impedance mismatches, both dischargeable at ZERO machine cost

1. **Depth is phantom.**  `loopHeadDispatch_span` concludes `ExecEntry g N A SL φf φc
   st 0 env s ...` (depth HARDCODED to `0`), while `SeqHeadStagePre` needs
   `ExecEntry ... st d env s` at the arm's arbitrary `d`.  But `ExecEntry`'s fields
   (`ExecEntry.lean:207–280`) reference `d` NOWHERE in any machine-state clause — the
   depth only rides inside `st`/`env`/`s` (all fixed here).  `execEntry_recast_depth`
   re-emits the same field proofs under any `d` (no `Config` re-run).

2. **`Steps` → counted `StepsN m` with `1 ≤ m`.**  The span gives `Steps cH cE`;
   `SeqHeadStagePre` wants `∃ m, 1 ≤ m ∧ StepsN m cH cE`.  Since `cE`'s PC
   (`execStmtEntry = 0x80003fe0`) differs from `cH`'s (`interpLoopHeadPC = 0x8000448c`),
   the run is provably non-empty: `stepsN_pos_of_pc_ne` cases the `Steps` (an empty
   `refl` would force equal PCs) and reads the count off `Steps.toN`.

The honest remaining residual is exactly `loopHeadDispatch_span`'s premises
(`LoopHeadDispatchGeom` + the `value_null` / arg-setup splices + the loop-head `sp`/`s0`
register pins that `SegEntry` does not project — see `observations.md`), shared with
the `driveToLoopHead` endgame.  This file adds ZERO machine steps.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats` bump.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
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
open Vsa.Sim.ApproxDispatchSuppliers (SqEntryC)

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) the ∃s here are reached-Config run bundles /
-- the landed `ExecEntry`/span predicates being re-packaged (consumed through their
-- own named suppliers, not positional chains); no NEW anonymous ∃/∧-tower post is
-- defined in this file.

local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

/-! ## §1. The two zero-cost recasts -/

/-- **`Steps` with distinct start/end PCs is a counted run of `≥ 1` step.**  An empty
`Steps` (`refl`) would identify the two configs, forcing equal PCs; so a PC
disagreement makes the run non-empty.  Reads the count off `Steps.toN`. -/
theorem stepsN_pos_of_pc_ne {cH cE : Config} {p q : BitVec 64}
    (hs : Steps cH cE)
    (hpcH : cH.σ.regs.get? Register.PC = some p)
    (hpcE : cE.σ.regs.get? Register.PC = some q)
    (hpq : p ≠ q) :
    ∃ m, 1 ≤ m ∧ StepsN m cH cE := by
  cases hs with
  | refl =>
    rw [hpcH] at hpcE
    exact absurd (Option.some.inj hpcE) hpq
  | @head a b c hstep hrest =>
    obtain ⟨n, hn⟩ := hrest.toN
    exact ⟨n + 1, Nat.le_add_left 1 n, StepsN.succ hstep hn⟩

/-- **`ExecEntry` depth recast.**  `ExecEntry` carries `d` only through `st`/`env`/`s`
(no machine-state field mentions the depth), so a proof at depth `d₀` re-emits under
any `d` by copying every field.  Used to lift `loopHeadDispatch_span`'s `d = 0`
conclusion to the arm's arbitrary `d`. -/
theorem execEntry_recast_depth
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (c : Config)
    (h : ExecEntry g N A SL φf φc st 0 env s sp r aInterp aStmt aEnv aRet m0 c) :
    ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0 c :=
  { good := h.good, tick := h.tick, pc := h.pc, a0 := h.a0, a1 := h.a1, a2 := h.a2,
    a3 := h.a3, ra := h.ra, ra_align := h.ra_align, spReg := h.spReg,
    stackOK := h.stackOK,
    -- The source at depth 0 carries the MAXIMUM budget `(maxCallDepth - 0)`;
    -- the target at depth `d` demands `(maxCallDepth - d) ≤ maxCallDepth`, so
    -- `StackOK.mono` discharges the recast.
    stackBudget := Vsa.Alloc.StackOK.mono
      (by
        have : (Vsa.While.maxCallDepth - d) ≤ (Vsa.While.maxCallDepth - 0) := by
          omega
        exact Nat.add_le_add_right (Nat.add_le_add_left
          (Nat.mul_le_mul_right _ this) _) _) h.stackBudget,
    stmt_bodies := h.stmt_bodies, store_bodies := h.store_bodies,
    minstret := h.minstret, mem := h.mem, code := h.code,
    stmt := h.stmt, store := h.store, store_survives := h.store_survives,
    out := h.out, frame := h.frame,
    code_stack_disjoint := h.code_stack_disjoint, stack_ram := h.stack_ram,
    stack_win := h.stack_win, stmt_stack_disjoint := h.stmt_stack_disjoint,
    stmt_align := h.stmt_align, stmt_ram := h.stmt_ram, stmt_win := h.stmt_win,
    spill_defined := h.spill_defined }

#print axioms execEntry_recast_depth

/-! ## §2. `seqHeadStagePre_of_span` — the `SeqHeadStagePre` supplier

`SeqHeadStagePre Reflect s ss c st d env` says: given `SqEntryC Reflect c st d env
(s :: ss)`, there is a config `cE` reached in `≥ 1` step carrying `ExecEntry ... st d
env s`.  We supply it from `loopHeadDispatch_span`.  The span's premises come in
two families, packaged as `hRegs` (the loop-head `sp`/`s0`/`mem` register pins the
`SegEntry` half does not project) and `hSpan` (the geometry + call splices that are
the honest `driveToLoopHead` residual).  Both are keyed on the `SqEntryC` witness
`c` so the caller threads them once per arm. -/

/-- **The `seqHead` staging residual, supplied from `loopHeadDispatch_span`.**  A
provider of the span's inputs (loop-head register pins + geometry/splice premises)
for the config `c` yields `SeqHeadStagePre Reflect s ss c st d env`.  Every clause
is `loopHeadDispatch_span`'s own hypothesis; this theorem only marshals the span's
`Steps`/`ExecEntry` conclusion into the `SeqHeadStagePre` shape (count via
`stepsN_pos_of_pc_ne`, depth via `execEntry_recast_depth`). -/
theorem seqHeadStagePre_of_span
    (Reflect : Config → Addr → List Stmt → Prop)
    (s : Stmt) (ss : List Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (hSpan : SqEntryC Reflect c st d env (s :: ss) →
      ∃ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (sp s0 aStmt aEnv aInterp aRet : BitVec 64) (m0 mE : Mem),
        -- loop-head control/register pins (SegEntry half + the sp/s0 pins it lacks):
        (GoodState c.σ ∧ c.tick < 2 ∧
          c.σ.regs.get? Register.PC = some (0x8000448c#64 : BitVec 64) ∧
          c.σ.mem = m0 ∧
          c.σ.regs.get? Register.x2 = some sp ∧
          c.σ.regs.get? Register.x8 = some s0 ∧
          (∃ w, c.σ.regs.get? Register.minstret = some w)) ∧
        -- the geometry + splices `loopHeadDispatch_span` demands:
        LoopHeadDispatchGeom g N A SL φf φc st sp aStmt s mE ∧
        (ChainFacts c.σ.mem c.σ.mem (loopHeadDispatchL sp s0) [] loopHeadDispatchSeg) ∧
        (∀ (c458 : Config),
          c458.σ.regs.get? Register.PC = some (0x80004458#64 : BitVec 64) →
          GoodState c458.σ → c458.tick < 2 →
          (∃ w, c458.σ.regs.get? Register.minstret = some w) →
          ValueNullSplice c458) ∧
        (∀ (c460 : Config),
          c460.σ.regs.get? Register.PC = some (0x80004460#64 : BitVec 64) →
          GoodState c460.σ → c460.tick < 2 →
          (∃ w, c460.σ.regs.get? Register.minstret = some w) →
          ∃ (cE : Config),
            Steps c460 cE ∧
            cE.σ.regs.get? Register.PC = some (0x80003fe0#64 : BitVec 64) ∧
            cE.σ.regs.get? Register.x1 = some (0x80004478#64 : BitVec 64) ∧
            cE.σ.regs.get? Register.x10 = some aInterp ∧
            cE.σ.regs.get? Register.x11 = some aStmt ∧
            cE.σ.regs.get? Register.x12 = some aEnv ∧
            cE.σ.regs.get? Register.x13 = some aRet ∧
            cE.σ.regs.get? Register.x2 = some sp ∧
            GoodState cE.σ ∧ cE.tick < 2 ∧
            cE.σ.mem = mE ∧
            (∃ w, cE.σ.regs.get? Register.minstret = some w) ∧
            (∀ R : Register, AbiPreservedNoise R → cE.σ.regs.get? R = g R) ∧
            OutRepr cE.σ st ∧
            (∃ v, cE.σ.regs.get? Register.x8 = some v) ∧
            (∃ v, cE.σ.regs.get? Register.x9 = some v) ∧
            (∃ v, cE.σ.regs.get? Register.x18 = some v) ∧
            (∃ v, cE.σ.regs.get? Register.x19 = some v))) :
    SeqHeadStagePre Reflect s ss c st d env := by
  intro hSq
  obtain ⟨g, N, A, SL, φf, φc, sp, s0, aStmt, aEnv, aInterp, aRet, m0, mE,
    ⟨hGH, htickH, hpcH, hmemH, hspH, hs0H, hmiH⟩, hGeom, hDispatchFacts,
    hValueNullSplice, hArgSetup⟩ := hSpan hSq
  -- run the built span; it lands at `exec_stmt`'s entry carrying `ExecEntry ... 0 ...`
  obtain ⟨cE, hsteps, hEntry⟩ :=
    loopHeadDispatch_span c g N A SL φf φc st env sp s0 aStmt aEnv aInterp aRet s m0 mE
      hGH htickH hpcH hmemH hspH hs0H hmiH hDispatchFacts hGeom hValueNullSplice hArgSetup
  -- the landing PC (0x80003fe0) differs from the loop head (0x8000448c) ⇒ ≥ 1 step
  have hpcE : cE.σ.regs.get? Register.PC = some (BitVec.ofNat 64 execStmtEntry) := hEntry.pc
  have hcount : ∃ m, 1 ≤ m ∧ StepsN m c cE :=
    stepsN_pos_of_pc_ne hsteps hpcH hpcE (by
      show (0x8000448c#64 : BitVec 64) ≠ BitVec.ofNat 64 execStmtEntry
      decide)
  -- recast the phantom depth 0 → d and re-pack the ExecEntry ghosts
  exact ⟨cE, hcount,
    ⟨g, N, A, SL, φf, φc, sp, (0x80004478#64), aInterp, aStmt, aEnv, aRet, mE,
      execEntry_recast_depth g N A SL φf φc st d env s sp (0x80004478#64)
        aInterp aStmt aEnv aRet mE cE hEntry⟩⟩

#print axioms seqHeadStagePre_of_span

end Vsa.Sim
