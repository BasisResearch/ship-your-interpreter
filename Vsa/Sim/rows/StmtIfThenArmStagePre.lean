import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.ArmSegSplitTwins

/-!
# `StmtIfThenArmStagePre` — the `.ifStmt` THEN-arm tail-re-dispatch staging
(Wave 44 pilot for `execEntry_of_jTailRedispatch`)

The `.ifStmt` then arm does NOT `jal exec_stmt` (observation
`ifstmt-then-else-tail-redispatch-not-jal`): after eval-cond + `value_truthy`, the
TRUE route re-materializes the dispatch registers and TAIL-re-dispatches to the
post-prologue head `0x80004014` in the SAME frame:

    8000421c:  li a6,8            -- kind bound
    80004220:  auipc a4,0x16      -- ┐ jump-table base
    80004224:  addi a4,a4,-616    -- ┘ a4 := 0x80019fb8 (stmtJumpTableBase)
    80004228:  beqz a0,0x800042cc -- NOT taken (truthy: a0 ≠ 0)
    8000422c:  ld s0,16(s0)       -- s0 := then-child node
    80004230:  j 0x80004014       -- TAIL re-dispatch (the twin's hop)

This file is the wave-44 PILOT riding twin 1 (`Vsa/Sim/ArmSegSplitTwins.lean`):

* §1 — the arm-head span `0x8000421c → 0x8000422c` as ONE 2-block `#derive_case`
  chain (mid-span not-taken `beqz` in-model), ending parked AT the `j` site
  `0x80004230`.  The seg MACHINE-COMPUTES `a4 = 0x80019fb8 = stmtJumpTableBase`
  and `a6 = 8` — discharging the `ExecDispatchEntry.a4`/`a6` staging by
  computation, and `s0 :=` the loaded then-child pointer.
* §2 — the `segToTriple` row (`stmtIfThenTailRow`), one kernel `ChainOK` `decide`.
* §3 — the obstruction tie-in `stmtIfThenTail_target_not_sEntryC`: the route's
  landing PC is the dispatch head, where `SEntryC` is REFUTED
  (`sEntryC_false_at_dispatchHead`) — the frozen `NonEvalChildStages.stmtIfThen`
  target `ExecStmtPreBundle` (fresh-jal model) is not this arm's machine shape.
* §4 — the named residuals (`IfThenArmHeadInv` / `IfThenTailStagePre` /
  `IfThenTailDispatch`, the wave-43 `ArgsHeadDispatch` shape) + the composer
  `stmtIfThen_tailField_of_dispatch` producing the AMENDED-shape field
  (`LandedN 1 (ExecStmtTailPreBundle t)`), and `stmtIfThen_amended_of_dispatch`
  finishing through `stmtIfThen_splitT` to `SDispatchC t`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump beyond the seg-derivation budget the GEN idiom uses.  Axioms of every theorem
⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.ApproxArmReseat

namespace Vsa.Sim

set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

/-! ## §1. The then-arm tail span `0x8000421c → 0x8000422c` (2 blocks: not-taken
`beqz` mid-chain, fall-through end AT the `j` site `0x80004230`) -/

#derive_case stmtIfThenTailSeg chain
  [(0x8000421c#64, 0x00800813#32),   -- li   a6,8       (addi x16,x0,8)
   (0x80004220#64, 0x00016717#32),   -- auipc a4,0x16
   (0x80004224#64, 0xd9870713#32)]   -- addi a4,a4,-616 (a4 := 0x80019fb8)
    terminator ⟨0x80004228#64, 0x0a050263#32, 0x63#8, 0x02#8, 0x05#8, 0x0a#8,
      .br bop.BEQ false, 10, 0, 0x0a4#13, 0#21, 0#12⟩ ;;  -- beqz a0 NOT taken
  [(0x8000422c#64, 0x01043403#32)]   -- ld s0,16(s0)    (s0 := then-child)

/-- The then-arm tail pin list — the registers the span reads (`x10` the truthy
status for the `beqz`, `x8` the if-node for the `ld`) plus the dispatch pins the
marshalling carries through (`x2`/`x9`/`x18`/`x19`). -/
def stmtIfThenTailL (a0v s0 sp s1 s2 s3 : BitVec 64) : GRegs :=
  [(10, a0v), (8, s0), (2, sp), (9, s1), (18, s2), (19, s3)]

/-! ## §2. The row (`segToTriple`) — parked at the `j 0x80004014` site -/

/-- The then-arm tail row post: parked AT the `j` site `0x80004230` with the
reloaded `s0`, the recomputed `a6`/`a4`, and every carried pin available in
`GHolds` (the landed wave-43 row shape — values consumed abstractly; the
`a4 = stmtJumpTableBase` fold value is machine-checked by
`stmtIfThenTail_a4_computed` below). -/
def StmtIfThenTailPost (a0v s0 sp s1 s2 s3 : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks stmtIfThenTailSeg
    (SegEvalState.init (stmtIfThenTailL a0v s0 sp s1 s2 s3) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80004230#64 ∧
  gprGet c.σ 16 = some (8#64) ∧
  GHolds c.σ (evalBlocks stmtIfThenTailSeg
    (SegEvalState.init (stmtIfThenTailL a0v s0 sp s1 s2 s3) lds)).regs

/-- **`stmtIfThenTailRow`** — the whole then-arm tail staging span as a `Triple`
via `segToTriple`; ONE kernel `ChainOK` `decide`. -/
theorem stmtIfThenTailRow (a0v s0 sp s1 s2 s3 : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre stmtIfThenTailSeg (stmtIfThenTailL a0v s0 sp s1 s2 s3) lds
        0x8000421c#64 m0)
      (StmtIfThenTailPost a0v s0 sp s1 s2 s3 lds m0) := by
  apply segToTriple stmtIfThenTailSeg (stmtIfThenTailL a0v s0 sp s1 s2 s3) lds
    0x8000421c#64 m0 (StmtIfThenTailPost a0v s0 sp s1 s2 s3 lds m0)
    (by have h : keysG (stmtIfThenTailL a0v s0 sp s1 s2 s3) = [10, 8, 2, 9, 18, 19] := rfl
        rw [h]
        show ChainOK 0x8000421c#64 [10, 8, 2, 9, 18, 19] stmtIfThenTailSeg; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, ?_, hregs⟩
  · rw [hpc']
    show some (evalBlocksPC 0x8000421c#64
      (SegEvalState.init (stmtIfThenTailL a0v s0 sp s1 s2 s3) lds) stmtIfThenTailSeg)
      = some 0x80004230#64
    rfl
  · exact gholds_lookup (v := 8#64) _ hregs (by rfl)

#print axioms stmtIfThenTailRow

/-- **The `a4 = stmtJumpTableBase` fold value, machine-checked** (ground
instantiation, ONE kernel `decide`): the `auipc a4,0x16; addi a4,a4,-616` pair the
seg carries computes exactly the statement jump-table base — the
`ExecDispatchEntry.a4` staging is dischargeable from this span.  (Stated ground
because the symbolic `lookupG`-value normalization has no peel lemma yet — see
observation `lookupG-evalBlocks-value-peel-missing`; the value is
ghost-independent, `x14` is written by the closed `auipc`/`addi` pair.) -/
theorem stmtIfThenTail_a4_computed :
    lookupG 14 (evalBlocks stmtIfThenTailSeg
      (SegEvalState.init (stmtIfThenTailL 1 0 0 0 0 0) [])).regs
    = some (BitVec.ofNat 64 stmtJumpTableBase) := by decide

#print axioms stmtIfThenTail_a4_computed

/-! ## §3. The obstruction tie-in (Law 4)

The route's landing (one `j` hop past the row's end) is the dispatch head
`0x80004014`, where `SEntryC` is decidably REFUTED — this arm can NEVER discharge
the frozen `NonEvalChildStages.stmtIfThen` field (target `ExecStmtPreBundle`,
whose bridge lands at `SEntryC`); the amended `SDispatchC` shape (§4) is the
machine truth. -/

/-- Any config the then-arm tail hop lands on refutes `SEntryC` — the pilot-level
witness that the frozen field conclusion is not this arm's machine shape. -/
theorem stmtIfThenTail_target_not_sEntryC (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr) (s : Stmt)
    (hpc : c.σ.regs.get? Register.PC =
      some (BitVec.ofNat 64 execStmtDispatchHead)) :
    ¬ SEntryC c st d env s :=
  sEntryC_false_at_dispatchHead c st d env s hpc

#print axioms stmtIfThenTail_target_not_sEntryC

/-! ## §4. The arm-head bundle + named residuals + the amended-field composer

Mirrors the wave-43 `WhileBodyArmHeadInv`/`WhileBodyArmStagePre`/
`WhileBodyArmDispatch` shape, re-seated on the TAIL twin: the marshalling residual
lands at `ExecStmtTailPreBundle t` (the state at the `j` site with the hop
supplied via `gregsHopInto_of_jx0Site` off the `j @0x80004230` site obs), and the
verified twin (`stmtIfThen_splitT` ≫ `execEntry_of_jTailRedispatch`) finishes to
`SDispatchC t`. -/

/-- **The then-arm head bundle** — the machine at `0x8000421c` (post-truthy) with
the span pins live (`a0 ≠ 0` routing is `ChainFacts` content), the if-node in
`s0`, and the then-child's `StmtRepr` at the address the `ld s0,16(s0)` reads. -/
def IfThenArmHeadInv
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : Vsa.While.St) (t : Stmt)
    (a0v s0 sp s1 s2 s3 aThen : BitVec 64) (m0 : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x8000421c#64) ∧
  GHolds c.σ (stmtIfThenTailL a0v s0 sp s1 s2 s3) ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  c.σ.mem = m0 ∧
  StmtRepr m0 aThen.toNat t ∧
  StoreRepr m0 N A φf φc st'.store ∧
  Machine.output c.σ = st'.out

/-- **The `stmtIfThen` tail marshalling residual** — from the arm-head bundle,
run the span (`stmtIfThenTailRow`) and marshal the computed `GHolds`/write-log at
the `j` site into `ExecStmtTailPreBundle t` (whose hop is
`gregsHopInto_of_jx0Site` off the `j @0x80004230` site obs).  Named per Law 2. -/
def IfThenTailStagePre
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : Vsa.While.St) (d : Nat) (env : Addr) (t : Stmt)
    (a0v s0 sp s1 s2 s3 aThen : BitVec 64) (m0 : Mem) : Prop :=
  ∀ c' : Config,
    IfThenArmHeadInv N A SL φf φc st' t a0v s0 sp s1 s2 s3 aThen m0 c' →
    LandedN 1 c' (fun c'' => ExecStmtTailPreBundle t c'' st' d env)

/-- **The `stmtIfThen` tail dispatch residual** — from the parent
`SEntryC (.ifStmt cnd t e)` plus the taken condition, land (LandedN 0) at the
arm-head bundle.  Genuinely upstream (cnd-eval → `value_truthy` → truthy-nonzero
routing is M4 arm-seg content). -/
def IfThenTailDispatch (cnd : Expr) (t : Stmt) (e : Option Stmt)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (v : Value) (c : Config) : Prop :=
  EvalE st d env cnd st' v → v.truthy = true → SEntryC c st d env (.ifStmt cnd t e) →
  ∃ (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (a0v s0 sp s1 s2 s3 aThen : BitVec 64) (m0 : Mem),
    LandedN 0 c (IfThenArmHeadInv N A SL φf φc st' t a0v s0 sp s1 s2 s3 aThen m0) ∧
    IfThenTailStagePre N A SL φf φc st' d env t a0v s0 sp s1 s2 s3 aThen m0

/-- **The AMENDED `stmtIfThen` staging field, machine-composed** — the
`ExecStmtTailPreBundle`-typed counterpart of `NonEvalChildStages.stmtIfThen`
(what the field becomes under the `SDispatchC` amendment plan). -/
theorem stmtIfThen_tailField_of_dispatch
    (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st st' : Vsa.While.St)
    (d : Nat) (env : Addr) (v : Value)
    (hDisp : IfThenTailDispatch cnd t e st st' d env v c)
    (hE : EvalE st d env cnd st' v) (ht : v.truthy = true)
    (hSE : SEntryC c st d env (.ifStmt cnd t e)) :
    LandedN 1 c (fun c' => ExecStmtTailPreBundle t c' st' d env) := by
  obtain ⟨N, A, SL, φf, φc, a0v, s0, sp, s1, s2, s3, aThen, m0, hLanded0, hStage⟩ :=
    hDisp hE ht hSE
  have hcomp : LandedN (0 + 1) c (fun c' => ExecStmtTailPreBundle t c' st' d env) :=
    LandedN.bind hLanded0 (fun c' hInv => hStage c' hInv)
  exact LandedN.weakenCount (by omega) hcomp

#print axioms stmtIfThen_tailField_of_dispatch

/-- **The full amended `stmtIfThen` arm** — dispatch residual ≫ staging ≫ the
verified tail twin: from the parent if-entry and the taken condition, the machine
lands (≥ 1 step) at the then-child's `SDispatchC` — the machine-true counterpart
of the frozen (unreachable) `SEntryC` conclusion. -/
theorem stmtIfThen_amended_of_dispatch
    (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st st' : Vsa.While.St)
    (d : Nat) (env : Addr) (v : Value)
    (hDisp : IfThenTailDispatch cnd t e st st' d env v c)
    (hE : EvalE st d env cnd st' v) (ht : v.truthy = true)
    (hSE : SEntryC c st d env (.ifStmt cnd t e)) :
    LandedN 1 c (fun c' => SDispatchC c' st' d env t) :=
  stmtIfThen_splitT cnd t e c st st' d env v
    (fun hE' ht' hSE' => stmtIfThen_tailField_of_dispatch cnd t e c st st' d env v
      hDisp hE' ht' hSE')
    hE ht hSE

#print axioms stmtIfThen_amended_of_dispatch

end Vsa.Sim
