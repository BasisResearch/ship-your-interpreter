import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg
import Vsa.Sim.ArmSegSplitNonEval

/-!
# `StmtForInitArmStagePre` — the exec-`forStmt`-init-arm-head → `ExecStmtPreBundle`
staging field (Wave 43, non-eval side)

The `stmtForInit` field of `NonEvalChildStages` (`ArmSegSplitNonEval.lean`) is a
STAGING residual: from `SEntryC (.forStmt (some init) cnd step b)` plus the
`allocFrame` (the for-loop's new inner scope) run the init-arm head and land at
`ExecStmtPreBundle init` — the recursive `jal exec_stmt` on the loop INIT statement.

The arm head (from `experiments/disasm.txt`, the for-init at `0x80004248`, the
NOT-taken branch of `beqz a1,0x8000426c` at `0x80004244`, after `env_new`
@0x80004238 established the new scope and `ld a1,8(s0)` @0x8000423c loaded the init
node) is:

    80004248:  mv a2,a0       -- a2 := env   (env_new result, addi x12,x10,0)
    8000424c:  mv a3,s2       -- a3 := interp* (addi x13,x18,0)
    80004250:  mv a0,s1       -- a0 := ret   (addi x10,x9,0)
    80004254:  jal exec_stmt  -- 0x80003fe0, link 0x80004258

a STRAIGHT-LINE-then-`jal exec_stmt` span — exactly the wave-41 `argsHead` shape
(the init node `a1` was loaded before the `beqz` and survives the three `mv`s).
Per the CLAUDE.md discipline table, the body `0x80004248 → 0x80004250` is a
`#derive_case` seg and the `jal exec_stmt` seam is `bridgeOfSeg`; the dispatch
residual (`SEntryC (.forStmt …) + allocFrame → arm-head bundle at 0x80004248`) and
the marshalling residual (`GHolds`/`writeLog` → `ExecStmtPreBundle init` conjuncts)
stay NAMED typed premises (Law 2), exactly as `ArgsHeadDispatch`/`ArgsHeadStagePre`.

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

