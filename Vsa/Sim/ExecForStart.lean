import Vsa.Sim.ExecFor

/-!
# Layer 4 — M4 `forStmt` case: `ExecS.forStart` (the env_new + init bridge)

`ExecS.forStart` is the outer wrapper of the `for` statement (kind 5, arm
`0x80004234`). It allocates a child scope (`st.store.allocFrame (some env) =
(store', outer)`, the machine `env_new`), runs the optional `init` statement
(`ExecInit ⟨store', st.out⟩ d outer init st'`), then hands control to the
`ForLoop` proper (`ForLoop st' d outer cnd step b st'' status`), whose four
constructors are already discharged by `execForLoopBody` (`ExecFor.lean`).

## Machine path (arm `0x80004234`, kind 5 — the `forStart` prologue)

```
80004234:  mv   a0,s3            -- a0 := env
80004238:  jal  env_new          -- child scope (Store.allocFrame); a0 := new env `outer`
8000423c:  ld   a1,8(s0)         -- a1 := stmt->init   (offset 8)
80004240:  mv   s3,a0            -- s3 := outer env
80004244:  beqz a1,0x8000426c    -- no init → skip to cond head
80004248:  mv   a2,a0            -- (init present) a2 := outer env
8000424c:  mv   a3,s2            -- a3 := retslot
80004250:  mv   a0,s1            -- a0 := interp*
80004254:  jal  exec_stmt        -- init (ExecIH), link 0x80004258
80004258:  j    0x8000426c       -- → cond head (init's status = .normal, per ExecInit)
-- cond head 0x8000426c: the ForLoop head (see ExecFor.lean).
```

## Structure

`execForStartSim` mirrors `execBlockSim`'s `env_new` wiring (`ExecBlock2.lean`):
the arm prologue (`execBlockA` (kind 5) ≫ `env_new` (`Store.allocFrame` = `outer`)
≫ the optional `ExecInit` via `armExec_rec`/`ExecIH` ≫ landing at the cond head
`0x8000426c`) is delivered as the residual `hArm` — a bridge from the outer
`ExecEntry (.forStmt …)` at `env` to the ForLoop-head `ExecEntry (.forStmt …)` at
the child scope `outer` for the post-init state `st'`. `execForLoopBody`
(`ExecFor.lean`, proved unconditionally on its `hstep`/`hForIH` residuals) then
runs the loop from that head to the final `ExecExit`. Composing `hArm ≫
execForLoopBody` closes the `forStart` case conditional only on named residuals —
exactly the residual style of `execBlockSim`.

`hArm` bundles the `env_new` linkage (the child-scope allocation, `env_new_spec`,
`EnvNewSpec.lean`) and the `ExecInit` sub-derivation (the init statement's
`ExecIH` threaded through `armExec_rec`, `ExecBlock.lean`). `hstep`/`hForIH` are
the `execForLoopBody` per-iteration `ExecForStep` and recursive-sub-`for` IH
residuals (`ExecFor.lean`).

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

/-! ## `ExecForStartSimGoal` — the `ExecS.forStart` simulation Triple (packaged)

The post-state is the loop's final state `st''` with status `status`, exactly the
`ExecS.forStart` conclusion; the entry scope is the OUTER `env` (not the child
scope — the child `outer` is internal to the arm). -/

/-! ## `execForStartSim` — `ExecS.forStart`: `hArm (env_new + ExecInit) ≫ execForLoopBody`

Composes the whole `forStmt` arm. The arm prologue residual `hArm` bridges the
outer `ExecEntry (.forStmt …)` at `env` to the ForLoop-head `ExecEntry
(.forStmt …)` at the freshly-allocated child scope `outer` for the post-init state
`st'` (with extended φ-maps `φf'`/`φc'` accounting for the `env_new`/init store
growth, and a re-based memory baseline `m0'`). `execForLoopBody` then runs the
`ForLoop` from that head to the final `ExecExit`, which `hArm`'s memory framing
re-bases back to the outer entry. -/

end Vsa.Sim
