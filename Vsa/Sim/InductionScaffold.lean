import Vsa.Sim.DecodeTable.Batch04Part21
import Vsa.Sim.DecodeTable.Batch09Part26
import Vsa.Sim.DecodeTable.Batch11Part04
import Vsa.Sim.DecodeTable.Batch14Part10
import Vsa.Sim.DecodeTable.Batch16Part04
import Vsa.Sim.EnvGetSpec3
import Vsa.Sim.EvalIntSim2
import Vsa.Sim.EvalRecCommon

/-!
# Layer 4 — the mutual-recursor SCAFFOLDING for the simulation induction

This file builds the design-doc-mandated prerequisite for the recursive
`EvalE`/`ExecS`/`Call` cases of `term_sim`
(`experiments/M4-induction-design.md`, "The mutual recursor" note). It does
NOT prove the real induction; it establishes and VERIFIES the recursor
plumbing so the real cases can be fanned out onto a trusted skeleton.

## 1. The `@Vsa.While.EvalE.rec` binder structure (documented from `#check`)

The nine mutual relations of `Vsa/While/Semantics.lean`
(`EvalE`, `EvalArgs`, `Call`, `ExecS`, `ExecInit`, `ForLoop`, `ForCond`,
`ExecStep`, `ExecSeq`) generate a SINGLE recursor `Vsa.While.EvalE.rec`
(with siblings `.EvalArgs.rec` … that are definitionally the same object up
to which relation the final major premise ranges over). It takes:

### Nine motives (implicit), one per relation, in this order:
```
motive_1 : (st) (d) (env) (e : Expr)      (st') (v : Value)  → EvalE …    → Prop  -- EvalE
motive_2 : (st) (d) (env) (es: List Expr) (st') (vs)         → EvalArgs … → Prop  -- EvalArgs
motive_3 : (st) (d) (fv)  (vs)            (st') (v)          → Call …     → Prop  -- Call
motive_4 : (st) (d) (env) (s : Stmt)      (st') (status)     → ExecS …    → Prop  -- ExecS
motive_5 : (st) (d) (env) (init:Opt Stmt) (st')             → ExecInit … → Prop  -- ExecInit
motive_6 : (st) (d) (env) (cnd)(step)(b)  (st') (status)     → ForLoop …  → Prop  -- ForLoop
motive_7 : (st) (d) (env) (cnd:Opt Expr)  (st')             → ForCond …  → Prop  -- ForCond
motive_8 : (st) (d) (env) (step:Opt Expr) (st')             → ExecStep … → Prop  -- ExecStep
motive_9 : (st) (d) (env) (ss: List Stmt) (st') (status)     → ExecSeq …  → Prop  -- ExecSeq
```
Every motive takes ALL of its relation's indices AND the derivation proof of
that relation as its final explicit argument — i.e. the motives are
"parameterized by the derivation node", exactly the shape the design doc's
per-relation simulation-Triple statements need.

### ~40 minor premises (explicit), in constructor order, grouped by relation:
* `motive_1` (EvalE, 15): `int str bool null var assign binary orTrue orFalse
  andFalse andTrue neg not call fn`
* `motive_2` (EvalArgs, 2): `nil cons`
* `motive_3` (Call, 4): `closure print println assertOk`
* `motive_4` (ExecS, 16): `expr varInit varNull block ifTrue ifFalse ifNone
  whileFalse whileBreak whileRet whileLoop forStart ret retNull brk cont`
* `motive_5` (ExecInit, 2): `none some`
* `motive_6` (ForLoop, 4): `condFalse bodyBreak bodyRet loop`
* `motive_7` (ForCond, 2): `none some`
* `motive_8` (ExecStep, 2): `none some`
* `motive_9` (ExecSeq, 3): `nil consNormal consAbrupt`

Each minor premise for a NON-recursive constructor is just
`∀ (ctor args), motive_k … (proof)`. Each RECURSIVE constructor's minor
premise additionally takes the induction hypotheses `motive_j … (sub-proof)`
for every recursive sub-derivation, in left-to-right order, BEFORE the
conclusion. E.g. `binary` gets `motive_1 …l… → motive_1 …r… → motive_1 …binary…`
and `call` gets `motive_1 (f) → motive_2 (args) → motive_3 (call) → motive_1`.

### Major premise / conclusion:
`{st d env e st' v} (t : EvalE st d env e st' v) → motive_1 st d env e st' v t`.
(The `.EvalArgs.rec`/`.ExecS.rec`/… siblings differ only in taking the major
premise / concluding at `motive_2`/`motive_4`/… instead; the minor-premise
block is identical. So a single application with all nine motives + all minor
premises proves ALL nine families simultaneously by picking the right entry
point per relation.)

## 2. The motive family

Each `motiveSk_R` below is the per-relation simulation-`Triple` STATEMENT: it
asserts "the compiled code segment for this derivation node simulates it",
between a skeleton entry predicate and a skeleton exit predicate. For `EvalE`
we reuse the honest v1 predicates `EvalEntry`/`EvalExit` from
`InterpEntry.lean` (the same ones `evalIntSim`/`evalNullSim` discharge). For
the other eight relations we give entry/exit predicate SKELETONS with the
right SHAPE (entry PC + GoodState + StoreRepr + depth/arena budget; exit
PC + re-established StoreRepr + φ-extension), honestly marked as skeletons
where fields are placeholders. All are ∀-closed over the ghost layout params
and carry the `depthLeft`/`arenaLeft` budget parameters the design doc
mandates.

## 3. The toy plumbing check

`induction_plumbing_check` instantiates the recursor with the TRIVIAL motives
(`fun … => True`) and closes every one of the ~50 minor premises with
`True.intro`, yielding `∀ (derivation), True`. This is a genuine
kernel-checked theorem that validates motive count, binder order and every
minor-premise shape end-to-end.

## 4. The real statement

`motive_EvalE`/… are the real motive-family `def`s (Triple over the honest
predicates for `EvalE`, skeletons for the rest). `EvalESimGoalType` records
the top-level `term_sim`-shaped goal for the `EvalE` relation as a
`Prop`-valued `def` (NOT a `sorry`'d theorem) — its proof is the real
induction, future work.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

namespace Vsa.Sim.Scaffold

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim

-- `Vsa.Sim` also exports `Muldi3Spec.St` (a `Config → Prop` family), which
-- makes the bare name `St` ambiguous with the spec state type `Vsa.While.St`.
-- Alias the spec state type under an unambiguous name and use it throughout.
local notation "SpecSt" => Vsa.While.St

/-! ## Budget parameters threaded through every entry predicate

The design doc (decisions #2/#3) requires each entry predicate to carry a
call-depth budget and an arena budget from day one. `depthLeft` is the number
of nested closure calls still permitted (`maxCallDepth - d`, available at every
node because `d` is an index of every relation); `arenaLeft` is a byte budget
bounding this subtree's allocations against the finite arena. Both are `Nat`s
carried as skeleton fields — the real induction constrains them (`d < 1000`
from `Call.closure`; allocation ≤ arena from `MallocContract`). -/

/-! ## Skeleton entry/exit predicates for the eight non-`EvalE` relations

These have the SHAPE of the `EvalEntry`/`EvalExit` predicates (entry PC pinned,
GoodState, whole-store representation, budget fields) but leave the precise
per-relation ABI (which machine reg holds `env`, the arg vector `vs`, the
`Status`/`Value` result encoding, the exit PC) as honestly-labelled skeleton
placeholders. Filling them in is the per-relation case work; here they only
have to type-check and carry the right threaded data.

Common ghost/layout parameters (mirroring `EvalEntry`): register ghost frame
`g`, native addrs `N`, arena `A`, stack layout `SL`, correspondence maps
`φf`/`φc`, machine memory `m0`, and the `depthLeft`/`arenaLeft` budgets. -/

/-! ## The REAL motive family (§4)

For each relation `R`, `motive_R` maps a derivation node (and its indices) to
the simulation-`Triple` statement for that node — the entry predicate holds ⇒
some finite run reaches the exit predicate. The ghost layout params and the
budgets are ∀-quantified INSIDE the motive (each node picks its own layout).

`EvalE` uses the honest v1 `EvalEntry`/`EvalExit`; the other eight use the
`SegEntry`/`SegExit` skeletons with placeholder entry/exit PCs (`0`) and budget
`depthLeft d`. The `aExpr`/`sret`/… machine addresses in `EvalEntry` are ghosts
∀-bound here; the recursor never inspects them.

These type-check green (that is the deliverable); their PROOFS are the real
induction, not attempted here. -/

/-! ## §4. The top-level `term_sim`-shaped goal for the `EvalE` relation

Recorded as a `Prop`-valued `def`, NOT an asserted (`sorry`'d) theorem. Proving
it IS the real mutual induction: apply `@EvalE.rec` with the nine `motive_*`
above and discharge each minor premise. The integer case below is the first
actual minor premise. The other completed leaf walks currently use distinct
arm-specific entry predicates; they cannot be used by this motive until the
integer-specific `EvalEntry` is replaced by a dependent per-arm entry family.
-/

/-! ## A discharged real recursor premise

`EvalEntry` currently contains exactly the `EX_INT` jump-table and callee
resources, so `evalIntSim` has precisely the Triple required by
`motive_EvalE` for `EvalE.int`. This theorem is therefore the first
non-trivial minor premise of the eventual mutual-recursion proof, rather than
another statement-only scaffold. -/

/-! ## Completed leaf cases with dependent entries

The completed leaf walks do not share one entry structure: each dispatch arm
requires its own jump-table slot, callee code, and footprint geometry. This
mixed motive preserves those requirements instead of pretending the
integer-only `EvalEntry` is generic. It is the prototype for the dependent
entry family needed by the full induction. -/

/-! ## §3. The toy plumbing check

Instantiate `@EvalE.rec` with all-`True` motives; close every minor premise
with `True.intro`. This validates motive count (9), binder order, and every
minor-premise shape (recursive constructors' IH arguments included) against the
kernel. `intro`+`exact trivial` per premise would work; `fun _ … => trivial`
via `fun` is terser but the premise count is large, so we use the recursor
applied to explicit trivial closers and let `exact` unify. -/

end Vsa.Sim.Scaffold
