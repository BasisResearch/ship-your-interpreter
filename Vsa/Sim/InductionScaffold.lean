import Vsa.Sim.InterpEntry
import Vsa.Sim.EvalIntSim
import Vsa.Sim.EvalNullSim
import Vsa.Sim.EvalBoolSim
import Vsa.Sim.EvalStrSim
import Vsa.Sim.EvalVarSim

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

/-- The remaining call-depth budget at a node evaluated at active depth `d`. -/
def depthLeft (d : Nat) : Nat := maxCallDepth - d

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

/-- Skeleton machine precondition shared by the non-`EvalE` relations. `entryPC`
is the compiled segment's entry address (a per-relation constant, placeholder
`0` in the skeleton); `st`/`d` are the spec pre-state and depth; `dLeft`/`aLeft`
the budgets. -/
structure SegEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (entryPC : Nat)
    (m0 : Mem)
    (c : Config) : Prop where
  /-- Control state pinned (M-mode, Bare, …). -/
  good : GoodState c.σ
  /-- Tick parity (`M3`). -/
  tick : c.tick < 2
  /-- PC at the segment's entry address. -/
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 entryPC)
  /-- The whole spec store is represented. -/
  store : StoreRepr c.σ.mem N A φf φc st.store
  /-- Console output correspondence. -/
  out : OutRepr c.σ st
  /-- Machine memory is the pinned pre-memory. -/
  mem : c.σ.mem = m0
  /-- The blanket ghost frame (callee-preserved registers tie to `g`). -/
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R
  /-- SKELETON: the call-depth budget is respected (`d + dLeft = maxCallDepth`).
  The real predicate derives `d < maxCallDepth` on `Call.closure` from this. -/
  depth_budget : d + dLeft = maxCallDepth
  /-- SKELETON: the arena has `aLeft` bytes free below `A.hi`; the real
  predicate bounds this subtree's allocations by `aLeft` (`MallocContract`). -/
  arena_budget : A.lo + aLeft ≤ A.hi

/-- **The stack-window discipline table** (wave 38, ledger
`body-ih-no-caller-frame-slots`): maps a segment EXIT PC to the segment's
stack-scratch bound `k`.  A span landing at a tabled `q` scribbles the stack
only STRICTLY BELOW `(entry sp) + k` — its own inline scratch slots plus every
callee frame (all below sp) — so stack bytes at/above `sp + k` survive the span
(`SegExit.stackWin`).  Untabled exit PCs keep the clause vacuous (exactly the
pre-amendment `SegExit`).  The bound is keyed per segment because it is genuine
per-site geometry: the closure-body `ExecSeq` loop (`→ 0x80003378`) writes
`0(sp)` (a6 spill, `0x80003370`) and the result buffer `144..167(sp)` (the
`addi a3,sp,144` pointer at `0x8000335c`, written by the `exec_stmt` subtree),
so its bound is `168`; the eval-frame arm spans (`→ callJoinPC`) scribble up to
`sp+1088` and stay untabled; one global or per-motive constant is impossible
(analysis: `experiments/logs/wave38-cruxresid.md`).  The sp anchor is the ghost
frame — `AbiPreservedNoise x2` holds, so `SegEntry.frame`/`SegExit.frame` pin
the machine sp to `g x2` at both ends; no new parameter anywhere. -/
def stackScratchTop : Nat → Option Nat
  | 0x80003378 => some 168  -- callBodyRetPC: the closure-body ExecSeq loop
  | _ => none

/-- **The entry-side spill-image table** (wave 40, ledger
`segentry-no-caller-spill-image` — the DUAL of `stackScratchTop`): maps a
segment ENTRY PC to the caller-frame spill slot whose `m0`-image the segment's
routes RESTORE from, as `(sp-offset, GPR index)`.  A tabled entry PC asserts
(via `EntryImage`) that the pre-memory `m0` holds, at `sp + off`, the LE bytes
of the ghost frame's value for that GPR — the link between the ∀-quantified
`m0` and `g` that a restore-route (`ld <reg>, off(sp)` after a sub-run) needs
to re-establish the exit `frame` clause.  One entry today: the closure-call
dispatch `callDispatchPC = 0x80003254` restores `s7 = x23` from `1016(sp)`
(`ld s7,1016(sp)` at `0x800033b0`/`0x80003970`), a slot spilled at
`0x800031cc` — BEFORE the segment (all other slots — `s5@1032`, `s3@1048`,
`s6@1024` — are in-span, carried by `CallerSpillSlots`).  Untabled entry PCs
keep the clause vacuous.  SEAT NOTE (ledger
`segentry-spillimage-field-blocked-by-frozen-generic-producer`): the clause is
consumed as an `mCall`-motive hypothesis (`TermSimAssembly.mCall`), not yet a
`SegEntry` field — `ArmSegSplitSeg.segEntry_of_jalPrefix` constructs `SegEntry`
at a ∀-quantified entry PC and is frozen this wave; the hoist is mechanical
once that file may take an `entrySpillImage entryPC = none` hypothesis. -/
def entrySpillImage : Nat → Option (Nat × Nat)
  | 0x80003254 => some (1016, 23)  -- callDispatchPC: the s7 slot (0x800031cc)
  | _ => none

/-- Homogeneous ghost-frame GPR read — the ghost twin of `BlockPilot.gprGet`:
dispatches the heterogeneous `RegisterType` register file at concrete GPR
indices, so every branch reduces to `BitVec 64` and no cast is needed.
Non-GPR indices read `none`. -/
def gGpr (g : (R : Register) → Option (RegisterType R)) : Nat → Option (BitVec 64)
  | 1 => g Register.x1
  | 2 => g Register.x2
  | 3 => g Register.x3
  | 4 => g Register.x4
  | 5 => g Register.x5
  | 6 => g Register.x6
  | 7 => g Register.x7
  | 8 => g Register.x8
  | 9 => g Register.x9
  | 10 => g Register.x10
  | 11 => g Register.x11
  | 12 => g Register.x12
  | 13 => g Register.x13
  | 14 => g Register.x14
  | 15 => g Register.x15
  | 16 => g Register.x16
  | 17 => g Register.x17
  | 18 => g Register.x18
  | 19 => g Register.x19
  | 20 => g Register.x20
  | 21 => g Register.x21
  | 22 => g Register.x22
  | 23 => g Register.x23
  | 24 => g Register.x24
  | 25 => g Register.x25
  | 26 => g Register.x26
  | 27 => g Register.x27
  | 28 => g Register.x28
  | 29 => g Register.x29
  | 30 => g Register.x30
  | 31 => g Register.x31
  | _ => none

/-- `gGpr` at the one tabled register, for the consumer side. -/
theorem gGpr_x23 (g : (R : Register) → Option (RegisterType R)) :
    gGpr g 23 = g Register.x23 := rfl

/-- **The entry-side spill-image clause** — guard-implication style, the
`stackWin` dual: for a TABLED entry PC, the pre-memory `m0` holds at
`sp + off` the LE bytes of the ghost's value for GPR `n` (`sp` anchored at
`g x2`, exactly as `stackWin` anchors its window).  Vacuous when
`entrySpillImage entryPC = none` — generic producers discharge it by
`entryImage_of_none`.  Byte-level LE, matching `CallerSpillSlots.s5/.s3` so
the restore-route dischargers consume one uniform shape. -/
def EntryImage (entryPC : Nat)
    (g : (R : Register) → Option (RegisterType R)) (m0 : Mem) : Prop :=
  ∀ (off n : Nat), entrySpillImage entryPC = some (off, n) →
    ∀ spv : BitVec 64, g Register.x2 = some spv →
    ∀ w : BitVec 64, gGpr g n = some w →
    ∀ i : Nat, i < 8 →
      m0[spv.toNat + off + i]? = some (w.extractLsb' (8 * i) 8)

/-- The vacuous case: an untabled entry PC carries no image obligation. -/
theorem entryImage_of_none {entryPC : Nat}
    {g : (R : Register) → Option (RegisterType R)} {m0 : Mem}
    (h : entrySpillImage entryPC = none) : EntryImage entryPC g m0 := by
  intro off n hoff
  rw [h] at hoff
  exact absurd hoff (by simp)

#print axioms gGpr_x23
#print axioms entryImage_of_none

/-- Skeleton machine postcondition shared by the non-`EvalE` relations. `exitPC`
is the segment's return/continuation PC (placeholder `0`); `st'` the spec
post-state, re-represented with EXTENDED correspondence maps (φ-extension order
`PhiExtends`, as in `EvalExit`). -/
structure SegExit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : SpecSt) (exitPC : Nat)
    (m0 : Mem)
    (c : Config) : Prop where
  /-- Control state re-established. -/
  good : GoodState c.σ
  /-- Tick parity still `< 2`. -/
  tick : c.tick < 2
  /-- PC at the segment's exit/continuation address. -/
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 exitPC)
  /-- The store is re-represented for `st'` with φ-maps extended over the
  allocated prefix (SKELETON: same φ-extension shape as `EvalExit.store`). -/
  store : ∃ (φf' φc' : Addr → Nat),
    PhiExtends φf φf' nf ∧
    PhiExtends φc φc' nc ∧
    StoreRepr c.σ.mem N A φf' φc' st'.store
  /-- Console output correspondence for `st'`. -/
  out : OutRepr c.σ st'
  /-- The blanket ghost frame restored. -/
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R
  /-- SKELETON: memory outside the arena and the scribbled stack window is
  framed to `m0` (same shape as `EvalExit.memFrame`, minus the sret buffer
  carve-out which is EvalE-specific). -/
  memFrame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    c.σ.mem[a]? = m0[a]?
  /-- **The stack-window clause** (wave 38, ledger
  `body-ih-no-caller-frame-slots`): caller-window survival.  For a TABLED exit
  PC (`stackScratchTop exitPC = some k`), stack bytes at/above `sp + k` — the
  caller's window above the segment's scratch — survive to the segment's entry
  memory `m0`; `sp` is the segment's ABI stack pointer, tied to the ghost frame
  (`frame` + `AbiPreservedNoise x2`, pinned at entry and exit alike).  Stated
  the way `memFrame` states its frame (implication-guarded), scoped to the
  stack region (`a < SL.hi`) and outside the arena.  Vacuous when
  `stackScratchTop exitPC = none` — every pre-amendment producer is unaffected
  at untabled exit PCs. -/
  stackWin : ∀ k : Nat, stackScratchTop exitPC = some k →
    ∀ spv : BitVec 64, g Register.x2 = some spv →
    ∀ a : Nat, spv.toNat + k ≤ a → a < SL.hi → ¬ (A.lo ≤ a ∧ a < A.hi) →
      c.σ.mem[a]? = m0[a]?

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

/-- `EvalE` motive: the honest `EvalEntry → EvalExit` Triple, as in
`EvalIntSimGoal`. `d`/`st`/`env`/`e`/`st'`/`v` come from the recursor; the
layout ghosts and budgets are ∀-bound. -/
def motive_EvalE (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
    (v : Value) (_h : EvalE st d env e st' v) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    Triple
      (EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0)
      (EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size st' v sp r sret m0)

/-- `EvalArgs` motive: SKELETON Triple. The arg vector `vs` and its ABI
placement are part of the skeleton exit (a per-case field). -/
def motive_EvalArgs (st : SpecSt) (d : Nat) (env : Addr) (_es : List Expr)
    (st' : SpecSt) (_vs : List Value) (_h : EvalArgs st d env _es st' _vs) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d (depthLeft d) 0 0 m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' 0 m0)

/-- `Call` motive: SKELETON Triple. `Call.closure` is where the depth budget
(`d < maxCallDepth`) actually bites and a fresh frame is allocated. -/
def motive_Call (st : SpecSt) (d : Nat) (_fv : Value) (_vs : List Value)
    (st' : SpecSt) (_v : Value) (_h : Call st d _fv _vs st' _v) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d (depthLeft d) 0 0 m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' 0 m0)

/-- `ExecS` motive: SKELETON Triple. The `Status` result and its ABI encoding
are per-case skeleton fields. -/
def motive_ExecS (st : SpecSt) (d : Nat) (env : Addr) (_s : Stmt) (st' : SpecSt)
    (_status : Status) (_h : ExecS st d env _s st' _status) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d (depthLeft d) 0 0 m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' 0 m0)

/-- `ExecInit` motive: SKELETON Triple. -/
def motive_ExecInit (st : SpecSt) (d : Nat) (env : Addr) (_init : Option Stmt)
    (st' : SpecSt) (_h : ExecInit st d env _init st') : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d (depthLeft d) 0 0 m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' 0 m0)

/-- `ForLoop` motive: SKELETON Triple. -/
def motive_ForLoop (st : SpecSt) (d : Nat) (env : Addr) (_cnd _step : Option Expr)
    (_b : Stmt) (st' : SpecSt) (_status : Status)
    (_h : ForLoop st d env _cnd _step _b st' _status) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d (depthLeft d) 0 0 m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' 0 m0)

/-- `ForCond` motive: SKELETON Triple. -/
def motive_ForCond (st : SpecSt) (d : Nat) (env : Addr) (_cnd : Option Expr)
    (st' : SpecSt) (_h : ForCond st d env _cnd st') : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d (depthLeft d) 0 0 m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' 0 m0)

/-- `ExecStep` motive: SKELETON Triple. -/
def motive_ExecStep (st : SpecSt) (d : Nat) (env : Addr) (_step : Option Expr)
    (st' : SpecSt) (_h : ExecStep st d env _step st') : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d (depthLeft d) 0 0 m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' 0 m0)

/-- `ExecSeq` motive: SKELETON Triple. The statement-list loop lands here (this
is what `interp_run` consumes). -/
def motive_ExecSeq (st : SpecSt) (d : Nat) (env : Addr) (_ss : List Stmt)
    (st' : SpecSt) (_status : Status) (_h : ExecSeq st d env _ss st' _status) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d (depthLeft d) 0 0 m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' 0 m0)

/-! ## §4. The top-level `term_sim`-shaped goal for the `EvalE` relation

Recorded as a `Prop`-valued `def`, NOT an asserted (`sorry`'d) theorem. Proving
it IS the real mutual induction: apply `@EvalE.rec` with the nine `motive_*`
above and discharge each minor premise. The integer case below is the first
actual minor premise. The other completed leaf walks currently use distinct
arm-specific entry predicates; they cannot be used by this motive until the
integer-specific `EvalEntry` is replaced by a dependent per-arm entry family.
-/

/-- The `EvalE` simulation induction goal: every `EvalE` derivation's compiled
segment simulates it. This is the `EvalE`-projection of `term_sim`. -/
def EvalESimGoalType : Prop :=
  ∀ {st : SpecSt} {d : Nat} {env : Addr} {e : Expr} {st' : SpecSt} {v : Value}
    (h : EvalE st d env e st' v),
    motive_EvalE st d env e st' v h

/-! ## A discharged real recursor premise

`EvalEntry` currently contains exactly the `EX_INT` jump-table and callee
resources, so `evalIntSim` has precisely the Triple required by
`motive_EvalE` for `EvalE.int`. This theorem is therefore the first
non-trivial minor premise of the eventual mutual-recursion proof, rather than
another statement-only scaffold. -/

/-- The `EvalE.int` minor premise for the real `motive_EvalE`. -/
theorem motive_EvalE_int
    (st : SpecSt) (d : Nat) (env : Addr) (n : Int)
    (h : EvalE st d env (.int n) st (.int n)) :
    motive_EvalE st d env (.int n) st (.int n) h := by
  intro g N A SL φf φc sp r sret aEnv aExpr m0
  exact evalIntSim g N A SL φf φc st d env n sp r sret aEnv aExpr m0 h

#print axioms motive_EvalE_int

/-! ## Completed leaf cases with dependent entries

The completed leaf walks do not share one entry structure: each dispatch arm
requires its own jump-table slot, callee code, and footprint geometry. This
mixed motive preserves those requirements instead of pretending the
integer-only `EvalEntry` is generic. It is the prototype for the dependent
entry family needed by the full induction. -/

/-- Real machine Triples for the five completed `EvalE` leaf forms; `True` for
the unfinished forms. The variable case retains `EvalVarEntry`'s explicit
`env_get_found` contract. -/
def motive_EvalE_completedLeaf (st : SpecSt) (d : Nat) (env : Addr) (e : Expr)
    (st' : SpecSt) (v : Value) (_h : EvalE st d env e st' v) : Prop :=
  match e with
  | .int n =>
      ∀ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
        Triple
          (EvalEntry g N A SL φf φc st d env (.int n) sp r sret aEnv aExpr m0)
          (EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size st' v sp r sret m0)
  | .str s =>
      ∀ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
        Triple
          (EvalStrEntry g N A SL φf φc st d env s sp r sret aEnv aExpr m0)
          (EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size st' v sp r sret m0)
  | .bool b =>
      ∀ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
        Triple
          (EvalBoolEntry g N A SL φf φc st d env b sp r sret aEnv aExpr m0)
          (EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size st' v sp r sret m0)
  | .null =>
      ∀ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
        Triple
          (EvalNullEntry g N A SL φf φc st d env sp r sret aEnv aExpr m0)
          (EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size st' v sp r sret m0)
  | .var x =>
      ∀ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
        Triple
          (EvalVarEntry g N A SL φf φc st d env x v sp r sret aEnv aExpr m0)
          (EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size st' v sp r sret m0)
  | _ => True

/-- The generated mutual recursor accepts all five completed leaf simulation
Triples simultaneously, with each arm's exact entry predicate. -/
theorem induction_completed_leaf_cases_check :
    ∀ {st : SpecSt} {d : Nat} {env : Addr} {e : Expr} {st' : SpecSt} {v : Value}
      (t : EvalE st d env e st' v), motive_EvalE_completedLeaf st d env e st' v t := by
  intro st d env e st' v t
  refine EvalE.rec
    (motive_1 := motive_EvalE_completedLeaf)
    (motive_2 := fun _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_  -- EvalE (15)
    ?_ ?_                                            -- EvalArgs (2)
    ?_ ?_ ?_ ?_                                      -- Call (4)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ -- ExecS (16)
    ?_ ?_                                            -- ExecInit (2)
    ?_ ?_ ?_ ?_                                      -- ForLoop (4)
    ?_ ?_                                            -- ForCond (2)
    ?_ ?_                                            -- ExecStep (2)
    ?_ ?_ ?_                                         -- ExecSeq (3)
    t
  · intro st d env n g N A SL φf φc sp r sret aEnv aExpr m0
    exact evalIntSim g N A SL φf φc st d env n sp r sret aEnv aExpr m0
      (EvalE.int st d env n)
  · intro st d env s g N A SL φf φc sp r sret aEnv aExpr m0
    exact evalStrSim g N A SL φf φc st d env s sp r sret aEnv aExpr m0
      (EvalE.str st d env s)
  · intro st d env b g N A SL φf φc sp r sret aEnv aExpr m0
    exact evalBoolSim g N A SL φf φc st d env b sp r sret aEnv aExpr m0
      (EvalE.bool st d env b)
  · intro st d env g N A SL φf φc sp r sret aEnv aExpr m0
    exact evalNullSim g N A SL φf φc st d env sp r sret aEnv aExpr m0
      (EvalE.null st d env)
  · intro st d env x v hget g N A SL φf φc sp r sret aEnv aExpr m0
    exact evalVarSim g N A SL φf φc st d env x v sp r sret aEnv aExpr m0
      (EvalE.var st d env x v hget)
  all_goals (intros; trivial)

#print axioms induction_completed_leaf_cases_check

/-! ## §3. The toy plumbing check

Instantiate `@EvalE.rec` with all-`True` motives; close every minor premise
with `True.intro`. This validates motive count (9), binder order, and every
minor-premise shape (recursive constructors' IH arguments included) against the
kernel. `intro`+`exact trivial` per premise would work; `fun _ … => trivial`
via `fun` is terser but the premise count is large, so we use the recursor
applied to explicit trivial closers and let `exact` unify. -/

/-- The toy instantiation: for the all-`True` motive family, the recursor
produces `∀ (t : EvalE …), True`. Kernel-checked; validates the plumbing.

Proved by `refine`-ing the recursor with the nine all-`True` motives supplied
by name, then closing EVERY remaining minor-premise goal with `intros; trivial`
(`all_goals`). This is arity-robust: whatever the binder count of each
constructor's minor premise (including the recursive-constructor IH arguments),
`intros` discharges them and the goal is definitionally `True`. That the
`refine` unifies at all is exactly the validation of motive count and order. -/
theorem induction_plumbing_check :
    ∀ {st : SpecSt} {d : Nat} {env : Addr} {e : Expr} {st' : SpecSt} {v : Value}
      (_t : EvalE st d env e st' v), True := by
  intro st d env e st' v t
  refine EvalE.rec
    (motive_1 := fun _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_  -- EvalE (15)
    ?_ ?_                                            -- EvalArgs (2)
    ?_ ?_ ?_ ?_                                      -- Call (4)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ -- ExecS (16)
    ?_ ?_                                            -- ExecInit (2)
    ?_ ?_ ?_ ?_                                      -- ForLoop (4)
    ?_ ?_                                            -- ForCond (2)
    ?_ ?_                                            -- ExecStep (2)
    ?_ ?_ ?_                                         -- ExecSeq (3)
    t
  all_goals (intros; trivial)

#print axioms induction_plumbing_check

end Vsa.Sim.Scaffold
