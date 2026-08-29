import Vsa.Sim.CallEntry
import Vsa.Sim.TermSimAssembly

/-!
# Layer 4 — M4: the `Call.closure` crux (`callClosurePC = 0x80003288`)

The single hardest remaining M4 case: a user closure call. Reached from the
`EX_CALL` dispatch (`callDispatchPC = 0x80003254`) when `fv->kind == 4`
(`VAL_CLOSURE`), the machine branches to the closure arm at
`callClosurePC = 0x80003288` and runs, end-to-end (decode in `CallEntry.lean`):

```
0x80003288  arity check   argc == cd->arity     (spec: vs.length = cd.params.length)
0x8000329c  depth guard   ++call_depth; blt 1000  (spec: d < maxCallDepth, body at d+1)
0x800032bc  jal env_new    frame := allocFrame (some cd.env)
0x800032dc  param-bind fold  env_define(frame, params[i], vs[i])   (foldl .define)
0x80003354  body ExecSeq loop   jal exec_stmt at depth d+1  (the recursive body IH)
0x80003954/0x8000339c  .normal → value_null / .ret v → copy 24B into CALL sret; --call_depth
0x800033ec  join into the shared eval_expr epilogue (callJoinPC)
```

## The residual this file discharges

`hCallClosure` (the `Call.closure` minor premise of `term_sim_of_cases`) has
conclusion `mCall st d (Value.closure a) vs st' v (Call.closure …)`, which by the
`mCall` motive definition is exactly the machine Triple

```
Triple (CallEntryP g N A SL φf φc st         d dLeft aLeft m0)   -- at callDispatchPC
       (CallExitP  g N A SL φf φc st'                       m0)  -- at callJoinPC
```

and it is *given* the body induction hypothesis
`mExecSeq {store := foldl .define store' (cd.params.zip vs), out := st.out}
         (d+1) frame cd.body st' status a_5`
— i.e. the whole closure body sequence as a `SegEntry → SegExit` Triple at PCs of
our choosing (the motive `∀`-binds the entry/exit PCs `p`/`q`).

## The `Call.closure` decomposition — three seams (`Triple.seq`)

We split the arm at two decoded PCs, `callBodyLoopPC = 0x80003354` (body loop
head) and `callBodyRetPC = 0x80003378` (link after `jal exec_stmt`; also the PC
the body-sequence exit lands at). The proof is `prefix ≫ body-IH ≫ return`:

* **(a) prefix** `ClosureEntrySpec` — the STRAIGHT-LINE marshalling
  `Triple (CallEntryP … st … callDispatchPC) (SegEntry … bound (d+1) frame …
  callBodyLoopPC)`: the closure branch (`kind==4`), arity check (`a_2` gates it
  taken), depth guard (`a_3 = d < maxCallDepth` gates the `blt` not-taken and
  makes the body run at `d+1`), `jal env_new` = `allocFrame (some cd.env)`
  (`a_4`), and the `env_define` param-bind fold (`params.zip vs`, the bound
  store). This is `#derive_case`-shaped EXCEPT for two callee contracts —
  `env_new_spec` (allocFrame, landed in `EnvNewSpec`) and the per-iteration
  `env_define` grow contract (landed ledger algebra in `EnvDefineClose` +
  `ReallocSpec`) — which it composes. It is block-reflectable modulo those two.

* **(b) body-IH** — the recursive body sequence: the given
  `mExecSeq (bound) (d+1) frame cd.body st' status a_5`, instantiated at
  `p := callBodyLoopPC`, `q := callBodyRetPC`. This is the `SegEntry → SegExit`
  Triple. NOTHING to prove here — it is a hypothesis (the IH-glue is the
  recursor's job, exactly as `armTail_rec` supplies the `EvalE` sub-call IHs).

* **(c) return** `ClosureRetSpec` — the STRAIGHT-LINE return marshalling
  `Triple (SegExit … st' status … callBodyRetPC) (CallExitP … st' … callJoinPC)`:
  classify `status` (`a_6`: `.normal ∧ v = .null`, or `.ret v`), `--call_depth`,
  and (on `.ret v`) copy the 24-byte body return `Value` from `sp+144` into the
  CALL's own sret; on `.normal`, `value_null` into the sret. This is
  block-reflectable (no recursion, no callee alloc — one `value_null` sub-call on
  the `.normal` arm, a 24-byte `memcpy` on the `.ret` arm).

So the crux **composes structurally** here (this file), with the two straight-line
seams (a)/(c) as named residuals — the exact deferral pattern of `callAssertOk`'s
`NativeAssertOkSpec` and `evalNegSim`'s `NegExtras`. The recursion is fully
absorbed by the body IH; the depth budget `d < maxCallDepth` and the
`allocFrame`/`env_define` fold live entirely in the prefix seam.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Scaffold

local notation "SpecSt" => Vsa.While.St

/-! ## The bound child store (`env_new` + param-bind fold)

The store the closure body runs against: a fresh frame `frame` allocated over the
captured environment `cd.env`, with each parameter bound to its argument (the
`foldl .define` over `cd.params.zip vs`). This is exactly the spec state the body
`ExecSeq` (and the `mExecSeq` IH) is stated over — we name it once so the three
seams share a canonical write-log normal form (fast-reflection rule 5). -/
def closureBoundStore (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) : Store :=
  List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store'
    (cd.params.zip vs)

/-- The spec state the closure body runs at: the bound child store, output
carried from the caller state `st`. -/
def closureBoundSt (st : SpecSt) (store' : Store) (cd : ClosureData)
    (vs : List Value) (frame : Addr) : SpecSt :=
  { store := closureBoundStore store' cd vs frame, out := st.out }

/-! ## The two straight-line seam residuals

Both are `#derive_case`-shaped straight-line machine runs (the recursion is in
the body IH between them). `ClosureEntrySpec` composes the `env_new` /
`env_define` callee contracts; `ClosureRetSpec` composes one `value_null` / a
24-byte copy. Named exactly as `callAssertOk` names `NativeAssertOkSpec`. -/

/-- **Seam (a): the closure prefix.** From the `EX_CALL` dispatch entry
(`CallEntryP` at `callDispatchPC`, with `fv = .closure a` staged and the argument
vector `vs` materialised) the machine runs the closure branch — arity check
(`a_2`), depth guard (`a_3`), `jal env_new` = `allocFrame (some cd.env)` (`a_4`),
and the `env_define` param-bind fold — to the body `ExecSeq` loop head
(`callBodyLoopPC`) in the fresh frame `frame` over the bound child store, at depth
`d+1`. This is the `SegEntry` shape the body IH consumes.

Discharged (future) by threading the closure-branch decode ≫ `env_new_spec`
(`EnvNewSpec`) ≫ the `env_define` fold (`EnvDefineClose`/`ReallocSpec`). -/
def ClosureEntrySpec
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
    (store' : Store) (frame : Addr) (dLeft aLeft : Nat) (m0 : Mem) : Prop :=
  ∀ (φf' φc' : Addr → Nat) (m0' : Mem),
    Triple
      (CallEntryP g N A SL φf φc st d dLeft aLeft m0)
      (SegEntry g N A SL φf' φc'
        (closureBoundSt st store' cd vs frame) (d + 1) (dLeft - 1) (aLeft - 1)
        callBodyLoopPC m0')

/-- **Seam (c): the closure return.** From the body-sequence exit
(`SegExit` at `callBodyRetPC` with the body result `st'`/`status`) the machine
runs the return marshalling — `status` classification (`a_6`), `--call_depth`,
and the result copy (`value_null` on `.normal`, the 24-byte body-sret→CALL-sret
copy on `.ret v`) — to the epilogue join (`CallExitP` at `callJoinPC`).

Discharged (future) by the return-block reflection (one `value_null` sub-call /
a 24-byte `memcpy`; no recursion, no callee alloc). -/
def ClosureRetSpec
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : SpecSt) (status : Status) (m0 : Mem) : Prop :=
  ∀ (φf' φc' : Addr → Nat) (m0' : Mem),
    Triple
      (SegExit g N A SL φf' φc' st' callBodyRetPC m0')
      (CallExitP g N A SL φf φc st' m0)

/-! ## `callClosureSim` — the `Call.closure` crux as a machine Triple

Composes the three seams `prefix ≫ body-IH ≫ return` into the `mCall`-shape
Triple. CONDITIONAL on the two straight-line seam residuals (`ClosureEntrySpec`,
`ClosureRetSpec`); the recursion is discharged UNCONDITIONALLY by the body IH
`hBodyIH` (the `mExecSeq` the recursor supplies). The `Call.closure` spec
premises are threaded: `a_2` (arity) and `a_3` (depth) gate the prefix path,
`a_4` (allocFrame) fixes `frame`/`store'`, `a_5` (body derivation) is the IH's
index, `a_6` classifies `status` for the return. -/
theorem callClosureSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
    (store' : Store) (frame : Addr) (status : Status) (v : Value)
    (dLeft aLeft : Nat) (m0 : Mem)
    (_hClos : st.store.closures[a]? = some cd)
    (_hArity : vs.length = cd.params.length)
    (_hDepth : d < maxCallDepth)
    (_hAlloc : st.store.allocFrame (some cd.env) = (store', frame))
    (_hStatus : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v)
    -- the recursive body IH (the `mExecSeq` the recursor supplies), instantiated
    -- at the closure body-loop head/return PCs:
    (hBodyIH :
      Triple
        (SegEntry g N A SL φf φc
          (closureBoundSt st store' cd vs frame) (d + 1) (dLeft - 1) (aLeft - 1)
          callBodyLoopPC m0)
        (SegExit g N A SL φf φc st' callBodyRetPC m0))
    -- the two straight-line seam residuals:
    (hEntry : ClosureEntrySpec g N A SL φf φc st d a cd vs store' frame dLeft aLeft m0)
    (hRet : ClosureRetSpec g N A SL φf φc st' status m0) :
    Triple
      (CallEntryP g N A SL φf φc st d dLeft aLeft m0)
      (CallExitP g N A SL φf φc st' m0) :=
  -- prefix ≫ body ≫ return
  Triple.seq (Triple.seq (hEntry φf φc m0) hBodyIH) (hRet φf φc m0)

end Vsa.Sim
