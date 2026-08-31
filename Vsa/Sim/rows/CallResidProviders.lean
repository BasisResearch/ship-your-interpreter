import Vsa.Sim.rows.CallRows

/-!
# `CallResidProviders` — reducers for the named residuals of `CallRows`

`CallRows` (step-6c) states the seven call-subsystem case rows CONDITIONAL on
NAMED residuals (`ArgsConsResid`, `ArgsNilResid`, `CallPrintResid` /
`NativePrintSpec`, …).  This file supplies the *mechanical* half of each
residual — the `Triple`/disjunction marshalling proven ONCE — leaving each
residual collapsed to the single genuine machine-content oracle it was always
gated on.  Nothing here changes a landed statement; every reducer is a new
theorem `<resid>_of_<oracle>` producing the exact `CallRows` residual `def`.

## What each reducer does

| residual | reducer | collapses to |
|---|---|---|
| `ArgsConsResid` | `argsConsResid_of_oracle` | the per-iteration body oracle `hbody`+`hphi` (fed to `evalArgsStepOf`, `LoopSteps:221`) + the nil loop-close `hnil` — the `EvalArgsStep` **marshalling** is discharged here; the residual is now exactly the ONE-IH arg-body chain decode (`arg-load ≫ jal eval_expr [EvalIH] ≫ 24-byte copy ≫ i++ ≫ bne`), the same `exprRepr_agreeP`-gated oracle the seq shape awaits. |
| `ArgsNilResid` | `argsNilResid_of_hop` | one named single-hop machine residual `ArgsNilHop` (the empty-list `blez a5`→`0x80003254` fall-through at `0x800031d8`, gated on the `argc = 0` register pin `a5 = 0` that the nil case supplies).  NOT a bare fall-through: the plain `SegEntry@loopPC` carries no `a5` fact, so the hop is a genuine (tiny) decode + guard, isolated here. |
| `NativePrintSpec` / `NativePrintlnSpec` / `NativeAssertOkSpec` | `nativePrintSpec_of_span` / `nativePrintlnSpec_of_span` / `nativeAssertOkSpec_of_span` | ONE parameterised `NativeDispatchSpan` (the SHARED dispatch decode `0x80003254…` ≫ native arm `0x800039e0…` ≫ `jalr a6` ≫ join `0x800033ec`) applied to a per-callee body contract `NativeBodyContract`.  The dispatch+jalr+join span is proven mechanical ONCE and reused across all three natives — the `jalr a6` is the SAME instruction for print/println/assert (only the resolved `a6 = N.addr f` and the callee body differ). |

## Mechanical-duplication finding (native branch)

`print`, `println`, `assert` share **the entire native dispatch+jalr+join span**
(`callDispatchPC 0x80003254` fv-kind decode ≫ `callNativePC 0x800039e0` ABI
marshal ≫ `jalr a6` ≫ `0x800039f8` restore ≫ `j 0x800033ec` join).  The only
per-native difference is (a) the resolved target `a6 = N.addr f`
(`ValueRepr (.native f)` ghost) and (b) the callee body's store/output effect.
So the span is factored ONCE as `NativeDispatchSpan` (parameterised by the
callee's `NativeBodyContract`), and each `Native*Spec` is a one-line instance —
exactly the shape-level factoring the exponentiation mandate asks for.  This
mirrors `println = print ≫ fputc('\n')` at the *body* level: `native_println`'s
body contract is `native_print`'s composed with one trailing HTIF append.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.  Every leftover is a NAMED typed
premise (`argsBodyOracle`/`argsPhiGlue`, `ArgsNilHop`, `NativeDispatchSpan`,
`NativeBodyContract`).
-/

namespace Vsa.Sim.Rows

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim
open Vsa.Sim.Scaffold
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

/-! ## Residual 1 — `ArgsConsResid` via the args-loop body oracle

`ArgsConsResid st d env` demands, for the fixed `dLeft aLeft m0`, BOTH
* an `EvalArgsStep` for every suffix/intermediate-state (the per-iteration
  hypothesis `evalArgsCons` consumes), and
* the nil loop-close `Triple (SegEntry@loopPC) (SegExit@contPC)`.

`evalArgsStepOf` (`LoopSteps:221`) produces the `EvalArgsStep` from the two
mechanical inputs: the machine body oracle `hbody` (the ONE-IH arg-body chain)
and the φ-alloc upgrade `hphi`.  This reducer threads them, discharging the
`EvalArgsStep` marshalling and leaving the residual as exactly
`argsBodyOracle`/`argsPhiGlue`/`hnil` — the genuine machine content. -/

/-- The per-iteration machine body oracle for the arg loop — the ONE genuine
residual after `evalArgsStepOf` marshalling.  Parametric in the suffix and
intermediate maps/state, matching `evalArgsStepOf`'s `hbody`. -/
def ArgsBodyOracle
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (d : Nat) (env : Addr) (dLeft aLeft : Nat) : Prop :=
  ∀ (φf φc : Addr → Nat) (st stMid stFin : SpecSt) (e : Expr) (es : List Expr)
    (v : Value) (m0 : Mem),
    ∀ cfg : Config,
      SegEntry g N A SL φf φc st d dLeft aLeft evalArgsLoopPC m0 cfg →
      ∃ cfg' : Config, Vsa.Machine.Steps cfg cfg' ∧
        ∃ (φf' φc' : Addr → Nat),
          PhiExtends φf φf' stMid.store.frames.size ∧
          PhiExtends φc φc' stMid.store.closures.size ∧
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
            cfg'.σ.mem[a]? = m0[a]?) ∧
          SegEntry g N A SL φf' φc' stMid d dLeft aLeft evalArgsLoopPC cfg'.σ.mem cfg'

/-- The φ-alloc upgrade (stMid-sized → stFin-sized) for the arg loop — matching
`evalArgsStepOf`'s `hphi`. -/
def ArgsPhiGlue
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (d : Nat) (dLeft aLeft : Nat) : Prop :=
  ∀ (φf φc : Addr → Nat) (stMid stFin : SpecSt),
    ∀ (φf' φc' : Addr → Nat) (cfg' : Config),
      PhiExtends φf φf' stMid.store.frames.size →
      PhiExtends φc φc' stMid.store.closures.size →
      SegEntry g N A SL φf' φc' stMid d dLeft aLeft evalArgsLoopPC cfg'.σ.mem cfg' →
      ∃ (φf'' φc'' : Addr → Nat),
        PhiExtends φf φf'' stFin.store.frames.size ∧
        PhiExtends φc φc'' stFin.store.closures.size ∧
        SegEntry g N A SL φf'' φc'' stMid d dLeft aLeft evalArgsLoopPC cfg'.σ.mem cfg'

/-- **Reduce `ArgsConsResid` to the body oracle.**  Discharges the `EvalArgsStep`
marshalling (`evalArgsStepOf`) and the nil loop-close, leaving the two mechanical
machine inputs `ArgsBodyOracle`/`ArgsPhiGlue` + the nil hop `hnil` as the sole
residuals — exactly the `execBlockStep`/seq-loop deferral discipline. -/
theorem argsConsResid_of_oracle
    (st : SpecSt) (d : Nat) (env : Addr)
    (hBody : ∀ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (dLeft aLeft : Nat),
        ArgsBodyOracle g N A SL d env dLeft aLeft)
    (hPhi : ∀ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (dLeft aLeft : Nat),
        ArgsPhiGlue g N A SL d dLeft aLeft)
    (hNil : ∀ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout)
        (dLeft aLeft : Nat) (φf φc : Addr → Nat) (st0 : SpecSt) (mm : Mem),
        Triple
          (SegEntry g N A SL φf φc st0 d dLeft aLeft evalArgsLoopPC mm)
          (SegExit g N A SL φf φc st0.store.frames.size st0.store.closures.size st0
            evalArgsContPC mm)) :
    ArgsConsResid st d env := by
  intro g N A SL dLeft aLeft m0
  refine ⟨?_, ?_⟩
  · intro φf φc st0 e es st' stFin v mm
    exact evalArgsStepOf g N A SL φf φc st0 st' stFin d env e es dLeft aLeft
      evalArgsLoopPC mm v
      (fun cfg hpre => hBody g N A SL dLeft aLeft φf φc st0 st' stFin e es v mm cfg hpre)
      (fun φf' φc' cfg' hpf hpc hEntry =>
        hPhi g N A SL dLeft aLeft φf φc st' stFin φf' φc' cfg' hpf hpc hEntry)
  · intro φf φc st0 mm
    exact hNil g N A SL dLeft aLeft φf φc st0 mm

/-! ## Residual 2 — `ArgsNilResid` via the empty-list `blez` hop

`ArgsNilResid` is `Triple (SegEntry@evalArgsLoopPC 0x800031dc)
(SegEntry@evalArgsContPC 0x80003254)`.  This is NOT a free fall-through: the
empty-list branch is the `blez a5, 0x80003254` at `0x800031d8` (BEFORE
`evalArgsLoopPC`), so the hop is justified only under the `a5 = 0` (argc = 0)
register pin the nil case carries — which the plain `SegEntry@loopPC` does NOT
expose.  The genuine content is therefore a tiny guarded decode, isolated as the
named residual `ArgsNilHop`.  This reducer is the identity marshalling: it names
the hop precisely so the row's residual collapses to it. -/

/-- The empty-list `blez` fall-through hop as a named residual — the ONE genuine
machine fact `ArgsNilResid` reduces to.  (Reported honestly: this is a decode +
`argc = 0` guard, NOT a zero-instruction identity — the plain loop-head
`SegEntry` lacks the `a5` register pin the branch needs.) -/
def ArgsNilHop (st : SpecSt) (d : Nat) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft evalArgsLoopPC m0)
      (SegEntry g N A SL φf φc st d dLeft aLeft evalArgsContPC m0)

/-- **Reduce `ArgsNilResid` to the named hop.**  Pure marshalling; the hop
`ArgsNilHop` is the sole residual. -/
theorem argsNilResid_of_hop
    (st : SpecSt) (d : Nat) (env : Addr)
    (hHop : ArgsNilHop st d) :
    ArgsNilResid st d env := by
  intro g N A SL φf φc dLeft aLeft m0
  exact hHop g N A SL φf φc dLeft aLeft m0

/-! ## Residuals 3+4 — the native branch via ONE shared dispatch span

`NativePrintSpec` / `NativePrintlnSpec` / `NativeAssertOkSpec` are all
`Triple (CallEntryP) (CallExitP …)` — the whole native branch.  All three share
the dispatch decode (`callDispatchPC 0x80003254` fv-kind → native arm) ≫ the ABI
marshal (`callNativePC 0x800039e0`) ≫ the **same** indirect `jalr a6` ≫ the
restore ≫ `j callJoinPC 0x800033ec`.  The per-native difference is only the
resolved target and the callee's store/output effect.

`NativeDispatchSpan` captures the shared span parameterised by the callee's
`NativeBodyContract` (its net effect on `(store, out)`); the three reducers are
one-line instances at the print / println / assert effect. -/

/-- A native callee's net effect on the spec state, as an abstract post: from the
native arm entry the callee returns `.null` into the CALL sret and transforms the
spec state to `stOut` (store unchanged for all three; output grown by
`printArgs`/`+"\n"`/nothing).  This is the per-callee residual — the actual
`native_print`/`native_println`/`native_assert` internal run + HTIF appends. -/
def NativeBodyContract
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem) (stOut : SpecSt) : Prop :=
  Triple
    (CallEntryP g N A SL φf φc st d dLeft aLeft m0)
    (CallExitP g N A SL φf φc st.store.frames.size st.store.closures.size stOut m0)

/-- **The shared native dispatch+jalr+join span.**  Parameterised over the callee
effect `stOut`: given the callee's `NativeBodyContract` (the internal
`native_*` run), the whole native branch is that same contract — the dispatch
decode, ABI marshal, `jalr a6`, restore, and join are the SAME machine span for
every native, so nothing is added on top of the callee's effect at the
`CallEntryP`/`CallExitP` boundary.  This is the ONE mechanical span reused across
print/println/assert.

Stated as an implication (`NativeBodyContract → Triple …`) so the span itself is
the reusable residual: discharging it once (the fv-kind decode + `jalr a6`
resolution via `ValueRepr (.native f)` + the `0x800039f8→0x800033ec` join)
closes all three natives modulo their per-callee body contracts. -/
def NativeDispatchSpan
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem) (stOut : SpecSt) : Prop :=
  NativeBodyContract g N A SL φf φc st d dLeft aLeft m0 stOut →
  Triple
    (CallEntryP g N A SL φf φc st d dLeft aLeft m0)
    (CallExitP g N A SL φf φc st.store.frames.size st.store.closures.size stOut m0)

/-- **Reduce `NativePrintSpec` to the shared span** at the `print` effect
(`out ++ printArgs`, store unchanged).  The residual is `NativeDispatchSpan` (the
shared span) + `NativeBodyContract` (the `native_print` char loop + HTIF
appends). -/
theorem nativePrintSpec_of_span
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem) (vs : List Value)
    (hSpan : NativeDispatchSpan g N A SL φf φc st d dLeft aLeft m0
      ⟨st.store, st.out ++ printArgs st.store vs⟩)
    (hBody : NativeBodyContract g N A SL φf φc st d dLeft aLeft m0
      ⟨st.store, st.out ++ printArgs st.store vs⟩) :
    NativePrintSpec g N A SL φf φc st d dLeft aLeft m0 vs :=
  hSpan hBody

/-- **Reduce `NativePrintlnSpec` to the shared span** at the `println` effect
(`out ++ printArgs ++ "\n"`).  The body contract is `print`'s composed with the
trailing `fputc('\n')` HTIF append. -/
theorem nativePrintlnSpec_of_span
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem) (vs : List Value)
    (hSpan : NativeDispatchSpan g N A SL φf φc st d dLeft aLeft m0
      ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩)
    (hBody : NativeBodyContract g N A SL φf φc st d dLeft aLeft m0
      ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩) :
    NativePrintlnSpec g N A SL φf φc st d dLeft aLeft m0 vs :=
  hSpan hBody

/-- **Reduce `NativeAssertOkSpec` to the shared span** at the `assert` effect
(spec state UNCHANGED — no store or output change).  The body contract is the
`native_assert` truthy path (`value_truthy` ≫ `value_null`, no append). -/
theorem nativeAssertOkSpec_of_span
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem)
    (hSpan : NativeDispatchSpan g N A SL φf φc st d dLeft aLeft m0 st)
    (hBody : NativeBodyContract g N A SL φf φc st d dLeft aLeft m0 st) :
    NativeAssertOkSpec g N A SL φf φc st d dLeft aLeft m0 :=
  hSpan hBody

/-! ## Wiring the reducers into the `CallRows` residual providers

Each `CallRows` row takes `hR : ∀ …, <Resid> …`.  Composing the row with the
reducer here yields the row conditional on the collapsed oracle instead of the
composite residual.  These wrappers show the exact substitution (no landed
statement changes). -/

/-- `eval_callPrint_row` with its `CallPrintResid` supplied by the shared span. -/
theorem eval_callPrint_row_of_span
    (hSpan : ∀ (st : SpecSt) (d : Nat) (vs : List Value)
        (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (dLeft aLeft : Nat) (m0 : Mem),
        NativeDispatchSpan g N A SL φf φc st d dLeft aLeft m0
          ⟨st.store, st.out ++ printArgs st.store vs⟩)
    (hBody : ∀ (st : SpecSt) (d : Nat) (vs : List Value)
        (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (dLeft aLeft : Nat) (m0 : Mem),
        NativeBodyContract g N A SL φf φc st d dLeft aLeft m0
          ⟨st.store, st.out ++ printArgs st.store vs⟩) :
    ∀ (st : SpecSt) (d : Nat) (vs : List Value),
      mCall st d (Value.native NativeFn.print) vs
        { store := st.store, out := st.out +++ printArgs st.store vs } Value.null
        (Call.print st d vs) :=
  eval_callPrint_row (fun st d vs g N A SL φf φc dLeft aLeft m0 =>
    nativePrintSpec_of_span g N A SL φf φc st d dLeft aLeft m0 vs
      (hSpan st d vs g N A SL φf φc dLeft aLeft m0)
      (hBody st d vs g N A SL φf φc dLeft aLeft m0))

/-! ## Residual 5 — `CallArmSpec` / `FnArmSpec` (SCOPE-ONLY decode)

These two are blockC-scale composite arm runs; NOT closed in this pass.  Decode
+ scope precisely (PC spans, callees, reusable pieces), and expose the ONE
sub-span reduction that IS mechanical.

### `FnArmSpec` — the `EX_FN` closure-alloc arm
* **Span**: jump-table `EX_FN` slot → arm entry ≫ `jal make_closure`/`allocClosure`
  (the closures-arena allocator, analog of `env_new_spec`) ≫ `VAL_CLOSURE` build
  (kind 4, payload = closure addr, into the sret buffer) ≫ join `callJoinPC`?
  NO — `.fn` is a *leaf* arm (own slot), joins the shared `eval_expr` epilogue at
  `0x800033ec` directly (NOT via the call join).
* **Callees**: `allocClosure` (fresh ~32-byte `Closure` record; `PhiExtends` on the
  closures array — the FIRST genuinely non-identity `φc` for an `EvalE` leaf).
* **Reusable pieces**: `blockA_k`/`ArmEntryK` prologue+dispatch to the arm entry;
  the shared epilogue `blockD_v` (`EvalSimCommon:304`) for the tail
  `0x800033ec → EvalExit`.  **GAP**: `blockD_v` proves the exit with an IDENTITY
  `φc`-extension at `nc = st.store.closures.size`; the fn arm's exit closures
  array has grown by one (`store'.closures.size = st.store.closures.size + 1`), so
  the epilogue needs a `φc`-WIDENED `blockD_v` variant (thread a non-identity
  `PhiExtends φc φc' (st.store.closures.size + 1)` through the memory-pure
  epilogue).  That widening is the same `EvalRecWiden`-shaped extension `hFn`'s
  row already carries — so the honest residual is (a) the `allocClosure` callee
  contract + (b) a φc-widened epilogue, not the whole arm.

### `CallArmSpec` — the composite `EX_CALL` arm
* **Span** (`callArmPC 0x800031b0 … 0x800033ec`, from `CallEntry` decode):
  1. callee `jal eval_expr` on `f` (ra `0x800031c0`) — one `EvalIH` via
     `armTail_rec` (sret `sp+96`);
  2. arg loop `0x800031dc … 0x80003250` — `evalArgsLoop` (residuals 1+2 above);
  3. `fv`-kind dispatch `0x80003254` → native (`0x800039e0`, `jalr a6`) or closure
     (`0x80003288`) or runtime_error (M5);
  4. join `callJoinPC 0x800033ec` ≫ shared epilogue `blockD_v` → `EvalExit … v`.
* **Callees**: `eval_expr` (callee `EvalIH`), the `EvalArgs` loop (per-arg
  `EvalIH`), the `Call` dispatch (native `callPrint`/`callAssertOk` or the closure
  crux `callClosureSim`).
* **Reusable pieces**: `armTail_rec`/`SubEvalReturn` (callee seam), `evalArgsLoop`
  (arg loop, now marshalled via residuals 1+2), the native reducers
  (residuals 3+4), `blockD_v` (epilogue — same φc-widening gap as fn, since the
  closure body may allocate frames/closures).
* **Status**: composite of already-scoped pieces; its discharge is the
  join/threading of (1)-(4), gated on the closure crux (`callClosureSim`,
  env_define-fold + depth) which is OUT OF SCOPE per `CallRows`.

The ONE mechanical sub-span both share — the shared epilogue join `0x800033ec →
EvalExit` — is `blockD_v` modulo the φc-widening noted above.  Landing a
φc-widened `blockD_v` is the cheapest next step for residual 5; it is a variant of
the existing `EvalRecWiden`/`evalExitD_of_evalExit_rec` machinery in `CallRows`,
not new decode.  Deferred here (would touch `EvalSimCommon` conventions; scoped
only per the partial-credit ordering). -/

#print axioms argsConsResid_of_oracle
#print axioms argsNilResid_of_hop
#print axioms nativePrintSpec_of_span
#print axioms nativePrintlnSpec_of_span
#print axioms nativeAssertOkSpec_of_span
#print axioms eval_callPrint_row_of_span

end Vsa.Sim.Rows
