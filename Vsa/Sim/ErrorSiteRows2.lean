import Vsa.Sim.ErrorSiteRows

/-!
# `ErrorSiteRows2` — Wave-D error-site rows, BATCH 2

`Vsa/Sim/ErrorSiteRows.lean` (the PILOT) established the per-site recipe and
discharged three leaf `errorSimFull` minor premises (`row_hNotCallable`,
`row_hNegType`, `row_hAssertFail`) through the committed row template `errRow`
(a thin wrapper over the L6 combinator `errHalts_exists_of_site`).  This file
continues that fan-out with a **batch** of the next simplest residuals, all via
the SAME `errRow` application — no new machinery.

Each row here states one `errorSimFull` minor premise's exact `∀`-closure
(`Vsa/Sim/ErrorSimFull.lean`, `hVarUndef`…`hSeqTail`), `intro`s every binder,
and applies `errRow g inp … SC out HT T c hsite`.  Because every one of the six
error motives is the *constant* `ErrHalts c`, a minor premise's constructor
arguments (and, for propagation nodes, its sub-derivation IH `ErrHalts c`) are
all ignored — the conclusion is discharged entirely by the shared `SC`/`HT`, the
site's marshalled segment `Triple` `T`, and the reachability link `hsite`,
exactly as in the three pilot rows.

## What this batch lands

Ten more of the 42 residuals, prioritising LEAF error nodes (no sub-derivation
to relate — the ∀-closure ends directly in `→ ErrHalts c`):

* EvalErr leaves: `row_hVarUndef` (undefined variable), `row_hAssignUnbound`
  (assign to unbound name), `row_hBinaryOp` (binary-op type error / e.g.
  division-by-zero — `binOpSem = none`).
* CallErr leaves: `row_hArity` (closure arity mismatch), `row_hDepth`
  (call-depth exceeded), `row_hEscape` (break/continue escaping a call),
  `row_hAssertArity` (assert wrong arity).

Plus three of the simplest EvalErr/ExecErr *propagation* nodes (one sub-IH,
also ignored under the constant motive): `row_hUnaryE`, `row_hCallF`,
`row_hExpr`.

Together with the pilot's three, **13 of the 42** `errorSimFull` minor premises
are now discharged as rows.  The remaining rows follow the identical shape; the
only genuinely per-row artefact (deferred to L7/L8) is the site's segment
`Triple` `T` and the reachability link `hsite`, taken here as hypotheses exactly
as the pilot does.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.  This file adds no
reflection of its own (no `#derive_case` here — the pilot already pinned recipe
step 2 on a real error-site body); every row is one `errRow` application, so the
per-file elaboration cost is small and constant (rule 7).  Timing witness: see
the commit gate (`lake env lean Vsa/Sim/ErrorSiteRows2.lean`).
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.Logic (Triple)
open Vsa.While

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

section Rows2

/-! ### EvalErr leaf nodes -/

/-- Row for `EvalErr.varUndef` (`hVarUndef`): reading an unbound variable reaches
its `jal runtime_error` node. -/
theorem row_hVarUndef
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String),
      st.store.get? env x = none → ErrHalts c :=
  fun _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT T c hsite

/-- Row for `EvalErr.assignUnbound` (`hAssignUnbound`): assigning to an unbound
name reaches its `jal runtime_error` node. -/
theorem row_hAssignUnbound
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → st'.store.set? env x v = none → ErrHalts c :=
  fun _ _ _ _ _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT T c hsite

/-- Row for `EvalErr.binaryOp` (`hBinaryOp`): a binary op whose semantics is
`none` (type error / division-by-zero) reaches its `jal runtime_error` node. -/
theorem row_hBinaryOp
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : SpecSt) (lv rv : Value),
      EvalE st d env l st' lv → EvalE st' d env r st'' rv →
      binOpSem st''.store op lv rv = none → ErrHalts c :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT T c hsite

/-! ### CallErr leaf nodes -/

/-- Row for `CallErr.arity` (`hArity`): calling a closure with the wrong number
of arguments reaches its `jal runtime_error` node. -/
theorem row_hArity
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value),
      st.store.closures[a]? = some cd → vs.length ≠ cd.params.length → ErrHalts c :=
  fun _ _ _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT T c hsite

/-- Row for `CallErr.depth` (`hDepth`): a call exceeding `maxCallDepth` reaches
its `jal runtime_error` node. -/
theorem row_hDepth
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      ¬ d < maxCallDepth → ErrHalts c :=
  fun _ _ _ _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT T c hsite

/-- Row for `CallErr.escape` (`hEscape`): a `break`/`continue` escaping a call
body reaches its `jal runtime_error` node. -/
theorem row_hEscape
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      d < maxCallDepth → st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
        st.out⟩ (d + 1) frame cd.body st' status →
      (status = .brk ∨ status = .cont) → ErrHalts c :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT T c hsite

/-- Row for `CallErr.assertArity` (`hAssertArity`): calling `assert` with the
wrong number of arguments reaches its `jal runtime_error` node. -/
theorem row_hAssertArity
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∀ (st : SpecSt) (d : Nat) (vs : List Value),
      (∀ v, vs ≠ [v]) → (∀ v m, vs ≠ [v, m]) → ErrHalts c :=
  fun _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT T c hsite

/-! ### Simplest propagation nodes (one sub-IH, ignored under the constant motive) -/

/-- Row for `EvalErr.unaryE` (`hUnaryE`): a unary op whose operand errors reaches
its `jal runtime_error` node. -/
theorem row_hUnaryE
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : UnOp) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c :=
  fun _ _ _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT T c hsite

/-- Row for `EvalErr.callF` (`hCallF`): a call whose callee-expression errors
reaches its `jal runtime_error` node. -/
theorem row_hCallF
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr),
      EvalErr st d env f → ErrHalts c → ErrHalts c :=
  fun _ _ _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT T c hsite

/-- Row for `ExecErr.expr` (`hExpr`): an expression statement whose expression
errors reaches its `jal runtime_error` node. -/
theorem row_hExpr
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c :=
  fun _ _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT T c hsite

end Rows2

#print axioms row_hVarUndef
#print axioms row_hAssignUnbound
#print axioms row_hBinaryOp
#print axioms row_hArity
#print axioms row_hDepth
#print axioms row_hEscape
#print axioms row_hAssertArity
#print axioms row_hUnaryE
#print axioms row_hCallF
#print axioms row_hExpr

end Vsa.Sim
