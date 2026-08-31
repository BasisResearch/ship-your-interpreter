import Vsa.Sim.EvalFn
import Vsa.Sim.EvalCall
import Vsa.Sim.rows.EvalAssignRow
import Vsa.Sim.rows.CallArmEpilogue
import Vsa.Sim.EvalSimCommon
import Vsa.Sim.TripleCat

/-!
# `ArmSpecBridge` — `armSpec_of_seams`: the composite-arm oracle combinator family

The three composite-arm oracles — `FnArmSpec` (`EvalFn`), `AssignArmSpec`
(`rows/EvalAssignRow`), `CallArmSpec` (`EvalCall`) — plus the remainder of
`StrArmPrologue` all share ONE composition shape:

```
  arm-entry linkage  ≫  sub-EvalIH splice(s)  ≫  the GENERATED seams  ≫
    box/store marshalling  ≫  blockD_v(_phic) epilogue  →  the oracle conclusion.
```

This file factors that shape into a combinator FAMILY (one per sub-IH arity),
each a thin `Triple.seq`/`Triple.dimap` gluing of NAMED, typed inputs.  The genuine
gaps in each arm — the parts the LANDED seams do not yet supply — are the fields
of a per-arm `*Geom` structure (the established `NegExtras`/`VarCallLinkage`/
`CallClosureGeom` pattern): a `*Geom` instance carries exactly the entry-widening
bridge, the seam-run `Triple`s in order, and the φ-extension/marshalling facts, so
the combinator's proof is pure composition with NO machine reasoning.

## Why a FAMILY, not one combinator

The three oracles are the SAME shape but at DIFFERENT type indices, and factoring
them under one signature would hide, not reveal, their structure:

* **`FnArmSpec`** (arity 0): a machine `Triple (EvalEntry (.fn …)) (EvalExit …)`.
  No sub-`EvalE` is evaluated (the closure captures the env by pointer); the arm is
  `dispatch ≫ malloc-call ≫ VAL_CLOSURE-build ≫ epilogue`.  The closures array grows
  by one, so the epilogue is `blockD_v_phic` at `PhiExtends φc φc' nc` (frames fixed).

* **`AssignArmSpec`** (arity 1): NOT a machine Triple — it is stated at the
  `EvalIH`-level (`EvalIH (.assign x e) …`), taking one sub-`EvalIH` for `e`.  Its
  combinator is a pure `EvalIH → EvalIH` implication; the machine content lives one
  layer down (the assign arm's `EvalEntry (.assign x e) → EvalExit` sim, which a
  future `evalAssignSim` supplies as an `AssignArmMachine` field and the combinator
  just re-wraps).  The store is `set?`-updated in place, so `st' = ⟨store'', st'.out⟩`
  keeps the ENTRY frame/closure sizes (identity φ).

* **`CallArmSpec`** (arity 3): a machine `Triple (EvalEntry (.call f args)) (EvalExit …)`
  taking the callee `EvalIH`, the `EvalArgs`, and the `Call` sub-derivations.  The
  closure body may allocate both frames and closures, so the epilogue is
  `blockD_v_phic` at BOTH `PhiExtends φf φf' nf` and `PhiExtends φc φc' nc`.

Their SHARED spine is `blockD_v_phic` (the φ-widened epilogue, `CallArmEpilogue`);
`ArmSpecBridge` supplies the three entry/seam glues that feed it, each closed modulo
its `*Geom` residual.

## Per-oracle verdict (closed-modulo-what)

* `fnArmSpec_of_geom`  — CLOSED modulo `FnArmGeom` (entry→dispatch bridge; the
  malloc≫build seam-run as a `Triple` to `PreEpilogueV`; the `PhiExtends φc φc' nc`
  from `allocClosure`).  Pure `Triple.seq` + `blockD_v_phic`.
* `assignArmSpec_of_machine` — CLOSED modulo `AssignArmMachine` (the assign arm's
  `EvalEntry (.assign x e) → EvalExitD` sim; a future `evalAssignSim`).  Pure
  `EvalIH`-rewrap.
* `callArmSpec_of_geom` — CLOSED modulo `CallArmGeom` (entry→dispatch bridge; the
  callee-eval seam consuming `hIH_f`; the arg-loop seam consuming `hArgs`; the
  dispatch seam consuming `hCall` to `PreEpilogueV`; the `PhiExtends` pair).  Pure
  `Triple.seq` chain + `blockD_v_phic`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.  Every leftover is a
NAMED typed field of a `*Geom`/`*Machine` structure with a doc comment saying what
supplies it — exactly the `NegExtras`/`VarCallLinkage` deferral discipline.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim
open Vsa.Sim.Rows

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. `FnArmSpec` (arity 0) — `fnArmSpec_of_geom`

The `EX_FN` arm is `dispatch ≫ malloc-call ≫ VAL_CLOSURE-build ≫ epilogue`, a
machine `Triple (EvalEntry (.fn …)) (EvalExit … (.closure a))`.  It has NO
sub-`EvalE` (the closure captures the env by pointer, a leaf-like arm), so the
combinator is a straight three-stage `Triple.seq` with no IH threading:

```
  EvalEntry (.fn …)
    ≫ hDispatch  (blockA_k-analog: EvalEntry → the EX_FN dispatch entry)
    ≫ hSeam      (malloc-call ≫ closure-build: the two GENERATED seams,
                  fnArmMallocCallBridge ≫ fnArmClosureBuildRow, marshalled to
                  PreEpilogueV at the WIDENED φc' the closure alloc produced)
    ≫ blockD_v_phic  (φc-widened shared epilogue → EvalExit … (.closure a))
```

`hDispatch` and `hSeam` are the entry-widening + seam-run residuals (the LANDED
`fnArmMallocCall`/`fnArmClosureBuild` gens are raw `Steps`-chain / `segToTriple`
rows; marshalling their write-log memory into `PreEpilogueV`'s `ValueRepr`/store
representation is the genuine remaining work).  `hpc` is the `allocClosure`
`PhiExtends`.  All are `FnArmGeom` fields. -/

/-- The `EX_FN` arm's composition residual: the two seam-runs packaged as `Triple`s
plus the closure-alloc φ-extension.  A future `EX_FN` decode + `allocClosure`
contract discharges each field; the combinator glues them with `blockD_v_phic`. -/
structure FnArmGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φc' : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (store' : Store) (a : Addr)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    -- the closure-saved callee frame the epilogue restores (as in `PreEpilogueV`).
    (v8 v9 v18 : BitVec 64) (out0 : Array String) (mpre : Mem) : Prop where
  /-- `allocClosure` grows the closures array by one; the fresh closure is witnessed
  at the extended map `φc'`, which extends `φc` over the entry closures. -/
  hpc : PhiExtends φc φc' st.store.closures.size
  /-- The output invariant is preserved across the (allocating) arm. -/
  hout : String.join out0.toList = st.out
  /-- **The whole arm run to the shared epilogue entry**, as a single `Triple` from
  the `.fn` `EvalEntry` to `PreEpilogueV` at the WIDENED closures map `φc'` and the
  post-store `⟨store', st.out⟩` (the `.closure a` value materialised into the sret).
  This is `blockA_k`(EX_FN slot) ≫ `fnArmMallocCallBridge` ≫ `fnArmClosureBuildRow`,
  with the seam `Steps`-chains marshalled into `PreEpilogueV`'s memory/value
  representation — the genuine `EX_FN` machine residual (its decode + `allocClosure`
  contract). -/
  hArm : Triple
    (EvalEntry g N A SL φf φc st d env (.fn name params body) sp r sret aEnv aExpr m0)
    (fun c => PreEpilogueV g N A SL φf φc' ⟨store', st.out⟩ (.closure a)
      sp r sret v8 v9 v18 out0 m0 mpre c)

/-- **`fnArmSpec_of_geom`** — discharge `FnArmSpec` from `FnArmGeom`.  The arm-run
`Triple` reaches `PreEpilogueV` at the widened `φc'`; `blockD_v_phic` (frames fixed
⇒ `PhiExtends φf φf` reflexively, closures widened by `hpc`) carries it to the
`EvalExit` at the ENTRY sizes/maps the oracle demands.  Pure `Triple.seq`. -/
theorem fnArmSpec_of_geom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φc' : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (store' : Store) (a : Addr)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String) (mpre : Mem)
    -- the store the arm ends at (`⟨store', st.out⟩`) has frames unchanged and
    -- closures grown by one, so the entry sizes are ≤ the exit sizes.
    (hfr : st.store.frames.size ≤ store'.frames.size)
    (hcl : st.store.closures.size ≤ store'.closures.size)
    (hG : FnArmGeom g N A SL φf φc φc' st d env name params body store' a
      sp r sret aEnv aExpr m0 v8 v9 v18 out0 mpre) :
    FnArmSpec g N A SL φf φc st d env name params body store' a sp r sret aEnv aExpr m0 := by
  -- `FnArmSpec` = `allocClosure … = (store', a) → Triple (EvalEntry …) (EvalExit …)`.
  intro _hAlloc
  -- `hArm : EvalEntry → PreEpilogueV … φc' …`; `blockD_v_phic` : `PreEpilogueV … φc' … →
  -- EvalExit … φc (entry sizes) …`.  The epilogue is stated over `∃ mpre, PreEpilogueV ∧ Q`;
  -- take `Q := fun _ => True`, discharged trivially.
  have hEpi := blockD_v_phic g N A SL φf φc φf φc'
    st.store.frames.size st.store.closures.size
    ⟨store', st.out⟩ (.closure a) sp r sret v8 v9 v18 out0 m0 (fun _ => True)
    (PhiExtends.refl φf st.store.frames.size) hG.hpc ⟨hfr, hcl⟩
  -- seq the arm-run into the epilogue (padding the epilogue pre with the trivial `Q`).
  refine Triple.seq hG.hArm ?_
  intro c hpre
  obtain ⟨c', hs, hExit, _⟩ := hEpi c ⟨mpre, hpre, trivial⟩
  exact ⟨c', hs, hExit⟩

/-! ## §2. `AssignArmSpec` (arity 1) — `assignArmSpec_of_machine`

`AssignArmSpec` is stated at the `EvalIH` level (NOT a machine Triple):

```
  AssignArmSpec st d env x e st' v store'' :=
    EvalIH st d env e st' v → EvalIH st d env (.assign x e) ⟨store'', st'.out⟩ v
```

`EvalIH … e` and `EvalIH … (.assign x e)` are each `∀ ghosts, Triple (EvalEntry …)
(EvalExitD …)`.  The composition shape is present but its machine content lives one
layer down: the assign arm's `EvalEntry (.assign x e) → EvalExitD` sim (entry ≫ the
`jal eval_expr` splice consuming the sub-`EvalIH` ≫ the value-stage seam ≫ the
`jal env_set` = `Store.set?` splice ≫ HIT-return), which a future `evalAssignSim`
supplies.  Because `set?` updates in place, `st' = ⟨store'', st'.out⟩` keeps the
entry frame/closure sizes (identity φ), so no `blockD_v_phic` widening is needed —
the assign arm returns through the shared `varInit`-twin HIT-tail.

The combinator is therefore a pure `EvalIH`-rewrap: given the machine sim (as a
∀-closed field consuming the sub-`EvalIH`), yield the assign `EvalIH`. -/

/-- The assign arm's machine residual: the whole `EvalEntry (.assign x e) →
EvalExitD` sim, ∀-closed over the ghosts, CONSUMING the sub-`EvalIH` for `e`.  A
future `evalAssignSim` (entry ≫ `jal eval_expr` ⋈ IH ≫ value-stage ≫ `jal env_set`
≫ HIT-return, the `AssignArm{Entry,Stage,Return}Gen` seams + `envSetArmBridge`)
discharges it — the assign twin of `evalNegSim`/`evalVarSim`. -/
def AssignArmMachine (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
    (st' : SpecSt) (v : Value) (store'' : Store) : Prop :=
  EvalIH st d env e st' v →
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    Triple
      (EvalEntry g N A SL φf φc st d env (.assign x e) sp r sret aEnv aExpr m0)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨store'', st'.out⟩ v sp r sret m0)

/-- **`assignArmSpec_of_machine`** — discharge `AssignArmSpec` from
`AssignArmMachine`.  `AssignArmSpec`'s conclusion `EvalIH st d env (.assign x e)
⟨store'', st'.out⟩ v` is, by `EvalIH`'s definition, exactly the ∀-closed `Triple
(EvalEntry (.assign x e)) (EvalExitD …)` at the entry sizes — which is what
`AssignArmMachine (fed the sub-IH)` produces.  Pure re-wrap (the `⟨store'', st'.out⟩`
keeps `st.store.frames.size`/`st.store.closures.size` since `set?` allocates
nothing).  No φ-widening. -/
theorem assignArmSpec_of_machine (st : SpecSt) (d : Nat) (env : Addr) (x : String)
    (e : Expr) (st' : SpecSt) (v : Value) (store'' : Store)
    (hM : AssignArmMachine st d env x e st' v store'') :
    AssignArmSpec st d env x e st' v store'' := by
  -- `AssignArmSpec := EvalIH … e → EvalIH … (.assign x e)`.
  intro hIH
  -- `EvalIH … (.assign x e) ⟨store'', st'.out⟩ v` unfolds to the ∀-closed Triple.
  intro g N A SL φf φc sp r sret aEnv aExpr m0
  exact hM hIH g N A SL φf φc sp r sret aEnv aExpr m0

/-! ## §3. `CallArmSpec` (arity 3) — `callArmSpec_of_geom`

The `EX_CALL` arm is `callee-eval ≫ arg-loop ≫ Call-dispatch ≫ epilogue`, a machine
`Triple (EvalEntry (.call f args)) (EvalExit … v)` taking THREE sub-derivations:
`hIH_f` (the callee `EvalIH`), `hArgs` (`EvalArgs`), `hCall` (`Call`).  The closure
body may allocate both frames and closures, so the epilogue is `blockD_v_phic` at
BOTH φ-maps widened.  The four-stage run is packaged as ONE `Triple` field of
`CallArmGeom` — the entry-to-`PreEpilogueV` sim, into which all three sub-derivations
are threaded — because their branching (which callee, how many args, native vs
closure) is internal to the arm and cannot be exposed as separate stage
preconditions without the full decode.  This mirrors `CallArmSpec`'s own statement
(the residual stated ABOVE the three sub-derivations). -/

/-- The `EX_CALL` arm's composition residual: the whole four-stage run as a single
`Triple` (fed the three sub-derivations) plus the frame/closure φ-extensions.  The
LANDED seams (`CallArmCalleeEvalGen` stage-1, the `CallClosure*Gen` closure crux,
the args loop `EvalArgs`) discharge the internal stages; this field is their
composition to the shared-epilogue entry. -/
structure CallArmGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φf' φc' : Addr → Nat)
    (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr)
    (f : Expr) (args : List Expr) (fval : Value) (vs : List Value) (v : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String) (mpre : Mem) : Prop where
  /-- The closure body may allocate frames; the exit frames map `φf'` extends `φf`
  over the entry frames. -/
  hpf : PhiExtends φf φf' st.store.frames.size
  /-- … and closures; the exit closures map `φc'` extends `φc` over the entry closures. -/
  hpc : PhiExtends φc φc' st.store.closures.size
  /-- store counts only grow across the arm. -/
  hfr : st.store.frames.size ≤ st'''.store.frames.size
  hcl : st.store.closures.size ≤ st'''.store.closures.size
  /-- the output invariant at the shared-epilogue entry. -/
  hout : String.join out0.toList = st'''.out
  /-- **The whole EX_CALL arm run to the shared epilogue entry**, fed the three
  sub-derivations, as a single `Triple` from the `.call` `EvalEntry` to
  `PreEpilogueV` at the WIDENED maps `φf'`/`φc'` and the fully-threaded post-store
  `st'''` (the call result `v` materialised into the sret).  This is
  `blockA_k`(EX_CALL slot) ≫ `CallArmCalleeEvalGen`⋈`hIH_f` ≫ `evalArgsLoop`⋈`hArgs`
  ≫ the `Call` dispatch (`callAssertOk`/`callClosureSim`)⋈`hCall` ≫ marshalling. -/
  hArm :
    EvalIH st d env f st' fval →
    EvalArgs st' d env args st'' vs →
    Call st'' d fval vs st''' v →
    Triple
      (EvalEntry g N A SL φf φc st d env (.call f args) sp r sret aEnv aExpr m0)
      (fun c => PreEpilogueV g N A SL φf' φc' st''' v
        sp r sret v8 v9 v18 out0 m0 mpre c)

/-- **`callArmSpec_of_geom`** — discharge `CallArmSpec` from `CallArmGeom`.  The
three sub-derivations are threaded into `hArm` (yielding the entry-to-`PreEpilogueV`
run at the widened maps); `blockD_v_phic` (both φ-maps widened by `hpf`/`hpc`)
carries it to the `EvalExit` at the ENTRY sizes/maps.  Pure `Triple.seq`. -/
theorem callArmSpec_of_geom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φf' φc' : Addr → Nat)
    (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr)
    (f : Expr) (args : List Expr) (fval : Value) (vs : List Value) (v : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String) (mpre : Mem)
    (hG : CallArmGeom g N A SL φf φc φf' φc' st st' st'' st''' d env f args fval vs v
      sp r sret aEnv aExpr m0 v8 v9 v18 out0 mpre) :
    CallArmSpec g N A SL φf φc st st' st'' st''' d env f args fval vs v
      sp r sret aEnv aExpr m0 := by
  -- `CallArmSpec := EvalIH f → EvalArgs → Call → Triple (EvalEntry) (EvalExit)`.
  intro hIH_f hArgs hCall
  have hEpi := blockD_v_phic g N A SL φf φc φf' φc'
    st.store.frames.size st.store.closures.size
    st''' v sp r sret v8 v9 v18 out0 m0 (fun _ => True)
    hG.hpf hG.hpc ⟨hG.hfr, hG.hcl⟩
  refine Triple.seq (hG.hArm hIH_f hArgs hCall) ?_
  intro c hpre
  obtain ⟨c', hs, hExit, _⟩ := hEpi c ⟨mpre, hpre, trivial⟩
  exact ⟨c', hs, hExit⟩

#print axioms fnArmSpec_of_geom
#print axioms assignArmSpec_of_machine
#print axioms callArmSpec_of_geom

end Vsa.Sim
