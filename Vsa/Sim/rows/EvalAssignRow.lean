import Vsa.Sim.EvalRecCommon
import Vsa.Sim.TermSimAssembly

/-!
# `EvalAssignRow` — the `hAssign` recursor case row (`EvalE.assign`, CONDITIONAL)

The `assign x e` case of `term_sim_of_cases`/`term_sim_of_closed`
(`TermCaseBundle.hAssign`, verbatim):

```
∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt)
  (v : Value) (store'' : Store) (a : EvalE st d env e st' v)
  (a_1 : st'.store.set? env x v = some store''),
  mEvalE st d env e st' v a →
  mEvalE st d env (Expr.assign x e) { store := store'', out := st'.out } v
    (EvalE.assign st d env x e st' v store'' a a_1)
```

which is `EvalRecCommon.EvalIH st d env (.assign x e) ⟨store'', st'.out⟩ v` by
definitional unfolding (`TermSimAssembly.mEvalE = EvalRecCommon.EvalIH`), and the
sub-derivation IH `mEvalE st d env e st' v a` is `EvalIH st d env e st' v` by the SAME
unfolding — passed straight through, no adapter.

## The decoded assign arm (verified against `experiments/disasm.txt:3477–3484,3488–3495`)

`eval_expr`'s jump-table dispatch (`jr a5` @ `0x800031ac`, table @ `0x80019f58`)
routes `Expr.assign` to the arm entry `0x8000347c`:

```
8000347c  ld   a2,16(a2)        -- a2 := expr->child[16] = the RHS node `e`   [ARM ENTRY]
80003480  addi a0,sp,240        -- a0 := sret buffer (sub-eval result, in-frame @ sp+240)
80003484  sd   a3,0(sp)         -- spill a3 (env) across the sub-call
80003488  jal  eval_expr        -- link 0x8000348c; the recursive sub-derivation (EvalIH for `e`)
8000348c  ld   a1,8(s0)         -- a1 := expr->name[8]   (the assign target name `x`)
80003490  ld   a6,240(sp)       -- reload the 24-byte sub-eval value word0
80003494  ld   a4,248(sp)       --   … word1
80003498  ld   a5,256(sp)       --   … word2
8000349c  ld   a0,0(sp)         -- a0 := env  (reload the spill)
800034a0  addi a2,sp,64         -- a2 := pv buffer (env_set arg, @ sp+64)
800034a4  sd   a6,64(sp)        -- *pv       := word0
800034a8  sd   a4,72(sp)        -- *(pv+8)   := word1
800034ac  sd   a5,80(sp)        -- *(pv+16)  := word2
800034b0  jal  env_set          -- link 0x800034b4; env_set(env=a0, name=a1, pv=a2) = Store.set?
800034b4  bnez a0,0x80003448    -- a0 = env_set result: NONZERO (found/updated) → shared return
                                --      tail @ 0x80003448 (reload value @240, restore, ret, a0=v);
                                --      a0 == 0 (UNBOUND) → fallthrough to jal runtime_error @0x800034e4
```

**Callee = `env_set`** (entry `0x80002cdc`, `Store.set?` — the parent-chain in-place
update), NOT `env_define`.  The successful path (`a1 = env_set ≠ 0`) rejoins the shared
epilogue at `0x80003448` (identical to the `var` arm's HIT-tail) and returns the value
`v` reloaded from the sret buffer.  So the arm is structurally the `varInit` twin:
`arm-entry ≫ jal eval_expr (EvalIH) ≫ value reload/stage ≫ jal env_set (Store.set?) ≫
return v`.  Arm PC span: `[0x8000347c, 0x800034b8)` for the success path (+ the
`runtime_error` unbound arm at `0x800034b8..0x800034e8`, which is the `EvalErr`
`.assignUnbound` case — off this `hAssign` premise's path since `set? = some store''`).

## Why this row is CONDITIONAL on a named `AssignArmSpec` oracle

There is **no landed `evalAssignSim`** (nor an `env_set` top-level Triple).  Per the
`eval_var_row` precedent (`rows/EvalVarRow.lean`, survey §5 "conditional leaf_bridge":
row now, arm spec later), the row threads the whole assign arm as a named `Triple`
oracle `AssignArmSpec` — the arm's `EvalEntry (.assign x e) → EvalExitD` sim at the
`set?`-updated post store — and CONSUMES the sub-`EvalIH` inside it.  When the assign
arm's machine derivation lands (arg-setup prefix ≫ `jal eval_expr` consuming the IH ≫
value reload/stage ≫ `jal env_set` = `Store.set?` ≫ HIT-return), it discharges
`AssignArmSpec` exactly.  The env_set callee is the `Store.set?` analogue of `varInit`'s
`env_define`; the update path is the `hUpdate_wired` shape (`EnvDefMarshal`) —
`env_set`'s in-place `vars.map (if ·.1==x then (x,v) else ·)` matches `Store.set`'s
`modify`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim.Rows

open Vsa.Sim
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

/-! ## `AssignArmSpec` — the assign-arm oracle (the `O`-class residual)

The whole `Expr.assign x e` arm as an `EvalIH`-shaped sim, ∀-closed over the ghosts:
from the assign arm entry `EvalEntry (.assign x e)`, consuming the sub-`EvalIH` for `e`,
reach `EvalExitD` at the `set?`-updated store `⟨store'', st'.out⟩` and value `v` (the
sub-eval value, unchanged by `set?`).  This is the eval-arm analogue of
`EvalVarEntry.env_get_found` / `ExecVarInitGeom.hGlue` — the genuinely-open field,
discharged once the assign-arm machine derivation (`jal eval_expr` ≫ `jal env_set`)
lands.  It is stated at the EXACT `EvalIH` shape the recursor demands (frame/closure
sizes are the ENTRY store's `st.store.frames.size`/`st.store.closures.size`), so the row
just feeds the sub-`EvalIH` and returns it — the "row now, arm spec later" precedent. -/
def AssignArmSpec (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
    (st' : SpecSt) (v : Value) (store'' : Store) : Prop :=
  EvalIH st d env e st' v →
  EvalIH st d env (Expr.assign x e) ⟨store'', st'.out⟩ v

/-- The assign-case residual: the `AssignArmSpec` oracle, ∀-closed (the sub-eval data
`st'`/`v`/`store''` are recursor-supplied, so the residual is keyed on them). -/
def AssignResid (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
    (st' : SpecSt) (v : Value) (store'' : Store) : Prop :=
  AssignArmSpec st d env x e st' v store''

/-- Route `hAssign` → the `AssignArmSpec` oracle.  CONDITIONAL (the `eval_var_row`
precedent): no `evalAssignSim` exists yet, so the whole arm is threaded as the named
`AssignArmSpec` residual, which consumes the sub-`EvalIH` (`mEvalE … a = EvalIH …` by
`rfl`) and yields the `hAssign` motive. -/
theorem eval_assign_row
    (hR : ∀ st d env x e st' v store'', AssignResid st d env x e st' v store'') :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt)
      (v : Value) (store'' : Store) (a : EvalE st d env e st' v)
      (a_1 : st'.store.set? env x v = some store''),
      mEvalE st d env e st' v a →
      mEvalE st d env (Expr.assign x e) { store := store'', out := st'.out } v
        (EvalE.assign st d env x e st' v store'' a a_1) := by
  intro st d env x e st' v store'' a hset ihE
  show Vsa.Sim.EvalIH st d env (.assign x e) ⟨store'', st'.out⟩ v
  exact hR st d env x e st' v store'' ihE

/-- **Slot-verify.** `eval_assign_row` fills the EXACT `hAssign` minor-premise slot of
`TermCaseBundle.TermCases.hAssign`: the type below is the verbatim premise type; the
term type-checks iff the row's conclusion matches it. -/
theorem eval_assign_row_fills_hAssign
    (hR : ∀ st d env x e st' v store'', AssignResid st d env x e st' v store'') :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt)
      (v : Value) (store'' : Store) (a : EvalE st d env e st' v)
      (a_1 : st'.store.set? env x v = some store''),
      mEvalE st d env e st' v a →
      mEvalE st d env (Expr.assign x e) { store := store'', out := st'.out } v
        (EvalE.assign st d env x e st' v store'' a a_1) :=
  eval_assign_row hR

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.eval_assign_row
#print axioms Vsa.Sim.Rows.eval_assign_row_fills_hAssign
