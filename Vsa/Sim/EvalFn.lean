import Vsa.Sim.EvalCall

/-!
# Layer 4 — M4: the `EvalE.fn` case (closure allocation, near-leaf)

`EvalE.fn` is a near-leaf `EvalE` constructor: `.fn name params body` allocates a
heap `ClosureData⟨env, name, params, body⟩` capturing the current environment and
returns `.closure a` (the fresh closure address). No sub-expression is evaluated;
the only effect is a single closure allocation:
```
st.store.allocClosure ⟨env, name, params, body⟩ = (store', a)  ⇒
  EvalE st d env (.fn name params body) ⟨store', st.out⟩ (.closure a)
```
On the machine this is the `EX_FN` arm of `eval_expr` (its own jump-table slot):
it calls the closure allocator (`make_closure`/`allocClosure`, analogous to
`env_new` for frames), which writes the ~32-byte `Closure` record into the
closures arena and returns its address, then the arm builds a `VAL_CLOSURE`
`Value` (kind 4, payload = the closure address) into the sret and joins the
shared `eval_expr` epilogue.

This is the FIRST `EvalE` leaf whose φc-map is genuinely non-identity: the
closures array grows by one, so the exit `StoreRepr`/`result` are witnessed at an
EXTENDED `φc'` (`PhiExtends φc φc' (st.store.closures.size + 1)`), the exact
extension `EvalExit`'s existentials were shaped to carry.

Because no `make_closure`/`allocClosure` machine contract exists yet (the
closure-arena analog of `env_new_spec`), and the `EX_FN` arm is not yet decoded,
`evalFnSim` is stated CONDITIONAL on a single named residual `FnArmSpec` — the
whole `EX_FN` arm run (dispatch ≫ closure alloc ≫ `VAL_CLOSURE` build ≫ epilogue)
→ `EvalExit … (.closure a)`. This is the deferral discipline of
`callAssertOk`/`evalCallSim`. Discharging it needs (a) the `EX_FN` arm decode
(a fresh jump-table slot), (b) an `allocClosure` callee contract (fresh
closure record; `PhiExtends` on the closures array), and (c) the shared epilogue
(`blockD_v`). NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Scaffold

local notation "SpecSt" => Vsa.While.St

/-! ## `FnArmSpec` — the `EX_FN` closure-allocation arm residual

From the `EvalEntry` for `.fn name params body`, the `EX_FN` arm — dispatch ≫
`allocClosure` ≫ `VAL_CLOSURE` build ≫ epilogue — runs to the `EvalExit` for the
allocated closure value `.closure a`, at the post-store `⟨store', st.out⟩`
(store grows by the fresh `ClosureData`; output unchanged). The named residual
abstracts the whole arm behind one Triple — the closure-side analog of
`NativeAssertOkSpec`/`CallArmSpec`. Its allocation invariant (`hAlloc`, i.e.
`allocClosure` succeeded with result `(store', a)`) gates the closure-address
payload the arm materialises. -/
def FnArmSpec
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (store' : Store) (a : Addr)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) : Prop :=
  st.store.allocClosure ⟨env, name, params, body⟩ = (store', a) →
  Triple
    (EvalEntry g N A SL φf φc st d env (.fn name params body) sp r sret aEnv aExpr m0)
    (EvalExit g N A SL φf φc ⟨store', st.out⟩ (.closure a) sp r sret m0)

/-- **`evalFnSim`**: the `EvalE.fn` minor premise (closure allocation, near-leaf)
at the machine level, in the recursor motive shape. From the `EvalEntry` for
`.fn name params body`, the `EX_FN` arm allocates the capturing closure
(`allocClosure ⟨env, name, params, body⟩ = (store', a)`) and returns
`.closure a`, running to the `EvalExit` for the post-store `⟨store', st.out⟩`.

CONDITIONAL on `FnArmSpec` — the named `EX_FN` arm residual (dispatch ≫
`allocClosure` ≫ `VAL_CLOSURE` build ≫ epilogue) — into which the allocation fact
`hAlloc` is fed, exactly the deferral pattern of `callAssertOk`/`evalCallSim`. The
`EvalE.fn` spec derivation is threaded (its single `allocClosure` premise
determines `(store', a)`). This is the first `EvalE` leaf with a genuinely
non-identity φc-map: the closures array grows by one, and `EvalExit`'s
existential exposes the `PhiExtends φc φc' (st.store.closures.size + 1)`. -/
theorem evalFnSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (store' : Store) (a : Addr)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hAlloc : st.store.allocClosure ⟨env, name, params, body⟩ = (store', a))
    (_hEval : EvalE st d env (.fn name params body) ⟨store', st.out⟩ (.closure a))
    (hArm : FnArmSpec g N A SL φf φc st d env name params body store' a
      sp r sret aEnv aExpr m0) :
    Triple
      (EvalEntry g N A SL φf φc st d env (.fn name params body) sp r sret aEnv aExpr m0)
      (EvalExit g N A SL φf φc ⟨store', st.out⟩ (.closure a) sp r sret m0) :=
  hArm hAlloc

end Vsa.Sim
