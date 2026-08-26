import Vsa.Sim.EvalArgs

/-!
# Layer 4 — M4: the `EvalE.call` case (the call-expression composition)

`EvalE.call` is the last-but-one `EvalE` constructor: `.call f args` evaluates
the callee expression `f → fval`, then the argument list `args → vs`
(threading store/output left-to-right), then applies `Call fval vs → v`. On the
machine this is the WHOLE inline `EX_CALL` arm of `eval_expr` (jump-table slot 6
→ `callArmPC = 0x800031b0`; there is no separate `call_value` symbol — see
`CallEntry` for the full decode):

1. callee eval — `jal eval_expr` on `f` (sret `sp+96`), one `EvalIH`;
2. the argument-evaluation loop — `evalArgsLoop`/`EvalArgs`, materialising the
   stack Value-array (`ArgVecRepr`);
3. the `fv->kind` dispatch — `Call` (native `jalr a6` or closure body), landing
   at the epilogue join `callJoinPC = 0x800033ec`;
4. the shared `eval_expr` epilogue (`blockD_v`) → `EvalExit … v`.

This file states the `EvalE.call` minor premise as a machine `Triple`
(`EvalEntry (.call f args) → EvalExit … v`), CONDITIONAL on a single named
residual `CallArmSpec` — the whole `EX_CALL` arm machine run — into which the
three sub-relation results (the callee `EvalIH`, the `EvalArgs` derivation, and
the `Call` derivation) are threaded. This is exactly the deferral discipline of
`callAssertOk` (`= hNative`) and `evalNegSim` (residuals + IH), applied to the
composite call arm: the sub-relation IHs supplied by the mutual recursor are
consumed by `CallArmSpec`, and `evalCallSim` is the wrapper that packages them
into the `EvalEntry → EvalExit` motive.

`CallArmSpec` is the reusable composite residual. Its eventual discharge chains
(a) the arm's `blockA` dispatch (slot 6 landing at `callArmPC`), (b) the callee
`armTail_rec` on `f` (consuming the callee `EvalIH`), (c) `evalArgsLoop` on
`args` (consuming the per-argument residual `EvalArgsStep`), (d) the `Call`
dispatch (native `callAssertOk`-style or the closure crux), and (e) `blockD_v`.
The three sub-derivations gate the branches (which callee, how many args, native
vs closure). NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
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

/-! ## `CallArmSpec` — the composite `EX_CALL` arm residual

From the `EvalEntry` for `.call f args`, the whole arm runs (callee eval ≫ arg
loop ≫ `Call` dispatch ≫ epilogue) to the `EvalExit` for the call's result `v`.
The residual is stated ABOVE the three sub-derivations — the callee's induction
hypothesis `hIH_f` (an `EvalIH` on `f`), the `EvalArgs` derivation for the
arguments, and the `Call` derivation for the application — so that discharging it
may freely consume all three (via `armTail_rec` / `evalArgsLoop` / the `Call`
minor premise). It abstracts the entire arm machine run behind one Triple, the
composite analog of `NativeAssertOkSpec`. -/
def CallArmSpec
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr)
    (f : Expr) (args : List Expr) (fval : Value) (vs : List Value) (v : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) : Prop :=
  EvalIH st d env f st' fval →
  EvalArgs st' d env args st'' vs →
  Call st'' d fval vs st''' v →
  Triple
    (EvalEntry g N A SL φf φc st d env (.call f args) sp r sret aEnv aExpr m0)
    (EvalExit g N A SL φf φc st''' v sp r sret m0)

/-- **`evalCallSim`**: the `EvalE.call` minor premise (the call-expression
composition) at the machine level, in the recursor motive shape. From the
`EvalEntry` for `.call f args`, the `EX_CALL` arm — callee eval (`EvalIH` on `f`)
≫ the argument loop (`EvalArgs`) ≫ the `Call` dispatch ≫ the shared epilogue —
runs to the `EvalExit` for the call's result `v` with the fully-threaded
post-state `st'''`.

The three sub-relation results supplied by the mutual recursor are threaded:
`hIH_f` (the callee's `EvalIH`), `hArgs` (the `EvalArgs args → vs` derivation,
whose machine simulation is `evalArgsLoop`), and `hCall` (the `Call fval vs → v`
derivation, whose machine simulation is the native/closure dispatch). CONDITIONAL
on `CallArmSpec` — the named composite `EX_CALL` arm residual — into which all
three are fed, exactly the deferral pattern of `callAssertOk`/`evalNegSim`. The
`EvalE.call` spec derivation is threaded (its three premises structure the
arm). -/
theorem evalCallSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr)
    (f : Expr) (args : List Expr) (fval : Value) (vs : List Value) (v : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hIH_f : EvalIH st d env f st' fval)
    (hArgs : EvalArgs st' d env args st'' vs)
    (hCall : Call st'' d fval vs st''' v)
    (_hEval : EvalE st d env (.call f args) st''' v)
    (hArm : CallArmSpec g N A SL φf φc st st' st'' st''' d env f args fval vs v
      sp r sret aEnv aExpr m0) :
    Triple
      (EvalEntry g N A SL φf φc st d env (.call f args) sp r sret aEnv aExpr m0)
      (EvalExit g N A SL φf φc st''' v sp r sret m0) :=
  hArm hIH_f hArgs hCall

end Vsa.Sim
