import Vsa.Sim.rows.CallResidProviders
import Vsa.Sim.rows.ErrorRouting

/-!
# Indexed call-error seam

`ErrorSimFull` now exposes entry-indexed error motives and a reusable
`ChildSeam`.  This module closes `EvalErr.callTooMany` as the first compiled
client, without an arbitrary-configuration premise.
-/

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (Config Steps Halts)
open Vsa.Logic (Triple)
open Vsa.MemRepr
open Vsa.RuntimeRepr (NativeAddrs Arena)
open Vsa.Alloc (StackLayout)
open Vsa.While

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-- The normal call-arm prefix through the recursive callee call.  This is the
`CallArmStages.callee` field with no irrelevant later call-stage indices. -/
def CallCalleeStage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) : Prop :=
  Triple
    (EvalEntry g N A SL φf φc st d env (.call f args)
      sp r sret aEnv aExpr m0)
    (fun c => Rows.CallChildJalPre aExpr f args f c st d env)

/-- The MAX_ARGS guard entry.  Its concrete count and signed range are derived
from the transported outer-call representation in `ArgsChildReturn`; the
semantic strict bound selects the error edge. -/
def CallTooManyReady
    (st st' : SpecSt) (d : Nat) (env : Addr) (callNode : BitVec 64)
    (f : Expr) (args : List Expr) (fv : Value) : Config → Prop :=
  fun c =>
    Rows.ArgsChildReturn st st' d env callNode f args f fv c ∧
    read32 c.σ.mem (callNode.toNat + 24) = some args.length ∧
    args.length < 2 ^ 31 ∧
    maxArgs < args.length

/-- The post-callee MAX_ARGS branch.  Its exit is the exact `0x80003fdc` jal
checkpoint consumed by the proved error tail. -/
def CallTooManyStage (S : ErrShared)
    (st st' : SpecSt) (d : Nat) (env : Addr) (callNode : BitVec 64)
    (f : Expr) (args : List Expr) (fv : Value) : Prop :=
  Triple
    (CallTooManyReady st st' d env callNode f args fv)
    (ReachJal S.g S.inp S.m0
      0x80003fdc#64 0xef#8 0xe0#8 0xdf#8 0xdc#8)

/-- The callTooMany instance of the reusable recursive seam.  Its child exit
is the strengthened returned-callee carrier, not an unrelated configuration. -/
def callTooManyChildSeam
    (S : ErrShared)
    (st st' : SpecSt) (d : Nat) (env : Addr) (callNode : BitVec 64)
    (f : Expr) (args : List Expr) (fv : Value)
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret aEnv : BitVec 64)
    (hTooMany : maxArgs < args.length)
    (hCallee : CallCalleeStage S.g N A SL φf φc st d env f args
      sp r sret aEnv callNode S.m0)
    (hGuard : CallTooManyStage S st st' d env callNode f args fv) :
    ChildSeam
      (EvalEntry S.g N A SL φf φc st d env (.call f args)
        sp r sret aEnv callNode S.m0)
      (fun c => Rows.CallChildJalPre callNode f args f c st d env)
      (Rows.ArgsChildReturn st st' d env callNode f args f fv)
      (CallTooManyReady st st' d env callNode f args fv)
      (ReachJal S.g S.inp S.m0
        0x80003fdc#64 0xef#8 0xe0#8 0xdf#8 0xdc#8) where
  dispatch := hCallee
  resume_ready := fun _ hRet => by
    have hCount := Rows.ArgsChildReturn.call_count hRet
    exact ⟨hRet, hCount.1, hCount.2, hTooMany⟩
  resume := hGuard

/-- Indexed `EvalErr.callTooMany`: call-arm dispatch reaches the callee call;
the already-proved normal `EvalIH` evaluates the callee; the strict MAX_ARGS
stage reaches the exact runtime-error jal; the shared error row closes the
runtime_error/longjmp/exit tail. -/
theorem evalErr_callTooMany_indexed
    (S : ErrShared)
    (st st' : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
    (fv : Value)
    (hEf : EvalE st d env f st' fv)
    (hTooMany : maxArgs < args.length)
    (hEfIH : EvalIH st d env f st' fv)
    (hCallee : ∀ (N : NativeAddrs) (A : Arena) (SL : StackLayout)
      (φf φc : Addr → Nat) (sp r sret aEnv aExpr : BitVec 64),
      CallCalleeStage S.g N A SL φf φc st d env f args
        sp r sret aEnv aExpr S.m0)
    (hGuard : ∀ callNode,
      CallTooManyStage S st st' d env callNode f args fv) :
    EvalErrI S.g S.m0 st d env (.call f args) := by
  intro N A SL φf φc sp r sret aEnv aExpr c hEntry
  obtain ⟨cJal, hs, hJal⟩ :=
    (callTooManyChildSeam S st st' d env aExpr f args fv N A SL φf φc
      sp r sret aEnv hTooMany
      (hCallee N A SL φf φc sp r sret aEnv aExpr) (hGuard aExpr)).run
      (Rows.argsChildReturn_of_jalBundle st st' d env aExpr f args f fv hEfIH)
      c hEntry
  exact errHalts_of_steps hs
    (errRow_reach S 0x80003fdc#64 0xef#8 0xe0#8 0xdf#8 0xdc#8
      (errSite_80003fdc S.g S.inp S.m0) cJal hJal)

/-- The exact `ErrorCasesI.hCallTooMany` field.  Normal callee evaluation comes
from the ordinary semantic simulation family; the two machine stages are the
validated call-arm cut and MAX_ARGS guard cut. -/
theorem callTooManyCase_indexed
    (S : ErrShared)
    (hEval : ∀ st d env e st' v, EvalE st d env e st' v →
      EvalIH st d env e st' v)
    (hCallee : ∀ st d env f args
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (sp r sret aEnv aExpr : BitVec 64),
      CallCalleeStage S.g N A SL φf φc st d env f args
        sp r sret aEnv aExpr S.m0)
    (hGuard : ∀ st st' d env callNode f args fv,
      CallTooManyStage S st st' d env callNode f args fv) :
    ∀ st d env f args st' fv, EvalE st d env f st' fv →
      maxArgs < args.length →
      EvalErrI S.g S.m0 st d env (.call f args) := by
  intro st d env f args st' fv hEf hTooMany
  exact evalErr_callTooMany_indexed S st st' d env f args fv hEf hTooMany
    (hEval st d env f st' fv hEf) (hCallee st d env f args)
    (fun callNode => hGuard st st' d env callNode f args fv)

#print axioms evalErr_callTooMany_indexed
#print axioms callTooManyCase_indexed

end Vsa.Sim
