import Vsa.Sim.AllocClosure
import Vsa.Sim.FnArmGeomReduce

/-!
# `fnArmSeamRun_of_allocClosure` — discharge the `EX_FN` middle seam from the contract

`FnArmGeomReduce.lean` brackets the whole `EX_FN` arm run into front (`armEntry_widen`),
back (`preEpilogueV_of_writeLog`), and the NAMED middle residual `FnArmSeamRun` (the
malloc-call ≫ closure-build run whose genuine opens are the `allocClosure` callee
contract + the write-log marshalling).

This file closes that middle seam from the `AllocClosureContract` (the `env_new_spec`
analog, `AllocClosure.lean`): the contract's `spec` produces the fresh closure block
`p`, its `ClosureRepr`, the OLD store at `φc'`, and the register/geometry/sret bundle;
`storeRepr_pushClosure` (proved in `AllocClosure.lean`, axiom-clean) upgrades the OLD
store to the GROWN store `(st.store.allocClosure cd).1` that `FnArmSeamRun`'s post
demands.  Pure structural gluing — no machine reasoning; the machine work is inside
`AllocClosureContract.spec` (a named hypothesis, never constructed here).

Composing with `fnArmGeom_hArm_of_seam` (FnArmGeomReduce) then yields `FnArmGeom.hArm`
— the whole arm run — modulo ONLY the `AllocClosureContract` (its arm-head `a3 := φf
env` decode + `malloc` splice + build write-log), which is the single honestly-off-path
machine residual for `fnArmGeom_closed`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- **`fnArmSeamRun_of_allocClosure`** — the `EX_FN` middle seam from the contract.

`cd := ⟨env, name, params, body⟩` is the allocated closure record; `a := st.store.
closures.size` is its fresh spec index (`allocClosure` pushes at the end), so the fixed
`φc' a = p` is exactly the sret-payload the seam post reads.  The contract's `spec`
runs the arm's dispatch config (the `ArmEntryK`-∃ predicate, matched to `FnArmSeamRun`'s
pre) to a post exposing the fresh block + old-store-at-`φc'` + the sret/register/
geometry bundle; `storeRepr_pushClosure` grows the store to `(st.store.allocClosure
cd).1`.  `store' = (st.store.allocClosure cd).1` matches `EvalFn.lean`'s allocation
result.  Pure `Triple`-consequence — no machine reasoning. -/
theorem fnArmSeamRun_of_allocClosure
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φc' : Addr → Nat)
    (st : Vsa.While.St) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (p : Nat) (armPC : BitVec 64) (calleeLoaded : Mem → Prop)
    (sp r sret aExpr aEnv : BitVec 64) (m0 mpre : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (hC : AllocClosureContract g N A SL φf φc φc' st ⟨env, name, params, body⟩
      st.store.closures.size p
      (fun c => ∃ o ment vv8 vv9 vv18,
        ArmEntryK g N A SL φf φc' st armPC calleeLoaded (.fn name params body)
          sp r sret aExpr aEnv vv8 vv9 vv18 o m0 ment c)
      sp r sret m0 mpre v8 v9 v18 out0) :
    FnArmSeamRun g N A SL φf φc' st st.store.closures.size armPC calleeLoaded
      name params body (st.store.allocClosure ⟨env, name, params, body⟩).1
      sp r sret aExpr aEnv m0 v8 v9 v18 out0 mpre := by
  -- `FnArmSeamRun … = Triple Pre Post`; run the contract's `spec`, then grow the store.
  intro c hpre
  obtain ⟨c', hsteps, hpost⟩ := hC.spec rfl c hpre
  obtain ⟨hmemc, hp, hpnz, harena, halign, hpfresh, hrepr,
    hext, hOld, hkind, hpay, hpaynz, hrest⟩ := hpost
  refine ⟨c', hsteps, ?_⟩
  -- grow the old store (at `φc'`) to `(allocClosure).1` via `storeRepr_pushClosure`
  have hgrow : StoreRepr mpre N A φf φc'
      (st.store.allocClosure ⟨env, name, params, body⟩).1 :=
    storeRepr_pushClosure hOld hp hrepr harena halign hpfresh
  -- assemble the seam post: mem, kind read, payload read (φc' a nonzero), grown store.
  obtain ⟨hG, htick, hpc, hx9, hx2, hmi, hout, houtStr, hcode, hframe,
    hRa, hS0, hS1, hS2, hgx8, hgx9, hgx18, hgx2, hmemframe,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩ := hrest
  refine ⟨hmemc, hkind, hpay, hpaynz, ?_⟩
  exact ⟨hG, htick, hpc, hx9, hx2, hmi, hout, houtStr, hcode, hgrow, hframe,
    hRa, hS0, hS1, hS2, hgx8, hgx9, hgx18, hgx2, hmemframe,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩

#print axioms fnArmSeamRun_of_allocClosure

end Vsa.Sim
