import Vsa.Sim.rows.CallRows
import Vsa.Sim.rows.FnArmSeamReduce

/-!
# `FnResidSupply` — supply the `hFn` residual `FnResid` from the `EX_FN` pipeline

`eval_fn_row` (`rows/CallRows`) fills the recursor's `hFn` slot by routing to
`evalFnSimD` over the named residual `FnResid` (the `FnArmSpec` arm run + the
`EvalRecWiden` φc-widener).  This file SUPPLIES that residual by assembling the
whole `EX_FN` arm pipeline landed across wave 33-38:

```
  fnArmSeamRun_of_allocClosure  (FnArmSeamReduce)   → FnArmSeamRun
    ⊕ 9 dispatch facts + hEntryRebase
      → fnArmGeom_hArm_offdiag (below)              → FnArmGeom.hArm  (φc → φc')
        ⊕ hpc/hout                                  → FnArmGeom
          ⊕ hfr/hcl (store-size monotonicity, trivial)
            → fnArmSpec_of_geom (ArmSpecBridge)      → FnArmSpec
              ⊕ EvalRecWiden                          → FnResid
```

## The ONE genuine open beyond the off-path bundles: the φc-entry rebase

`fnArmGeom_hArm_of_seam` (`FnArmGeomReduce`) is stated over a SINGLE closures map,
so it produces the DIAGONAL `Triple (EvalEntry … φc' …) (PreEpilogueV … φc' …)`.
`FnArmGeom.hArm` needs the OFF-DIAGONAL `Triple (EvalEntry … φc …) (PreEpilogueV …
φc' …)` — entry at the PRE-alloc map `φc`, exit at the widened `φc'` (the closures
array grows by one across the arm).  `EvalEntry.store = StoreRepr … φc st.store`
genuinely depends on the closures map, so the two entries are not defeq; the gap is
the closures-side analog of the φf-rebase in `CallClosureEnvNewMarshal`
(`StoreRepr … φf` through `PhiExtends φf φf'`).  It is named here as the premise
`hEntryRebase` — a `StoreRepr … φc st.store → StoreRepr … φc' st.store` entry rebase
over `PhiExtends φc φc' st.store.closures.size` (the OLD store references no fresh
closure index).  See observations `fnArmGeom-hArm-diagonal-phic-only`.

## The remaining named premises (each irreducible / itemized in the report)

* `hSeam : FnArmSeamRun …` — the `EX_FN` middle seam (malloc-call ≫ closure-build);
  itself closed by `fnArmSeamRun_of_allocClosure` modulo the `AllocClosureContract`
  (the honestly-off-path arm-head decode + build write-log).  Passed opaque here.
* the 9 jump-table dispatch facts (`hkle … htableStk`) — the standard leaf-arm
  dispatch shape (fn kind = 10, arm PC 0x800033c4), an int/null/bool/str clone.
* `hEntryRebase` — the φc-entry rebase above.
* `hpc`/`hout` — the closure-alloc `PhiExtends` + output invariant.
* `hfr`/`hcl` — store-size monotonicity (frames fixed, closures +1: trivial from
  `allocClosure`, discharged inline by `store_size_of_allocClosure`).
* `hW` — `EvalRecWiden` at the grown store.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- **`fnArmGeom_hArm_offdiag`** — the off-diagonal `FnArmGeom.hArm` Triple
(`EvalEntry … φc …` → `PreEpilogueV … φc' …`) from the diagonal
`fnArmGeom_hArm_of_seam` (`EvalEntry … φc' …` → `PreEpilogueV … φc' …`) plus the
named `φc`-entry rebase `hEntryRebase`.  The rebase transports the entry
`StoreRepr … φc st.store` to `StoreRepr … φc' st.store` (the only `EvalEntry` field
that mentions the closures map), so the two entry predicates coincide and the
diagonal Triple applies.  Everything else in `EvalEntry` is closures-map-free. -/
theorem fnArmGeom_hArm_offdiag
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φc' : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (a : Addr)
    (k : Nat) (armPC : BitVec 64) (calleeLoaded : Mem → Prop)
    (name : Option String) (params : List String) (body : List Stmt)
    (store' : Store)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String) (mpre : Mem)
    (hkle : k ≤ 10) (hklt : k < 128)
    (hkind : read32 m0 aExpr.toNat = some k)
    (hslot : KindSlotPinned k armPC m0) (hcallee : calleeLoaded m0)
    (hcalleeSurv : ∀ (mem : Mem) (a8 : Nat) (dd : BitVec (8 * 8)),
      SL.lo ≤ a8 → a8 + 8 ≤ sp.toNat → calleeLoaded mem → calleeLoaded (writeMap8 mem a8 dd))
    (hexprSurv : ∀ m' : Mem,
      (∀ aa : Nat, ¬ (SL.lo ≤ aa ∧ aa < sp.toNat) → m0[aa]? = m'[aa]?) →
        ExprRepr m' aExpr.toNat (.fn name params body))
    (harmAl : armPC.toNat % 4 = 0)
    (htableStk : jumpTableBase + 4 * k + 4 ≤ SL.lo ∨ sp.toNat ≤ jumpTableBase + 4 * k)
    (hSeam : FnArmSeamRun g N A SL φf φc' st a armPC calleeLoaded name params body store'
      sp r sret aExpr aEnv m0 v8 v9 v18 out0 mpre)
    -- the φc-entry rebase (the ONE genuine open; observations
    -- `fnArmGeom-hArm-diagonal-phic-only`):
    (hEntryRebase : ∀ mm : Mem, StoreRepr mm N A φf φc st.store → StoreRepr mm N A φf φc' st.store) :
    Triple
      (EvalEntry g N A SL φf φc st d env (.fn name params body) sp r sret aEnv aExpr m0)
      (fun c => PreEpilogueV g N A SL φf φc' ⟨store', st.out⟩ (.closure a)
        sp r sret v8 v9 v18 out0 m0 mpre c) := by
  -- the diagonal Triple (entry AND exit at `φc'`)
  have hDiag := fnArmGeom_hArm_of_seam g N A SL φf φc' st d env a k armPC calleeLoaded
    name params body store' sp r sret aEnv aExpr m0 v8 v9 v18 out0 mpre
    hkle hklt hkind hslot hcallee hcalleeSurv hexprSurv harmAl htableStk hSeam
  -- rebase the entry: `EvalEntry … φc …` ⇒ `EvalEntry … φc' …`.  Only the `store`
  -- and `store_survives` fields mention the closures map; every other field is
  -- closures-map-free, so a record-update over `hc` overriding exactly those two
  -- keeps the shape (no positional navigation).
  intro c hc
  refine hDiag c ?_
  have hstore' : StoreRepr c.σ.mem N A φf φc' st.store := hEntryRebase _ hc.store
  have hsurv' : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        c.σ.mem[k]? = m'[k]?) → StoreRepr m' N A φf φc' st.store :=
    fun m' hm' => hEntryRebase m' (hc.store_survives m' hm')
  exact { hc with store := hstore', store_survives := hsurv' }

/-- **`store_size_of_allocClosure`** — `allocClosure` fixes the frames array and
grows the closures array by one, so the entry sizes are ≤ the result sizes.  This
discharges `fnArmSpec_of_geom`'s `hfr`/`hcl` trivially. -/
theorem store_size_of_allocClosure
    (st : Vsa.While.St) (cd : ClosureData) (store' : Store) (a : Addr)
    (hAlloc : st.store.allocClosure cd = (store', a)) :
    st.store.frames.size ≤ store'.frames.size ∧
    st.store.closures.size ≤ store'.closures.size := by
  -- `allocClosure` = push the record onto `closures`, frames untouched.
  have h1 : store' = (st.store.allocClosure cd).1 := by rw [hAlloc]
  subst h1
  refine ⟨?_, ?_⟩
  · exact Nat.le_of_eq (by rfl)
  · simp only [Store.allocClosure]
    rw [Array.size_push]
    exact Nat.le_succ _

/-- **`fnResid_of_pipeline`** — SUPPLY `FnResid` (the `hFn` slot residual) from the
`EX_FN` pipeline.  Assembles `FnArmSpec` via `fnArmGeom_hArm_offdiag` →
`FnArmGeom` → `fnArmSpec_of_geom`, then pairs it with the `EvalRecWiden` φc-widener.
The `allocClosure` result `(store', a)` is fixed by `hAlloc` (so `hfr`/`hcl` are
`store_size_of_allocClosure`); the remaining inputs are the named residuals in the
file doc.  This is the closure-side analog of the leaf residual suppliers. -/
theorem fnResid_of_pipeline
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φc' : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (store' : Store) (a : Addr)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String) (mpre : Mem)
    (k : Nat) (armPC : BitVec 64) (calleeLoaded : Mem → Prop)
    (hAlloc : st.store.allocClosure ⟨env, name, params, body⟩ = (store', a))
    (hpc : PhiExtends φc φc' st.store.closures.size)
    (hout : String.join out0.toList = st.out)
    (hkle : k ≤ 10) (hklt : k < 128)
    (hkind : read32 m0 aExpr.toNat = some k)
    (hslot : KindSlotPinned k armPC m0) (hcallee : calleeLoaded m0)
    (hcalleeSurv : ∀ (mem : Mem) (a8 : Nat) (dd : BitVec (8 * 8)),
      SL.lo ≤ a8 → a8 + 8 ≤ sp.toNat → calleeLoaded mem → calleeLoaded (writeMap8 mem a8 dd))
    (hexprSurv : ∀ m' : Mem,
      (∀ aa : Nat, ¬ (SL.lo ≤ aa ∧ aa < sp.toNat) → m0[aa]? = m'[aa]?) →
        ExprRepr m' aExpr.toNat (.fn name params body))
    (harmAl : armPC.toNat % 4 = 0)
    (htableStk : jumpTableBase + 4 * k + 4 ≤ SL.lo ∨ sp.toNat ≤ jumpTableBase + 4 * k)
    (hSeam : FnArmSeamRun g N A SL φf φc' st a armPC calleeLoaded name params body store'
      sp r sret aExpr aEnv m0 v8 v9 v18 out0 mpre)
    (hEntryRebase : ∀ mm : Mem, StoreRepr mm N A φf φc st.store → StoreRepr mm N A φf φc' st.store)
    (hW : EvalRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size
      ⟨store', st.out⟩ (.closure a) sp r sret m0) :
    Vsa.Sim.FnArmSpec g N A SL φf φc st d env name params body store' a
      sp r sret aEnv aExpr m0 ∧
    Vsa.Sim.EvalRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size
      ⟨store', st.out⟩ (.closure a) sp r sret m0 := by
  have hArm := fnArmGeom_hArm_offdiag g N A SL φf φc φc' st d env a k armPC calleeLoaded
    name params body store' sp r sret aEnv aExpr m0 v8 v9 v18 out0 mpre
    hkle hklt hkind hslot hcallee hcalleeSurv hexprSurv harmAl htableStk hSeam hEntryRebase
  have hGeom : FnArmGeom g N A SL φf φc φc' st d env name params body store' a
      sp r sret aEnv aExpr m0 v8 v9 v18 out0 mpre :=
    { hpc := hpc, hout := hout, hArm := hArm }
  obtain ⟨hfr, hcl⟩ := store_size_of_allocClosure st ⟨env, name, params, body⟩ store' a hAlloc
  exact ⟨fnArmSpec_of_geom g N A SL φf φc φc' st d env name params body store' a
    sp r sret aEnv aExpr m0 v8 v9 v18 out0 mpre hfr hcl hGeom, hW⟩

#print axioms fnArmGeom_hArm_offdiag
#print axioms store_size_of_allocClosure
#print axioms fnResid_of_pipeline

end Vsa.Sim
