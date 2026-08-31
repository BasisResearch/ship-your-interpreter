import Vsa.Sim.rows.EvalVarBridge
import Vsa.Sim.EnvGetMarshal

/-!
# `EvalVarBridgeCallee` — discharging `VarCallLinkage.callee` from the two new
`env_get` lemmas (`foundSt_of_storeRepr` + `env_get_found_framed`).

`rows/EvalVarBridge.lean` reduced the whole var-arm `env_get` call bridge to ONE
open field of `VarCallLinkage`: the `callee` `Triple`

    EnvGetEntryV … → (fun c => ∃ mpc, VarPostCall … v … mpc c),

i.e. run the `env_get` FOUND body from the call-entry config, then repackage its
return into the var-arm's `VarPostCall`.  Its doc-comment named the two facts that
would make it PROVABLE:

1. **the `env_get` FOUND contract from the whole store** — now
   `EnvGetMarshal.foundSt_of_storeRepr` (`StoreRepr` + the immediate first-match →
   `FoundSt`; `FrameStackDisj` = the honest heap-vs-stack disjointness caller
   premise);
2. **the `env_get` memory-frame post** — now `EnvGetSpec10.env_get_found_framed`
   ("the run wrote only `[out, out+24) ∪ [sp0-64, sp0)`"), the exact frame the
   `VarPostCall` repackaging needs to transport the caller's spills and `StoreRepr`
   across the call.

This file wires the two together into `varCallLinkage_callee`: a `Triple`
`EnvGetEntryV → ∃ mpc, VarPostCall` built by running `env_get_found_framed` over the
`FoundSt` marshalled by `foundSt_of_storeRepr`, then applying the `VarPostCall`
repackaging.

## The genuinely-open residuals (all above `env_get`'s contract)

Two things remain that neither new lemma provides, because they are CALLER-frame
data (not part of `env_get`'s own contract), threaded as named premises:

* **`EnvGetCallerGeom` + `FrameStackDisj` + the immediate-hit witness** — the
  callee-entry register/geometry residue + heap-vs-stack disjointness + the
  first-match index.  These come from the M4 caller's layout witness + the spec
  lookup `st.store.get? env x = some v` (which is exactly `EnvGetEntryV`'s
  provenance).  `env` here is the machine env pointer `penv = x13`, still the
  seam's one honestly caller-supplied datum (`VarCallLinkage.a3`).

* **`VarPostRepack`** — the repackaging of `env_get`'s framed post
  (`ValueRepr m' out v` + the `[out,out+24)∪[sp0-64,sp0)` memframe + restored
  callee-saveds/`sp`/`PC=r`) into the var-arm's `VarPostCall` (the result-buffer→
  `sret` relocation words `d0/d1/d2`, the caller's own spill slots
  `sp-8..sp-32`, the g-frame, `StoreRepr` survival, and the remaining geometry).
  This consumes exactly the memframe `env_get_found_framed` now provides — the
  frame is the load-bearing input, and it was the missing fact before deliverable 2.

`varCallLinkage_callee` proves `VarCallLinkage.callee` from those premises.  The
statement `VarCallLinkage`/`varBridge` (EvalVarBridge.lean) is UNCHANGED.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option maxHeartbeats 800000

set_option linter.unusedVariables false in
/-- The `env_get` framed FOUND post as a standalone `Config → Prop`, at the call's
env_get parameters (`sp0 = sp-1088`, `out = (sp-1088)+0xf0`, `r = 0x80003444`).
This is exactly what `env_get_found_framed` delivers; `VarPostRepack` consumes it.
`env`/`r0`/`φf` are carried for signature-uniformity with the marshalling lemmas. -/
def EnvGetFramedPost
    (env : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (v : Value) (sp : BitVec 64) (ment : Mem) (c : Config) : Prop :=
  ∃ (m' : Mem),
    GoodState c.σ ∧ c.tick < 2 ∧
    c.σ.regs.get? Register.PC = some (0x80003444#64) ∧
    c.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) ∧
    c.σ.regs.get? Register.x1 = some (0x80003444#64) ∧
    c.σ.regs.get? Register.x2 = some (((sp - 1088#64) - 64#64) + 64#64) ∧
    c.σ.regs.get? Register.x8 = some r8 ∧
    c.σ.regs.get? Register.x9 = some r9 ∧
    c.σ.regs.get? Register.x18 = some r18 ∧
    c.σ.regs.get? Register.x19 = some r19 ∧
    c.σ.regs.get? Register.x20 = some r20 ∧
    c.σ.regs.get? Register.x21 = some r21 ∧
    c.σ.mem = m' ∧ Env_getLoaded m' ∧
    ValueRepr m' N φc (((sp - 1088#64) + 0xf0#64).toNat) v ∧
    (∀ a : Nat, EnvGetFootprint ((sp - 1088#64) + 0xf0#64) (sp - 1088#64) a → m'[a]? = ment[a]?)

/-- The `env_get` framed run as a `Triple` from `EnvGetEntryV` (the call-entry
predicate the proved prefix produces) to `EnvGetFramedPost`.

Consumes: the whole-store representation `StoreRepr` + the immediate first-match at
the looked-up frame (the spec lookup's provenance) + `EnvGetCallerGeom` (the
callee-entry register/geometry residue) + `FrameStackDisj` (heap-vs-stack disj).
The first three build `FoundSt` via `foundSt_of_storeRepr`; the framed run is
`env_get_found_framed`.

`EnvGetEntryV`'s registers (`x10=penv`, `x11=nm`, `x12=out`, `x1=link`,
`x2=sp-1088`) must match the `EnvGetCallerGeom` witness — that is the caller-linkage
consistency the M4 recursor supplies (with `penv = φf fa`, the looked-up frame's
machine address). -/
theorem envGetFramed_triple
    (st : SpecSt) (x : String) (v : Value)
    (sp sret aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64) (ment : Mem)
    (penv nm : BitVec 64)
    (N : NativeAddrs) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (fa : Vsa.While.Addr) (iw : Nat) (len pn : Nat)
    (r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (hpenv : penv.toNat = φf fa)
    (hSR : StoreRepr ment N A φf φc st.store)
    (hfa : fa < st.store.frames.size)
    (hiw : iw < st.store.frames[fa].vars.length)
    (hbelow : ∀ j, (hj : j < iw) →
      ¬ (st.store.frames[fa].vars[j]'(Nat.lt_trans hj hiw)).1 = x)
    (hhit : (st.store.frames[fa].vars[iw]).1 = x)
    (hlen : len = st.store.frames[fa].vars.length)
    (hval : (st.store.frames[fa].vars[iw]).2 = v)
    -- the callee-entry register/geometry residue + heap-vs-stack disjointness
    (hGeom : ∀ c, EnvGetEntryV st sp sret aExpr aEnv v8 v9 v18 ment penv nm c →
      EnvGetCallerGeom penv nm ((sp - 1088#64) + 0xf0#64) (0x80003444#64) (sp - 1088#64)
        r0 r8 r9 r18 r19 r20 r21 len pn x st.store.frames[fa] ment c)
    (hD : FrameStackDisj penv nm (sp - 1088#64) pn x st.store.frames[fa] ment) :
    Triple
      (EnvGetEntryV st sp sret aExpr aEnv v8 v9 v18 ment penv nm)
      (EnvGetFramedPost penv r0 r8 r9 r18 r19 r20 r21 N φf φc v sp ment) := by
  intro c hEntry
  have hCG := hGeom c hEntry
  have hFS : FoundSt penv nm ((sp - 1088#64) + 0xf0#64) (0x80003444#64) (sp - 1088#64)
      r0 r8 r9 r18 r19 r20 r21 len pn x iw st.store.frames[fa] N φf φc ment c :=
    foundSt_of_storeRepr penv nm ((sp - 1088#64) + 0xf0#64) (0x80003444#64) (sp - 1088#64)
      r0 r8 r9 r18 r19 r20 r21 len pn x N A φf φc st.store fa iw ment c hSR hfa hpenv
      hiw hbelow hhit hlen hCG
  have hrun := env_get_found_framed penv nm ((sp - 1088#64) + 0xf0#64) (0x80003444#64)
    (sp - 1088#64) r0 r8 r9 r18 r19 r20 r21 len pn x iw st.store.frames[fa] N φf φc ment c hFS hD
  obtain ⟨c', m', iHit, hi, hs, hG, htick, hpc, ha0, hra, hsp', hx8, hx9, hx18, hx19,
    hx20, hx21, hmem', hcode', hvr, hitName, hitFirst, hframe⟩ := hrun
  -- reconcile the machine's first-match index `iHit` with the spec's least-match `iw`:
  -- both are name-hits for `x`, and each is minimal among hits (via `hbelow`/`hitFirst`),
  -- so `iHit = iw` by antisymmetry (`iHit < iw` contradicts `hbelow`; `iw < iHit`
  -- contradicts `hitFirst`).  Hence `f.vars[iHit].2 = f.vars[iw].2 = v`.
  have hiHitEq : iHit = iw := by
    rcases Nat.lt_trichotomy iHit iw with hlt | heq | hgt
    · exact absurd hitName (hbelow iHit hlt)
    · exact heq
    · exact absurd hhit (hitFirst iw hiw hgt)
  subst hiHitEq
  refine ⟨c', ?_, m', hG, htick, hpc, ha0, hra, hsp', hx8, hx9, hx18, hx19, hx20, hx21,
    hmem', hcode', ?_, hframe⟩
  · exact hs
  · rw [hval] at hvr; exact hvr

/-! ## Discharging `VarCallLinkage.callee`

`VarCallLinkage.callee` is `Triple (EnvGetEntryV …) (fun c => ∃ mpc, VarPostCall …)`.
We build it as `envGetFramed_triple ≫ VarPostRepack`:

* `envGetFramed_triple` (above) runs the `env_get` FOUND body from the call entry,
  producing `EnvGetFramedPost` — the framed post the two new lemmas deliver;
* `VarPostRepack` repackages `EnvGetFramedPost` into `∃ mpc, VarPostCall` — the
  result-buffer→`sret` relocation (`d0/d1/d2`), the caller's own spill slots, the
  g-frame, `StoreRepr` survival, and the remaining geometry.  This consumes exactly
  the `[out,out+24)∪[sp0-64,sp0)` memory frame `env_get_found_framed` now carries;
  it is CALLER-frame data (not part of `env_get`'s contract), so it is a named
  premise the M4 caller's layout witness supplies.

The result IS a `VarCallLinkage.callee` (same type), assembled entirely from the two
new lemmas plus the two honest caller premises — the `x13=penv` datum being the only
other genuinely caller-supplied field of `VarCallLinkage` (its `.a3`). -/
theorem varCallLinkage_callee
    (st : SpecSt) (x : String) (v : Value)
    (sp sret aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64) (ment : Mem)
    (penv nm : BitVec 64)
    (N : NativeAddrs) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (fa : Vsa.While.Addr) (iw : Nat) (len pn : Nat)
    (r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (hpenv : penv.toNat = φf fa)
    (hSR : StoreRepr ment N A φf φc st.store)
    (hfa : fa < st.store.frames.size)
    (hiw : iw < st.store.frames[fa].vars.length)
    (hbelow : ∀ j, (hj : j < iw) →
      ¬ (st.store.frames[fa].vars[j]'(Nat.lt_trans hj hiw)).1 = x)
    (hhit : (st.store.frames[fa].vars[iw]).1 = x)
    (hlen : len = st.store.frames[fa].vars.length)
    (hval : (st.store.frames[fa].vars[iw]).2 = v)
    (hGeom : ∀ c, EnvGetEntryV st sp sret aExpr aEnv v8 v9 v18 ment penv nm c →
      EnvGetCallerGeom penv nm ((sp - 1088#64) + 0xf0#64) (0x80003444#64) (sp - 1088#64)
        r0 r8 r9 r18 r19 r20 r21 len pn x st.store.frames[fa] ment c)
    (hD : FrameStackDisj penv nm (sp - 1088#64) pn x st.store.frames[fa] ment)
    -- the caller-frame repackaging of the framed env_get post into `VarPostCall`
    -- (the only remaining CALLER-frame obligation; consumes the memory frame).
    (VarPostRepack : ∀ (g : (R : Register) → Option (RegisterType R))
        (SL : StackLayout) (r : BitVec 64) (out0 : Array String) (m0 : Mem),
      Triple
        (EnvGetFramedPost penv r0 r8 r9 r18 r19 r20 r21 N φf φc v sp ment)
        (fun c => ∃ mpc, VarPostCall g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpc c))
    (g : (R : Register) → Option (RegisterType R)) (SL : StackLayout)
    (r : BitVec 64) (out0 : Array String) (m0 : Mem) :
    Triple
      (EnvGetEntryV st sp sret aExpr aEnv v8 v9 v18 ment penv nm)
      (fun c => ∃ mpc, VarPostCall g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpc c) :=
  Triple.seq
    (envGetFramed_triple st x v sp sret aExpr aEnv v8 v9 v18 ment penv nm N A φf φc
      fa iw len pn r0 r8 r9 r18 r19 r20 r21 hpenv hSR hfa hiw hbelow hhit hlen hval hGeom hD)
    (VarPostRepack g SL r out0 m0)

#print axioms envGetFramed_triple
#print axioms varCallLinkage_callee

end Vsa.Sim
