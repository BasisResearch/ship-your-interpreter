import Vsa.Sim.ArmEntryWiden
import Vsa.Sim.PreEpilogueWriteLog
import Vsa.Sim.ArmSpecBridge

/-!
# `FnArmGeomReduce` — reduce `FnArmGeom.hArm` through the two Task-#48 lemmas

`FnArmGeom.hArm` (`ArmSpecBridge`) is the WHOLE `EX_FN` arm run
`EvalEntry (.fn …) → PreEpilogueV … (.closure a)`.  This file brackets that run
with the two parametric lemmas landed for Task #48:

* `armEntry_widen` closes the FRONT stage `EvalEntry → ArmEntryK` (prologue +
  jump-table dispatch, callee-generic), given the arm's dispatch data;
* `preEpilogueV_of_writeLog` closes the BACK stage: from the two sret-region reads
  the `VAL_CLOSURE` build leaves plus the register/store/geometry bundle, assemble
  `PreEpilogueV … (.closure a)`.

What remains is the strictly-smaller MIDDLE seam — the malloc-call ≫ closure-build
run from `ArmEntryK` to the write-log config that exposes those two sret reads and
the `hrest` bundle — packaged as the NAMED residual `FnArmSeamRun`.  Its genuine
opens (per `EvalFn.lean`) are the `EX_FN` arm decode marshalling and the missing
`allocClosure` callee contract that links the malloc'd payload to `φc a`; those are
NOT fabricated here — they are named in `FnArmSeamRun`'s doc.

`fnArmGeom_hArm_of_seam` shows the two new lemmas discharge the front and back of
every closure arm, so the per-arm hand derivation collapses to `FnArmSeamRun`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- **`FnArmSeamRun`** — the MIDDLE seam of the `EX_FN` arm, from the dispatch
target `ArmEntryK … armPC calleeLoaded (.fn …)` to a config `c` whose memory
`mpre` exposes the closure `VAL_CLOSURE` sret reads (kind `4`, payload `φc' a`,
non-null) AND the register/store/geometry bundle `preEpilogueV_of_writeLog` needs.
This is the malloc-call (`fnArmMallocCallBridge`) ≫ closure-build
(`fnArmClosureBuildRow`) run, marshalled into the shared-epilogue-entry facts.

GENUINELY OPEN (not fabricated): the write-log→facts marshalling of those two
landed seg rows, and the `allocClosure` callee contract that ties the malloc'd
closure payload to `φc' a` with `φc' a ≠ 0` (`EvalFn.lean`: "no `allocClosure`
machine contract exists yet").  Named here as ONE Triple residual so the front/back
(the two new lemmas) are separated from it. -/
def FnArmSeamRun
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc' : Addr → Nat)
    (st : Vsa.While.St) (a : Addr)
    (armPC : BitVec 64) (calleeLoaded : Mem → Prop)
    (name : Option String) (params : List String) (body : List Stmt)
    (store' : Store)
    (sp r sret aExpr aEnv : BitVec 64) (m0 : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String) (mpre : Mem) : Prop :=
  Triple
    (fun c => ∃ o ment vv8 vv9 vv18,
      ArmEntryK g N A SL φf φc' st armPC calleeLoaded (.fn name params body)
        sp r sret aExpr aEnv vv8 vv9 vv18 o m0 ment c)
    (fun c => c.σ.mem = mpre ∧
      read32 mpre sret.toNat = some 4 ∧
      read64 mpre (sret.toNat + 8) = some (φc' a) ∧
      φc' a ≠ 0 ∧
      (GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (0x800033ec#64) ∧
        c.σ.regs.get? Register.x9 = some sret ∧
        c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        c.σ.sailOutput = out0 ∧ String.join out0.toList = st.out ∧
        Eval_exprLoaded mpre ∧
        StoreRepr mpre N A φf φc' store' ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          c.σ.regs.get? R = g R) ∧
        read64 mpre (sp.toNat - 8) = some r.toNat ∧
        read64 mpre (sp.toNat - 16) = some v8.toNat ∧
        read64 mpre (sp.toNat - 24) = some v9.toNat ∧
        read64 mpre (sp.toNat - 32) = some v18.toNat ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧ g Register.x18 = some v18 ∧
        g Register.x2 = some sp ∧
        (∀ aa : Nat, ¬ (SL.lo ≤ aa ∧ aa < sp.toNat) → ¬ (A.lo ≤ aa ∧ aa < A.hi) →
          (sret.toNat ≤ aa ∧ aa < sret.toNat + 24) ∨ mpre[aa]? = m0[aa]?) ∧
        1088 ≤ sp.toNat ∧
        sp.toNat ≤ 0x100000000 ∧ 0x80000000 ≤ sp.toNat ∧
        tohostAddr + 16 + 1088 ≤ sp.toNat ∧ sp.toNat % 8 = 0 ∧
        r.toNat % 4 = 0))

/-- **`fnArmGeom_hArm_of_seam`** — build `FnArmGeom.hArm` (the whole arm run
`EvalEntry → PreEpilogueV … (.closure a)`) from the dispatch data (front, via
`armEntry_widen`) and the middle seam `FnArmSeamRun` (back closed by
`preEpilogueV_of_writeLog`).  Pure `Triple.seq` of the two new lemmas around the
named seam — no machine reasoning.  This is exactly the `FnArmGeom.hArm` field's
type at the entry closures map `φc'` (the store `⟨store', st.out⟩`). -/
theorem fnArmGeom_hArm_of_seam
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc' : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (a : Addr)
    (k : Nat) (armPC : BitVec 64) (calleeLoaded : Mem → Prop)
    (name : Option String) (params : List String) (body : List Stmt)
    (store' : Store)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String) (mpre : Mem)
    -- dispatch data for `armEntry_widen`:
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
    -- the middle seam (with the genuine opens named):
    (hSeam : FnArmSeamRun g N A SL φf φc' st a armPC calleeLoaded name params body store'
      sp r sret aExpr aEnv m0 v8 v9 v18 out0 mpre) :
    Triple
      (EvalEntry g N A SL φf φc' st d env (.fn name params body) sp r sret aEnv aExpr m0)
      (fun c => PreEpilogueV g N A SL φf φc' ⟨store', st.out⟩ (.closure a)
        sp r sret v8 v9 v18 out0 m0 mpre c) := by
  -- front: EvalEntry → ArmEntryK  (armEntry_widen)
  have hFront := armEntry_widen g N A SL φf φc' st d env (.fn name params body)
    k armPC calleeLoaded sp r sret aEnv aExpr m0
    hkle hklt hkind hslot hcallee hcalleeSurv hexprSurv harmAl htableStk
  -- middle: ArmEntryK → the sret-reads + hrest config  (FnArmSeamRun)
  -- back: that config → PreEpilogueV … (.closure a)  (preEpilogueV_of_writeLog)
  refine Triple.seq hFront (Triple.seq hSeam ?_)
  intro c hc
  obtain ⟨hmem, hkindR, hpayR, hnz, hrest⟩ := hc
  exact ⟨c, .refl c,
    preEpilogueV_of_writeLog g N A SL φf φc' ⟨store', st.out⟩ a
      sp r sret v8 v9 v18 out0 m0 mpre c hmem hkindR hpayR hnz hrest⟩

#print axioms fnArmGeom_hArm_of_seam

end Vsa.Sim
