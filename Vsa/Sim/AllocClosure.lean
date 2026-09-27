import Vsa.Sim.ReprSurvival
import Vsa.Sim.InterpEntry
import Vsa.Sim.EvalSimCommon

/-!
# `AllocClosure` — the closures-arena callee contract (the `env_new_spec` analog)

`EvalE.fn` allocates a heap `ClosureData⟨env, name, params, body⟩` and returns
`.closure a`.  On the machine the `EX_FN` arm runs

```
li a0,16 ; sd a3,0(sp) ; jal malloc          -- fnArmMallocCall  (0x800033c4)
ld a3,0(sp) ; beqz a0,OOM                     -- reload record ptr; NULL edge OFF
li a5,4 ; sd s0,0(a0) ; sd a3,8(a0)           -- fnArmClosureBuild (0x800033d8)
        ; sd a0,8(s1) ; sw a5,0(s1)
```

so a fresh 16-byte `Closure` record at the malloc'd block `p` is written with
`closure[0] := s0 = fn_expr` (the `EX_FN` AST node) and `closure[8] := a3 = φf env`
(the captured-environment frame pointer), matching `ClosureRepr`'s two reads
(`RuntimeRepr.lean:93`).  The `VAL_CLOSURE` box (`sret[0]=4`, `sret[8]=p`) is the
`fnArmClosureBuild` seg's job and is marshalled by `preEpilogueV_of_writeLog`; THIS
file is the *store-side* half — the closures-array grow.

## Two reusable facts

* **`storeRepr_pushClosure`** — the genuinely-missing general fact (there was NO
  StoreRepr-grow / `closures.push` lemma anywhere; `env_new_post` produces only the
  fresh `FrameRepr`, the store reindex is done at the eval-arm caller).  Given the
  OLD store already represented at the EXTENDED map `φc'` (dischargeable from
  `PhiExtends φc φc' s.closures.size` when the store is closure-index-bounded —
  supplied as `hOld`), plus the fresh closure's `ClosureRepr`, arena/alignment, and
  injectivity extension, it builds `StoreRepr m N A φf φc' (s.closures.push cd)`.
  Reused by every closure producer (`allocClosure` here, any future one).

* **`AllocClosureContract`** — the callee contract structure (mirrors
  `env_new_post`'s shape: fresh aligned in-arena block `p`, its `ClosureRepr`, and a
  memory frame outside `[p,p+16) ∪ privFoot ∪ stack`).  Its single `spec` field is
  the total-correctness `Triple` for the `malloc(16) ≫ closure-build` run.  Nobody
  constructs it — it is a named hypothesis of the arm derivation, exactly as
  `MallocContract` is of the final theorem.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-! ## `storeRepr_pushClosure` — the closures-array grow -/

/-! ## `AllocClosureContract` — the malloc≫closure-build callee contract

The `env_new_spec` analog for the closures arena.  Its `spec` field is the
total-correctness `Triple` for the whole `EX_FN` build run — from the arm's
`ArmEntryK`-shaped dispatch config (register/geometry pins carried opaquely as the
`Pre` predicate the arm supplies) to a post config `c` that, at a fixed post-memory
`mpre` and extension `φc'`, exposes:

* the fresh closure block `φc' st.store.closures.size = p`, in-arena, aligned,
  fresh vs every OLD closure image (`hp`/`harena`/`halign`/`hpfresh`);
* its `ClosureRepr mpre φf p cd` (the two closure-header reads the
  `fnArmClosureBuild` stores leave);
* the OLD store still represented at `φc'` (`hOld`: dischargeable from
  `PhiExtends φc φc' st.store.closures.size` when the store is closure-index-bounded);
* the `PhiExtends φc φc' st.store.closures.size` witness itself;
* the `VAL_CLOSURE` sret reads (kind `4`, payload `φc' a`, non-null) and the full
  register/geometry/frame bundle `PostRest` that `FnArmSeamRun`'s post demands.

The genuine machine opens (the `EX_FN` arm-head `a3 := φf env` decode, the `malloc`
splice threading `MallocContract.spec`, and the `fnArmClosureBuild` write-log
marshalling into `mpre`/the sret reads) are precisely what a construction of this
structure discharges — nobody constructs it here; it is a NAMED hypothesis of the
arm derivation, exactly as `MallocContract` is of the final theorem.  What THIS file
proves is that `storeRepr_pushClosure` upgrades the contract's `hOld` (old store at
`φc'`) to the GROWN-store `StoreRepr` `FnArmSeamRun` wants — the store-side seam. -/

end Vsa.Sim
