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

/-- **`storeRepr_pushClosure`** — grow a represented store by one closure.

`hOld` is the OLD store represented at the NEW map `φc'` (agreeing with `φc` on the
old closure prefix): a caller with a closure-index-bounded store discharges it from
`PhiExtends φc φc' s.closures.size` by rewriting every `φc' ca = φc ca` for
`ca < s.closures.size`.  The remaining premises pin the fresh closure entry at spec
index `s.closures.size`:

* `hp` — its machine image `φc' s.closures.size = p`;
* `hrepr` — `ClosureRepr m φf p cd` (the two closure-header reads, established by the
  `fnArmClosureBuild` stores);
* `harena` / `halign` — the malloc block is in-arena and 8-aligned;
* `hpfresh` — `p` differs from every old closure image (injectivity extension), which
  a caller gets from malloc's freshness (`ExtDisjoint`) against the old closures.

The frames are untouched (`allocClosure` grows only the closures array), so `φf` and
the frame fields carry over verbatim. -/
theorem storeRepr_pushClosure
    {m : Mem} {N : NativeAddrs} {A : Arena} {φf φc' : Addr → Nat} {s : Store}
    {cd : ClosureData} {p : Nat}
    (hOld : StoreRepr m N A φf φc' s)
    (hp : φc' s.closures.size = p)
    (hrepr : ClosureRepr m φf p cd)
    (harena : A.contains p 16) (halign : p % 8 = 0)
    (hpfresh : ∀ ca, ca < s.closures.size → φc' ca ≠ p) :
    StoreRepr m N A φf φc' (s.allocClosure cd).1 where
  -- `(s.allocClosure cd).1.frames = s.frames` and `.closures = s.closures.push cd`
  -- hold by `rfl` (`Store.allocClosure`), so the `hfa`/`hca` bounds are defeq to the
  -- old-store / pushed-array bounds and no rewrite of the index type is needed.
  frames fa hfa := by
    have hfa' : fa < s.frames.size := hfa
    have := hOld.frames fa hfa'
    exact this
  closures ca hca := by
    have hca' : ca < (s.closures.push cd).size := hca
    rw [Array.size_push] at hca'
    rcases Nat.lt_or_ge ca s.closures.size with hlt | hge
    · -- old closure: carries over (reindex fixed at φc')
      have hval := hOld.closures ca hlt
      have heq : (s.allocClosure cd).1.closures[ca]'hca = s.closures[ca] :=
        Array.getElem_push_lt (h := hlt)
      rw [heq]; exact hval
    · -- the fresh closure at index s.closures.size
      have hce : ca = s.closures.size := by omega
      subst hce
      have heq : (s.allocClosure cd).1.closures[s.closures.size]'hca = cd :=
        Array.getElem_push_eq
      rw [heq, hp]; exact hrepr
  φf_inj a b ha hb h := hOld.φf_inj a b ha hb h
  φc_inj a b ha hb h := by
    have ha' : a < (s.closures.push cd).size := ha
    have hb' : b < (s.closures.push cd).size := hb
    rw [Array.size_push] at ha' hb'
    rcases Nat.lt_or_ge a s.closures.size with hla | hga <;>
      rcases Nat.lt_or_ge b s.closures.size with hlb | hgb
    · exact hOld.φc_inj a b hla hlb h
    · have hbe : b = s.closures.size := by omega
      subst hbe
      exact absurd (hp ▸ h) (hpfresh a hla)
    · have hae : a = s.closures.size := by omega
      subst hae
      exact absurd (hp ▸ h.symm) (hpfresh b hlb)
    · omega
  frames_arena fa hfa := hOld.frames_arena fa hfa
  closures_arena ca hca := by
    have hca' : ca < (s.closures.push cd).size := hca
    rw [Array.size_push] at hca'
    rcases Nat.lt_or_ge ca s.closures.size with hlt | hge
    · exact hOld.closures_arena ca hlt
    · have hce : ca = s.closures.size := by omega
      subst hce
      rw [hp]; exact ⟨harena, halign⟩

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
structure AllocClosureContract
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φc' : Addr → Nat)
    (st : Vsa.While.St) (cd : ClosureData) (a : Addr) (p : Nat)
    (Pre : Config → Prop)
    (sp r sret : BitVec 64) (m0 mpre : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String) : Prop where
  /-- The extended closures map and the fresh block, packaged as a `Triple` from the
  arm-supplied dispatch predicate `Pre` to the closure-build post at the FIXED
  post-memory `mpre`, extension `φc'`, and block `p` (fixed as contract parameters so
  the `Triple` post is composable with `FnArmSeamRun`, whose `φc'`/`mpre` are also
  fixed).  A construction of the structure witnesses them from the malloc result. -/
  spec :
    a = st.store.closures.size →
    Triple Pre
      (fun c =>
        c.σ.mem = mpre ∧
        -- fresh closure block + its representation
        φc' st.store.closures.size = p ∧ p ≠ 0 ∧
        A.contains p 16 ∧ p % 8 = 0 ∧
        (∀ ca, ca < st.store.closures.size → φc' ca ≠ p) ∧
        ClosureRepr mpre φf p cd ∧
        PhiExtends φc φc' st.store.closures.size ∧
        StoreRepr mpre N A φf φc' st.store ∧
        -- the VAL_CLOSURE sret reads (a = closures.size ⇒ φc' a = p)
        read32 mpre sret.toNat = some 4 ∧
        read64 mpre (sret.toNat + 8) = some (φc' a) ∧ φc' a ≠ 0 ∧
        -- the register / geometry / frame bundle `FnArmSeamRun`'s post demands
        (GoodState c.σ ∧ c.tick < 2 ∧
          c.σ.regs.get? Register.PC = some (0x800033ec#64) ∧
          c.σ.regs.get? Register.x9 = some sret ∧
          c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
          (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
          c.σ.sailOutput = out0 ∧ String.join out0.toList = st.out ∧
          Eval_exprLoaded mpre ∧
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

#print axioms storeRepr_pushClosure

end Vsa.Sim
