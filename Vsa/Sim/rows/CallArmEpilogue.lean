import Vsa.Sim.EvalSimCommon
import Vsa.Sim.rows.CallRows

/-!
# `CallArmEpilogue` — the φc-WIDENED shared epilogue (`blockD_v_phic`)

`blockD_v` (`EvalSimCommon.lean`) proves the shared `eval_expr` epilogue
`PreEpilogueV … → EvalExit …` with an IDENTITY φ-extension: its produced
`EvalExit` witnesses the `result`/`store` existentials at the ENTRY maps `φf`/`φc`
(`PhiExtends.refl`) and re-represents `st.store` — true for every LEAF arm, whose
sub-derivation neither allocates a frame nor a closure (`st' = st`,
`store.frames.size`/`store.closures.size` unchanged).

The `EX_FN` and `EX_CALL` arms are DIFFERENT: their sub-derivation extends the
store (a closure allocation for `.fn`; frames/closures for the closure-call body),
so the exit store re-represents `st'.store` (grown) at a **non-identity**
`PhiExtends φc φc' nc` / `PhiExtends φf φf' nf` — exactly the widening the
`CallResidProviders`/`CallRows` ledger flagged as the residual-5 epilogue gap
("`blockD_v` proves the exit with an IDENTITY `φc`-extension at `nc =
st.store.closures.size`; the fn arm's exit closures array has grown by one, so the
epilogue needs a `φc`-WIDENED `blockD_v` variant").

This file supplies that variant ADDITIVELY (`blockD_v` is untouched), reusing the
`EvalRecWiden`/`evalExitD_of_evalExit_rec`-shaped `PhiExtends.mono`/`.trans`
reindexing already used by `segExit_extend` (`EvalArgs.lean`). The construction is
a pure record reshape: `blockD_v` is invoked at the SHIFTED ghosts
(`st := st'`, `φf := φf'`, `φc := φc'`), producing an `EvalExit` at `st'`'s OWN
sizes/maps, and `evalExit_rebase` re-bases it down to the entry sizes/maps `nf`/
`nc`/`φf`/`φc` the `mEvalE` motive demands — NO new decode, no re-run of the seven
epilogue instructions.

## Consumers (documented for the eventual fn/call row wiring)

* **`FnArmSpec`'s epilogue** (`EX_FN`): closures array grows by one, so
  `nc = st.store.closures.size`, `st'.store.closures.size = nc + 1`, and the
  `allocClosure` post supplies `φc'` with `PhiExtends φc φc' nc`. The fn arm feeds
  its `PreEpilogueV` at `(φf, φc', st')` (frames unchanged, closures widened) into
  `blockD_v_phic` to obtain the `EvalExit … st.store...size … st' (.closure a)`
  the row's `EvalRecWiden` then upgrades to `EvalExitD`.
* **`CallArmSpec`'s epilogue** (`EX_CALL`): the closure body may allocate BOTH
  frames and closures, so both φ-maps widen (`PhiExtends φf φf' nf`,
  `PhiExtends φc φc' nc`); the closure-crux post (`callClosureSim`) supplies the
  pair. Same `blockD_v_phic` call at `(φf', φc', st''')`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib. Every leftover is the
honest `PhiExtends`/`≤` reindexing the sub-derivation's post already carries.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## `evalExit_rebase` — re-base an `EvalExit` to earlier φ-maps / entry sizes

The `EvalExit` analog of `segExit_extend` (`EvalArgs.lean`).  Three φ/size-dependent
fields must be rebased:

* **`result`** — `∃ φc'', PhiExtends φc'' … nc'' ∧ ValueRepr …`.  Its
  `PhiExtends φc' φc'' nc'` composes with the entry-to-`φc'` extension and the
  size monotonicity (`PhiExtends.mono` narrows `nc' → nc`, `.trans` chains).
* **`store`** — `∃ φf'' φc'', PhiExtends … ∧ StoreRepr …`.  Same composition on
  both maps.
* **`memFrame`** — framed to the inner memory (`= m0` here, since the epilogue runs
  over the SAME `m0` at both ghost instantiations); the `hmid` frame threads it
  back.  For the straight epilogue `mNow = m0`, so `hmid` is `fun _ _ _ => rfl`.

`good`/`tick`/`pc`/`a0`/`ra`/`spReg`/`minstret`/`out`/`frame` are φ/size-independent
and pass through unchanged.  This is the exact `PhiExtends.mono`/`.trans` reindexing
`evalExitD_of_evalExit_rec` and `segExit_extend` already use — no new machine
content. -/
theorem evalExit_rebase
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φf' φc' : Addr → Nat)
    (nf nc nf' nc' : Nat)
    (st' : SpecSt) (v : Value) (sp r sret : BitVec 64) (m0 mNow : Mem) (c : Config)
    (hpf : PhiExtends φf φf' nf)
    (hpc : PhiExtends φc φc' nc)
    (hle : nf ≤ nf' ∧ nc ≤ nc')
    (hmid : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ mNow[a]? = m0[a]?)
    (hexit : EvalExit g N A SL φf' φc' nf' nc' st' v sp r sret mNow c) :
    EvalExit g N A SL φf φc nf nc st' v sp r sret m0 c := by
  obtain ⟨φcR, hpcR, hvalR⟩ := hexit.result
  obtain ⟨φfS, φcS, hpfS, hpcS, hstoreS⟩ := hexit.store
  exact
    { good := hexit.good
      tick := hexit.tick
      pc := hexit.pc
      a0 := hexit.a0
      ra := hexit.ra
      spReg := hexit.spReg
      minstret := hexit.minstret
      result := ⟨φcR, hpc.trans (PhiExtends.mono hle.2 hpcR), hvalR⟩
      store := ⟨φfS, φcS, hpf.trans (PhiExtends.mono hle.1 hpfS),
        hpc.trans (PhiExtends.mono hle.2 hpcS), hstoreS⟩
      out := hexit.out
      frame := hexit.frame
      memFrame := fun a ha1 ha2 =>
        match hexit.memFrame a ha1 ha2, hmid a ha1 ha2 with
        | Or.inl hsret, _ => Or.inl hsret
        | Or.inr hframe, Or.inl hsret => Or.inl hsret
        | Or.inr hframe, Or.inr hmidEq => Or.inr (hframe.trans hmidEq) }

/-! ## `blockD_v_phic` — the φ-WIDENED shared epilogue

`blockD_v` at the SHIFTED ghosts `(st := st', φf := φf', φc := φc')`, re-based to the
entry sizes/maps via `evalExit_rebase`.  The pre is `PreEpilogueV`-shaped at the
EXTENDED maps (the sub-derivation's post already re-represents `st'.store` /
`ValueRepr … φc' … v` there); the widened `PhiExtends`/`≤` facts are threaded to the
re-base.  The seven epilogue instructions run over the SAME `m0` (the caller frame)
in both instantiations, so the memory-frame `hmid` collapses to reflexivity. -/
theorem blockD_v_phic
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φf' φc' : Addr → Nat)
    (nf nc : Nat)
    (st' : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem)
    (Q : Mem → Prop)
    -- the sub-derivation's φ-extension witnesses (from `allocClosure`/the closure
    -- crux): the exit maps `φf'`/`φc'` extend the entry maps over the entry sizes.
    (hpf : PhiExtends φf φf' nf)
    (hpc : PhiExtends φc φc' nc)
    -- store counts only grow across the arm (frames/closures possibly allocated).
    (hle : nf ≤ st'.store.frames.size ∧ nc ≤ st'.store.closures.size) :
    Triple
      (fun c => ∃ mpre, PreEpilogueV g N A SL φf' φc' st' v sp r sret v8 v9 v18 out0 m0 mpre c ∧ Q mpre)
      (fun c => EvalExit g N A SL φf φc nf nc st' v sp r sret m0 c ∧ Q c.σ.mem) := by
  intro c hpre
  obtain ⟨c', hs, hExit', hQ⟩ :=
    blockD_v g N A SL φf' φc' st' v sp r sret v8 v9 v18 out0 m0 Q c hpre
  refine ⟨c', hs, ?_, hQ⟩
  exact evalExit_rebase g N A SL φf φc φf' φc'
    nf nc st'.store.frames.size st'.store.closures.size st' v sp r sret m0 m0 c'
    hpf hpc hle (fun a _ _ => Or.inr rfl) hExit'

#print axioms evalExit_rebase
#print axioms blockD_v_phic

end Vsa.Sim
