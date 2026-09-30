import Vsa.Sim.EvalSimCommon
import Vsa.Sim.CoherentReturn

/-!
# Layer 4 — M4 RECURSIVE-case common machinery: the IH-application glue

The leaf `EvalE` cases (`int`/`str`/`bool`/`null`/`var`) close their arms with
`armTail_v`: a `jal <value_*>` whose callee post is a *leaf* `value_*` spec.
The recursive cases (`neg`/`not`/`assign`/`binary`/`logical`/`call`) instead
contain `jal eval_expr` — the callee is `eval_expr` itself, and its behavior is
the **induction hypothesis** of the Layer-4 mutual recursion: a
`Triple (EvalEntry …) (EvalExit …)` for the sub-derivation. This file provides
the `armTail_v` analogue for that shape:

* **`MemExtends`** — presence-monotonicity of memory. The post-call code of a
  recursive arm re-reads the whole 24-byte sub-result buffer (`ld a3,144(sp)`
  reads bytes `[subsret, subsret+8)`, `ld a4,160(sp)` reads
  `[subsret+16, subsret+24)`), but `ValueRepr … (.int n)` pins only the kind
  word and the payload — bytes 4–7 and 16–23 are unconstrained. The machine
  `ld` still needs them *present*. `EvalExit` says nothing about presence, so
  the recursive motive must be stated against the widened exit below.
* **`EvalExitD`** — `EvalExit` plus (a) `MemExtends m0 mem` and (b) an
  exit-side `StoreRepr`-survival clause over the whole stack region
  `[SL.lo, SL.hi)` (the caller's *remaining* writes — its own sret write, its
  own spill traffic — all land in the stack region; the entry-side
  `store_survives` is for the *entry* store `st.store` at the *entry* maps and
  is useless for `st'.store` at the extended maps).
* **`EvalIH`** — the recursive-case motive shape: the ∀-closed
  `Triple (EvalEntry …) (EvalExitD …)` for a sub-derivation. This is
  `InductionScaffold.motive_EvalE` with `EvalExit` replaced by `EvalExitD`;
  the leaf minor premises must be re-landed at this exit (mechanical: their
  memory deltas are `writeMap4/8` chains, which preserve presence, and their
  store survival comes from the entry clause — RESIDUAL, tracked in
  `memory/m4-recursive-cases.md`).
* **`SubEvalReturn`** — the machine state a recursive arm holds right after
  its `jal eval_expr` returns: PC at the link, sub-result represented at
  `subsret`, `st'.store` re-represented (+ survival), the four spill slots
  intact, `eval_expr`'s code still loaded, callee-saved registers restored to
  the call-point frame `gpre`, memory framed to the pre-call memory `mcall`
  outside (sub-stack-window ∪ arena ∪ subsret), presence-extended.
* **`armTail_rec`** — THE GLUE: `jal eval_expr` (per-arm site hypothesis) ≫
  IH ⇒ `SubEvalReturn`. It builds the sub-call's `EvalEntry` from the arm
  state (choosing the sub-ghosts: `g_sub` := the post-`jal` register file,
  `sp_sub := sp - 1088`, `m0_sub := mcall`), applies the IH, and repackages
  `EvalExitD` into `SubEvalReturn` (spill-slot survival via the exit
  `memFrame` + arena/stack disjointness, code survival via
  `loaded_eval_expr_agreeP`, frame composition across the `jal`).

Geometry notes (all recorded as explicit hypotheses):
* the sub-call needs its own 2176-byte `StackOK` headroom below `sp - 1088`,
  so a recursive arm's entry must carry `SL.lo + 3264 ≤ sp` — ONE extra
  1088-byte frame per recursion level. The fully general induction needs
  depth-indexed headroom (`SL.lo + 1088 * (depthLeft…) ≤ sp`) — RESIDUAL.
* the arena must be disjoint from the stack region and from `eval_expr`'s
  code (`harenaStk`/`harenaCode`): the sub-call may genuinely allocate
  (arena writes), and the spill slots / code must survive that.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

-- (`MemExtends` + presence lemmas RELOCATED to `EvalSimCommon.lean`, wave 47e —
--  the leaf blockC files need them below `EvalRecCommon` in the import DAG.)

/-! ## `EvalExitD` — the presence/survival-widened exit -/

/-- `EvalExit` strengthened with the two clauses every recursive CALLER needs
from its sub-call:
1. presence monotonicity (`MemExtends m0 mem`);
2. an exit-side `StoreRepr` survival clause: the re-represented `st'.store`
   (at ONE coherent extended map pair) tolerates arbitrary further memory
   changes inside the stack region `[SL.lo, SL.hi)` — where all of the
   caller's remaining writes land. Instantiating `m' := c.σ.mem` recovers the
   plain exit `StoreRepr`. -/
def EvalExitD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop :=
  EvalExit g N A SL φf φc nf nc st' v sp r sret m0 c ∧
  MemExtends m0 c.σ.mem ∧
  ValueWordsTotal c.σ.mem sret.toNat ∧
  ∃ φf' φc' : Addr → Nat,
    PhiExtends φf φf' nf ∧
    PhiExtends φc φc' nc ∧
    ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store

/-! ## `EvalIH` — the recursive-case motive shape -/

/-- A reached result and an additional fact about that same configuration. -/
structure ReturnedWith (Result Extra : Config → Prop) (c : Config) : Prop where
  result : Result c
  extra : Extra c

/-! ## `SubEvalReturn` — the post-sub-call machine state -/

/-! ## `armTail_rec` — `jal eval_expr` ≫ IH ⇒ `SubEvalReturn`

The recursive-arm analogue of `armTail_v`. From the arm state at the `jal`'s
PC (`callPC`), with the sub-call's arguments already in place
(`a0 = subsret`, `a1 = aIn`, `a2 = aOperand`, `sp` lowered), one `jal` step
lands at `eval_expr`'s entry with link `retPC = callPC + 4`; the sub-call's
`EvalEntry` is assembled from the arm state, the IH is applied, and its
`EvalExitD` is repackaged into `SubEvalReturn`. -/

/-! ## `PreEpilogueVD` — the epilogue-entry state widened for the recursive exit

`PreEpilogueV` plus the two `EvalExitD` upgrade clauses ABOUT the epilogue-entry
memory `mpre`: (1) presence monotonicity `MemExtends m0 mpre`, and (2) the
`[SL.lo,SL.hi)`-survival of the (extended-map) `st.store`. The epilogue is
memory-pure, so both transport verbatim to the exit config; `blockD_v_rec` closes
`PreEpilogueVD → EvalExitD`. A recursive arm's block C produces this (it has both
facts internally — the pre-call memory is fully populated and all of its own
writes land in `[SL.lo,SL.hi)`), whereas the leaf block C's only produce the plain
`PreEpilogueV` for `blockD_v`. -/

/-! ## `blockD_v_rec` — the shared epilogue producing `EvalExitD`

Projects `blockD_v_rec_coherent` at the same execution endpoint. Ordinary
callers use `Owned := True`; the stronger post retains the common maps. -/

end Vsa.Sim
