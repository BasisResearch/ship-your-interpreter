import Vsa.Triple
import Vsa.Sim.TripleCat
import Vsa.Sim.DeriveCallSeg

/-!
# `FnSummary` — whole-function summaries (the gen_fn support layer)

One rung above the per-seg layer: a **whole function** (entry PC → exit
condition) as a single named object, foldable across the call graph.  This is
the Lean side of `scripts/gen_fn.py` (the CFG assembler): gen_fn emits per-block
arm sections (the genseg idiom), one named-field `Post` structure per join
point, and a top-level theorem packaging the fold as a `FnSummary`.

Design:

* `PCAt pc c` — parked at `pc`.  A function summary's precondition is always
  `PCAt entry ∧ Pre`; naming the conjunction here keeps every emitted summary in
  the same canonical shape (seams are `rfl`-shaped, not re-derived).
* `FnSummary entry Pre Post` — the summary proper: a `Triple` from the parked
  entry to the function's exit condition `Post`.  The *content* of `Post` (result
  registers, callee-saved frame, memory footprint, sailOutput delta) lives in the
  per-function named-field structure gen_fn emits — reuse
  `FrameMeta.abiFrame_of_wrChain` / `FrameMeta.memFrame_of_chain` shapes there,
  and thread output via the `chain_out` idiom.  `FnSummary` itself stays
  model-independent plumbing (`Triple.seq`/`conseq` only), like `DeriveCallSeg`.

The fold combinators (ALL built from existing pieces):

* `FnSummary.weaken` — consequence (`Triple.conseq`).
* `FnSummary.seq` — two summaries through a seam entailment (`Triple.seq`).
* `FnSummary.callSplice` — `prefix ≫ callee-summary ≫ suffix` (`callSegConseq`).
* `tailJump_of_summary` — the ONE genuinely new seam: a span ending in a
  tail-`j` into another function.  genseg does not model tail-`j` as a call:
  the `j` transfers control to the target's entry with `ra` still holding the
  ORIGINAL caller's return address, so the target returns FOR the caller and
  there is NO suffix — the target's exit *is* the whole caller's exit.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable
open Vsa.Machine (Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-- Parked at `pc`: the canonical "control is at" predicate every function
summary's precondition opens with. -/
def PCAt (pc : BitVec 64) (c : Config) : Prop :=
  c.σ.regs.get? Register.PC = some pc

/-- **A whole-function summary.**  From a configuration parked at the function's
entry PC satisfying the summary precondition `Pre` (ABI arguments, code-region
pins, stack/HTIF side conditions…), the machine runs to the function's exit
condition `Post` — parked at the caller's return target for a `ret`-exiting
function, or at the tail-target's own exit for a tail-`j` one — carrying the
derived named-field post (result registers, clobber frame, memory footprint,
sailOutput delta). -/
structure FnSummary (entry : BitVec 64) (Pre Post : Config → Prop) : Prop where
  run : Triple (fun c => PCAt entry c ∧ Pre c) Post

/-- Consequence for summaries: strengthen the precondition, weaken the post. -/
theorem FnSummary.weaken {entry : BitVec 64} {Pre Pre' Post Post' : Config → Prop}
    (S : FnSummary entry Pre Post)
    (hpre : ∀ c, Pre' c → Pre c) (hpost : ∀ c, Post c → Post' c) :
    FnSummary entry Pre' Post' :=
  ⟨Triple.conseq S.run (fun c h => ⟨h.1, hpre c h.2⟩) hpost⟩

/-- Sequential composition of two summaries through a seam entailment: the
first summary's exit lands parked at the second's entry with its precondition
established.  (`Triple.seq` + the seam `Triple.conseq`.) -/
theorem FnSummary.seq {e₁ e₂ : BitVec 64} {Pre Mid Pre₂ Post : Config → Prop}
    (S₁ : FnSummary e₁ Pre Mid) (S₂ : FnSummary e₂ Pre₂ Post)
    (hseam : ∀ c, Mid c → PCAt e₂ c ∧ Pre₂ c) :
    FnSummary e₁ Pre Post :=
  ⟨Triple.seq S₁.run (Triple.lmap hseam S₂.run)⟩

/-- **Call splice around a callee summary** — `prefix ≫ callee ≫ suffix`
(`callSegConseq` with the callee's `FnSummary` packaging opened).  `pre` is the
caller-side prefix Triple landing parked at the callee's entry with its
precondition marshalled; `suf` resumes from the callee's exit condition. -/
theorem FnSummary.callSplice {entry : BitVec 64}
    {P Mid1 Mid2 Q CPre CPost : Config → Prop}
    (pre : Triple P Mid1) (callee : FnSummary entry CPre CPost)
    (suf : Triple Mid2 Q)
    (hin : ∀ c, Mid1 c → PCAt entry c ∧ CPre c)
    (hout : ∀ c, CPost c → Mid2 c) :
    Triple P Q :=
  callSegConseq pre callee.run suf hin hout

/-- **The tail-`j` seam.**  The caller's body Triple runs to a configuration
parked at the tail-target's entry (the `j` executed; `ra` untouched, still the
ORIGINAL return address) with the target's precondition established; the
target's summary carries the run to its own exit, which IS the caller's exit —
no suffix exists.  This is the terminator class genseg does not model as a
call (`__swrite`'s `j _write_r`). -/
theorem tailJump_of_summary {entry : BitVec 64} {P Mid Q Pre : Config → Prop}
    (body : Triple P Mid) (target : FnSummary entry Pre Q)
    (hin : ∀ c, Mid c → PCAt entry c ∧ Pre c) :
    Triple P Q :=
  Triple.seq body (Triple.lmap hin target.run)

/-- `tailJump_of_summary`, packaged back up as the caller's own summary (the
caller's body Triple stated from its parked entry). -/
theorem FnSummary.tailJump {e₀ entry : BitVec 64} {Pre Mid TPre Q : Config → Prop}
    (body : Triple (fun c => PCAt e₀ c ∧ Pre c) Mid)
    (target : FnSummary entry TPre Q)
    (hin : ∀ c, Mid c → PCAt entry c ∧ TPre c) :
    FnSummary e₀ Pre Q :=
  ⟨tailJump_of_summary body target hin⟩

#print axioms FnSummary.weaken
#print axioms FnSummary.seq
#print axioms FnSummary.callSplice
#print axioms tailJump_of_summary
#print axioms FnSummary.tailJump

end Vsa.Sim
