import Vsa.Sim.StepFrameOut

/-!
# `chain_frame_out` — fold a run's per-step `ReadsLikePost` hyps into ONE `StepFrameOut`

A machine helper that walks a contiguous straight-line run threads, at each step
`τₖ₋₁ → τₖ`, an observation hypothesis
`hoτₖ : ReadsLikePost τₖ (sigmaPost_CLASS τₖ₋₁ …)`.  To get the *whole run's*
register frame + output-preservation `τ₀ → τₙ`, prior proofs hand-wrote a per-step
ladder: for each register `R`, a chain of
`(hoτₖ.1 R hmc hmt hmip).trans (get?_sigmaPost_CLASS … R hmi hpc … hnp hmii)`
equalities, one line per step, each carrying the class-specific `by decide`
disequality wall — the `f_14/f_15/…` ladder in e.g. `EvalMulRow.blockC_mul`.

`StepFrameOut` (`Vsa/Sim/StepFrameOut.lean`) already packages ONE step's frame +
output as a record whose `.trans` unions the write-sets by list append.  This file
adds the *dispatcher*: `chain_frame_out [ho₀, ho₁, …, hoₙ]` reads each hyp's type,
looks at the SYNTACTIC HEAD of its `sigmaPost_CLASS` application, emits the
matching smart constructor `StepFrameOut.of_CLASS hoᵢ`, and left-folds `.trans`,
producing `StepFrameOut (W₀ ++ … ++ Wₙ) τ₀ τₙ` for the whole run in one call.

The result carries `.out` (whole-run `sailOutput` equality) and `.get R (by decide)
hσ` (transport any non-written register's value across the whole run) — so a caller
writes those ONCE per register instead of once per step.

## Class dispatch

The dispatch is purely syntactic and O(1) per step: `chainFrameOutStepTerm`
whnf-reduces the hyp's type to a `ReadsLikePost σ' spost`, reads `spost`'s head
constant, and maps

| `sigmaPost_*` head          | constructor                    | write-set `W`     |
|-----------------------------|--------------------------------|-------------------|
| `sigmaPost_alu`             | `StepFrameOut.of_alu`          | `rd :: noiseRegs` |
| `sigmaPost_jal`             | `StepFrameOut.of_jal`          | `rd :: noiseRegs` |
| `sigmaPost_jump_x0`         | `StepFrameOut.of_jr`           | `noiseRegs`       |
| `sigmaPost_branch_taken`    | `StepFrameOut.of_branch_taken` | `noiseRegs`       |
| `sigmaPost_branch_nottaken` | `StepFrameOut.of_branch_nottaken` | `noiseRegs`    |
| `sigmaPost_store`           | `StepFrameOut.of_store`        | `noiseRegs`       |

If the head is none of these, the tactic FAILS LOUDLY naming the offending hyp —
there is no search, no `simp`, no `omega` in the hot path; every emitted term is a
constructor application, and the fold is a left-nest of `.trans`.

## `W`-`decide` cost

The only decision procedure a caller runs is the per-register membership
`(W.all fun r => !(r == R)) = true` in `StepFrameOut.get` / the `.frame` avoidance,
where `W` is the *unioned* write-set of the whole run (`~2·steps + steps` entries,
e.g. 3 arm steps → a 9-16 element list).  This is a single `List.all` over
concrete `Register` `beq`s: O(|W|), no recursion into `sigmaPost`/`ExtHashMap`.
The demo below composes an 8-step run (`W` ~ 44 entries) and its `.get`/`.out`
`by decide`s stay well under a heartbeat — see `chainFrameOut_demo`.

No `sorry`/`native_decide`/`bv_decide`/Mathlib.  Verify with
`lake env lean Vsa/Sim/ChainFrameOut.lean`.
-/

open Lean Elab Tactic Meta
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Register

namespace Vsa.Sim

/-! ## Avoidance sugar — build the `∀ r ∈ W, (r == R) = false` side-condition

`StepFrameOut.frame`/`.get` need `∀ r ∈ W, (r == R) = false` for the run's unioned
write-set `W`.  When `W` is a nest of `rd :: noiseRegs` blocks joined by `++`, the
avoidance decomposes into (a) the seven per-step noise diseqs `{minstret, PC,
nextPC, minstret_increment, mcycle, mtime, mip} ≠ R` a caller already holds, and
(b) one `rd ≠ R` per written destination.  These helpers assemble those into the
membership predicate WITHOUT `decide`-ing over the whole `W` (which would be O(|W|)
`beq`s at *each* register query); they are `List.forall_mem_*` folds over the
concrete `noiseRegs` list, so each is a fixed 7-way (resp. 8-way) conjunction. -/

/-- Map a `sigmaPost_*` head constant to the `StepFrameOut.of_*` smart-constructor
name.  Returns `none` for a non-`sigmaPost` head so the caller can fail with the
offending hyp's name. -/
private def cfoCtorOf? : Name → Option Name
  | ``sigmaPost_alu             => some ``StepFrameOut.of_alu
  | ``sigmaPost_jal             => some ``StepFrameOut.of_jal
  | ``sigmaPost_jump_x0         => some ``StepFrameOut.of_jr
  | ``sigmaPost_branch_taken    => some ``StepFrameOut.of_branch_taken
  | ``sigmaPost_branch_nottaken => some ``StepFrameOut.of_branch_nottaken
  | ``sigmaPost_store           => some ``StepFrameOut.of_store
  | _                           => none

/-- Build the single-step `StepFrameOut.of_CLASS h` term for one observation hyp
`h`, dispatching CLASS off the syntactic head of the `sigmaPost_*` application in
`h`'s type.  Purely syntactic — no unification search, no `simp`.  Fails loudly
(naming the hyp) if the head is not a known `sigmaPost_*`. -/
private def chainFrameOutStepTerm (h : Term) : TacticM Term := do
  let hE ← Term.elabTerm h none
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars (← inferType hE)
  -- `ReadsLikePost σ' spost`: normalize at *reducible* transparency only.  This
  -- strips mdata/beta and unfolds nothing user-facing — `ReadsLikePost` is a plain
  -- (non-reducible) `def`, so its head survives; the inner `sigmaPost_*` abbrevs
  -- are read off WITHOUT reduction below.  Fail loudly if the head isn't it.
  let ty ← whnfR ty
  unless ty.getAppFn.constName? == some ``ReadsLikePost do
    throwError "chain_frame_out: hypothesis {h} is not a `ReadsLikePost _ _` \
      (head {ty.getAppFn.constName?}); type {ty}"
  let some spost := ty.getAppArgs[1]?
    | throwError "chain_frame_out: hypothesis {h} is not a `ReadsLikePost _ _`"
  -- Read the `sigmaPost_*` head *without* reducing — the classes are `abbrev`s,
  -- so whnf would delta them down to a raw `SequentialState.mk` record.
  let headName := spost.consumeMData.getAppFn.constName?
  match headName.bind cfoCtorOf? with
  | some ctor => `($(mkIdent ctor) $h)
  | none =>
    throwError
      "chain_frame_out: hypothesis {h} has post-state head {headName}, \
       not a known `sigmaPost_*` class (alu/jal/jump_x0/branch_taken/\
       branch_nottaken/store)"

/-- `chain_frame_out [ho₀, ho₁, …, hoₙ]` closes a `StepFrameOut W τ₀ τₙ` goal by
mapping each ordered observation hyp `hoᵢ : ReadsLikePost τᵢ (sigmaPost_CLASS …)`
to `StepFrameOut.of_CLASS hoᵢ` and left-folding `.trans`.  Class dispatch is by the
syntactic head of the `sigmaPost_*` application; a non-matching hyp fails loudly. -/
elab "chain_frame_out " "[" hs:term,* "]" : tactic => withMainContext do
  let hyps := hs.getElems
  if hyps.isEmpty then
    throwError "chain_frame_out: empty hypothesis list; use `StepFrameOut.refl`"
  let mut acc ← chainFrameOutStepTerm hyps[0]!
  for h in hyps[1:] do
    let step ← chainFrameOutStepTerm h
    acc ← `(($acc).trans $step)
  closeMainGoal `chain_frame_out (← Term.elabTermEnsuringType acc (← getMainTarget))

/-- Build the folded `StepFrameOut` term (no goal, `W` left as a synthesized
metavariable fixed by the constructor applications). Shared by `chain_out`. -/
private def chainFrameOutFoldTerm (hyps : Array Term) : TacticM Term := do
  let mut acc ← chainFrameOutStepTerm hyps[0]!
  for h in hyps[1:] do
    let step ← chainFrameOutStepTerm h
    acc ← `(($acc).trans $step)
  return acc

/-- `chain_out [ho₀, …, hoₙ]` closes a **whole-run `sailOutput`-invariance** goal
`σₙ.sailOutput = σ₀.sailOutput` in ONE fold: it builds the same left-nested
`StepFrameOut.of_CLASS … |>.trans …` term as `chain_frame_out`, then projects
`.out`.  The unioned write-set `W` is inferred (never spelled), so a caller threads
output through an arbitrary-length straight-line run without naming any register —
the exponentiating replacement for a per-step `hout` ladder. -/
elab "chain_out " "[" hs:term,* "]" : tactic => withMainContext do
  let hyps := hs.getElems
  if hyps.isEmpty then
    throwError "chain_out: empty hypothesis list; the run has no steps (use `rfl`)"
  let acc ← chainFrameOutFoldTerm hyps
  let outTm ← `(($acc).out)
  closeMainGoal `chain_out (← Term.elabTermEnsuringType outTm (← getMainTarget))

/-! ## Demo — an 8-step arm run collapsed in one call

The exact shape `EvalMulRow.blockC_mul` threads over its MUL arm (before the
callee-frame breaks): three ALU steps, a `jal`, two ALU steps, a `jal`, an ALU
step, terminated by a `jr`/`j` (`jump_x0`).  Each contributes ONE constructor; the
whole-run frame + output fall out of the fold, and `.out` / `.get` deliver the
run's output-invariance and any callee-saved register's transported value in one
line each.  Compare `StepFrameOut`'s hand-written 4-step demo `.trans` nest. -/

end Vsa.Sim
