import Vsa.Sim.StepFrameOut

open Lean Elab Tactic Meta
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Register

namespace Vsa.Sim

private def cfoCtorOf? : Name → Option Name
  | ``sigmaPost_alu             => some ``StepFrameOut.of_alu
  | ``sigmaPost_jal             => some ``StepFrameOut.of_jal
  | ``sigmaPost_jump_x0         => some ``StepFrameOut.of_jr
  | ``sigmaPost_branch_taken    => some ``StepFrameOut.of_branch_taken
  | ``sigmaPost_branch_nottaken => some ``StepFrameOut.of_branch_nottaken
  | ``sigmaPost_store           => some ``StepFrameOut.of_store
  | _                           => none

private def chainFrameOutStepTerm (h : Term) : TacticM Term := do
  let hE ← Term.elabTerm h none
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars (← inferType hE)

  let ty ← whnfR ty
  unless ty.getAppFn.constName? == some ``ReadsLikePost do
    throwError "chain_frame_out: hypothesis {h} is not a `ReadsLikePost _ _` \
      (head {ty.getAppFn.constName?}); type {ty}"
  let some spost := ty.getAppArgs[1]?
    | throwError "chain_frame_out: hypothesis {h} is not a `ReadsLikePost _ _`"

  let headName := spost.consumeMData.getAppFn.constName?
  match headName.bind cfoCtorOf? with
  | some ctor => `($(mkIdent ctor) $h)
  | none =>
    throwError
      "chain_frame_out: hypothesis {h} has post-state head {headName}, \
       not a known `sigmaPost_*` class (alu/jal/jump_x0/branch_taken/\
       branch_nottaken/store)"

elab "chain_frame_out " "[" hs:term,* "]" : tactic => withMainContext do
  let hyps := hs.getElems
  if hyps.isEmpty then
    throwError "chain_frame_out: empty hypothesis list; use `StepFrameOut.refl`"
  let mut acc ← chainFrameOutStepTerm hyps[0]!
  for h in hyps[1:] do
    let step ← chainFrameOutStepTerm h
    acc ← `(($acc).trans $step)
  closeMainGoal `chain_frame_out (← Term.elabTermEnsuringType acc (← getMainTarget))

private def chainFrameOutFoldTerm (hyps : Array Term) : TacticM Term := do
  let mut acc ← chainFrameOutStepTerm hyps[0]!
  for h in hyps[1:] do
    let step ← chainFrameOutStepTerm h
    acc ← `(($acc).trans $step)
  return acc

elab "chain_out " "[" hs:term,* "]" : tactic => withMainContext do
  let hyps := hs.getElems
  if hyps.isEmpty then
    throwError "chain_out: empty hypothesis list; the run has no steps (use `rfl`)"
  let acc ← chainFrameOutFoldTerm hyps
  let outTm ← `(($acc).out)
  closeMainGoal `chain_out (← Term.elabTermEnsuringType outTm (← getMainTarget))

end Vsa.Sim
