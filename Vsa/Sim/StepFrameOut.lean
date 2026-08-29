import Vsa.Sim.StepObs
import Vsa.Sim.RegPins

/-!
# `StepFrameOut` — one-call per-step register-frame + output-preservation

Recent spec work (e.g. `divdi3_spec` carrying a `sailOutput` field and a
callee-saved register frame) threaded, at *every* machine step, two facts by
hand:

* output preservation `σ'.sailOutput = σ.sailOutput` (via `hobs.out` +
  `sailOutput_sigmaPost_CLASS`), and
* the register frame `σ'.regs.get? R = σ.regs.get? R` for every non-written `R`
  (via per-register `obs_CLASS_other hobs R (by decide)×8 hσ`, or the blanket
  `get?_sigmaPost_CLASS`).

That is 5-10 lines per step across ~28 helpers. `StepFrameOut` folds both into a
**single record per step**, composable across a run by `.trans`, mirroring the
`FrameCalc` (`Vsa/Sim/FrameCalc.lean`) packaging template: a per-step fact whose
composition is a *list append* over the write-set, never `ExtHashMap` reduction.

## Design of the frame predicate

The written-register set differs per instruction class (ALU/JAL write `rd`; the
jumps/branches/store write only noise). `FrameCalc` handles the analogous problem
(write *windows* differing per step) by carrying the write **log** and unioning
it by `++` in `.trans`. We mirror that here: `StepFrameOut` carries an explicit
write-set `W : List Register`, and the frame is quantified over the value-free
avoidance hypothesis `∀ r ∈ W, (r == R) = false` — exactly the shape
`Vsa.Sim.all_notin` and `keep_of_frame` already consume. `.trans` appends the
two write-sets; the caller discharges the merged avoidance by `decide`.

Every class's `W` is `noiseRegs` (`{minstret, PC, nextPC, minstret_increment,
mcycle, mtime, mip}` — the union of the step-write noise and the tick-write
noise) optionally prefixed by the written `rd_reg`. So the tick-parity
registers `{mcycle, mtime, mip}` that `ReadsLikePost` peels and the step-write
registers `{minstret, PC, nextPC, minstret_increment, rd_reg}` that
`get?_sigmaPost_CLASS` peels are *both* covered by the single `W`-avoidance
hypothesis.

## Ergonomics delivered

A caller that used to write

```
obs_alu_other hobs R (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) hσ
```

(the `by decide × 8` register disequality wall) now writes

```
(sfo.frame R (by decide)).trans hσ
```

and threads output with `sfo.out` (or `.trans` for a whole run's output).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Register

namespace Vsa.Sim

/-- One step's register-frame + output-preservation fact between two `MState`s.

`out` is the HTIF-console (`sailOutput`) invariance; `frame` says every register
outside the concrete write-set `W` reads identically in `σ'` and `σ`. `W` is
value-free (a `List Register`), so `.trans` unions write-sets by `++` and callers
discharge avoidance by `decide` — no `ExtHashMap` reduction, mirroring
`FrameCalc`. -/
structure StepFrameOut (W : List Register) (σ σ' : MState) : Prop where
  out   : σ'.sailOutput = σ.sailOutput
  frame : ∀ R : Register, (∀ r ∈ W, (r == R) = false) →
            σ'.regs.get? R = σ.regs.get? R

namespace StepFrameOut

/-- The empty step: identical states, empty write-set. -/
theorem refl (σ : MState) : StepFrameOut [] σ σ :=
  ⟨Eq.refl _, fun _ _ => Eq.refl _⟩

/-- Compose two steps. The output-eqs chain; the frame holds on the union `W₁ ++
W₂` of the two write-sets (a register avoided by both is avoided by the join),
mirroring `FrameCalc.trans`'s log append. -/
theorem trans {W₁ W₂ : List Register} {σ σ' σ'' : MState}
    (h1 : StepFrameOut W₁ σ σ') (h2 : StepFrameOut W₂ σ' σ'') :
    StepFrameOut (W₁ ++ W₂) σ σ'' where
  out := h2.out.trans h1.out
  frame := by
    intro R hR
    have hR1 : ∀ r ∈ W₁, (r == R) = false := fun r hr => hR r (List.mem_append_left _ hr)
    have hR2 : ∀ r ∈ W₂, (r == R) = false := fun r hr => hR r (List.mem_append_right _ hr)
    exact (h2.frame R hR2).trans (h1.frame R hR1)

/-! ## The noise write-set and the `ReadsLikePost` peel

`noiseRegs = {minstret, PC, nextPC, minstret_increment, mcycle, mtime, mip}` is
the union of the tick-noise (`{mcycle,mtime,mip}`, peeled by `ReadsLikePost.1`)
and the step-noise (`{minstret, PC, nextPC, minstret_increment}`, peeled by
`get?_sigmaPost_CLASS`). A `W`-avoidance hypothesis containing `noiseRegs` thus
supplies *both* peels' side conditions. The `noise_*` helpers extract the six
concrete `(reg == R) = false` facts a class needs from `∀ r ∈ noiseRegs …`. -/

/-- From a full `noiseRegs`-containing avoidance, read off the tick + step
disequalities a `sigmaPost_alu`-class step needs. -/
theorem of_alu {σ σ' : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) :
    StepFrameOut (rd :: noiseRegs) σ σ' where
  out := (hobs.out).trans (sailOutput_sigmaPost_alu σ pc vm rd v)
  frame := by
    intro R hR
    have h := all_notin (S := rd :: noiseRegs)
      (List.all_eq_true.mpr (fun r hr => by simpa using hR r hr))
    -- `h : ∀ r ∈ rd :: noiseRegs, (r == R) = false`
    have hrd : (rd == R) = false := h _ (List.mem_cons_self ..)
    have hms : (Register.minstret == R) = false := h _ (by simp [noiseRegs])
    have hpc : (Register.PC == R) = false := h _ (by simp [noiseRegs])
    have hnp : (Register.nextPC == R) = false := h _ (by simp [noiseRegs])
    have hmi' : (Register.minstret_increment == R) = false := h _ (by simp [noiseRegs])
    have hmc : (Register.mcycle == R) = false := h _ (by simp [noiseRegs])
    have hmt : (Register.mtime == R) = false := h _ (by simp [noiseRegs])
    have hmip : (Register.mip == R) = false := h _ (by simp [noiseRegs])
    exact (hobs.1 R hmc hmt hmip).trans
      (get?_sigmaPost_alu σ pc vm rd v R hms hpc hrd hnp hmi')

/-- `jal` (linking call) step frame. Written set `rd :: noiseRegs`. -/
theorem of_jal {σ σ' : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd : Register} {link : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd link)) :
    StepFrameOut (rd :: noiseRegs) σ σ' where
  out := (hobs.out).trans (sailOutput_sigmaPost_jal σ pc vm imm rd link)
  frame := by
    intro R hR
    have h := all_notin (S := rd :: noiseRegs)
      (List.all_eq_true.mpr (fun r hr => by simpa using hR r hr))
    have hrd : (rd == R) = false := h _ (List.mem_cons_self ..)
    have hms : (Register.minstret == R) = false := h _ (by simp [noiseRegs])
    have hpc : (Register.PC == R) = false := h _ (by simp [noiseRegs])
    have hnp : (Register.nextPC == R) = false := h _ (by simp [noiseRegs])
    have hmi' : (Register.minstret_increment == R) = false := h _ (by simp [noiseRegs])
    have hmc : (Register.mcycle == R) = false := h _ (by simp [noiseRegs])
    have hmt : (Register.mtime == R) = false := h _ (by simp [noiseRegs])
    have hmip : (Register.mip == R) = false := h _ (by simp [noiseRegs])
    exact (hobs.1 R hmc hmt hmip).trans
      (get?_sigmaPost_jal σ pc vm imm rd link R hms hpc hrd hnp hmi')

/-- `jr`/`j`/`ret` (jump with `rd = x0`) step frame. Written set `noiseRegs`. -/
theorem of_jr {σ σ' : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) :
    StepFrameOut noiseRegs σ σ' where
  out := (hobs.out).trans (sailOutput_sigmaPost_jump_x0 σ pc vm tgt)
  frame := by
    intro R hR
    have h := all_notin (S := noiseRegs)
      (List.all_eq_true.mpr (fun r hr => by simpa using hR r hr))
    have hms : (Register.minstret == R) = false := h _ (by simp [noiseRegs])
    have hpc : (Register.PC == R) = false := h _ (by simp [noiseRegs])
    have hnp : (Register.nextPC == R) = false := h _ (by simp [noiseRegs])
    have hmi' : (Register.minstret_increment == R) = false := h _ (by simp [noiseRegs])
    have hmc : (Register.mcycle == R) = false := h _ (by simp [noiseRegs])
    have hmt : (Register.mtime == R) = false := h _ (by simp [noiseRegs])
    have hmip : (Register.mip == R) = false := h _ (by simp [noiseRegs])
    exact (hobs.1 R hmc hmt hmip).trans
      (get?_sigmaPost_jump_x0 σ pc vm tgt R hms hpc hnp hmi')

/-- Taken-branch step frame. Written set `noiseRegs`. -/
theorem of_branch_taken {σ σ' : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) :
    StepFrameOut noiseRegs σ σ' where
  out := (hobs.out).trans (sailOutput_sigmaPost_branch_taken σ pc vm imm)
  frame := by
    intro R hR
    have h := all_notin (S := noiseRegs)
      (List.all_eq_true.mpr (fun r hr => by simpa using hR r hr))
    have hms : (Register.minstret == R) = false := h _ (by simp [noiseRegs])
    have hpc : (Register.PC == R) = false := h _ (by simp [noiseRegs])
    have hnp : (Register.nextPC == R) = false := h _ (by simp [noiseRegs])
    have hmi' : (Register.minstret_increment == R) = false := h _ (by simp [noiseRegs])
    have hmc : (Register.mcycle == R) = false := h _ (by simp [noiseRegs])
    have hmt : (Register.mtime == R) = false := h _ (by simp [noiseRegs])
    have hmip : (Register.mip == R) = false := h _ (by simp [noiseRegs])
    exact (hobs.1 R hmc hmt hmip).trans
      (get?_sigmaPost_branch_taken σ pc vm imm R hms hpc hnp hmi')

/-- Not-taken-branch step frame. Written set `noiseRegs`. -/
theorem of_branch_nottaken {σ σ' : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    StepFrameOut noiseRegs σ σ' where
  out := (hobs.out).trans (sailOutput_sigmaPost_branch_nottaken σ pc vm)
  frame := by
    intro R hR
    have h := all_notin (S := noiseRegs)
      (List.all_eq_true.mpr (fun r hr => by simpa using hR r hr))
    have hms : (Register.minstret == R) = false := h _ (by simp [noiseRegs])
    have hpc : (Register.PC == R) = false := h _ (by simp [noiseRegs])
    have hnp : (Register.nextPC == R) = false := h _ (by simp [noiseRegs])
    have hmi' : (Register.minstret_increment == R) = false := h _ (by simp [noiseRegs])
    have hmc : (Register.mcycle == R) = false := h _ (by simp [noiseRegs])
    have hmt : (Register.mtime == R) = false := h _ (by simp [noiseRegs])
    have hmip : (Register.mip == R) = false := h _ (by simp [noiseRegs])
    exact (hobs.1 R hmc hmt hmip).trans
      (get?_sigmaPost_branch_nottaken σ pc vm R hms hpc hnp hmi')

/-- STORE step frame. Written set `noiseRegs` (registers only; the `mem := m'`
update is register-transparent, and `sailOutput` is untouched by the store class
— the HTIF console append only fires inside the tohost window the store lemmas
exclude). -/
theorem of_store {σ σ' : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    StepFrameOut noiseRegs σ σ' where
  out := (hobs.out).trans (sailOutput_sigmaPost_store σ pc vm m')
  frame := by
    intro R hR
    have h := all_notin (S := noiseRegs)
      (List.all_eq_true.mpr (fun r hr => by simpa using hR r hr))
    have hms : (Register.minstret == R) = false := h _ (by simp [noiseRegs])
    have hpc : (Register.PC == R) = false := h _ (by simp [noiseRegs])
    have hnp : (Register.nextPC == R) = false := h _ (by simp [noiseRegs])
    have hmi' : (Register.minstret_increment == R) = false := h _ (by simp [noiseRegs])
    have hmc : (Register.mcycle == R) = false := h _ (by simp [noiseRegs])
    have hmt : (Register.mtime == R) = false := h _ (by simp [noiseRegs])
    have hmip : (Register.mip == R) = false := h _ (by simp [noiseRegs])
    exact (hobs.1 R hmc hmt hmip).trans
      (get?_sigmaPost_store σ pc vm m' R hms hpc hnp hmi')

/-- Transport a `get?` value across a step in **one line**, the ergonomic
replacement for `obs_CLASS_other hobs R (by decide)×8 hσ`:
`sfo.get R (by decide) hσ`. -/
theorem get {W : List Register} {σ σ' : MState}
    (sfo : StepFrameOut W σ σ') (R : Register)
    (hR : (W.all fun r => !(r == R)) = true)
    {w : RegisterType R} (hσ : σ.regs.get? R = some w) :
    σ'.regs.get? R = some w :=
  (sfo.frame R (all_notin hR)).trans hσ

end StepFrameOut

/-! ## Demo — a representative multi-step frame+output chain

Three ALU steps followed by one `jal`, composed by `.trans`, reconstructing the
combined register-frame + output-preservation over the whole 4-step run. This is
the ergonomic payoff: each step contributes ONE `.of_CLASS hobs` line and the
run's frame/output fall out of `.trans`, versus ~5-10 hand-threaded lines/step
(a `by decide × 8` register wall + a `sailOutput` rewrite) previously. -/
section Demo

example (σ σ1 σ2 σ3 σ4 : MState)
    (pc1 pc2 pc3 pc4 vm1 vm2 vm3 vm4 : BitVec 64)
    (rd1 rd2 rd3 rdj : Register)
    (v1 : RegisterType rd1) (v2 : RegisterType rd2) (v3 : RegisterType rd3)
    (imm : BitVec 21) (link : RegisterType rdj)
    (h1 : ReadsLikePost σ1 (sigmaPost_alu σ pc1 vm1 rd1 v1))
    (h2 : ReadsLikePost σ2 (sigmaPost_alu σ1 pc2 vm2 rd2 v2))
    (h3 : ReadsLikePost σ3 (sigmaPost_alu σ2 pc3 vm3 rd3 v3))
    (h4 : ReadsLikePost σ4 (sigmaPost_jal σ3 pc4 vm4 imm rdj link)) :
    StepFrameOut
      ((rd1 :: noiseRegs) ++ (rd2 :: noiseRegs) ++ (rd3 :: noiseRegs) ++ (rdj :: noiseRegs))
      σ σ4 :=
  (((StepFrameOut.of_alu h1).trans (StepFrameOut.of_alu h2)).trans
    (StepFrameOut.of_alu h3)).trans (StepFrameOut.of_jal h4)

-- The chain delivers BOTH the output-preservation (`.out`) and any non-written
-- register's transported value (`.get`) over the whole run in one line each.
example (σ σ1 σ2 σ3 σ4 : MState)
    (pc1 pc2 pc3 pc4 vm1 vm2 vm3 vm4 : BitVec 64)
    (v1 : RegisterType Register.x5) (v2 : RegisterType Register.x6)
    (v3 : RegisterType Register.x7)
    (imm : BitVec 21) (link : RegisterType Register.x1)
    (h1 : ReadsLikePost σ1 (sigmaPost_alu σ pc1 vm1 Register.x5 v1))
    (h2 : ReadsLikePost σ2 (sigmaPost_alu σ1 pc2 vm2 Register.x6 v2))
    (h3 : ReadsLikePost σ3 (sigmaPost_alu σ2 pc3 vm3 Register.x7 v3))
    (h4 : ReadsLikePost σ4 (sigmaPost_jal σ3 pc4 vm4 imm Register.x1 link))
    {w : RegisterType Register.x18} (hσ : σ.regs.get? Register.x18 = some w) :
    σ4.sailOutput = σ.sailOutput ∧ σ4.regs.get? Register.x18 = some w := by
  have sfo := (((StepFrameOut.of_alu h1).trans (StepFrameOut.of_alu h2)).trans
    (StepFrameOut.of_alu h3)).trans (StepFrameOut.of_jal h4)
  exact ⟨sfo.out, sfo.get Register.x18 (by decide) hσ⟩

end Demo

#print axioms StepFrameOut.trans
#print axioms StepFrameOut.of_alu
#print axioms StepFrameOut.of_jr
#print axioms StepFrameOut.get

end Vsa.Sim
