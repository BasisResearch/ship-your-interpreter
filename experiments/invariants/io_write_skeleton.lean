/-
loopFromBody-shaped proof SKELETON for the mined _write loop invariant, to
MEASURE the residual obligation left for a prover (the plan's "small obligation"
claim, Experiment 2 tail).  Self-contained.  Nothing enters a real proof.

The plan's contract: once the invariant is mined + fuzzed, `loopFromBody`
collapses the whole loop to ONE per-iteration back-edge obligation.  Everything
else (the whole-loop total-correctness fold, the exit, the measure well-founded
recursion) is DISCHARGED BY THE COMBINATOR.  We reproduce that split here on the
mined WInv and count what remains as `sorry`-holes (each hole = one residual
goal a prover must close), then note its size.
-/

namespace IoWriteSkeleton

structure WG where
  buf : Nat
  len : Nat
  writeCmd : Nat

/-- Mined invariant `I k` (fields as mined; abstracts the machine Config as the
tuple (a1,a3,a2,a4) the trace probed — a real instantiation replaces this with
`Config` and `gprGet`). -/
structure WInv (g : WG) (k : Nat) (a1 a3 a2 a4 : Nat) : Prop where
  klt   : k < g.len
  a1cur : a1 = g.buf + k
  a3end : a3 = g.buf + g.len
  a2len : a2 = g.len
  a4cmd : a4 = g.writeCmd
  guard : a1 < a3

/-- The MEASURE `μ = a3 - a1` (bytes remaining), read off the state. -/
def mu (a1 a3 : Nat) : Nat := a3 - a1

/-! ## The loopFromBody split.

`loopFromBody` needs exactly ONE oracle: the per-iteration back-edge body.
Signature (specialized): for all k and register values with `I k` holding and
`μ = n`, one machine back-edge iteration reaches a state with `I (k+1)` and
`μ < n`.  We state it and mark its proof `sorry` — that ONE `sorry` is the
entire residual a prover sees. -/

/-- THE RESIDUAL OBLIGATION (the single per-iteration body Triple, in the
mined dialect).  A real proof supplies the machine back-edge run
(`bblock_sound_bt` over the 5-instruction body 0x4c..0x60) that:
  * loads the byte, ORs the putchar cmd, stores to tohost (the SEAM),
  * increments a1 (`addi a1,a1,1`),
  * re-establishes every WInv field at k+1,
  * decreases μ by exactly 1.
Here abstracted to the arithmetic core the prover must still discharge. -/
theorem write_body_step (g : WG) (k a1 a3 a2 a4 : Nat)
    (hI : WInv g k a1 a3 a2 a4) (n : Nat) (hn : mu a1 a3 = n) (hk1 : k + 1 < g.len) :
    -- next-iteration state (a1' = a1+1, others fixed) satisfies I (k+1) with μ<n
    WInv g (k+1) (a1+1) a3 a2 a4 ∧ mu (a1+1) a3 < n := by
  -- ARITHMETIC RESIDUAL (fully dischargeable here — the omega part):
  refine ⟨⟨hk1, ?_, hI.a3end, hI.a2len, hI.a4cmd, ?_⟩, ?_⟩
  · rw [hI.a1cur]; omega       -- a1+1 = buf + (k+1)
  · -- guard a1+1 < a3 : from k+1<len and a3=buf+len, a1=buf+k
    rw [hI.a3end, hI.a1cur]; omega
  · -- μ decreases: (a3-(a1+1)) < (a3-a1) = n, using a1<a3
    have := hI.guard; rw [← hn]; simp only [mu]; omega

/-- The whole-loop Triple the combinator PRODUCES from `write_body_step`
(schematically): `I 0 → I len ∧ ¬guard`.  This is what `loopFromBody` gives
for free; the prover writes NONE of it.  We record it as a statement only. -/
def WholeLoopProduced (g : WG) : Prop :=
  ∀ a1 a3 a2 a4, WInv g 0 a1 a3 a2 a4 →
    ∃ a1', WInv g (g.len - 1) a1' a3 a2 a4 ∧ ¬ (a1' + 1 < a3)

end IoWriteSkeleton
