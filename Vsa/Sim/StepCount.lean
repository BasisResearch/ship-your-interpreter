import Vsa.Sim.DeriveCaseRow

/-!
# `StepCount` — counted machine-step LOWER BOUNDS for every seg row, for free

This is the step-counting exponentiating layer.  ONE metatheorem
(`segToTripleN`) upgrades EVERY existing and future `#derive_case` seg row to a
counted triple `TripleN (evalBlocksFuel bs) …`, whose count is the concrete
instruction length of the reflected block list.  The divergence-family seams in
`Vsa/Sim/InterpRunLoopSeamsClose.lean` (`iterFromCountedRun` /
`approxFromCountedRun`) consume exactly this `TripleN` shape, so any row is now a
positive machine-step lower bound with NO extra proof.

## What was already in place (reused, not rebuilt)

* `Vsa/Triple.lean` already has the full `TripleN` algebra: `TripleN.toTriple`,
  `of_triple`, `mono` (weaken the count), `of_step`, `conseq`, `seq` (counts ADD
  across seams).  Task parts 2 (counted composition + `TripleN.weaken`) are
  therefore ALREADY LANDED there — `TripleN.mono` IS the weaken lemma, and
  `TripleN.seq` IS the counted `Triple.seq`.  This file does not restate them; it
  points a future agent at them and only supplies the missing seg-count bridge.
* `Vsa/Sim/DeriveCaseRow.lean`'s `segToTriple` builds the row's `Steps` chain via
  `segEval_sound`, whose conclusion pins the reached config's `steps` counter to
  `u + evalBlocksFuel bs`.  That counter IS the length: every `Step` increments
  `steps` by exactly 1 (the `.inr` branch of `stepOnce` returns `used + 1`, both
  cases — see `Vsa/Elf.lean:47`), so a `Steps` run whose `steps` advances by `k`
  has exactly `k` links.  `Steps.toN_of_stepsField` below turns that field-delta
  into a `StepsN k`, and `segToTripleN` folds it into the flagship metatheorem.

## The recipe (how a future agent counts an existing row)

Given ANY row `myRow : Triple (SegPre bs L lds pc0 m0) Q` built by `segToTriple`:
you do NOT need to touch `myRow`.  Either
  (a) re-derive the counted form directly: `segToTripleN bs L lds pc0 m0 Q hwf
      hpost : TripleN (evalBlocksFuel bs) (SegPre bs L lds pc0 m0) Q` — same
      `hwf`/`hpost` the plain row supplied; or
  (b) if you only have the plain `Triple` and want a crude positive bound, note
      `evalBlocksFuel bs = chainLen bs > 0` for any non-empty chain, and feed the
      counted row through `TripleN.mono` down to whatever bound (e.g. `1`, or
      `n + 1`) the consumer wants.  `iterFromCountedRun` wants `TripleN 1`;
      `approxFromCountedRun` wants `TripleN (n + 1)` — both reachable by
      `TripleN.mono` from `TripleN (evalBlocksFuel bs)` once `1 ≤ evalBlocksFuel
      bs` / `n + 1 ≤ evalBlocksFuel bs` is a `decide`.

## `Landed` combinator (task part 3)

`Landed c P := ∃ c', Steps c c' ∧ P c'` — the canonical "seam landing" bundle
from the `landing-bundle-must-be-prop-existential` observation.  It carries the
reached config as DATA yet is Prop-valued (built from a `Triple`'s `Exists`,
consumed by `obtain` into Prop goals — the only shape that survives, per the
observation).  `Landed.mk`/`bind`/`weaken` + the counted `LandedN` give the
shared destructurer `SpillLanded`/`SegLanded` (DriveToLoopHeadSpans) can migrate
onto.  Reseat is not done here — the combinator is landed for future files.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic (Triple TripleN)

namespace Vsa.Machine

/-! ## §1. `Step` advances the `steps` counter by exactly 1

Every architectural step returns `used + 1` on its continue branch
(`stepOnce`, `Vsa/Elf.lean`).  So the `steps` field of a `Config` counts the
links of any `Steps` run out of it, and a run whose `steps` field advances by `k`
is a `StepsN k`. -/

/-- One `Step` increments the `steps` counter by exactly one. -/
theorem Step.steps_succ {a b : Config} (h : Step a b) : b.steps = a.steps + 1 := by
  cases h with
  | @mk σ σ' i i' u u' e =>
    -- `Step.mk : (stepOnce i u).run σ = .ok (.inr (i', u')) σ' → Step ⟨σ,i,u⟩ ⟨σ',i',u'⟩`.
    -- The `.inr` continue branch of `stepOnce` returns `(_, u + 1)`, so `u' = u + 1`.
    show u' = u + 1
    -- Reduce the `EStateM` run of `stepOnce`'s bind tree to a nest of `match`/`if`
    -- over the opaque effect results (`readReg`/`try_step`/`cycle_count`/…), each of
    -- whose leaves returns `.inl (…, u)` or `.inr (_, u + 1)`.  Only the `.inr`
    -- leaves unify with `e`'s RHS `.inr (i', u')`, and every one carries `u + 1`;
    -- the `.inl` leaves inject to `False`.
    unfold stepOnce at e
    repeat' first
      | -- `.inr` leaf: injection to the payload pair, count is `u + 1`.
        (simp only [EStateM.Result.ok.injEq, Sum.inr.injEq, Prod.mk.injEq,
           reduceCtorEq, false_and] at e
         omega)
      | -- `.inl` leaf: `.inl _ = .inr _` is `False`; simp closes the goal.
        simp only [EStateM.Result.ok.injEq, reduceCtorEq, false_and] at e
      | -- peel one `EStateM.bind`/`.run`/`pure` layer …
        simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
          Bind.bind, Pure.pure] at e
      | -- … then split the exposed effect-result `match` / guard `if`.
        split at e

/-- The `steps` counter is monotone along a run. -/
theorem Steps.steps_le {a b : Config} (hs : Steps a b) : a.steps ≤ b.steps := by
  induction hs with
  | refl c => exact Nat.le_refl _
  | head s _ ih =>
    have := s.steps_succ
    omega

/-- A finite run whose `steps` field advances by `k` is a `StepsN k` run. -/
theorem Steps.toN_of_stepsField {a b : Config} (hs : Steps a b) :
    StepsN (b.steps - a.steps) a b := by
  induction hs with
  | refl c => simpa using StepsN.zero c
  | @head a b c s hbc ih =>
    have hstep : b.steps = a.steps + 1 := s.steps_succ
    have hle : b.steps ≤ c.steps := hbc.steps_le
    -- `c.steps ≥ b.steps = a.steps + 1`, so `c.steps - a.steps = (c.steps - b.steps) + 1`.
    have hrw : c.steps - a.steps = (c.steps - b.steps) + 1 := by omega
    rw [hrw]
    exact StepsN.succ s ih

/-- Convenience: a run pinned to end at `steps = a.steps + k` is a `StepsN k`. -/
theorem Steps.toN_of_stepsEq {a b : Config} {k : Nat}
    (hs : Steps a b) (hk : b.steps = a.steps + k) : StepsN k a b := by
  have := hs.toN_of_stepsField
  rw [hk] at this
  simpa using this

#print axioms Step.steps_succ
#print axioms Steps.steps_le
#print axioms Steps.toN_of_stepsField
#print axioms Steps.toN_of_stepsEq

end Vsa.Machine

namespace Vsa.Sim

open Vsa.Machine

/-! ## §2. `segToTripleN` — the flagship counted seg metatheorem

`segEval_sound` produces `Steps ⟨σ,i,u⟩ ⟨σ', i', u + evalBlocksFuel bs⟩`.  The
end `steps` counter is `u + evalBlocksFuel bs`, so `Steps.toN_of_stepsEq` gives a
`StepsN (evalBlocksFuel bs)` run — exactly the counted-triple witness.  This is
the counted twin of `segToTriple`: identical `hwf`/`hpost`, upgraded conclusion
`TripleN (evalBlocksFuel bs) (SegPre …) Q`. -/

/-- **Counted seg→`TripleN` metatheorem.**  From the same `SegPre`, kernel
`decide` `hwf`, and outcome-post `hpost` a plain `segToTriple` row supplies, the
seg run counts `evalBlocksFuel bs` machine steps.  Every `#derive_case` seg row
becomes a machine-step LOWER BOUND `TripleN (instruction count) …` for free:
apply this with the row's OWN `hwf`/`hpost`, no re-proof.  Compose down with
`TripleN.mono` to any smaller bound a consumer wants. -/
theorem segToTripleN (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (Q : Config → Prop)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hpost : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log →
      σ'.regs.get? Register.PC
        = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      GHolds σ' (evalBlocks bs (SegEvalState.init L lds)).regs →
      Q ⟨σ', i', u'⟩) :
    TripleN (evalBlocksFuel bs) (SegPre bs L lds pc0 m0) Q := by
  intro c hpre
  obtain ⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, htick⟩ := hpre
  obtain ⟨σ', i', hs, hi', hG', hmem', hout, hpc', hmi', hregs, _hframe⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf htick
  rw [hmem] at hmem'
  refine ⟨evalBlocksFuel bs, ⟨σ', i', c.steps + evalBlocksFuel bs⟩, Nat.le_refl _, ?_, ?_⟩
  · -- The `Steps` chain from `segEval_sound` ends at `steps = c.steps + evalBlocksFuel bs`;
    -- `toN_of_stepsEq` reads the count off the `steps` field.
    exact hs.toN_of_stepsEq (by simp)
  · exact hpost σ' i' (c.steps + evalBlocksFuel bs) hG' hi' hmem' hpc' hmi' hregs

#print axioms segToTripleN

/-! ## §3. Positive-lower-bound corollaries for the divergence seams

`iterFromCountedRun` wants `TripleN 1`; `approxFromCountedRun` wants `TripleN
(n + 1)`.  Both come from `segToTripleN` via `TripleN.mono` once the fuel bound
is a `decide`.  These two corollaries package the arithmetic so a seam supplier
hands only the fuel-bound `decide` (usually `by decide` on a concrete `bs`). -/

/-- A seg row with `≥ 1` instruction is a `TripleN 1` — the `iterFromCountedRun`
input shape.  Supply `hfuel : 1 ≤ evalBlocksFuel bs` (a `decide` on concrete
`bs`). -/
theorem segToTripleN_one (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (Q : Config → Prop)
    (hfuel : 1 ≤ evalBlocksFuel bs)
    (hT : TripleN (evalBlocksFuel bs) (SegPre bs L lds pc0 m0) Q) :
    TripleN 1 (SegPre bs L lds pc0 m0) Q :=
  TripleN.mono hfuel hT

/-- A seg row with `≥ n+1` instructions is a `TripleN (n+1)` — the
`approxFromCountedRun` input shape.  Supply `hfuel : n + 1 ≤ evalBlocksFuel
bs`. -/
theorem segToTripleN_succ (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (Q : Config → Prop)
    (n : Nat) (hfuel : n + 1 ≤ evalBlocksFuel bs)
    (hT : TripleN (evalBlocksFuel bs) (SegPre bs L lds pc0 m0) Q) :
    TripleN (n + 1) (SegPre bs L lds pc0 m0) Q :=
  TripleN.mono hfuel hT

#print axioms segToTripleN_one
#print axioms segToTripleN_succ

/-! ## §4. The `Landed` combinator (task part 3)

`Landed c P` = "from `c`, some finite run reaches a `P`-config".  Prop-valued but
DATA-carrying (the reached config lives under the `∃`), the only shape that both
builds from a `Triple`'s `Exists` and consumes into a Prop goal
(`landing-bundle-must-be-prop-existential`).  `LandedN n` additionally records a
`≥ n` step count.  `SpillLanded`/`SegLanded` in `DriveToLoopHeadSpans.lean` are
instances of `Landed` (their `∃ c', Steps c c' ∧ …`), and can migrate onto these
shared `mk`/`bind`/`weaken` lemmas. -/

/-- **The landing combinator.**  From `c`, a finite run reaches a config
satisfying `P`.  Carries the reached config as data under the existential; a
`Triple`'s result IS `Landed` at its pre-config (`Triple.landed`). -/
def Landed (c : Config) (P : Config → Prop) : Prop :=
  ∃ c', Steps c c' ∧ P c'

/-- **Counted landing.**  A landing that took at least `n` machine steps. -/
def LandedN (n : Nat) (c : Config) (P : Config → Prop) : Prop :=
  ∃ (m : Nat) (c' : Config), n ≤ m ∧ StepsN m c c' ∧ P c'

namespace Landed

/-- **`mk`** — a reached config with its run and post IS a `Landed`. -/
theorem mk {c c' : Config} {P : Config → Prop} (hs : Steps c c') (hp : P c') :
    Landed c P :=
  ⟨c', hs, hp⟩

/-- **Zero-step landing** — a config already satisfying `P` has landed. -/
theorem refl {c : Config} {P : Config → Prop} (hp : P c) : Landed c P :=
  ⟨c, .refl c, hp⟩

/-- **`weaken`** — a landing under a stronger post weakens to a weaker one. -/
theorem weaken {c : Config} {P Q : Config → Prop} (h : Landed c P)
    (hPQ : ∀ c', P c' → Q c') : Landed c Q := by
  obtain ⟨c', hs, hp⟩ := h
  exact ⟨c', hs, hPQ c' hp⟩

/-- **`bind`** — land at a `P`-config, then continue landing from there; the
runs compose by `Steps.trans`.  This is how a call splice / row seam chains two
landings into one. -/
theorem bind {c : Config} {P Q : Config → Prop} (h : Landed c P)
    (k : ∀ c', P c' → Landed c' Q) : Landed c Q := by
  obtain ⟨c', hs, hp⟩ := h
  obtain ⟨c'', hs', hq⟩ := k c' hp
  exact ⟨c'', hs.trans hs', hq⟩

/-- **The `Triple` ⇒ `Landed` bridge.**  `Triple P Q` says every `P`-config
lands at a `Q`-config; so at any `P`-config `c`, `Landed c Q`.  Marshalling a row
result into a landing is `id` (the observation's goal: "the `Triple` result IS
`Landed` at the pre-config"). -/
theorem of_triple {P Q : Config → Prop} (h : Triple P Q) {c : Config} (hc : P c) :
    Landed c Q :=
  h c hc

end Landed

namespace LandedN

/-- **`mk`** — a counted run reaching a `P`-config is a counted landing. -/
theorem mk {n : Nat} {c c' : Config} {P : Config → Prop}
    (hm : n ≤ m) (hs : StepsN m c c') (hp : P c') : LandedN n c P :=
  ⟨m, c', hm, hs, hp⟩

/-- **Forget the count** — a counted landing is a landing. -/
theorem toLanded {n : Nat} {c : Config} {P : Config → Prop} (h : LandedN n c P) :
    Landed c P := by
  obtain ⟨m, c', _, hs, hp⟩ := h
  exact ⟨c', hs.toSteps, hp⟩

/-- **`weakenCount`** — lower the recorded step bound. -/
theorem weakenCount {m n : Nat} {c : Config} {P : Config → Prop} (hmn : m ≤ n)
    (h : LandedN n c P) : LandedN m c P := by
  obtain ⟨k, c', hk, hs, hp⟩ := h
  exact ⟨k, c', Nat.le_trans hmn hk, hs, hp⟩

/-- **`weaken`** — weaken the post. -/
theorem weaken {n : Nat} {c : Config} {P Q : Config → Prop} (h : LandedN n c P)
    (hPQ : ∀ c', P c' → Q c') : LandedN n c Q := by
  obtain ⟨m, c', hm, hs, hp⟩ := h
  exact ⟨m, c', hm, hs, hPQ c' hp⟩

/-- **`bind`** — counted landings compose, adding step counts
(`StepsN.trans_add`). -/
theorem bind {m n : Nat} {c : Config} {P Q : Config → Prop} (h : LandedN m c P)
    (k : ∀ c', P c' → LandedN n c' Q) : LandedN (m + n) c Q := by
  obtain ⟨m₁, c', hm₁, hs, hp⟩ := h
  obtain ⟨m₂, c'', hm₂, hs', hq⟩ := k c' hp
  exact ⟨m₁ + m₂, c'', Nat.add_le_add hm₁ hm₂, hs.trans_add hs', hq⟩

/-- **The `TripleN` ⇒ `LandedN` bridge.**  A counted triple lands `≥ n` steps at
any pre-config. -/
theorem of_tripleN {n : Nat} {P Q : Config → Prop} (h : TripleN n P Q)
    {c : Config} (hc : P c) : LandedN n c Q :=
  h c hc

end LandedN

#print axioms Landed.bind
#print axioms Landed.of_triple
#print axioms LandedN.bind
#print axioms LandedN.of_tripleN

/-! ## §5. Demonstration on a real seg row (task part 4)

`demoChainRow` (`DeriveCaseRow.lean`) is `Triple (SegPre demoChain [] [] … m0)
(DemoPost m0)`, a three-`addi` chain.  We reproduce it as a COUNTED triple
`TripleN (evalBlocksFuel demoChain) …` through `segToTripleN` with the SAME
`hwf`/`hpost` the plain row used — proving the counted fan-out is mechanical.
`evalBlocksFuel demoChain` reduces to the concrete instruction count (3), so the
row is a `≥ 3` machine-step lower bound; the `_one`/`_succ` corollaries then drop
it to `TripleN 1` for `iterFromCountedRun` by one `decide`. -/

/-- **Counted demo row.**  Same statement as `demoChainRow` but counted: the
three-`addi` chain lands in `≥ evalBlocksFuel demoChain` machine steps.  Built by
`segToTripleN` with the plain row's `hwf`/`hpost` verbatim — the recipe in
action. -/
theorem demoChainRowN (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    TripleN (evalBlocksFuel demoChain) (SegPre demoChain [] [] 0x80000000#64 m0)
      (DemoPost m0) := by
  apply segToTripleN demoChain [] [] 0x80000000#64 m0 (DemoPost m0) (by decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', ?_, ?_, ?_⟩
  · rw [hmem']; rfl
  · rw [hpc']; rfl
  · exact gholds_lookup (v := 3#64) _ hregs (by decide)

/-- The demo chain has `≥ 1` instruction, so it lands at least one machine step —
the `iterFromCountedRun` input shape, reached by one `decide` on the fuel. -/
theorem demoChainRow_one (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    TripleN 1 (SegPre demoChain [] [] 0x80000000#64 m0) (DemoPost m0) :=
  segToTripleN_one demoChain [] [] 0x80000000#64 m0 (DemoPost m0) (by decide)
    (demoChainRowN m0)

#print axioms demoChainRowN
#print axioms demoChainRow_one

end Vsa.Sim
