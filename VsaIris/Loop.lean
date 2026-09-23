import VsaIris.MachWP

/-!
# The bounded-loop rule (work package F3)

INTERP_DESIGN.md §1 ("Helper loops are proved by **fuel induction, not Löb**")
and §4.3. MachCSL proves a bounded loop by induction on the remaining
iteration count, never by `iLöb`: xv6iris `ProofMemset.v:1-9` ("bounded loop,
not iLöb") and `ProofMemmove.v:350` `mm_loop` (induction on `rem`). Fuel
induction is sound for BOTH `MachWP` instances, so `strlen`, `memcpy`,
`strcmp`, the `args[32]` fill and the interpreter's statement-sequence loops
share one rule.

Two shapes:

* `MachWP.loop` — the general rule. The invariant `I k` holds with `k`
  iterations left; the body proves the rest of the run from an ADDITIVE PAIR
  of continuations, the next iteration's `I k` and the loop's inherited exit
  `K`. The pair is what keeps `K` alive across iterations: with a plain `∗`
  the body would consume `K` and the second iteration would have none
  (INTERP_DESIGN.md §10.1, xv6iris `durable-notes.md` "Contracts and
  resources"). The loop body may do anything an Iris proof can do, including
  call `exec_stmt` under a Löb hypothesis.
* `MachWP.loopSeg` — the body is ONE reflected segment (`RunFact`, the shape
  `Inst.seg_runFact` produces from `segEval_sound`). The client supplies the
  invariant's opener and closer around the segment's footprint; the frame
  `F k` crosses the segment untouched.

Neither rule mentions `lat`, so neither costs a later: the loop is bounded and
the recursion that needs Löb is elsewhere (the three recursive entry points).
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

namespace MachWP

variable (Wp : MachWP (GF := GF) M)

/-- **The bounded-loop rule**, for either WP (xv6iris `ProofMemset.v:1-9`,
`ProofMemmove.v:350` `mm_loop`: induction on the remaining count).

`I k` is the loop invariant with `k` iterations still to run and `K` is the
resource the loop's exit continuation consumes — for a partial-mode loop, the
abort resource the caller inherited (`fnSpecAbort`'s second branch).

The body's two continuations are an ADDITIVE pair: the body proves the rest of
the run either by starting the next iteration (`I k`) or by leaving the loop
(`K`), and BOTH are proved from its one context, so `K` survives every
iteration. `fin` closes the loop when the fuel runs out. -/
theorem loop {Φ : Nat × String → IProp GF} (I : Nat → IProp GF) (K : IProp GF)
    (body : ∀ k, I (k + 1) ∗ ((I k -∗ Wp.W Φ) ∧ (K -∗ Wp.W Φ)) ⊢ Wp.W Φ)
    (fin : I 0 ∗ (K -∗ Wp.W Φ) ⊢ Wp.W Φ) :
    ∀ n, I n ∗ (K -∗ Wp.W Φ) ⊢ Wp.W Φ
  | 0 => fin
  | n + 1 =>
    .trans (sep_mono_right (and_intro (wand_intro_left (loop I K body fin n)) .rfl)) (body n)

/-- The bounded-loop rule with no separate exit resource: the loop is left
through its own invariant at fuel `0`. -/
theorem loopI {Φ : Nat × String → IProp GF} (I : Nat → IProp GF)
    (body : ∀ k, I (k + 1) ∗ (I k -∗ Wp.W Φ) ⊢ Wp.W Φ) :
    ∀ n, I n ∗ (I 0 -∗ Wp.W Φ) ⊢ Wp.W Φ :=
  Wp.loop I (I 0) (fun k => .trans (sep_mono_right and_elim_l) (body k)) (by
    iintro ⟨Hi, Hk⟩
    iapply Hk $$ Hi)

/-- **The bounded-loop rule over a reflected segment**, for either WP: one
iteration is one `RunFact` run (`Inst.seg_runFact`). `hopen` hands the
segment its footprint out of the invariant at `k + 1` and keeps the rest as a
frame `F k`; `hclose` rebuilds the invariant at `k` from the committed
footprint and that frame. This is the rule `strlen`, `memcpy` and `strcmp`
use (H3). -/
theorem loopSeg {Φ : Nat × String → IProp GF} (I : Nat → IProp GF) (K : IProp GF)
    (F : Nat → IProp GF) (n : Nat → Nat)
    (RR : Nat → List (Nat × DFrac × BitVec 64)) (MR : Nat → List (Nat × DFrac × BitVec 8))
    (RW : Nat → List (Nat × BitVec 64 × BitVec 64)) (MW : Nat → List (Nat × BitVec 8 × BitVec 8))
    (hseg : ∀ k, RunFact M (n k) (RR k) (MR k) (RW k) (MW k))
    (hopen : ∀ k, I (k + 1) ⊢ footPre (RR k) (MR k) (RW k) (MW k) ∗ F k)
    (hclose : ∀ k, footPost (RR k) (MR k) (RW k) (MW k) ∗ F k ⊢ I k)
    (fin : I 0 ∗ (K -∗ Wp.W Φ) ⊢ Wp.W Φ) :
    ∀ m, I m ∗ (K -∗ Wp.W Φ) ⊢ Wp.W Φ := by
  refine Wp.loop I K (fun k => ?_) fin
  iintro ⟨Hi, Hk⟩
  ihave Hk := and_elim_l $$ Hk
  ihave ⟨Hf, HF⟩ := hopen k $$ Hi
  iapply Wp.run (n k) (RR k) (MR k) (RW k) (MW k) (hseg k)
  iframe Hf
  iintro Hf
  iapply Hk
  iapply hclose k $$ [Hf HF]
  iframe Hf HF

end MachWP

/-- **The bounded-loop rule** for the total WP. -/
theorem wp_loop {Φ : Nat × String → IProp GF} (I : Nat → IProp GF) (K : IProp GF)
    (body : ∀ k, I (k + 1) ∗ ((I k -∗ mTWP M Φ) ∧ (K -∗ mTWP M Φ)) ⊢ mTWP M Φ)
    (fin : I 0 ∗ (K -∗ mTWP M Φ) ⊢ mTWP M Φ) :
    ∀ n, I n ∗ (K -∗ mTWP M Φ) ⊢ mTWP M Φ :=
  (twpW M).loop I K body fin

/-- **The bounded-loop rule** for the partial WP. It needs no later: the loop
is bounded, and Löb is spent only on the recursive entry points. -/
theorem wpP_loop {Φ : Nat × String → IProp GF} (I : Nat → IProp GF) (K : IProp GF)
    (body : ∀ k, I (k + 1) ∗ ((I k -∗ mWP M Φ) ∧ (K -∗ mWP M Φ)) ⊢ mWP M Φ)
    (fin : I 0 ∗ (K -∗ mWP M Φ) ⊢ mWP M Φ) :
    ∀ n, I n ∗ (K -∗ mWP M Φ) ⊢ mWP M Φ :=
  (wpW M).loop I K body fin

end

end VsaIris
