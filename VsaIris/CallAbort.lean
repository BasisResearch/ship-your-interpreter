import VsaIris.Call

/-!
# Function specifications with an abort branch (work package F3)

INTERP_DESIGN.md §1 ("The mode-generic function spec"), §4.2 and §10.1.

The partial (`stuck_sim`) specs of `eval_expr` and `exec_stmt` have TWO exits:
the function returns with a derivation, or the run aborts — a runtime error
(`runtime_error` → `snprintf` → `longjmp` to `interp_run`'s `setjmp` landing)
or an out-of-memory `exit(1)`. Exactly one fires, and which one is not known
to the caller, so the two continuations are an **additive** pair `∧`, not a
separating one (xv6iris `durable-notes.md`, "Contracts and resources"). Both
branches are proved from the caller's ONE context, so the caller's frame —
and the abort continuation it inherited from ITS caller — serves both.

The first draft put the abort continuation in the precondition as a plain
wand; the return branch then consumed it and a loop's second iteration had
none (INTERP_DESIGN.md §10.1). The `∧` is the fix, and it is the same shape
`MachWP.loop` (`Loop.lean`) carries across iterations.

Everything here is mode-generic (`∀ Wp : MachWP M`), so the total specs may
use it too: `fnSpecAbort_of_fnSpecW` says a function that always returns meets
an abort spec with any abort resource.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- **A function that returns OR aborts.** `P`/`Q` are the ordinary pre- and
postcondition of `fnSpecW`, indexed by the return address; `A` is what an
abort hands the continuation (for `eval_expr`/`exec_stmt`: `abortRes`, the
landing registers, some world, and the whole owned stack below the site's
`sp`). The caller proves the rest of the run from BOTH exits out of one
context (`∧`). Persistent, like `fnSpecW`. -/
def fnSpecAbort (Wp : MachWP (GF := GF) M) (entry : BitVec 64)
    (P Q : BitVec 64 → IProp GF) (A : IProp GF) : IProp GF :=
  iprop(□ ∀ (r : BitVec 64) (Φ : Nat × String → IProp GF),
    PC ↦ᵣ entry -∗ ra ↦ᵣ r -∗ P r -∗
      ((PC ↦ᵣ r -∗ ra ↦ᵣ r -∗ Q r -∗ Wp.W Φ) ∧ (A -∗ Wp.W Φ)) -∗ Wp.W Φ)

instance (Wp : MachWP (GF := GF) M) (entry : BitVec 64) (P Q : BitVec 64 → IProp GF)
    (A : IProp GF) : Persistent (fnSpecAbort Wp entry P Q A) := by
  unfold fnSpecAbort; infer_instance

/-- **Call a function that may abort**, for either WP: a `jal ra, entry` at
`i` into a function meeting `fnSpecAbort`. The caller hands over the
precondition and, from its one context, the additive pair of continuations.
Whatever else it owns is framed by both branches (paper §4.6). -/
theorem wp_callAbort (Wp : MachWP (GF := GF) M) {Φ : Nat × String → IProp GF} {i : Nat}
    {code : List (BitVec 8)} {entry v : BitVec 64} {P Q : BitVec 64 → IProp GF}
    {A : IProp GF} (hexec : JalExec M i code entry) :
    instrAt (GF := GF) i code ∗ fnSpecAbort Wp entry P Q A ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗
      ra ↦ᵣ v ∗ P (BitVec.ofNat 64 (i + 4)) ∗
      ((PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗
          Q (BitVec.ofNat 64 (i + 4)) -∗ Wp.W Φ) ∧ (A -∗ Wp.W Φ))
    ⊢ Wp.W Φ := by
  unfold fnSpecAbort
  iintro ⟨#Hi, #Hspec, Hpc, Hra, HP, Hk⟩
  iapply wp_jalW Wp hexec
  iframe Hi Hpc Hra
  iintro Hpc Hra
  iapply Wp.lat_intro
  iapply Hspec $$ %(BitVec.ofNat 64 (i + 4)) %Φ Hpc Hra HP Hk

/-- **Call under a later** (partial mode): the recursive `jal` of the Löb
proof of `evalSpecP_body ∧ execSpecP_body`. The callee's abort spec is only
available later (the Löb hypothesis) and the `jal` step pays for it — the
`fnSpecAbort` twin of `wp_call_later`. -/
theorem wp_callAbort_later {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    {entry v : BitVec 64} {P Q : BitVec 64 → IProp GF} {A : IProp GF}
    (hexec : JalExec M i code entry) :
    instrAt (GF := GF) i code ∗ ▷ fnSpecAbort (wpW M) entry P Q A ∗
      PC ↦ᵣ BitVec.ofNat 64 i ∗ ra ↦ᵣ v ∗ P (BitVec.ofNat 64 (i + 4)) ∗
      ((PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗
          Q (BitVec.ofNat 64 (i + 4)) -∗ mWP M Φ) ∧ (A -∗ mWP M Φ))
    ⊢ mWP M Φ := by
  unfold fnSpecAbort
  refine .trans ?_ (wp_jalW (wpW M) (Φ := Φ) (v := v) hexec)
  iintro ⟨#Hi, Hspec, Hpc, Hra, HP, Hk⟩
  iframe Hi Hpc Hra
  iintro Hpc Hra
  simp only [wpW_lat, wpW_W]
  inext
  iapply Hspec $$ %(BitVec.ofNat 64 (i + 4)) %Φ Hpc Hra HP Hk

end

end VsaIris
