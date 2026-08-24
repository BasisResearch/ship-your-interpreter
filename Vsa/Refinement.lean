import Vsa.MemRepr
import Vsa.While.Semantics

/-!
# ∀-program refinement: machine behavior vs big-step semantics

CompCert-style behavioral correspondence between

* the **machine**: the interpreter binary running under the RISC-V ISA
  presented as an inductive transition relation (`Vsa.Machine.Step`), with
  observable behaviors `Halts`/`Diverges`, and
* the **specification**: the purely inductive big-step semantics `BigStep`,

universally quantified over deep-embedded WHILE programs, connected through
the inductive memory-representation relation (`Vsa.MemRepr.ProgramRepr`).

The correspondence is packaged the way CompCert does it:

* `InterpSim` states **forward simulation**: every defined source behavior
  is produced by the machine, and undefined programs never halt cleanly.
  These obligations quantify over all programs and are exactly
  "the compiled interpreter is correct" — discharging them means verifying
  the binary's code against the ISA relation, rule by rule.
* From forward simulation, the **backward** direction (whatever the machine
  does was specified) is *derived* here, by machine determinism
  (`Halts.deterministic`, `Diverges.not_halts`) and classical case analysis
  — the same composition CompCert uses to turn forward simulation plus
  target determinism into full behavioral equivalence.

No execution, no `native_decide`: every proof in this file is by induction
over the inductive relations.
-/

namespace Vsa.Refine

open Vsa.Machine Vsa.MemRepr Vsa.While

/-- Observable behaviors (CompCert's `program_behavior`, specialized: the
HTIF console string is the whole observable trace, exit code included). -/
inductive Behavior where
  | terminates (out : String) (exit : Nat)
  | diverges
  deriving Repr, DecidableEq

/-- Machine behaviors, over the inductive ISA relation. -/
def MachBehaves (c : Config) : Behavior → Prop
  | .terminates out e => Halts c out e
  | .diverges => Diverges c

/-- Program-point facts about the fixed interpreter binary: what it means
for a configuration to be at `interp_run`'s entry with an AST-array
argument. Determined by the binary's layout (symbol addresses, ABI); kept
abstract here — the refinement theorem holds for any instantiation. -/
structure Layout where
  atInterpRun : Config → Nat → Nat → Prop

/-- **The program is loaded**: the machine configuration is at the
interpreter phase, and memory holds the C AST representation of `p`
(the inductive `ProgramRepr` relation ties the deep embedding to bytes). -/
def Loaded (L : Layout) (p : Program) (c : Config) : Prop :=
  ∃ a n, ProgramRepr c.σ.mem a n p ∧ L.atInterpRun c a n

/-- **Forward simulation obligations** (interpreter correctness), ∀
programs:

* `term_sim` — a derivable big-step behavior is realized by the machine:
  it halts cleanly with exactly the specified output;
* `stuck_sim` — a program with no big-step derivation (runtime error or
  divergence) never halts cleanly: the machine diverges or exits nonzero
  (the interpreter prints a diagnostic and exits 70; a clean exit 0 is
  impossible).

Each is proved (in principle) by induction on the big-step derivation
resp. on the machine trace, composed from per-C-function simulation lemmas
about the compiled code of `eval_expr`/`exec_stmt`/`interp_run` — the
verified-compilation-scale core, stated here as explicit hypotheses. -/
structure InterpSim (L : Layout) : Prop where
  term_sim : ∀ p c out, Loaded L p c → BigStep p out → Halts c out 0
  stuck_sim : ∀ p c, Loaded L p c → (¬ ∃ out, BigStep p out) →
    Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0

/-! ## Derived: full behavioral correspondence

The interesting direction — everything below is proved outright. -/

/-- **Backward simulation for terminating behaviors**, derived from forward
simulation and machine determinism: if the machine halts cleanly with
`out`, then `out` is *the* specified behavior of `p`. Classical case split:
either `p` has a derivable behavior (then determinism forces agreement), or
it has none (then `stuck_sim` says a clean halt is impossible). -/
theorem halts_bigStep {L : Layout} (H : InterpSim L) {p : Program}
    {c : Config} (hL : Loaded L p c) {out : String}
    (h : Halts c out 0) : BigStep p out := by
  by_cases hex : ∃ out', BigStep p out'
  · obtain ⟨out', hb⟩ := hex
    obtain ⟨ho, -⟩ := h.deterministic (H.term_sim p c out' hL hb)
    exact ho ▸ hb
  · rcases H.stuck_sim p c hL hex with hd | ⟨out', e, h', he⟩
    · exact (hd.not_halts h).elim
    · obtain ⟨-, hee⟩ := h.deterministic h'
      exact (he hee.symm).elim

/-- **Divergence preservation (backward)**: a diverging machine run means
`p` has no terminating specified behavior. -/
theorem diverges_no_bigStep {L : Layout} (H : InterpSim L) {p : Program}
    {c : Config} (hL : Loaded L p c) (hd : Diverges c) :
    ¬ ∃ out, BigStep p out := by
  rintro ⟨out, hb⟩
  exact hd.not_halts (H.term_sim p c out hL hb)

/-- **The refinement theorem.** For *every* WHILE program `p` (deep
embedding, universally quantified) and every machine configuration in which
the interpreter binary holds `p`'s memory representation: the machine's
clean terminating behaviors are *exactly* the big-step behaviors of `p`,
and machine divergence entails `p` has no terminating behavior. The ELF
under the ISA relation is the implementation; the big-step relation is its
proven abstraction. -/
theorem refinement {L : Layout} (H : InterpSim L) :
    ∀ p c, Loaded L p c →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out) := by
  intro p c hL
  refine ⟨fun out => ⟨fun hb => H.term_sim p c out hL hb,
    fun h => halts_bigStep H hL h⟩, fun hd => diverges_no_bigStep H hL hd⟩

/-- Uniqueness of specified behavior, inherited by the source semantics
from machine determinism through the equivalence — a sanity corollary
(big-step determinism proven via the machine, CompCert's observation that
the target's determinism reflects back along an equivalence). -/
theorem bigStep_deterministic_of_loaded {L : Layout} (H : InterpSim L)
    {p : Program} {c : Config} (hL : Loaded L p c) {out out' : String}
    (h : BigStep p out) (h' : BigStep p out') : out = out' :=
  ((H.term_sim p c out hL h).deterministic (H.term_sim p c out' hL h')).1

end Vsa.Refine
