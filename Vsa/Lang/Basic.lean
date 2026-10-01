import Vsa.Machine

/-!
# Language-parametric refinement

A `Lang` is a source semantics observed through the machine's halting
behaviour: `Spec p e out` says `p` halts with exit code `e` having printed
`out`. `Obs e` selects the exit codes the specification speaks about (every
`Spec` result is observable); a machine halt with an unobservable code is a
runtime error. `Fits p` is the side condition under which the binary is
claimed correct (fragment and resource budget).

`Lang.Sim` is forward simulation from a loading relation. With machine
determinism it yields `Lang.refinement`. `Lang.Total` adds a divergence
semantics and trichotomy; `Lang.SimTotal` then yields `refinement_total`
(exact halts and exact divergence).
-/

namespace Vsa.Lang

open Vsa.Machine

structure Lang where
  Prog : Type
  /-- `p` halts with exit code `e`, having printed `out`. -/
  Spec : Prog → Nat → String → Prop
  /-- Exit codes the specification observes. -/
  Obs : Nat → Prop
  spec_obs : ∀ {p e out}, Spec p e out → Obs e
  /-- Side condition on programs (fragment, budget). -/
  Fits : Prog → Prop

namespace Lang

variable (L : Lang) (Loaded : L.Prog → Config → Prop)

/-- **Forward simulation**: every specified behaviour is a machine halt,
and a program with no specified behaviour diverges or halts unobservably. -/
structure Sim : Prop where
  term : ∀ p c e out, Loaded p c → L.Fits p → L.Spec p e out → Halts c out e
  stuck : ∀ p c, Loaded p c → L.Fits p → (¬ ∃ e out, L.Spec p e out) →
    Diverges c ∨ ∃ out e, Halts c out e ∧ ¬ L.Obs e

/-- The conclusion of the refinement theorem at one loaded program. -/
structure Refines (p : L.Prog) (c : Config) : Prop where
  halts : ∀ e out, L.Obs e → (L.Spec p e out ↔ Halts c out e)
  diverges : Diverges c → ¬ ∃ e out, L.Spec p e out

variable {L Loaded}

theorem Sim.spec_of_halts (H : L.Sim Loaded) {p : L.Prog} {c : Config}
    (hL : Loaded p c) (hf : L.Fits p) {e : Nat} {out : String} (ho : L.Obs e)
    (h : Halts c out e) : L.Spec p e out := by
  by_cases hex : ∃ e' out', L.Spec p e' out'
  · obtain ⟨e', out', hs⟩ := hex
    obtain ⟨rfl, rfl⟩ := h.deterministic (H.term p c e' out' hL hf hs)
    exact hs
  · rcases H.stuck p c hL hf hex with hd | ⟨out', e', h', hn⟩
    · exact (hd.not_halts h).elim
    · obtain ⟨-, rfl⟩ := h.deterministic h'
      exact (hn ho).elim

theorem Sim.no_spec_of_diverges (H : L.Sim Loaded) {p : L.Prog} {c : Config}
    (hL : Loaded p c) (hf : L.Fits p) (hd : Diverges c) : ¬ ∃ e out, L.Spec p e out :=
  fun ⟨e, out, hs⟩ => hd.not_halts (H.term p c e out hL hf hs)

/-- **The refinement theorem**, for any language. -/
theorem Sim.refinement (H : L.Sim Loaded) {p : L.Prog} {c : Config}
    (hL : Loaded p c) (hf : L.Fits p) : L.Refines p c where
  halts e out ho := ⟨H.term p c e out hL hf, H.spec_of_halts hL hf ho⟩
  diverges := H.no_spec_of_diverges hL hf

/-- The specification is deterministic on loaded programs. -/
theorem Sim.spec_deterministic (H : L.Sim Loaded) {p : L.Prog} {c : Config}
    (hL : Loaded p c) (hf : L.Fits p) {e e' : Nat} {out out' : String}
    (h : L.Spec p e out) (h' : L.Spec p e' out') : out = out' ∧ e = e' :=
  (H.term p c e out hL hf h).deterministic (H.term p c e' out' hL hf h')

/-! ## Total languages: divergence is specified -/

/-- A divergence semantics and the trichotomy: a fitting program halts
(observably) or diverges. -/
class Total (L : Lang) where
  Div : L.Prog → Prop
  total : ∀ p, L.Fits p → (∃ e out, L.Spec p e out) ∨ Div p

variable (L Loaded) in
/-- Forward simulation for a total language: halts and divergence. -/
structure SimTotal [L.Total] : Prop where
  term : ∀ p c e out, Loaded p c → L.Fits p → L.Spec p e out → Halts c out e
  div : ∀ p c, Loaded p c → L.Fits p → Total.Div p → Diverges c

theorem SimTotal.sim [L.Total] (H : L.SimTotal Loaded) : L.Sim Loaded where
  term := H.term
  stuck p c hL hf hn := by
    rcases Total.total p hf with hs | hd
    · exact (hn hs).elim
    · exact .inl (H.div p c hL hf hd)

variable (L) in
/-- The refinement conclusion for a total language. -/
structure RefinesTotal [L.Total] (p : L.Prog) (c : Config) : Prop where
  halts : ∀ e out, L.Obs e → (L.Spec p e out ↔ Halts c out e)
  diverges : Total.Div p ↔ Diverges c

/-- **The refinement theorem for a total language.** -/
theorem SimTotal.refinement [L.Total] (H : L.SimTotal Loaded) {p : L.Prog} {c : Config}
    (hL : Loaded p c) (hf : L.Fits p) : L.RefinesTotal p c where
  halts := (H.sim.refinement hL hf).halts
  diverges := ⟨H.div p c hL hf, fun hd => by
    rcases Total.total p hf with ⟨e, out, hs⟩ | hdv
    · exact (hd.not_halts (H.term p c e out hL hf hs)).elim
    · exact hdv⟩

end Lang

/-! ## Output-only languages: clean exit, specified output -/

/-- A language observed only through clean (`e = 0`) halts. Instances:
WHILE's `BigStep`, Lua's `BcSem`. -/
def ofOutput (P : Type) (S : P → String → Prop) : Lang where
  Prog := P
  Spec p e out := e = 0 ∧ S p out
  Obs e := e = 0
  spec_obs h := h.1
  Fits _ := True

section Output

variable {P : Type} (S : P → String → Prop) (Loaded : P → Config → Prop)

/-- Forward simulation for an output-only language. -/
structure OutSim : Prop where
  term_sim : ∀ p c out, Loaded p c → S p out → Halts c out 0
  stuck_sim : ∀ p c, Loaded p c → (¬ ∃ out, S p out) →
    Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0

variable {S Loaded}

theorem OutSim.sim (H : OutSim S Loaded) : (ofOutput P S).Sim Loaded where
  term p c _ out hL _ hs := hs.1 ▸ H.term_sim p c out hL hs.2
  stuck p c hL _ hn := H.stuck_sim p c hL fun ⟨out, hs⟩ => hn ⟨0, out, rfl, hs⟩

theorem OutSim.of_sim (H : (ofOutput P S).Sim Loaded) : OutSim S Loaded where
  term_sim p c out hL hs := H.term p c 0 out hL trivial ⟨rfl, hs⟩
  stuck_sim p c hL hn := H.stuck p c hL trivial fun ⟨_, out, _, hs⟩ => hn ⟨out, hs⟩

/-- **The refinement theorem for an output-only language.** -/
theorem OutSim.refinement (H : OutSim S Loaded) :
    ∀ p c, Loaded p c →
      (∀ out, S p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, S p out) := by
  intro p c hL
  have R := H.sim.refinement hL trivial
  refine ⟨fun out => ?_, fun hd ⟨out, hs⟩ => R.diverges hd ⟨0, out, rfl, hs⟩⟩
  exact ⟨fun hs => (R.halts 0 out rfl).1 ⟨rfl, hs⟩, fun h => ((R.halts 0 out rfl).2 h).2⟩

end Output

end Vsa.Lang
