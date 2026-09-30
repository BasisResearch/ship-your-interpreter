import Vsa.Lang.Basic
import Vsa.Lang.Runs

/-!
# Per-step arms ⇒ forward simulation

A `SmallStep` semantics (bytecode VMs: Lua, OCaml) has states, a step
relation `Next` and final states `Final p s e out`. `ArmSim` is the
per-step obligation family over a representation relation `Repr p s c`:
the entry reaches the initial state's representation, every `Next` step is
matched by at least one machine step, and every final state halts the
machine. `ArmSim.simTotal` derives total forward simulation for
`SmallStep.toLang`; `SmallStep.halts_or_diverges` supplies its trichotomy.
-/

namespace Vsa.Lang

open Vsa.Machine

structure SmallStep where
  Prog : Type
  State : Type
  init : Prog → State
  Next : Prog → State → State → Prop
  /-- `s` is final: the program halts with exit `e` having printed `out`. -/
  Final : Prog → State → Nat → String → Prop

namespace SmallStep

variable (S : SmallStep)

inductive StepsN (p : S.Prog) : Nat → S.State → S.State → Prop where
  | zero (s : S.State) : StepsN p 0 s s
  | succ {n : Nat} {a b c : S.State} : S.Next p a b → StepsN p n b c → StepsN p (n + 1) a c

def Reach (p : S.Prog) (s : S.State) : Prop := ∃ n, S.StepsN p n (S.init p) s

def Halts (p : S.Prog) (e : Nat) (out : String) : Prop := ∃ s, S.Reach p s ∧ S.Final p s e out

def Diverges (p : S.Prog) : Prop := ∀ n, ∃ s, S.StepsN p n (S.init p) s

/-- Every reachable state steps or is final. -/
def Progress (p : S.Prog) : Prop :=
  ∀ s, S.Reach p s → (∃ s', S.Next p s s') ∨ ∃ e out, S.Final p s e out

variable {S}

theorem StepsN.snoc {p : S.Prog} {n : Nat} {a b c : S.State}
    (h : S.StepsN p n a b) (s : S.Next p b c) : S.StepsN p (n + 1) a c := by
  induction h with
  | zero => exact .succ s (.zero _)
  | succ s0 _ ih => exact .succ s0 (ih s)

theorem Reach.next {p : S.Prog} {a b : S.State} (h : S.Reach p a) (s : S.Next p a b) :
    S.Reach p b :=
  let ⟨n, hn⟩ := h; ⟨n + 1, hn.snoc s⟩

theorem halts_or_diverges {p : S.Prog} (hp : S.Progress p) :
    (∃ e out, S.Halts p e out) ∨ S.Diverges p := by
  by_cases hd : S.Diverges p
  · exact .inr hd
  · left
    obtain ⟨n, hn⟩ : ∃ n, ¬ ∃ s, S.StepsN p n (S.init p) s := Classical.not_forall.1 hd
    induction n with
    | zero => exact (hn ⟨_, .zero _⟩).elim
    | succ k ih =>
      by_cases hk : ∃ s, S.StepsN p k (S.init p) s
      · obtain ⟨s, hs⟩ := hk
        rcases hp s ⟨k, hs⟩ with ⟨s', hs'⟩ | ⟨e, out, hf⟩
        · exact (hn ⟨s', hs.snoc hs'⟩).elim
        · exact ⟨e, out, s, ⟨k, hs⟩, hf⟩
      · exact ih hk

variable (S) in
/-- The language of a small-step semantics under side condition `Fits`,
which must imply progress. Every exit code is observable. -/
def toLang (Fits : S.Prog → Prop) (_hp : ∀ p, Fits p → S.Progress p) : Lang where
  Prog := S.Prog
  Spec := S.Halts
  Obs _ := True
  spec_obs _ := trivial
  Fits := Fits

instance {Fits : S.Prog → Prop} {hp : ∀ p, Fits p → S.Progress p} :
    (S.toLang Fits hp).Total where
  Div := S.Diverges
  total p hf := halts_or_diverges (hp p hf)

variable (S) in
/-- **Per-step obligations** for one program. -/
structure ArmSim (Fits : S.Prog → Prop) (Loaded : S.Prog → Config → Prop)
    (Repr : S.Prog → S.State → Config → Prop) (p : S.Prog) : Prop where
  entry : ∀ c, Loaded p c → Fits p → ∃ c', Plus c c' ∧ Repr p (S.init p) c'
  next : ∀ s s' c, S.Reach p s → Fits p → Repr p s c → S.Next p s s' →
    ∃ c', Plus c c' ∧ Repr p s' c'
  halt : ∀ s e out c, S.Reach p s → Fits p → Repr p s c → S.Final p s e out →
    Vsa.Machine.Halts c out e

variable {Fits : S.Prog → Prop} {Loaded : S.Prog → Config → Prop}
  {Repr : S.Prog → S.State → Config → Prop}

/-- Along `k` source steps from a represented reachable state, the machine
runs at least `k` steps to a configuration representing the end state. -/
theorem ArmSim.run {p : S.Prog} (A : S.ArmSim Fits Loaded Repr p) (hf : Fits p) :
    ∀ {k : Nat} {s s' : S.State} {c : Config}, S.Reach p s → S.StepsN p k s s' → Repr p s c →
      ∃ n c', k ≤ n ∧ Vsa.Machine.StepsN n c c' ∧ Repr p s' c' := by
  intro k s s' c hr hs hv
  induction hs generalizing c with
  | zero => exact ⟨0, c, Nat.le_refl _, .zero _, hv⟩
  | succ st _ ih =>
    obtain ⟨c1, ⟨n1, h1⟩, hv1⟩ := A.next _ _ c hr hf hv st
    obtain ⟨n2, c2, hle, h2, hv2⟩ := ih (hr.next st) hv1
    exact ⟨n1 + 1 + n2, c2, by omega, stepsN_append h1 h2, hv2⟩

/-- **Forward simulation from the per-step obligations.** -/
theorem ArmSim.simTotal {hp : ∀ p, Fits p → S.Progress p}
    (A : ∀ p, S.ArmSim Fits Loaded Repr p) : (S.toLang Fits hp).SimTotal Loaded where
  term := by
    intro p c e out hL hf ⟨s, ⟨k, hk⟩, hfin⟩
    obtain ⟨c0, ⟨n0, h0⟩, hv0⟩ := (A p).entry c hL hf
    obtain ⟨n, c', -, hn, hv⟩ := (A p).run hf ⟨0, .zero _⟩ hk hv0
    exact halts_of_steps (steps_trans (stepsN_toSteps h0) (stepsN_toSteps hn))
      ((A p).halt s e out c' ⟨k, hk⟩ hf hv hfin)
  div := by
    intro p c hL hf hd m
    obtain ⟨c0, ⟨n0, h0⟩, hv0⟩ := (A p).entry c hL hf
    obtain ⟨s, hs⟩ := hd m
    obtain ⟨n, c', hle, hn, -⟩ := (A p).run hf ⟨0, .zero _⟩ hs hv0
    have hall := stepsN_append h0 hn
    obtain ⟨d, hd'⟩ := Nat.exists_eq_add_of_le (show m ≤ n0 + 1 + n by omega)
    rw [hd'] at hall
    exact stepsN_prefix hall

end SmallStep

end Vsa.Lang
