import Vsa.Sim.SegmentEffect

namespace Vsa.Sim

open Vsa.Machine (Config)

universe u v w

/-- The executable effect descriptor and its proof share the same predicates. -/
structure CertifiedSegment (values : Nat → Nat) (P Q : Config → Prop) where
  effect : RegionEffect
  machine : FramedTriple (effect.denote values) P Q

/-- A certificate for a relation whose endpoints are already fixed. -/
structure CertifiedRSegment (values : Nat → Nat) {α : Type u} {β : Type v}
    (R : α → β → Prop) (a : α) (b : β) (P Q : Config → Prop) where
  effect : RegionEffect
  run : FramedRTriple (effect.denote values) R a b P Q

/-- The machine run chooses the semantic endpoint and witnesses its postcondition. -/
structure IndexedFramedRTriple {α : Type u} {β : Type v}
    (effect : FrameEffect) (Sem : α → β → Prop)
    (Pre : α → Config → Prop) (Post : β → Config → Prop) : Prop where
  run : ∀ a cfg, Pre a cfg → ∃ b cfg',
    Sem a b ∧ Post b cfg' ∧ FramedSteps effect cfg cfg'

namespace IndexedFramedRTriple

variable {α : Type u} {β : Type v} {γ : Type w}
variable {effect first second : FrameEffect}
variable {R R' : α → β → Prop} {S : β → γ → Prop}
variable {Pre Pre' : α → Config → Prop} {Mid : β → Config → Prop}
variable {Post Post' : β → Config → Prop} {Fin : γ → Config → Prop}

theorem conseq (h : IndexedFramedRTriple effect R Pre Post)
    (pre : ∀ a cfg, Pre' a cfg → Pre a cfg)
    (sem : ∀ a b, R a b → R' a b)
    (post : ∀ b cfg, Post b cfg → Post' b cfg) :
    IndexedFramedRTriple effect R' Pre' Post' := by
  refine ⟨fun a cfg hp => ?_⟩
  obtain ⟨b, cfg', hr, hq, hs⟩ := h.run a cfg (pre a cfg hp)
  exact ⟨b, cfg', sem a b hr, post b cfg' hq, hs⟩

theorem weaken (h : IndexedFramedRTriple first R Pre Post)
    (hle : EffectLe second first) : IndexedFramedRTriple second R Pre Post := by
  refine ⟨fun a cfg hp => ?_⟩
  obtain ⟨b, cfg', hr, hq, hs⟩ := h.run a cfg hp
  exact ⟨b, cfg', hr, hq, hs.weaken hle⟩

/-- The selected semantic midpoint is passed to the second machine run. -/
theorem bind (h₁ : IndexedFramedRTriple first R Pre Post)
    (h₂ : IndexedFramedRTriple second S Mid Fin)
    (seam : ∀ b cfg, Post b cfg → Mid b cfg) :
    IndexedFramedRTriple (FrameEffect.comp first second)
      (fun a c => ∃ b, R a b ∧ S b c) Pre Fin := by
  refine ⟨fun a cfg hp => ?_⟩
  obtain ⟨b, cfg₁, hr, hq, hs₁⟩ := h₁.run a cfg hp
  obtain ⟨c, cfg₂, ht, hf, hs₂⟩ := h₂.run b cfg₁ (seam b cfg₁ hq)
  exact ⟨c, cfg₂, ⟨b, hr, ht⟩, hf, hs₁.comp hs₂⟩

/-- A fixed relational certificate is one endpoint selection rule. -/
theorem ofFixed (a : α) (b : β)
    (h : FramedRTriple effect R a b (Pre a) (Post b)) :
    IndexedFramedRTriple effect R
      (fun a' cfg => a' = a ∧ Pre a cfg) Post := by
  refine ⟨fun a' cfg hp => ?_⟩
  obtain ⟨cfg', hq, hs⟩ := h.machine.run cfg hp.2
  exact ⟨b, cfg', hp.1.symm ▸ h.semantic, hq, hs⟩

/-- Either branch retains its own semantic index; only the common frame escapes. -/
theorem branch
    {δ : Type w} {ε : Type w}
    {T : δ → ε → Prop} {Entry : δ → Config → Prop}
    {Exit : ε → Config → Prop}
    (left : IndexedFramedRTriple first R Pre Post)
    (right : IndexedFramedRTriple second T Entry Exit) :
    IndexedFramedRTriple (FrameEffect.comp first second)
      (fun (a : Sum α δ) (b : Sum β ε) => match a, b with
        | .inl a, .inl b => R a b
        | .inr a, .inr b => T a b
        | _, _ => False)
      (fun a => Sum.elim Pre Entry a)
      (fun b => Sum.elim Post Exit b) := by
  refine ⟨fun a cfg hp => ?_⟩
  cases a with
  | inl a =>
    obtain ⟨b, cfg', hr, hq, hs⟩ := left.run a cfg hp
    exact ⟨.inl b, cfg', hr, hq,
      hs.weaken ⟨fun _ h => h.1, fun _ h => h.1, fun h => h.1⟩⟩
  | inr a =>
    obtain ⟨b, cfg', hr, hq, hs⟩ := right.run a cfg hp
    exact ⟨.inr b, cfg', hr, hq,
      hs.weaken ⟨fun _ h => h.2, fun _ h => h.2, fun h => h.2⟩⟩

/-- Finite source iteration with every semantic midpoint retained. -/
def Iter (R : α → α → Prop) : Nat → α → α → Prop
  | 0, a, b => a = b
  | n + 1, a, b => ∃ mid, R a mid ∧ Iter R n mid b

def iterEffect (effect : FrameEffect) : Nat → FrameEffect
  | 0 => FrameEffect.all
  | n + 1 => FrameEffect.comp effect (iterEffect effect n)

theorem fold {R : α → α → Prop} {P : α → Config → Prop}
    (step : IndexedFramedRTriple effect R P P) (n : Nat) :
    IndexedFramedRTriple (iterEffect effect n) (Iter R n) P P := by
  induction n with
  | zero =>
    exact ⟨fun a cfg hp =>
      ⟨a, cfg, rfl, hp, ⟨Vsa.Machine.Steps.refl cfg, FrameGuarantee.refl cfg⟩⟩⟩
  | succ n ih => exact step.bind ih (fun _ _ h => h)

/-- A recursive cut consumes the selected midpoint and folds its source evidence. -/
theorem recursiveCut {Whole : α → γ → Prop}
    (step : IndexedFramedRTriple first R Pre Post)
    (recurse : IndexedFramedRTriple second S Mid Fin)
    (seam : ∀ b cfg, Post b cfg → Mid b cfg)
    (close : ∀ a b c, R a b → S b c → Whole a c) :
    IndexedFramedRTriple (FrameEffect.comp first second) Whole Pre Fin := by
  apply (step.bind recurse seam).conseq (fun _ _ h => h) _ (fun _ _ h => h)
  intro a c h
  obtain ⟨b, hr, hs⟩ := h
  exact close a b c hr hs

end IndexedFramedRTriple

/-- Recursive certificates keep the machine-selected endpoint in their type. -/
structure CertifiedIndexedRSegment (values : Nat → Nat) {α : Type u} {β : Type v}
    (R : α → β → Prop) (Pre : α → Config → Prop)
    (Post : β → Config → Prop) where
  effect : RegionEffect
  run : IndexedFramedRTriple (effect.denote values) R Pre Post

namespace CertifiedSegment

def refl (values : Nat → Nat) (P : Config → Prop) : CertifiedSegment values P P where
  effect := RegionEffect.identity
  machine := by
    rw [RegionEffect.denote_identity]
    exact FramedTriple.refl

def seq (first : CertifiedSegment values P Q) (second : CertifiedSegment values Q₂ R)
    (seam : ∀ cfg, Q cfg → Q₂ cfg) : CertifiedSegment values P R where
  effect := first.effect.comp second.effect
  machine := by
    rw [RegionEffect.denote_comp]
    exact first.machine.seq second.machine seam

end CertifiedSegment

namespace CertifiedRSegment

def seq {α : Type u} {β : Type v} {γ : Type w}
    {R : α → β → Prop} {S : β → γ → Prop} {a : α} {b : β} {c : γ}
    (first : CertifiedRSegment values R a b P Q)
    (second : CertifiedRSegment values S b c P₂ T)
    (seam : ∀ cfg, Q cfg → P₂ cfg) :
    CertifiedRSegment values (Vsa.Logic.RelVia b R S) a c P T where
  effect := first.effect.comp second.effect
  run := by
    rw [RegionEffect.denote_comp]
    exact first.run.seq second.run seam

end CertifiedRSegment

namespace CertifiedIndexedRSegment

def bind {α : Type u} {β : Type v} {γ : Type w}
    {R : α → β → Prop} {S : β → γ → Prop}
    {Pre : α → Config → Prop} {Post Mid : β → Config → Prop}
    {Fin : γ → Config → Prop}
    (first : CertifiedIndexedRSegment values R Pre Post)
    (second : CertifiedIndexedRSegment values S Mid Fin)
    (seam : ∀ b cfg, Post b cfg → Mid b cfg) :
    CertifiedIndexedRSegment values (fun a c => ∃ b, R a b ∧ S b c) Pre Fin where
  effect := first.effect.comp second.effect
  run := by
    rw [RegionEffect.denote_comp]
    exact first.run.bind second.run seam

end CertifiedIndexedRSegment

/-- A finite query identity includes the stop policy, not only its display name. -/
structure SegmentIdentity where
  query : String
  residual : String
  entryPC : BitVec 64
  exitPC : BitVec 64
  stopBefore : Bool
  deriving DecidableEq, Repr

/-- Both PCs are proved against the certificate's actual machine predicates. -/
structure CertifiedSpan (values : Nat → Nat) (identity : SegmentIdentity) (P Q : Config → Prop) where
  segment : CertifiedSegment values P Q
  entry : ∀ cfg, P cfg →
    cfg.σ.regs.get? LeanRV64DExecutable.Register.PC = some identity.entryPC
  exit : ∀ cfg, Q cfg →
    cfg.σ.regs.get? LeanRV64DExecutable.Register.PC = some identity.exitPC

#print axioms IndexedFramedRTriple.bind
#print axioms IndexedFramedRTriple.branch
#print axioms IndexedFramedRTriple.fold
#print axioms IndexedFramedRTriple.recursiveCut
#print axioms CertifiedIndexedRSegment.bind

end Vsa.Sim
