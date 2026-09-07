import Vsa.Sim.SegEffect

namespace Vsa.Sim

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)

/-- Finite register masks, including the shared ABI mask. -/
inductive RegFrame where
  | all
  | none
  | abi
  | explicit (regs : List Register)

namespace RegFrame

def Holds : RegFrame → Register → Prop
  | .all, _ => True
  | .none, _ => False
  | .abi, R => Vsa.Alloc.AbiPreserved R = true
  | .explicit regs, R => R ∈ regs

def meet : RegFrame → RegFrame → RegFrame
  | .all, r => r
  | r, .all => r
  | .none, _ => .none
  | _, .none => .none
  | .abi, .abi => .abi
  | .abi, .explicit rs => .explicit (rs.filter Vsa.Alloc.AbiPreserved)
  | .explicit rs, .abi => .explicit (rs.filter Vsa.Alloc.AbiPreserved)
  | .explicit rs, .explicit ss => .explicit (rs.filter fun R => R ∈ ss)

theorem holds_meet (first second : RegFrame) (R : Register) :
    (meet first second).Holds R ↔ first.Holds R ∧ second.Holds R := by
  cases first <;> cases second <;> simp [meet, Holds, and_comm]

def ofSelection : RegisterSelection → RegFrame
  | .all => .all
  | .only rs => .explicit rs

theorem holds_ofSelection (rs : RegisterSelection) (R : Register) :
    (ofSelection rs).Holds R ↔ rs.Holds R := by
  cases rs <;> rfl

end RegFrame

/-- Address parameters are explicit inputs to effect denotation. -/
inductive AddrExpr where
  | literal (value : Nat)
  | variable (index : Nat)
  | add (base : AddrExpr) (offset : Nat)
  deriving DecidableEq

def AddrExpr.eval (values : Nat → Nat) : AddrExpr → Nat
  | .literal value => value
  | .variable index => values index
  | .add base offset => base.eval values + offset

/-- Guards remain attached to writes during normalization. -/
inductive GuardExpr where
  | always
  | eq (left right : AddrExpr)
  | conj (left right : GuardExpr)
  deriving DecidableEq

def GuardExpr.eval (values : Nat → Nat) : GuardExpr → Bool
  | .always => true
  | .eq left right => decide (left.eval values = right.eval values)
  | .conj left right => left.eval values && right.eval values

/-- A guarded, half-open byte interval. -/
structure WriteRegion where
  base : AddrExpr
  bytes : Nat
  guard : GuardExpr := .always
  deriving DecidableEq

namespace WriteRegion

def Contains (region : WriteRegion) (values : Nat → Nat) (a : Nat) : Prop :=
  region.guard.eval values = true ∧
    region.base.eval values ≤ a ∧ a < region.base.eval values + region.bytes

/-- Coalesce overlapping intervals with the same symbolic origin and guard.
Different guards are never widened or discarded. -/
def insert (region : WriteRegion) : List WriteRegion → List WriteRegion
  | [] => [region]
  | head :: rest =>
      if region.base = head.base ∧ region.guard = head.guard then
        { head with bytes := max region.bytes head.bytes } :: rest
      else head :: insert region rest

theorem contains_insert (region : WriteRegion) (regions : List WriteRegion)
    (values : Nat → Nat) (a : Nat) :
    (∃ r ∈ insert region regions, r.Contains values a) ↔
      region.Contains values a ∨ ∃ r ∈ regions, r.Contains values a := by
  induction regions with
  | nil => simp [insert]
  | cons head rest ih =>
    simp only [insert]
    split
    · rename_i h
      rcases region with ⟨base, bytes, guard⟩
      rcases head with ⟨base', bytes', guard'⟩
      simp only at h
      rcases h with ⟨rfl, rfl⟩
      simp only [List.mem_cons, exists_eq_or_imp, Contains]
      have hmax : a < base.eval values + max bytes bytes' ↔
          a < base.eval values + bytes ∨ a < base.eval values + bytes' := by omega
      simp only [hmax, and_or_left, or_assoc]
    · simp only [List.mem_cons, exists_eq_or_imp, ih]
      exact or_left_comm

def normalize : List WriteRegion → List WriteRegion
  | [] => []
  | region :: rest => insert region (normalize rest)

theorem contains_normalize (regions : List WriteRegion)
    (values : Nat → Nat) (a : Nat) :
    (∃ r ∈ normalize regions, r.Contains values a) ↔
      ∃ r ∈ regions, r.Contains values a := by
  induction regions with
  | nil => simp [normalize]
  | cons region rest ih =>
    simp only [normalize, contains_insert, ih, List.mem_cons, exists_eq_or_imp]

end WriteRegion

/-- Region form extends the existing finite-address `SegmentEffect` without
changing its compiled clients. -/
structure RegionEffect where
  regs : RegFrame
  writes : List WriteRegion
  outputPreserved : Bool

namespace RegionEffect

def denote (effect : RegionEffect) (values : Nat → Nat) : FrameEffect where
  regs := effect.regs.Holds
  mem := fun a => ¬ ∃ region ∈ effect.writes, region.Contains values a
  output := effect.outputPreserved = true

def identity : RegionEffect := ⟨.all, [], true⟩

def comp (first second : RegionEffect) : RegionEffect where
  regs := first.regs.meet second.regs
  writes := WriteRegion.normalize (first.writes ++ second.writes)
  outputPreserved := first.outputPreserved && second.outputPreserved

def branchJoin := comp

theorem denote_identity (values : Nat → Nat) :
    identity.denote values = FrameEffect.all := by
  apply FrameEffect.ext
  · rfl
  · funext a; simp [denote, identity, FrameEffect.all]
  · simp [denote, identity, FrameEffect.all]

theorem denote_comp (first second : RegionEffect) (values : Nat → Nat) :
    (comp first second).denote values =
      FrameEffect.comp (first.denote values) (second.denote values) := by
  apply FrameEffect.ext
  · funext R
    exact propext (RegFrame.holds_meet first.regs second.regs R)
  · funext a
    simp [denote, comp, WriteRegion.contains_normalize, FrameEffect.comp,
      List.mem_append, or_imp, forall_and]
  · simp [denote, comp, FrameEffect.comp, Bool.and_eq_true]

def ofFinite (effect : SegmentEffect) : RegionEffect where
  regs := RegFrame.ofSelection effect.preservedRegs
  writes := effect.writtenAddresses.map fun a => ⟨.literal a, 1, .always⟩
  outputPreserved := effect.preservesOutput

theorem denote_ofFinite (effect : SegmentEffect) (values : Nat → Nat) :
    (ofFinite effect).denote values = effect.denote := by
  apply FrameEffect.ext
  · funext R
    exact propext (RegFrame.holds_ofSelection effect.preservedRegs R)
  · funext a
    apply propext
    simp only [denote, ofFinite, SegmentEffect.denote, List.mem_map]
    have interval : ∀ b, (WriteRegion.mk (.literal b) 1 .always).Contains values a ↔ b = a := by
      intro b
      simp only [WriteRegion.Contains, GuardExpr.eval, AddrExpr.eval, true_and]
      omega
    simp [interval]
    constructor
    · intro h ha
      exact h a ha rfl
    · intro h b hb hba
      exact h (hba ▸ hb)
  · rfl

end RegionEffect

namespace EffectLe

theorem comp_left (first second : FrameEffect) :
    EffectLe (FrameEffect.comp first second) first :=
  ⟨fun _ h => h.1, fun _ h => h.1, fun h => h.1⟩

theorem comp_right (first second : FrameEffect) :
    EffectLe (FrameEffect.comp first second) second :=
  ⟨fun _ h => h.2, fun _ h => h.2, fun h => h.2⟩

theorem comp (h₁ : EffectLe weak₁ strong₁) (h₂ : EffectLe weak₂ strong₂) :
    EffectLe (FrameEffect.comp weak₁ weak₂) (FrameEffect.comp strong₁ strong₂) :=
  ⟨fun R h => ⟨h₁.regs R h.1, h₂.regs R h.2⟩,
   fun a h => ⟨h₁.mem a h.1, h₂.mem a h.2⟩,
   fun h => ⟨h₁.output h.1, h₂.output h.2⟩⟩

end EffectLe

/-- A predicate depends only on observations preserved by the effect. -/
def StableUnder (effect : FrameEffect) (P : Config → Prop) : Prop :=
  ∀ c0 c1, P c0 → FrameGuarantee effect c0 c1 → P c1

namespace StableUnder

theorem weaken (h : StableUnder weak P) (hle : EffectLe weak strong) :
    StableUnder strong P :=
  fun c0 c1 hp hf => h c0 c1 hp (hf.weaken hle)

theorem and (hP : StableUnder effect P) (hQ : StableUnder effect Q) :
    StableUnder effect (fun c => P c ∧ Q c) :=
  fun c0 c1 h hf => ⟨hP c0 c1 h.1 hf, hQ c0 c1 h.2 hf⟩

theorem forall_ {α : Sort u} {P : α → Config → Prop}
    (h : ∀ a, StableUnder effect (P a)) :
    StableUnder effect (fun c => ∀ a, P a c) :=
  fun c0 c1 hp hf a => h a c0 c1 (hp a) hf

theorem constant (effect : FrameEffect) (P : Prop) :
    StableUnder effect (fun _ => P) := fun _ _ h _ => h

theorem register (hR : effect.regs R) (value : Option (RegisterType R)) :
    StableUnder effect (fun c => c.σ.regs.get? R = value) := by
  intro c0 c1 h hf
  exact (hf.regs.eq R hR).trans h

theorem byte (ha : effect.mem a) (value : Option (BitVec 8)) :
    StableUnder effect (fun c => c.σ.mem[a]? = value) := by
  intro c0 c1 h hf
  exact (hf.mem a ha).trans h

theorem output (ho : effect.output) (value : Array String) :
    StableUnder effect (fun c => c.σ.sailOutput = value) := by
  intro c0 c1 h hf
  exact (hf.output ho).trans h

/-- Stability propagates through two actual frames at their shared endpoint. -/
theorem seq (h₁ : StableUnder first P) (h₂ : StableUnder second P)
    (hf₁ : FrameGuarantee first c0 c1) (hf₂ : FrameGuarantee second c1 c2)
    (hP : P c0) : P c2 :=
  h₂ c1 c2 (h₁ c0 c1 hP hf₁) hf₂

end StableUnder

namespace FramedTriple

theorem weaken (h : FramedTriple strong P Q) (hle : EffectLe weak strong) :
    FramedTriple weak P Q := by
  refine ⟨fun c hc => ?_⟩
  obtain ⟨c', hQ, hs⟩ := h.run c hc
  exact ⟨c', hQ, hs.weaken hle⟩

theorem branch (left : FramedTriple first P Q) (right : FramedTriple second R S) :
    FramedTriple (FrameEffect.comp first second)
      (fun c => P c ∨ R c) (fun c => Q c ∨ S c) := by
  refine ⟨fun c hc => ?_⟩
  rcases hc with hp | hr
  · obtain ⟨c', hQ, hs⟩ := left.run c hp
    exact ⟨c', Or.inl hQ, hs.weaken (EffectLe.comp_left first second)⟩
  · obtain ⟨c', hS, hs⟩ := right.run c hr
    exact ⟨c', Or.inr hS, hs.weaken (EffectLe.comp_right first second)⟩

theorem carryStable (h : FramedTriple effect P Q) (stable : StableUnder effect X) :
    FramedTriple effect (fun c => P c ∧ X c) (fun c => Q c ∧ X c) :=
  h.carry X stable

theorem regionSeq
    (h₁ : FramedTriple (first.denote values) P Q)
    (h₂ : FramedTriple (second.denote values) Q₂ R)
    (seam : ∀ c, Q c → Q₂ c) :
    FramedTriple ((RegionEffect.comp first second).denote values) P R := by
  rw [RegionEffect.denote_comp]
  exact h₁.seq h₂ seam

end FramedTriple

namespace FramedSteps

theorem regionComp
    (h₁ : FramedSteps (first.denote values) c0 c1)
    (h₂ : FramedSteps (second.denote values) c1 c2) :
    FramedSteps ((RegionEffect.comp first second).denote values) c0 c2 := by
  rw [RegionEffect.denote_comp]
  exact h₁.comp h₂

end FramedSteps

namespace FramedRTriple

theorem regionSeq
    (h₁ : FramedRTriple (first.denote values) R a b P Q)
    (h₂ : FramedRTriple (second.denote values) S b c P₂ T)
    (seam : ∀ cfg, Q cfg → P₂ cfg) :
    FramedRTriple ((RegionEffect.comp first second).denote values)
      (Vsa.Logic.RelVia b R S) a c P T := by
  rw [RegionEffect.denote_comp]
  exact h₁.seq h₂ seam

end FramedRTriple

#print axioms RegionEffect.denote_comp
#print axioms RegionEffect.denote_ofFinite
#print axioms FramedTriple.branch
#print axioms FramedTriple.carryStable

end Vsa.Sim
