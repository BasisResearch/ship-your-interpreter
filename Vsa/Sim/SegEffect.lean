import Vsa.Sim.BridgeSegFramed
import Vsa.Sim.SegReadback
import Vsa.Sim.TripleCat

namespace Vsa.Sim

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.Logic (Triple)

/-- A dependent register map is unchanged on the selected register predicate.
The codomain remains indexed by the register, matching the machine register
file rather than erasing values to an untyped word. -/
structure EffectStable (keep : Register → Prop)
    (left right : (R : Register) → Option (RegisterType R)) : Prop where
  eq : ∀ R, keep R → left R = right R

/-- Stability is symmetric. -/
theorem EffectStable.symm
    (h : EffectStable keep left right) : EffectStable keep right left := by
  exact ⟨fun R hR => (h.eq R hR).symm⟩

/-- Opaque transitivity for dependent register maps. -/
theorem EffectStable.trans
    (h₁ : EffectStable keep left middle)
    (h₂ : EffectStable keep middle right) :
    EffectStable keep left right := by
  exact ⟨fun R hR => (h₁.eq R hR).trans (h₂.eq R hR)⟩

#print axioms EffectStable.trans

/-! ## Compositional machine frames -/

/-- Observations guaranteed unchanged by a machine run.  The memory field is
an address predicate, so an exact write footprint `foot` is represented by
`fun a => ¬ foot a`.  Store/allocation representations remain typed predicates
and can be carried with `FramedTriple.carry` below. -/
structure FrameEffect where
  regs : Register → Prop
  mem : Nat → Prop
  output : Prop

namespace FrameEffect

/-- Effects are equal when their three observation predicates are equal. -/
theorem ext {left right : FrameEffect}
    (regs : left.regs = right.regs) (mem : left.mem = right.mem)
    (output : left.output = right.output) : left = right := by
  cases left
  cases right
  cases regs
  cases mem
  cases output
  rfl

/-- The zero-step effect preserves every core observation. -/
def all : FrameEffect where
  regs := fun _ => True
  mem := fun _ => True
  output := True

/-- Sequential effects preserve exactly the observations preserved by both
runs. -/
def comp (first second : FrameEffect) : FrameEffect where
  regs := fun R => first.regs R ∧ second.regs R
  mem := fun a => first.mem a ∧ second.mem a
  output := first.output ∧ second.output

end FrameEffect

/-- `EffectLe weak strong` says that every observation requested by `weak`
is supplied by `strong`.  It is the order used when forgetting frame facts. -/
structure EffectLe (weak strong : FrameEffect) : Prop where
  regs : ∀ R, weak.regs R → strong.regs R
  mem : ∀ a, weak.mem a → strong.mem a
  output : weak.output → strong.output

namespace EffectLe

theorem refl (effect : FrameEffect) : EffectLe effect effect := by
  exact ⟨fun _ h => h, fun _ h => h, fun h => h⟩

theorem trans (h₁ : EffectLe first middle) (h₂ : EffectLe middle last) :
    EffectLe first last := by
  exact
    { regs := fun R hR => h₂.regs R (h₁.regs R hR)
      mem := fun a ha => h₂.mem a (h₁.mem a ha)
      output := fun ho => h₂.output (h₁.output ho) }

end EffectLe

/-! ## Finite effect descriptions -/

/-- A finite description of the registers preserved by a segment. -/
inductive RegisterSelection where
  | all
  | only (regs : List Register)

namespace RegisterSelection

def Holds : RegisterSelection → Register → Prop
  | .all, _ => True
  | .only regs, R => R ∈ regs

/-- Flat normal form for the observations preserved by two paths. -/
def meet : RegisterSelection → RegisterSelection → RegisterSelection
  | .all, second => second
  | first, .all => first
  | .only first, .only second =>
      .only (first.filter fun R => R ∈ second)

theorem holds_meet (first second : RegisterSelection) (R : Register) :
    (meet first second).Holds R ↔ first.Holds R ∧ second.Holds R := by
  cases first <;> cases second <;> simp [meet, Holds]

end RegisterSelection

/-- Reified core effect.  Memory stores are a finite may-write set; every
address outside it is preserved.  Composition stays in this flat form. -/
structure SegmentEffect where
  preservedRegs : RegisterSelection
  writtenAddresses : List Nat
  preservesOutput : Bool

namespace SegmentEffect

def denote (effect : SegmentEffect) : FrameEffect where
  regs := effect.preservedRegs.Holds
  mem := fun a => a ∉ effect.writtenAddresses
  output := effect.preservesOutput = true

def identity : SegmentEffect where
  preservedRegs := .all
  writtenAddresses := []
  preservesOutput := true

/-- Normalized sequential composition: intersect preserved observations and
flatten the two finite may-write sets. -/
def comp (first second : SegmentEffect) : SegmentEffect where
  preservedRegs := first.preservedRegs.meet second.preservedRegs
  writtenAddresses := first.writtenAddresses ++ second.writtenAddresses
  preservesOutput := first.preservesOutput && second.preservesOutput

/-- A branch exposes only observations preserved by both alternatives. -/
def branchJoin (left right : SegmentEffect) : SegmentEffect :=
  comp left right

theorem denote_identity : identity.denote = FrameEffect.all := by
  apply FrameEffect.ext
  · funext R
    simp [identity, denote, RegisterSelection.Holds, FrameEffect.all]
  · funext a
    simp [identity, denote, FrameEffect.all]
  · simp [identity, denote, FrameEffect.all]

theorem denote_comp (first second : SegmentEffect) :
    (comp first second).denote =
      FrameEffect.comp first.denote second.denote := by
  apply FrameEffect.ext
  · funext R
    apply propext
    exact RegisterSelection.holds_meet first.preservedRegs second.preservedRegs R
  · funext a
    simp [comp, denote, FrameEffect.comp]
  · simp [comp, denote, FrameEffect.comp, Bool.and_eq_true]

theorem denote_branchJoin (left right : SegmentEffect) :
    (branchJoin left right).denote =
      FrameEffect.comp left.denote right.denote := by
  exact denote_comp left right

end SegmentEffect

/-- Core frame evidence for one concrete run.  Every equality is oriented
post-state to pre-state, matching the existing register-frame contracts. -/
structure FrameGuarantee (effect : FrameEffect) (c0 c1 : Config) : Prop where
  regs : EffectStable effect.regs
    (fun R => c1.σ.regs.get? R) (fun R => c0.σ.regs.get? R)
  mem : ∀ a, effect.mem a → c1.σ.mem[a]? = c0.σ.mem[a]?
  output : effect.output → c1.σ.sailOutput = c0.σ.sailOutput

namespace FrameGuarantee

/-- Zero steps preserve every observation. -/
theorem refl (c : Config) : FrameGuarantee FrameEffect.all c c := by
  exact
    { regs := ⟨fun _ _ => rfl⟩
      mem := fun _ _ => rfl
      output := fun _ => rfl }

/-- Compose two concrete frames through their shared machine midpoint. -/
theorem comp
    (h₁ : FrameGuarantee first c0 c1)
    (h₂ : FrameGuarantee second c1 c2) :
    FrameGuarantee (FrameEffect.comp first second) c0 c2 := by
  exact
    { regs := ⟨fun R hR => (h₂.regs.eq R hR.2).trans (h₁.regs.eq R hR.1)⟩
      mem := fun a ha => (h₂.mem a ha.2).trans (h₁.mem a ha.1)
      output := fun ho => (h₂.output ho.2).trans (h₁.output ho.1) }

/-- Forget observations while retaining the same concrete run. -/
theorem weaken (h : FrameGuarantee strong c0 c1)
    (hle : EffectLe weak strong) : FrameGuarantee weak c0 c1 := by
  exact
    { regs := ⟨fun R hR => h.regs.eq R (hle.regs R hR)⟩
      mem := fun a ha => h.mem a (hle.mem a ha)
      output := fun ho => h.output (hle.output ho) }

end FrameGuarantee

/-- A concrete machine run whose endpoint carries a typed core frame. -/
structure FramedSteps (effect : FrameEffect) (c0 c1 : Config) : Prop where
  steps : Steps c0 c1
  frame : FrameGuarantee effect c0 c1

namespace FramedSteps

/-- Compose framed runs through their explicit shared endpoint. -/
theorem comp
    (h₁ : FramedSteps first c0 c1) (h₂ : FramedSteps second c1 c2) :
    FramedSteps (FrameEffect.comp first second) c0 c2 := by
  exact ⟨h₁.steps.trans h₂.steps, h₁.frame.comp h₂.frame⟩

/-- Forget observations without changing the run endpoints. -/
theorem weaken (h : FramedSteps strong c0 c1) (hle : EffectLe weak strong) :
    FramedSteps weak c0 c1 := by
  exact ⟨h.steps, h.frame.weaken hle⟩

/-- Compose runs described by finite effects. -/
theorem segmentComp
    (h₁ : FramedSteps first.denote c0 c1)
    (h₂ : FramedSteps second.denote c1 c2) :
    FramedSteps (SegmentEffect.comp first second).denote c0 c2 := by
  rw [SegmentEffect.denote_comp]
  exact h₁.comp h₂

end FramedSteps

/-- Total-correctness triple whose chosen endpoint also carries the indexed
register, memory, and output frame.  The postcondition and frame cannot be
witnessed by different runs. -/
structure FramedTriple (effect : FrameEffect)
    (P Q : Config → Prop) : Prop where
  run : ∀ c, P c → ∃ c', Q c' ∧ FramedSteps effect c c'

namespace FramedTriple

/-- Forget only the frame evidence. -/
theorem triple (h : FramedTriple effect P Q) : Triple P Q := by
  intro c hc
  obtain ⟨c', hQ, hrun⟩ := h.run c hc
  exact ⟨c', hrun.steps, hQ⟩

/-- Zero-step framed triple. -/
theorem refl : FramedTriple FrameEffect.all P P := by
  exact ⟨fun c hc =>
    ⟨c, hc, ⟨Vsa.Machine.Steps.refl c, FrameGuarantee.refl c⟩⟩⟩

/-- Consequence changes predicates without discarding the frame. -/
theorem conseq (h : FramedTriple effect P Q)
    (pre : ∀ c, P' c → P c) (post : ∀ c, Q c → Q' c) :
    FramedTriple effect P' Q' := by
  refine ⟨fun c hc => ?_⟩
  obtain ⟨c', hQ, hrun⟩ := h.run c (pre c hc)
  exact ⟨c', post c' hQ, hrun⟩

/-- Sequential composition.  The predicate seam is explicit; the effect is
combined generically by `FrameEffect.comp`. -/
theorem seq (h₁ : FramedTriple first P Q)
    (h₂ : FramedTriple second Q₂ R) (seam : ∀ c, Q c → Q₂ c) :
    FramedTriple (FrameEffect.comp first second) P R := by
  refine ⟨fun c hc => ?_⟩
  obtain ⟨c₁, hQ, hrun₁⟩ := h₁.run c hc
  obtain ⟨c₂, hR, hrun₂⟩ := h₂.run c₁ (seam c₁ hQ)
  exact ⟨c₂, hR, hrun₁.comp hrun₂⟩

/-- Typed extension point for store, allocation, code, or syntax invariants.
The caller proves once that its predicate survives this core effect. -/
theorem carry (h : FramedTriple effect P Q) (X : Config → Prop)
    (stable : ∀ c0 c1, X c0 → FrameGuarantee effect c0 c1 → X c1) :
    FramedTriple effect (fun c => P c ∧ X c) (fun c => Q c ∧ X c) := by
  refine ⟨fun c hc => ?_⟩
  obtain ⟨c', hQ, hrun⟩ := h.run c hc.1
  exact ⟨c', ⟨hQ, stable c c' hc.2 hrun.frame⟩, hrun⟩

end FramedTriple

#print axioms FrameGuarantee.comp
#print axioms FramedSteps.comp
#print axioms FramedTriple.seq
#print axioms FramedTriple.carry

/-! ## Relation-indexed framed refinements -/

universe u v w

/-- Source-semantic evidence paired with the same framed machine run used by
the postcondition.  This is the effect-aware layer above `Logic.RTriple`:
forgetting the frame recovers an ordinary relation-indexed triple. -/
structure FramedRTriple {α : Sort u} {β : Sort v}
    (effect : FrameEffect) (R : α → β → Prop) (a : α) (b : β)
    (P Q : Config → Prop) : Prop where
  semantic : R a b
  machine : FramedTriple effect P Q

namespace FramedRTriple

/-- Package semantic evidence and an already-framed machine triple. -/
theorem pack (semantic : R a b) (machine : FramedTriple effect P Q) :
    FramedRTriple effect R a b P Q :=
  ⟨semantic, machine⟩

/-- Forget only effect evidence, retaining the source relation and machine
triple. -/
theorem rTriple (h : FramedRTriple effect R a b P Q) :
    Vsa.Logic.RTriple R a b P Q :=
  ⟨h.semantic, h.machine.triple⟩

/-- Consequence changes machine predicates without losing either semantic or
frame evidence. -/
theorem conseq (h : FramedRTriple effect R a b P Q)
    (pre : ∀ c, P' c → P c) (post : ∀ c, Q c → Q' c) :
    FramedRTriple effect R a b P' Q' :=
  ⟨h.semantic, h.machine.conseq pre post⟩

/-- Compose semantic relations through `b` and machine frames through their
explicit predicate seam. -/
theorem seq
    (h₁ : FramedRTriple first R a b P Q)
    (h₂ : FramedRTriple second S b c P₂ T)
    (seam : ∀ cfg, Q cfg → P₂ cfg) :
    FramedRTriple (FrameEffect.comp first second)
      (Vsa.Logic.RelVia b R S) a c P T :=
  ⟨⟨h₁.semantic, h₂.semantic⟩, h₁.machine.seq h₂.machine seam⟩

/-- Carry a stable machine invariant without adding it to every bespoke
segment postcondition. -/
theorem carry (h : FramedRTriple effect R a b P Q) (X : Config → Prop)
    (stable : ∀ c0 c1, X c0 → FrameGuarantee effect c0 c1 → X c1) :
    FramedRTriple effect R a b
      (fun cfg => P cfg ∧ X cfg) (fun cfg => Q cfg ∧ X cfg) :=
  ⟨h.semantic, h.machine.carry X stable⟩

end FramedRTriple

#print axioms FramedRTriple.rTriple
#print axioms FramedRTriple.seq
#print axioms FramedRTriple.carry

/-- One symbolic register update selected from a reflected segment result. -/
abbrev GUpdate := Nat × BitVec 64

/-- A finite list of exact projections from a symbolic register result. -/
def GProjects (out : GRegs) : List GUpdate → Prop
  | [] => True
  | (n, v) :: rest => lookupG n out = some v ∧ GProjects out rest

/-- Selected projections of a held symbolic result are concrete machine pins. -/
theorem gholds_selected {sigma : Vsa.Machine.MState} {out selected : GRegs}
    (hproj : GProjects out selected) (hregs : GHolds sigma out) :
    GHolds sigma selected := by
  induction selected with
  | nil => trivial
  | cons update rest ih =>
    obtain ⟨n, v⟩ := update
    exact ⟨gholds_lookup out hregs hproj.1, ih hproj.2⟩

/-- A register lookup survives one symbolic instruction that writes elsewhere. -/
theorem lookupG_stepGM_preserved (a : MInstr) (L : GRegs)
    (bs : List (BitVec 8)) (n : Nat) (h : n ≠ a.rd) :
    lookupG n (stepGM a L bs) = lookupG n L := by
  unfold stepGM
  split <;> try rfl
  show lookupG n ((a.rd, wvalM a L bs) :: eraseG a.rd L) = lookupG n L
  rw [lookupG, if_neg (by omega), lookupG_eraseG_ne n a.rd (by omega) L]

/-- A lookup survives a finite symbolic instruction list that never writes it. -/
theorem lookupG_runGM_preserved (n : Nat) : ∀ body : List MInstr,
    (∀ a ∈ body, a.rd ≠ n) → ∀ (L : GRegs) (lds : List (List (BitVec 8))),
      lookupG n (runGM body L lds) = lookupG n L := by
  intro body
  induction body with
  | nil => intro _ L lds; rfl
  | cons a rest ih =>
    intro h L lds
    rw [runGM, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    exact lookupG_stepGM_preserved a L (lds.headD []) n
      (Ne.symm (h a (List.mem_cons_self ..)))

/-- Read a register written once in the middle of a finite symbolic program. -/
theorem lookupG_runGM_after_writer (pre : List MInstr) (a : MInstr)
    (post : List MInstr) (L : GRegs) (lds : List (List (BitVec 8)))
    (hstore : a.kind ≠ .sw ∧ a.kind ≠ .sd ∧ a.kind ≠ .sb ∧ a.kind ≠ .sh)
    (n : Nat) (hrd : a.rd = n) (hpost : ∀ b ∈ post, b.rd ≠ n) :
    lookupG n (runGM (pre ++ a :: post) L lds) =
      some (wvalM a (runGM pre L lds) ((ldsRunM pre lds).headD [])) := by
  induction pre generalizing L lds with
  | nil =>
    simp only [List.nil_append, runGM, ldsRunM]
    rw [lookupG_runGM_preserved n post hpost
      (stepGM a L (lds.headD [])) (stepLdsM a.kind lds)]
    exact lookupG_stepGM_writer a L (lds.headD []) hstore n hrd
  | cons b rest ih =>
    simp only [List.cons_append, runGM, ldsRunM]
    exact ih (stepGM b L (lds.headD [])) (stepLdsM b.kind lds)

/-- Opaque semantic result for a reflected segment with an exact memory result,
an exact footprint frame, a register frame, and finitely selected post-registers. -/
structure SelectedFramedSegResult
    (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (foot : Nat → Prop) (keep : Register → Bool)
    (selected : GRegs) (c0 c1 : Config) : Prop where
  steps : Steps c0 c1
  good : GoodState c1.σ
  tick : c1.tick < 2
  mem : c1.σ.mem = writeLog c0.σ.mem
    (evalBlocks bs (SegEvalState.init L lds)).log
  outside : ∀ k, ¬ foot k → c0.σ.mem[k]? = c1.σ.mem[k]?
  output : c1.σ.sailOutput = c0.σ.sailOutput
  pc : c1.σ.regs.get? Register.PC =
    some (evalBlocksPC pc0 (SegEvalState.init L lds) bs)
  minstret : ∃ w, c1.σ.regs.get? Register.minstret = some w
  selected_regs : GHolds c1.σ selected
  reg_frame : ∀ R, keep R = true → c1.σ.regs.get? R = c0.σ.regs.get? R

/-- Core effect exposed by a selected reflected segment. -/
def selectedSegEffect (foot : Nat → Prop)
    (keep : Register → Bool) : FrameEffect where
  regs := fun R => keep R = true
  mem := fun a => ¬ foot a
  output := True

/-- Forget segment-specific facts while retaining its run and compositional
core frame. -/
theorem SelectedFramedSegResult.framedSteps
    (h : SelectedFramedSegResult bs L lds pc0 foot keep selected c0 c1) :
    FramedSteps (selectedSegEffect foot keep) c0 c1 := by
  exact
    { steps := h.steps
      frame :=
        { regs := ⟨h.reg_frame⟩
          mem := fun a ha => (h.outside a ha).symm
          output := fun _ => h.output } }

#print axioms SelectedFramedSegResult.framedSteps

/-- Generic constructor for the selected, footprint-aware segment result. -/
theorem segEval_selected_framed
    (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 vm : BitVec 64) (foot : Nat → Prop) (keep : Register → Bool)
    (selected : GRegs) (c : Config)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some pc0)
    (hmi : c.σ.regs.get? Register.minstret = some vm)
    (hL : GHolds c.σ L) (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts c.σ.mem c.σ.mem L lds bs)
    (hwf : ChainOK pc0 (keysG L) bs) (hi : c.tick < 2)
    (hfoot : ∀ k, ¬ foot k → c.σ.mem[k]? =
      (writeLog c.σ.mem (evalBlocks bs (SegEvalState.init L lds)).log)[k]?)
    (hnoise : ∀ rr ∈ noiseRegs, keep rr = false)
    (havoid : WrChainAvoids keep bs)
    (hproj : GProjects (evalBlocks bs (SegEvalState.init L lds)).regs selected) :
    ∃ c', SelectedFramedSegResult bs L lds pc0 foot keep selected c c' := by
  obtain ⟨sigma', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hregs', hframe'⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds
      hG hpc hmi hL hkeys hfacts hwf hi
  let c' : Config := ⟨sigma', i', c.steps + evalBlocksFuel bs⟩
  refine ⟨c', ?_⟩
  refine
    { steps := by simpa [c'] using hsteps
      good := by simpa [c'] using hG'
      tick := by simpa [c'] using hi'
      mem := by simpa [c'] using hmem'
      outside := ?_
      output := by simpa [c'] using hout'
      pc := by simpa [c'] using hpc'
      minstret := by simpa [c'] using hmi'
      selected_regs := by
        simpa [c'] using gholds_selected hproj hregs'
      reg_frame := ?_ }
  · intro k hk
    exact (hfoot k hk).trans (congrArg (fun m : Vsa.MemRepr.Mem => m[k]?) hmem').symm
  · intro R hR
    simpa [c'] using
      frame_of_wrChain_avoids (P := keep) hnoise havoid hframe' R hR

#print axioms segEval_selected_framed

end Vsa.Sim
