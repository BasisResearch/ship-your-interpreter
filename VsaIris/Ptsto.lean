import VsaIris.Machine
import Iris.ProgramLogic.TotalWeakestPre
import Iris.ProgramLogic.TotalLifting
import Iris.Instances.Lib.GhostMap
import Std.Data.ExtTreeMap

/-!
# Points-to and the state interpretation

Port of xv6iris `iris/RiscvPtsto.v`, single-hart and sequential:

* `r ↦ᵣ{dq} v` (RiscvPtsto.v:1359 `reg_pointsto`) is a `ghost_map` element on
  the register ghost name;
* `a ↦ₘ{dq} b` (RiscvPtsto.v:1584 `mem_pointsto`) is a `ghost_map` element on
  the memory ghost name. MachCSL's version also carries a kernel page-map
  witness (`kmap_at`) and the RAM predicate; VSA runs untranslated
  (bare-metal M-mode), so the byte is the physical one;
* the register bridge is an *existential* authoritative map that agrees with
  the concrete state where defined (`reg_agree`/`reg_interp_at`,
  RiscvPtsto.v:2207-2213). We use the same partial-agreement bridge for
  memory as well. MachCSL uses `gen_heap_interp σ.mem` (exact agreement,
  RiscvPtsto.v:2341), which requires the model's memory to BE a finite map;
  VSA's Sail memory reads unmapped bytes as zero, and the initial RAM image is
  not a finite map worth tracking, so memory gets the register treatment
  (DESIGN.md §"Deviations");
* `mstate_interp` (RiscvPtsto.v:2340) = register bridge ∗ memory bridge; the
  device conjunct is dropped.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

/-- Finite maps keyed by `Nat` (register index or byte address). -/
abbrev NatMap := fun V => Std.ExtTreeMap Nat V compare

/-- The two ghost maps (RiscvPtsto.v:479 `riscvFixedGS` keeps the register
map per hart and memory in `gen_heapGS`). -/
class MachPreG (GF : BundledGFunctors) where
  regG : GhostMapG GF Nat (BitVec 64) NatMap
  memG : GhostMapG GF Nat (BitVec 8) NatMap

attribute [reducible, instance] MachPreG.regG MachPreG.memG

class MachGpreS (GF : BundledGFunctors) extends InvGpreS GF where
  machPre : MachPreG GF

attribute [reducible, instance] MachGpreS.machPre

/-- `riscvGS` (RiscvPtsto.v:691), cut to the two names a single hart needs. -/
class MachGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  [invGS : InvGS_gen hlc GF]
  machPre : MachPreG GF
  regName : GName
  memName : GName

attribute [reducible, instance] MachGS.machPre
attribute [implicit_reducible, instance] MachGS.invGS

section Defs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- `reg_pointsto` (RiscvPtsto.v:1359). -/
def regPointsTo (r : Nat) (dq : DFrac) (v : BitVec 64) : IProp GF :=
  ghost_map_elem G.regName dq r v

/-- `mem_pointsto` (RiscvPtsto.v:1584), physical and untranslated. -/
def memPointsTo (a : Nat) (dq : DFrac) (b : BitVec 8) : IProp GF :=
  ghost_map_elem G.memName dq a b

notation:50 r:50 " ↦ᵣ{" dq "} " v:50 => regPointsTo r dq v
notation:50 r:50 " ↦ᵣ " v:50 => regPointsTo r (DFrac.own 1) v
notation:50 r:50 " ↦ᵣ□ " v:50 => regPointsTo r DFrac.discard v
notation:50 a:50 " ↦ₘ{" dq "} " v:50 => memPointsTo a dq v
notation:50 a:50 " ↦ₘ " v:50 => memPointsTo a (DFrac.own 1) v
notation:50 a:50 " ↦ₘ□ " v:50 => memPointsTo a DFrac.discard v

instance (r : Nat) (v : BitVec 64) : Persistent (PROP := IProp GF) (r ↦ᵣ□ v) := by
  unfold regPointsTo; infer_instance
instance (a : Nat) (b : BitVec 8) : Persistent (PROP := IProp GF) (a ↦ₘ□ b) := by
  unfold memPointsTo; infer_instance

variable (M : MachineModel)

/-- `reg_agree` (RiscvPtsto.v:2207): the ghost map agrees with the state
wherever it is defined. -/
def RegAgree (m : NatMap (BitVec 64)) (σ : M.State) : Prop :=
  ∀ k v, PartialMap.get? m k = some v → M.reg σ k = v

def MemAgree (m : NatMap (BitVec 8)) (σ : M.State) : Prop :=
  ∀ k v, PartialMap.get? m k = some v → M.mem σ k = v

/-- `reg_interp_at` (RiscvPtsto.v:2213). -/
def regInterp (σ : M.State) : IProp GF :=
  iprop(∃ m, ghost_map_auth G.regName (DFrac.own 1) m ∗ ⌜RegAgree M m σ⌝)

def memInterp (σ : M.State) : IProp GF :=
  iprop(∃ m, ghost_map_auth G.memName (DFrac.own 1) m ∗ ⌜MemAgree M m σ⌝)

/-- `mstate_interp` (RiscvPtsto.v:2340) without the device conjunct. -/
def mstateInterp (σ : M.State) : IProp GF := iprop(regInterp M σ ∗ memInterp M σ)

/-- The `IrisGS` instance (RiscvPtsto.v:2622 §3): no later credits per
step, no forks, and the state interpretation ignores the step and thread
counters. -/
instance machIrisGS : IrisGS_gen hlc (MExprOf M) GF where
  invGS := G.invGS
  stateInterp σ _ _ _ := mstateInterp M σ
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by
    letI := G.invGS
    iintro $

end Defs

section Rules

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- `reg_valid` (RiscvPtsto.v:2909). -/
theorem reg_valid {σ : M.State} {r : Nat} {dq : DFrac} {v : BitVec 64} :
    regInterp (GF := GF) M σ ⊢ (r ↦ᵣ{dq} v) -∗ ⌜M.reg σ r = v⌝ := by
  unfold regInterp regPointsTo
  iintro ⟨%m, Hm, %Hag⟩ Hr
  ihave %Hlk := ghost_map_lookup $$ Hm Hr
  ipureintro
  exact Hag r v Hlk

theorem mem_valid {σ : M.State} {a : Nat} {dq : DFrac} {b : BitVec 8} :
    memInterp (GF := GF) M σ ⊢ (a ↦ₘ{dq} b) -∗ ⌜M.mem σ a = b⌝ := by
  unfold memInterp memPointsTo
  iintro ⟨%m, Hm, %Hag⟩ Ha
  ihave %Hlk := ghost_map_lookup $$ Hm Ha
  ipureintro
  exact Hag a b Hlk

/-- `reg_update` (RiscvPtsto.v:2919), stated against a successor state whose
register `r` holds `v'` and which agrees with `σ` on every other register. -/
theorem reg_update {σ σ' : M.State} {r : Nat} {v v' : BitVec 64}
    (hr : M.reg σ' r = v') (hframe : ∀ k, k ≠ r → M.reg σ' k = M.reg σ k) :
    regInterp (GF := GF) M σ ⊢ (r ↦ᵣ v) ==∗ regInterp M σ' ∗ r ↦ᵣ v' := by
  unfold regInterp regPointsTo
  iintro ⟨%m, Hm, %Hag⟩ Hr
  imod ghost_map_update v' $$ Hm Hr with ⟨Hm, Hr⟩
  imodintro
  iframe Hr
  iexists (PartialMap.insert m r v')
  iframe Hm
  ipureintro
  intro k w hk
  by_cases hkr : r = k
  · subst hkr
    rw [LawfulPartialMap.get?_insert_eq rfl] at hk
    cases hk; exact hr
  · rw [LawfulPartialMap.get?_insert_ne hkr] at hk
    rw [hframe k (Ne.symm hkr)]
    exact Hag k w hk

theorem mem_update {σ σ' : M.State} {a : Nat} {b b' : BitVec 8}
    (ha : M.mem σ' a = b') (hframe : ∀ k, k ≠ a → M.mem σ' k = M.mem σ k) :
    memInterp (GF := GF) M σ ⊢ (a ↦ₘ b) ==∗ memInterp M σ' ∗ a ↦ₘ b' := by
  unfold memInterp memPointsTo
  iintro ⟨%m, Hm, %Hag⟩ Ha
  imod ghost_map_update b' $$ Hm Ha with ⟨Hm, Ha⟩
  imodintro
  iframe Ha
  iexists (PartialMap.insert m a b')
  iframe Hm
  ipureintro
  intro k w hk
  by_cases hka : a = k
  · subst hka
    rw [LawfulPartialMap.get?_insert_eq rfl] at hk
    cases hk; exact ha
  · rw [LawfulPartialMap.get?_insert_ne hka] at hk
    rw [hframe k (Ne.symm hka)]
    exact Hag k w hk

/-- Exclusive byte ownership is disjoint (`ghost_map_elem_ne`). -/
theorem mem_ne (a a' : Nat) (dq : DFrac) (v w : BitVec 8) :
    ⊢@{IProp GF} (a ↦ₘ v) -∗ (a' ↦ₘ{dq} w) -∗ ⌜a ≠ a'⌝ := by
  unfold memPointsTo
  iintro Ha Ha'
  iapply ghost_map_elem_ne $$ Ha Ha'

/-- A step that touches no owned register re-establishes the register bridge
unchanged. -/
theorem regInterp_frame {σ σ' : M.State} (h : ∀ k, M.reg σ' k = M.reg σ k) :
    regInterp (GF := GF) M σ ⊢ regInterp M σ' := by
  unfold regInterp
  iintro ⟨%m, Hm, %Hag⟩
  iexists m
  iframe Hm
  ipureintro
  intro k v hk
  rw [h k]; exact Hag k v hk

theorem memInterp_frame {σ σ' : M.State} (h : ∀ k, M.mem σ' k = M.mem σ k) :
    memInterp (GF := GF) M σ ⊢ memInterp M σ' := by
  unfold memInterp
  iintro ⟨%m, Hm, %Hag⟩
  iexists m
  iframe Hm
  ipureintro
  intro k v hk
  rw [h k]; exact Hag k v hk

end Rules

end VsaIris
