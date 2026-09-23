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
  device conjunct is dropped. The client-visible form `mstateInterp` also
  carries the model's global invariant `M.ok`.

**Lag.** VSA's instruction facts are *segment* facts: a reflected run of
`n` instructions with an end-state frame, and no statement about the states in
between. The state interpretation therefore allows the ghost maps to agree
with a state `j` steps in the past (`lagInterp j`), where `j` is recorded in a
third ghost map (`ctl`, key 0). Only the holder of the key-0 cell can make
`j` nonzero, and every client holds it at value 0 (`cpuTok`, handed out by
`mTWP`), so a client always sees `j = 0`, that is `mstateInterp`. The segment
rule `wp_run` (Step.lean) moves the counter while a segment runs.
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
  /-- Control ghost map; key 0 holds the lag counter. -/
  ctlG : GhostMapG GF Nat Nat NatMap
  /-- Console ghost map; key 0 holds the output printed so far. -/
  conG : GhostMapG GF Nat String NatMap

attribute [reducible, instance] MachPreG.regG MachPreG.memG MachPreG.ctlG MachPreG.conG

class MachGpreS (GF : BundledGFunctors) extends InvGpreS GF where
  machPre : MachPreG GF

attribute [reducible, instance] MachGpreS.machPre

/-- `riscvGS` (RiscvPtsto.v:691), cut to the two names a single hart needs. -/
class MachGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  [invGS : InvGS_gen hlc GF]
  machPre : MachPreG GF
  regName : GName
  memName : GName
  ctlName : GName
  /-- The console cell (INTERP_DESIGN.md §2 F2). -/
  conName : GName

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

/-- The console cell agrees with the model's output where defined (key 0). -/
def ConAgree (m : NatMap String) (σ : M.State) : Prop :=
  ∀ v, PartialMap.get? m 0 = some v → M.out σ = v

/-- `reg_interp_at` (RiscvPtsto.v:2213). -/
def regInterp (σ : M.State) : IProp GF :=
  iprop(∃ m, ghost_map_auth G.regName (DFrac.own 1) m ∗ ⌜RegAgree M m σ⌝)

def memInterp (σ : M.State) : IProp GF :=
  iprop(∃ m, ghost_map_auth G.memName (DFrac.own 1) m ∗ ⌜MemAgree M m σ⌝)

/-- The console bridge. MachCSL's console authority (paper §7.5, Figure 28
`cons_auth`) sits in the state interpretation the same way. -/
def conInterp (σ : M.State) : IProp GF :=
  iprop(∃ m, ghost_map_auth G.conName (DFrac.own 1) m ∗ ⌜ConAgree M m σ⌝)

/-- `mstate_interp` (RiscvPtsto.v:2340) without the device conjunct, plus the
model's global invariant. This is what clients see. -/
def mstateInterp (σ : M.State) : IProp GF :=
  iprop(regInterp M σ ∗ memInterp M σ ∗ conInterp M σ ∗ ⌜M.ok σ⌝)

/-- The ghost maps agree with `σ0`, which satisfies the global invariant. -/
def AgreeOk (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8)) (σ0 : M.State) : Prop :=
  RegAgree M mr σ0 ∧ MemAgree M mm σ0 ∧ M.ok σ0

/-- The ghost maps agree with a state `j` steps before `σ`. -/
def lagInterp (j : Nat) (σ : M.State) : IProp GF :=
  iprop(∃ mr mm mo, ghost_map_auth G.regName (DFrac.own 1) mr ∗
    ghost_map_auth G.memName (DFrac.own 1) mm ∗ ghost_map_auth G.conName (DFrac.own 1) mo ∗
    ⌜∃ σ0, AgreeOk M mr mm σ0 ∧ ConAgree M mo σ0 ∧ ReachesN M j σ0 σ⌝)

/-- The console cell: the output printed so far is `s`. Exclusive. Holding
it is the only way to print (`wp_runOut`, Step.lean), and the halt rule reads
the exit's output off it (`wp_halt_console`). -/
def consoleOwn (s : String) : IProp GF := ghost_map_elem G.conName (DFrac.own 1) 0 s

/-- The console cell is exclusive: there is one console. -/
theorem consoleOwn_excl (s s' : String) : consoleOwn (GF := GF) s ∗ consoleOwn s' ⊢ False := by
  unfold consoleOwn
  iintro ⟨H1, H2⟩
  ihave %h := ghost_map_elem_ne $$ H1 H2
  exact absurd rfl h

/-- The key-0 control cell at lag `j`. -/
def ctlAt (j : Nat) : IProp GF := ghost_map_elem G.ctlName (DFrac.own 1) 0 j

/-- The CPU token: the control cell at lag 0. `mTWP` hands it to its prover. -/
abbrev cpuTok : IProp GF := ctlAt 0

/-- The full state interpretation: the lag counter and the lagging bridges. -/
def fullInterp (σ : M.State) : IProp GF :=
  iprop(∃ (c : NatMap Nat) (j : Nat), ghost_map_auth G.ctlName (DFrac.own 1) c ∗
    ⌜PartialMap.get? c 0 = some j⌝ ∗ lagInterp M j σ)

/-- The `IrisGS` instance (RiscvPtsto.v:2622 §3): no later credits per
step, no forks, and the state interpretation ignores the step and thread
counters. -/
instance machIrisGS : IrisGS_gen hlc (MExprOf M) GF where
  invGS := G.invGS
  stateInterp σ _ _ _ := fullInterp M σ
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

/-- At lag zero the lagging bridges are exactly the client-visible ones. -/
theorem lagInterp_zero {σ : M.State} : lagInterp (GF := GF) M 0 σ ⊣⊢ mstateInterp M σ := by
  unfold lagInterp mstateInterp regInterp memInterp conInterp
  constructor
  · iintro ⟨%mr, %mm, %mo, Hr, Hm, Ho, %h⟩
    obtain ⟨σ0, ⟨hr, hm, hok⟩, ho, hre⟩ := h
    cases hre.zero_eq
    isplitl [Hr]
    · iexists mr; iframe Hr; ipureintro; exact hr
    isplitl [Hm]
    · iexists mm; iframe Hm; ipureintro; exact hm
    isplitl [Ho]
    · iexists mo; iframe Ho; ipureintro; exact ho
    ipureintro; exact hok
  · iintro ⟨⟨%mr, Hr, %hr⟩, ⟨%mm, Hm, %hm⟩, ⟨%mo, Ho, %ho⟩, %hok⟩
    iexists mr, mm, mo
    iframe Hr Hm Ho
    ipureintro
    exact ⟨σ, ⟨hr, hm, hok⟩, ho, .zero σ⟩

/-- A client holding the CPU token sees lag zero. -/
theorem fullInterp_cpu {σ : M.State} :
    fullInterp (GF := GF) M σ ⊢ cpuTok -∗
      ∃ c : NatMap Nat, ghost_map_auth G.ctlName (DFrac.own 1) c ∗ ⌜PartialMap.get? c 0 = some 0⌝ ∗
        cpuTok ∗ mstateInterp M σ := by
  unfold fullInterp
  iintro ⟨%c, %j, Hc, %hj, Hl⟩ Ht
  unfold cpuTok ctlAt
  ihave %hl := ghost_map_lookup $$ Hc Ht
  rw [hj] at hl
  cases hl
  iexists c
  iframe Hc Ht
  isplitr
  · ipureintro; exact hj
  iapply lagInterp_zero.1 $$ Hl

/-- Rebuild the full interpretation at lag zero. -/
theorem fullInterp_of_cpu {σ : M.State} (c : NatMap Nat) (hc : PartialMap.get? c 0 = some 0) :
    ghost_map_auth (GF := GF) G.ctlName (DFrac.own 1) c ∗ mstateInterp M σ ⊢ fullInterp M σ := by
  unfold fullInterp
  iintro ⟨Hc, Hs⟩
  iexists c, 0
  iframe Hc
  isplitr
  · ipureintro; exact hc
  iapply lagInterp_zero.2 $$ Hs

end Rules

end VsaIris
