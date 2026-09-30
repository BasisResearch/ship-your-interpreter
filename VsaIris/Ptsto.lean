import VsaIris.Machine
import Iris.ProgramLogic.TotalWeakestPre
import Iris.ProgramLogic.TotalLifting
import Iris.Instances.Lib.GhostMap
import Std.Data.ExtTreeMap

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

abbrev NatMap := fun V => Std.ExtTreeMap Nat V compare

class MachPreG (GF : BundledGFunctors) where
  regG : GhostMapG GF Nat (BitVec 64) NatMap
  memG : GhostMapG GF Nat (BitVec 8) NatMap

  ctlG : GhostMapG GF Nat Nat NatMap

  conG : GhostMapG GF Nat String NatMap

attribute [reducible, instance] MachPreG.regG MachPreG.memG MachPreG.ctlG MachPreG.conG

class MachGpreS (GF : BundledGFunctors) extends InvGpreS GF where
  machPre : MachPreG GF

attribute [reducible, instance] MachGpreS.machPre

class MachGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  [invGS : InvGS_gen hlc GF]
  machPre : MachPreG GF
  regName : GName
  memName : GName
  ctlName : GName

  conName : GName

attribute [reducible, instance] MachGS.machPre
attribute [implicit_reducible, instance] MachGS.invGS

section Defs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

def regPointsTo (r : Nat) (dq : DFrac) (v : BitVec 64) : IProp GF :=
  ghost_map_elem G.regName dq r v

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

def RegAgree (m : NatMap (BitVec 64)) (σ : M.State) : Prop :=
  ∀ k v, PartialMap.get? m k = some v → M.reg σ k = v

def MemAgree (m : NatMap (BitVec 8)) (σ : M.State) : Prop :=
  ∀ k v, PartialMap.get? m k = some v → M.mem σ k = v

def ConAgree (m : NatMap String) (σ : M.State) : Prop :=
  ∀ v, PartialMap.get? m 0 = some v → M.out σ = v

def regInterp (σ : M.State) : IProp GF :=
  iprop(∃ m, ghost_map_auth G.regName (DFrac.own 1) m ∗ ⌜RegAgree M m σ⌝)

def memInterp (σ : M.State) : IProp GF :=
  iprop(∃ m, ghost_map_auth G.memName (DFrac.own 1) m ∗ ⌜MemAgree M m σ⌝)

def conInterp (σ : M.State) : IProp GF :=
  iprop(∃ m, ghost_map_auth G.conName (DFrac.own 1) m ∗ ⌜ConAgree M m σ⌝)

def mstateInterp (σ : M.State) : IProp GF :=
  iprop(regInterp M σ ∗ memInterp M σ ∗ conInterp M σ ∗ ⌜M.ok σ⌝)

def AgreeOk (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8)) (σ0 : M.State) : Prop :=
  RegAgree M mr σ0 ∧ MemAgree M mm σ0 ∧ M.ok σ0

def lagInterp (j : Nat) (σ : M.State) : IProp GF :=
  iprop(∃ mr mm mo, ghost_map_auth G.regName (DFrac.own 1) mr ∗
    ghost_map_auth G.memName (DFrac.own 1) mm ∗ ghost_map_auth G.conName (DFrac.own 1) mo ∗
    ⌜∃ σ0, AgreeOk M mr mm σ0 ∧ ConAgree M mo σ0 ∧ ReachesN M j σ0 σ⌝)

def consoleOwn (s : String) : IProp GF := ghost_map_elem G.conName (DFrac.own 1) 0 s

def ctlAt (j : Nat) : IProp GF := ghost_map_elem G.ctlName (DFrac.own 1) 0 j

abbrev cpuTok : IProp GF := ctlAt 0

def fullInterp (σ : M.State) : IProp GF :=
  iprop(∃ (c : NatMap Nat) (j : Nat), ghost_map_auth G.ctlName (DFrac.own 1) c ∗
    ⌜PartialMap.get? c 0 = some j⌝ ∗ lagInterp M j σ)

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

theorem mem_ne (a a' : Nat) (dq : DFrac) (v w : BitVec 8) :
    ⊢@{IProp GF} (a ↦ₘ v) -∗ (a' ↦ₘ{dq} w) -∗ ⌜a ≠ a'⌝ := by
  unfold memPointsTo
  iintro Ha Ha'
  iapply ghost_map_elem_ne $$ Ha Ha'

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
