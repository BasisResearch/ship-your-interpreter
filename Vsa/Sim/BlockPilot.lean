import Vsa.Sim.RegPins
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.Execute
import Vsa.Sim.RegAccess

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev GRegs := List (Nat × BitVec 64)

def keysG : GRegs → List Nat
  | [] => []
  | (n, _) :: L => n :: keysG L

def lookupG (n : Nat) : GRegs → Option (BitVec 64)
  | [] => none
  | (m, v) :: L => if m = n then some v else lookupG n L

def eraseG (n : Nat) : GRegs → GRegs
  | [] => []
  | (m, v) :: L => if m = n then eraseG n L else (m, v) :: eraseG n L

abbrev KeysOK (d : List Nat) : Prop := ∀ n ∈ d, 1 ≤ n ∧ n ≤ 31

def GHolds (σ : MState) : GRegs → Prop
  | [] => True
  | (n, v) :: L => gprGet σ n = some v ∧ GHolds σ L

def srcPin (σ : MState) : Nat → BitVec 64 → Prop
  | 0, v => v = 0#64
  | m+1, v => gprGet σ (m+1) = some v

def srcVal (n : Nat) (L : GRegs) : BitVec 64 :=
  match n with
  | 0 => 0#64
  | m+1 => (lookupG (m+1) L).getD 0#64

theorem gpr_rd_ok : ∀ n, n < 32 → 1 ≤ n →
    ((gprReg n == Register.nextPC) = false ∧
     (gprReg n == Register.minstret_increment) = false ∧
     (gprReg n == Register.minstret) = false ∧
     (gprReg n == Register.hart_state) = false ∧
     NonPinned (gprReg n)) := by decide

theorem gprReg_beq_false : ∀ n, n < 32 → ∀ m, m < 32 → 1 ≤ n → 1 ≤ m → n ≠ m →
    (gprReg n == gprReg m) = false := by decide

theorem gprGet_afterNextPC (σ : MState) (pc : BitVec 64) (n : Nat) (h1 : 1 ≤ n) (h31 : n ≤ 31) :
    gprGet (afterNextPC (afterPrelude σ) pc) n = gprGet σ n := by
  gpr_cases n => exact get?_afterNextPC σ pc _ (by decide) (by decide)

theorem rX_src (σ : MState) (pc : BitVec 64) :
    ∀ (n : Nat), n ≤ 31 → ∀ (v : BitVec 64), srcPin σ n v →
    (rX_bits (gprIdx n)).run (afterNextPC (afterPrelude σ) pc)
      = .ok v (afterNextPC (afterPrelude σ) pc)
  | 0, _, v, h => by rw [show v = 0#64 from h]; exact rX_bits_zero _
  | m+1, hn, v, h => rX_bits_gpr _ (m+1) (by omega) hn v
      ((gprGet_afterNextPC σ pc (m+1) (by omega) hn).trans h)

theorem wX_gpr (s : MState) (d : BitVec 64) :
    ∀ (n : Nat), 1 ≤ n → n ≤ 31 →
    (wX_bits (gprIdx n) d).run s
      = .ok () {s with regs := s.regs.insert (gprReg n) (gprRT n d)} :=
  wX_bits_gpr s d

theorem obs_gpr_rd {σ' σ : MState} {pc vm : BitVec 64} :
    ∀ (n : Nat), 1 ≤ n → n ≤ 31 → ∀ (v : BitVec 64),
    ReadsLikePost σ' (sigmaPost_alu σ pc vm (gprReg n) (gprRT n v)) →
    gprGet σ' n = some v := by
  intro n h1 h31 v hobs
  gpr_cases n => exact obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)

theorem obs_gpr_other {σ' σ : MState} {pc vm : BitVec 64} {n : Nat} {v : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm (gprReg n) (gprRT n v))) :
    ∀ (m : Nat), 1 ≤ m → m ≤ 31 → (gprReg n == gprReg m) = false →
    ∀ (w : BitVec 64), gprGet σ m = some w → gprGet σ' m = some w := by
  intro m h1 h31 hne w h
  gpr_cases m => refine obs_alu_other hobs _ ?_ ?_ ?_ ?_ ?_ hne ?_ ?_ h <;> decide

theorem gholds_lookup {σ : MState} {n : Nat} {v : BitVec 64} :
    ∀ (L : GRegs), GHolds σ L → lookupG n L = some v → gprGet σ n = some v := by
  intro L
  induction L with
  | nil => intro _ hlk; exact nomatch hlk
  | cons p L ih =>
    obtain ⟨m, w⟩ := p
    intro hL hlk
    simp only [lookupG] at hlk
    split at hlk
    · next heq => cases hlk; exact heq ▸ hL.1
    · exact ih hL.2 hlk

theorem lookup_of_mem {n : Nat} :
    ∀ (L : GRegs), n ∈ keysG L → ∃ v, lookupG n L = some v := by
  intro L
  induction L with
  | nil => intro h; exact nomatch h
  | cons p L ih =>
    obtain ⟨m, w⟩ := p
    intro h
    simp only [lookupG]
    split
    · exact ⟨w, rfl⟩
    · next hne =>
      have h' : n ∈ m :: keysG L := h
      cases h' with
      | head => exact absurd rfl hne
      | tail _ htl => exact ih htl

theorem mem_of_mem_keysG_eraseG {n k : Nat} :
    ∀ (L : GRegs), k ∈ keysG (eraseG n L) → k ∈ keysG L := by
  intro L
  induction L with
  | nil => intro h; exact nomatch h
  | cons p L ih =>
    obtain ⟨m, w⟩ := p
    intro h
    simp only [eraseG] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · have h' : k ∈ m :: keysG (eraseG n L) := h
      cases h' with
      | head => exact List.mem_cons_self ..
      | tail _ htl => exact List.mem_cons_of_mem _ (ih htl)

theorem mem_keysG_eraseG {n k : Nat} (hne : k ≠ n) :
    ∀ (L : GRegs), k ∈ keysG L → k ∈ keysG (eraseG n L) := by
  intro L
  induction L with
  | nil => intro h; exact nomatch h
  | cons p L ih =>
    obtain ⟨m, w⟩ := p
    intro h
    have h' : k ∈ m :: keysG L := h
    simp only [eraseG]
    split
    · next heq =>
      cases h' with
      | head => exact absurd heq hne
      | tail _ htl => exact ih htl
    · cases h' with
      | head => exact List.mem_cons_self ..
      | tail _ htl => exact List.mem_cons_of_mem _ (ih htl)

theorem gholds_eraseG {σ' σ : MState} {pc vm : BitVec 64} {n : Nat} {v : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm (gprReg n) (gprRT n v)))
    (hn1 : 1 ≤ n) (hn31 : n ≤ 31) :
    ∀ (L : GRegs), KeysOK (keysG L) → GHolds σ L → GHolds σ' (eraseG n L) := by
  intro L
  induction L with
  | nil => intro _ _; exact trivial
  | cons p L ih =>
    obtain ⟨m, w⟩ := p
    intro hK hL
    simp only [eraseG]
    split
    · exact ih (fun k hk => hK k (List.mem_cons_of_mem _ hk)) hL.2
    · next hne =>
      have hm := hK m (List.mem_cons_self ..)
      exact ⟨obs_gpr_other hobs m hm.1 hm.2
        (gprReg_beq_false n (by omega) m (by omega) hn1 hm.1 (fun e => hne e.symm)) w hL.1,
        ih (fun k hk => hK k (List.mem_cons_of_mem _ hk)) hL.2⟩

theorem srcPin_srcVal (σ : MState) (L : GRegs) :
    ∀ (n : Nat), (n = 0 ∨ n ∈ keysG L) → GHolds σ L → srcPin σ n (srcVal n L)
  | 0, _, _ => rfl
  | m+1, hok, hL => by
    obtain ⟨v, hv⟩ := lookup_of_mem L (hok.resolve_left (Nat.succ_ne_zero m))
    show gprGet σ (m+1) = some ((lookupG (m+1) L).getD 0#64)
    rw [hv]
    exact gholds_lookup L hL hv

abbrev SrcOK (n : Nat) (dom : List Nat) : Prop :=
  n ≤ 31 ∧ (n = 0 ∨ n ∈ dom)

end Vsa.Sim
