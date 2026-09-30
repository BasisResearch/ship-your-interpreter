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

abbrev gprIdx (n : Nat) : regidx := regidx.Regidx (BitVec.ofNat 5 n)

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

def gprReg : Nat → Register
  | 1 => Register.x1
  | 2 => Register.x2
  | 3 => Register.x3
  | 4 => Register.x4
  | 5 => Register.x5
  | 6 => Register.x6
  | 7 => Register.x7
  | 8 => Register.x8
  | 9 => Register.x9
  | 10 => Register.x10
  | 11 => Register.x11
  | 12 => Register.x12
  | 13 => Register.x13
  | 14 => Register.x14
  | 15 => Register.x15
  | 16 => Register.x16
  | 17 => Register.x17
  | 18 => Register.x18
  | 19 => Register.x19
  | 20 => Register.x20
  | 21 => Register.x21
  | 22 => Register.x22
  | 23 => Register.x23
  | 24 => Register.x24
  | 25 => Register.x25
  | 26 => Register.x26
  | 27 => Register.x27
  | 28 => Register.x28
  | 29 => Register.x29
  | 30 => Register.x30
  | 31 => Register.x31
  | 0 => Register.x1
  | _+32 => Register.x1

def gprGet (σ : MState) : Nat → Option (BitVec 64)
  | 1 => σ.regs.get? Register.x1
  | 2 => σ.regs.get? Register.x2
  | 3 => σ.regs.get? Register.x3
  | 4 => σ.regs.get? Register.x4
  | 5 => σ.regs.get? Register.x5
  | 6 => σ.regs.get? Register.x6
  | 7 => σ.regs.get? Register.x7
  | 8 => σ.regs.get? Register.x8
  | 9 => σ.regs.get? Register.x9
  | 10 => σ.regs.get? Register.x10
  | 11 => σ.regs.get? Register.x11
  | 12 => σ.regs.get? Register.x12
  | 13 => σ.regs.get? Register.x13
  | 14 => σ.regs.get? Register.x14
  | 15 => σ.regs.get? Register.x15
  | 16 => σ.regs.get? Register.x16
  | 17 => σ.regs.get? Register.x17
  | 18 => σ.regs.get? Register.x18
  | 19 => σ.regs.get? Register.x19
  | 20 => σ.regs.get? Register.x20
  | 21 => σ.regs.get? Register.x21
  | 22 => σ.regs.get? Register.x22
  | 23 => σ.regs.get? Register.x23
  | 24 => σ.regs.get? Register.x24
  | 25 => σ.regs.get? Register.x25
  | 26 => σ.regs.get? Register.x26
  | 27 => σ.regs.get? Register.x27
  | 28 => σ.regs.get? Register.x28
  | 29 => σ.regs.get? Register.x29
  | 30 => σ.regs.get? Register.x30
  | 31 => σ.regs.get? Register.x31
  | 0 => none
  | _+32 => none

def gprRT : (n : Nat) → BitVec 64 → RegisterType (gprReg n)
  | 1, v => v
  | 2, v => v
  | 3, v => v
  | 4, v => v
  | 5, v => v
  | 6, v => v
  | 7, v => v
  | 8, v => v
  | 9, v => v
  | 10, v => v
  | 11, v => v
  | 12, v => v
  | 13, v => v
  | 14, v => v
  | 15, v => v
  | 16, v => v
  | 17, v => v
  | 18, v => v
  | 19, v => v
  | 20, v => v
  | 21, v => v
  | 22, v => v
  | 23, v => v
  | 24, v => v
  | 25, v => v
  | 26, v => v
  | 27, v => v
  | 28, v => v
  | 29, v => v
  | 30, v => v
  | 31, v => v
  | 0, v => v
  | _+32, v => v

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

theorem rX_src (σ : MState) (pc : BitVec 64) :
    ∀ (n : Nat), n ≤ 31 → ∀ (v : BitVec 64), srcPin σ n v →
    (rX_bits (gprIdx n)).run (afterNextPC (afterPrelude σ) pc)
      = .ok v (afterNextPC (afterPrelude σ) pc)
  | 0, _, v, h => by rw [show v = 0#64 from h]; exact rX_bits_zero _
  | 1, _, v, h => rX_bits_x1 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 2, _, v, h => rX_bits_x2 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 3, _, v, h => rX_bits_x3 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 4, _, v, h => rX_bits_x4 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 5, _, v, h => rX_bits_x5 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 6, _, v, h => rX_bits_x6 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 7, _, v, h => rX_bits_x7 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 8, _, v, h => rX_bits_x8 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 9, _, v, h => rX_bits_x9 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 10, _, v, h => rX_bits_x10 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 11, _, v, h => rX_bits_x11 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 12, _, v, h => rX_bits_x12 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 13, _, v, h => rX_bits_x13 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 14, _, v, h => rX_bits_x14 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 15, _, v, h => rX_bits_x15 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 16, _, v, h => rX_bits_x16 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 17, _, v, h => rX_bits_x17 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 18, _, v, h => rX_bits_x18 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 19, _, v, h => rX_bits_x19 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 20, _, v, h => rX_bits_x20 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 21, _, v, h => rX_bits_x21 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 22, _, v, h => rX_bits_x22 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 23, _, v, h => rX_bits_x23 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 24, _, v, h => rX_bits_x24 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 25, _, v, h => rX_bits_x25 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 26, _, v, h => rX_bits_x26 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 27, _, v, h => rX_bits_x27 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 28, _, v, h => rX_bits_x28 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 29, _, v, h => rX_bits_x29 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 30, _, v, h => rX_bits_x30 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | 31, _, v, h => rX_bits_x31 _ v (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact h)
  | _+32, hn, _, _ => absurd hn (by omega)

theorem wX_gpr (s : MState) (d : BitVec 64) :
    ∀ (n : Nat), 1 ≤ n → n ≤ 31 →
    (wX_bits (gprIdx n) d).run s
      = .ok () {s with regs := s.regs.insert (gprReg n) (gprRT n d)}
  | 0, h, _ => absurd h (by omega)
  | 1, _, _ => wX_bits_x1 s d
  | 2, _, _ => wX_bits_x2 s d
  | 3, _, _ => wX_bits_x3 s d
  | 4, _, _ => wX_bits_x4 s d
  | 5, _, _ => wX_bits_x5 s d
  | 6, _, _ => wX_bits_x6 s d
  | 7, _, _ => wX_bits_x7 s d
  | 8, _, _ => wX_bits_x8 s d
  | 9, _, _ => wX_bits_x9 s d
  | 10, _, _ => wX_bits_x10 s d
  | 11, _, _ => wX_bits_x11 s d
  | 12, _, _ => wX_bits_x12 s d
  | 13, _, _ => wX_bits_x13 s d
  | 14, _, _ => wX_bits_x14 s d
  | 15, _, _ => wX_bits_x15 s d
  | 16, _, _ => wX_bits_x16 s d
  | 17, _, _ => wX_bits_x17 s d
  | 18, _, _ => wX_bits_x18 s d
  | 19, _, _ => wX_bits_x19 s d
  | 20, _, _ => wX_bits_x20 s d
  | 21, _, _ => wX_bits_x21 s d
  | 22, _, _ => wX_bits_x22 s d
  | 23, _, _ => wX_bits_x23 s d
  | 24, _, _ => wX_bits_x24 s d
  | 25, _, _ => wX_bits_x25 s d
  | 26, _, _ => wX_bits_x26 s d
  | 27, _, _ => wX_bits_x27 s d
  | 28, _, _ => wX_bits_x28 s d
  | 29, _, _ => wX_bits_x29 s d
  | 30, _, _ => wX_bits_x30 s d
  | 31, _, _ => wX_bits_x31 s d
  | _+32, _, h => absurd h (by omega)

theorem obs_gpr_rd {σ' σ : MState} {pc vm : BitVec 64} :
    ∀ (n : Nat), 1 ≤ n → n ≤ 31 → ∀ (v : BitVec 64),
    ReadsLikePost σ' (sigmaPost_alu σ pc vm (gprReg n) (gprRT n v)) →
    gprGet σ' n = some v
  | 0, h, _, _, _ => absurd h (by omega)
  | 1, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 2, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 3, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 4, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 5, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 6, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 7, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 8, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 9, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 10, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 11, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 12, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 13, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 14, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 15, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 16, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 17, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 18, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 19, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 20, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 21, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 22, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 23, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 24, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 25, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 26, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 27, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 28, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 29, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 30, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | 31, _, _, v, hobs => obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  | _+32, _, h, _, _ => absurd h (by omega)

theorem obs_gpr_other {σ' σ : MState} {pc vm : BitVec 64} {n : Nat} {v : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm (gprReg n) (gprRT n v))) :
    ∀ (m : Nat), 1 ≤ m → m ≤ 31 → (gprReg n == gprReg m) = false →
    ∀ (w : BitVec 64), gprGet σ m = some w → gprGet σ' m = some w
  | 0, h, _, _, _, _ => absurd h (by omega)
  | 1, _, _, hne, w, h => obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 2, _, _, hne, w, h => obs_alu_other hobs Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 3, _, _, hne, w, h => obs_alu_other hobs Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 4, _, _, hne, w, h => obs_alu_other hobs Register.x4 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 5, _, _, hne, w, h => obs_alu_other hobs Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 6, _, _, hne, w, h => obs_alu_other hobs Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 7, _, _, hne, w, h => obs_alu_other hobs Register.x7 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 8, _, _, hne, w, h => obs_alu_other hobs Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 9, _, _, hne, w, h => obs_alu_other hobs Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 10, _, _, hne, w, h => obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 11, _, _, hne, w, h => obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 12, _, _, hne, w, h => obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 13, _, _, hne, w, h => obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 14, _, _, hne, w, h => obs_alu_other hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 15, _, _, hne, w, h => obs_alu_other hobs Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 16, _, _, hne, w, h => obs_alu_other hobs Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 17, _, _, hne, w, h => obs_alu_other hobs Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 18, _, _, hne, w, h => obs_alu_other hobs Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 19, _, _, hne, w, h => obs_alu_other hobs Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 20, _, _, hne, w, h => obs_alu_other hobs Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 21, _, _, hne, w, h => obs_alu_other hobs Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 22, _, _, hne, w, h => obs_alu_other hobs Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 23, _, _, hne, w, h => obs_alu_other hobs Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 24, _, _, hne, w, h => obs_alu_other hobs Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 25, _, _, hne, w, h => obs_alu_other hobs Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 26, _, _, hne, w, h => obs_alu_other hobs Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 27, _, _, hne, w, h => obs_alu_other hobs Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 28, _, _, hne, w, h => obs_alu_other hobs Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 29, _, _, hne, w, h => obs_alu_other hobs Register.x29 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 30, _, _, hne, w, h => obs_alu_other hobs Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | 31, _, _, hne, w, h => obs_alu_other hobs Register.x31 (by decide) (by decide) (by decide) (by decide) (by decide) hne (by decide) (by decide) h
  | _+32, _, h, _, _, _ => absurd h (by omega)

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

inductive AKind where
  | addi : AKind
  | add  : AKind
deriving DecidableEq

structure AInstr where
  pc   : BitVec 64
  word : BitVec 32
  b0   : BitVec 8
  b1   : BitVec 8
  b2   : BitVec 8
  b3   : BitVec 8
  kind : AKind
  rd   : Nat
  rs1  : Nat
  rs2  : Nat
  imm  : BitVec 12

def endPC (pc0 : BitVec 64) : List AInstr → BitVec 64
  | [] => pc0
  | a :: r => endPC (BitVec.addInt a.pc 4) r

abbrev SrcOK (n : Nat) (dom : List Nat) : Prop :=
  n ≤ 31 ∧ (n = 0 ∨ n ∈ dom)

abbrev InstrOK (pc0 : BitVec 64) (dom : List Nat) (a : AInstr) : Prop :=
  a.pc.toNat = pc0.toNat ∧
  (((a.b3.append a.b2).append a.b1).append a.b0).toNat = a.word.toNat ∧
  (Sail.BitVec.extractLsb (((a.b3.append a.b2).append a.b1).append a.b0) 1 0).toNat
    = (0b11#2 : BitVec 2).toNat ∧
  0x80000000 ≤ a.pc.toNat ∧
  a.pc.toNat + 4 ≤ tohostAddr ∧
  a.pc.toNat % 4 = 0 ∧
  1 ≤ a.rd ∧ a.rd ≤ 31 ∧
  SrcOK a.rs1 dom ∧
  (¬ a.kind = AKind.add ∨ SrcOK a.rs2 dom)

def BlockOK (pc0 : BitVec 64) (dom : List Nat) : List AInstr → Prop
  | [] => True
  | a :: r => InstrOK pc0 dom a ∧ BlockOK (BitVec.addInt a.pc 4) (a.rd :: dom) r

instance instDecBlockOK (pc0 : BitVec 64) (dom : List Nat) :
    (is : List AInstr) → Decidable (BlockOK pc0 dom is)
  | [] => isTrue trivial
  | a :: r =>
    have : Decidable (BlockOK (BitVec.addInt a.pc 4) (a.rd :: dom) r) :=
      instDecBlockOK _ _ r
    inferInstanceAs (Decidable (_ ∧ _))

end Vsa.Sim
