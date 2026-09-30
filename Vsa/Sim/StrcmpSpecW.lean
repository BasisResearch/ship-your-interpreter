import Vsa.Sim.StrcmpSpec
import Vsa.Sim.ObsAvoid

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem word_ne_byte (wa wb : BitVec 64) (h : wa ≠ wb) :
    ∃ k, k < 8 ∧ wa.extractLsb' (8*k) 8 ≠ wb.extractLsb' (8*k) 8 := by
  apply Decidable.byContradiction
  intro hc
  have hall : ∀ k, k < 8 → wa.extractLsb' (8*k) 8 = wb.extractLsb' (8*k) 8 := by
    intro k hk
    apply Decidable.byContradiction
    intro hne; exact hc ⟨k, hk, hne⟩
  apply h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hk : i / 8 < 8 := by omega
  have hib : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have heq : wa.extractLsb' (8*(i/8)) 8 = wb.extractLsb' (8*(i/8)) 8 := hall (i/8) hk
  have := congrArg (fun w => w.getLsbD (i % 8)) heq
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true hib, Bool.true_and] at this
  rwa [show 8*(i/8) + i%8 = i from by omega] at this

theorem neg_one_allOnes : (-1#64 : BitVec 64) = BitVec.allOnes 64 := by
  apply BitVec.eq_of_toNat_eq; decide

theorem strcmpWordVal_eq (w : BitVec 64) :
    (((w &&& magic7f) + magic7f) ||| (w ||| magic7f)) = strlenWordVal w := by
  show _ = (((w &&& magic7f) + magic7f) ||| w) ||| magic7f
  rw [BitVec.or_assoc]

end Vsa.Sim
