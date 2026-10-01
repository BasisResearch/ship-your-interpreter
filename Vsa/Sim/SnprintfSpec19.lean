import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.DecodeNF
import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.StrcmpSpecW3
import Vsa.Sim.ValueEqualSpec2
import Vsa.Sim.EnvNewSpec

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem word4_eq_sp (w : BitVec 32) :
    ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
      (w.extractLsb' 0 8) : BitVec (8 * 4)) = w := by
  apply BitVec.eq_of_toNat_eq
  rw [word_toNat_recon]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega

theorem lw_cap_reassemble_sp (w : BitVec 32) :
    (sign_extend (m := 64)
      ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
        (w.extractLsb' 0 8) : BitVec (8 * 4)) : BitVec 64) = sign_extend (m := 64) w :=
  congrArg _ (word4_eq_sp w)

def Pin8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 64) : Prop :=
  mem[a]? = some ((sdData_val v).extractLsb' 0 8) ∧
  mem[a + 1]? = some ((sdData_val v).extractLsb' 8 8) ∧
  mem[a + 2]? = some ((sdData_val v).extractLsb' 16 8) ∧
  mem[a + 3]? = some ((sdData_val v).extractLsb' 24 8) ∧
  mem[a + 4]? = some ((sdData_val v).extractLsb' 32 8) ∧
  mem[a + 5]? = some ((sdData_val v).extractLsb' 40 8) ∧
  mem[a + 6]? = some ((sdData_val v).extractLsb' 48 8) ∧
  mem[a + 7]? = some ((sdData_val v).extractLsb' 56 8)

end Vsa.Sim
