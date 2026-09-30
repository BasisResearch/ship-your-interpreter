import Vsa.Sim.EqNeDispatchSeg
import Vsa.Sim.EvalNotSim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

namespace Vsa.Sim

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem writeMap8_ld_byte (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (bs : List (BitVec 8)) (k : Nat) (hk : k < 8) :
    (writeMap8 mem a (sdData_val (bytesVal .ld bs)))[a + k]? = some (bs.getD k 0#8) := by
  obtain ⟨s0,s1,s2,s3,s4,s5,s6,s7⟩ := sdData_sext_bytes (bs.getD 0 0#8) (bs.getD 1 0#8)
    (bs.getD 2 0#8) (bs.getD 3 0#8) (bs.getD 4 0#8) (bs.getD 5 0#8) (bs.getD 6 0#8) (bs.getD 7 0#8)
  have hbv : bytesVal .ld bs = sign_extend (m := 64)
      ((((((((bs.getD 7 0#8).append (bs.getD 6 0#8)).append (bs.getD 5 0#8)).append
        (bs.getD 4 0#8)).append (bs.getD 3 0#8)).append (bs.getD 2 0#8)).append
        (bs.getD 1 0#8)).append (bs.getD 0 0#8)) := rfl
  match k, hk with
  | 0, _ => rw [Nat.add_zero, getElem_writeMap8_0, hbv, s0]
  | 1, _ => rw [getElem_writeMap8_1, hbv, s1]
  | 2, _ => rw [getElem_writeMap8_2, hbv, s2]
  | 3, _ => rw [getElem_writeMap8_3, hbv, s3]
  | 4, _ => rw [getElem_writeMap8_4, hbv, s4]
  | 5, _ => rw [getElem_writeMap8_5, hbv, s5]
  | 6, _ => rw [getElem_writeMap8_6, hbv, s6]
  | 7, _ => rw [getElem_writeMap8_7, hbv, s7]

end Vsa.Sim
