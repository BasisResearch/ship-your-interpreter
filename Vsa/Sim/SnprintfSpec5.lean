import Vsa.Sim.KeepRegs
import Vsa.Sim.Code.Strcpy
import Vsa.Sim.DecodeNF
import Vsa.Sim.SnprintfSpec
import Vsa.Sim.StrlenMagic

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

def entryTop (vsp : BitVec 64) : BitVec 64 := vsp + sign_extend (m := 64) (0x15c#12)

theorem getElem?_writeMap8_out (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat)
    (d : BitVec (8 * 8)) (a : Nat) (ha : a < k ∨ k + 8 ≤ a) :
    (writeMap8 mem k d)[a]? = mem[a]? := by
  show ((((((((mem.insert k _).insert (k+1) _).insert (k+2) _).insert (k+3) _).insert
    (k+4) _).insert (k+5) _).insert (k+6) _).insert (k+7) _)[a]? = mem[a]?
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

end Vsa.Sim
