import Vsa.Sim.KeepRegs
import Vsa.Sim.Code.Strcpy
import Vsa.Sim.DecodeTable.Batch01Part02
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch01Part27
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch02Part07
import Vsa.Sim.DecodeTable.Batch02Part09
import Vsa.Sim.DecodeTable.Batch02Part15
import Vsa.Sim.DecodeTable.Batch02Part27
import Vsa.Sim.DecodeTable.Batch02Part30
import Vsa.Sim.DecodeTable.Batch03Part02
import Vsa.Sim.DecodeTable.Batch03Part06
import Vsa.Sim.DecodeTable.Batch03Part09
import Vsa.Sim.DecodeTable.Batch03Part12
import Vsa.Sim.DecodeTable.Batch03Part13
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch03Part27
import Vsa.Sim.DecodeTable.Batch03Part29
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part17
import Vsa.Sim.DecodeTable.Batch04Part18
import Vsa.Sim.DecodeTable.Batch04Part19
import Vsa.Sim.DecodeTable.Batch04Part22
import Vsa.Sim.DecodeTable.Batch04Part23
import Vsa.Sim.DecodeTable.Batch04Part25
import Vsa.Sim.DecodeTable.Batch04Part26
import Vsa.Sim.DecodeTable.Batch04Part32
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch06Part23
import Vsa.Sim.DecodeTable.Batch06Part24
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch06Part29
import Vsa.Sim.DecodeTable.Batch07Part02
import Vsa.Sim.DecodeTable.Batch07Part06
import Vsa.Sim.DecodeTable.Batch07Part09
import Vsa.Sim.DecodeTable.Batch07Part14
import Vsa.Sim.DecodeTable.Batch07Part16
import Vsa.Sim.DecodeTable.Batch07Part20
import Vsa.Sim.DecodeTable.Batch07Part27
import Vsa.Sim.DecodeTable.Batch08Part07
import Vsa.Sim.DecodeTable.Batch08Part17
import Vsa.Sim.DecodeTable.Batch08Part23
import Vsa.Sim.DecodeTable.Batch09Part09
import Vsa.Sim.DecodeTable.Batch09Part12
import Vsa.Sim.DecodeTable.Batch10Part06
import Vsa.Sim.DecodeTable.Batch10Part14
import Vsa.Sim.DecodeTable.Batch11Part17
import Vsa.Sim.DecodeTable.Batch11Part23
import Vsa.Sim.DecodeTable.Batch13Part06
import Vsa.Sim.DecodeTable.Batch14Part08
import Vsa.Sim.DecodeTable.Batch14Part10
import Vsa.Sim.DecodeTable.Batch16Part03
import Vsa.Sim.DecodeTable.Batch16Part10
import Vsa.Sim.DecodeTable.Batch16Part12
import Vsa.Sim.DecodeTable.Batch16Part18
import Vsa.Sim.DecodeTable.Batch16Part31
import Vsa.Sim.SnprintfSpec
import Vsa.Sim.StrlenMagic

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

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
