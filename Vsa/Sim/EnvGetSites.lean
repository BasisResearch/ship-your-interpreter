import Vsa.Sim.ValueSites
import Vsa.Sim.Code.Env_get
import Vsa.Sim.DecodeNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem w_0004b503_eg : (((0x00#8).append (0x04#8)).append (0xb5#8)).append (0x03#8) = (0x0004b503#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0004b503_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x04#8)).append (0xb5#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

end Vsa.Sim
