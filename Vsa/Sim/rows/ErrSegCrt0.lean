import Vsa.Sim.DeriveCase
import Vsa.Sim.BlockTactics
import Vsa.Sim.ErrorSim
import Vsa.Sim.HtifLift

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps output)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 800000

#derive_case crt0JSeg chain
  [] terminator ⟨0x80000038#64, 0x72c0406f#32, 0x6f#8, 0x40#8, 0xc0#8, 0x72#8,
      .j, 0, 0, 0#13, 0x0472c#21, 0#12⟩

end Vsa.Sim
