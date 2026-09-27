import Vsa.Sim.rows.EnvDefineAppendExact
import Vsa.Sim.EnvDefBridges4
import Vsa.Sim.EnvGetSpec7
import Vsa.Sim.ReallocPublicFrame
import Vsa.Sim.AllocSuccessAdapters
import Vsa.Sim.AllocReserveTransport

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.MemRepr
open Vsa.RuntimeRepr
open Vsa.Logic (Triple)

namespace Vsa.Sim

@[simp] private theorem growLine0 : mkLine 0x80002bc0#64 0x008a3783#32 =
    ⟨0x80002bc0#64, 0x008a3783#32, 0x83#8, 0x37#8, 0x8a#8, 0x00#8,
      .ld, 15, 20, 0, 0x008#12⟩ := by rfl

@[simp] private theorem growLine1 : mkLine 0x80002bc4#64 0x00aa3823#32 =
    ⟨0x80002bc4#64, 0x00aa3823#32, 0x23#8, 0x38#8, 0xaa#8, 0x00#8,
      .sd, 0, 20, 10, 0x010#12⟩ := by rfl

end Vsa.Sim
