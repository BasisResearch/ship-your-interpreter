import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.EnvDefSites
import Vsa.Sim.BridgeSeg
import Vsa.Sim.EnvGetSpec3

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

/- Positive-count entry: take the nonzero polarity, load the names base,
initialize the index/cursor, and jump to the scan head. -/

/- Full-live scan initialization used by the semantic env_define composition. -/

/- One scan-head argument marshal, ending immediately before `jal strcmp`. -/

/- `strcmp == 0`: fall through into the update store. -/

/- A miss followed by a non-final index: advance and return to the scan head. -/

/- A miss at the final index: advance and branch to the capacity check. -/

/- Full-live variants used by the semantic scan loop. -/

end Vsa.Sim
