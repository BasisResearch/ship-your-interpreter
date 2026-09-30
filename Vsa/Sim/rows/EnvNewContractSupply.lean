import Vsa.Sim.AllocMallocAdapters
import Vsa.Sim.AllocReserveTransport
import Vsa.Sim.HelperCallEnvNew
import Vsa.Sim.EnvNewRetained
import Vsa.Sim.EnvNewSuccessSuffix
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.BridgeSegFramed
import Vsa.Sim.rows.CallClosureEnvNewMarshal
import Vsa.Sim.RuntimeOwnershipTransport
import Vsa.Sim.RuntimeOwnershipAllocation
import Vsa.Sim.AllocOff
import Vsa.Sim.AllocRuns
import Vsa.Sim.StoreInvariant
import Vsa.Sim.MemPresence
import Vsa.Sim.Code.FixedImage_Env_new

/-!
# `EnvNewContractSupply` — the `env_new` contract from one named ledger

`EnvNewContract` (`HelperCallEnvNew.lean`) is supplied on the layer:

* the `env_new` prologue `0x800029fc`–`0x80002a0c` (`addi sp,-16; sd s0; mv s0,a0;
  li a0,32; sd ra`) is ONE `#derive_case` seg (`envNewPrologueSeg`), run by
  `segEval_sound`; the `jal malloc` at `0x80002a10` is the generated site
  `site_80002a10_env` through `jalCallFacts_of_obs` (`envNewParked_of_entry`);
* the allocator call uses the ledger's `MallocSuccessRun`, with credit and
  concrete placement at the actual entry. Its selected return retains the
  fresh block, memory frame, code, output, presence, and unused reserve;
* the landed success suffix `envNewSuccess_run` (`EnvNewSuccessSuffix.lean`)
  initialises the 32-byte frame and returns;
* the pushed store is `storeRepr_allocFrame` (`rows/CallClosureEnvNewMarshal`)
  under `pushFrameMap`, after the ownership transport
  `StoreOwned.repr_transport` (allocator-private and fresh bytes are outside
  every represented byte by `HeapOwned`) and the frame-map rebase
  `storeRepr_phif_mono` (new here).

The facts the entry state does not carry are ONE named ledger, `EnvNewLedger`,
each field naming its supplier.  The landed `env_new_spec` is not used: its
premise `∀ p, EnvRegions … p` is false at `p = 0` (`frame_lo`).
-/

