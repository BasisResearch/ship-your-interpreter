import VsaIris.Vsa.Malloc
import Vsa.Sim.AllocCapacity
import Vsa.Sim.rows.CallClosureRow
import Vsa.Sim.rows.EnvDefineContractUpdate

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc Vsa.Sim Vsa.Sim.DlHeap Vsa.Sim.RuntimeOwnership

def reallocEntryBV : BitVec 64 := BitVec.ofNat 64 Vsa.Sim.reallocEntry

end VsaIris.VsaHeap
