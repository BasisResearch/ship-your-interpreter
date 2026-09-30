import Vsa.Sim.ValueSites
import Vsa.Sim.ValueSpec
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.SnprintfSpec19

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem sdData_val_id (v : BitVec 64) : sdData_val v = v :=
  BitVec.eq_of_toNat_eq (sdData_toNat v)

theorem pinw4_sext_reassemble (v : BitVec (8 * 4)) :
    (sign_extend (m := 64)
      (((((v.extractLsb' 24 8).append (v.extractLsb' 16 8)).append (v.extractLsb' 8 8)).append (v.extractLsb' 0 8)) : BitVec (8 * 4)) : BitVec 64) = sign_extend (m := 64) v :=
  lw_cap_reassemble_sp v

end Vsa.Sim
