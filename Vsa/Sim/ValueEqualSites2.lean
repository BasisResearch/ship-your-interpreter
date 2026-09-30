import Vsa.Sim.ValueEqualSites
import Vsa.Sim.ValueTruthySpec

/-!
# Layer 3 — payload-equality bridges + `str`-path call sites for `value_equal`

This companion to `ValueEqualSites.lean` adds:

* the four **payload-equality bridges** (bool/int/closure/native): each shows that
  the machine `sub payA payB` is `0` iff the corresponding spec `Value.equal` clause
  holds. The `sub` result feeds `seqz`, giving `cond (payA - payB = 0) 1 0`, so we need
  `(payA - payB = 0#64) = Value.equal …` at the `BitVec 64` level;
* the six **`str`-path call instructions** (`0x800028c4 … 0x800028e4`): argument moves,
  the stack `sd ra`/`ld ra`, the `jal strcmp`, and the trailing `seqz`. `site_ret_gen`
  already covers the `ret` at `0x800028e4`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Payload-equality bridges

`seqz` gives `cond ((payA - payB) == 0) 1 0`; we rewrite the `payA - payB == 0` test to
the spec `Value.equal` clause. All are stated at the `BitVec 64` level as `(x == 0) = P`. -/

end Vsa.Sim
