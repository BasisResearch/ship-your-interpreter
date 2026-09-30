import Vsa.Elf
import Vsa.Sim.InitValues

/-!
# Layer-0 decode-table entry for the M1 spike word

`decode_spike_addi` — the Layer-0 decode-table entry
(`PLAN-InterpSim.md` §Layer 0 item 4) for the M1 spike word
`0x00000513` = `addi a0, x0, 0`.

This is the post-`reset()` variant of experiment `E1i`
(`experiments/E1i_decode_staged.lean`): it pins the control registers at
their real post-`setupElf` values (`Vsa.Sim.initMisa`, `mseccfg = 0`) rather
than the pre-reset `sail_model_init` seeds, and it drives the step-path entry
`ext_decode` (`LeanRV64DExecutable/DecodeExt.lean:199`) rather than
`encdec_backwards` directly. `ext_decode bv` is definitionally `encdec_backwards
bv`, so the two statements coincide after unfolding.

Staging discipline (see E1i): a one-pass simp times out; the decode is peeled
in stages, closing the width-coerced residuals with
`BitVec.eq_of_toNat_eq; decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

