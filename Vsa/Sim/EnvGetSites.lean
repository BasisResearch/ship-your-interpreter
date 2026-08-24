import Vsa.Sim.ValueSites
import Vsa.Sim.Code.Env_get
import Vsa.Sim.Code.Env_set

/-!
# Layer 3 — per-site observational step lemmas for `env_get` and `env_set`

One observational-step (`StepObs`) lemma per instruction of `env_get`
(`c/src/env.c`, @0x80002c10, 51 instructions in the census) and `env_set`
(@0x80002cdc, 51 instructions), hosting both here to share the chain-walk
machinery.  env_set-specific items carry the `_es` suffix; shared / env_get
items carry `_eg`.

## Control-flow map — `env_get(env, name, out)` [0x80002c10, 0x80002cdc)

```
c10 beqz a0,cd4          ; entry: if env==NULL → NULL-return (cd4)
c14 addi sp,sp,-64       ; prologue: frame + spill s3/s4/s5/ra/s0/s1/s2
c18..c30 sd s3/s4/s5/ra/s0/s1/s2
c34 mv s4,a0             ; s4 (x20) = env
c38 mv s3,a1             ; s3 (x19) = name
c3c mv s5,a2             ; s5 (x21) = out
c40 lw s2,0(s4)          ; [CHAIN HEAD] s2 (x18) = env->count (32-bit signed)
c44 blez s2,cc4          ; if count<=0 → descend (cc4)
c48 ld s1,8(s4)          ; s1 (x9) = env->names
c4c li s0,0              ; s0 (x8) = i = 0
c50 j c60                ; enter scan loop at the test
c54 addi s0,s0,1         ; [SCAN back-edge] i++
c58 addi s1,s1,8         ; names++
c5c beq s0,s2,cc4        ; [SCAN TEST] if i==count → descend
c60 ld a0,0(s1)          ; a0 = names[i]
c64 mv a1,s3             ; a1 = name
c68 jal strcmp           ; a0 = strcmp(names[i], name)
c6c bnez a0,c54          ; if != 0 → next iteration (c54)
c70..c9c HIT: a5=env->vals; a4=vals[i] (24*i stride via slli/add/slli/add);
             *out = vals[i] (3×8B copy); a0=1
ca0..cc0 epilogue: restore s*/ra, sp+=64, ret
cc4 ld s4,24(s4)         ; [DESCEND] env = env->parent
cc8 bnez s4,c40          ; [CHAIN TEST] if parent!=0 → chain head (c40)
ccc li a0,0              ; MISS through whole chain
cd0 j ca0                ; → epilogue (a0=0)
cd4 li a0,0              ; NULL-env entry return
cd8 ret                  ; a0=0
```

env_set [0x80002cdc, 0x80002da8) is structurally identical; on HIT it LOADS the
24-byte value from `*out` (a1/a2/a3 = out[0/8/16]) and STORES it into `vals[i]`
(the 24*i slot), returning a0=1.  No malloc; both are pure walkers.  Neither
calls `runtime_error`/`longjmp` — the miss path returns 0 in-function.

Register map (env_get/env_set share it):
`s4=x20 env`, `s3=x19 name`, `s5=x21 out`, `s2=x18 count`, `s1=x9 names/ptr`,
`s0=x8 i`, `a0=x10`, `a1=x11`, `a2=x12`, `a3=x13`, `a4=x14`, `a5=x15`,
`ra=x1`, `sp=x2`.

**24*i stride** (verified from this assembly): `slli a4,s0,1; add a4,a4,s0;
slli a4,a4,3` computes `a4 = ((i<<1)+i)<<3 = 24*i`; then `add a5,a5,a4` gives
`&vals[i]`.  This is the 24-byte `Value` stride recorded in `RuntimeRepr`.

Reuses `ValueSites`: the `stepObs_*` wrappers, `exec_sd_val`, `exec_ld`,
`exec_lw`, `writeMap8`, `sdData_val`, the `decode_*` table, plus the generic
`execute_*_char` ALU/branch builders.  Loads (`lw`/`ld`) are ALU-class sites
(they write a GPR with `sign_extend`, observed as `sigmaPost_alu`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Byte-word / non-RVC facts for the env_get/env_set instruction words

`w_<word>_eg` : the 4-byte little-endian reassembly equals the 32-bit word.
`nr_<word>_eg` : the low two bits are `0b11` (not an RVC compressed instruction).
Both by `decide`.  Shared across env_get and env_set (union of their words). -/

theorem w_0c050263_eg : (((0x0c#8).append (0x05#8)).append (0x02#8)).append (0x63#8) = (0x0c050263#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0c050263_eg : Sail.BitVec.extractLsb ((((0x0c#8).append (0x05#8)).append (0x02#8)).append (0x63#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_fc010113_eg : (((0xfc#8).append (0x01#8)).append (0x01#8)).append (0x13#8) = (0xfc010113#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_fc010113_eg : Sail.BitVec.extractLsb ((((0xfc#8).append (0x01#8)).append (0x01#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_01313c23_eg : (((0x01#8).append (0x31#8)).append (0x3c#8)).append (0x23#8) = (0x01313c23#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_01313c23_eg : Sail.BitVec.extractLsb ((((0x01#8).append (0x31#8)).append (0x3c#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_01413823_eg : (((0x01#8).append (0x41#8)).append (0x38#8)).append (0x23#8) = (0x01413823#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_01413823_eg : Sail.BitVec.extractLsb ((((0x01#8).append (0x41#8)).append (0x38#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_01513423_eg : (((0x01#8).append (0x51#8)).append (0x34#8)).append (0x23#8) = (0x01513423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_01513423_eg : Sail.BitVec.extractLsb ((((0x01#8).append (0x51#8)).append (0x34#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_02113c23_eg : (((0x02#8).append (0x11#8)).append (0x3c#8)).append (0x23#8) = (0x02113c23#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_02113c23_eg : Sail.BitVec.extractLsb ((((0x02#8).append (0x11#8)).append (0x3c#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_02813823_eg : (((0x02#8).append (0x81#8)).append (0x38#8)).append (0x23#8) = (0x02813823#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_02813823_eg : Sail.BitVec.extractLsb ((((0x02#8).append (0x81#8)).append (0x38#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_02913423_eg : (((0x02#8).append (0x91#8)).append (0x34#8)).append (0x23#8) = (0x02913423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_02913423_eg : Sail.BitVec.extractLsb ((((0x02#8).append (0x91#8)).append (0x34#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_03213023_eg : (((0x03#8).append (0x21#8)).append (0x30#8)).append (0x23#8) = (0x03213023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_03213023_eg : Sail.BitVec.extractLsb ((((0x03#8).append (0x21#8)).append (0x30#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00050a13_eg : (((0x00#8).append (0x05#8)).append (0x0a#8)).append (0x13#8) = (0x00050a13#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00050a13_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x0a#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00058993_eg : (((0x00#8).append (0x05#8)).append (0x89#8)).append (0x93#8) = (0x00058993#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00058993_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x89#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00060a93_eg : (((0x00#8).append (0x06#8)).append (0x0a#8)).append (0x93#8) = (0x00060a93#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00060a93_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x06#8)).append (0x0a#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_000a2903_eg : (((0x00#8).append (0x0a#8)).append (0x29#8)).append (0x03#8) = (0x000a2903#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_000a2903_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x0a#8)).append (0x29#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_09205063_eg : (((0x09#8).append (0x20#8)).append (0x50#8)).append (0x63#8) = (0x09205063#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_09205063_eg : Sail.BitVec.extractLsb ((((0x09#8).append (0x20#8)).append (0x50#8)).append (0x63#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_008a3483_eg : (((0x00#8).append (0x8a#8)).append (0x34#8)).append (0x83#8) = (0x008a3483#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_008a3483_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x8a#8)).append (0x34#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00000413_eg : (((0x00#8).append (0x00#8)).append (0x04#8)).append (0x13#8) = (0x00000413#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00000413_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x04#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_0100006f_eg : (((0x01#8).append (0x00#8)).append (0x00#8)).append (0x6f#8) = (0x0100006f#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0100006f_eg : Sail.BitVec.extractLsb ((((0x01#8).append (0x00#8)).append (0x00#8)).append (0x6f#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00140413_eg : (((0x00#8).append (0x14#8)).append (0x04#8)).append (0x13#8) = (0x00140413#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00140413_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x14#8)).append (0x04#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00848493_eg : (((0x00#8).append (0x84#8)).append (0x84#8)).append (0x93#8) = (0x00848493#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00848493_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x84#8)).append (0x84#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_07240463_eg : (((0x07#8).append (0x24#8)).append (0x04#8)).append (0x63#8) = (0x07240463#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_07240463_eg : Sail.BitVec.extractLsb ((((0x07#8).append (0x24#8)).append (0x04#8)).append (0x63#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_0004b503_eg : (((0x00#8).append (0x04#8)).append (0xb5#8)).append (0x03#8) = (0x0004b503#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0004b503_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x04#8)).append (0xb5#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00098593_eg : (((0x00#8).append (0x09#8)).append (0x85#8)).append (0x93#8) = (0x00098593#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00098593_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x09#8)).append (0x85#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_238040ef_eg : (((0x23#8).append (0x80#8)).append (0x40#8)).append (0xef#8) = (0x238040ef#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_238040ef_eg : Sail.BitVec.extractLsb ((((0x23#8).append (0x80#8)).append (0x40#8)).append (0xef#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_16c040ef_eg : (((0x16#8).append (0xc0#8)).append (0x40#8)).append (0xef#8) = (0x16c040ef#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_16c040ef_eg : Sail.BitVec.extractLsb ((((0x16#8).append (0xc0#8)).append (0x40#8)).append (0xef#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_fe0514e3_eg : (((0xfe#8).append (0x05#8)).append (0x14#8)).append (0xe3#8) = (0xfe0514e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_fe0514e3_eg : Sail.BitVec.extractLsb ((((0xfe#8).append (0x05#8)).append (0x14#8)).append (0xe3#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_010a3783_eg : (((0x01#8).append (0x0a#8)).append (0x37#8)).append (0x83#8) = (0x010a3783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_010a3783_eg : Sail.BitVec.extractLsb ((((0x01#8).append (0x0a#8)).append (0x37#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00141713_eg : (((0x00#8).append (0x14#8)).append (0x17#8)).append (0x13#8) = (0x00141713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00141713_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x14#8)).append (0x17#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00870733_eg : (((0x00#8).append (0x87#8)).append (0x07#8)).append (0x33#8) = (0x00870733#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00870733_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x87#8)).append (0x07#8)).append (0x33#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00371713_eg : (((0x00#8).append (0x37#8)).append (0x17#8)).append (0x13#8) = (0x00371713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00371713_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x37#8)).append (0x17#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00e787b3_eg : (((0x00#8).append (0xe7#8)).append (0x87#8)).append (0xb3#8) = (0x00e787b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00e787b3_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0xe7#8)).append (0x87#8)).append (0xb3#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_0007b703_eg : (((0x00#8).append (0x07#8)).append (0xb7#8)).append (0x03#8) = (0x0007b703#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0007b703_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x07#8)).append (0xb7#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00100513_eg : (((0x00#8).append (0x10#8)).append (0x05#8)).append (0x13#8) = (0x00100513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00100513_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x10#8)).append (0x05#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00eab023_eg : (((0x00#8).append (0xea#8)).append (0xb0#8)).append (0x23#8) = (0x00eab023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00eab023_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0xea#8)).append (0xb0#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_0087b703_eg : (((0x00#8).append (0x87#8)).append (0xb7#8)).append (0x03#8) = (0x0087b703#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0087b703_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x87#8)).append (0xb7#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00eab423_eg : (((0x00#8).append (0xea#8)).append (0xb4#8)).append (0x23#8) = (0x00eab423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00eab423_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0xea#8)).append (0xb4#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_0107b783_eg : (((0x01#8).append (0x07#8)).append (0xb7#8)).append (0x83#8) = (0x0107b783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0107b783_eg : Sail.BitVec.extractLsb ((((0x01#8).append (0x07#8)).append (0xb7#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00fab823_eg : (((0x00#8).append (0xfa#8)).append (0xb8#8)).append (0x23#8) = (0x00fab823#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00fab823_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0xfa#8)).append (0xb8#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_03813083_eg : (((0x03#8).append (0x81#8)).append (0x30#8)).append (0x83#8) = (0x03813083#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_03813083_eg : Sail.BitVec.extractLsb ((((0x03#8).append (0x81#8)).append (0x30#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_03013403_eg : (((0x03#8).append (0x01#8)).append (0x34#8)).append (0x03#8) = (0x03013403#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_03013403_eg : Sail.BitVec.extractLsb ((((0x03#8).append (0x01#8)).append (0x34#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_02813483_eg : (((0x02#8).append (0x81#8)).append (0x34#8)).append (0x83#8) = (0x02813483#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_02813483_eg : Sail.BitVec.extractLsb ((((0x02#8).append (0x81#8)).append (0x34#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_02013903_eg : (((0x02#8).append (0x01#8)).append (0x39#8)).append (0x03#8) = (0x02013903#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_02013903_eg : Sail.BitVec.extractLsb ((((0x02#8).append (0x01#8)).append (0x39#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_01813983_eg : (((0x01#8).append (0x81#8)).append (0x39#8)).append (0x83#8) = (0x01813983#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_01813983_eg : Sail.BitVec.extractLsb ((((0x01#8).append (0x81#8)).append (0x39#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_01013a03_eg : (((0x01#8).append (0x01#8)).append (0x3a#8)).append (0x03#8) = (0x01013a03#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_01013a03_eg : Sail.BitVec.extractLsb ((((0x01#8).append (0x01#8)).append (0x3a#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00813a83_eg : (((0x00#8).append (0x81#8)).append (0x3a#8)).append (0x83#8) = (0x00813a83#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00813a83_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x81#8)).append (0x3a#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_04010113_eg : (((0x04#8).append (0x01#8)).append (0x01#8)).append (0x13#8) = (0x04010113#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_04010113_eg : Sail.BitVec.extractLsb ((((0x04#8).append (0x01#8)).append (0x01#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00008067_eg : (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00008067_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_018a3a03_eg : (((0x01#8).append (0x8a#8)).append (0x3a#8)).append (0x03#8) = (0x018a3a03#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_018a3a03_eg : Sail.BitVec.extractLsb ((((0x01#8).append (0x8a#8)).append (0x3a#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_f60a1ce3_eg : (((0xf6#8).append (0x0a#8)).append (0x1c#8)).append (0xe3#8) = (0xf60a1ce3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_f60a1ce3_eg : Sail.BitVec.extractLsb ((((0xf6#8).append (0x0a#8)).append (0x1c#8)).append (0xe3#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00000513_eg : (((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8) = (0x00000513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00000513_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_fd1ff06f_eg : (((0xfd#8).append (0x1f#8)).append (0xf0#8)).append (0x6f#8) = (0xfd1ff06f#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_fd1ff06f_eg : Sail.BitVec.extractLsb ((((0xfd#8).append (0x1f#8)).append (0xf0#8)).append (0x6f#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_000ab583_eg : (((0x00#8).append (0x0a#8)).append (0xb5#8)).append (0x83#8) = (0x000ab583#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_000ab583_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x0a#8)).append (0xb5#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_008ab603_eg : (((0x00#8).append (0x8a#8)).append (0xb6#8)).append (0x03#8) = (0x008ab603#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_008ab603_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x8a#8)).append (0xb6#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_010ab683_eg : (((0x01#8).append (0x0a#8)).append (0xb6#8)).append (0x83#8) = (0x010ab683#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_010ab683_eg : Sail.BitVec.extractLsb ((((0x01#8).append (0x0a#8)).append (0xb6#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00b7b023_eg : (((0x00#8).append (0xb7#8)).append (0xb0#8)).append (0x23#8) = (0x00b7b023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00b7b023_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0xb7#8)).append (0xb0#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00c7b423_eg : (((0x00#8).append (0xc7#8)).append (0xb4#8)).append (0x23#8) = (0x00c7b423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00c7b423_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0xc7#8)).append (0xb4#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_00d7b823_eg : (((0x00#8).append (0xd7#8)).append (0xb8#8)).append (0x23#8) = (0x00d7b823#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00d7b823_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0xd7#8)).append (0xb8#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide


/-! ## env_get site step lemmas

Each site is a `stepObs_*` instantiation over the `env_get_at_<addr>` code
lemma and the matching `decode_<word>` + `execute_*_char` builder, following
the `EnvNewSites`/`DivSites` templates verbatim. -/

/-! ### 0x80002c10 (`beqz a0,0x80002cd4`): `beq x10,x0`, imm 0x00c4.
Taken iff `a0 == 0` (env == NULL). -/
theorem exec_beqz_a0_taken_eg (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (htgt : (pc + sign_extend (m := 64) (0x00c4#13)).toNat % 4 = 0)
    (hv : (v10 == (0#64)) = true) :
    (execute (instruction.BTYPE (0x00c4#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, bop.BEQ))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x00c4#13)) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_beq_taken (0x00c4#13) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
    v10 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x10 _ v10 h10) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

theorem exec_beqz_a0_nottaken_eg (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hv : (v10 == (0#64)) = false) :
    (execute (instruction.BTYPE (0x00c4#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, bop.BEQ))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_btype_beq_nottaken (0x00c4#13) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
    v10 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x10 _ v10 h10) (rX_bits_zero _) hv

theorem site_80002c10_nottaken_eg
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c10#64 : BitVec 64)) (hv : (v10 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c10 hmem
  exact stepObs_branch_nottaken σ i u (0x80002c10#64) vminstret (0x00c4#13)
    (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5) bop.BEQ (0x0c050263#32)
    (0x63#8) (0x02#8) (0x05#8) (0x0c#8)
    hG hpc hminstret w_0c050263_eg nr_0c050263_eg
    (Vsa.Sim.DecodeTable.decode_0c050263 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a0_nottaken_eg σ (0x80002c10#64) v10 hx10 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80002c14 (`addi sp,sp,-64`): `x2 := x2 + sext 0xfc0`. -/
theorem site_80002c14_eg
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c14#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x2 (vsp + sign_extend (m := 64) (0xfc0#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c14 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002c14#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80002c14#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002c14#64) vminstret (0xfc010113#32)
    (instruction.ITYPE (0xfc0#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))
    Register.x2 (vsp + sign_extend (m := 64) (0xfc0#12)) (0x13#8) (0x01#8) (0x01#8) (0xfc#8)
    hG hpc hminstret w_fc010113_eg nr_fc010113_eg
    (Vsa.Sim.DecodeTable.decode_fc010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0xfc0#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) vsp
      (afterNextPC (afterPrelude σ) (0x80002c14#64))
      (sigma3_alu σ (0x80002c14#64) Register.x2 (vsp + sign_extend (m := 64) (0xfc0#12)))
      (rX_bits_x2 _ vsp hx2₂) (wX_bits_x2 _ (vsp + sign_extend (m := 64) (0xfc0#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
