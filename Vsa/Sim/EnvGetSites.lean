import Vsa.Sim.ValueSites
import Vsa.Sim.Code.Env_get
import Vsa.Sim.DecodeTable.Batch16Part01
import Vsa.Sim.DecodeTable.Batch09Part17

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

theorem w_0004b503_eg : (((0x00#8).append (0x04#8)).append (0xb5#8)).append (0x03#8) = (0x0004b503#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0004b503_eg : Sail.BitVec.extractLsb ((((0x00#8).append (0x04#8)).append (0xb5#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## env_get site step lemmas

Each site is a `stepObs_*` instantiation over the `env_get_at_<addr>` code
lemma and the matching `decode_<word>` + `execute_*_char` builder, following
the `EnvNewSites`/`DivSites` templates verbatim. -/

/-! ### 0x80002c10 (`beqz a0,0x80002cd4`): `beq x10,x0`, imm 0x00c4.
Taken iff `a0 == 0` (env == NULL). -/

/-! ### 0x80002c14 (`addi sp,sp,-64`): `x2 := x2 + sext 0xfc0`. -/

end Vsa.Sim
