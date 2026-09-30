import Vsa.Sim.ValueSites
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch06Part16
import Vsa.Sim.DecodeTable.Batch06Part20
import Vsa.Sim.DecodeTable.Batch12Part19
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.Code.Env_new

/-!
# Layer 3 — per-site observational step lemmas for `env_new`

One observational-step (`StepObs`) lemma per instruction of the success path of
`env_new` (`c/src/env.c`, @0x800029fc, 24 instructions in the census; the success
path is 15 instructions ending in `ret` at 0x80002a34, plus a NULL-error path
[0x80002a38, 0x80002a5c) that calls `exit` and never returns — see `EnvNewSpec`).

The success path (from `experiments/disasm.txt`):

```
29fc addi sp,sp,-16        ; ITYPE addi x2,x2,0xff0
2a00 sd   s0,0(sp)         ; STORE sd x8 @ x2+0
2a04 mv   s0,a0            ; ITYPE addi x8,x10,0
2a08 li   a0,32            ; ITYPE addi x10,x0,0x020
2a0c sd   ra,8(sp)         ; STORE sd x1 @ x2+8
2a10 jal  malloc           ; JAL x1, 0x001d80  → 0x80004790
2a14 beqz a0,80002a38      ; BTYPE beq x10,x0  (NULL-error path)
2a18 ld   ra,8(sp)         ; LOAD ld x1, 8(x2)
2a1c sd   s0,24(a0)        ; STORE sd x8 @ x10+24  (parent field)
2a20 ld   s0,0(sp)         ; LOAD ld x8, 0(x2)
2a24 sd   zero,0(a0)       ; STORE sd x0 @ x10+0   (count=cap=0)
2a28 sd   zero,8(a0)       ; STORE sd x0 @ x10+8   (names=NULL)
2a2c sd   zero,16(a0)      ; STORE sd x0 @ x10+16  (vals=NULL)
2a30 addi sp,sp,16         ; ITYPE addi x2,x2,0x010
2a34 ret                   ; JALR x0, 0(x1)
```

**Loads are ALU-class sites.** A `ld rd,off(rs1)` writes a GPR with
`sign_extend (dword)`, so its observation is `sigmaPost_alu σ pc vm rd v` (via
`exec_ld` from `ValueSites`) — consumed by `obs_alu_*`/`frame_alu`, exactly like
an `addi`. The stores use `exec_sd_val` (width-8 `sd`).

Reuses the execution machinery from `ValueSites` and imports the required decode
parts directly. It also reuses the shared byte-word facts
`w_00053423`/`w_00008067` (+ their `nr_`). The 13 fresh instruction words get
`_env`-suffixed byte-word facts (collision sweep).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

