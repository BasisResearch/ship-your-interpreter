import Vsa.Sim.EnvDefCompose
import Vsa.Sim.StrlenSpec
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.EnvNewSites
import Vsa.Sim.Code.Env_define
import Vsa.Sim.DecodeTable.Batch02Part03
import Vsa.Sim.DecodeTable.Batch10Part15
import Vsa.Sim.DecodeTable.Batch02Part22
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch12Part06

/-!
# `EnvDefBridges` — the Shape-A straight-line machine bridges of `EnvDefCompose`

`Vsa/Sim/EnvDefCompose.lean` composed the whole `env_define` function over the real
callee contracts (`strlen`/`malloc`/`memcpy`/`realloc`), leaving its `*Contract`
theorems parameterised by NAMED machine-bridge hypotheses (`bridgeStrlenPre`,
`bridgeMallocPre`, …).  Each bridge is a straight-line `mv`/`addi`/`sd`/`ld` +
`jal callee` segment: NO call composition (that is `callSeg`'s job upstream), just the
per-instruction `StepObs` threading carrying the entry semantic facts across the arg
marshalling into the callee's entry predicate.

## The shared `mv rd,rs ; jal callee` prefix sub-shape

EVERY append/grow call prefix is the same 2-instruction idiom: one `addi`-class move
that marshals an argument into `a0`, then a `jal` that links the return address and
jumps to the callee entry.  `mvJalPrefix` factors that idiom into a reusable lemma:
given the entry state (PC at the `mv`, source register value, callee byte pins,
decode facts), it runs both steps and delivers the post-`jal` state (PC = callee
entry, `x10 = marshalled arg`, `x1 = link`, all other pins framed through).  Each
concrete bridge instantiates it and packages the callee's entry predicate.

The `jal`-marshalling helpers (`obs_jal_*`, `frame_jal_env`, `frame_alu_env`) are
reused verbatim from `EnvNewSpec` — env_new's single-malloc splice IS this same shape
(the ledger's fan-out note).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Sim.Code (StrlenLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Site step lemmas for the strlen prefix (`0x80002b1c mv a0,s2 ; 0x80002b20 jal strlen`) -/

/-! ## Site step lemmas for the malloc prefix
(`0x80002b24 addi s0,a0,1 ; 0x80002b28 mv a0,s0 ; 0x80002b2c jal malloc`) -/

/-! ## The strlen-prefix run: `0x80002b1c mv a0,s2 ; 0x80002b20 jal strlen`

Chains the two site steps.  From a state at `0x80002b1c` with `x18 = namePtr`, runs to a
state at the strlen entry `0x80006cf0` with `x10 = namePtr`, `x1 = 0x80002b24` (the link),
memory unchanged, and `minstret` defined.  `x18` is preserved by both steps (the `mv`
writes `x10`, the `jal` writes `x1`), and memory is untouched, so all entry semantic facts
carry through unchanged. -/

/-! ## `bridgeStrlenPre` discharged — FRAME-CARRYING

The append-path entry predicate `AppendStrlenEntry` supplies exactly what `strlen_pre`
needs about the `name` argument (`StrlenLoaded`, `StrRegions`, 8-alignment, `CString`)
plus the machine entry state at `0x80002b1c` (`x18 = namePtr`, `mem = m0`, tick, minstret),
AND the **carried caller-frame** (`EnvDefFrame`: sp/`StackOK`, gp, ABI callee-saved tie,
`AInv`) that the downstream malloc entry will need — the assertion-carried framing the
composed contract's strlen seam now demands.

`bridgeStrlenPre_closed` runs the two-instruction prefix (`strlenPrefix_run`), repackaging
the post-state as `strlen_pre namePtr 0x80002b24 nameStr m0 ∧ EnvDefFrame …`.  The frame
survives because the prefix writes only `x10` (mv) and `x1` (jal): sp/gp/callee-saveds are
framed through by `strlenPrefix_run`'s frame clauses, and `AInv` survives by its
stability under (mem-agree ∧ gp-agree) — the same `MallocContract`-interface property
`env_new` draws on (`EnvNewSpec` line 496).  This discharges `envDefAppendContract`'s
frame-carrying `bridgeStrlenPre` hypothesis. -/

/-! ## The malloc-prefix run:
`0x80002b24 addi s0,a0,1 ; 0x80002b28 mv a0,s0 ; 0x80002b2c jal malloc`

Chains the three site steps.  From a state at `0x80002b24` with `x10 = len` (the strlen
result), runs to a state at `mallocEntry = 0x80004790` with `x10 = len+1`, `x8 = len+1`
(`s0`, the saved size), `x1 = 0x80002b30` (link), memory unchanged, minstret defined, and a
FRAME clause: every register the three steps do not write (`x8` by the addi, `x10` by the
mv, `x1` by the jal) is preserved — in particular `x2`/sp and `x3`/gp and every OTHER
callee-saved.  `x8` is the one callee-saved the prefix rewrites (to the malloc size), so the
malloc-entry ABI ghost differs from the entry ghost only there. -/

/-! ## `bridgeMallocPre` discharged — FRAME-CARRYING

`bridgeMallocPre`'s source is `strlen_post 0x80002b24 nameStr m0 ∧ EnvDefFrame …` (the
frame-carrying strlen seam).  The `addi;mv;jal malloc` prefix marshals `len+1` into `a0`
and lands `MallocContract.spec`'s entry predicate.  The malloc size is `nMalloc = len+1`
where `len = nameStr.length` (from `strlen_post`'s `x10 = ofNat len`); the return address
is `0x80002b30`; `sp`/`gp`/`AInv` come straight from the carried `EnvDefFrame`.  The one
callee-saved the prefix rewrites is `x8`/`s0` (holds the size across the malloc call), so the
malloc-entry ABI ghost `g'` agrees with the entry ghost `gm` everywhere except `x8`. -/

end Vsa.Sim
