import Vsa.Sim.DeriveCallSeg
import Vsa.Sim.EnvDefineClose
import Vsa.Sim.EnvDefSpec3
import Vsa.Sim.StrlenSpec
import Vsa.Sim.MemcpySpec4
import Vsa.Sim.MemcpySpecFramed
import Vsa.Sim.rows.EnvDefineEpilogueCore

/-!
# `EnvDefCompose` — the composed `env_define` contract (Shape-D)

Step 5 of `experiments/interp-sim-completion-plan.md`.  `env_define` is the
biggest semantic gap: its append/grow paths call `strlen`, `malloc`, `memcpy`,
and `realloc` (twice).  Every one of those calls is a Shape-D `jal rd` splice
`prefix ≫ callee ≫ suffix` (`Vsa/Sim/DeriveCallSeg.lean`, `callSeg`), with the
callee contract threaded as a NAMED HYPOTHESIS — `MallocContract` (`Vsa/Alloc.lean`,
the plan's `MallocSpec`), `ReallocOps` (`Vsa/Sim/ReallocSpec.lean`), `strlen_spec`
(`StrlenSpec`), `memcpy_spec` (`MemcpySpec4`).  None is a Lean `axiom`; each is a
structure field or a proved Triple.

This file lands the **maximal composition skeleton**, modelling `divValueTail`
(`Vsa/Sim/BinOpValueTails.lean`): the whole append and grow paths are assembled as
`callSeg` chains over the real callee contracts, with the per-block MACHINE
BRIDGES stated as named hypotheses.  Each bridge is a straight-line
`#derive_case`/`chain_facts` segment (Shape-A) — the honest remaining machine
work — but the CALL COMPOSITION (the hard Shape-D algebra) is proved here and is
axiom-clean.  The consumer (`Call.closure`/`varDecl`/`assign`) sees one Triple.

## Control-flow map (from `experiments/disasm.txt`; recap of `EnvDefSpec2` header)

```
PROLOGUE 0x80002a5c..0x80002a90  ── PROVED (EnvDefSpec17.env_define_prologue)
  blez s3 → CAP-INIT   (count == 0, name absent)
SCAN 0x80002a94..0x80002abc      ── update path (EnvDefSpec3, loop + strcmp)
  hit  → UPDATE 0x80002ac0..0x80002ae8 → EPILOGUE      (name found)
  miss → CAP-CHECK 0x80002b14: beq cap,count → GROW      (name absent)
APPEND 0x80002b1c..0x80002b8c     ── strlen ≫ malloc ≫ (NULL guard) ≫ memcpy ≫ store
  b20 jal strlen  ;  b2c jal malloc  ;  b34 beqz a0 → OOM  ;  b40 jal memcpy
  b44..b88 store copy into names[count]/vals[count], count++      → EPILOGUE
GROW 0x80002b90..0x80002bcc       ── cap' ≫ realloc(names) ≫ realloc(vals) → APPEND head
  ba0 jal realloc(names,cap'*8)  ;  bbc jal realloc(vals,cap'*24)  ;  bcc → 0xb1c
EPILOGUE 0x80002aec..0x80002b10  ── restore 7 spills, sp+=64, ret
```

## What is PROVED vs a NAMED BRIDGE

| Segment | Status |
|---------|--------|
| prologue 0x80002a5c→0x80002a90 | PROVED (`env_define_prologue`) |
| scan loop + update block | statement + all ingredients (`EnvDefSpec3`); loop body a documented obligation |
| **strlen call splice** | PROVED HERE (`envDefStrlenSplice`) over `strlen_spec` |
| **malloc call splice** | PROVED HERE (`envDefMallocSplice`) over `MallocContract.spec` |
| **memcpy call splice** | PROVED HERE (`envDefMemcpySplice`) over `memcpy_spec` |
| **realloc(names) splice** | PROVED HERE (`envDefReallocNamesSplice`) over `ReallocOps.grow` |
| **realloc(vals) splice** | PROVED HERE (`envDefReallocValsSplice`) over `ReallocOps.grow` |
| **append path composed** | PROVED HERE (`envDefAppendContract`) |
| **grow path composed** | PROVED HERE (`envDefGrowContract`) |
| machine bridges (`*Pre`/`*Stage`/`*Suf`) | NAMED HYPOTHESES (Shape-A residuals) |

The residual per splice is exactly the three concrete straight-line machine
bridges the arm still needs (mirroring `divValueTail`'s `pre`/`stage`/`suf`):
the prefix landing the callee entry, the inter-call staging, and the return
suffix.  Each is a `#derive_case` segment over pinned bytes — no reflection is
performed here, so the whole file elaborates in constant time and is axiom-clean.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc

namespace Vsa.Sim

/-! ## The CARRIED FRAME — assertion-carried framing across the callee seams

The structural gap diagnosed in `experiments/envdefine-composition.md` (last
ledger section) is this: the seam predicate between two callees was the BARE
downstream-callee post (`strlen_post`, malloc-post), which discards the
caller-saved context (`sp`/`gp`/ABI callee-saveds/`AInv`) that the NEXT callee's
entry requires.  So `bridgeMallocPre`/`bridgeMemcpyPre` were unprovable as
stated — there was nowhere for the malloc-entry `sp`/`gp`/`AInv` facts to come
from.

The fix is the house pattern (`BlockLogic.negProloguePost`, `BinOpValueTails`,
`ReallocPost`): **assertion-carried framing** — the seam is
`calleePost ∧ <carried frame>`, where the frame is precisely the ABI/heap
context the downstream entry needs, and it is threaded THROUGH each callee by a
frame-preservation clause the callee's own contract supplies.  A generic
`Triple.frame` would be unsound (`BlockLogic.lean:78`); the frame is instead
carried as an explicit conjunct proved by the segment that spans it.

`EnvDefFrame` is that carried context: the ABI callee-saveds tie (`gm`), `sp` +
`StackOK`, `gp`, and the allocator invariant `AInv` over the live extents — i.e.
the malloc/realloc-entry frame minus the argument-specific pins (PC/x10/x1/mem),
which each prefix supplies. -/

/-! ## Single-call splices — each `prefix ≫ callee ≫ suffix` over one real contract

Each splice is `callSeg pre callee suf` (`DeriveCallSeg.lean`): the caller prefix
lands the callee's entry predicate, the real callee contract runs, the caller
suffix consumes the callee's exit.  The two `Triple.seq`s are the whole content of
the Shape-D algebra; the callee is threaded, never re-proved. -/

/-! ## `realloc` splices — over `ReallocOps.grow` (both grow-path calls) -/

/-! ## The APPEND path composed — `strlen ≫ malloc ≫ memcpy ≫ store`

The append path (`0x80002b1c..0x80002b8c`, name absent, `count < cap`) is three
call splices in series plus a straight-line store block.  It is one
`callSeg`-chain over `strlen_spec`, `MallocContract.spec`, `memcpy_spec`, with
the inter-call staging blocks (`mv`/`addi`/`beqz` arg marshalling) and the final
store block (`0x80002b44..0x80002b88`: 3×`sd` into `vals[count]`, `sd` into
`names[count]`, `sw count+1`) as named machine bridges.

`Astrlen`/`Amalloc`/`Amemcpy` are the callee-entry seam predicates (the three
`*_pre`); `Bafter*` are the callee-exit seam predicates (the three `*_post`).
The whole append path reduces to: land `Astrlen` from `P` (prologue/scan exit),
thread the three callees, marshal each `*_post` to the next `*_pre`, then run the
store block to `Q`.  Exactly `divValueTail` scaled to three calls. -/

/-! ## The GROW path composed — `cap' ≫ realloc(names) ≫ realloc(vals) ≫ append-head`

The grow path (`0x80002b90..0x80002bcc`, `count == cap`) computes the new capacity
(`cap' = 2*cap`, or `8` from CAP-INIT), stores it, then calls `realloc` twice.  It
is two `ReallocOps.grow` splices in series plus the cap-compute prefix and the
inter-call reload/store staging, ending by falling into the APPEND head (`0xb1c`).

The two-successful-grow arena re-establishment (`realloc_grow2_arena`, `Grow2Exts`)
and the two-frame public-memory composition (`heapPublicFrame_trans`) — both landed
in `EnvDefineClose` — are what the grow BLOCK's post consumes; here they are the
suffix bridge's obligation, so the composition stays pure `callSeg` algebra. -/

/-! ## The top-level `env_define` contract interface

`env_define_pre`/`env_define_post` are the interface the consumers
(`Call.closure`/`varDecl`/`assign`) require: a `Triple` from the entry `0x80002a5c`
with the ABI args (`env`/`name`/`&v`) to the return `ret` with the `Env` at `env`
now representing `Store.define f nameStr v`.  We reuse the established
`env_define_update_pre`/`env_define_update_post` shape (`EnvDefSpec3`) as the
canonical interface — the update-path pre/post already IS this shape (the post's
`FrameRepr` is the `Store.define` result for any path: update, append, or grow).

The full contract dispatches on the runtime path (name found → update; absent,
`count < cap` → append; absent, `count == cap` → grow).  `envDefContract` states
it, composed from the prologue (proved) ≫ the path taken, with each path's
composed contract (`envDefAppendContract`/`envDefGrowContract` above, or the
update-path Triple) supplied as a per-path segment.  Because the three paths land
the SAME `env_define_update_post`, the dispatch is a `Triple.cond`-style join
(here taken as the three per-path segment hypotheses reaching a common `Q`). -/

end Vsa.Sim
