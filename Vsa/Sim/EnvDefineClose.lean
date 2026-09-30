import Vsa.Sim.HeapOps

/-!
# `EnvDefineClose` — the `env_define` grow-path ledger algebra (L5, brick 1)

`EnvDefSpec.lean`'s "Remaining" note staged the append/grow path as blocked on
"no landed realloc spec". That blocker is GONE: `Vsa/Sim/ReallocSpec.lean`
(Wave-A/B integration) supplies `ReallocOps` — the parameterized grow/null
contracts over one allocator invariant `AInv` and private footprint
`privFoot` — and `Vsa/Sim/HeapOps.lean` packages malloc + realloc onto that
one ledger.

This file lands the first brick of the close: the **grow-path ledger algebra**
the machine's grow block (`0x80002b90..0x80002bc0`: `cap' = if cap == 0 then 8
else 2*cap`; `realloc(names, cap'*8)`; `realloc(vals, cap'*24)`) consumes:

* `mem_erase_mono` / `pairwise_erase` / `mem_erase_of_pairwise` — the
  `List.erase` algebra over a pairwise-`ExtDisjoint`, positive-sized extent
  ledger (a set-like ledger: duplicates are ruled out by self-disjointness);
* `realloc_grow2_arena` — two sequential SUCCESSFUL grows over ONE ledger:
  the composed extent list (`Grow2Exts`) is again a `HeapArena` — live,
  in-arena, pairwise disjoint — from the two results' disjointness clauses
  and the entry arena. The `AInv` re-establishment at the composed list is
  the grow BLOCK's obligation (it is abstract in `HeapOps`), taken as an
  explicit hypothesis at the call site;
* `heapPublicFrame_trans` — two sequential public-memory frames compose over
  the concatenation of their excepted extents (the four-extent frame of the
  two-call footprint).

Remaining bricks (per `experiments/exponentiation-plan.md` L5, each its own
workstream): the grow BLOCK's machine decode (a `#derive_case` chain through
`0x80002b90..0x80002bc0` feeding two `ReallocOps.grow` Triples through the
L4 `callStep` seam), the append path (strlen/malloc/memcpy), and the scan-loop
+ path-dispatch assembly into the top-level
`env_define_spec : Triple env_define_pre env_define_post` that unblocks the
`Call.closure`/`assign`/`varDecl` callers.

Timing witness (2026-08-26): pure Prop/list algebra — no reflection, no
machine decode; see the commit gate for the build time.
-/

open LeanRV64DExecutable Vsa
open Vsa.RuntimeRepr (Arena)
open Vsa.Alloc (StackLayout ExtDisjoint)

