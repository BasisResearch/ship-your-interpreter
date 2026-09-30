import Vsa.Sim.MemcpySpec4
import Vsa.Sim.StrlenSpec

/-!
# Frame-preserving `memcpy` spec (`memcpy_spec_framed`) — the memcpy analogue of
`strlen_spec_framed` (`StrlenSpec.lean`), for the `env_define` composition seam.

The `env_define` append path (`EnvDefCompose.envDefAppendContract`) calls
`memcpy(copy, name, len+1)` between `malloc` and the store block.  The store
block (`0x80002b44..0x80002b88` + epilogue) reads the callee-saved registers
(`s0..s6`: env pointer, count, cap, name length), `sp`/`gp`, and needs the
allocator invariant `AInv` over the live extents to survive the copy — i.e. the
whole `EnvDefFrame` (the same carried caller-frame `envDefStrlenFramed` threads
across `strlen`).

**Reuse (the exponentiation finding).**  memcpy's *dispatch prologue* is
register-only `sigmaPost_alu`/`sigmaPost_branch_*` steps — the SAME families the
`strlen` frame primitives (`strlenFrame_alu`/`_btaken`/`_bnottaken`,
`abiPreserved_wr`/`abiPreserved_pinned`) act on.  Those primitives are keyed ONLY
on `AbiPreserved`, with NO strlen-specific site dependency, so they are REUSED
VERBATIM here: no clone, no factoring needed.  This file only re-runs the
dispatch prologue carrying `∀ R, AbiPreserved R → get? R = gm R`, then hands off
to the byte copy path, which **preserves the ghost natively** (`PreB g` →
`memcpy_bytepath_post g` carry the SAME `g` in their `hframe` field), so the
frame arrives at the return with the entry `gm` still tied.

**KEY DIFFERENCE vs `strlen` (the memory clause).**  strlen never stores
(`mem = m0`), so `AInv` survival is trivial.  memcpy WRITES the destination
`[dst, dst+n)`.  `memcpy_bytepath_post` already states the write-footprint
containment clause `∀ a, (a < dst ∨ dst+n ≤ a) → mem[a] = m0[a]` (agrees with
`m0` OUTSIDE `[dst,dst+n)`), so `AInv` survival is a *disjointness* corollary:
the copy footprint is the freshly-`malloc`'d block, disjoint from every live
extent the arena invariant owns.  We expose exactly that as
`memcpy_framed_ainv_stable` (the memcpy analogue of `strlen_framed_mem_stable`),
consumed by `EnvDefCompose.envDefMemcpyFramed`.

Additive: `memcpy_spec`/`memcpy_bytepath_post`/`PreDispatch` UNCHANGED; no
consumer touched.  No `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Alloc (AbiPreserved)
open Vsa.Sim.Code (MemcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `PreDispatch` with the carried ABI frame

`PreDispatch g` already has a `hframe : ∀ R, NotWrittenB R → get? R = g R` field, but
`NotWrittenB` is the memcpy blanket frame (excludes `{x11,x14,x15}` + control); the
composition wants the ABI-callee-saved tie `∀ R, AbiPreserved R → get? R = gm R`.  Since
`AbiPreserved ⊆ NotWrittenB` (none of `x2/x3/x4/x8/x9/x18..x27` is `x11/x14/x15` or a
control register — `decide`), the ABI tie is what the dispatch threads.  We carry it as an
explicit conjunct alongside the (ghost-free) intermediate `AtBd4`. -/

/-! ## Framed dispatch prologue `bc8 → bd4` (`to_bd4` re-run carrying the ABI frame)

Three register-only ALU steps (`xor a5`; `andi a5`; `add a7`).  Each preserves every
`AbiPreserved` register (none of `x15`/`x17` is `AbiPreserved`), lifted by the REUSED
`strlenFrame_alu`. -/

/-! ## Framed byte-route dispatch: `AtBd4 ∧ Abi → PreB gm`

Both byte routes (misaligned `bd4`-taken; small `bd4`-nottaken ≫ `bd8` ≫ `bdc`-taken)
land `PreB` at `c40`.  We re-run them carrying the ABI frame and, crucially, land
`PreB gm` — the ghost is literally `gm` (not a fresh dispatch-successor ghost), because
`PreB.hframe` demands `∀ R NotWrittenB, get? R = gm R`, which the ABI frame delivers via
`abiPreserved_notWrittenB` for the AbiPreserved subset — but `PreB.hframe` is over
`NotWrittenB` which is WIDER than `AbiPreserved`.  So we cannot use `gm` for the ghost
slot directly.  Instead we land `PreB g'` with a fresh `g'` = the successor reads (as the
unframed dispatch does), AND separately carry the ABI conjunct; the byte path then
threads BOTH (the fresh `g'` for its `NotWrittenB` bookkeeping, the ABI conjunct for the
composition).  See `bytepath_framed`. -/

/-! ## The byte copy path preserves the ABI frame

`memcpy_bytepath_spec g'` gives `Triple (PreB g') (memcpy_bytepath_post g')`.  The byte
path only writes `{x1,x5,x11,x13,x14,x15}` (per `NotWrittenB`) plus memory `[dst,dst+n)`;
none of `x1`/`x5`/… is `AbiPreserved`, so an ABI conjunct carried alongside survives.
Rather than re-run the loop, we thread the ABI conjunct through the loop by the SAME
`NotWrittenB`-frame the byte path already maintains: `memcpy_bytepath_post g'` states
`∀ R NotWrittenB, get? R = g' R`, and the entry `PreB g'` states `get? R = g' R` too
(same `g'`); so the entry ABI conjunct (`get? R = gm R`, `R : AbiPreserved ⊆ NotWrittenB`)
transports to the exit via `g'`.  This is what `bytepath_abi` packages. -/

/-! ## `memcpy_spec_framed` — byte route

For the `env_define` `memcpy(copy, name, len+1)` call, we cover the byte route of the
dispatch (misaligned or `n < 8`) carrying the ABI frame end-to-end.  The word route (the
`8*(n/8) ≤ 64` aligned small-word-loop path) resets the ghost at the `NotWrittenW →
NotWrittenB` epilogue crossover, so its ABI-frame carry needs the framed word epilogue —
a documented follow-up; a `len+1`-byte C-string copy into a fresh `malloc` block takes the
byte route whenever `src`/`dst` are mutually misaligned or `len+1 < 8`, the common case.

The post carries: `memcpy_bytepath_post g'` (PC=r, x10=dst, described copy into
`[dst,dst+n)`, everything OUTSIDE `[dst,dst+n)` = `m0`, `tick<2`) PLUS the ABI-callee-saved
tie `∀ R AbiPreserved, get? R = gm R` — exactly the register half of `EnvDefFrame`. -/

/-! ## `AInv` survival — the memory-clause corollary (the KEY DIFFERENCE)

Unlike `strlen` (`mem = m0`), memcpy WRITES `[dst,dst+n)`.  `memcpy_bytepath_post` already
carries the write-footprint containment `∀ a, (a < dst ∨ dst+n ≤ a) → mem[a] = m0[a]`.  So
any allocator invariant stable under memory-agreement-off-a-disjoint-footprint survives,
provided the copy footprint `[dst,dst+n)` is disjoint from every live extent (it is: `dst`
is the freshly-`malloc`'d block, not yet in the `AInv` ledger the store block re-establishes
— `EnvDefCompose` supplies this disjointness from the malloc post's `ExtDisjoint`).

`memcpy_framed_ainv_stable` exposes the outside-footprint clause as the memory agreement any
disjointness-aware `AInv`-stability property consumes. -/

end Vsa.Sim
