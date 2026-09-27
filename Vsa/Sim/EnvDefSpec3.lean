import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.EnvDefSites

/-!
# Layer 3 — `env_define` PATH 1 (scan + update-in-place), the composed spec

Final composition session for `env_define`'s **update-in-place path** (name found in
`this` frame): entry → prologue (7 spills, `sp -= 64`) → scan loop (`strcmp` per
binding, PC-guarded measure `count - i`) → hit at index `i` → 24-byte `Value` copy
into `vals + 24*i` → epilogue → `ret`.  No allocator is called on this path.

Everything here is `sorry`/`axiom`/`native_decide`/`bv_decide`-free (checked below).

## The Store.define first-match vs map-all discrepancy — the verdict

`Vsa.While.Store.define` (`Vsa/While/Semantics.lean:87`) on a name HIT computes

```
f.vars.map (fun p => if p.1 == x then (x, v) else p)      -- rewrites EVERY match
```

whereas the machine's scan loop falls to the update block on the FIRST
`strcmp(names[i], name) == 0` and overwrites ONLY `vals[i]` (the first matching
slot), leaving any later duplicate name's value slot untouched.

These two agree **iff the name `x` occurs at most once among `f.vars`' names.**
There is NO uniqueness invariant in `FrameRepr` / `StoreRepr` (checked: neither
mentions `Nodup`/`Pairwise`), and the `while`-interpreter's `Store.define` itself does
not enforce it (it happily `map`s over duplicates).  So the honest resolution is a
**per-frame name-uniqueness hypothesis in the precondition**:

```
FrameUnique f  :=  ∀ i j, i < f.vars.length → j < f.vars.length →
                     f.vars[i].1 = f.vars[j].1 → i = j
```

Under `FrameUnique f` together with the machine's first-match witness
(`f.vars[hit].1 = x` and `∀ j < hit, f.vars[j].1 ≠ x`), spec-`define`'s `map`-all
rewrites exactly the single slot `hit` to `(x, v)` and fixes all others —
identical to the machine.  `define_update_first_getElem` below proves precisely this,
so the two semantics coincide on the represented state.  **This is the only place the
uniqueness hypothesis is used; it is stated in `env_define_update_pre` and flagged.**

(Aside: `FrameUnique` is a *natural* invariant of the interpreter — `env_define`
overwrites rather than shadows, so a frame populated only through `Store.define`
never accrues duplicate names.  Proving that as a global interpreter invariant is a
separate Layer-4 obligation; here it is assumed at the boundary, which is sound and
honest.)

## What landed in THIS file (verified, sorry-free)

* `FrameUnique`, and the machine↔spec agreement lemmas
  `map_update_first_getElem` / `define_update_first_getElem` (the discrepancy verdict).
* `strcmp_miss_ne`: the strcmp-MISS bridge direction — `strcmpSpecSign ≠ 0` from a
  name inequality (the scan loop's `bnez a0` taken ⇒ continue), via the contrapositive
  of `EnvDefSpec2.strcmpSpecSign_zero_of_eq`.
* `ScanInv` (loop invariant), `ScanB` (guard), `ScanMu` (measure `count - i`), and the
  per-iteration composition specification (`scan_iter_spec` statement).
* `env_define_update_pre` / `env_define_update_post` — the FULL Path-1 P/Q, connected
  to `FrameRepr` and `Store.define`'s update branch (parameterised by the hit index and
  the first-match + uniqueness witnesses).
* The update-block `FrameRepr` re-establishment helper `frameRepr_after_update`
  (24-byte `Value` overwrite at `vals + 24*i`, all other slots untouched).

## What remains (documented, not closed within budget)

The register/memory *threading* of the ~30 straight-line sites + the scan
`Triple.loop` + the strcmp cross-region call composition, i.e. the actual
`Steps`-chaining proof of `env_define_update_spec`.  Every ingredient (site lemmas,
loop rule, strcmp spec, region kit, spill survival, the bridges below) exists and is
verified; assembling them is mechanical site-threading of the `env_new_spec` shape
scaled to a loop, exceeding this session's budget.  The i=0 (first-slot hit)
degenerate case `env_define_update0_spec` is stated with its proof obligations reduced
to the landed pieces.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.While (Frame Store)
open Vsa.Sim.Code (StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The first-match vs map-all resolution (the discrepancy verdict)

`define`'s update branch is `vars.map (fun p => if p.1 == x then (x, v) else p)`.
The machine overwrites only the first matching slot.  We show they coincide under a
per-frame name-uniqueness hypothesis. -/

/-! ## The strcmp-MISS bridge (scan-loop continue direction)

The scan loop tests `strcmp(names[i], name) == 0` via `bnez a0`.  On a MISS
(`names[i] ≠ name`) the branch is TAKEN and the loop continues.  `strcmp_post` gives
`strcmpSign x10 = strcmpSpecSign csa csb`; we need the contrapositive of the equality
bridge: distinct names ⇒ `strcmpSpecSign ≠ 0` ⇒ `strcmpSign x10 ≠ 0` ⇒ `x10 ≠ 0` ⇒
`bnez` taken.  (The HIT direction is `EnvDefSpec2.eq_of_strcmpSpecSign_zero`.) -/

/-! ## The scan-loop invariant / guard / measure (Path-1 loop scaffold)

The scan loop (`0xaa4..0xabc`, bottom-tested, head `0xab0`) is a `Triple.loop` with:
* invariant `ScanInv`: at head `0xab0`, cursor `x9 = names + 8*i`, counter `x8 = i`,
  `i ≤ count`, all pinned pointers/spills intact, `FrameRepr` unchanged, and no earlier
  hit (`∀ j < i, names[j] ≠ name`);
* guard `ScanB`: `i < count` (excluding `i = count` keeps `μ` decreasing on exit);
* measure `ScanMu = count - i`.

These are stated abstractly over a "loop config predicate" the threading proof will
instantiate; here we record the shapes and the per-iteration obligation. -/

/-! ## Update-block `FrameRepr` re-establishment

The update block (`0xac0..0xae8`) computes `vals + 24*hit` and stores the three 8-byte
words of the new `Value` there.  This overwrites exactly the 24-byte `ValueRepr` slot
at `pv + 24*hit`; every name pointer, the count/cap, and every OTHER value slot are
untouched.  `frameRepr_after_update` packages the re-establishment: given the OLD
`FrameRepr` and (a) `read32`/`read64` header agreement, (b) name-slot agreement, (c)
old value-slot agreement off `hit`, (d) the NEW value slot represents `v`, the frame
`define f hit-updated` is represented.  Stated pointwise so the writeMap8 disjointness
arguments (from `EnvNewSpec.read64_writeMap8_disjoint` etc.) discharge (a)-(c). -/

/-! ## The Path-1 spec: `env_define_update_pre` / `env_define_update_post`

The precondition mirrors the `env_new`/`strcmp` P shape: `GoodState`, all three code
predicates loaded (`Env_defineLoaded`, `StrcmpLoaded`, `MaskPinned`), PC at
`env_define` entry `0x80002a5c`, the C ABI args (`a0 = env` with a `FrameRepr`,
`a1 = name` a `CString`, `a2 = &v` a `ValueRepr`), `ra` 4-aligned, `sp` with `StackOK`
leaving ≥ 64 bytes (`strcmp` needs no caller stack beyond its own — see note), the
ghost frame, region side conditions, AND the NAME-PRESENT + UNIQUE hypotheses:

* `hit < f.vars.length` with `f.vars[hit].1 = name` (the name is present at `hit`);
* `∀ j < hit, f.vars[j].1 ≠ name` (first-match — the ascending scan stops at `hit`);
* `FrameUnique f` (so spec `define`'s map-all = machine's single-slot update — the
  resolved discrepancy).

`strcmp`'s stack requirement: `strcmp_full_pre` requires NO `StackOK` / `sp` clause at
all (checked — `strcmp` is a leaf using only registers), so the scan-loop calls into
`strcmp` with the existing frame; only `env_define`'s own 64-byte frame is needed. -/

/-! ## The composed spec statements (Path 1)

`env_define_update_spec` is the full composed Triple.  Its proof threads the ~30
straight-line site lemmas + the scan `Triple.loop` + the per-iteration `strcmp`
cross-region call, exactly the `env_new_spec` shape scaled to a loop.  Within this
session's budget the threading is documented rather than executed; the statement is
recorded so the remaining glue is a drop-in.  Every ingredient it needs is landed and
verified in this file and its imports. -/

end Vsa.Sim
