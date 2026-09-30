import Vsa.Sim.EnvGetSpec3
import Vsa.Sim.HeapOwnershipGeometry
import Vsa.Sim.MemcpySpec4
import Vsa.Sim.rows.EnvDefineEpilogueCore

/-!
# `EnvDefBridges3` — the grow-path `bridgeNamesToVals` machine bridge + the
`GrowEnvEntry` struct-field carrier

`Vsa/Sim/EnvDefCompose.lean`'s `envDefGrowContract` leaves the grow path's inter-call
staging as the named hypothesis `bridgeNamesToVals`, whose source is the FIRST realloc's
post (`ReallocPost(names) ∧ ReallocGrowResult(names)`) and whose target is the SECOND
realloc's entry predicate `ReallocPre(vals)`.  The prefix `0x80002ba4..0x80002bbc` reads
`Env`-struct fields, stores the new `names` pointer, and computes the `vals` realloc args:

```
80002ba4  lw   a5,4(s4)     -- x15 := env->cap   (= newcap, from bridgeCapCompute's sw)
80002ba8  sd   a0,8(s4)     -- env->names := a0  (the realloc(names) result pointer)
80002bac  ld   a0,16(s4)    -- x10 := env->vals  (pValsOld, the realloc(vals) arg p)
80002bb0  slli a1,a5,1      -- x11 := newcap*2
80002bb4  add  a1,a1,a5     -- x11 := newcap*3
80002bb8  slli a1,a1,3      -- x11 := newcap*24  (the realloc(vals) arg n)
80002bbc  jal  realloc      -- x1 := 0x80002bc0, PC := reallocEntry
```

## The `GrowEnvEntry` struct-field carrier (item 1)

`bridgeCapCompute`'s `GrowCapEntry` only pinned the cap REGISTER `x15`.  This staging
bridge additionally READS the `Env`-struct field CONTENTS (`env->cap` at `s4+4`,
`env->vals` at `s4+16`), which the cap-compute source did not expose.  `GrowEnvEntry`
is the additive frame-carrying carrier that pins those field contents (as `read64`/`read32`
facts) alongside the `EnvDefFrame` caller-frame — exactly the `envDefStrlenFramed`/
`bridgeCapCompute_closed` precedent.  The pinned struct words survived the first realloc
because they live in the caller's `Env` struct (public memory, disjoint from the realloc'd
extent), so the realloc post's `HeapPublicFrame` outside-clause preserves them; the carrier
takes them as data (the caller/dispatch knows the `Env` layout and its field values).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Site step lemmas for the names→vals staging prefix -/

/-! ## The names→vals staging prefix run: `0x80002ba4..0x80002bbc`

Chains all seven steps.  From a state at `0x80002ba4` with `x20 = s4Ptr` (`env` base),
`x10 = pNamesNew` (the realloc(names) result), and the pinned struct fields
`env->cap = read32 m0 (s4+4)` / `env->vals = read64 m0 (s4+16)`, runs to `reallocEntry`
with:
* `x10 = pValsOld` (`env->vals`, the realloc(vals) arg `p`),
* `x11 = env->cap * 24` (the machine shift/add result, realloc(vals) arg `n`),
* `x1 = 0x80002bc0` (link),
* memory = the input memory with `env->names` (word at `s4+8`) overwritten by `pNamesNew`
  (`= writeMap8 m0 (s4+8) (sdData_val pNamesNew)`),
* every register outside the write set `{x15, x10, x11, x1}` + control preserved (in
  particular `x2`/sp, `x3`/gp and every other callee-saved).

The `env->vals` read at `s4+16` survives the intervening `sd` at `s4+8` because the two
8-byte windows `[s4+8,s4+16)` / `[s4+16,s4+24)` are disjoint (`read64_writeMap8_disjoint_eg6`).
The `env->cap` read at `s4+4` happens BEFORE the `sd`, so it reads `m0` directly. -/

/-! ## The `GrowEnvEntry` struct-field carrier (item 1)

The additive frame-carrying carrier for the grow path's inter-realloc staging.  Beyond the
`EnvDefFrame` caller-frame (sp/gp/ABI-callee-saveds/AInv) it pins the `Env`-struct field
CONTENTS the staging reads — `env->cap` (at `s4+4`) and `env->vals` (at `s4+16`) — as
`read32`/`read64` facts on the CURRENT memory, plus the machine state at `0x80002ba4`.  Those
struct words survived the first realloc: they live in the caller's `Env` struct (public
memory, disjoint from the realloc'd extent), so the realloc post's `HeapPublicFrame`
outside-clause preserved them; the dispatch/scan (which owns the `Env` layout) supplies their
values as data — exactly the `AppendStrlenEntry`/`GrowCapEntry` precedent.

`s4Ptr` = the `env` base; `pValsOld` = `env->vals` = the second realloc's arg `p`;
`pNamesNew` = the first realloc's result (stored into `env->names`).  This structure is what
the top-level dispatch builds and threads into `bridgeNamesToVals_closed`. -/

/-! ## `bridgeNamesToVals` discharged — FRAME-CARRYING

From the first realloc's post enriched with the struct-field pins (`GrowEnvEntry`), the
`lw;sd;ld;slli;add;slli;jal realloc` staging lands the SECOND realloc's entry predicate
`ReallocPre(vals)`.  The frame (sp/gp/callee-saveds) survives because the staging writes only
`{x15,x10,x11,x1}` (and one memory word, `env->names`); `AInv` survives the `env->names`
store via the named `hAInvStableNames` (store-analogue of `bridgeCapCompute`'s
`hAInvStableCap`: the `env->names` word is inside the caller-owned `Env` struct, disjoint from
every allocator extent).

Value ties supplied by the caller (dispatch/scan, which knows the concrete `cap`):
* `hpTie` : the loaded `env->vals` = `ofNat pValsOld` (via `ld_value_eq_read64`; supplied as a
  named premise packaging that bridge over the `valsEq` pin),
* `hnTie` : the machine shift/add result `env->cap*24` = `ofNat nValsNew`. -/

/-! ## Wiring adapter: the contract's `bridgeNamesToVals` premise from `bridgeNamesToVals_closed`

`envDefGrowContract`'s `bridgeNamesToVals` premise is sourced at `ReallocPost(names) ∧
ReallocGrowResult(names)` (the first realloc's exact post), not at `GrowEnvEntry`.  This adapter
seqs the `ReallocPost ∧ ReallocGrowResult → GrowEnvEntry` construction (deriving the machine
state from `ReallocPost`, the new names pointer from `ReallocGrowResult`'s success case, and
the struct-field pins as caller data — they survived the realloc via `ReallocGrowResult`'s
`HeapPublicFrame`, so the dispatch knows their `mN`-values) into `bridgeNamesToVals_closed`,
producing the contract premise VERBATIM (with `rN := 0x80002ba4`, `spV := spN`, `rV := 0x80002bc0`,
`mV := writeMap8 mN (s4+8) (sdData_val pNamesNew)`).

The struct pins, geometry, ties, ABI-ghost tie, and AInv-stability are the named residuals the
dispatch/scan supplies — exactly the `AppendStrlenEntry`/`GrowCapEntry` discipline.  This makes
the grow-path names→vals seam a direct `Triple.seq` plug into `envDefGrowContract`, no gap in the
machine reasoning. -/

/-! ## `frameRepr_append` — the FrameRepr append core (item 3)

The append path's store block (`0x80002b44..0x80002b88`) writes the copied name pointer
into `names[count]`, the value into `vals[count]`, and `count+1` into `env->count`, turning
`FrameRepr … e f` into `FrameRepr … e (f` with `(x,v)` appended`)` — the append (name-absent)
case of `Store.define`.  `foundSt_of_storeRepr` (`EnvGetMarshal`) is the REVERSE direction
(`StoreRepr → FoundSt` for a HIT); this is the forward append.

This core lemma is stated purely on the post-store memory `m` (no machine steps): given the
readback facts for the EXTENDED structure — the new count `n+1`, the cap with `n+1 ≤ cap`, the
`names`/`vals` base pointers, the OLD `n` slots' name+value representations surviving, the NEW
slot's `CString`/`ValueRepr`, and the parent unchanged — it assembles `FrameRepr m N φf φc e f'`
for the frame `f'` whose `vars = f.vars ++ [(x,v)]`.  It is the shared spec-side reconstruction
the task flags: it serves `bridgeStore` (append path) AND the `env_define`-update append arm AND
`Call.closure`'s env-fold (each appends one bound slot to a `FrameRepr`).

The residual for the LIVE `bridgeStore` is only the MACHINE side (the store-block Steps chain
threading the four `sd`/`sw` sites + the count fold, delivering exactly these readback facts) —
named, not built here; this lemma discharges the FrameRepr-reconstruction content it feeds. -/
theorem frameRepr_append (m : Vsa.MemRepr.Mem) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat)
    (e : Nat) (parent : Option Vsa.While.Addr) (vars : List (String × Vsa.While.Value))
    (x : String) (v : Vsa.While.Value) (cap pn pv : Nat)
    -- header: count = n+1, cap with n+1 ≤ cap, names/vals base pointers.
    (hcount : read32 m e = some (vars.length + 1))
    (hcap : read32 m (e + 4) = some cap) (hcapLe : vars.length + 1 ≤ cap)
    (hpn : read64 m (e + 8) = some pn) (hpv : read64 m (e + 16) = some pv)
    -- OLD slots survive (their name pointer + CString + value representation).
    (hold : ∀ i, (h : i < vars.length) →
      (∃ q, read64 m (pn + 8 * i) = some q ∧ CString m q (vars[i].1)) ∧
      ValueRepr m N φc (pv + 24 * i) (vars[i].2))
    -- parent unchanged (given explicitly to avoid a match-type motive capture).
    (hparentNone : parent = none → read64 m (e + 24) = some 0)
    (hparentSome : ∀ pa, parent = some pa →
      read64 m (e + 24) = some (φf pa) ∧ φf pa ≠ 0)
    -- NEW slot (index vars.length): the copied name + the stored value.
    (hnewName : ∃ q, read64 m (pn + 8 * vars.length) = some q ∧ CString m q x)
    (hnewVal : ValueRepr m N φc (pv + 24 * vars.length) v) :
    FrameRepr m N φf φc e ⟨parent, vars ++ [(x, v)]⟩ := by
  -- the extended frame's `.vars` is `vars ++ [(x,v)]` and `.parent` is `parent`, both by rfl.
  refine ⟨?_, ⟨cap, hcap, ?_⟩, ⟨pn, pv, hpn, hpv, ?_⟩, ?_⟩
  · -- count = length of extended vars
    show read32 m e = some (vars ++ [(x, v)]).length
    rw [define_append_length]; exact hcount
  · -- length ≤ cap
    show (vars ++ [(x, v)]).length ≤ cap
    rw [define_append_length]; exact hcapLe
  · -- per-slot: split index into old (< length) vs the new appended slot (= length)
    show ∀ i, (h : i < (vars ++ [(x, v)]).length) →
      (∃ q, read64 m (pn + 8 * i) = some q ∧ CString m q ((vars ++ [(x, v)])[i].1)) ∧
      ValueRepr m N φc (pv + 24 * i) ((vars ++ [(x, v)])[i].2)
    intro i hi
    rw [define_append_length] at hi
    by_cases hlt : i < vars.length
    · -- old slot i: getElem is vars[i]
      have hge : (vars ++ [(x, v)])[i] = vars[i]'hlt := define_append_getElem_old vars x v i hlt
      rw [hge]; exact hold i hlt
    · -- new slot: i = vars.length, getElem is (x, v)
      have hieq : i = vars.length := by omega
      subst hieq
      have hge : (vars ++ [(x, v)])[vars.length] = (x, v) := define_append_getElem_new vars x v
      rw [hge]; exact ⟨hnewName, hnewVal⟩
  · -- parent clause (the frame's `.parent` is `parent` by rfl)
    cases hpa : parent with
    | none => exact hparentNone hpa
    | some pa => exact hparentSome pa hpa

end Vsa.Sim
