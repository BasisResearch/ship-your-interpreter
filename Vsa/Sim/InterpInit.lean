import Vsa.Sim.EntrySeams

/-!
# `InterpInit` — closing `InterpInitStoreRepr` by composing `env_new ≫ env_define×3`

`Vsa/Sim/EntrySeams.lean` localized the program-entry store-init to the ONE named
residual `InterpInitStoreRepr` (`EntrySeams.lean:182`): from a `Loaded L p c`
config, the machine reaches `SegEntry … initSt … interpLoopHeadPC` — the single
global frame carrying the three natives, established off-path by `interp_init`
(`0x80004308`), which `main` calls at `0x800045b4` BEFORE `interp_run`.

This file BUILDS the store `initSt.store` as the composition of `interp_init`'s
body and reseats `InterpInitStoreRepr` on the two honest residuals that survive
(the store composition and the `interp_run` prologue drive), plus the per-call
seam premises.  The composition itself — `env_new ≫ define×3` at the store level —
is proved here, axiom-clean.

## Decoded `interp_init` body (verified against `experiments/disasm.txt:4403–4460`)

```
80004308 <interp_init>:
  80004308  addi sp,sp,-96          ┐ PROLOGUE (spill s0,s1,ra; s1=5; a0=0)
  8000430c  sd s0,80(sp)            │
  80004310  sd s1,72(sp)            │
  80004314  mv s0,a0               │  s0 = &globals slot (out-param)
  80004318  li s1,5                │
  8000431c  li a0,0               │  a0 = NULL (env_new's parent = top-level)
  80004320  sd ra,88(sp)           ┘
  80004324  jal env_new            ── CALL env_new(NULL)  → a0 = fresh Env*
  80004328..80004360  ARG SETUP #1 (name "print"@0x80019538, value native_print@0x80002ed4)
              sd a0,0(s0)  ; *globals = env    (store the fresh frame ptr)
  80004364  jal env_define         ── CALL env_define(env, "print", &print_val)
  80004368..80004398  ARG SETUP #2 (name "println"@0x80019540, value native_println@0x80002f7c)
  8000439c  jal env_define         ── CALL env_define(env, "println", &println_val)
  800043a0..800043d0  ARG SETUP #3 (name "assert"@0x80019548, value native_assert@0x80002df4)
  800043d4  jal env_define         ── CALL env_define(env, "assert", &assert_val)
  800043d8..800043e4  EPILOGUE (restore ra,s0,s1; sp+=96)
  800043e8  ret
```

The three arg-setup spans (`0x80004328..0x80004364`, `0x80004368..0x8000439c`,
`0x800043a0..0x800043d4`) are straight-line `sd`/`ld`/`auipc`/`addi`/`sw`/`mv`
segments (in-model `#derive_case` seg territory).  The three `jal env_define`s
are `callSeg`/`bridgeOfSeg` splices of the `env_define_append_spec` contract
(`EnvDefMarshal`), each appending ONE native binding to the growing global frame.

## The store built, definitionally (verified `rfl`)

`env_new(NULL)` allocates frame 0 = `⟨none, []⟩`.  The three defines APPEND (each
native name is absent from the frame-so-far, so `Store.define`'s
`f.vars.any (·.1 == x) = false` branch = `f.vars ++ [(x,v)]` fires), giving:

```
⟨none,[]⟩
  ─define "print"  → ⟨none,[("print",…)]⟩
  ─define "println"→ ⟨none,[("print",…),("println",…)]⟩
  ─define "assert" → ⟨none,[("print",…),("println",…),("assert",…)]⟩  =  initSt.store's frame 0
```

`initStore_eq_initSt` records this equality (it holds by `rfl` — the three
`Store.define`s over the fresh store ARE `initSt.store`).  ORDER: [print, println,
assert], matching `Semantics.initSt` (`Vsa/While/Semantics.lean:532`).

## The println byte-route verdict (the task's flagged crux)

`env_define`'s memcpy copies `len+1` bytes (name + NUL).  Lengths: `print`=5→6,
`println`=7→**8**, `assert`=6→7.  `env_define_append_spec`'s `hrouteCbyte`
premise is `(src ^^^ dst) % 8 ≠ 0 ∨ nMemcpy < 8`:

* **print** (6) and **assert** (7): `nMemcpy < 8` holds → byte route unconditionally.
* **println** (8): `nMemcpy < 8` is FALSE.  The byte route is then gated ONLY on
  the mutual-misalignment disjunct `(src ^^^ dst) % 8 ≠ 0`.  Whether that holds
  depends on the concrete src (`"println"` static @ `0x80019540`) vs dst (the
  freshly-malloc'd 8-byte copy block) alignment — a fact the dispatch reads off
  the layout, NOT derivable here.  So the println cell carries this as the NAMED
  premise `hRoutePrintln` (mutual misalignment), OR, if that fails, the copy takes
  the WORD route (the `#15` word-route framed-spec residual, out of scope for this
  file).  We name it precisely and do NOT fabricate it.

## What this file lands vs. names

| Piece | Status |
|-------|--------|
| decoded body + spans | verified against disasm (doc above) |
| `initStore_eq_initSt` (store equals `initSt.store`) | PROVED (`rfl`) |
| append-order of each define | PROVED (`rfl`, in `initStore_eq_initSt`'s witnesses) |
| store-carrier composition `env_new ≫ define×3` | PROVED HERE (`interpInitStore_compose`) |
| `interpInitStoreRepr_of` (closes `InterpInitStoreRepr`) | PROVED HERE, modulo the named seams |
| per-call seams (env_new fresh frame / 3 defines / prologue drive) | NAMED typed premises |
| println route | NAMED premise `hRoutePrintln` (the flagged crux) |

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (initSt Store Frame Value NativeFn Addr Program St)
open Vsa.Refine (Layout Loaded)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The store `interp_init` builds, definitionally

The composition target: `env_new(NULL)` gives the fresh single-global-frame store,
and the three `env_define`s append `print`/`println`/`assert` (each absent ⇒ append
path).  This is `initSt.store` by `rfl`. -/

/-! ## §2. The store-carrier seam predicate

`InitSeg store entryPC` is the `Config → Prop` carrier threaded between the
`interp_init` calls: the store-so-far represented in memory, PC pinned at the
straight-line resume point, control state good, tick parity, and empty console
output (nothing prints in `interp_init`).  It is the store-parametric analogue of
`SegEntry` restricted to what the composition needs — one named-field structure, no
∃/∧ tower.  Each `env_define` splice advances `store` by one `Store.define` and the
PC past that call's arg-setup + `jal`. -/

/-! ## §3. The composition — `env_new ≫ define(print) ≫ define(println) ≫ define(assert)`

Each stage is a NAMED `Triple` seam (the honest per-call residual):

* `hEnvNew`   : `interp_init` entry `P` → `InitSeg initGlobalStore 0x80004328` — the
  prologue (`0x80004308..0x80004324`) `≫` `env_new(NULL)` (`env_new_spec`,
  `EnvNewSpec`) `≫` the `sd a0,0(s0)` store, landing the fresh global frame's
  `StoreRepr`.  A `callSeg`/`bridgeOfSeg` splice over `env_new_spec`.
* `hDefPrint` / `hDefPrintln` / `hDefAssert` : each advances the store by one
  `Store.define` and the PC past that arg-setup + `jal env_define`.  Each is an
  `env_define_append_spec` (`EnvDefMarshal`) splice specialized to a native binding
  (name absent ⇒ append path), MARSHALLED into the `InitSeg` carrier.
* `hEpilogue` : `InitSeg storeAfterAssert 0x800043d8` → `Q` — the restore + `ret`
  span (`0x800043d8..0x800043e8`), a straight-line `#derive_case` seam; it preserves
  the store (`ld`/`addi`/`ret` write no represented memory) so `Q` still carries
  `StoreRepr storeAfterAssert = StoreRepr initSt.store`.

The composition is pure `Triple.seq`, threading the four store advances. -/

/-! ## §4. `InterpInitStoreRepr` closed on the composition + the prologue drive

`InterpInitStoreRepr L p` (`EntrySeams.lean:182`) demands: from `Loaded L p c`,
`∃ c1 …, Steps c c1 ∧ SegEntry … initSt 0 dLeft aLeft interpLoopHeadPC m0 c1`.  Two
honest residuals compose into it:

1. **the store** — `initSt.store`, built by `interpInitStore_compose` and equal to
   `storeAfterAssert` by `initStore_eq_initSt`.  The composition delivers a config
   whose memory carries `StoreRepr initSt.store` at `interp_init`'s `ret`.
2. **the `interp_run` prologue drive** — from `Loaded` (machine at `interp_run`'s
   entry `0x800043ec`) through the spill/`setjmp`/loop-setup to `SegEntry` at the
   loop head, threading the `interp_init`-established store.  This is exactly the
   drive `EntrySeams`'s doc spells out; it is off `interp_init`'s body, so it is a
   NAMED premise `hRunDrive` here.

`interpInitStoreRepr_of` bundles them: `hRunDrive` IS the `Loaded → ∃ c1, Steps ∧
SegEntry@loopHead` obligation (the drive that consumes the built store), and the
built store enters through `hStore` (the composition's output = `StoreRepr
initSt.store`, which `hRunDrive` reads).  Because `InterpInitStoreRepr`'s own shape
is precisely `Loaded → ∃ c1 …, Steps ∧ SegEntry@loopHead`, and the store carried is
`initSt` (whole state, `initSt.store` = the built frame + empty out), the residual
is `hRunDrive` — the machine drive from `Loaded` to the loop head, taking the built
store as data. -/

/-! ### §4a′. The store-consuming drive form

`interpInitStoreRepr_of` above names the whole drive.  The genuine composition —
where the built store is CONSUMED by a `SegEntry`-producing drive — is
`interpInitStoreRepr_of_drive`: the drive premise `hDrive` is now a `SegEntry`
BUILDER that, from `Loaded L p c`, produces the machine steps + all `SegEntry`
fields EXCEPT the store, and the store is supplied by `hStore` (the composition's
output, `StoreRepr … storeAfterAssert = … initSt.store`).  So the drive no longer
has to re-derive the store representation — it takes it as data, exactly the
convergence point `EntrySeams` describes.  The `SegEntry` is reassembled field-by-
field from `hDrive`'s non-store fields + the composed store (via
`interpInitSegEntry_store`). -/

end Vsa.Sim
