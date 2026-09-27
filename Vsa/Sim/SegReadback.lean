import Vsa.Sim.SegFrameFactsAuto

/-!
# `SegReadback` — mechanize two `#derive_case`/`chain_facts` hand patterns

Two hand idioms recur in the str-cmp arm rows (`StrArmChain`) and every future
rejoin/kind-check seg.  Both were fixed by hand there (see
`experiments/observations.md`, `loadbearing-seg-register-readback` and
`chainfacts-branchguard-arith-overflow`); this file turns each into a reusable
brick that the rows call once.

## 1. `gholds_lookup_ld` — register readback off a LOAD-BEARING seg outcome

`gholds_lookup L hregs (by rfl)` (`BlockPilot`) closes register projections for
LOAD-FREE segs: `evalBlocks seg …` reduces to the reg pin under `rfl`.  The
moment the seg body contains an `ld`/`lw`/`lbu`, `rfl` on
`lookupG n (evalBlocks seg (init L lds)).regs = some v` STALLS — `runGM` threads
`stepLdsM .ld lds = lds.tail` + `wvalM .ld (lds.headD [])` with symbolic `lds`,
leaving an un-reducible `bytesVal .ld …` cell in the map spine that whnf refuses
to skip (a NATIVE STACK OVERFLOW at high `maxRecDepth`, not a `rfl` error).

The fix here: a peel lemma `lookupG_runGM_writer` that reads the value the seg's
LAST writer of `n` deposits, peeling the intervening loads structurally with the
existing `srcVal_runGM_ne` (Fix 1a) — never reducing the fold.  It is the
`gholds_lookup` companion the observation asked for.

## 2. `seg_guard_close` — branch-guard closing without deep `rfl`

`chain_facts … all_goals rfl` closes a branch guard whose value is a pinned
literal (`cmpFixupTail`'s `x12 ≠ 21/22/23`).  It does NOT close a guard whose
value is a computed arithmetic (str kind-check's `x15 = x10 - 3 = 0`): `rfl` must
reduce the `addi`'s `sign_extend (-3)` + subtraction through `runGM` with
symbolic `lds` to unbounded depth → SIGABRT.  `seg_guard_close` is the
symbolic-reduce fallback (`simp only [runGM,stepGM,wvalM,srcVal,guardB,…] <;>
decide`) packaged as ONE tactic the facts rows call — additive, never touching
`chain_facts`'s landed leaf-closing behavior.

No `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.  Verify with
`lake env lean Vsa/Sim/SegReadback.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While
open Vsa.Sim.Code

namespace Vsa.Sim

set_option maxRecDepth 4000

/-! ## Part 1 — `gholds_lookup_ld`: readback off a load-bearing seg -/

/-! ### Regression demo (readback) — `strRejoin_x11`'s shape

`rbDemo` is the EXACT `strRejoin` block: `ld x12,0(x2)` then `mv x11,x10`
(`addi x11,x10,0`).  Reading `x11` back off `evalBlocks rbDemo …` is where the hand
`simp only [runGM,stepGM,wvalM,srcVal,…]` + `BitVec.add_zero` (10 lines, 6 field pins)
lived.  Here it collapses to `lookupG_runGM_snoc` (splits the body as `pre ++ [mv]`,
reads the writer's `wvalM`) + `srcVal_runGM_ne` (peels the leading `ld` off the `mv`'s
source read) + the `+ sext 0` cleanup.  NO deep `rfl`, `maxRecDepth` stays at 4000. -/
                -- mv   x11,x10  (addi x11,x10,0)

/-! ## Part 2 — `seg_guard_close`: symbolic-reduce branch-guard fallback -/

/-- `seg_guard_close` closes a `#derive_case`/`chain_facts` branch-guard obligation
whose value is a COMPUTED arithmetic (subtract-and-compare against a pinned register),
without the deep `rfl` that overflows.  It unfolds the guard's `runGM`/`stepGM` tower
symbolically to a concrete `BitVec` comparison and finishes with `decide`.

Call it in the `all_goals` tail of a `*_facts` row AFTER `chain_facts …`, in place of
`all_goals rfl`, when a guard is arith-heavy.  The caller supplies the per-word `mkLine`
field pins as extra `simp` lemmas (they are `rfl` facts the `#derive_case` table already
determines); `seg_guard_close [pin₁, …]` threads them.  The base simp-set (`runGM`,
`stepGM`, `wvalM`, `srcVal`, `guardB`, `lookupG`, `eraseG`, and the `Nat`/`Option`
simprocs) is fixed, so only the decode pins vary per row. -/
syntax "seg_guard_close" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| seg_guard_close $[[ $pins,* ]]?) => do
    let extra := match pins with
      | some ps => ps.getElems
      | none => #[]
    `(tactic|
      simp only [runGM, stepGM, wvalM, srcVal, lookupG, eraseG, guardB,
        $[$extra:term],*,
        Nat.reduceEqDiff, if_true, if_false, Option.getD_some] <;> decide)

/-! ### Regression demo (guard) — `strKindCheck_facts`' shape

`gcDemo` is the EXACT `strKindCheck` two-block chain: `addi x15,x10,-3 ; bnez` (NOT
taken, x10=3 ⇒ x15=0) then `addi x15,x16,-3 ; beqz` (TAKEN, x16=3 ⇒ x15=0).  The two
branch guards are computed arithmetics (`x10-3=0`, `x16-3=0`) — the ones that native-
stack-overflow under `all_goals rfl`.  `chain_facts` closes every mechanical leaf; the
two guards fall to `seg_guard_close` with the per-word `mkLine` field pins.  `maxRecDepth`
stays at 4000 (the file default), never bumped. -/
     -- TAKEN (x15=0) → 0x3b0c

end Vsa.Sim
