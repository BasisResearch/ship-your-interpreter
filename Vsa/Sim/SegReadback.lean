import Vsa.Sim.SegFrameFactsAuto
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.rows.StrCmpSignTail

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

/-- `lookupG n` of a `stepGM` that WRITES `n` (a non-store whose `rd = n`) is
exactly the value written, `wvalM a L bs`.  The one-instruction base case of the
readback: no fold, one match reduction on the concrete `a.kind`. -/
theorem lookupG_stepGM_writer (a : MInstr) (L : GRegs) (bs : List (BitVec 8))
    (hstore : a.kind ≠ .sw ∧ a.kind ≠ .sd ∧ a.kind ≠ .sb ∧ a.kind ≠ .sh) (n : Nat)
    (hrd : a.rd = n) :
    lookupG n (stepGM a L bs) = some (wvalM a L bs) := by
  unfold stepGM
  obtain ⟨h1, h2, h3, h4⟩ := hstore
  cases hk : a.kind <;> first
    | (exact absurd hk (by assumption))
    | (subst hrd; rw [lookupG, if_pos rfl])

/-- **The readback peel.**  A register `n` written by the seg body's LAST
instruction `a` (with the load-free tail `rest` after it not touching `n`) is read
back off `runGM body L lds` as `wvalM a (runGM pre …) …`, peeling the leading loads
with `srcVal_runGM_ne` — never reducing the fold.  Stated in the form a seg row
consumes: the body splits as `pre ++ [a]` with `a.rd = n`, and the value is the
writer's `wvalM` over the peeled-source pin state.

Rather than carry the split abstractly (which forces a `runGM_append` detour), we
expose the single lemma callers actually need — `lookupG_runGM_last`: when the WHOLE
body's last element writes `n` and no later element re-writes it, the readback is the
`wvalM` of that writer.  For the concrete rejoin shape (`[ld …; mv x_n, x_k, 0]`) this
reduces `lookupG n (runGM body L lds)` to `some (srcVal k (runGM body L lds) + sext 0)`
which `srcVal_runGM_ne` then collapses to `some (srcVal k L)` = the pre-load source. -/
theorem lookupG_runGM_snoc (pre : List MInstr) (a : MInstr) (L : GRegs)
    (lds : List (List (BitVec 8)))
    (hstore : a.kind ≠ .sw ∧ a.kind ≠ .sd ∧ a.kind ≠ .sb ∧ a.kind ≠ .sh) (n : Nat)
    (hrd : a.rd = n) :
    lookupG n (runGM (pre ++ [a]) L lds)
      = some (wvalM a (runGM pre L lds) ((ldsRunM pre lds).headD [])) := by
  induction pre generalizing L lds with
  | nil =>
    simp only [List.nil_append, runGM, ldsRunM]
    exact lookupG_stepGM_writer a L (lds.headD []) hstore n hrd
  | cons b rest ih =>
    simp only [List.cons_append, runGM, ldsRunM]
    exact ih (stepGM b L (lds.headD [])) (stepLdsM b.kind lds)

#print axioms lookupG_runGM_snoc

/-- **`gholds_lookup_ld`** — the load-bearing companion of `gholds_lookup`.  From
`GHolds σ (evalBlocks bs (SegEvalState.init L lds)).regs` and a proof that the seg's
register readback of `n` equals `some v` (supplied by `lookupG_runGM_snoc` +
`srcVal_runGM_ne` peeling, NOT by `rfl`), conclude `gprGet σ n = some v`.  This is
`gholds_lookup` with the `(by rfl)` replaced by the peel proof, so a load-bearing seg
(any rejoin/spill-reload) reads back in one application instead of the 10-line hand
`simp only [runGM,stepGM,wvalM,srcVal,…]`. -/
theorem gholds_lookup_ld {σ : MState} {n : Nat} {v : BitVec 64}
    (L : GRegs) (bs : List BBlock) (lds : List (List (BitVec 8)))
    (hregs : GHolds σ (evalBlocks bs (SegEvalState.init L lds)).regs)
    (hread : lookupG n (evalBlocks bs (SegEvalState.init L lds)).regs = some v) :
    gprGet σ n = some v :=
  gholds_lookup _ hregs hread

/-! ### Regression demo (readback) — `strRejoin_x11`'s shape

`rbDemo` is the EXACT `strRejoin` block: `ld x12,0(x2)` then `mv x11,x10`
(`addi x11,x10,0`).  Reading `x11` back off `evalBlocks rbDemo …` is where the hand
`simp only [runGM,stepGM,wvalM,srcVal,…]` + `BitVec.add_zero` (10 lines, 6 field pins)
lived.  Here it collapses to `lookupG_runGM_snoc` (splits the body as `pre ++ [mv]`,
reads the writer's `wvalM`) + `srcVal_runGM_ne` (peels the leading `ld` off the `mv`'s
source read) + the `+ sext 0` cleanup.  NO deep `rfl`, `maxRecDepth` stays at 4000. -/
#derive_case rbDemo chain
  [(0x80003b1c#64, 0x00013603#32),                -- ld   x12,0(x2)
   (0x80003b20#64, 0x00050593#32)]                -- mv   x11,x10  (addi x11,x10,0)

/-- The readback of `x11` off the load-bearing `rbDemo` seg, via the peel bricks —
the mechanized replacement for `strRejoin_x11`'s hand `simp only [runGM,…]`. -/
theorem rbDemo_x11 (sp x : BitVec 64) (lds : List (List (BitVec 8))) :
    lookupG 11 (evalBlocks rbDemo (SegEvalState.init [(2, sp), (10, x)] lds)).regs
      = some x := by
  rw [evalBlocks_regs]
  -- single-block seg: `runChain rbDemo L lds` reduces to `runGM body L lds`, and
  -- `body = [ld x12,0(x2); mv x11,x10]`; last writer of x11 is the `mv`.
  show lookupG 11 (runGM
      ([mkLine 0x80003b1c#64 0x00013603#32] ++ [mkLine 0x80003b20#64 0x00050593#32])
      [(2, sp), (10, x)] lds) = some x
  rw [lookupG_runGM_snoc [mkLine 0x80003b1c#64 0x00013603#32]
      (mkLine 0x80003b20#64 0x00050593#32) [(2, sp), (10, x)] lds
      (by decide) 11 (by decide)]
  -- writer is `addi x11,x10,0`: value = srcVal 10 (runGM [ld …] L lds) + sext 0
  show some (srcVal 10 (runGM [mkLine 0x80003b1c#64 0x00013603#32] [(2, sp), (10, x)] lds)
      + Functions.sign_extend 0#12) = some x
  rw [srcVal_runGM_ne 10 [mkLine 0x80003b1c#64 0x00013603#32] (by decide) [(2, sp), (10, x)] lds]
  show some (srcVal 10 [(2, sp), (10, x)] + Functions.sign_extend 0#12) = some x
  rw [show (Functions.sign_extend 0#12 : BitVec 64) = 0#64 from by decide, BitVec.add_zero]
  rfl

#print axioms rbDemo_x11

/-- **Second readback demo — the full `gholds_lookup_ld` row interface.**  This is the
shape a `segToTriple` `hpost` marshalling actually calls: from `GHolds σ (evalBlocks …).regs`
(the row's `hregs`) and the peel-derived readback (`rbDemo_x11`), land `gprGet σ 11 = some x`
in ONE application — the mechanized `exact gholds_lookup (v := x) _ hregs (strRejoin_x11 …)`
line of `strRejoinRow`, with the `(by rfl)`/hand-`simp` readback replaced by the peel. -/
theorem rbDemo_gprGet {σ : Vsa.Machine.MState} (sp x : BitVec 64) (lds : List (List (BitVec 8)))
    (hregs : GHolds σ (evalBlocks rbDemo (SegEvalState.init [(2, sp), (10, x)] lds)).regs) :
    gprGet σ 11 = some x :=
  gholds_lookup_ld _ rbDemo lds hregs (rbDemo_x11 sp x lds)

#print axioms rbDemo_gprGet

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
#derive_case gcDemo chain
  [(0x80003628#64, 0xffd50793#32)]                -- addi x15,x10,-3
    terminator ⟨0x8000362c#64, 0x00079663#32, 0x63#8, 0x96#8, 0x07#8, 0x00#8,
      .br bop.BNE false, 15, 0, 0x000c#13, 0#21, 0#12⟩ ;;   -- NOT taken (x15=0) → 0x3630
  [(0x80003630#64, 0xffd80793#32)]                -- addi x15,x16,-3
    terminator ⟨0x80003634#64, 0x4c078c63#32, 0x63#8, 0x8c#8, 0x07#8, 0x4c#8,
      .br bop.BEQ true, 15, 0, 0x04d8#13, 0#21, 0#12⟩     -- TAKEN (x15=0) → 0x3b0c

/-- The kind-check pin list: both operand kind tags are 3 (`str`). -/
def gcDemoL : GRegs := [(10, 3#64), (16, 3#64)]

/-- The `ChainFacts` leg for `gcDemo` via `chain_facts` (mechanical leaves) +
`seg_guard_close` (the two arith guards).  This is the mechanized `strKindCheck_facts`:
the `all_goals rfl` that overflowed is now the additive `seg_guard_close` fallback. -/
theorem gcDemo_facts (σ : Vsa.Machine.MState) (lds : List (List (BitVec 8)))
    (h : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    ChainFacts σ.mem σ.mem gcDemoL lds gcDemo := by
  chain_facts h with "Vsa.Sim.Code.eval_expr_at_"
  all_goals
    seg_guard_close [gcDemoL,
      show (mkLine 0x80003628#64 0xffd50793#32).kind = MKind.addi from rfl,
      show (mkLine 0x80003628#64 0xffd50793#32).rd = 15 from rfl,
      show (mkLine 0x80003628#64 0xffd50793#32).rs1 = 10 from rfl,
      show (mkLine 0x80003628#64 0xffd50793#32).imm = 0xffd#12 from rfl,
      show (mkLine 0x80003630#64 0xffd80793#32).kind = MKind.addi from rfl,
      show (mkLine 0x80003630#64 0xffd80793#32).rd = 15 from rfl,
      show (mkLine 0x80003630#64 0xffd80793#32).rs1 = 16 from rfl,
      show (mkLine 0x80003630#64 0xffd80793#32).imm = 0xffd#12 from rfl]

#print axioms gcDemo_facts

end Vsa.Sim
