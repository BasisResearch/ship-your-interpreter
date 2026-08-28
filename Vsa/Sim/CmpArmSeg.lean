import Vsa.Sim.EvalGeChain
import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac

/-!
# `CmpArmSeg` — exponentiation proof-of-method: the comparison operator-fixup
tail auto-threaded via `#derive_case` + `segToTriple`

This file demonstrates, on a REAL fragment of `eval_expr`, that the binary-op
comparison arm's operator-fixup tail (`0x800036a4 → 0x800036c8`: the three
operator `beq`s + `not`/`srli`/`mv`) collapses from hand-threaded
`bblock_sound_bt` composition (the `geLadB7`/`geLadNot`/`ltLadG` blocks + the
`evalGeLadderEF`/`evalLtLadderG` theorems, ~120 lines of step-count/frame
plumbing) to a `(pc, word)` block table + ONE `chain_facts` + ONE `ChainOK`
`decide`.

The measured point (see `#print` at the bottom): `cmpFixupTail_seg` is emitted
by `#derive_case` with the whole Steps chain / computed end PC / computed
registers / write log auto-threaded, and `cmpFixupTailRow` marshals it into a
`Triple` via `segToTriple` in a handful of lines. This is the template the
remaining binary-op rows (div/mod/eq/ne) fan out from: paste the block table,
one command, one `decide`, project the outcome.

The resolved path is `ge` (token 23): all three operator `beq`s fall through
(23 ≠ 21, 22, 20), so `not x11,x11` executes then the shared `srli x11,x11,0x3f`
sign-bit; `x11` ends as the complemented spaceship top bit.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

/- The comparison operator-fixup tail `0x800036a4 → 0x800036c8`, resolved for
the `ge`/fall-through path (token ≠ 21, 22, 20).  Four blocks:
  `li x15,21` ▷ `beq x12,x15` NOT taken (→ 0x36ac);
  `li x15,22` ▷ `beq x12,x15` NOT taken (→ 0x36b4);
  `li x15,20` ▷ `beq x12,x15` NOT taken (→ 0x36bc);
  `not x11,x11 ; srli x11,x11,0x3f ; mv x10,x9` — straight-line to 0x36c8. -/
#derive_case cmpFixupTail chain
  [(0x800036a4#64, 0x01500793#32)]                -- li x15,21
    terminator ⟨0x800036a8#64, 0x44f60863#32, 0x63#8, 0x08#8, 0xf6#8, 0x44#8,
      .br bop.BEQ false, 12, 15, 0x0450#13, 0#21, 0#12⟩ ;;
  [(0x800036ac#64, 0x01600793#32)]                -- li x15,22
    terminator ⟨0x800036b0#64, 0x42f60a63#32, 0x63#8, 0x0a#8, 0xf6#8, 0x42#8,
      .br bop.BEQ false, 12, 15, 0x0434#13, 0#21, 0#12⟩ ;;
  [(0x800036b4#64, 0x01400793#32)]                -- li x15,20
    terminator ⟨0x800036b8#64, 0x00f60463#32, 0x63#8, 0x04#8, 0xf6#8, 0x00#8,
      .br bop.BEQ false, 12, 15, 0x0008#13, 0#21, 0#12⟩ ;;
  [(0x800036bc#64, 0xfff5c593#32),                -- not  x11,x11  (xori x11,x11,-1)
   (0x800036c0#64, 0x03f5d593#32),                -- srli x11,x11,0x3f
   (0x800036c4#64, 0x00048513#32)]                -- mv   x10,x9

/-- The mechanical `ChainFacts` bundle for the fixup tail, discharged in one
`chain_facts` call from a single loaded-image hypothesis.  The three branch
guards (`x12 ≠ 21/22/20`) are the only data-dependent leftovers; for the `ge`
token `x12 = 23` they close by `decide`, given the pin. -/
theorem cmpFixupTail_facts (σ : MState)
    (cmpV sret : BitVec 64) (lds : List (List (BitVec 8)))
    (h : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    ChainFacts σ.mem σ.mem [(11, cmpV), (12, 23#64), (9, sret)] lds cmpFixupTail := by
  chain_facts h with "Vsa.Sim.Code.eval_expr_at_"
  all_goals rfl

/-- A concrete row post read off the fixup-tail outcome: parked at the computed
end PC `0x800036c8` (fall-through past `mv`, no terminator), memory unchanged
(the fixup tail has no stores, so `out.log = []`). -/
def CmpFixupPost (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x800036c8#64

/-- **The payoff.**  The whole operator-fixup tail as a `Triple`, built by
`segToTriple` in a handful of lines: `hwf` is the row's one kernel `decide`
(`ChainOK`), and `hpost` projects the computed end PC / unchanged memory off the
`#derive_case`-emitted outcome.  This replaces the hand-threaded
`evalGeLadderEF`/`evalLtLadderG` composition (step-count bookkeeping, per-block
`obs_*_other` frame walking) with one application. -/
theorem cmpFixupTailRow (cmpV sret : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre cmpFixupTail [(11, cmpV), (12, 23#64), (9, sret)] []
      0x800036a4#64 m0) (CmpFixupPost m0) := by
  apply segToTriple cmpFixupTail [(11, cmpV), (12, 23#64), (9, sret)] []
    0x800036a4#64 m0 (CmpFixupPost m0)
    (by show ChainOK 0x800036a4#64 [11, 12, 9] cmpFixupTail; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' _hregs
  refine ⟨hG', ?_, ?_⟩
  · rw [hmem']; rfl
  · rw [hpc']; rfl

#print axioms cmpFixupTail_facts
#print axioms cmpFixupTailRow

end Vsa.Sim
