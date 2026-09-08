import Vsa.Sim.rows.StrCmpBlockC
import Vsa.Sim.BridgeSeg
import Vsa.Sim.BoxSuffixSeams
import Vsa.Sim.StrcmpSpecW4

/-!
# `StrArmChain` — the two landed segs of the string-comparison arm

The string-comparison arm (both operands of kind `3`) runs

```
80003628  addi a5,a0,-3 ; bnez a5 → 80003638   (kind check: right kind = 3, NOT taken)
80003630  addi a5,a6,-3 ; beqz a5 → 80003b0c   (left kind = 3, TAKEN → the seam)
80003b0c  mv a1,a7 ; mv a0,s3 ; sd a2,0(sp) ; jal strcmp   (`StrCmpSeam.strSeamSeg`)
80003b1c  ld a2,0(sp) ; mv a1,a0 ; j 800036a4   (rejoin — a1 := the strcmp sign)
800036a4  <op sign-test tail> ; jal value_bool  (`StrCmpSignTail`, `CmpArmSeg`)
```

This file lands the kind-check seg `strKindCheck` (branch-terminated, `segToTriple`)
and the rejoin seg `strRejoin` (`j`-terminated) with their register readbacks.
`Vsa/Sim/StrCmpSeam.lean` composes them with the seam and `strcmp_full_spec`;
`Vsa/Sim/StrCmpCell.lean` composes the dispatch, the sign tails, and the box.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While
open Vsa.Sim.Code

namespace Vsa.Sim

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-! ## SPAN 1 — the kind-check branch span as a `#derive_case` seg

Both operands are strings (kind tag 3): `x10 = 3` (right kind), `x16 = 3` (left kind).
* `0x80003628 addi x15,x10,-3` ⇒ `x15 = 0`; `bnez x15` @0x8000362c NOT taken (0),
  falls through to `0x80003630`;
* `0x80003630 addi x15,x16,-3` ⇒ `x15 = 0`; `beqz x15` @0x80003634 TAKEN (0) →
  `0x80003b0c` (the strcmp seam entry, the seg's computed end PC).

Branch-terminated (no jal, no store) → plain `segToTriple`, per the CLAUDE.md table. -/
#derive_case strKindCheck chain
  [(0x80003628#64, 0xffd50793#32)]                -- addi x15,x10,-3
    terminator ⟨0x8000362c#64, 0x00079663#32, 0x63#8, 0x96#8, 0x07#8, 0x00#8,
      .br bop.BNE false, 15, 0, 0x000c#13, 0#21, 0#12⟩ ;;   -- NOT taken (x15=0) → 0x3630
  [(0x80003630#64, 0xffd80793#32)]                -- addi x15,x16,-3
    terminator ⟨0x80003634#64, 0x4c078c63#32, 0x63#8, 0x8c#8, 0x07#8, 0x4c#8,
      .br bop.BEQ true, 15, 0, 0x04d8#13, 0#21, 0#12⟩     -- TAKEN (x15=0) → 0x3b0c

/-- The kind-check pin list: both operand kind tags are 3 (`str`). -/
def strKindL : GRegs := [(10, 3#64), (16, 3#64)]

/-- The `ChainFacts` leg (mechanical).  The two branch guards (`x15 = x10-3 = 0` for the
BNE, `x15 = x16-3 = 0` for the BEQ) do NOT close by `all_goals rfl`: `rfl` chases the
`addi`'s `sign_extend (-3)` + subtraction through the reflected `runGM` with symbolic
`lds` to unbounded depth (native stack overflow at high `maxRecDepth`).  Instead reduce the
guard symbolically — `simp only [runGM, stepGM, wvalM, srcVal, guardB, <per-word `mkLine`
field pins>]` collapses each guard to a concrete `BitVec` comparison, closed by `decide`.
This is the same load-free-but-arith-heavy readback pattern as span 3's `strRejoin_x11`. -/
theorem strKindCheck_facts (σ : MState) (lds : List (List (BitVec 8)))
    (h : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    ChainFacts σ.mem σ.mem strKindL lds strKindCheck := by
  chain_facts h with "Vsa.Sim.Code.eval_expr_at_"
  all_goals (
    simp only [strKindL, runGM, stepGM, wvalM, srcVal, lookupG, eraseG, guardB,
      show (mkLine 0x80003628#64 0xffd50793#32).kind = MKind.addi from rfl,
      show (mkLine 0x80003628#64 0xffd50793#32).rd = 15 from rfl,
      show (mkLine 0x80003628#64 0xffd50793#32).rs1 = 10 from rfl,
      show (mkLine 0x80003628#64 0xffd50793#32).imm = 0xffd#12 from rfl,
      show (mkLine 0x80003630#64 0xffd80793#32).kind = MKind.addi from rfl,
      show (mkLine 0x80003630#64 0xffd80793#32).rd = 15 from rfl,
      show (mkLine 0x80003630#64 0xffd80793#32).rs1 = 16 from rfl,
      show (mkLine 0x80003630#64 0xffd80793#32).imm = 0xffd#12 from rfl,
      Nat.reduceEqDiff, if_true, if_false, Option.getD_some]
    <;> decide)

/-- Post of the kind-check span: parked at `0x80003b0c` (the strcmp seam entry),
memory unchanged (no stores). -/
def StrKindCheckPost (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x80003b0c#64

/-- **SPAN 1 payoff.**  The whole kind-check branch span as a `Triple`, via
`segToTriple`: `hwf` is the row's one kernel `decide` (`ChainOK`), `hpost` projects
the computed end PC / unchanged memory off the `#derive_case` outcome. -/
theorem strKindCheckRow (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre strKindCheck strKindL [] 0x80003628#64 m0) (StrKindCheckPost m0) := by
  apply segToTriple strKindCheck strKindL [] 0x80003628#64 m0 (StrKindCheckPost m0)
    (by show ChainOK 0x80003628#64 [10, 16] strKindCheck; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' _hregs
  refine ⟨hG', ?_, ?_⟩
  · rw [hmem']; rfl
  · rw [hpc']
    show some (chainEndPC 0x80003628#64 strKindL [] strKindCheck) = some 0x80003b0c#64
    rw [chainEndPC_eq_bt strKindCheck 0x80003628#64 strKindL [] (by decide)]
    rfl

#print axioms strKindCheck_facts
#print axioms strKindCheckRow

/-! ## SPAN 3 — the rejoin seg `0x80003b1c ld;mv; j 0x800036a4`

After the `strcmp` call returns (`x10 = strcmp sign`, `x1 = link`, `x2 = sp`, `x9 = sret`),
the rejoin block reloads the spilled `a2` and moves the strcmp sign into `a1`, then jumps
into the SHARED operator sign-test tail at `0x800036a4`:

* `0x80003b1c ld x12,0(x2)`   — reload the spilled `a2` (dead for the sign tail);
* `0x80003b20 mv x11,x10`     — `x11 := x10` (the strcmp sign scalar `x`);
* `0x80003b24 j 0x800036a4`   — jump to the sign-test tail entry (`jal x0`, imm21 = -0x480).

The `mv x11,x10` sets the spaceship scalar the sign tail reads.  Both `x9 = sret` and the
sign `x = x10` are carried symbolically; `x12` is overwritten by the `ld` (its value is the
positional load, irrelevant downstream).  `j`-terminated → plain `segToTriple`. -/
#derive_case strRejoin chain
  [(0x80003b1c#64, 0x00013603#32),                -- ld   x12,0(x2)
   (0x80003b20#64, 0x00050593#32)]                -- mv   x11,x10  (addi x11,x10,0)
    terminator ⟨0x80003b24#64, 0xb81ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0xb8#8,
      .j, 0, 0, 0#13, 0x1ffb80#21, 0#12⟩           -- j 0x800036a4  (jal x0, -0x480)

/-- The rejoin pin list: `x2 = sp` (the `ld` base), the strcmp sign scalar in `x10`, and
the sret buffer in `x9`.  `x2` must be pinned so the `ld x12,0(x2)` block's `ChainOK`
decode resolves. -/
def strRejoinL (sp x sret : BitVec 64) : GRegs := [(2, sp), (10, x), (9, sret)]

/-! ### Load-bearing register readback (see `experiments/observations.md`
`loadbearing-seg-register-readback`)

`gholds_lookup … (by rfl)` closes register projections for LOAD-FREE segs (the
sign-tail / cmpFixup rows), but the `ld x12,0(x2)` here makes `rfl` on
`lookupG 11 (runGM …)` stall on the symbolic-`lds` load cell (`bytesVal .ld
(lds.headD [])` in the dead `x12` slot).  `x9 = sret` is unwritten by the body →
peeled by `srcVal_runGM_ne`.  `x11 = x` (the `mv x11,x10`) is read via the hand
`runGM`/`stepGM` unfold with the six per-word `mkLine` field pins + `Nat`
simprocs, finishing the `+ sext 0#12` by `BitVec.add_zero`. -/
theorem strRejoin_x11 (sp x sret : BitVec 64) (lds : List (List (BitVec 8))) :
    lookupG 11 (evalBlocks strRejoin (SegEvalState.init (strRejoinL sp x sret) lds)).regs
      = some x := by
  rw [evalBlocks_regs]
  show lookupG 11 (runChain strRejoin (strRejoinL sp x sret) lds) = some x
  simp only [strRejoin, runChain, runGM, stepGM, wvalM, srcVal, lookupG, eraseG,
    strRejoinL,
    show (mkLine 0x80003b1c#64 0x00013603#32).kind = MKind.ld from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).kind = MKind.addi from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).rd = 11 from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).rs1 = 10 from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).imm = 0#12 from rfl,
    show (mkLine 0x80003b1c#64 0x00013603#32).rd = 12 from rfl,
    Nat.reduceEqDiff, if_true, if_false, Option.getD_some]
  show some (x + Functions.sign_extend 0#12) = some x
  rw [show (Functions.sign_extend 0#12 : BitVec 64) = 0#64 from by decide, BitVec.add_zero]

theorem strRejoin_x9 (sp x sret : BitVec 64) (lds : List (List (BitVec 8))) :
    lookupG 9 (evalBlocks strRejoin (SegEvalState.init (strRejoinL sp x sret) lds)).regs
      = some sret := by
  rw [evalBlocks_regs]
  show lookupG 9 (runChain strRejoin (strRejoinL sp x sret) lds) = some sret
  simp only [strRejoin, runChain, runGM, stepGM, wvalM, srcVal, lookupG, eraseG,
    strRejoinL,
    show (mkLine 0x80003b1c#64 0x00013603#32).kind = MKind.ld from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).kind = MKind.addi from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).rd = 11 from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).rs1 = 10 from rfl,
    show (mkLine 0x80003b1c#64 0x00013603#32).rd = 12 from rfl,
    Nat.reduceEqDiff, if_true, if_false, Option.getD_some]

/-- Post of the rejoin span: parked at `0x800036a4` (the sign-test tail entry), memory
unchanged (the `ld` reads, no stores), with the spaceship scalar `x` in `x11` (the `mv`)
and `x9 = sret` surviving.  This is EXACTLY the `SegPre`/pin shape `sTail{Lt,Gt,Le}Row` /
`cmpFixupTail` consume at `0x800036a4` (`x11 = cmpV`, `x9 = sret`; the op token `x12` is
staged by the arm prologue, not here). -/
def StrRejoinPost (x sret : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x800036a4#64 ∧
  gprGet c.σ 11 = some x ∧
  gprGet c.σ 9 = some sret

/-- **SPAN 3 payoff.**  The rejoin span as a `Triple`, via `segToTriple`: `hwf` is the
row's one kernel `decide` (`ChainOK`), `hpost` projects the `j`-target end PC (`0x800036a4`),
the moved sign scalar `x11 = x` (`strRejoin_x11`), and the surviving `x9 = sret`
(`strRejoin_x9`) off the outcome.  The rejoin `SegPre` carries the load's `ChainFacts`
(the caller — `strArmFront` — supplies it from the post-`strcmp` reload pin). -/
theorem strRejoinRow (sp x sret : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre strRejoin (strRejoinL sp x sret) lds 0x80003b1c#64 m0)
      (StrRejoinPost x sret m0) := by
  apply segToTriple strRejoin (strRejoinL sp x sret) lds 0x80003b1c#64 m0 (StrRejoinPost x sret m0)
    (by show ChainOK 0x80003b1c#64 [2, 10, 9] strRejoin; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', ?_, ?_, ?_, ?_⟩
  · rw [hmem']; rfl
  · rw [hpc']
    show some (chainEndPC 0x80003b1c#64 (strRejoinL sp x sret) lds strRejoin) = some 0x800036a4#64
    rw [chainEndPC_eq_bt strRejoin 0x80003b1c#64 (strRejoinL sp x sret) lds (by decide)]
    rfl
  · exact gholds_lookup (v := x) _ hregs (strRejoin_x11 sp x sret lds)
  · exact gholds_lookup (v := sret) _ hregs (strRejoin_x9 sp x sret lds)

#print axioms strRejoin_x11
#print axioms strRejoin_x9
#print axioms strRejoinRow

/-! ## The seam, the `strcmp` call, and the sign tails

The seam `0x80003b0c → jal strcmp`, the `strcmp` call, and the rejoin are composed
ONCE in `Vsa/Sim/StrCmpSeam.lean` (`strCmpTailReady_of_kindEntry`) over the two segs
above; the four sign tails and the `value_bool` box are composed by
`Vsa/Sim/StrCmpCell.lean` (`blockC_strcmp`).  The four cells are
`rows/StrCmpCellInstances.lean`. -/

end Vsa.Sim
