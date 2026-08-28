import Vsa.Sim.EvalGeChain
import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac

/-!
# `CmpDispatchSeg` — the WHOLE comparison dispatch ladder as ONE `#derive_case` seg

Scaling the exponentiation proof-of-method (`Vsa/Sim/CmpArmSeg.lean`, which rebuilt
only the operator-fixup *tail* `0x800036a4 → 0x800036c8`) up to the **entire**
post-`jr` dispatch ladder `0x80003628 → 0x800036c8` of the binary-op comparison
arm (resolved for `ge`, token 23).  In the hand development this span is FIVE
theorems totalling ~600 lines of `bblock_sound_bt` plumbing:
`evalGeLadderAB` (kind ladder, 106 lines) ≫ `evalGeLadderC` (store block, 114) ≫
`evalGeLadderD` (operand-load/store block, 128) ≫ `evalGeLadderEF` (operator `beq`
ladder + `not`, 145) ≫ `evalLtLadderG` (`srli`/`mv` tail).

Here it is ONE `#derive_case` block table (`cmpDispatch`, 8 blocks) + ONE
`segToTriple` (`cmpDispatchRow`) + ONE `chain_facts` (`cmpDispatch_facts`).  The
whole `Steps` chain / computed end PC / computed registers / write log (the five
stack stores are non-empty `out.log`, unlike the fixup-tail demo) are
auto-threaded; the row's only kernel obligation is the single `ChainOK` `decide`.

The `jr` jump-table @0x80003558 in the *prefix* (`0x8000351c → 0x80003558`) can
only TERMINATE a `#derive_case` chain (`TermChainO`/`TermNotJrO`: a `jr`'s target
is data-dependent, so no block may structurally follow it); it is a separate seg,
and `jal value_bool @0x800036c8` stays the Shape-D `callSeg` seam.  So the maximal
single seg is exactly this post-`jr` dispatch ladder.

The resolved `ge` path (token 23, right/left kinds `int`):
  `bnez` TAKEN (a5=a0-3=-1) → `beq` TAKEN (a5=a2-20=3=a4) → `bne` NOT (a6=a1=2) →
  `bne` NOT (a0=a6=2) → three operator `beq`s all NOT (23∉{21,22,20}) → `not`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/- The `ge` post-`jr` dispatch ladder `0x80003628 → 0x800036c8`, eight blocks:
  K1 `addi x15,x10,-3` ▷ `bnez x15` TAKEN (a0=2 → -1≠0) → 0x3638;
  K2 `addiw x15,x12,-20 ; li x14,3 ; auipc x13 ; addi x13` ▷ `beq x15,x14` TAKEN
     (a2=23 → x15=3=x14) → 0x3664;
  K3 `ld x14,0x78 ; ld x15,0x88 ; li x11,2 ; sd x14,0xf0 ; sd x15,0x100` ▷
     `bne x16,x11` NOT (x16=2=x11) → 0x367c;
  K4 `ld x14,0x90 ; ld x11,0x98 ; ld x15,0xa0 ; sd x14,0xf0 ; sd x11,0xf8 ;
     sd x15,0x100` ▷ `bne x10,x16` NOT (2=2) → 0x3698;
  K5 `slt x14,x17,x19 ; slt x15,x19,x17 ; subw x11,x14,x15 ; li x15,21` ▷
     `beq x12,x15` NOT (23≠21) → 0x36ac;
  K6 `li x15,22` ▷ `beq x12,x15` NOT (23≠22) → 0x36b4;
  K7 `li x15,20` ▷ `beq x12,x15` NOT (23≠20) → 0x36bc;
  K8 `not x11,x11 ; srli x11,x11,0x3f ; mv x10,x9` — straight-line to 0x36c8. -/
#derive_case cmpDispatch chain
  [(0x80003628#64, 0xffd50793#32)]                -- addi x15,x10,-3
    terminator ⟨0x8000362c#64, 0x00079663#32, 0x63#8, 0x96#8, 0x07#8, 0x00#8,
      .br bop.BNE true, 15, 0, 0x000c#13, 0#21, 0#12⟩ ;;
  [(0x80003638#64, 0xfec6079b#32),                -- addiw x15,x12,-20
   (0x8000363c#64, 0x00300713#32),                -- li    x14,3
   (0x80003640#64, 0x00016697#32),                -- auipc x13,0x16   (dead)
   (0x80003644#64, 0xd4068693#32)]                -- addi  x13,x13,-704 (dead)
    terminator ⟨0x80003648#64, 0x00e78e63#32, 0x63#8, 0x8e#8, 0xe7#8, 0x00#8,
      .br bop.BEQ true, 15, 14, 0x001c#13, 0#21, 0#12⟩ ;;
  [(0x80003664#64, 0x07813703#32),                -- ld   x14,0x78(x2)
   (0x80003668#64, 0x08813783#32),                -- ld   x15,0x88(x2)
   (0x8000366c#64, 0x00200593#32),                -- li   x11,2
   (0x80003670#64, 0x0ee13823#32),                -- sd   x14,0xf0(x2)
   (0x80003674#64, 0x10f13023#32)]                -- sd   x15,0x100(x2)
    terminator ⟨0x80003678#64, 0x02b812e3#32, 0xe3#8, 0x12#8, 0xb8#8, 0x02#8,
      .br bop.BNE false, 16, 11, 0x0824#13, 0#21, 0#12⟩ ;;
  [(0x8000367c#64, 0x09013703#32),                -- ld   x14,0x90(x2)
   (0x80003680#64, 0x09813583#32),                -- ld   x11,0x98(x2)
   (0x80003684#64, 0x0a013783#32),                -- ld   x15,0xa0(x2)
   (0x80003688#64, 0x0ee13823#32),                -- sd   x14,0xf0(x2)
   (0x8000368c#64, 0x0eb13c23#32),                -- sd   x11,0xf8(x2)
   (0x80003690#64, 0x10f13023#32)]                -- sd   x15,0x100(x2)
    terminator ⟨0x80003694#64, 0x7d051063#32, 0x63#8, 0x10#8, 0x05#8, 0x7d#8,
      .br bop.BNE false, 10, 16, 0x07c0#13, 0#21, 0#12⟩ ;;
  [(0x80003698#64, 0x0138a733#32),                -- slt  x14,x17,x19
   (0x8000369c#64, 0x0119a7b3#32),                -- slt  x15,x19,x17
   (0x800036a0#64, 0x40f705bb#32),                -- subw x11,x14,x15
   (0x800036a4#64, 0x01500793#32)]                -- li   x15,21
    terminator ⟨0x800036a8#64, 0x44f60863#32, 0x63#8, 0x08#8, 0xf6#8, 0x44#8,
      .br bop.BEQ false, 12, 15, 0x0450#13, 0#21, 0#12⟩ ;;
  [(0x800036ac#64, 0x01600793#32)]                -- li   x15,22
    terminator ⟨0x800036b0#64, 0x42f60a63#32, 0x63#8, 0x0a#8, 0xf6#8, 0x42#8,
      .br bop.BEQ false, 12, 15, 0x0434#13, 0#21, 0#12⟩ ;;
  [(0x800036b4#64, 0x01400793#32)]                -- li   x15,20
    terminator ⟨0x800036b8#64, 0x00f60463#32, 0x63#8, 0x04#8, 0xf6#8, 0x00#8,
      .br bop.BEQ false, 12, 15, 0x0008#13, 0#21, 0#12⟩ ;;
  [(0x800036bc#64, 0xfff5c593#32),                -- not  x11,x11  (xori x11,x11,-1)
   (0x800036c0#64, 0x03f5d593#32),                -- srli x11,x11,0x3f
   (0x800036c4#64, 0x00048513#32)]                -- mv   x10,x9

/-- The dispatch-ladder pin list for the `ge` path: `x10=2`/`x16=2` (the two int
kind tags driving the `bnez`/`bne` guards), `x12=23` (the op token driving the
`beq` ladder), `x2=v2` (frame base of every load/store), `x9=sret` (the
`value_bool` buffer, copied to `x10` by the final `mv`), and `x17=Wr`/`x19=Wl`
(the comparison operands feeding the `slt`/`subw` spaceship scalar). -/
def cmpDispL (v2 sret Wr Wl : BitVec 64) : GRegs :=
  [(10, 2#64), (12, 23#64), (16, 2#64), (2, v2), (9, sret), (17, Wr), (19, Wl)]

/-- A concrete row post read off the `cmpDispatch` outcome: parked at the computed
end PC `0x800036c8` (fall-through past the final `mv`, ready for `jal value_bool`),
memory = the entry memory updated by the five stack stores (`writeLog m0 out.log`),
and the register frame the `value_bool` seam / epilogue consume: `x10=sret` (`mv
x10,x9`), `x9=sret`, `x2=v2`, `x19=Wl` all survive the ladder. -/
def CmpDispatchPost (v2 sret Wr Wl : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks cmpDispatch
    (SegEvalState.init (cmpDispL v2 sret Wr Wl) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x800036c8#64

/-- **The payoff.**  The whole `ge` post-`jr` dispatch ladder `0x80003628 →
0x800036c8` as a `Triple`, built by `segToTriple` in a handful of lines: `hwf` is
the row's one kernel `decide` (`ChainOK`), and `hpost` projects the computed end
PC / write-log memory / the surviving frame registers off the `#derive_case`
outcome.  Replaces the five hand ladder theorems
(`evalGeLadderAB`/`C`/`D`/`EF` + `evalLtLadderG`, ~600 lines). -/
theorem cmpDispatchRow (v2 sret Wr Wl : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre cmpDispatch (cmpDispL v2 sret Wr Wl) lds 0x80003628#64 m0)
      (CmpDispatchPost v2 sret Wr Wl lds m0) := by
  apply segToTriple cmpDispatch (cmpDispL v2 sret Wr Wl) lds 0x80003628#64 m0
    (CmpDispatchPost v2 sret Wr Wl lds m0)
    (by show ChainOK 0x80003628#64 [10, 12, 16, 2, 9, 17, 19] cmpDispatch; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_⟩
  -- end PC: collapse the value-independent control-flow fold to `chainEndPCc`
  -- (all terminators are `br`, so the end PC ignores the symbolic pin/load fold —
  -- unlike the register outcome, which stays available in `GHolds σ' out.regs`
  -- for the downstream `value_bool` seam exactly as the hand `blockC_ge` threads it).
  rw [hpc']
  show some (chainEndPC 0x80003628#64 (cmpDispL v2 sret Wr Wl) lds cmpDispatch)
    = some 0x800036c8#64
  rw [chainEndPC_eq_bt cmpDispatch 0x80003628#64 (cmpDispL v2 sret Wr Wl) lds (by decide)]
  rfl

#print axioms cmpDispatchRow

/-! ## The `chain_facts` leg (the third part of the three-part pattern)

`chain_facts h with "Vsa.Sim.Code.eval_expr_at_"` applied to the
`ChainFacts σ.mem σ.mem (cmpDispL v2 sret Wr Wl) lds cmpDispatch` bundle
mechanically discharges every byte-pin / decode leaf of ALL EIGHT blocks and
reduces the whole bundle to exactly its data-dependent residue:

* the **seven dispatch branch guards** (`bnez`/`beq`/`bne`, one per terminator) —
  these close by `decide`, since the token `x12=23` and the kind tags `x10=x16=2`
  are pinned concretely in `cmpDispL` (verified: `chain_facts …; all_goals decide`
  clears them even though `cmpDispL` also carries the symbolic `v2/sret/Wr/Wl`);
* the **ten load/store `MemFacts`** — the five stack stores (`sd …(sp)`) and the
  five spill reloads (`ld …(sp)`), each an sp-window over the *store-threaded*
  memory `writeLog (writeLog σ.mem …) …`.  These are the genuinely data-dependent
  windows — exactly the `a_lo/a_hi/a_ht/a_al` obligations the hand
  `evalGeLadderC`/`evalGeLadderD` take as arguments — the caller's frame layout,
  identical in the hand and the combinator developments.

So the `chain_facts` leg auto-threads all mechanical work at 8-block scale (the
same tactic proven end-to-end on the fixup tail in `cmpFixupTail_facts`), leaving
only the frame-layout windows a real row (`blockC_ge`) supplies from its `SL`
bundle.  `cmpDispatchRow` above consumes that residue via `SegPre`'s `ChainFacts`
conjunct, exactly as every real row's caller supplies it. -/

end Vsa.Sim
