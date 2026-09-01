import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg

/-!
# `callClosureRetClass` — the `.ret v` status-classification span (wave 40)

Wave-40 residual span: the `0x8000337c..0x80003398` classification after the
body loop's `beqz a0 @0x80003378` FALLS THROUGH (`a0 ≠ 0`, an abrupt status).
Under the recursor premise's `a_6` (`status = .normal ∧ v = .null ∨
status = .ret v`) the abrupt status is `.ret v` — machine encoding `a0 = 3` —
so BOTH guards resolve ONE way and this is a SINGLE seg (not a polarity
family):

```
8000337c  lw a4,8(s2)       0x00892703   -- call_depth
80003380  addiw a5,a0,-1    0xfff5079b   -- a5 := status - 1
80003384  li a3,1           0x00100693
80003388  addiw a4,a4,-1    0xfff7071b   -- --call_depth
8000338c  sw a4,8(s2)       0x00e92423   -- (the ONLY store: 4 bytes at 8(s2))
80003390  ▷ bgeu a3,a5 → 0x80003cc8     NOT taken (a0=3 ⇒ a5=2 > 1):
                                          the brk/cont ERROR route, OFF a_6
80003394  li a5,3           0x00300793
80003398  ▷ bne a0,a5 → 0x80003960      NOT taken (a0=3):
                                          the dead defensive route (a0 > 3
                                          is unreachable under a_6 + beqz)
-- fall-through → 0x8000339c = the GEN retCopy row entry
--                (callClosureRetCopyRow, `rows/CallClosureRetCopyGen.lean`)
```

Both guard obligations sit in `ChainFacts`, dischargeable from `a0 = 3` — the
status→a0 ABI fact (`BodyStatusABI`, the `SeqForRows`-class named residual in
`rows/CallClosureSplice.lean`).  The span's one store (the `--call_depth`
word at `8(s2)`) is in the write-log; the interp pointer `s2` is the arm
ghost's `x18` (`BodyGhostTie.interp`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

/- The single route: `bgeu` NOT taken (not brk/cont) ;; `bne` NOT taken
(status = ret), landing at the retCopy entry `0x8000339c`. -/
#derive_case callClosureRetClassSeg chain
  [(0x8000337c#64, 0x00892703#32),  -- lw a4,8(s2)
   (0x80003380#64, 0xfff5079b#32),  -- addiw a5,a0,-1
   (0x80003384#64, 0x00100693#32),  -- li a3,1
   (0x80003388#64, 0xfff7071b#32),  -- addiw a4,a4,-1
   (0x8000338c#64, 0x00e92423#32)]  -- sw a4,8(s2)
    terminator ⟨0x80003390#64, 0x12f6fce3#32, 0xe3#8, 0xfc#8, 0xf6#8, 0x12#8,
      .br bop.BGEU false, 13, 15, 0x0938#13, 0#21, 0#12⟩ ;;
  [(0x80003394#64, 0x00300793#32)]  -- li a5,3
    terminator ⟨0x80003398#64, 0x5cf51463#32, 0x63#8, 0x14#8, 0xf5#8, 0x5c#8,
      .br bop.BNE false, 10, 15, 0x05C8#13, 0#21, 0#12⟩

#print axioms callClosureRetClassSeg_seg

/-- The entry pin list: `x18` (s2, the interp pointer — `call_depth` at
`8(s2)`) and `x10` (a0, the body's status word — `= 3` on this route). -/
def callClosureRetClassL (s2v a0v : BitVec 64) : GRegs := [(18, s2v), (10, a0v)]

/-- The post: parked at the retCopy entry `0x8000339c`
(`callClosureRetCopyRow`'s `SegPre` PC), memory = entry + the `--call_depth`
word at `8(s2)`, the computed pins exposed. -/
def CallClosureRetClassPost (s2v a0v : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks callClosureRetClassSeg
    (SegEvalState.init (callClosureRetClassL s2v a0v) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x8000339c#64 ∧
  GHolds c.σ (evalBlocks callClosureRetClassSeg
    (SegEvalState.init (callClosureRetClassL s2v a0v) lds)).regs

/-- **`callClosureRetClassRow`** — the `.ret v` classification span as a
`Triple` (`segToTriple`), landing at the GEN retCopy row's entry. -/
theorem callClosureRetClassRow (s2v a0v : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre callClosureRetClassSeg (callClosureRetClassL s2v a0v)
        lds 0x8000337c#64 m0)
      (CallClosureRetClassPost s2v a0v lds m0) := by
  apply segToTriple callClosureRetClassSeg (callClosureRetClassL s2v a0v)
    lds 0x8000337c#64 m0 (CallClosureRetClassPost s2v a0v lds m0)
    (by have h : keysG (callClosureRetClassL s2v a0v) = [18, 10] := rfl
        rw [h]
        show ChainOK 0x8000337c#64 [18, 10] callClosureRetClassSeg
        decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, hregs⟩
  rw [hpc']
  show some (evalBlocksPC 0x8000337c#64
      (SegEvalState.init (callClosureRetClassL s2v a0v) lds)
      callClosureRetClassSeg)
    = some 0x8000339c#64
  rfl

#print axioms callClosureRetClassRow

end Vsa.Sim
