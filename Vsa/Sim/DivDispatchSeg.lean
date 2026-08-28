import Vsa.Sim.EvalGeChain
import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.DeriveCallSeg
import Vsa.Sim.DivSpec3

/-!
# `DivDispatchSeg` — the `div` arm dispatch ladder as a NEW `#derive_case` leaf

The first genuinely NEW binary-op arm assembled on the `#derive_case`/`segToTriple`
combinator (validated in `Vsa/Sim/CmpDispatchSeg.lean` on the `ge` comparison arm)
— NOT a hand-cloned row.  `div` (token 14) reaches its own arithmetic arm
`0x800037dc → 0x8000381c` (ending just before `jal __divdi3`):

  D1 `ld a4,0x78 ; ld a5,0x88 ; li a3,2 ; sd a4,0xf0 ; sd a5,0x100` ▷
     `bne a6,a3` NOT (right kind `int`, a6=2=a3) → 0x37f4;
  D2 `ld a4,0x90 ; ld a3,0x98 ; ld a5,0xa0 ; sd a4,0xf0 ; sd a3,0xf8 ; sd a5,0x100` ▷
     `bne a0,a6` NOT (left kind `int`, a0=2=a6) → 0x380c;
  D3 (empty body) ▷ `beqz a7` NOT taken → 0x3814 — **the divisor-nonzero guard**:
     `a7 = Wr` (the divisor `b`), so this `beq a7,x0 = false` is exactly div's
     `b ≠ 0` value-path condition.  It is DATA-DEPENDENT (unlike the two kind
     `bne`s, which pin concretely), so `chain_facts` leaves it as a leftover — the
     caller supplies `Wr ≠ 0`, mirroring `binOpSem .div = if b == 0 then none …`;
  D4 `mv a1,a7 ; mv a0,s3` — straight-line to 0x381c: sets up the `__divdi3`
     arguments `a0 = s3 = Wl` (dividend `a`) and `a1 = a7 = Wr` (divisor `b`).

The row `divDispatchRow` parks at `0x8000381c` with `x10 = Wl`, `x11 = Wr` — the
libgcc `__divdi3(a, b)` call arguments — and the five stack stores in `out.log`.
On top of it, `jal __divdi3 @0x8000381c` is a Shape-D `callSeg` seam
(`divdi3_spec`, the `a0 = a.tdiv b` callee contract, mirror of `muldi3_spec`) and
`jal value_int @0x80003828` boxes the result into `.int (wrap64 (a.tdiv b))` — the
same two-seam arithmetic shape as the landed `blockC_mul`, composed on this seg.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

set_option maxHeartbeats 4000000

/- The `div` arithmetic arm `0x800037dc → 0x8000381c`, four blocks (two int-kind
`bne`s NOT taken, the divisor-nonzero `beqz` NOT taken, then the `__divdi3`
argument `mv`s).  All terminators are `br` with fixed polarity. -/
#derive_case divDispatch chain
  [(0x800037dc#64, 0x07813703#32),                -- ld   x14,0x78(x2)
   (0x800037e0#64, 0x08813783#32),                -- ld   x15,0x88(x2)
   (0x800037e4#64, 0x00200693#32),                -- li   x13,2
   (0x800037e8#64, 0x0ee13823#32),                -- sd   x14,0xf0(x2)
   (0x800037ec#64, 0x10f13023#32)]                -- sd   x15,0x100(x2)
    terminator ⟨0x800037f0#64, 0x76d81663#32, 0x63#8, 0x16#8, 0xd8#8, 0x76#8,
      .br bop.BNE false, 16, 13, 0x076c#13, 0#21, 0#12⟩ ;;
  [(0x800037f4#64, 0x09013703#32),                -- ld   x14,0x90(x2)
   (0x800037f8#64, 0x09813683#32),                -- ld   x13,0x98(x2)
   (0x800037fc#64, 0x0a013783#32),                -- ld   x15,0xa0(x2)
   (0x80003800#64, 0x0ee13823#32),                -- sd   x14,0xf0(x2)
   (0x80003804#64, 0x0ed13c23#32),                -- sd   x13,0xf8(x2)
   (0x80003808#64, 0x10f13023#32)]                -- sd   x15,0x100(x2)
    terminator ⟨0x8000380c#64, 0x71051463#32, 0x63#8, 0x14#8, 0x05#8, 0x71#8,
      .br bop.BNE false, 10, 16, 0x0708#13, 0#21, 0#12⟩ ;;
  []                                              -- (empty body: the beqz block)
    terminator ⟨0x80003810#64, 0x4c088e63#32, 0x63#8, 0x8e#8, 0x08#8, 0x4c#8,
      .br bop.BEQ false, 17, 0, 0x04dc#13, 0#21, 0#12⟩ ;;
  [(0x80003814#64, 0x00088593#32),                -- mv   x11,x17  (a1 = a7 = divisor b)
   (0x80003818#64, 0x00098513#32)]                -- mv   x10,x19  (a0 = s3  = dividend a)

/-- The `div` arm pin list: `x16=2`/`x10=2` (right/left `int` kind tags driving
the two `bne`s), `x2=v2` (frame base of the loads/stores), `x9=sret` (the
`value_int` buffer), `x17=Wr` (divisor `b`, the `beqz` source and `mv a1`), and
`x19=Wl` (dividend `a`, the `mv a0` source).  The divisor-nonzero `beqz` guard
(`x17 = Wr ≠ 0`) is left to the caller by `chain_facts`. -/
def divDispL (v2 sret Wr Wl : BitVec 64) : GRegs :=
  [(16, 2#64), (10, 2#64), (2, v2), (9, sret), (17, Wr), (19, Wl)]

/-- The `div` dispatch outcome: parked at `0x8000381c` (ready for `jal __divdi3`),
memory updated by the five stack stores, and the `__divdi3` call arguments staged
— `x10 = Wl` (dividend `a`), `x11 = Wr` (divisor `b`) — with `x9=sret`/`x2=v2`
surviving for the `value_int` seam and frame. -/
def DivDispatchPost (v2 sret Wr Wl : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks divDispatch
    (SegEvalState.init (divDispL v2 sret Wr Wl) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x8000381c#64 ∧
  gprGet c.σ 10 = some Wl ∧
  gprGet c.σ 11 = some Wr ∧
  gprGet c.σ 9 = some sret ∧
  gprGet c.σ 2 = some v2

/-- **The new div leaf.**  The whole `div` arm dispatch `0x800037dc → 0x8000381c`
as a `Triple`, assembled by `#derive_case` + `segToTriple` — no hand cloning.
`hwf` is the one `ChainOK` `decide`; `hpost` projects the end PC / write-log
memory off the outcome.  The `__divdi3` (`callSeg` → `divdi3_spec`) and
`value_int` seams compose on top to conclude `.int (wrap64 (a.tdiv b))`. -/
theorem divDispatchRow (v2 sret Wr Wl : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre divDispatch (divDispL v2 sret Wr Wl) lds 0x800037dc#64 m0)
      (DivDispatchPost v2 sret Wr Wl lds m0) := by
  apply segToTriple divDispatch (divDispL v2 sret Wr Wl) lds 0x800037dc#64 m0
    (DivDispatchPost v2 sret Wr Wl lds m0)
    (by show ChainOK 0x800037dc#64 [16, 10, 2, 9, 17, 19] divDispatch; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpc']
    show some (chainEndPC 0x800037dc#64 (divDispL v2 sret Wr Wl) lds divDispatch)
      = some 0x8000381c#64
    rw [chainEndPC_eq_bt divDispatch 0x800037dc#64 (divDispL v2 sret Wr Wl) lds (by decide)]
    rfl
  -- the `__divdi3` call arguments, read off `GHolds σ' out.regs` (div's arm has no
  -- `slt`/`subw`, so the register fold reduces): `x10 = Wl` (dividend), `x11 = Wr`
  -- (`mv` = `addi rd,rs,0`, so the fold yields `_ + sign_extend 0#12`; bridge `+0`).
  · have e : (Wl + sign_extend (m := 64) (0#12) : BitVec 64) = Wl := by
      rw [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 from by decide, BitVec.add_zero]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · have e : (Wr + sign_extend (m := 64) (0#12) : BitVec 64) = Wr := by
      rw [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 from by decide, BitVec.add_zero]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · exact gholds_lookup (v := sret) _ hregs (by rfl)
  · exact gholds_lookup (v := v2) _ hregs (by rfl)

#print axioms divDispatchRow

/-! ## The `__divdi3` seam via `callSeg` — concluding the div value

The div arm's arithmetic tail is the Shape-D call splice
`dispatch ≫ jal __divdi3 ≫ value_int`.  The callee contract is the REAL
`divdi3_spec` (`Vsa/Sim/DivSpec3.lean`, `x10.toInt = n.toInt.tdiv d.toInt`);
`callSeg` threads it between the caller prefix (the `divDispatchRow` dispatch
above, then the `jal __divdi3` link landing at `divdi3_pre`'s entry `0x800046a4`
with `x10=a`, `x11=b`, `x1=return`) and the caller suffix (the `mv`s + `jal
value_int` boxing the quotient), exactly as the landed `blockC_mul` threads
`muldi3_spec`. -/

/-- The spec-side div bridge: for a nonzero divisor, `binOpSem .div` is the
wrapped truncating quotient — the value the `value_int` suffix must produce from
`divdi3_spec`'s `x10` (`res.toInt = a.tdiv b`, so `res = wrap64 (a.tdiv b)`). -/
theorem binOpSem_div_int (s : Vsa.While.Store) (a b : Int) (hb : b ≠ 0) :
    Vsa.While.binOpSem s .div (.int a) (.int b) = some (.int (Vsa.While.wrap64 (a.tdiv b))) := by
  simp only [Vsa.While.binOpSem]
  rw [if_neg (by simpa using hb)]

/-- **The `__divdi3` seam, realized via `callSeg` with the real `divdi3_spec`.**
Given the caller prefix landing the staged `divDispatchRow` args at the
`__divdi3` entry (`Triple P (divdi3_pre n d r m0)`) and the caller return suffix
boxing the quotient (`Triple (divdi3_post n d r m0) Q`), `callSeg` produces the
whole div call site `Triple P Q` — the exact Shape-D composition the goal asks
for, with `divdi3_spec` (not a hand re-derivation) as the threaded callee. -/
theorem divCallSeam {P Q : Config → Prop} (n d r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (pre : Triple P (divdi3_pre n d r m0))
    (suf : Triple (divdi3_post n d r m0) Q) :
    Triple P Q :=
  callSeg pre (divdi3_spec n d r m0) suf

#print axioms binOpSem_div_int
#print axioms divCallSeam

end Vsa.Sim
