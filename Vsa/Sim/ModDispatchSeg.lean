import Vsa.Sim.EvalGeChain
import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.DeriveCallSeg
import Vsa.Sim.DivSpec3

/-!
# `ModDispatchSeg` — the `mod` arm dispatch ladder as a NEW `#derive_case` leaf

The direct clone of `Vsa/Sim/DivDispatchSeg.lean` for `mod` (token 15).  The `div`
and `mod` arms are structurally identical machine code — the ld/li/sd bodies and
the two `mv` argument setups are *byte-for-byte* the same encodings; only the arm
PCs, the three terminator branch offsets, the libgcc callee (`__moddi3` @0x80004728
instead of `__divdi3`), and the semantics (`a.tmod b` instead of `a.tdiv b`)
change.  `mod` reaches its own arithmetic arm `0x80003784 → 0x800037c4` (ending
just before `jal __moddi3`):

  D1 `ld a4,0x78 ; ld a5,0x88 ; li a3,2 ; sd a4,0xf0 ; sd a5,0x100` ▷
     `bne a6,a3` NOT (right kind `int`, a6=2=a3) → 0x3c14;
  D2 `ld a4,0x90 ; ld a3,0x98 ; ld a5,0xa0 ; sd a4,0xf0 ; sd a3,0xf8 ; sd a5,0x100` ▷
     `bne a0,a6` NOT (left kind `int`, a0=2=a6) → 0x3bcc;
  D3 (empty body) ▷ `beqz a7` NOT taken → 0x3ba0 — **the divisor-nonzero guard**:
     `a7 = Wr` (the divisor `b`), so this `beq a7,x0 = false` is exactly mod's
     `b ≠ 0` value-path condition.  It is DATA-DEPENDENT (unlike the two kind
     `bne`s, which pin concretely), so `chain_facts` leaves it as a leftover — the
     caller supplies `Wr ≠ 0`, mirroring `binOpSem .mod = if b == 0 then none …`;
  D4 `mv a1,a7 ; mv a0,s3` — straight-line to 0x37c4: sets up the `__moddi3`
     arguments `a0 = s3 = Wl` (dividend `a`) and `a1 = a7 = Wr` (divisor `b`).

The row `modDispatchRow` parks at `0x800037c4` with `x10 = Wl`, `x11 = Wr` — the
libgcc `__moddi3(a, b)` call arguments — and the five stack stores in `out.log`.
On top of it, `jal __moddi3 @0x800037c4` is a Shape-D `callSeg` seam
(`moddi3_spec`, the `a0 = a.tmod b` callee contract, sibling of `divdi3_spec`) and
`jal value_int @0x800037d0` boxes the result into `.int (wrap64 (a.tmod b))` — the
same two-seam arithmetic shape as the landed `blockC_mul`/`divDispatchRow`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

set_option maxHeartbeats 4000000

/- The `mod` arithmetic arm `0x80003784 → 0x800037c4`, four blocks (two int-kind
`bne`s NOT taken, the divisor-nonzero `beqz` NOT taken, then the `__moddi3`
argument `mv`s).  All terminators are `br` with fixed polarity.  Body encodings
are identical to the `div` arm; only PCs and branch offsets differ. -/
#derive_case modDispatch chain
  [(0x80003784#64, 0x07813703#32),                -- ld   x14,0x78(x2)
   (0x80003788#64, 0x08813783#32),                -- ld   x15,0x88(x2)
   (0x8000378c#64, 0x00200693#32),                -- li   x13,2
   (0x80003790#64, 0x0ee13823#32),                -- sd   x14,0xf0(x2)
   (0x80003794#64, 0x10f13023#32)]                -- sd   x15,0x100(x2)
    terminator ⟨0x80003798#64, 0x46d81e63#32, 0x63#8, 0x1e#8, 0xd8#8, 0x46#8,
      .br bop.BNE false, 16, 13, 0x047c#13, 0#21, 0#12⟩ ;;
  [(0x8000379c#64, 0x09013703#32),                -- ld   x14,0x90(x2)
   (0x800037a0#64, 0x09813683#32),                -- ld   x13,0x98(x2)
   (0x800037a4#64, 0x0a013783#32),                -- ld   x15,0xa0(x2)
   (0x800037a8#64, 0x0ee13823#32),                -- sd   x14,0xf0(x2)
   (0x800037ac#64, 0x0ed13c23#32),                -- sd   x13,0xf8(x2)
   (0x800037b0#64, 0x10f13023#32)]                -- sd   x15,0x100(x2)
    terminator ⟨0x800037b4#64, 0x41051c63#32, 0x63#8, 0x1c#8, 0x05#8, 0x41#8,
      .br bop.BNE false, 10, 16, 0x0418#13, 0#21, 0#12⟩ ;;
  []                                              -- (empty body: the beqz block)
    terminator ⟨0x800037b8#64, 0x3e088463#32, 0x63#8, 0x84#8, 0x08#8, 0x3e#8,
      .br bop.BEQ false, 17, 0, 0x03e8#13, 0#21, 0#12⟩ ;;
  [(0x800037bc#64, 0x00088593#32),                -- mv   x11,x17  (a1 = a7 = divisor b)
   (0x800037c0#64, 0x00098513#32)]                -- mv   x10,x19  (a0 = s3  = dividend a)

/-- The `mod` arm pin list: `x16=2`/`x10=2` (right/left `int` kind tags driving
the two `bne`s), `x2=v2` (frame base of the loads/stores), `x9=sret` (the
`value_int` buffer), `x17=Wr` (divisor `b`, the `beqz` source and `mv a1`), and
`x19=Wl` (dividend `a`, the `mv a0` source).  The divisor-nonzero `beqz` guard
(`x17 = Wr ≠ 0`) is left to the caller by `chain_facts`.  Identical to `divDispL`. -/
def modDispL (v2 sret Wr Wl : BitVec 64) : GRegs :=
  [(16, 2#64), (10, 2#64), (2, v2), (9, sret), (17, Wr), (19, Wl)]

/-- The `mod` dispatch outcome: parked at `0x800037c4` (ready for `jal __moddi3`),
memory updated by the five stack stores, and the `__moddi3` call arguments staged
— `x10 = Wl` (dividend `a`), `x11 = Wr` (divisor `b`) — with `x9=sret`/`x2=v2`
surviving for the `value_int` seam and frame. -/
def ModDispatchPost (v2 sret Wr Wl : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks modDispatch
    (SegEvalState.init (modDispL v2 sret Wr Wl) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x800037c4#64 ∧
  gprGet c.σ 10 = some Wl ∧
  gprGet c.σ 11 = some Wr ∧
  gprGet c.σ 9 = some sret ∧
  gprGet c.σ 2 = some v2

/-- **The new mod leaf.**  The whole `mod` arm dispatch `0x80003784 → 0x800037c4`
as a `Triple`, assembled by `#derive_case` + `segToTriple` — no hand cloning.
`hwf` is the one `ChainOK` `decide`; `hpost` projects the end PC / write-log
memory off the outcome.  The `__moddi3` (`callSeg` → `moddi3_spec`) and
`value_int` seams compose on top to conclude `.int (wrap64 (a.tmod b))`. -/
theorem modDispatchRow (v2 sret Wr Wl : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre modDispatch (modDispL v2 sret Wr Wl) lds 0x80003784#64 m0)
      (ModDispatchPost v2 sret Wr Wl lds m0) := by
  apply segToTriple modDispatch (modDispL v2 sret Wr Wl) lds 0x80003784#64 m0
    (ModDispatchPost v2 sret Wr Wl lds m0)
    (by show ChainOK 0x80003784#64 [16, 10, 2, 9, 17, 19] modDispatch; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpc']
    show some (chainEndPC 0x80003784#64 (modDispL v2 sret Wr Wl) lds modDispatch)
      = some 0x800037c4#64
    rw [chainEndPC_eq_bt modDispatch 0x80003784#64 (modDispL v2 sret Wr Wl) lds (by decide)]
    rfl
  -- the `__moddi3` call arguments, read off `GHolds σ' out.regs` (mod's arm has no
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

#print axioms modDispatchRow

/-! ## The `__moddi3` seam via `callSeg` — concluding the mod value

The mod arm's arithmetic tail is the Shape-D call splice
`dispatch ≫ jal __moddi3 ≫ value_int`.  The callee contract is the REAL
`moddi3_spec` (`Vsa/Sim/DivSpec3.lean`, `x10.toInt = n.toInt.tmod d.toInt`);
`callSeg` threads it between the caller prefix (the `modDispatchRow` dispatch
above, then the `jal __moddi3` link landing at `moddi3_pre`'s entry `0x80004728`
with `x10=a`, `x11=b`, `x1=return`) and the caller suffix (the `mv`s + `jal
value_int` boxing the remainder), exactly as `divDispatchRow` threads
`divdi3_spec`. -/

/-- The spec-side mod bridge: for a nonzero divisor, `binOpSem .mod` is the
wrapped truncating remainder — the value the `value_int` suffix must produce from
`moddi3_spec`'s `x10` (`res.toInt = a.tmod b`, so `res = wrap64 (a.tmod b)`). -/
theorem binOpSem_mod_int (s : Vsa.While.Store) (a b : Int) (hb : b ≠ 0) :
    Vsa.While.binOpSem s .mod (.int a) (.int b) = some (.int (Vsa.While.wrap64 (a.tmod b))) := by
  simp only [Vsa.While.binOpSem]
  rw [if_neg (by simpa using hb)]

/-- **The `__moddi3` seam, realized via `callSeg` with the real `moddi3_spec`.**
Given the caller prefix landing the staged `modDispatchRow` args at the
`__moddi3` entry (`Triple P (moddi3_pre n d r m0)`) and the caller return suffix
boxing the remainder (`Triple (moddi3_post n d r m0) Q`), `callSeg` produces the
whole mod call site `Triple P Q` — the exact Shape-D composition the goal asks
for, with `moddi3_spec` (not a hand re-derivation) as the threaded callee. -/
theorem modCallSeam {P Q : Config → Prop} (n d r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (pre : Triple P (moddi3_pre n d r m0))
    (suf : Triple (moddi3_post n d r m0) Q) :
    Triple P Q :=
  callSeg pre (moddi3_spec n d r m0) suf

#print axioms binOpSem_mod_int
#print axioms modCallSeam

end Vsa.Sim
