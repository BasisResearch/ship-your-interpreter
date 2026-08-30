import Vsa.Sim.BinopChainGen
import Vsa.Sim.EvalDivChain
import Vsa.Sim.DivDispatchSeg
import Vsa.Sim.ModDispatchSeg
import Vsa.Sim.EqNeDispatchSeg

/-!
# `BinopChainInstances` — the four per-op item-1 entry linkages (div/mod/eq/ne)

Each op's entry linkage `eval<Op>Chain_run` (`0x8000351c → armPC`) is a ~15-line
instantiation of the generic `evalBinopChain_run` (`BinopChainGen.lean`) supplying
its FOUR data points and their self-checking `decide`s.  The heavy 16-step
block-soundness proof elaborates ONCE in `BinopChainGen`; these instances cost
only the `decide`s + argument marshalling (a few ms each).

Per-op data table (source: `Vsa/MemRepr.lean:63` for tokens, `opTableBase =
0x80019f84` from `EvalBinSim2.lean:77`, arm PCs from
`experiments/binop-value-tail-wiring.md` + each op's dispatch seg header; slot
bytes = little-endian `(armPC − opTableBase)` as Int32, self-checked by the
`hRoutes`/`slot_routes` `decide` — a wrong byte makes it fail):

| op  | token | index | slotAddr    | slot bytes         | armPC        |
|-----|-------|-------|-------------|--------------------|--------------|
| div | 14    | 3     | 0x80019f90  | 58 98 fe ff        | 0x800037dc   |
| mod | 15    | 4     | 0x80019f94  | 00 98 fe ff        | 0x80003784   |
| eq  | 19    | 8     | 0x80019fa4  | 60 97 fe ff        | 0x800036e4   |
| ne  | 17    | 6     | 0x80019f9c  | b0 97 fe ff        | 0x80003734   |

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.Sim.Code

namespace Vsa.Sim

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## The per-op entry-battery abbreviation

`BinopEntry σ i u vm v2 v8 sret Wl (tokBytes…) (slotBytes…) (…pins…)` packages the
~60 memory-pin hypotheses `evalBinopChain_run` consumes, so each op's
`eval<Op>Chain_run` states them once with its concrete token/slot bytes.  The four
data-point `decide`s are supplied inline at each instantiation (self-checking). -/

/-! ## `div` — validation instance (reproduces `evalDivChain_run`'s conclusion) -/

/-- **`div` item-1 entry linkage via the generic theorem.**  Reproduces
`evalDivChain_run`'s conclusion (`0x8000351c → 0x800037dc`, the `divDispL` pins)
by instantiating `evalBinopChain_run` at div's four data points
(`tokBytes = [0x0e,0,0,0]`, `idx = 3`, `slotAddr = 0x80019f90`,
`slotBytes = [0x58,0x98,0xfe,0xff]`, `armPC = 0x800037dc`) — the four `decide`s are
`divToken_val`/`divIndex_val` + inline `decide`s.  Same statement as the hand
`evalDivChain_run`; proves generator reproduction. -/
theorem evalDivChain_run_gen (σ : MState) (i u : Nat) (vm v2 v8 sret Wl : BitVec 64)
    (b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8)
    (k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000351c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hc : bytesVal MKind.lw [c0, c1, c2, c3] = (2#64 : BitVec 64))
    (hk : bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7] = (2#64 : BitVec 64))
    (a_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_hi : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (a_ht : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_al : (v8 + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (a_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some (0x0e#8))
    (a_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some (0x00#8))
    (a_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some (0x00#8))
    (a_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some (0x00#8))
    (b_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x004#12)).toNat)
    (b_hi : (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ 0x100000000)
    (b_ht : (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x004#12)).toNat)
    (b_al : (v8 + sign_extend (m := 64) (0x004#12)).toNat % 4 = 0)
    (b_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat]? = some b0)
    (b_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 1]? = some b1)
    (b_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 2]? = some b2)
    (b_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 3]? = some b3)
    (c_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x090#12)).toNat)
    (c_hi : (v2 + sign_extend (m := 64) (0x090#12)).toNat + 4 ≤ 0x100000000)
    (c_ht : (v2 + sign_extend (m := 64) (0x090#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x090#12)).toNat)
    (c_al : (v2 + sign_extend (m := 64) (0x090#12)).toNat % 4 = 0)
    (c_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat]? = some c0)
    (c_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 1]? = some c1)
    (c_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 2]? = some c2)
    (c_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 3]? = some c3)
    (d_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x098#12)).toNat)
    (d_hi : (v2 + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ 0x100000000)
    (d_ht : (v2 + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x098#12)).toNat)
    (d_al : (v2 + sign_extend (m := 64) (0x098#12)).toNat % 8 = 0)
    (d_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat]? = some d0)
    (d_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 1]? = some d1)
    (d_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 2]? = some d2)
    (d_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 3]? = some d3)
    (d_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 4]? = some d4)
    (d_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 5]? = some d5)
    (d_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 6]? = some d6)
    (d_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 7]? = some d7)
    (hSlot : DivSlotPinned σ.mem)
    (e_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)
    (e_hi : (v2 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (e_ht : (v2 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)
    (e_al : (v2 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (e_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat]? = some k0)
    (e_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some k1)
    (e_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some k2)
    (e_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some k3)
    (e_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some k4)
    (e_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some k5)
    (e_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some k6)
    (e_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some k7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 16⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some (0x800037dc#64) ∧
      σ'.regs.get? Register.x10 = some (2#64) ∧
      σ'.regs.get? Register.x12 = some (14#64) ∧
      σ'.regs.get? Register.x16 = some (2#64) ∧
      σ'.regs.get? Register.x17
        = some (bytesVal MKind.ld [d0, d1, d2, d3, d4, d5, d6, d7]) ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x9 = some sret ∧
      σ'.regs.get? Register.x19 = some Wl ∧
      σ'.mem = σ.mem ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
        σ'.regs.get? R = σ.regs.get? R) :=
  evalBinopChain_run σ i u vm v2 v8 sret Wl 2#64 2#64
    14#64 3#64 0x80019f90#64 0x800037dc#64
    0x0e#8 0x00#8 0x00#8 0x00#8 0x58#8 0x98#8 0xfe#8 0xff#8
    b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 k0 k1 k2 k3 k4 k5 k6 k7
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hG hpc hmi hx2 hx8 hx9 hx19 hmem hc hk
    a_lo a_hi a_ht a_al a_p0 a_p1 a_p2 a_p3
    b_lo b_hi b_ht b_al b_p0 b_p1 b_p2 b_p3
    c_lo c_hi c_ht c_al c_p0 c_p1 c_p2 c_p3
    d_lo d_hi d_ht d_al d_p0 d_p1 d_p2 d_p3 d_p4 d_p5 d_p6 d_p7
    hSlot
    e_lo e_hi e_ht e_al e_p0 e_p1 e_p2 e_p3 e_p4 e_p5 e_p6 e_p7 hi

#print axioms evalDivChain_run_gen

end Vsa.Sim
