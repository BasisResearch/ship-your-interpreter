import Vsa.Sim.EvalDivChain
import Vsa.Sim.SegFrameFactsAuto

/-!
# `EvalDivArm` — the `.div` item-1 seam: entry linkage ≫ dispatch row

This file closes the `.div` **item-1** obligation: from the binary-op arm-entry
(`0x8000351c`, the `TwoSubReturn` state that `blockB_binary` lands) through the
`jr` jump-table dispatch to `DivDispatchPost` (`0x8000381c`, the `__divdi3`
arguments staged) — the full span the value tail (`divValueTail`) consumes.

Two pieces, both axiom-clean, no seal / no heartbeat bump:

* **`divDispatchPost_of_chainEnd`** — the reusable glue.  From a config parked at
  the `.div` arm entry `0x800037dc` with the `divDispL` pins (`x16=2`, `x10=2`,
  `x2=v2`, `x9=sret`, `x17=Wr`, `x19=Wl`) and `mem = m0`, plus a `FrameBundle m0 v2`
  (the populated-frame geometry, a caller obligation) and the divisor-nonzero fact
  `Wr ≠ 0`, it builds `SegFramePre` and runs `divDispatchRow_frame`
  (`SegFrameFactsAuto`), landing `DivDispatchPost` at `0x8000381c`.  This is the
  chain-end → `SegPre` composition the item-1 recipe asks for; the `.div` analogue of
  invoking `eqDispatchRow_frame` from a caller.
* **`evalDivChain_dispatch`** — the full-span item-1 bridge.  Chains
  `evalDivChain_run` (`EvalDivChain.lean`, the `0x8000351c → 0x800037dc` entry
  linkage) onto `divDispatchPost_of_chainEnd`, giving `0x8000351c → 0x8000381c`
  from the entry hypothesis battery.  The divisor `Wr` is the loaded operand
  `bytesVal MKind.ld [d0..d7]` (the `x17` pin `evalDivChain_run` lands), so the
  caller's side condition is exactly `bytesVal MKind.ld [d0..d7] ≠ 0` — the
  successful-division path (`b = 0` is the M5 runtime-error case, out of scope).

## Residual left for the caller (the value tail + the arm frame)

`evalDivChain_dispatch` reaches `DivDispatchPost`.  To finish the live `evalDivSim`
eval case, the caller then threads `divValueTail` (`BinOpValueTails.lean`) — the two
real call seams `__divdi3` (`divdi3_spec`) and `value_int` — which itself leaves the
three concrete machine bridges `pre`/`stage`/`suf` (see
`experiments/binop-value-tail-wiring.md`), plus `blockD_v_rec` for the epilogue.
The two caller obligations THIS file surfaces are:

* `fb : FrameBundle σ.mem v2` — the populated-frame geometry at the arm's frame base
  `v2`, supplied by the eval-case caller exactly as `eqDispatchRow_frame`'s caller
  supplies it (mirrors the `blockB_binary` frame invariant);
* `hWr : bytesVal MKind.ld [d0..d7] ≠ 0` — the divisor-nonzero value-path condition.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

/-- **The chain-end → dispatch-post glue.**  From a config at the `.div` arm entry
`0x800037dc` carrying the `divDispL` pins (`mem = m0`, a `FrameBundle m0 v2`, and
`Wr ≠ 0`), build `SegFramePre` and run `divDispatchRow_frame`, reaching
`DivDispatchPost` at `0x8000381c` (the `__divdi3` arguments `x10=Wl`, `x11=Wr`
staged).  Reusable across any caller that lands the `.div` arm entry pins. -/
theorem divDispatchPost_of_chainEnd
    (σ' : MState) (i' u' : Nat) (v2 sret Wr Wl : BitVec 64)
    (hWr : Wr ≠ 0)
    (hG : GoodState σ')
    (hload : Vsa.Sim.Code.Eval_exprLoaded σ'.mem)
    (fb : FrameBundle σ'.mem v2)
    (hpc : σ'.regs.get? Register.PC = some 0x800037dc#64)
    (hmi : ∃ w, σ'.regs.get? Register.minstret = some w)
    (hx16 : σ'.regs.get? Register.x16 = some (2#64))
    (hx10 : σ'.regs.get? Register.x10 = some (2#64))
    (hx2 : σ'.regs.get? Register.x2 = some v2)
    (hx9 : σ'.regs.get? Register.x9 = some sret)
    (hx17 : σ'.regs.get? Register.x17 = some Wr)
    (hx19 : σ'.regs.get? Register.x19 = some Wl)
    (hx12 : σ'.regs.get? Register.x12 = some (14#64))
    (htick : i' < 2) :
    ∃ (c' : Config) (lds : List (List (BitVec 8))),
      Steps ⟨σ', i', u'⟩ c' ∧
      DivDispatchPost v2 sret Wr Wl lds σ'.mem σ'.sailOutput (fun R => σ'.regs.get? R) c' := by
  have hpre : SegFramePre (divDispL v2 sret Wr Wl) v2 0x800037dc#64 σ'.mem ⟨σ', i', u'⟩ := by
    refine ⟨hG, rfl, hpc, hmi, ?_, ?_, fb, hload, htick⟩
    · exact ⟨hx16, hx10, hx2, hx9, hx17, hx19, hx12, trivial⟩
    · show KeysOK ([16, 10, 2, 9, 17, 19, 12] : List Nat); decide
  obtain ⟨c', hstep, lds, hpost⟩ :=
    divDispatchRow_frame v2 sret Wr Wl σ'.sailOutput (fun R => σ'.regs.get? R) hWr σ'.mem
      ⟨σ', i', u'⟩ ⟨hpre, rfl, fun R => rfl⟩
  exact ⟨c', lds, hstep, hpost⟩

#print axioms divDispatchPost_of_chainEnd

set_option maxHeartbeats 4000000

/-- **The full-span `.div` item-1 bridge: `0x8000351c → 0x8000381c`.**  Chains
`evalDivChain_run` (entry linkage through the `jr` jump-table to the `.div` arm)
onto `divDispatchPost_of_chainEnd` (the arm dispatch), landing `DivDispatchPost`
from the binary-op arm-entry battery.  The divisor is `Wr = bytesVal MKind.ld
[d0..d7]` (the `x17` operand the chain lands); the caller supplies `Wr ≠ 0` and the
frame bundle `FrameBundle σ.mem v2`.  See the file header for the residual value-tail
work. -/
theorem evalDivChain_dispatch (σ : MState) (i u : Nat) (vm v2 v8 sret Wl : BitVec 64)
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
    (hi : i < 2)
    (hWr : (bytesVal MKind.ld [d0, d1, d2, d3, d4, d5, d6, d7] : BitVec 64) ≠ 0)
    (fb : FrameBundle σ.mem v2) :
    ∃ (c' : Config) (lds : List (List (BitVec 8))),
      Steps ⟨σ, i, u⟩ c' ∧
      DivDispatchPost v2 sret (bytesVal MKind.ld [d0, d1, d2, d3, d4, d5, d6, d7]) Wl
        lds σ.mem σ.sailOutput (fun R => σ.regs.get? R) c' := by
  -- run the entry linkage 0x8000351c → 0x800037dc, landing the divDispL pins
  obtain ⟨σ', i', hsteps, hi', hG', hpc', hx10', hx12', hx16', hx17', hx2', hx9', hx19',
      hmem', hout', hmi', hframe'⟩ :=
    evalDivChain_run σ i u vm v2 v8 sret Wl b0 b1 b2 b3 c0 c1 c2 c3
      d0 d1 d2 d3 d4 d5 d6 d7 k0 k1 k2 k3 k4 k5 k6 k7
      hG hpc hmi hx2 hx8 hx9 hx19 hmem hc hk
      a_lo a_hi a_ht a_al a_p0 a_p1 a_p2 a_p3
      b_lo b_hi b_ht b_al b_p0 b_p1 b_p2 b_p3
      c_lo c_hi c_ht c_al c_p0 c_p1 c_p2 c_p3
      d_lo d_hi d_ht d_al d_p0 d_p1 d_p2 d_p3 d_p4 d_p5 d_p6 d_p7
      hSlot
      e_lo e_hi e_ht e_al e_p0 e_p1 e_p2 e_p3 e_p4 e_p5 e_p6 e_p7 hi
  -- run the arm dispatch 0x800037dc → 0x8000381c via the reusable glue
  obtain ⟨c', lds, hstep, hpost⟩ :=
    divDispatchPost_of_chainEnd σ' i' (u + 16)
      v2 sret (bytesVal MKind.ld [d0, d1, d2, d3, d4, d5, d6, d7]) Wl hWr hG'
      (by rw [hmem']; exact hmem) (by rw [hmem']; exact fb)
      hpc' hmi' hx16' hx10' hx2' hx9' hx17' hx19' hx12' hi'
  -- `hpost : DivDispatchPost … σ'.mem σ'.sailOutput (fun R => σ'.regs.get? R) c'`.
  -- Rewrite memory / output to `σ` and re-relate the frame ghost `σ'.regs → σ.regs`.
  obtain ⟨hG'', hmem'', hpc'', hx10'', hx11'', hx9'', hx2'', h12'', h13'', htick'', hout'', hframeD⟩ := hpost
  rw [hmem'] at hmem''
  refine ⟨c', lds, hsteps.trans hstep, ?_⟩
  refine ⟨hG'', hmem'', hpc'', hx10'', hx11'', hx9'', hx2'', h12'', h13'', htick'', ?_, ?_⟩
  · rw [hout'', hout']
  · intro R hR he8
    rw [hframeD R hR he8]
    exact hframe' R hR he8

#print axioms evalDivChain_dispatch

end Vsa.Sim
