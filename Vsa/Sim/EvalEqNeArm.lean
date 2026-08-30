import Vsa.Sim.BinopChainGen
import Vsa.Sim.EqNeDispatchStrong

/-!
# `EvalEqNeArm` — the `.eq`/`.ne` item-1 seams: entry linkage ≫ dispatch row

The `.eq`/`.ne` analogues of `EvalDivArm.lean`.  Each op:

* `<op>DispatchPost_of_chainEnd` — chain-end → dispatch glue: from a config at the
  arm entry (`0x800036e4`/`0x80003734`) with `x2=sp` + `FrameBundle m0 sp`, builds
  `SegFramePre (eqDispL sp)` and runs `eqDispatchRow_frameS`/`neDispatchRow_frameS`,
  landing `EqDispatchPostS`/`NeDispatchPostS`;
* `eval<Op>Chain_dispatch` — full-span `0x8000351c → arm-exit`: the generic entry
  linkage (`evalBinopChain_run`, eq token 19/index 8/slot `0x80019fa4`/bytes
  `[0x60,0x97,0xfe,0xff]`; ne token 17/index 6/slot `0x80019f9c`/bytes
  `[0xb0,0x97,0xfe,0xff]`) onto the glue.

Note the entry linkage lands the div/mod-flavoured pins (`x16=2/x10=2/x17=Wr/x19=Wl`
etc.) but eq/ne's arm reads only `x2=sp`; the extra pins are simply unused.

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

/-! ## `eq` -/

/-- **The chain-end → dispatch-post glue for `.eq`.**  From the arm entry
`0x800036e4` with `x2=sp` + `FrameBundle m0 sp`, run to `EqDispatchPostS`. -/
theorem eqDispatchPost_of_chainEnd
    (σ' : MState) (i' u' : Nat) (sp : BitVec 64)
    (hG : GoodState σ')
    (hload : Vsa.Sim.Code.Eval_exprLoaded σ'.mem)
    (fb : FrameBundle σ'.mem sp)
    (hpc : σ'.regs.get? Register.PC = some 0x800036e4#64)
    (hmi : ∃ w, σ'.regs.get? Register.minstret = some w)
    (hx2 : σ'.regs.get? Register.x2 = some sp)
    (htick : i' < 2) :
    ∃ (c' : Config) (lds : List (List (BitVec 8))),
      Steps ⟨σ', i', u'⟩ c' ∧
      EqDispatchPostS sp lds σ'.mem σ'.sailOutput (fun R => σ'.regs.get? R) c' := by
  have hpre : SegFramePre (eqDispL sp) sp 0x800036e4#64 σ'.mem ⟨σ', i', u'⟩ := by
    refine ⟨hG, rfl, hpc, hmi, ?_, ?_, fb, hload, htick⟩
    · exact ⟨hx2, trivial⟩
    · show KeysOK ([2] : List Nat); decide
  obtain ⟨c', hstep, lds, hpost⟩ :=
    eqDispatchRow_frameS sp σ'.sailOutput (fun R => σ'.regs.get? R) σ'.mem
      ⟨σ', i', u'⟩ ⟨hpre, rfl, fun R => rfl⟩
  exact ⟨c', lds, hstep, hpost⟩

#print axioms eqDispatchPost_of_chainEnd

/-- **The chain-end → dispatch-post glue for `.ne`.** -/
theorem neDispatchPost_of_chainEnd
    (σ' : MState) (i' u' : Nat) (sp : BitVec 64)
    (hG : GoodState σ')
    (hload : Vsa.Sim.Code.Eval_exprLoaded σ'.mem)
    (fb : FrameBundle σ'.mem sp)
    (hpc : σ'.regs.get? Register.PC = some 0x80003734#64)
    (hmi : ∃ w, σ'.regs.get? Register.minstret = some w)
    (hx2 : σ'.regs.get? Register.x2 = some sp)
    (htick : i' < 2) :
    ∃ (c' : Config) (lds : List (List (BitVec 8))),
      Steps ⟨σ', i', u'⟩ c' ∧
      NeDispatchPostS sp lds σ'.mem σ'.sailOutput (fun R => σ'.regs.get? R) c' := by
  have hpre : SegFramePre (eqDispL sp) sp 0x80003734#64 σ'.mem ⟨σ', i', u'⟩ := by
    refine ⟨hG, rfl, hpc, hmi, ?_, ?_, fb, hload, htick⟩
    · exact ⟨hx2, trivial⟩
    · show KeysOK ([2] : List Nat); decide
  obtain ⟨c', hstep, lds, hpost⟩ :=
    neDispatchRow_frameS sp σ'.sailOutput (fun R => σ'.regs.get? R) σ'.mem
      ⟨σ', i', u'⟩ ⟨hpre, rfl, fun R => rfl⟩
  exact ⟨c', lds, hstep, hpost⟩

#print axioms neDispatchPost_of_chainEnd

/-! ## The full-span bridges.  The generic entry linkage's post exposes `x2 = v2`
(here `sp`), `mem = σ.mem`, `sailOutput`, `tick<2`, and the frame — everything the
glue consumes.  We package the entry battery once via a helper predicate to keep
each bridge short. -/

/-- The generic entry-linkage battery, applied to land the arm entry pins at `armPC`
for an `eq`/`ne`-shaped op.  A thin wrapper over `evalBinopChain_run` naming only the
`sp`(=v2) frame base the eq/ne glue needs. -/
theorem evalEqChain_dispatch (σ : MState) (i u : Nat)
    (vm sp v8 sret Wl kindR kindL : BitVec 64)
    (t0 t1 t2 t3 : BitVec 8)
    (b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8)
    (k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 8)
    (s0 s1 s2 s3 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000351c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some sp)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (ht : bytesVal MKind.lw [t0, t1, t2, t3] = (19#64 : BitVec 64))
    (hc : bytesVal MKind.lw [c0, c1, c2, c3] = kindR)
    (hk : bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7] = kindL)
    (a_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_hi : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (a_ht : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_al : (v8 + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (a_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some t0)
    (a_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some t1)
    (a_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some t2)
    (a_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some t3)
    (b_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x004#12)).toNat)
    (b_hi : (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ 0x100000000)
    (b_ht : (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x004#12)).toNat)
    (b_al : (v8 + sign_extend (m := 64) (0x004#12)).toNat % 4 = 0)
    (b_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat]? = some b0)
    (b_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 1]? = some b1)
    (b_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 2]? = some b2)
    (b_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 3]? = some b3)
    (c_lo : 0x80000000 ≤ (sp + sign_extend (m := 64) (0x090#12)).toNat)
    (c_hi : (sp + sign_extend (m := 64) (0x090#12)).toNat + 4 ≤ 0x100000000)
    (c_ht : (sp + sign_extend (m := 64) (0x090#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (sp + sign_extend (m := 64) (0x090#12)).toNat)
    (c_al : (sp + sign_extend (m := 64) (0x090#12)).toNat % 4 = 0)
    (c_p0 : σ.mem[(sp + sign_extend (m := 64) (0x090#12)).toNat]? = some c0)
    (c_p1 : σ.mem[(sp + sign_extend (m := 64) (0x090#12)).toNat + 1]? = some c1)
    (c_p2 : σ.mem[(sp + sign_extend (m := 64) (0x090#12)).toNat + 2]? = some c2)
    (c_p3 : σ.mem[(sp + sign_extend (m := 64) (0x090#12)).toNat + 3]? = some c3)
    (d_lo : 0x80000000 ≤ (sp + sign_extend (m := 64) (0x098#12)).toNat)
    (d_hi : (sp + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ 0x100000000)
    (d_ht : (sp + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (sp + sign_extend (m := 64) (0x098#12)).toNat)
    (d_al : (sp + sign_extend (m := 64) (0x098#12)).toNat % 8 = 0)
    (d_p0 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat]? = some d0)
    (d_p1 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 1]? = some d1)
    (d_p2 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 2]? = some d2)
    (d_p3 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 3]? = some d3)
    (d_p4 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 4]? = some d4)
    (d_p5 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 5]? = some d5)
    (d_p6 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 6]? = some d6)
    (d_p7 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 7]? = some d7)
    (hSlot : SlotPinned 0x80019fa4#64 s0 s1 s2 s3 σ.mem)
    (hs0 : s0 = 0x60#8) (hs1 : s1 = 0x97#8) (hs2 : s2 = 0xfe#8) (hs3 : s3 = 0xff#8)
    (e_lo : 0x80000000 ≤ (sp + sign_extend (m := 64) (0x000#12)).toNat)
    (e_hi : (sp + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (e_ht : (sp + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (sp + sign_extend (m := 64) (0x000#12)).toNat)
    (e_al : (sp + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (e_p0 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat]? = some k0)
    (e_p1 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some k1)
    (e_p2 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some k2)
    (e_p3 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some k3)
    (e_p4 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some k4)
    (e_p5 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some k5)
    (e_p6 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some k6)
    (e_p7 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some k7)
    (hi : i < 2)
    (fb : FrameBundle σ.mem sp) :
    ∃ (c' : Config) (lds : List (List (BitVec 8))),
      Steps ⟨σ, i, u⟩ c' ∧
      EqDispatchPostS sp lds σ.mem σ.sailOutput (fun R => σ.regs.get? R) c' := by
  subst hs0 hs1 hs2 hs3
  obtain ⟨σ', i', hsteps, hi', hG', hpc', hx10', hx12', hx16', hx17', hx2', hx9', hx19',
      hmem', hout', hmi', hframe'⟩ :=
    evalBinopChain_run σ i u vm sp v8 sret Wl kindR kindL
      19#64 8#64 0x80019fa4#64 0x800036e4#64
      t0 t1 t2 t3 0x60#8 0x97#8 0xfe#8 0xff#8
      b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 k0 k1 k2 k3 k4 k5 k6 k7
      ht (by rw [ht]; decide) (by decide) (by decide) (by rw [ht]; decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hG hpc hmi hx2 hx8 hx9 hx19 hmem hc hk
      a_lo a_hi a_ht a_al a_p0 a_p1 a_p2 a_p3
      b_lo b_hi b_ht b_al b_p0 b_p1 b_p2 b_p3
      c_lo c_hi c_ht c_al c_p0 c_p1 c_p2 c_p3
      d_lo d_hi d_ht d_al d_p0 d_p1 d_p2 d_p3 d_p4 d_p5 d_p6 d_p7
      hSlot
      e_lo e_hi e_ht e_al e_p0 e_p1 e_p2 e_p3 e_p4 e_p5 e_p6 e_p7 hi
  obtain ⟨c', lds, hstep, hpost⟩ :=
    eqDispatchPost_of_chainEnd σ' i' (u + 16) sp hG'
      (by rw [hmem']; exact hmem) (by rw [hmem']; exact fb)
      hpc' hmi' hx2' hi'
  obtain ⟨hG'', hmem'', hpc'', hx10'', hx11'', hx2'', htick'', hout'', hframeD, hpinsD⟩ := hpost
  rw [hmem'] at hmem''
  rw [hmem'] at hpinsD
  refine ⟨c', lds, hsteps.trans hstep, ?_⟩
  refine ⟨hG'', hmem'', hpc'', hx10'', hx11'', hx2'', htick'', ?_, ?_, hpinsD⟩
  · rw [hout'', hout']
  · intro R hR he8
    rw [hframeD R hR he8]
    exact hframe' R hR he8

#print axioms evalEqChain_dispatch

/-- **The full-span `.ne` item-1 bridge: `0x8000351c → 0x8000376c`.** -/
theorem evalNeChain_dispatch (σ : MState) (i u : Nat)
    (vm sp v8 sret Wl kindR kindL : BitVec 64)
    (t0 t1 t2 t3 : BitVec 8)
    (b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8)
    (k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 8)
    (s0 s1 s2 s3 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000351c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some sp)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hx9 : σ.regs.get? Register.x9 = some sret)
    (hx19 : σ.regs.get? Register.x19 = some Wl)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (ht : bytesVal MKind.lw [t0, t1, t2, t3] = (17#64 : BitVec 64))
    (hc : bytesVal MKind.lw [c0, c1, c2, c3] = kindR)
    (hk : bytesVal MKind.ld [k0, k1, k2, k3, k4, k5, k6, k7] = kindL)
    (a_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_hi : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (a_ht : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_al : (v8 + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (a_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some t0)
    (a_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some t1)
    (a_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some t2)
    (a_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some t3)
    (b_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x004#12)).toNat)
    (b_hi : (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ 0x100000000)
    (b_ht : (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x004#12)).toNat)
    (b_al : (v8 + sign_extend (m := 64) (0x004#12)).toNat % 4 = 0)
    (b_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat]? = some b0)
    (b_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 1]? = some b1)
    (b_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 2]? = some b2)
    (b_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 3]? = some b3)
    (c_lo : 0x80000000 ≤ (sp + sign_extend (m := 64) (0x090#12)).toNat)
    (c_hi : (sp + sign_extend (m := 64) (0x090#12)).toNat + 4 ≤ 0x100000000)
    (c_ht : (sp + sign_extend (m := 64) (0x090#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (sp + sign_extend (m := 64) (0x090#12)).toNat)
    (c_al : (sp + sign_extend (m := 64) (0x090#12)).toNat % 4 = 0)
    (c_p0 : σ.mem[(sp + sign_extend (m := 64) (0x090#12)).toNat]? = some c0)
    (c_p1 : σ.mem[(sp + sign_extend (m := 64) (0x090#12)).toNat + 1]? = some c1)
    (c_p2 : σ.mem[(sp + sign_extend (m := 64) (0x090#12)).toNat + 2]? = some c2)
    (c_p3 : σ.mem[(sp + sign_extend (m := 64) (0x090#12)).toNat + 3]? = some c3)
    (d_lo : 0x80000000 ≤ (sp + sign_extend (m := 64) (0x098#12)).toNat)
    (d_hi : (sp + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ 0x100000000)
    (d_ht : (sp + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (sp + sign_extend (m := 64) (0x098#12)).toNat)
    (d_al : (sp + sign_extend (m := 64) (0x098#12)).toNat % 8 = 0)
    (d_p0 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat]? = some d0)
    (d_p1 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 1]? = some d1)
    (d_p2 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 2]? = some d2)
    (d_p3 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 3]? = some d3)
    (d_p4 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 4]? = some d4)
    (d_p5 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 5]? = some d5)
    (d_p6 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 6]? = some d6)
    (d_p7 : σ.mem[(sp + sign_extend (m := 64) (0x098#12)).toNat + 7]? = some d7)
    (hSlot : SlotPinned 0x80019f9c#64 s0 s1 s2 s3 σ.mem)
    (hs0 : s0 = 0xb0#8) (hs1 : s1 = 0x97#8) (hs2 : s2 = 0xfe#8) (hs3 : s3 = 0xff#8)
    (e_lo : 0x80000000 ≤ (sp + sign_extend (m := 64) (0x000#12)).toNat)
    (e_hi : (sp + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (e_ht : (sp + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (sp + sign_extend (m := 64) (0x000#12)).toNat)
    (e_al : (sp + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (e_p0 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat]? = some k0)
    (e_p1 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some k1)
    (e_p2 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some k2)
    (e_p3 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some k3)
    (e_p4 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some k4)
    (e_p5 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some k5)
    (e_p6 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some k6)
    (e_p7 : σ.mem[(sp + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some k7)
    (hi : i < 2)
    (fb : FrameBundle σ.mem sp) :
    ∃ (c' : Config) (lds : List (List (BitVec 8))),
      Steps ⟨σ, i, u⟩ c' ∧
      NeDispatchPostS sp lds σ.mem σ.sailOutput (fun R => σ.regs.get? R) c' := by
  subst hs0 hs1 hs2 hs3
  obtain ⟨σ', i', hsteps, hi', hG', hpc', hx10', hx12', hx16', hx17', hx2', hx9', hx19',
      hmem', hout', hmi', hframe'⟩ :=
    evalBinopChain_run σ i u vm sp v8 sret Wl kindR kindL
      17#64 6#64 0x80019f9c#64 0x80003734#64
      t0 t1 t2 t3 0xb0#8 0x97#8 0xfe#8 0xff#8
      b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 k0 k1 k2 k3 k4 k5 k6 k7
      ht (by rw [ht]; decide) (by decide) (by decide) (by rw [ht]; decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hG hpc hmi hx2 hx8 hx9 hx19 hmem hc hk
      a_lo a_hi a_ht a_al a_p0 a_p1 a_p2 a_p3
      b_lo b_hi b_ht b_al b_p0 b_p1 b_p2 b_p3
      c_lo c_hi c_ht c_al c_p0 c_p1 c_p2 c_p3
      d_lo d_hi d_ht d_al d_p0 d_p1 d_p2 d_p3 d_p4 d_p5 d_p6 d_p7
      hSlot
      e_lo e_hi e_ht e_al e_p0 e_p1 e_p2 e_p3 e_p4 e_p5 e_p6 e_p7 hi
  obtain ⟨c', lds, hstep, hpost⟩ :=
    neDispatchPost_of_chainEnd σ' i' (u + 16) sp hG'
      (by rw [hmem']; exact hmem) (by rw [hmem']; exact fb)
      hpc' hmi' hx2' hi'
  obtain ⟨hG'', hmem'', hpc'', hx10'', hx11'', hx2'', htick'', hout'', hframeD, hpinsD⟩ := hpost
  rw [hmem'] at hmem''
  rw [hmem'] at hpinsD
  refine ⟨c', lds, hsteps.trans hstep, ?_⟩
  refine ⟨hG'', hmem'', hpc'', hx10'', hx11'', hx2'', htick'', ?_, ?_, hpinsD⟩
  · rw [hout'', hout']
  · intro R hR he8
    rw [hframeD R hR he8]
    exact hframe' R hR he8

#print axioms evalNeChain_dispatch

end Vsa.Sim
