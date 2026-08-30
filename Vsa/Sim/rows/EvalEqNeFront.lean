import Vsa.Sim.rows.EvalEqNeRow
import Vsa.Sim.EqNeReprReadback
import Vsa.Sim.EqNeDispatchStrong
import Vsa.Sim.ValueEqualSpec4

/-!
# `EvalEqNeFront` — the eq/ne front closure (task 3)

The div-parity front wiring that reseats `evalEqNeSim`.  Composes the entry linkage +
dispatch (`evalEqChain_dispatch`/`evalNeChain_dispatch`) with the reflected-dispatch
operand repr readback (blocker B, `EqNeReprReadback`), the `value_equal` call
(`value_equal_spec_full`, both str + non-str branches), and the shared eq/ne back half
(`blockC_eqne`).

Deliverables (models in parens):
* `eqDispatch_lpins` — six source `LPins8` out of the eqDispatch `ChainFacts`.
* `eqnePreBridge` (model `divPreBridge`) — `jal value_equal` → `ve_pre`.
* `veReturnBridge` (no direct model) — `ve_str_post` → `VeReturn`.
* `EqResid` bundle (model `DivResid`).
* `blockC_eqne_front` (model `blockC_div`).
* reseated `evalEqNeSim` (model `evalDivSim`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- `NotWrittenVEStr R → NotWritten R` (the str write-set contains `NotWritten`'s set). -/
theorem notWritten_of_vestr {R : Register} (h : NotWrittenVEStr R) : NotWritten R := by
  obtain ⟨_, _, _, _, _, hx10, hx11, hx12, hx13, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := h
  exact ⟨hx10, hx11, hx12, hx13, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩

/-- `lds.headD [] = lds.getD 0 []`. -/
theorem eqDisp_headD_getD0 (lds : List (List (BitVec 8))) :
    lds.headD [] = lds.getD 0 [] := by cases lds <;> rfl

/-- `lds.tail.getD n [] = lds.getD (n+1) []`. -/
theorem eqDisp_tail_getD (lds : List (List (BitVec 8))) (n : Nat) :
    lds.tail.getD n [] = lds.getD (n+1) [] := by cases lds <;> rfl

/-- Extract the six load `LPins8` out of the eqDispatch `ChainFacts`.  The dispatch
block issues six `ld`s from `x2+0x78/0x80/0x88/0x90/0x98/0xa0`; each load's
`MemFacts` component of `ProgFactsM` carries `LPins8 m0 (eaddr) (lds[k])` at the
constant entry memory `m0` (loads don't write). -/
theorem eqDispatch_lpins (m0 : Std.ExtHashMap Nat (BitVec 8)) (sp : BitVec 64)
    (lds : List (List (BitVec 8)))
    (hfacts : ChainFacts m0 m0 (eqDispL sp) lds eqDispatch) :
    LPins8 m0 (sp + 0x78#64).toNat (lds.getD 0 []) ∧
    LPins8 m0 (sp + 0x80#64).toNat (lds.getD 1 []) ∧
    LPins8 m0 (sp + 0x88#64).toNat (lds.getD 2 []) ∧
    LPins8 m0 (sp + 0x90#64).toNat (lds.getD 3 []) ∧
    LPins8 m0 (sp + 0x98#64).toNat (lds.getD 4 []) ∧
    LPins8 m0 (sp + 0xa0#64).toNat (lds.getD 5 []) := by
  obtain ⟨⟨hprog, -, -⟩, -⟩ := hfacts
  -- peel six loads; each MemFacts.2 = LPins8 at the ld's eaddr
  obtain ⟨-, -, hmf0, hprog⟩ := hprog
  obtain ⟨-, -, hmf1, hprog⟩ := hprog
  obtain ⟨-, -, hmf2, hprog⟩ := hprog
  obtain ⟨-, -, hmf3, hprog⟩ := hprog
  obtain ⟨-, -, hmf4, hprog⟩ := hprog
  obtain ⟨-, -, hmf5, hprog⟩ := hprog
  have e78 : (sp + sign_extend (m := 64) (0x078#12) : BitVec 64) = sp + 0x78#64 := by
    rw [show (sign_extend (m := 64) (0x078#12) : BitVec 64) = 0x78#64 from by decide]
  have e80 : (sp + sign_extend (m := 64) (0x080#12) : BitVec 64) = sp + 0x80#64 := by
    rw [show (sign_extend (m := 64) (0x080#12) : BitVec 64) = 0x80#64 from by decide]
  have e88 : (sp + sign_extend (m := 64) (0x088#12) : BitVec 64) = sp + 0x88#64 := by
    rw [show (sign_extend (m := 64) (0x088#12) : BitVec 64) = 0x88#64 from by decide]
  have e90 : (sp + sign_extend (m := 64) (0x090#12) : BitVec 64) = sp + 0x90#64 := by
    rw [show (sign_extend (m := 64) (0x090#12) : BitVec 64) = 0x90#64 from by decide]
  have e98 : (sp + sign_extend (m := 64) (0x098#12) : BitVec 64) = sp + 0x98#64 := by
    rw [show (sign_extend (m := 64) (0x098#12) : BitVec 64) = 0x98#64 from by decide]
  have ea0 : (sp + sign_extend (m := 64) (0x0a0#12) : BitVec 64) = sp + 0xa0#64 := by
    rw [show (sign_extend (m := 64) (0x0a0#12) : BitVec 64) = 0xa0#64 from by decide]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hmf0.2
    change LPins8 m0 (sp + sign_extend (m := 64) (0x078#12) : BitVec 64).toNat
      (lds.headD []) at h
    rw [e78, eqDisp_headD_getD0] at h; exact h
  · have h := hmf1.2
    change LPins8 m0 (sp + sign_extend (m := 64) (0x080#12) : BitVec 64).toNat
      (lds.tail.headD []) at h
    rw [e80, eqDisp_headD_getD0, eqDisp_tail_getD] at h; exact h
  · have h := hmf2.2
    change LPins8 m0 (sp + sign_extend (m := 64) (0x088#12) : BitVec 64).toNat
      (lds.tail.tail.headD []) at h
    rw [e88, eqDisp_headD_getD0, eqDisp_tail_getD, eqDisp_tail_getD] at h; exact h
  · have h := hmf3.2
    change LPins8 m0 (sp + sign_extend (m := 64) (0x090#12) : BitVec 64).toNat
      (lds.tail.tail.tail.headD []) at h
    rw [e90, eqDisp_headD_getD0, eqDisp_tail_getD, eqDisp_tail_getD, eqDisp_tail_getD] at h
    exact h
  · have h := hmf4.2
    change LPins8 m0 (sp + sign_extend (m := 64) (0x098#12) : BitVec 64).toNat
      (lds.tail.tail.tail.tail.headD []) at h
    rw [e98, eqDisp_headD_getD0, eqDisp_tail_getD, eqDisp_tail_getD, eqDisp_tail_getD,
      eqDisp_tail_getD] at h
    exact h
  · have h := hmf5.2
    change LPins8 m0 (sp + sign_extend (m := 64) (0x0a0#12) : BitVec 64).toNat
      (lds.tail.tail.tail.tail.tail.headD []) at h
    rw [ea0, eqDisp_headD_getD0, eqDisp_tail_getD, eqDisp_tail_getD, eqDisp_tail_getD,
      eqDisp_tail_getD, eqDisp_tail_getD] at h
    exact h

/-- The `ne` sibling of `eqDispatch_lpins` (byte-identical block, same proof). -/
theorem neDispatch_lpins (m0 : Std.ExtHashMap Nat (BitVec 8)) (sp : BitVec 64)
    (lds : List (List (BitVec 8)))
    (hfacts : ChainFacts m0 m0 (eqDispL sp) lds neDispatch) :
    LPins8 m0 (sp + 0x78#64).toNat (lds.getD 0 []) ∧
    LPins8 m0 (sp + 0x80#64).toNat (lds.getD 1 []) ∧
    LPins8 m0 (sp + 0x88#64).toNat (lds.getD 2 []) ∧
    LPins8 m0 (sp + 0x90#64).toNat (lds.getD 3 []) ∧
    LPins8 m0 (sp + 0x98#64).toNat (lds.getD 4 []) ∧
    LPins8 m0 (sp + 0xa0#64).toNat (lds.getD 5 []) := by
  obtain ⟨⟨hprog, -, -⟩, -⟩ := hfacts
  obtain ⟨-, -, hmf0, hprog⟩ := hprog
  obtain ⟨-, -, hmf1, hprog⟩ := hprog
  obtain ⟨-, -, hmf2, hprog⟩ := hprog
  obtain ⟨-, -, hmf3, hprog⟩ := hprog
  obtain ⟨-, -, hmf4, hprog⟩ := hprog
  obtain ⟨-, -, hmf5, hprog⟩ := hprog
  have e78 : (sp + sign_extend (m := 64) (0x078#12) : BitVec 64) = sp + 0x78#64 := by
    rw [show (sign_extend (m := 64) (0x078#12) : BitVec 64) = 0x78#64 from by decide]
  have e80 : (sp + sign_extend (m := 64) (0x080#12) : BitVec 64) = sp + 0x80#64 := by
    rw [show (sign_extend (m := 64) (0x080#12) : BitVec 64) = 0x80#64 from by decide]
  have e88 : (sp + sign_extend (m := 64) (0x088#12) : BitVec 64) = sp + 0x88#64 := by
    rw [show (sign_extend (m := 64) (0x088#12) : BitVec 64) = 0x88#64 from by decide]
  have e90 : (sp + sign_extend (m := 64) (0x090#12) : BitVec 64) = sp + 0x90#64 := by
    rw [show (sign_extend (m := 64) (0x090#12) : BitVec 64) = 0x90#64 from by decide]
  have e98 : (sp + sign_extend (m := 64) (0x098#12) : BitVec 64) = sp + 0x98#64 := by
    rw [show (sign_extend (m := 64) (0x098#12) : BitVec 64) = 0x98#64 from by decide]
  have ea0 : (sp + sign_extend (m := 64) (0x0a0#12) : BitVec 64) = sp + 0xa0#64 := by
    rw [show (sign_extend (m := 64) (0x0a0#12) : BitVec 64) = 0xa0#64 from by decide]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hmf0.2
    change LPins8 m0 (sp + sign_extend (m := 64) (0x078#12) : BitVec 64).toNat
      (lds.headD []) at h
    rw [e78, eqDisp_headD_getD0] at h; exact h
  · have h := hmf1.2
    change LPins8 m0 (sp + sign_extend (m := 64) (0x080#12) : BitVec 64).toNat
      (lds.tail.headD []) at h
    rw [e80, eqDisp_headD_getD0, eqDisp_tail_getD] at h; exact h
  · have h := hmf2.2
    change LPins8 m0 (sp + sign_extend (m := 64) (0x088#12) : BitVec 64).toNat
      (lds.tail.tail.headD []) at h
    rw [e88, eqDisp_headD_getD0, eqDisp_tail_getD, eqDisp_tail_getD] at h; exact h
  · have h := hmf3.2
    change LPins8 m0 (sp + sign_extend (m := 64) (0x090#12) : BitVec 64).toNat
      (lds.tail.tail.tail.headD []) at h
    rw [e90, eqDisp_headD_getD0, eqDisp_tail_getD, eqDisp_tail_getD, eqDisp_tail_getD] at h
    exact h
  · have h := hmf4.2
    change LPins8 m0 (sp + sign_extend (m := 64) (0x098#12) : BitVec 64).toNat
      (lds.tail.tail.tail.tail.headD []) at h
    rw [e98, eqDisp_headD_getD0, eqDisp_tail_getD, eqDisp_tail_getD, eqDisp_tail_getD,
      eqDisp_tail_getD] at h
    exact h
  · have h := hmf5.2
    change LPins8 m0 (sp + sign_extend (m := 64) (0x0a0#12) : BitVec 64).toNat
      (lds.tail.tail.tail.tail.tail.headD []) at h
    rw [ea0, eqDisp_headD_getD0, eqDisp_tail_getD, eqDisp_tail_getD, eqDisp_tail_getD,
      eqDisp_tail_getD, eqDisp_tail_getD] at h
    exact h

/-! ## `eqnePreBridge` — the `jal value_equal` → `ve_pre` bridge (model `divPreBridge`)

From an `eq`/`ne` dispatch post `EqDispatchPostS`/`NeDispatchPostS` (parked at the jal
PC `jalPC`, `x10 = bufa = sp+0x40`, `x11 = bufb = sp+0x20`, `x2 = sp`, `mem = mA`) plus
the two buffer `ValueRepr`s on `mA` (blocker B) plus the `value_equal` caller
obligations (`Value_equalLoaded`/`JumpTable` on `mA`, both `VERegion`s, `r%4=0`), the
single `jal value_equal @jalPC` links `x1 := link` (= jalPC+4), lands `0x8000285c`, and
delivers `ve_pre g bufa bufb link N φc va vb mA out0`.  Parameterised by `jalPC`/`link`
and the site lemma so ONE bridge serves eq (`0x8000371c`/`0x80003720`) and ne
(`0x8000376c`/`0x80003770`). -/
theorem eqnePreBridge
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (sp sret : BitVec 64)
    (va vb : Value) (mA : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (jalPC link : BitVec 64) (jImm : BitVec 21)
    -- the jal value_equal site (eq: 0x8000371c/0x1ff140; ne: 0x8000376c/0x1ff0f0)
    (jalSite : ∀ (σ : MState) (i u : Nat) (pc vminstret : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some pc →
      σ.regs.get? Register.minstret = some vminstret →
      Vsa.Sim.Code.Eval_exprLoaded σ.mem → pc = jalPC → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
        σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ pc vminstret jImm Register.x1 (BitVec.addInt pc 4)))
    (hjalTgt : (jalPC + sign_extend (m := 64) jImm) = (0x8000285c#64 : BitVec 64))
    (hlink : BitVec.addInt jalPC 4 = link)
    (hlinkAl : (BitVec.update (link + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    -- value_equal caller obligations on the post-dispatch memory `mA`
    (hVeLoaded : Vsa.Sim.Code.Value_equalLoaded mA)
    (hJT : JumpTable mA)
    (hEE : Vsa.Sim.Code.Eval_exprLoaded mA)
    (hRegA : VERegion (sp + 0x40#64)) (hRegB : VERegion (sp + 0x20#64))
    (hReprA : ValueRepr mA N φc (sp + 0x40#64).toNat va)
    (hReprB : ValueRepr mA N φc (sp + 0x20#64).toNat vb) :
    Triple
      (fun c => c.σ.mem = mA ∧
        c.σ.regs.get? Register.PC = some jalPC ∧
        c.σ.regs.get? Register.x10 = some (sp + 0x40#64) ∧
        c.σ.regs.get? Register.x11 = some (sp + 0x20#64) ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        c.σ.regs.get? Register.x9 = some sret ∧
        (∀ R : Register, NotWrittenVEStr R → (Register.x1 == R) = false →
          c.σ.regs.get? R = gpre R) ∧
        c.σ.sailOutput = out0 ∧ c.tick < 2 ∧ GoodState c.σ)
      (fun c => c.σ.regs.get? Register.x2 = some sp ∧
        c.σ.regs.get? Register.x9 = some sret ∧
        (∀ R : Register, NotWrittenVEStr R → (Register.x1 == R) = false →
          c.σ.regs.get? R = gpre R) ∧
        ve_pre (fun R => c.σ.regs.get? R) (sp + 0x40#64) (sp + 0x20#64) link N φc va vb mA out0 c) := by
  intro c hpre
  obtain ⟨hmem, hpc, hx10, hx11, hx2, hx9, hpreframe, hout, htick, hG⟩ := hpre
  obtain ⟨vmi, hmi⟩ := hG.minstret
  have hEEσ : Vsa.Sim.Code.Eval_exprLoaded c.σ.mem := by rw [hmem]; exact hEE
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    jalSite c.σ c.tick c.steps jalPC vmi hG hpc hmi hEEσ rfl htick
  have hstep' : Step c ⟨σ', i', c.steps + 1⟩ := by cases c; exact hstep
  have hmem'A : σ'.mem = mA := by rw [hmem']; exact hmem
  have hpc' : σ'.regs.get? Register.PC = some (0x8000285c#64) := by
    have := obs_jal_pc hobs; rwa [hjalTgt] at this
  have hlink' : σ'.regs.get? Register.x1 = some link := by
    have := obs_jal_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hlink] at this
  have hx10' : σ'.regs.get? Register.x10 = some (sp + 0x40#64) :=
    obs_jal_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx10
  have hx11' : σ'.regs.get? Register.x11 = some (sp + 0x20#64) :=
    obs_jal_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx11
  have hx2' : σ'.regs.get? Register.x2 = some sp :=
    obs_jal_other hobs Register.x2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx2
  have hx9' : σ'.regs.get? Register.x9 = some sret :=
    obs_jal_other hobs Register.x9 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx9
  have hout' : σ'.sailOutput = out0 := by
    rw [hobs.out, sailOutput_sigmaPost_jal]; exact hout
  have hframe' : ∀ R : Register, NotWrittenVEStr R → (Register.x1 == R) = false →
      σ'.regs.get? R = gpre R := by
    intro R hR hx1ne
    rw [frame_jal hobs R hx1ne (notWritten_of_vestr hR)]; exact hpreframe R hR hx1ne
  refine ⟨⟨σ', i', c.steps + 1⟩, Steps.single hstep', hx2', hx9', hframe', ?_⟩
  refine ⟨hG', ?_, ?_, ?_, hout', hpc', hx10', hx11', hlink', obs_jal_minstret hobs,
    hi', ?_, ?_, hRegA, hRegB, hlinkAl, fun R _ => rfl⟩
  · rw [hmem'A]; exact hVeLoaded
  · rw [hmem'A]; exact hJT
  · exact hmem'A
  · exact hReprA
  · exact hReprB

#print axioms eqnePreBridge

/-! ## `veReturnBridge` — `ve_str_post` → `VeReturn` (NEW; no direct model)

`value_equal_spec_full` produces `ve_str_post gsnap link fbase vl vr mEnt out0 c`, where
`gsnap` is the value_equal-entry register snapshot (from `eqnePreBridge`), `fbase` is the
value_equal entry `sp` (= the caller frame base `sp-1088`), and `mEnt` is the
value_equal-entry memory (`mA`).  `blockC_eqne` consumes `VeReturn g fbase sret vl vr link
out0 mEnt c`.  This bridge reconciles the two:

* `x9 = sret` — from `gsnap x9 = sret` (the dispatch preserved `x9`; `x9 ∈ NotWrittenVEStr`);
* the eval-frame collapse `hframe` — `gsnap R = g R` for `NotWrittenVEStr R`, `x9≠R`, `x19≠R`;
* `MemExtends mEnt c.σ.mem` — value_equal never deletes keys (writeMap8 spill preserves
  presence); the exposed `ve_str_post` carries only outside-window agreement, so this is
  taken as an explicit hypothesis (a stronger `ve_str_post` would carry it internally). -/
theorem veReturnBridge
    (gsnap g : (R : Register) → Option (RegisterType R))
    (fbase sret : BitVec 64) (vl vr : Value) (link : BitVec 64)
    (out0 : Array String) (mEnt : Mem) (c : Config)
    (hgsx9 : gsnap Register.x9 = some sret)
    (hsnapEval : ∀ R : Register, NotWrittenVEStr R →
      (Register.x9 == R) = false → (Register.x19 == R) = false → gsnap R = g R)
    (hMemExt : MemExtends mEnt c.σ.mem)
    (hpost : ve_str_post gsnap link fbase vl vr mEnt out0 c) :
    VeReturn g fbase sret vl vr link out0 mEnt c := by
  obtain ⟨hG, hpc, hx10, hx1, hx2, hmi, htick, hout, hmemframe, hframe⟩ := hpost
  refine
    { hG := hG
      hpc := hpc
      hx10 := hx10
      hx9 := ?_
      hsp := hx2
      hmi := hmi
      htick := htick
      hout := hout
      hmemframe := hmemframe
      hMemExt := hMemExt
      hframe := ?_ }
  · -- x9 = sret: from the entry snapshot (x9 ∈ NotWrittenVEStr, unwritten by value_equal)
    rw [hframe Register.x9 (by decide)]; exact hgsx9
  · intro R hR he9 he19
    rw [hframe R hR]; exact hsnapEval R hR he9 he19

#print axioms veReturnBridge

/-! ## `EqFrontData` — the post-dispatch front residual bundle (div-parity caller data)

The data `blockC_eqne_front` consumes at the `value_equal` call site but cannot derive
from `TwoSubReturn` alone: the dispatch has already run to the `jal value_equal` PC
(`jalPC`), landing memory `mA` (the post-dispatch memory), with the compare buffers
`bufa = fbase+0x40`, `bufb = fbase+0x20` staged in `x10`/`x11`, `x2 = fbase`, `x9 = sret`;
the two operand `ValueRepr`s read back out of the reflected copy (blocker B); the
`value_equal` caller obligations on `mA` (`Value_equalLoaded`/`JumpTable`, both
`VERegion`s, `r`-alignment); the `str`-path witness; and the register/frame snapshot for
`veReturnBridge`.  This is the eq/ne analogue of `DivResid`'s post-dispatch loaded-image
+ operand data — the front machine-transport that the reseat threads as a caller residual,
exactly as `evalDivSim` threads `DivResid`. -/
structure EqFrontData
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (fbase sret : BitVec 64) (vl vr : Value) (link jalPC : BitVec 64) (jImm : BitVec 21)
    (mA : Mem) (out0 : Array String) (cD : Config) : Prop where
  -- the dispatch outcome parked at the `jal value_equal` PC
  hmemD : cD.σ.mem = mA
  hG : GoodState cD.σ
  htick : cD.tick < 2
  hpc : cD.σ.regs.get? Register.PC = some jalPC
  hjalTgt : (jalPC + sign_extend (m := 64) jImm) = (0x8000285c#64 : BitVec 64)
  hlink : BitVec.addInt jalPC 4 = link
  hlinkAl : (BitVec.update (link + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
  hx10 : cD.σ.regs.get? Register.x10 = some (fbase + 0x40#64)
  hx11 : cD.σ.regs.get? Register.x11 = some (fbase + 0x20#64)
  hx2 : cD.σ.regs.get? Register.x2 = some fbase
  hx9 : cD.σ.regs.get? Register.x9 = some sret
  hout : cD.σ.sailOutput = out0
  -- the `jal value_equal` site lemma (eq: 0x8000371c/0x1ff140; ne: 0x8000376c/0x1ff0f0)
  jalSite : ∀ (σ : MState) (i u : Nat) (pc vminstret : BitVec 64),
    GoodState σ → σ.regs.get? Register.PC = some pc →
    σ.regs.get? Register.minstret = some vminstret →
    Vsa.Sim.Code.Eval_exprLoaded σ.mem → pc = jalPC → i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ pc vminstret jImm Register.x1 (BitVec.addInt pc 4))
  -- `value_equal` caller obligations on `mA`
  hVeLoaded : Vsa.Sim.Code.Value_equalLoaded mA
  hJT : JumpTable mA
  hEE : Vsa.Sim.Code.Eval_exprLoaded mA
  hStrc : Vsa.Sim.Code.StrcmpLoaded mA
  hMask : MaskPinned mA
  hRegA : VERegion (fbase + 0x40#64)
  hRegB : VERegion (fbase + 0x20#64)
  hReprA : ValueRepr mA N φc (fbase + 0x40#64).toNat vl
  hReprB : ValueRepr mA N φc (fbase + 0x20#64).toNat vr
  hφc : ∀ (a b : Vsa.While.Addr), φc a = φc b → a = b
  hN : ∀ (f h : NativeFn), N.addr f = N.addr h → f = h
  hraln4 : link.toNat % 4 = 0
  -- the `str`-path witness (consumed only when both operands are strings)
  hstrwit : ∀ sa sb, vl = .str sa → vr = .str sb →
    ∃ (pa' pb' : Nat) (csa csb : List Char),
      read64 mA ((fbase + 0x40#64).toNat + 8) = some pa' ∧
      read64 mA ((fbase + 0x20#64).toNat + 8) = some pb' ∧
      CStr mA pa' csa ∧ CStr mA pb' csb ∧ sa = String.ofList csa ∧ sb = String.ofList csb ∧
      StrcmpRegion (BitVec.ofNat 64 pa') csa.length ∧
      StrcmpRegion (BitVec.ofNat 64 pb') csb.length ∧
      StrcmpWRegion (BitVec.ofNat 64 pa') csa.length ∧
      StrcmpWRegion (BitVec.ofNat 64 pb') csb.length ∧
      VEStrRegions fbase pa' pb' csa.length csb.length
  -- `veReturnBridge` inputs: the eval-frame collapse of the dispatch snapshot (the jal
  -- preserves every `NotWrittenVEStr\{x1}` register, so this rides to the value_equal
  -- entry), the `x1 = link` eval fact, and the `MemExtends mA → return` presence fact
  hgx1 : g Register.x1 = some link
  hsnapEval : ∀ R : Register, NotWrittenVEStr R → (Register.x1 == R) = false →
    (Register.x9 == R) = false → (Register.x19 == R) = false →
    cD.σ.regs.get? R = g R
  hMemExtRet : ∀ (c' : Config),
    (∀ a, ¬ (fbase.toNat - 16 ≤ a ∧ a < fbase.toNat) → c'.σ.mem[a]? = mA[a]?) →
    MemExtends mA c'.σ.mem

/-- **`blockC_eqne_front`** (model `blockC_div`).  From the dispatch outcome `cD` (parked
at the `jal value_equal` PC, `EqFrontData`), run `eqnePreBridge ≫ value_equal_spec_full ≫
veReturnBridge` to land the `VeReturn` that `blockC_eq`/`blockC_ne` consume, threaded
through the caller's `boolBoxPre` bundle.  Delivers a `VeReturn g fbase sret vl vr link
out0 mA cR'` for a config `cR'` reached from `cD`. -/
theorem blockC_eqne_front
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (fbase sret : BitVec 64) (vl vr : Value) (link jalPC : BitVec 64) (jImm : BitVec 21)
    (mA : Mem) (out0 : Array String) (cD : Config)
    (hData : EqFrontData g N φc fbase sret vl vr link jalPC jImm mA out0 cD) :
    ∃ (cR : Config), Steps cD cR ∧
      VeReturn g fbase sret vl vr link out0 mA cR := by
  -- === eqnePreBridge: jal value_equal → ve_pre (gpre = the dispatch snapshot) ===
  obtain ⟨cP, hStepsP, hx2P, hx9P, hframeP, hVePre⟩ :=
    eqnePreBridge (fun R => cD.σ.regs.get? R) N φc fbase sret vl vr mA out0
      jalPC link jImm hData.jalSite hData.hjalTgt hData.hlink hData.hlinkAl
      hData.hVeLoaded hData.hJT hData.hEE hData.hRegA hData.hRegB hData.hReprA hData.hReprB
      cD ⟨hData.hmemD, hData.hpc, hData.hx10, hData.hx11, hData.hx2, hData.hx9,
        (fun _ _ _ => rfl), hData.hout, hData.htick, hData.hG⟩
  -- === value_equal_spec_full: ve_pre → ve_str_post ===
  obtain ⟨cV, hStepsV, hVePost⟩ :=
    value_equal_spec_full (fun R => cP.σ.regs.get? R) (fbase + 0x40#64) (fbase + 0x20#64)
      link fbase N φc vl vr mA out0 cP hData.hφc hData.hN hVePre hx2P hData.hStrc hData.hMask
      hData.hraln4 hData.hstrwit
  -- === veReturnBridge: ve_str_post → VeReturn ===
  -- the eval-frame collapse of the value_equal-entry snapshot (= identity at cP):
  --   x1 → link (= g x1); every other NotWrittenVEStr reg survives the jal → cD → g.
  have hEvalCollapse : ∀ R : Register, NotWrittenVEStr R →
      (Register.x9 == R) = false → (Register.x19 == R) = false →
      (fun R => cP.σ.regs.get? R) R = g R := by
    intro R hR he9 he19
    by_cases hx1 : (Register.x1 == R) = true
    · -- R = x1: cP.x1 = link = g x1
      have hRx1 : R = Register.x1 := by
        rw [beq_iff_eq] at hx1; exact hx1.symm
      subst hRx1
      show cP.σ.regs.get? Register.x1 = g Register.x1
      rw [hData.hgx1]
      exact hVePre.2.2.2.2.2.2.2.2.1  -- ve_pre's `x1 = link`
    · have hx1ne : (Register.x1 == R) = false := by
        cases h : (Register.x1 == R) with
        | true => exact absurd h hx1
        | false => rfl
      show cP.σ.regs.get? R = g R
      rw [hframeP R hR hx1ne]
      exact hData.hsnapEval R hR hx1ne he9 he19
  have hMemExtV : MemExtends mA cV.σ.mem :=
    hData.hMemExtRet cV hVePost.2.2.2.2.2.2.2.2.1
  refine ⟨cV, (hStepsP.trans hStepsV), ?_⟩
  exact veReturnBridge (fun R => cP.σ.regs.get? R) g fbase sret vl vr link out0 mA cV
    hx9P hEvalCollapse hMemExtV hVePost

#print axioms blockC_eqne_front

/-! ## `EqResid` — the per-config front residual (model `DivResid`)

`EqResid` packages, for a `TwoSubReturn` config `c2` (frame base `sp-1088`), the whole
eq/ne front residual: the dispatch has run from `c2` to a config `cD` at the `jal
value_equal` PC (`link`/`jalPC`/`jImm` op-specific) with the `EqFrontData` transport
(operand reprs read back out of the reflected copy, `value_equal` caller obligations,
str-witness, frame collapse); the `φfm`/`φcm`/`φf'`/`φc'` sub-derivation maps + their
`PhiExtends` chain; and the shared post-`value_equal` `EqNeBoxPre` box bundle.  This is the
eq/ne analogue of `DivResid`'s post-dispatch operand + loaded-image data — the residual the
reseated `evalEqNeSim` threads exactly as `evalDivSim` threads `DivResid`. -/
def EqResid
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' st'' : Vsa.While.St)
    (sp r sret : BitVec 64) (v8 v9 v18 v19 w19 : BitVec 64)
    (vl vr : Value) (link jalPC : BitVec 64) (jImm : BitVec 21)
    (out0 : Array String) (m0 : Mem) (c2 : Config) : Prop :=
  ∃ (mA : Mem) (cD : Config) (φfm φcm φf' φc' : Addr → Nat),
    PhiExtends φf φfm st'.store.frames.size ∧
    PhiExtends φc φcm st'.store.closures.size ∧
    PhiExtends φfm φf' st''.store.frames.size ∧
    PhiExtends φcm φc' st''.store.closures.size ∧
    Steps c2 cD ∧
    EqFrontData g N φc (sp - 1088#64) sret vl vr link jalPC jImm mA out0 cD ∧
    EqNeBoxPre g N A SL φf' φc' st'' sp r sret v8 v9 v18 v19 w19 out0 m0 mA

/-- **`eqBlockC_bridge`** — build the `hblockC` obligation for the shared `blockC_eq`/
`blockC_ne` selector `blockCsel` from a `TwoSubReturn` config plus its `EqResid`, via
`blockC_eqne_front ≫ blockCsel`.  `blockCsel` is `blockC_eq` for eq (`resVal =
.bool (vl.equal vr)`, `link = 0x80003720`) / `blockC_ne` for ne.  The dispatch-run + box
transport is the `EqResid` residual; the `PhiExtends` chain rides through `blockCsel`. -/
theorem eqBlockC_bridge
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' st'' : Vsa.While.St)
    (sp r sret : BitVec 64) (v8 v9 v18 v19 w19 : BitVec 64)
    (vl vr : Value) (resVal : Value) (link jalPC : BitVec 64) (jImm : BitVec 21)
    (out0 : Array String) (m0 : Mem) (c2 : Config)
    (hSizeF : st'.store.frames.size = st''.store.frames.size)
    (hSizeC : st'.store.closures.size = st''.store.closures.size)
    (hOut0 : c2.σ.sailOutput = out0)
    (blockCsel : ∀ (φfa φca φfma φcma φf'a φc'a : Addr → Nat)
      (mEnt : Mem) (cR : Config),
      PhiExtends φfa φfma st'.store.frames.size → PhiExtends φca φcma st'.store.closures.size →
      PhiExtends φfma φf'a st''.store.frames.size → PhiExtends φcma φc'a st''.store.closures.size →
      VeReturn g (sp - 1088#64) sret vl vr link out0 mEnt cR →
      EqNeBoxPre g N A SL φf'a φc'a st'' sp r sret v8 v9 v18 v19 w19 out0 m0 mEnt →
      ∃ (mpre : Mem) (φfm' φcm' φfe φce : Addr → Nat) (cfin : Config),
        Steps cR cfin ∧
        PhiExtends φfa φfm' st'.store.frames.size ∧
        PhiExtends φca φcm' st'.store.closures.size ∧
        PhiExtends φfm' φfe st''.store.frames.size ∧
        PhiExtends φcm' φce st''.store.closures.size ∧
        PreEpilogueVD g N A SL φfe φce st'' resVal sp r sret v8 v9 v18 out0 m0 mpre cfin)
    (hResid : EqResid g N A SL φf φc st' st''
      sp r sret v8 v9 v18 v19 w19 vl vr link jalPC jImm out0 m0 c2) :
    ∃ (c3 : Config) (mpre : Mem) (φfe φce : Addr → Nat),
      Steps c2 c3 ∧
      PhiExtends φf φfe st''.store.frames.size ∧
      PhiExtends φc φce st''.store.closures.size ∧
      PreEpilogueVD g N A SL φfe φce st'' resVal sp r sret v8 v9 v18 c2.σ.sailOutput m0 mpre c3 := by
  obtain ⟨mA, cD, φfm, φcm, φf', φc', hpfm, hpcm, hpf', hpc', hStepsD, hFront, hBox⟩ := hResid
  -- front: dispatch-run c2 → cD, then blockC_eqne_front → VeReturn at cR
  obtain ⟨cR, hStepsFront, hVeReturn⟩ :=
    blockC_eqne_front g N φc (sp - 1088#64) sret vl vr link jalPC jImm mA out0 cD hFront
  -- box: blockCsel VeReturn + EqNeBoxPre → PreEpilogueVD
  obtain ⟨mpre, φfm', φcm', φfe, φce, cfin, hStepsBox, hp1, hp2, hp3, hp4, hPre⟩ :=
    blockCsel φf φc φfm φcm φf' φc' mA cR hpfm hpcm hpf' hpc' hVeReturn hBox
  refine ⟨cfin, mpre, φfe, φce, (hStepsD.trans hStepsFront).trans hStepsBox, ?_, ?_, ?_⟩
  · exact (hSizeF ▸ hp1).trans hp3
  · exact (hSizeC ▸ hp2).trans hp4
  · rw [hOut0]; exact hPre

#print axioms eqBlockC_bridge

/-! ## Reseated `evalEqSim` / `evalNeSim` (div-parity)

The div-parity reseat of the eq/ne value cases: the precondition carries
`(∀ c2, TwoSubReturn … → EqResid … c2)` (the front residual, exactly as `evalDivSim`
carries `∀ c', TwoSubReturn → DivResid`), and the body discharges the shared
`evalEqSim`/`evalNeSim` core's `hblockC` obligation via `eqBlockC_bridge` (⇒
`blockC_eqne_front ≫ blockC_eq/blockC_ne`).  These are the thin op wrappers; everything
else (the two IHs, `blockB`/`blockD`, φ/store threading) is the shared row core. -/

/-- **`evalEqSimD`** — the div-parity `EvalE.binary .eq` recursive case: the `hblockC`
bridge residual replaced by an `EqResid` precondition (front closed to `blockC_eq`). -/
theorem evalEqSimD
    (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl vr : Value)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 w19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hIHl : EvalIH st d env el st' vl) (hIHr : EvalIH st' d env er st'' vr)
    (hSizeF : st'.store.frames.size = st''.store.frames.size)
    (hSizeC : st'.store.closures.size = st''.store.closures.size)
    (hVlSurv : ∀ (φ : Addr → Nat) (mm mm' : Mem),
      ValueRepr mm N φ (sp.toNat - 968) vl →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → mm[k]? = mm'[k]?) →
      ValueRepr mm' N φ (sp.toNat - 968) vl)
    (hResid : ∀ c2 : Vsa.Machine.Config,
      TwoSubReturn gpre N A SL φf φc st' st'' vl vr sp r sret v8 v9 v18 m0 c2 →
      EqResid g N A SL φf φc st' st'' sp r sret v8 v9 v18 v19 w19 vl vr
        (0x80003720#64) (0x8000371c#64) (0x1ff140#21) c2.σ.sailOutput m0 c2) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .eq el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        (∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ bb, ment[a]? = some bb)) ∧
        MemExtends m0 ment)
      (EvalExitD g N A SL φf φc st'' (.bool (vl.equal vr)) sp r sret m0) :=
  evalEqSim gouter gpre g N A SL φf φc st st' st'' d env el er vl vr
    sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0
    hIHl hIHr hSizeF hSizeC hVlSurv
    (fun c2 hTS _hOut2 =>
      eqBlockC_bridge g N A SL φf φc st' st'' sp r sret v8 v9 v18 v19 w19 vl vr
        (.bool (vl.equal vr)) (0x80003720#64) (0x8000371c#64) (0x1ff140#21)
        c2.σ.sailOutput m0 c2 hSizeF hSizeC rfl
        (fun φfa φca φfma φcma φf'a φc'a mEnt cR hp1 hp2 hp3 hp4 hVe hBox =>
          blockC_eq g N A SL φfa φca φfma φcma φf'a φc'a st' st''
            sp r sret v8 v9 v18 v19 w19 vl vr c2.σ.sailOutput m0 mEnt cR hp1 hp2 hp3 hp4 hVe hBox)
        (hResid c2 hTS))

/-- **`evalNeSimD`** — the div-parity `EvalE.binary .ne` recursive case (ne clone). -/
theorem evalNeSimD
    (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl vr : Value)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 w19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hIHl : EvalIH st d env el st' vl) (hIHr : EvalIH st' d env er st'' vr)
    (hSizeF : st'.store.frames.size = st''.store.frames.size)
    (hSizeC : st'.store.closures.size = st''.store.closures.size)
    (hVlSurv : ∀ (φ : Addr → Nat) (mm mm' : Mem),
      ValueRepr mm N φ (sp.toNat - 968) vl →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → mm[k]? = mm'[k]?) →
      ValueRepr mm' N φ (sp.toNat - 968) vl)
    (hResid : ∀ c2 : Vsa.Machine.Config,
      TwoSubReturn gpre N A SL φf φc st' st'' vl vr sp r sret v8 v9 v18 m0 c2 →
      EqResid g N A SL φf φc st' st'' sp r sret v8 v9 v18 v19 w19 vl vr
        (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21) c2.σ.sailOutput m0 c2) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .ne el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        (∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ bb, ment[a]? = some bb)) ∧
        MemExtends m0 ment)
      (EvalExitD g N A SL φf φc st'' (.bool (!(vl.equal vr))) sp r sret m0) :=
  evalNeSim gouter gpre g N A SL φf φc st st' st'' d env el er vl vr
    sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0
    hIHl hIHr hSizeF hSizeC hVlSurv
    (fun c2 hTS _hOut2 =>
      eqBlockC_bridge g N A SL φf φc st' st'' sp r sret v8 v9 v18 v19 w19 vl vr
        (.bool (!(vl.equal vr))) (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21)
        c2.σ.sailOutput m0 c2 hSizeF hSizeC rfl
        (fun φfa φca φfma φcma φf'a φc'a mEnt cR hp1 hp2 hp3 hp4 hVe hBox =>
          blockC_ne g N A SL φfa φca φfma φcma φf'a φc'a st' st''
            sp r sret v8 v9 v18 v19 w19 vl vr c2.σ.sailOutput m0 mEnt cR hp1 hp2 hp3 hp4 hVe hBox)
        (hResid c2 hTS))

#print axioms evalEqSimD
#print axioms evalNeSimD

end Vsa.Sim
