import Vsa.Sim.rows.NativeArmSplice
import Vsa.Sim.EvalCallNative2

/-!
# `nativeBodyAssert` — the assertOk body leg of the native splice (wave 41)

Abstraction (3) of the observation `native-call-segentry-wrapper`, smallest
native first: the `native_assert` fn-body Triple in the `nativeArmSplice`
boundary shape — `NativeBodyPre(.assert) ∧ NativeAssertExtra → NativeBodyPost`
with the spec state UNCHANGED (`Call.assertOk` returns `st` and `.null`).

The internal run is the LANDED `nativeAssertInternal`
(`Vsa/Sim/EvalCallNative2.lean`, `naEntry → naExit` over the 33-site battery,
composing `value_truthy_spec` ≫ `value_null_spec`) — except that `naExit`
lacks an ABI-frame clause (observation `naexit-lacks-abi-frame-clause`), so
this file consumes the ABI-FRAMED variant as the ONE named residual
`NativeAssertInternalAbi` and lands everything else:

* the `naEntry` construction from the splice boundary (`NativeBodyPre` fields
  + the assert-specific config facts `NativeAssertExtra` + the geometry
  premises), with the internal ghost frame instantiated at the ENTRY CONFIG'S
  OWN READS (`g_na := fun R => c.σ.regs.get? R` — `naEntry`'s tie clause
  becomes `rfl`, and the framed exit clause hands back exactly the entry
  values, which `NativeBodyPre.frame` ties to the arm ghost `g`);
* the `naExit → NativeBodyPost` rebuild: `Eval_exprLoaded` transport
  (`loaded_eval_expr_agreeP` through the frame/sret carve-outs), `StoreRepr`
  via `NativeBodyPre.storeSurv` (the whole native footprint is stack-confined),
  `OutRepr` (no output), the `s7` spill-image survival, and the `m0` memFrame
  composition.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Scaffold

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The assert-specific config facts (the `Extra` of the splice's `Mid`) -/

/-- **The assert-specific config-dependent facts** riding in the splice's
`Mid` beside `NativeBodyPre`: the three callee code regions loaded, and the
`args[0]` payload pointer's window avoiding `native_assert`'s frame+buffer
window `[sp-80, sp+40)` (the `naEntry.hpayDisj` clause — payload strings live
in the arena). -/
structure NativeAssertExtra (argsBase spv : BitVec 64) (c : Config) : Prop where
  loadedNA : Vsa.Sim.Code.Native_assertLoaded c.σ.mem
  loadedVT : Vsa.Sim.Code.Value_truthyLoaded c.σ.mem
  loadedVN : Vsa.Sim.Code.Value_nullLoaded c.σ.mem
  payDisj : ∀ (p : Nat) (s : String),
    read64 c.σ.mem (argsBase.toNat + 8) = some p →
    ∀ k, k ≤ s.length → (p + k < spv.toNat - 80 ∨ spv.toNat + 40 ≤ p + k)

/-! ## §2. The named residual (observation `naexit-lacks-abi-frame-clause`) -/

/-- **NAMED RESIDUAL — the ABI-framed `native_assert` internal run.**  The
landed `nativeAssertInternal` (`EvalCallNative2.lean`) proves exactly this
Triple MINUS the exit frame conjunct: its `naExit` pins only `x2` among the
callee-saved registers, although the machine restores every one (the epilogue
reloads `ra/s0/s1/s2` from the frame spills; no other callee-saved is written)
and the landed proof tracks all the values site-by-site.  Supplied by a
one-clause `naExit` amendment + threading the already-tracked register facts
(coordinator: `EvalCallNative2.lean` is outside wave-41 file ownership) — see
the observation for the exact plan.  `g_na` is the internal run's OWN ghost
frame (its tie is `naEntry`'s existing final clause); the exit conjunct
re-establishes it. -/
def NativeAssertInternalAbi (N : NativeAddrs) (φc : Addr → Nat) : Prop :=
  ∀ (g_na : (R : Register) → Option (RegisterType R)) (v : Value)
    (fsp sret retAddr argsBase argc interp scratch s0v s1v s2v : BitVec 64)
    (m0 : Mem) (out0 : Array String),
    Triple
      (naEntry g_na N φc v fsp sret retAddr argsBase argc interp scratch
        s0v s1v s2v m0 out0)
      (fun c => naExit g_na N φc fsp sret retAddr m0 out0 c ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g_na R))

/-! ## §3. The body provider -/

/-- **The assertOk body leg** — `Triple (NativeBodyPre ∧ NativeAssertExtra)
NativeBodyPost` at the UNCHANGED spec state `st`.  Geometry premises (all
`StackOK`/Layout-level facts about the GHOSTS, supplied by the arm):

* `hRG` — `native_assert`'s own region facts (`NativeAssertRegion spv sret`);
* `hargs*` — the arg-slot window (disjoint from the native frame, in RAM, off
  the HTIF window, 8-aligned);
* `hframeStack`/`hsretStack` — the native frame+buffer window and the sret
  window sit INSIDE the stack region (so `storeSurv`/`memFrame` compose);
* `hsretSlot` — the sret window avoids the `s7` spill slot `[sp+1016,sp+1024)`;
* `hcodeStack` — the stack region avoids `eval_expr`'s code region (so the
  join's decode pins survive the body). -/
theorem nativeBodyAssert
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (vs : List Value) (v mv : Value) (fentry : Nat)
    (spv s7v sret interp argsBase scratch s0v s1v s2v : BitVec 64) (m0 : Mem)
    (hvs : vs = [v] ∨ vs = [v, mv])
    (htruthy : v.truthy = true)
    (hfe : fentry = 0x80002df4)
    (hg8 : g Register.x8 = some s0v)
    (hg9 : g Register.x9 = some s1v)
    (hg18 : g Register.x18 = some s2v)
    (hRG : NativeAssertRegion spv sret)
    (hargsFrame : argsBase.toNat + 24 ≤ spv.toNat - 80 ∨ spv.toNat + 40 ≤ argsBase.toNat)
    (hargsHi : argsBase.toNat + 24 ≤ 0x100000000)
    (hargsWin : tohostAddr + 8 ≤ argsBase.toNat)
    (hargsAlign : argsBase.toNat % 8 = 0)
    (hframeStack : SL.lo ≤ spv.toNat - 80 ∧ spv.toNat + 40 ≤ SL.hi)
    (hsretStack : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi)
    (hsretSlot : sret.toNat + 24 ≤ spv.toNat + 1016 ∨ spv.toNat + 1024 ≤ sret.toNat)
    (hcodeStack : ∀ a : Nat, 0x80003164 ≤ a → a < 0x80003fe0 →
      ¬ (SL.lo ≤ a ∧ a < SL.hi))
    (hInternal : NativeAssertInternalAbi N φc) :
    Triple
      (fun c => NativeBodyPre g N A SL φf φc st vs fentry
          spv s7v sret interp argsBase scratch m0 c ∧
        NativeAssertExtra argsBase spv c)
      (NativeBodyPost g N A SL φf φc st spv s7v m0) := by
  intro c hc
  obtain ⟨hpre, hextra⟩ := hc
  obtain ⟨vm, hvm⟩ := hpre.minstret
  have hlen1 : 0 < vs.length := by rcases hvs with rfl | rfl <;> simp
  -- the internal run's ghost frame := the entry config's own reads
  have hentry : naEntry (fun R => c.σ.regs.get? R) N φc v spv sret (0x800039f8#64)
      argsBase (BitVec.ofNat 64 vs.length) interp scratch s0v s1v s2v
      c.σ.mem c.σ.sailOutput c := by
    refine ⟨hpre.good, hextra.loadedNA, hextra.loadedVT, hextra.loadedVN, rfl,
      ?_, hpre.a0, hpre.a1, hpre.a2, hpre.a3, hpre.a4, hpre.ra, hpre.sp,
      ?_, ?_, ?_, ⟨vm, hvm⟩, hpre.tick,
      ?_, htruthy, ?_, hargsFrame, hargsHi, hargsWin, hargsAlign,
      ?_, hextra.payDisj, hRG, by decide, rfl, fun R _ => rfl⟩
    · -- PC at native_assert's entry
      have := hpre.pc
      rw [hfe] at this
      exact this
    · exact (hpre.frame Register.x8 (by decide) (by decide)).trans hg8
    · exact (hpre.frame Register.x9 (by decide) (by decide)).trans hg9
    · exact (hpre.frame Register.x18 (by decide) (by decide)).trans hg18
    · -- args[0] = v at the argsBase slot
      have h := hpre.args 0 hlen1
      rcases hvs with rfl | rfl <;> exact h
    · -- argc ∈ {1, 2}
      rcases hvs with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · -- the 24 arg-slot bytes are materialised
      intro j hj
      exact hpre.argsBytes j (by omega)
  -- run the (framed) internal body
  obtain ⟨c', hsteps, hexit, hframe'⟩ :=
    hInternal (fun R => c.σ.regs.get? R) v spv sret (0x800039f8#64)
      argsBase (BitVec.ofNat 64 vs.length) interp scratch s0v s1v s2v
      c.σ.mem c.σ.sailOutput c hentry
  obtain ⟨hG', htick', hpc', _hnull, hout', hmemF', ⟨w', hw'⟩, _hsp'⟩ := hexit
  have hfsp80 : 80 ≤ spv.toNat := by have := hRG.fsp_lo; omega
  -- exit memory agrees with the entry memory outside frame ∪ sret
  -- (both windows sit inside the stack region)
  refine ⟨c', hsteps, ?_⟩
  refine
    { good := hG'
      tick := htick'
      pc := ?_
      minstret := ⟨w', hw'⟩
      loaded := ?_
      store := ?_
      out := ?_
      frame := ?_
      s7slot := ?_
      memFrame := ?_ }
  · -- PC at the return link (the aligned ret target is the link itself)
    have := hpc'
    rwa [show BitVec.update ((0x800039f8#64 : BitVec 64)
        + sign_extend (m := 64) (0x000#12)) 0 0#1 = (0x800039f8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  · -- Eval_exprLoaded survives: the code region is off the stack, hence off
    -- the frame/sret carve-outs
    refine loaded_eval_expr_agreeP c.σ.mem c'.σ.mem (fun a ha => ?_) hpre.loaded
    have hns := hcodeStack a ha.1 ha.2
    exact (hmemF' a (by omega) (by omega)).symm
  · -- StoreRepr: the native footprint is stack-confined; storeSurv absorbs it
    refine hpre.storeSurv c'.σ.mem (fun k hk1 _hk2 => ?_)
    exact (hmemF' k (by omega) (by omega)).symm
  · -- OutRepr: no output on the assert path
    show Vsa.Machine.output c'.σ = st.out
    have hout2 : Vsa.Machine.output c'.σ = Vsa.Machine.output c.σ := by
      unfold Vsa.Machine.output; rw [hout']
    exact hout2.trans hpre.out
  · -- callee-saved (except s7) back to the arm ghost: the framed exit hands
    -- back the ENTRY reads, which NativeBodyPre.frame ties to g
    intro R hR hne
    exact (hframe' R hR).trans (hpre.frame R hR hne)
  · -- the s7 spill image survives (above the frame window, off the sret window)
    intro i hi
    have := hmemF' (spv.toNat + 1016 + i) (by omega) (by omega)
    rw [this]
    exact hpre.s7slot i hi
  · -- memory outside stack ∪ arena: exit = entry = m0
    intro a ha hA
    have hout1 : c'.σ.mem[a]? = c.σ.mem[a]? := by
      refine hmemF' a (by omega) (by omega)
    rw [hout1]
    exact hpre.memFrame a ha hA

#print axioms nativeBodyAssert

/-! ## §4. The assertOk contract, assembled

`NativeAssertOkSpec` from the splice + this body: the ONLY remaining legs are
the dispatch (`Triple CallEntryP (NativeBodyPre ∧ NativeAssertExtra)` — machine
body in `rows/NativeArmDispatch.lean`, its `SegEntry`→ABI geometry with the M6
caller, exactly the closure `hDispatchStage` residual class) and the
`NativeAssertInternalAbi` frame residual (§2). -/
theorem nativeAssertOkSpec_of_dispatch
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem)
    (vs : List Value) (v mv : Value) (fentry : Nat)
    (spv s7v sret interp argsBase scratch s0v s1v s2v : BitVec 64)
    (hvs : vs = [v] ∨ vs = [v, mv])
    (htruthy : v.truthy = true)
    (hfe : fentry = 0x80002df4)
    (hgsp : g Register.x2 = some spv)
    (hgs7 : g Register.x23 = some s7v)
    (hg8 : g Register.x8 = some s0v)
    (hg9 : g Register.x9 = some s1v)
    (hg18 : g Register.x18 = some s2v)
    (hslotLo : 0x80000000 ≤ spv.toNat + 1016)
    (hslotHi : spv.toNat + 1024 ≤ 0x100000000)
    (hslotHtif : spv.toNat + 1024 ≤ tohostAddr ∨ tohostAddr + 8 ≤ spv.toNat + 1016)
    (hslotAlign : (spv.toNat + 1016) % 8 = 0)
    (hRG : NativeAssertRegion spv sret)
    (hargsFrame : argsBase.toNat + 24 ≤ spv.toNat - 80 ∨ spv.toNat + 40 ≤ argsBase.toNat)
    (hargsHi : argsBase.toNat + 24 ≤ 0x100000000)
    (hargsWin : tohostAddr + 8 ≤ argsBase.toNat)
    (hargsAlign : argsBase.toNat % 8 = 0)
    (hframeStack : SL.lo ≤ spv.toNat - 80 ∧ spv.toNat + 40 ≤ SL.hi)
    (hsretStack : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi)
    (hsretSlot : sret.toNat + 24 ≤ spv.toNat + 1016 ∨ spv.toNat + 1024 ≤ sret.toNat)
    (hcodeStack : ∀ a : Nat, 0x80003164 ≤ a → a < 0x80003fe0 →
      ¬ (SL.lo ≤ a ∧ a < SL.hi))
    (hInternal : NativeAssertInternalAbi N φc)
    (hDispatch : Triple (CallEntryP g N A SL φf φc st d dLeft aLeft m0)
      (fun c => NativeBodyPre g N A SL φf φc st vs fentry
          spv s7v sret interp argsBase scratch m0 c ∧
        NativeAssertExtra argsBase spv c)) :
    NativeAssertOkSpec g N A SL φf φc st d dLeft aLeft m0 :=
  nativeAssertOkSpec_of_splice g N A SL φf φc st d dLeft aLeft m0 spv s7v _
    hgsp hgs7 hslotLo hslotHi hslotHtif hslotAlign hDispatch
    (nativeBodyAssert g N A SL φf φc st vs v mv fentry
      spv s7v sret interp argsBase scratch s0v s1v s2v m0
      hvs htruthy hfe hg8 hg9 hg18 hRG hargsFrame hargsHi hargsWin hargsAlign
      hframeStack hsretStack hsretSlot hcodeStack hInternal)

#print axioms nativeAssertOkSpec_of_dispatch

end Vsa.Sim
