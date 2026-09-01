import Vsa.Sim.EvalCallNative
import Vsa.Sim.EvalCallPrint
import Vsa.Sim.NativeWrapperSites
import Vsa.Sim.rows.NativeAddrResolve
import Vsa.Sim.StepFrameOut
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.EnvGetSpec
import Vsa.Sim.PinW

/-!
# `nativeArmSplice` — the native dispatch/join wrapper, factored ONCE (wave 41)

Task `#26 nativeArmSplice`, abstraction (1) of the observation
`native-call-segentry-wrapper`: the native analogue of the closure
`callClosureSim` decomposition.  The three native RemainingWork residuals
(`NativeAssertOkSpec` / `NativePrintSpec` / `NativePrintlnSpec`) are FULL
`Triple (CallEntryP @callDispatchPC) (CallExitP @callJoinPC)` contracts; this
file factors their SHARED route

    CallEntryP ─(dispatch beq-TAKEN + arm marshal + jalr a6)→ NativeBodyPre
              ─(the native fn body)→ NativeBodyPost
              ─(ld s7,1016(sp) ; j callJoinPC)→ CallExitP

into ONE splice (`nativeArmSplice`), with the two boundary predicates as
named-field structures (CLAUDE.md R6) and the JOIN leg **machine-discharged
here** (`nativeJoin` — the two `_nw` sites + the whole `SegExit` rebuild,
including the `s7` ghost-frame restore off the `EntryImage`-pinned spill slot).
Each native contract then becomes an INSTANTIATION: supply the dispatch leg and
its own body Triple; the join is free.

## The boundary design

* `NativeBodyPre` — parked at the native's entry (`N.addr f`), the arm ABI
  marshalled (`a0=sret, a1=interp, a2=argc, a3=argsBase, a4=scratch,
  ra=0x800039f8` — the CORRECTED map, `EvalCallNative3.lean`), the whole spec
  store still represented, the arg vector `vs` materialised at `argsBase`
  (24-byte slots), and the caller's `s7` spill image intact at `sp+1016` (the
  `entrySpillImage callDispatchPC = some (1016, 23)` slot).  The ghost frame
  ties every callee-saved EXCEPT the reseated `s7 = x23` (`mv s7,a1` at
  `0x80003278`).
* `NativeBodyPost` — parked at the return link `0x800039f8`, the spec
  post-state `st'` represented (store unchanged, output grown for
  print/println), callee-saved-except-`s7` restored, the `s7` slot bytes still
  intact.  `nativeJoin` turns this into `CallExitP` — the `ld s7,1016(sp)`
  readback re-establishes the FULL ghost frame (`sext_reassemble`), and
  `stackScratchTop callJoinPC = none` keeps `SegExit.stackWin` vacuous.

The dispatch leg (`Triple CallEntryP Mid`) is `Mid`-abstract in the splice: the
supplier owes `NativeBodyPre` plus whatever per-native geometry its body needs
(the closure-model parallel: `callClosureEntrySplice`'s `hDispatchStage` is the
same named residual class).  `rows/NativeArmDispatch.lean` provides its machine
body.

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

/-! ## §1. The two boundary predicates (named-field structures) -/

/-- **The native body entry** — the machine parked at the native's entry
`fentry` (`= N.addr f`) immediately after the `jalr a6`, with the arm ABI
marshalled and the spec state fully represented.  Ghost parameters: `spv` =
`eval_expr`'s sp (the natives build their own frames below it), `s7v` = the
ghost frame's `s7 = g x23` (its spill image at `sp+1016` must survive to the
join restore), `sret`/`interp`/`argsBase`/`scratch` = the marshalled ABI
registers, `vs` = the materialised argument vector. -/
structure NativeBodyPre
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (vs : List Value) (fentry : Nat)
    (spv s7v sret interp argsBase scratch : BitVec 64) (m0 : Mem)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  /-- PC at the native's entry (the resolved `jalr a6` target). -/
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 fentry)
  /-- The return link into the arm (`ld s7 ; j callJoinPC`). -/
  ra : c.σ.regs.get? Register.x1 = some (0x800039f8#64 : BitVec 64)
  /-- `sp` — `eval_expr`'s stack pointer (the arm does not lower it). -/
  sp : c.σ.regs.get? Register.x2 = some spv
  /-- `a0` — the CALL sret buffer. -/
  a0 : c.σ.regs.get? Register.x10 = some sret
  /-- `a1` — the interp pointer. -/
  a1 : c.σ.regs.get? Register.x11 = some interp
  /-- `a2` — argc (`= vs.length`). -/
  a2 : c.σ.regs.get? Register.x12 = some (BitVec.ofNat 64 vs.length)
  /-- `a3` — the arg Value-array base (`sp+240`). -/
  a3 : c.σ.regs.get? Register.x13 = some argsBase
  /-- `a4` — the scratch word (`e->line`; the natives treat it as noise). -/
  a4 : c.σ.regs.get? Register.x14 = some scratch
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  /-- `eval_expr`'s code region (the join `ld`/`j` decode from it). -/
  loaded : Vsa.Sim.Code.Eval_exprLoaded c.σ.mem
  store : StoreRepr c.σ.mem N A φf φc st.store
  /-- `StoreRepr` survival under stack-and-HTIF-confined memory changes (the
  natives write only their frames/buffers — all stack — and, for
  print/println, the HTIF `tohost` window). -/
  storeSurv : ∀ m' : Mem,
    (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
      ¬ (tohostAddr ≤ k ∧ k < tohostAddr + 16) → c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  out : OutRepr c.σ st
  /-- Writes so far (the dispatch's fv restaging) are stack-confined. -/
  memFrame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    c.σ.mem[a]? = m0[a]?
  /-- The arg vector, one 24-byte `ValueRepr` slot per argument. -/
  args : ∀ i, (hi : i < vs.length) →
    ValueRepr c.σ.mem N φc (argsBase.toNat + 24 * i) vs[i]
  /-- Every arg-slot byte is materialised (the natives copy raw 24-byte
  windows before inspecting them). -/
  argsBytes : ∀ j : Nat, j < 24 * vs.length →
    ∃ b, c.σ.mem[argsBase.toNat + j]? = some b
  /-- The ghost frame on every callee-saved EXCEPT the reseated `s7 = x23`. -/
  frame : ∀ R : Register, AbiPreservedNoise R → R ≠ Register.x23 →
    c.σ.regs.get? R = g R
  /-- The caller's `s7` spill image at `sp+1016` (`EntryImage callDispatchPC`,
  untouched by the dispatch's `sp+120/128/136` restaging). -/
  s7slot : ∀ i : Nat, i < 8 →
    c.σ.mem[spv.toNat + 1016 + i]? = some (s7v.extractLsb' (8 * i) 8)

/-- **The native body exit** — the machine parked at the arm's return link
`0x800039f8` after the native returned, with the spec POST-state `st'`
represented (`st' = st` for assert; output-grown for print/println), the
callee-saved frame restored except `s7` (about to be reloaded), and the `s7`
spill image still intact. -/
structure NativeBodyPost
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : SpecSt) (spv s7v : BitVec 64) (m0 : Mem)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  /-- PC at the arm's return link (`ld s7,1016(sp)`). -/
  pc : c.σ.regs.get? Register.PC = some (0x800039f8#64 : BitVec 64)
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  /-- `eval_expr`'s code region survived the native body. -/
  loaded : Vsa.Sim.Code.Eval_exprLoaded c.σ.mem
  store : StoreRepr c.σ.mem N A φf φc st'.store
  out : OutRepr c.σ st'
  /-- The ghost frame restored on every callee-saved EXCEPT `s7 = x23`. -/
  frame : ∀ R : Register, AbiPreservedNoise R → R ≠ Register.x23 →
    c.σ.regs.get? R = g R
  /-- The `s7` spill image survived the native body (its frame/buffers are
  disjoint from `[sp+1016, sp+1024)`). -/
  s7slot : ∀ i : Nat, i < 8 →
    c.σ.mem[spv.toNat + 1016 + i]? = some (s7v.extractLsb' (8 * i) 8)
  /-- Memory outside stack ∪ arena is framed to the dispatch entry's `m0`. -/
  memFrame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    c.σ.mem[a]? = m0[a]?

/-! ## §2. The join leg, machine-discharged

`0x800039f8: ld s7,1016(sp) ; 0x800039fc: j 0x800033ec` — two `_nw` sites.
The `ld` reassembles the ghost `s7v` from its LE spill bytes
(`sext_reassemble`), re-establishing the FULL `SegExit.frame`;
`stackScratchTop callJoinPC = none` keeps `stackWin` vacuous. -/

/-- The `sp+1016` slot address in the `ld`'s `sext` form. -/
private theorem nj_addr (spv : BitVec 64) (hhi : spv.toNat + 1024 ≤ 0x100000000) :
    (spv + sign_extend (m := 64) (0x3f8#12)).toNat = spv.toNat + 1016 := by
  rw [show (sign_extend (m := 64) (0x3f8#12) : BitVec 64) = 1016#64 from by
      apply BitVec.eq_of_toNat_eq; decide,
    BitVec.toNat_add]
  rw [show (1016#64 : BitVec 64).toNat = 1016 from by decide]
  rw [Nat.mod_eq_of_lt (by have := spv.isLt; omega)]

/-- **`nativeJoin`** — the shared return leg: from `NativeBodyPost` at
`0x800039f8` to `CallExitP` at `callJoinPC`, for ANY `nf`/`nc` (the φ-maps are
unchanged, `PhiExtends.refl`).  Premises: the ghost `sp`/`s7` values and the
`s7` slot's RAM-window geometry (inside RAM, off the HTIF window, 8-aligned —
`StackOK`-level facts the arm carries). -/
theorem nativeJoin
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st' : SpecSt) (spv s7v : BitVec 64) (m0 : Mem)
    (hgsp : g Register.x2 = some spv)
    (hgs7 : g Register.x23 = some s7v)
    (hslotLo : 0x80000000 ≤ spv.toNat + 1016)
    (hslotHi : spv.toNat + 1024 ≤ 0x100000000)
    (hslotHtif : spv.toNat + 1024 ≤ tohostAddr ∨ tohostAddr + 8 ≤ spv.toNat + 1016)
    (hslotAlign : (spv.toNat + 1016) % 8 = 0) :
    Triple
      (NativeBodyPost g N A SL φf φc st' spv s7v m0)
      (CallExitP g N A SL φf φc nf nc st' m0) := by
  intro c hc
  obtain ⟨vm, hvm⟩ := hc.minstret
  have haddr : (spv + sign_extend (m := 64) (0x3f8#12)).toNat = spv.toNat + 1016 :=
    nj_addr spv hslotHi
  have hx2 : c.σ.regs.get? Register.x2 = some spv :=
    (hc.frame Register.x2 (by decide) (by decide)).trans hgsp
  -- the 8 spill bytes at the ld's address form
  have h0 : c.σ.mem[(spv + sign_extend (m := 64) (0x3f8#12)).toNat]?
      = some (s7v.extractLsb' 0 8) := by rw [haddr]; exact hc.s7slot 0 (by omega)
  have h1 : c.σ.mem[(spv + sign_extend (m := 64) (0x3f8#12)).toNat + 1]?
      = some (s7v.extractLsb' 8 8) := by rw [haddr]; exact hc.s7slot 1 (by omega)
  have h2 : c.σ.mem[(spv + sign_extend (m := 64) (0x3f8#12)).toNat + 2]?
      = some (s7v.extractLsb' 16 8) := by rw [haddr]; exact hc.s7slot 2 (by omega)
  have h3 : c.σ.mem[(spv + sign_extend (m := 64) (0x3f8#12)).toNat + 3]?
      = some (s7v.extractLsb' 24 8) := by rw [haddr]; exact hc.s7slot 3 (by omega)
  have h4 : c.σ.mem[(spv + sign_extend (m := 64) (0x3f8#12)).toNat + 4]?
      = some (s7v.extractLsb' 32 8) := by rw [haddr]; exact hc.s7slot 4 (by omega)
  have h5 : c.σ.mem[(spv + sign_extend (m := 64) (0x3f8#12)).toNat + 5]?
      = some (s7v.extractLsb' 40 8) := by rw [haddr]; exact hc.s7slot 5 (by omega)
  have h6 : c.σ.mem[(spv + sign_extend (m := 64) (0x3f8#12)).toNat + 6]?
      = some (s7v.extractLsb' 48 8) := by rw [haddr]; exact hc.s7slot 6 (by omega)
  have h7 : c.σ.mem[(spv + sign_extend (m := 64) (0x3f8#12)).toNat + 7]?
      = some (s7v.extractLsb' 56 8) := by rw [haddr]; exact hc.s7slot 7 (by omega)
  -- step 1: 0x800039f8 `ld s7,1016(sp)`
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800039f8_nw c.σ c.tick c.steps (0x800039f8#64) vm spv
      (s7v.extractLsb' 0 8) (s7v.extractLsb' 8 8) (s7v.extractLsb' 16 8)
      (s7v.extractLsb' 24 8) (s7v.extractLsb' 32 8) (s7v.extractLsb' 40 8)
      (s7v.extractLsb' 48 8) (s7v.extractLsb' 56 8)
      hc.good hc.pc hvm hx2 hc.loaded rfl
      (by rw [haddr]; omega) (by rw [haddr]; omega)
      (by rw [haddr]; omega) (by rw [haddr]; exact hslotAlign)
      h0 h1 h2 h3 h4 h5 h6 h7 hc.tick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  -- the ld's value reassembles to the ghost s7v
  have hx23v : (sign_extend (m := 64)
      ((((((((s7v.extractLsb' 56 8).append (s7v.extractLsb' 48 8)).append
        (s7v.extractLsb' 40 8)).append (s7v.extractLsb' 32 8)).append
        (s7v.extractLsb' 24 8)).append (s7v.extractLsb' 16 8)).append
        (s7v.extractLsb' 8 8)).append (s7v.extractLsb' 0 8) : BitVec (8 * 8))
      : BitVec 64) = s7v :=
    sext_reassemble s7v _ _ _ _ _ _ _ _
      (by rw [sdData_val_id]) (by rw [sdData_val_id]) (by rw [sdData_val_id])
      (by rw [sdData_val_id]) (by rw [sdData_val_id]) (by rw [sdData_val_id])
      (by rw [sdData_val_id]) (by rw [sdData_val_id])
  have hx23_1 : σ1.regs.get? Register.x23 = some s7v := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hx23v] at this
  have hpc1 : σ1.regs.get? Register.PC = some (0x800039fc#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800039f8#64) 4 = (0x800039fc#64 : BitVec 64) from by decide]
      at this
  obtain ⟨vm1, hvm1⟩ := obs_alu_minstret hobs1
  have hload1 : Vsa.Sim.Code.Eval_exprLoaded σ1.mem := by rw [hmem1]; exact hc.loaded
  -- step 2: 0x800039fc `j 0x800033ec`
  have htgtv : ((0x800039fc#64 : BitVec 64) + sign_extend (m := 64) (0x1ff9f0#21))
      = (0x800033ec#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800039fc_nw σ1 i1 (c.steps + 1) (0x800039fc#64) vm1
      hG1 hpc1 hvm1 hload1 rfl (by rw [htgtv]; decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
  -- frame + output threading across the two steps
  have sfo1 := StepFrameOut.of_alu hobs1
  have sfo2 := StepFrameOut.of_jr hobs2
  have hmemEq : σ2.mem = c.σ.mem := hmem2.trans hmem1
  -- the exit config
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, Steps.trans (.single hstep1) (.single hstep2), ?_⟩
  have houtEq : σ2.sailOutput = c.σ.sailOutput := sfo2.out.trans sfo1.out
  refine
    { good := hG2
      tick := hi2
      pc := ?_
      store := ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, by
        rw [hmemEq]; exact hc.store⟩
      out := ?_
      frame := ?_
      memFrame := fun a ha hA => by rw [hmemEq]; exact hc.memFrame a ha hA
      stackWin := ?_ }
  · -- PC at callJoinPC
    have := obs_jump_x0_pc_eg hobs2
    rw [htgtv] at this
    exact this
  · -- OutRepr σ2 st': sailOutput preserved
    show Vsa.Machine.output σ2 = st'.out
    have : Vsa.Machine.output σ2 = Vsa.Machine.output c.σ := by
      unfold Vsa.Machine.output; rw [houtEq]
    exact this.trans hc.out
  · -- the ghost frame, INCLUDING the reloaded s7
    intro R hR
    by_cases h23 : R = Register.x23
    · subst h23
      have hpres : σ2.regs.get? Register.x23 = σ1.regs.get? Register.x23 :=
        sfo2.frame Register.x23 (by decide)
      rw [hpres, hx23_1, hgs7]
    · -- R ≠ x23: transported through both steps back to the body-post frame
      obtain ⟨habi, hPCne, hnPCne, hmsne, hmsine, hmcne, hmtne, hmipne⟩ := hR
      have h23ne : (Register.x23 == R) = false := by
        rcases hbeq : (Register.x23 == R) with _ | _
        · rfl
        · rw [beq_iff_eq] at hbeq; exact absurd hbeq.symm h23
      have hnoise : ∀ r ∈ noiseRegs, (r == R) = false := by
        intro r hr
        simp only [noiseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hmsne
        · exact hPCne
        · exact hnPCne
        · exact hmsine
        · exact hmcne
        · exact hmtne
        · exact hmipne
      have hfr2 : σ2.regs.get? R = σ1.regs.get? R := sfo2.frame R hnoise
      have hfr1 : σ1.regs.get? R = c.σ.regs.get? R := by
        refine sfo1.frame R ?_
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact h23ne
        · exact hnoise r hr'
      rw [hfr2, hfr1]
      exact hc.frame R ⟨habi, hPCne, hnPCne, hmsne, hmsine, hmcne, hmtne, hmipne⟩ h23
  · -- stackWin: callJoinPC is untabled
    intro k hk
    rw [show stackScratchTop callJoinPC = none from rfl] at hk
    exact absurd hk (by simp)

/-! ## §3. The splice, factored ONCE

`Mid` is the dispatch leg's landing predicate — `NativeBodyPre` plus whatever
per-native geometry the body needs (the per-native `Extra` rides inside `Mid`;
the splice never inspects it). -/

/-- **`nativeArmSplice`** — the native-branch decomposition: dispatch leg ≫
body leg ≫ the (machine-discharged) join.  The native analogue of the closure
`callClosureSim` route split. -/
theorem nativeArmSplice
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st' : SpecSt) (spv s7v : BitVec 64) (m0 : Mem)
    (P Mid : Config → Prop)
    (hgsp : g Register.x2 = some spv)
    (hgs7 : g Register.x23 = some s7v)
    (hslotLo : 0x80000000 ≤ spv.toNat + 1016)
    (hslotHi : spv.toNat + 1024 ≤ 0x100000000)
    (hslotHtif : spv.toNat + 1024 ≤ tohostAddr ∨ tohostAddr + 8 ≤ spv.toNat + 1016)
    (hslotAlign : (spv.toNat + 1016) % 8 = 0)
    (hDispatch : Triple P Mid)
    (hBody : Triple Mid (NativeBodyPost g N A SL φf φc st' spv s7v m0)) :
    Triple P (CallExitP g N A SL φf φc nf nc st' m0) :=
  Triple.seq hDispatch (Triple.seq hBody
    (nativeJoin g N A SL φf φc nf nc st' spv s7v m0
      hgsp hgs7 hslotLo hslotHi hslotHtif hslotAlign))

/-! ## §4. The three native contracts as instantiations

Each RemainingWork field type is produced by `nativeArmSplice` at its own
post-state: `st` itself for assert, the output-appended states for
print/println.  What remains per native: the dispatch leg (shared machine body
in `rows/NativeArmDispatch.lean`; its `SegEntry`→ABI geometry is the caller's,
exactly the closure `hDispatchStage` residual class) and the body leg. -/

/-- **`NativeAssertOkSpec` from the splice** — `Call.assertOk` leaves the spec
state unchanged. -/
theorem nativeAssertOkSpec_of_splice
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem)
    (spv s7v : BitVec 64) (Mid : Config → Prop)
    (hgsp : g Register.x2 = some spv)
    (hgs7 : g Register.x23 = some s7v)
    (hslotLo : 0x80000000 ≤ spv.toNat + 1016)
    (hslotHi : spv.toNat + 1024 ≤ 0x100000000)
    (hslotHtif : spv.toNat + 1024 ≤ tohostAddr ∨ tohostAddr + 8 ≤ spv.toNat + 1016)
    (hslotAlign : (spv.toNat + 1016) % 8 = 0)
    (hDispatch : Triple (CallEntryP g N A SL φf φc st d dLeft aLeft m0) Mid)
    (hBody : Triple Mid (NativeBodyPost g N A SL φf φc st spv s7v m0)) :
    NativeAssertOkSpec g N A SL φf φc st d dLeft aLeft m0 :=
  nativeArmSplice g N A SL φf φc st.store.frames.size st.store.closures.size st
    spv s7v m0 _ Mid hgsp hgs7 hslotLo hslotHi hslotHtif hslotAlign hDispatch hBody

/-- **`NativePrintSpec` from the splice** — `Call.print` grows the output by
`printArgs st.store vs`, store unchanged. -/
theorem nativePrintSpec_of_splice
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem) (vs : List Value)
    (spv s7v : BitVec 64) (Mid : Config → Prop)
    (hgsp : g Register.x2 = some spv)
    (hgs7 : g Register.x23 = some s7v)
    (hslotLo : 0x80000000 ≤ spv.toNat + 1016)
    (hslotHi : spv.toNat + 1024 ≤ 0x100000000)
    (hslotHtif : spv.toNat + 1024 ≤ tohostAddr ∨ tohostAddr + 8 ≤ spv.toNat + 1016)
    (hslotAlign : (spv.toNat + 1016) % 8 = 0)
    (hDispatch : Triple (CallEntryP g N A SL φf φc st d dLeft aLeft m0) Mid)
    (hBody : Triple Mid (NativeBodyPost g N A SL φf φc
      ⟨st.store, st.out ++ printArgs st.store vs⟩ spv s7v m0)) :
    NativePrintSpec g N A SL φf φc st d dLeft aLeft m0 vs :=
  nativeArmSplice g N A SL φf φc st.store.frames.size st.store.closures.size
    ⟨st.store, st.out ++ printArgs st.store vs⟩
    spv s7v m0 _ Mid hgsp hgs7 hslotLo hslotHi hslotHtif hslotAlign hDispatch hBody

/-- **`NativePrintlnSpec` from the splice** — `Call.println` = `print` plus the
trailing `"\n"`. -/
theorem nativePrintlnSpec_of_splice
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem) (vs : List Value)
    (spv s7v : BitVec 64) (Mid : Config → Prop)
    (hgsp : g Register.x2 = some spv)
    (hgs7 : g Register.x23 = some s7v)
    (hslotLo : 0x80000000 ≤ spv.toNat + 1016)
    (hslotHi : spv.toNat + 1024 ≤ 0x100000000)
    (hslotHtif : spv.toNat + 1024 ≤ tohostAddr ∨ tohostAddr + 8 ≤ spv.toNat + 1016)
    (hslotAlign : (spv.toNat + 1016) % 8 = 0)
    (hDispatch : Triple (CallEntryP g N A SL φf φc st d dLeft aLeft m0) Mid)
    (hBody : Triple Mid (NativeBodyPost g N A SL φf φc
      ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ spv s7v m0)) :
    NativePrintlnSpec g N A SL φf φc st d dLeft aLeft m0 vs :=
  nativeArmSplice g N A SL φf φc st.store.frames.size st.store.closures.size
    ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩
    spv s7v m0 _ Mid hgsp hgs7 hslotLo hslotHi hslotHtif hslotAlign hDispatch hBody

#print axioms nativeJoin
#print axioms nativeArmSplice
#print axioms nativeAssertOkSpec_of_splice
#print axioms nativePrintSpec_of_splice
#print axioms nativePrintlnSpec_of_splice

end Vsa.Sim
