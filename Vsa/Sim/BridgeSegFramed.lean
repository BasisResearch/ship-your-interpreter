import Vsa.Sim.BridgeSeg
import Vsa.Sim.ErrorSiteJal
import Vsa.Sim.rows.ErrorReachInhab

/-!
# `BridgeSegFramed` — the avoid-set-generic frame core + the two ABI-mutating fronts

`FrameMeta.abiFrame_of_wrChain` (and its consumer `BridgeSeg.bridgeOfSeg`) collapse
a reflected span's raw register-frame clause

    ∀ R, (∀ rr ∈ noiseRegs, (rr == R) = false) →
         (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
      σ'.regs.get? R = σ.regs.get? R

to the callee-contract shape `∀ R, AbiPreserved R = true → get? R = get? R`, under
the ONE `decide` datum `WrChainAvoidAbi bs` (no register the span writes is
callee-saved).  Two open fronts need a span that DOES write callee-saved registers,
where `WrChainAvoidAbi` legitimately fails:

* **(a) the closure-arm dispatch head** `0x80003254..0x800032b8` (`mv s7,a1` at
  `0x80003278`, `mv s5,a4` at `0x80003290` — deliberate callee-saved *reseats*
  before the `jal env_new @0x800032bc`).  `wrChain` here contains `{x21, x23}`,
  both `AbiPreserved`.
* **(b) the 42 error-branch spill prefixes** — `sd s3..s7` to the stack before the
  `jal runtime_error`.  These are STORES: they write MEMORY, not the registers
  `s3..s7`; `wrChain` is EMPTY.  (And `s3..s7 = x19..x23` are exempt in
  `NotWrittenJmp` regardless.)

## Design verdict (the two consumers differ)

The frame machinery's *kernel* (`FrameMeta.abiPreserved_ne`) is already avoid-set
generic — it proves `(X == R) = false` from `R`, `X` on opposite sides of the SAME
predicate.  Only the *packaging* (`WrChainAvoidAbi`, `noise_ne_abi`,
`abiFrame_of_wrChain`) is hardcoded to `AbiPreserved`.  This file factors the
hardcoding out: ONE generic `wrChain_avoids_frame (P : Register → Bool)` core, with
`AbiPreserved` re-expressed as a THIN instance (the landed path, consumers
untouched).

* **(b) needs NO framed variant at all** — avoid-set-swap OR spill-tracking are both
  overkill.  The spill prefix's `wrChain = []`, so the raw seg frame preserves EVERY
  register for free; the only real obligation is the MEMORY side (`Runtime_errorLoaded`
  / `LongjmpLoaded` must survive the stack stores), which is the *footprint* frame
  (`FrameMeta.memFrame_of_chain`, already avoid-set-independent).  See the demo.
* **(a) genuinely needs spill/delta EXPOSURE, not an avoid-set swap.**  `s5`, `s7`
  are BOTH written AND callee-saved, so no non-trivial predicate collapse recovers
  their frame — the frame simply does not hold for them.  The seg ALREADY computes
  the reseated values in `out.regs` (`GHolds σ' out.regs`); `bridgeOfSegFramed`
  exposes that directly, and asserts the ABI frame only for the callee-saveds the
  span does NOT write (`P := fun R => AbiPreserved R && decide (R ∉ writtenCalleeSaved)`,
  the generic core instantiated at the restricted predicate).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.Alloc (AbiPreserved)
open Vsa.Sim.Code (Runtime_errorLoaded LongjmpLoaded)
open Vsa.While

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

/-! ## §1. The avoid-set-generic frame core

The whole `FrameMeta` (c) layer, parameterised by an arbitrary decidable bool
predicate `P : Register → Bool`.  `AbiPreserved` is one `P`; the error-branch
`NotWrittenJmp`-shaped set is another. -/

/-- **The generic distinctness datum.**  Two registers on opposite sides of `P`
are unequal.  This is `FrameMeta.abiPreserved_ne` with `AbiPreserved` abstracted to
any `P` — the SAME proof, showing the kernel was never `AbiPreserved`-specific. -/
theorem regAvoids_ne {P : Register → Bool} {R X : Register}
    (hR : P R = true) (hX : P X = false) : (X == R) = false := by
  rcases hXR : (X == R) with _ | _
  · rfl
  · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)

/-- **The `decide`-checkable avoid datum for `P`.**  No register the chain writes
satisfies `P`.  First-order over `wrChain bs` (a concrete `List Nat`); for any
concrete chain + concrete `P` this is ONE kernel `decide`. -/
def WrChainAvoids (P : Register → Bool) (bs : List BBlock) : Prop :=
  ∀ n ∈ wrChain bs, P (gprReg n) = false

instance (P : Register → Bool) (bs : List BBlock) : Decidable (WrChainAvoids P bs) := by
  unfold WrChainAvoids; infer_instance

/-- **Noise never satisfies a well-formed frame predicate.**  Given `P` is false on
every noise register (`hnoiseP`, one `decide` for a concrete `P`), any `P R = true`
discharges the FIRST frame side-condition `∀ rr ∈ noiseRegs, (rr == R) = false`. -/
theorem noise_avoids {P : Register → Bool} (hnoiseP : ∀ rr ∈ noiseRegs, P rr = false)
    {R : Register} (hR : P R = true) : ∀ rr ∈ noiseRegs, (rr == R) = false :=
  fun rr hrr => regAvoids_ne hR (hnoiseP rr hrr)

/-- **The wrChain guard, discharged for `P`.**  Under `WrChainAvoids P bs`, every
written register differs from any `P R = true`. -/
theorem wrChain_avoids {P : Register → Bool} {bs : List BBlock}
    (hAvoid : WrChainAvoids P bs) {R : Register} (hR : P R = true) :
    ∀ n ∈ wrChain bs, (gprReg n == R) = false :=
  fun n hn => regAvoids_ne hR (hAvoid n hn)

/-- **The generic frame metatheorem (chain).**  Any raw frame clause the chain
soundness lemmas produce collapses — under `hnoiseP` + `WrChainAvoids P bs` (two
`decide`s) — to `∀ R, P R = true → get? R = get? R`.  `FrameMeta.abiFrame_of_wrChain`
is this at `P := AbiPreserved`. -/
theorem frame_of_wrChain_avoids {P : Register → Bool} {bs : List BBlock}
    {σ' σ : MState}
    (hnoiseP : ∀ rr ∈ noiseRegs, P rr = false)
    (hAvoid : WrChainAvoids P bs)
    (hframe : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
      σ'.regs.get? R = σ.regs.get? R) :
    ∀ R, P R = true → σ'.regs.get? R = σ.regs.get? R :=
  fun R hR => hframe R (noise_avoids hnoiseP hR) (wrChain_avoids hAvoid hR)

/-! ### Instance 1 — `AbiPreserved` (re-expressing the landed path)

`WrChainAvoids AbiPreserved` and `frame_of_wrChain_avoids (P := AbiPreserved)` ARE
`FrameMeta.WrChainAvoidAbi` / `FrameMeta.abiFrame_of_wrChain` — verified equal
below.  The landed `bridgeOfSeg` path is unchanged; this just exhibits it as the
`P := AbiPreserved` specialisation of the generic core. -/

/-- The `AbiPreserved` avoid predicate is false on every noise register (one
`decide`). -/
theorem abiPreserved_noise : ∀ rr ∈ noiseRegs, AbiPreserved rr = false := by decide

/-- `WrChainAvoids AbiPreserved` IS `FrameMeta.WrChainAvoidAbi` (definitional). -/
theorem wrChainAvoids_abi_eq (bs : List BBlock) :
    WrChainAvoids AbiPreserved bs = WrChainAvoidAbi bs := rfl

/-- The generic frame core at `P := AbiPreserved` recovers `abiFrame_of_wrChain`. -/
theorem frame_of_wrChain_avoids_abi {bs : List BBlock} {σ' σ : MState}
    (hAvoid : WrChainAvoidAbi bs)
    (hframe : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
      σ'.regs.get? R = σ.regs.get? R) :
    ∀ R, AbiPreserved R = true → σ'.regs.get? R = σ.regs.get? R :=
  frame_of_wrChain_avoids abiPreserved_noise hAvoid hframe

#print axioms regAvoids_ne
#print axioms frame_of_wrChain_avoids

/-! ## §2. `bridgeOfSegFramed` — the ABI-mutating jal-terminated bridge

`BridgeSeg.bridgeOfSeg` requires `WrChainAvoidAbi bs`, so it produces an ABI frame
`∀ R, AbiPreserved R → get? R = get? R` over the WHOLE callee-saved set.  A span
that reseats callee-saveds (consumer (a): `mv s7`, `mv s5`) cannot satisfy that.

`bridgeOfSegFramed` keeps everything `bridgeOfSeg` gives — the seg run, the jal
seam, the marshalled args' survival, the memory `writeLog m0 out.log`, the minstret
witness — but replaces the ABI-frame conclusion with the generic `P`-frame
(`frame_of_wrChain_avoids`).  A consumer instantiates `P` at the callee-saveds the
span does NOT write; the reseated ones (`s5`/`s7`) are read off the *exposed*
`GHolds σ2 out.regs` post — the deltas, already computed by the seg, are the "spill
tracking" the observation `callclosure-entrybase-abi` asked for, and they come FREE.

The genuinely per-callee jal seam is still the `JalStep` datum; only the frame
predicate is swapped from `AbiPreserved` (hardcoded) to caller-supplied `P`. -/
theorem bridgeOfSegFramed (P : Register → Bool)
    (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (σ : MState) (i u : Nat) (pc0 calleeEntry link vm : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hmem : σ.mem = m0)
    (hL : GHolds σ L)
    (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts σ.mem σ.mem L lds bs)
    (hi : i < 2)
    (hwf : ChainOK pc0 (keysG L) bs)
    -- the generic frame data (two `decide`s), REPLACING `WrChainAvoidAbi bs`:
    (hnoiseP : ∀ rr ∈ noiseRegs, P rr = false)
    (hAvoidP : WrChainAvoids P bs)
    (hKeysOut : KeysOK (keysG (evalBlocks bs (SegEvalState.init L lds)).regs))
    (hRaOut : KeysAvoidRa (evalBlocks bs (SegEvalState.init L lds)).regs)
    -- `P` restricts the callee-saved frame; the jal's OWN frame (in `JalStep`) is
    -- over `AbiPreserved`, and any well-formed `P` for consumer (a) is a SUBSET of
    -- `AbiPreserved` (it drops the reseated `s5`/`s7`), so `P → AbiPreserved` — one
    -- `decide` at the use site.  This lets the jal side reuse `JalStep`'s ABI frame.
    (hPabi : ∀ R, P R = true → AbiPreserved R = true)
    (hjal : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log →
      GHolds σ' (evalBlocks bs (SegEvalState.init L lds)).regs →
      JalStep calleeEntry link σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel bs + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some calleeEntry ∧
      σ2.regs.get? Register.x1 = some link ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      -- the whole reseated register bundle, EXPOSED (the deltas the span computes,
      -- incl. the callee-saved reseats `s5`/`s7`): the "spill tracking", free.
      GHolds σ2 (evalBlocks bs (SegEvalState.init L lds)).regs ∧
      σ2.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log ∧
      -- the P-restricted callee-saved frame across the whole bridge (body ∘ jal):
      (∀ R, P R = true → σ2.regs.get? R = σ.regs.get? R) := by
  -- run the seg body (FREE): whole Steps chain, computed end-PC = jalPC, computed
  -- reseated regs, computed memory, and the RAW wrChain frame clause.
  obtain ⟨σ', i', hs, hi', hG', hmem', _hout, hpc', hmi', hregs, hframe⟩ :=
    segEval_sound bs σ i u pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf hi
  -- the P-frame of the body, FREE (two `decide`s: `hnoiseP`, `hAvoidP`).
  have hPBody : ∀ R, P R = true → σ'.regs.get? R = σ.regs.get? R :=
    frame_of_wrChain_avoids hnoiseP hAvoidP hframe
  rw [hmem] at hmem'
  -- take the jal step (feeding it the seg-post memory + reseated regs).
  obtain ⟨σ2, i2, hstep2, hi2, hG2, hmem2, hpc2, hra2, hmi2, hnonra2, habiJal⟩ :=
    hjal σ' i' (u + evalBlocksFuel bs) hG' hi' hpc' hmi' hmem' hregs
  refine ⟨σ2, i2, Steps.trans hs (Steps.single hstep2), hi2, hG2, hpc2, hra2, hmi2, ?_, ?_, ?_⟩
  · exact gholds_of_jal hnonra2 _ hKeysOut hRaOut hregs
  · rw [hmem2]; exact hmem'
  · -- P-frame across body ∘ jal.  For `P R = true`: `P R → AbiPreserved R`
    -- (`hPabi`), so the jal's own `AbiPreserved` frame (`habiJal`) carries R across
    -- the jal; then the body's P-frame (`hPBody`) carries R back to `σ`.
    intro R hR
    exact (habiJal R (hPabi R hR)).trans (hPBody R hR)

#print axioms bridgeOfSegFramed

/-! ## §3. Demo (b) — one error-branch spill prefix, closed end-to-end

The `hNegType` error node's `jal runtime_error @0x800034e4` is preceded by the pure
stack-spill block

```
800034d0:  sd s3,1048(sp)      800034dc:  sd s6,1024(sp)
800034d4:  sd s4,1040(sp)      800034e0:  sd s7,1016(sp)  ── ▷ jal runtime_error
800034d8:  sd s5,1032(sp)
```

**Verdict for (b): NO framed variant is needed.**  Every instruction is a `.sd`
STORE — it writes MEMORY, not the registers `s3..s7`; `wrChain spillSeg = []`.  So
`segToTriple`'s underlying seg frame preserves EVERY register for free (no
`WrChainAvoids`/`bridgeOfSegFramed` at all).  The ONLY real obligation is the
MEMORY side: the post-spill memory `writeLog m0 spillLog` must still satisfy
`JalErrPre`'s `Runtime_errorLoaded`/`LongjmpLoaded` (code ⊥ stack) — the footprint
frame, avoid-set-independent.  We carry it as the arm's named `hLoadedPost` datum
(the arm supplies a config whose post-spill memory keeps the code images loaded;
the genuine geometric residual, exactly `ErrorReachInhab`'s `hlink` in spirit).

The seg is emitted here (a real `#derive_case` on the actual error-site path),
`segToTriple`d into `Triple ArmBranchPre (JalErrPre …)`, and fed through
`negType_hsite_of_armBranch` — so ONE complete `hNegType` error link closes to
`ErrHalts c`, modulo only the arm-linkage fact (`hlink`) and the loaded-post datum. -/

#derive_case spillNegSeg chain
  [(0x800034d0#64, 0x41313c23#32),   -- sd s3,1048(sp)
   (0x800034d4#64, 0x41413823#32),   -- sd s4,1040(sp)
   (0x800034d8#64, 0x41513423#32),   -- sd s5,1032(sp)
   (0x800034dc#64, 0x41613023#32),   -- sd s6,1024(sp)
   (0x800034e0#64, 0x3f713c23#32)]   -- sd s7,1016(sp)

#print axioms spillNegSeg_seg

/-- **The `hNegType` error-branch entry predicate.**  A config parked at the spill
block entry `0x800034d0` with everything the seg + the runtime_error entry demand:
the seg's `GoodState`/PC/minstret/`GHolds`/`KeysOK`/`ChainFacts`, the entry memory
`m0`, `tick < 2`, the ErrorIn pointer in `x10`, its `WinRAM`, the `g` ghost frame
over `NotWrittenJmp` (all at ENTRY — pure stores preserve them), and the target
facts over the POST-spill memory `S.m0 = writeLog m0 spillLog`: the code images stay
loaded (`code ⊥ stack`, the named geometric residual) and the jal byte pins.  The
end PC lands at the jal `0x800034e4`. -/
def SpillNegArmPre (S : ErrShared) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (L : GRegs) (lds : List (List (BitVec 8))) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x800034d0#64 ∧
  (∃ vm, c.σ.regs.get? Register.minstret = some vm) ∧
  GHolds c.σ L ∧ KeysOK (keysG L) ∧ ChainFacts c.σ.mem c.σ.mem L lds spillNegSeg ∧
  ChainOK 0x800034d0#64 (keysG L) spillNegSeg ∧
  c.tick < 2 ∧
  c.σ.regs.get? Register.x10 = some S.inp ∧ WinRAM (S.inp + 16#64) ∧
  (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = S.g R) ∧
  S.m0 = writeLog m0 (evalBlocks spillNegSeg (SegEvalState.init L lds)).log ∧
  Runtime_errorLoaded S.m0 ∧ LongjmpLoaded S.m0 ∧
  S.m0[(0x800034e4 : Nat)]? = some (0xef : BitVec 8) ∧
  S.m0[(0x800034e4 + 1 : Nat)]? = some (0xf0 : BitVec 8) ∧
  S.m0[(0x800034e4 + 2 : Nat)]? = some (0x5f : BitVec 8) ∧
  S.m0[(0x800034e4 + 3 : Nat)]? = some (0x8c : BitVec 8) ∧
  (evalBlocksPC 0x800034d0#64 (SegEvalState.init L lds) spillNegSeg)
    = (0x800034e4 : BitVec 64)

/-- **The spill-prefix seg, marshalled to `JalErrPre`.**  Runs the five `sd` stores
via `segEval_sound` (the RAW frame clause is what we need here, not the pin-only
`segToTriple`).  Because the body writes NO register (`wrChain spillNegSeg = []`),
the frame clause preserves EVERY non-noise register — so `x10 = inp` and the whole
`NotWrittenJmp` `g`-frame carry from entry to the jal PC for FREE.  The memory side
is `writeLog m0 spillLog = S.m0`, whose loadedness is the arm's `Runtime_errorLoaded
S.m0` datum (`code ⊥ stack`, the named residual).  This is exactly the `Triple
ArmBranchPre (JalErrPre …)` that `negType_hsite_of_armBranch` consumes — and NO
`bridgeOfSegFramed` is used, precisely because (b) never needed frame tracking. -/
theorem spillNeg_toJalErr (S : ErrShared) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (L : GRegs) (lds : List (List (BitVec 8))) :
    Triple (SpillNegArmPre S m0 L lds)
      (JalErrPre S.g S.inp S.m0 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8) := by
  intro c hpre
  obtain ⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, hwf, htick, hx10, hwin, hgframe,
    hm0eq, hRE, hLJ, hb0, hb1, hb2, hb3, hpcEq⟩ := hpre
  -- run the spill seg; keep the RAW frame clause `hframe`.
  obtain ⟨σ', i', hs, hi', hG', hmem', _hout, hpc', ⟨w, hmi'⟩, _hregs, hframe⟩ :=
    segEval_sound spillNegSeg c.σ c.tick c.steps 0x800034d0#64 vm L lds
      hG hpc hmi hL hkeys hfacts hwf htick
  rw [hmem] at hmem'
  -- `wrChain spillNegSeg = []` (pure stores write no register), so the frame clause
  -- preserves every non-noise reg — the wrChain guard is vacuous.
  have hwrNil : wrChain spillNegSeg = [] := by decide
  have hframe' : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      σ'.regs.get? R = c.σ.regs.get? R :=
    fun R hRn => hframe R hRn (fun n hn => by rw [hwrNil] at hn; exact absurd hn (by simp))
  -- the whole seg run IS the reachability witness (`c` runs to the parked config).
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel spillNegSeg⟩, hs, ?_⟩
  -- `NotWrittenJmp R` ⇒ R avoids every noise register (noise = jmp control set).
  have noiseAvoid : ∀ {R : Register}, NotWrittenJmp R → ∀ rr ∈ noiseRegs, (rr == R) = false := by
    intro R hR rr hrr
    simp only [noiseRegs, List.mem_cons, List.not_mem_nil, or_false] at hrr
    rcases hrr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hR.mi
    · exact hR.pc
    · exact hR.npc
    · exact hR.mii
    · exact hR.mc
    · exact hR.mt
    · exact hR.mip
  -- assemble `JalErrPre`.
  refine ⟨hG', ?_, ?_, ?_, ?_, ?_, hwin, ⟨w, hmi'⟩, hi', ?_, ?_, ?_, ?_, ?_⟩
  · exact hm0eq ▸ hRE
  · exact hm0eq ▸ hLJ
  · show σ'.mem = S.m0; rw [hmem', ← hm0eq]
  · show σ'.regs.get? Register.PC = _; rw [hpc']; exact congrArg some hpcEq
  · -- x10 = inp: `x10` is not noise; frame preserves it from entry.
    show σ'.regs.get? Register.x10 = some S.inp
    rw [hframe' Register.x10 (by decide)]; exact hx10
  · -- the g ghost frame: each `NotWrittenJmp` R is non-noise, frame-preserved.
    intro R hR
    show σ'.regs.get? R = S.g R
    rw [hframe' R (noiseAvoid hR)]; exact hgframe R hR
  · show σ'.mem[(0x800034e4 : Nat)]? = _; rw [hmem', ← hm0eq]; exact hb0
  · show σ'.mem[(0x800034e4 + 1 : Nat)]? = _; rw [hmem', ← hm0eq]; exact hb1
  · show σ'.mem[(0x800034e4 + 2 : Nat)]? = _; rw [hmem', ← hm0eq]; exact hb2
  · show σ'.mem[(0x800034e4 + 3 : Nat)]? = _; rw [hmem', ← hm0eq]; exact hb3

#print axioms spillNeg_toJalErr

/-- **ONE complete `hNegType` error link, closed.**  Feeding `spillNeg_toJalErr`'s
`Triple ArmBranchPre (JalErrPre …)` (the real spill-prefix seg) into
`negType_hsite_of_armBranch` discharges the whole `hNegType` `errFamily_of_sites`
premise to `ErrHalts c` — modulo ONLY the arm-linkage `hlink` (that the `negType`
spec context lands the machine at the spill-block entry `SpillNegArmPre`), the
genuine M4 residual `ErrorReachInhab` already names.  So the error link is complete
end-to-end: seg (this file) ≫ jal (`jalStep_to_runtimeError`) ≫ tail
(`route_hNegType`), with no fabricated frame step. -/
theorem negType_link_closed (S : ErrShared) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (L : GRegs) (lds : List (List (BitVec 8)))
    (hlink : ∀ (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
      (st' : Vsa.While.St) (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → SpillNegArmPre S m0 L lds c) :
    ∀ (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
      (st' : Vsa.While.St) (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → ErrHalts c :=
  negType_hsite_of_armBranch S (spillNeg_toJalErr S m0 L lds) hlink

#print axioms negType_link_closed

/-! ## §4. Demo (a) — the closure entryBase callee-saved reseat, via `bridgeOfSegFramed`

The closure-arm dispatch head `0x80003254..0x800032b8` reseats TWO callee-saved
registers before its `jal env_new @0x800032bc`: `mv s7,a1` (`x23 := x11`) at
`0x80003278` and `mv s5,a4` (`x21 := x14`) at `0x80003290`.  So `wrChain` contains
`{x21, x23}`, both `AbiPreserved` — `WrChainAvoidAbi` FAILS and `bridgeOfSeg` is
inapplicable (observation `callclosure-entrybase-abi`).

Here we demonstrate `bridgeOfSegFramed` on the load-bearing idiom — the real
`mv s7,a1` reseat (`0x80003278`, word `0x00058b93`).  The frame predicate is
`AbiPreserved` RESTRICTED to drop the written `x23` (`P := fun R => AbiPreserved R
&& !(R == x23)`); the reseated `s7 = a1` value is read off the EXPOSED post register
bundle `GHolds σ2 out.regs` — the "spill tracking" the observation asked for, FREE
from the seg.  The full 5-block entryBase (with its 4 guard branches) composes the
same way; the interior branches are a separate `#derive_case chain` `ChainOK`
concern, orthogonal to the frame issue this file resolves. -/

/-! The `mv s7,a1` reseat block (`0x80003278: addi x23,x11,0`), the callee-saved
write that defeats `WrChainAvoidAbi`. -/
#derive_case mvS7Seg chain
  [(0x80003278#64, 0x00058b93#32)]   -- addi x23,x11,0  (= mv s7,a1)

#print axioms mvS7Seg_seg

/-- The restricted ABI frame predicate: callee-saved EXCEPT the reseated `s7 = x23`.
`bridgeOfSegFramed`'s frame conclusion holds for exactly these; `s7`'s new value is
read off the exposed post bundle instead. -/
def AbiExceptS7 (R : Register) : Bool := AbiPreserved R && !(R == Register.x23)

/-- **The entryBase reseat idiom, bridged with `bridgeOfSegFramed`.**  Entry pin
`x11 = a1v`; the seg reseats `x23 := a1v` (a callee-saved write).  The combinator
produces: parked at `env_new` entry, `x1 = link`, the EXPOSED reseated bundle
`GHolds σ2 out.regs` (carrying the new `s7 = a1v`), and the ABI frame for every
callee-saved EXCEPT `s7`.  `WrChainAvoidAbi` is NOT required — only `WrChainAvoids
AbiExceptS7` (which holds: the sole write `x23` fails `AbiExceptS7`).  The env_new
`JalStep` stays a NAMED per-callee residual (its site lemma is region-specific). -/
theorem entryBaseReseat_framed
    (σ : MState) (i u : Nat) (a1v link vm : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x80003278#64)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hmem : σ.mem = m0)
    (hL : GHolds σ [(11, a1v)])
    (hfacts : ChainFacts σ.mem σ.mem [(11, a1v)] [] mvS7Seg)
    (hi : i < 2)
    (hjal : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC
        = some (evalBlocksPC 0x80003278#64 (SegEvalState.init [(11, a1v)] []) mvS7Seg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks mvS7Seg (SegEvalState.init [(11, a1v)] [])).log →
      GHolds σ' (evalBlocks mvS7Seg (SegEvalState.init [(11, a1v)] [])).regs →
      JalStep 0x800029fc#64 link σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel mvS7Seg + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some 0x800029fc#64 ∧
      σ2.regs.get? Register.x1 = some link ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      -- the reseated `s7 = a1v`, read off the EXPOSED post bundle (the delta, free):
      gprGet σ2 23 = some a1v ∧
      -- the ABI frame for every callee-saved EXCEPT the reseated `s7`:
      (∀ R, AbiExceptS7 R = true → σ2.regs.get? R = σ.regs.get? R) := by
  -- the side-condition decides, named.  `keysG`/`.regs`-keys never inspect the pin
  -- VALUE `a1v` (only the index), so each goal reduces (`rfl`) to an `a1v`-free
  -- concrete list, then closes by `decide`.
  have hkeys : KeysOK (keysG [(11, a1v)]) := by
    show KeysOK [11]; decide
  have hwf : ChainOK 0x80003278#64 (keysG [(11, a1v)]) mvS7Seg := by
    show ChainOK 0x80003278#64 [11] mvS7Seg; decide
  have hnoiseP : ∀ rr ∈ noiseRegs, AbiExceptS7 rr = false := by decide
  have hAvoidP : WrChainAvoids AbiExceptS7 mvS7Seg := by decide
  have hKeysOut : KeysOK (keysG (evalBlocks mvS7Seg (SegEvalState.init [(11, a1v)] [])).regs) := by
    show KeysOK [23, 11]; decide
  have hRaOut : KeysAvoidRa (evalBlocks mvS7Seg (SegEvalState.init [(11, a1v)] [])).regs := by
    show ∀ n ∈ ([23, 11] : List Nat), n ≠ 1; decide
  -- `AbiExceptS7 R → AbiPreserved R`: the restricted predicate is a subset (Bool `&&`).
  have hPabi : ∀ R, AbiExceptS7 R = true → AbiPreserved R = true := by
    intro R hR; unfold AbiExceptS7 at hR; exact (Bool.and_eq_true .. |>.mp hR).1
  obtain ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, hmi2, hregs2, _hmem2, hframe2⟩ :=
    bridgeOfSegFramed AbiExceptS7 mvS7Seg [(11, a1v)] [] σ i u
      0x80003278#64 0x800029fc#64 link vm m0
      hG hpc hmi hmem hL hkeys hfacts hi hwf
      hnoiseP hAvoidP hKeysOut hRaOut hPabi hjal
  refine ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, hmi2, ?_, hframe2⟩
  -- read the reseated `s7 = a1v` off the exposed post bundle `GHolds σ2 out.regs`.
  -- `lookupG 23 out.regs = some a1v` holds by `rfl` (the reseat wrote `x23 := a1v`).
  have hlk : lookupG 23 (evalBlocks mvS7Seg (SegEvalState.init [(11, a1v)] [])).regs
      = some a1v := by
    show lookupG 23 [(23, a1v + 0#64), (11, a1v)] = some a1v
    simp [lookupG, BitVec.add_zero]
  exact gholds_lookup (v := a1v) _ hregs2 hlk

#print axioms entryBaseReseat_framed

end Vsa.Sim
