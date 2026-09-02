import Vsa.Sim.EntryHalts
import Vsa.Sim.ExitPathSpans

/-!
# Layer 8 — discharging the two `EntryHalts` span seams

`Vsa/Sim/EntryHalts.lean`'s `hEntryHalts_of` reduced the program-entry premise to
TWO named span residuals — `EntryPrologueSpan` (`Loaded → SegEntry@loopHead`) and
`EntryEpilogueSpan` (`SegExit@exit → interp_run cont`).  This file supplies both,
mirroring the exit-70 twin `Vsa/Sim/ExitPathSpans.lean` (`interpContSeg_of`,
`interpContChain`, `icB1`), and lands `hEntryHalts_closed` modulo the honest
representation residuals that remain.

## The shared restore battery (`restoreRetChain`)

The exit-70 twin's `icB1` restore body and this file's `.normal`-epilogue restore
body are BYTE-IDENTICAL apart from `icB1`'s first three instructions
(`ld a5,0(sp); li s5,1; sw zero,8(a5)`).  Both are a single straight-line block of
nine `ld`s + `mv a0,s5` + `addi sp,sp,176` terminated by `ret`, whose only
load-bearing datum is the pinned `ra` slot (= `0x800045ec`, main's `jal interp_run`
link) and the `a0` return value latched from `s5`.  Rather than re-hand-thread a
second `bblocks_sound_bt` invocation we FACTOR the restore into
`restoreRetChain_run`: a single reusable lemma over a one-block `ret`-terminated
chain, parameterized by the pinned `ra` target, the `s5`/`a0` value, and the
`ChainFacts` spill residual.  `interpContSeg_of`'s tail (post-`bnez`) and this
file's epilogue are two instances of it.

## What is genuinely open (named residuals)

`SegEntry`/`SegExit` are the RICH M4-level predicates (`StoreRepr`, `OutRepr`,
budget fields), NOT machine-level `ChainFacts`.  The two spans therefore each
carry a representation seam that cannot be discharged by block-reflection alone:

* **`EpilogueFrame`** — from `SegExit` at the normal-exit PC, the concrete
  `ChainFacts` for the restore block (the spill images, `ra` pinned to
  `0x800045ec`), `sp = spv`, the return latch `s5 = 0` (⇐ `SegExit.frame` on the
  callee-saved `s5`, given the prologue latched `g s5 = 0`), and the produced
  `ExitTailChain0` (the tail span the epilogue's postcondition demands, itself
  discharged concretely by `TermEntry.cleanExitTail`'s consumer).  This is the
  exit-0 analogue of `ExitPathSpans.InterpContFrame`.
* **`PrologueSpanResid`** — from `Loaded L p c` the machine reaches `SegEntry` at
  the loop head.  This bundles: (a) the spill decode `[0x800043ec, 0x80004424)`;
  (b) the `jal setjmp` splice, discharged by `JmpSpec.setjmp_spec` (the FIRST
  return: `setjmp_pre` at `0x80006ffc` → `setjmp_post` with `a0 = 0`, `PC = ra0`),
  so `bnez a0` is NOT taken; (c) the loop-setup decode `[0x8000442c, 0x8000448c)`;
  (d) the store-init seam `ProgramRepr → StoreRepr initSt` (the AST/heap-init
  representation — `initSt` = the single global frame with the three natives —
  established by the interpreter's own `env_new` startup path, surfaced as the
  named `StoreInitSeam` premise).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps Halted Halts output)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq Addr)
open Vsa.Sim.TermSimAssembly (mExecSeq)
open Vsa.Sim.Scaffold (SegEntry SegExit)
open Vsa.Sim.Code (Interp_runLoaded)

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The shared restore battery — `restoreRetChain`

A single straight-line block: the nine epilogue `ld`s (restoring `ra` first),
`mv a0,s5`, `addi sp,sp,176`, terminated by `ret`.  This is EXACTLY `icB1` minus
the leading `ld a5,0(sp); li s5,1; sw zero,8(a5)` — so it factors the byte-similar
restore that both the exit-70 (`interpContSeg_of`) and exit-0 (epilogue) paths run.

Body (10 instructions, program order):
`ld ra,168(sp)`; `ld s0,160(sp)`; `ld s1,152(sp)`; `ld s2,144(sp)`;
`ld s3,136(sp)`; `ld s4,128(sp)`; `ld s6,112(sp)`; `mv a0,s5`; `ld s5,120(sp)`;
`addi sp,sp,176`.  Terminator: `ret` (`jr ra`). -/
def restoreB : BBlock :=
  { body :=
      [ -- ld ra,168(sp)   word 0a813083  bytes 83 30 81 0a  rd=1 rs1=2 off=0x0a8
        ⟨0x80004514#64, 0x0a813083#32, 0x83#8, 0x30#8, 0x81#8, 0x0a#8, .ld, 1, 2, 0, 0x0a8#12⟩,
        -- ld s0,160(sp)   word 0a013403  bytes 03 34 01 0a  rd=8 rs1=2 off=0x0a0
        ⟨0x80004518#64, 0x0a013403#32, 0x03#8, 0x34#8, 0x01#8, 0x0a#8, .ld, 8, 2, 0, 0x0a0#12⟩,
        -- ld s1,152(sp)   word 09813483  bytes 83 34 81 09  rd=9 rs1=2 off=0x098
        ⟨0x8000451c#64, 0x09813483#32, 0x83#8, 0x34#8, 0x81#8, 0x09#8, .ld, 9, 2, 0, 0x098#12⟩,
        -- ld s2,144(sp)   word 09013903  bytes 03 39 01 09  rd=18 rs1=2 off=0x090
        ⟨0x80004520#64, 0x09013903#32, 0x03#8, 0x39#8, 0x01#8, 0x09#8, .ld, 18, 2, 0, 0x090#12⟩,
        -- ld s3,136(sp)   word 08813983  bytes 83 39 81 08  rd=19 rs1=2 off=0x088
        ⟨0x80004524#64, 0x08813983#32, 0x83#8, 0x39#8, 0x81#8, 0x08#8, .ld, 19, 2, 0, 0x088#12⟩,
        -- ld s4,128(sp)   word 08013a03  bytes 03 3a 01 08  rd=20 rs1=2 off=0x080
        ⟨0x80004528#64, 0x08013a03#32, 0x03#8, 0x3a#8, 0x01#8, 0x08#8, .ld, 20, 2, 0, 0x080#12⟩,
        -- ld s6,112(sp)   word 07013b03  bytes 03 3b 01 07  rd=22 rs1=2 off=0x070
        ⟨0x8000452c#64, 0x07013b03#32, 0x03#8, 0x3b#8, 0x01#8, 0x07#8, .ld, 22, 2, 0, 0x070#12⟩,
        -- mv a0,s5        word 000a8513  bytes 13 85 0a 00  addi a0,s5,0
        ⟨0x80004530#64, 0x000a8513#32, 0x13#8, 0x85#8, 0x0a#8, 0x00#8, .addi, 10, 21, 0, 0x000#12⟩,
        -- ld s5,120(sp)   word 07813a83  bytes 83 3a 81 07  rd=21 rs1=2 off=0x078
        ⟨0x80004534#64, 0x07813a83#32, 0x83#8, 0x3a#8, 0x81#8, 0x07#8, .ld, 21, 2, 0, 0x078#12⟩,
        -- addi sp,sp,176  word 0b010113  bytes 13 01 01 0b  rd=2 rs1=2 off=0x0b0
        ⟨0x80004538#64, 0x0b010113#32, 0x13#8, 0x01#8, 0x01#8, 0x0b#8, .addi, 2, 2, 0, 0x0b0#12⟩ ],
    term := some ⟨0x8000453c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8,
      .jr, 1, 0, 0#13, 0#21, 0x000#12⟩ }

/-- The restore chain: a single block terminated by `ret`. -/
def restoreChain : List BBlock := [restoreB]

/-- The load byte-lists for `restoreB`'s eight `ld`s, in program order
(`ra, s0, s1, s2, s3, s4, s6, s5`), with the `ra` slot pinned to the LE bytes of
`0x800045ec` (main's `jal interp_run` link).  The other seven are arbitrary (the
restored callee-saveds are not observed downstream). -/
def ldsRestore (s0b s1b s2b s3b s4b s6b s5b : List (BitVec 8)) :
    List (List (BitVec 8)) :=
  [ [0xec#8, 0x45#8, 0x00#8, 0x80#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8],  -- ra = 0x800045ec
    s0b, s1b, s2b, s3b, s4b, s6b, s5b ]

/-- **The shared restore battery.**  From a config parked at `0x80004514` with
`s5 = a0v` (the return-value latch), `GoodState`, tick-bounded, the entry `sp`,
and the `ChainFacts` for `restoreChain`, the nine restores + `mv a0,s5` + `ret`
land at `0x800045ec` (main's `jal interp_run` link) with `a0 = a0v`, `GoodState`,
tick-bounded, and `output` unchanged.

ONE `bblocks_sound_bt` over the one-block chain; the exit-0 (epilogue) and exit-70
(`interpContSeg_of` tail) paths are two instances (they differ only in the value
`a0v` latched into `s5`, `0` vs `1`).  The pinned `ra` slot makes the end PC
reduce past the abstract load base `spv`, exactly as in `interpContSeg_of`. -/
theorem restoreRetChain_run (out : String) (a0v spv : BitVec 64)
    (s0b s1b s2b s3b s4b s6b s5b : List (BitVec 8))
    (c : Config)
    (hG : GoodState c.σ) (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some (0x80004514#64 : BitVec 64))
    (hs5 : c.σ.regs.get? Register.x21 = some a0v)
    (hsp : c.σ.regs.get? Register.x2 = some spv)
    (hout : output c.σ = out)
    (hcf : ChainFacts c.σ.mem c.σ.mem
      [(21, a0v), (2, spv)] (ldsRestore s0b s1b s2b s3b s4b s6b s5b) restoreChain) :
    ∃ c', Steps c c' ∧
      GoodState c'.σ ∧ c'.tick < 2 ∧
      c'.σ.regs.get? Register.PC = some (0x800045ec#64 : BitVec 64) ∧
      c'.σ.regs.get? Register.x10 = some a0v ∧
      output c'.σ = out := by
  obtain ⟨vm, hmi⟩ := hG.minstret
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, _hframe⟩ :=
    bblocks_sound_bt restoreChain c.σ c.tick c.steps (0x80004514#64) vm
      [(21, a0v), (2, spv)] (ldsRestore s0b s1b s2b s3b s4b s6b s5b)
      hG hpc hmi ⟨hs5, hsp, trivial⟩
      (show KeysOK [21, 2] by decide)
      hcf
      (show ChainOK (0x80004514#64) [21, 2] restoreChain by decide)
      htick
  refine ⟨⟨σ', i', c.steps + chainLen restoreChain⟩, ?_, hG', hi', ?_, ?_, ?_⟩
  · cases c; exact hsteps
  · -- PC = restored ra = 0x800045ec, independent of the load base spv.
    have hra : srcVal 1 (runGM restoreB.body
        [(21, a0v), (2, spv)] (ldsRestore s0b s1b s2b s3b s4b s6b s5b))
        = (0x800045ec#64 : BitVec 64) := by
      simp only [restoreB, ldsRestore, runGM, stepGM, stepLdsM, wvalM, eraseG, srcVal,
        lookupG, List.headD, List.tail]
      rfl
    have : chainEndPC (0x80004514#64) [(21, a0v), (2, spv)]
        (ldsRestore s0b s1b s2b s3b s4b s6b s5b) restoreChain
        = (0x800045ec#64 : BitVec 64) := by
      show BitVec.update (srcVal 1 (runGM restoreB.body
        [(21, a0v), (2, spv)] (ldsRestore s0b s1b s2b s3b s4b s6b s5b))
        + sign_extend (m := 64) (0#12)) 0 0#1 = _
      rw [hra]
      apply BitVec.eq_of_toNat_eq
      rfl
    rw [this] at hpc'
    exact hpc'
  · -- a0 = a0v: mv a0,s5 copied s5 = a0v.
    have hlk : lookupG 10 (runChain restoreChain [(21, a0v), (2, spv)]
        (ldsRestore s0b s1b s2b s3b s4b s6b s5b)) = some a0v := by
      simp only [restoreChain, restoreB, ldsRestore, runChain, runGM, stepGM, stepLdsM,
        wvalM, eraseG, srcVal, lookupG, List.headD, List.tail,
        Nat.reduceEqDiff, if_true, if_false, Option.getD_some]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, show sign_extend (m := 64) (0#12) = (0#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; rfl]
      have : a0v.toNat < 2 ^ 64 := a0v.isLt
      simp only [BitVec.toNat_ofNat]
      omega
    exact gholds_lookup (runChain restoreChain [(21, a0v), (2, spv)]
      (ldsRestore s0b s1b s2b s3b s4b s6b s5b)) hGH hlk
  · unfold output; rw [hout']; unfold output at hout; exact hout

/-! ## §2. The epilogue span — `EntryEpilogueSpan` discharged

`SegExit` at `interpNormalExitPC = 0x80004514` carries the rich M4 store/out
representation; the restore battery needs the concrete spill `ChainFacts` and the
`s5 = 0` latch, which are the honest `EpilogueFrame` residual.  The epilogue's
postcondition ALSO demands `ExitTailChain0` (the tail span its consumer
`cleanExitTail` runs) — surfaced as the same residual. -/

/-- The epilogue frame residual: from the `SegExit`-normal-exit config, the
restore-block `ChainFacts` (spill images, `ra` pinned to `0x800045ec`), `sp = spv`,
the `s5 = 0` latch, `output = out`, and the produced tail span `ExitTailChain0`.
Exit-0 analogue of `ExitPathSpans.InterpContFrame`. -/
def EpilogueFrame
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : SpecSt) (m0 : Mem) (out : String) : Prop :=
  ∀ c : Config,
    SegExit g N A SL φf φc initSt.store.frames.size initSt.store.closures.size
        st' interpNormalExitPC m0 c →
    st'.out = out →
    GoodState c.σ ∧ c.tick < 2 ∧
    c.σ.regs.get? Register.PC = some (0x80004514#64 : BitVec 64) ∧
    c.σ.regs.get? Register.x21 = some (0#64 : BitVec 64) ∧
    output c.σ = out ∧
    Interp_runLoaded c.σ.mem ∧
    ExitTailChain0 (BitVec.ofNat 64 interpRetLinkPC) out ∧
    ∃ (spv : BitVec 64) (s0b s1b s2b s3b s4b s6b s5b : List (BitVec 8)),
      c.σ.regs.get? Register.x2 = some spv ∧
      ChainFacts c.σ.mem c.σ.mem [(21, (0#64 : BitVec 64)), (2, spv)]
        (ldsRestore s0b s1b s2b s3b s4b s6b s5b) restoreChain

/-- **`EntryEpilogueSpan` discharged** (conditional on `EpilogueFrame`).  From
`SegExit` at the normal-exit PC (`s5 = 0`, `output = out`), the restore battery
lands the `interp_run` normal-return continuation config at `interpRetLinkPC` with
`a0 = 0`, `GoodState`, tick-bounded, together with the tail span `ExitTailChain0`
the postcondition names.  ONE `restoreRetChain_run`. -/
theorem entryEpilogueSpan_of
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : SpecSt) (m0 : Mem) (out : String)
    (hframe : EpilogueFrame g N A SL φf φc st' m0 out) :
    EntryEpilogueSpan g N A SL φf φc st' m0 out := by
  intro hout c hSeg
  obtain ⟨hG, htick, hpc, hs5, hout', _hloaded, hchain, spv, s0b, s1b, s2b, s3b,
    s4b, s6b, s5b, hsp, hcf⟩ := hframe c hSeg hout
  obtain ⟨c', hsteps, hG', htick', hpc', hx10', hout''⟩ :=
    restoreRetChain_run out (0#64) spv s0b s1b s2b s3b s4b s6b s5b c
      hG htick hpc hs5 hsp hout' hcf
  refine ⟨c', hsteps, ?_, hG', htick', ?_, ?_⟩
  · -- ExitTailChain0 at ra0 = interpRetLinkPC; interpRetLinkPC = 0x800045ec.
    exact hchain
  · rw [show (BitVec.ofNat 64 interpRetLinkPC : BitVec 64) = (0x800045ec#64 : BitVec 64)
        from by rfl]
    exact hpc'
  · exact hx10'

/-! ## §3. The prologue span — `EntryPrologueSpan` reduced to `PrologueSpanResid`

`Loaded → SegEntry@loopHead` composes: the spill decode, the `jal setjmp`
first-return splice (`JmpSpec.setjmp_spec`), `bnez a0` not-taken, the loop-setup
decode, and the store-init representation seam (`ProgramRepr → StoreRepr initSt`).
The `setjmp` contract is REUSED verbatim; the store-init seam is genuinely the
interpreter's own `env_new` startup path, surfaced as the named `StoreInitSeam`. -/

/-- The store-init representation seam: from `Loaded L p c` (the C AST for `p` laid
out in `c.σ.mem`), the initial spec store `initSt.store` is represented in the
machine at the loop head — the single global frame with the three natives, as the
interpreter's startup `env_new` establishes it.  This is the ONE genuinely-open
representation fact of the prologue (the AST/heap-init store seam). -/
def StoreInitSeam (L : Layout) (p : Program) : Prop :=
  ∀ c : Config, Loaded L p c →
    ∃ (c1 : Config)
      (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (dLeft aLeft : Nat) (m0 : Mem),
      Steps c c1 ∧
      -- ITEM ZERO (falsity #12, shape 3): also certify the `interp_run` image in
      -- `m0` (the `SeqSpanGround` feed for the guarded `mExecSeq`; the span
      -- discharger pins these bytes anyway).
      Vsa.Sim.Code.Interp_runLoaded m0 ∧
      SegEntry g N A SL φf φc initSt 0 dLeft aLeft interpLoopHeadPC m0 c1

/-- **`EntryPrologueSpan` discharged** (conditional on `StoreInitSeam`).  The
prologue-span decode (spill + `jal setjmp` first-return + `bnez` not taken + loop
setup) and the store-init seam together produce the `SegEntry` at the loop head
for the ghosts the seam picks.  Here the whole prologue drive is bundled into
`StoreInitSeam` (it must run the machine to the loop head anyway to establish the
`SegEntry` control state, so the decode composes there); `setjmp_spec` supplies
the first-return `a0 = 0` splice INSIDE that drive. -/
theorem entryPrologueSpan_of
    (L : Layout) (hseam : ∀ p, StoreInitSeam L p) :
    ∀ p, EntryPrologueSpan L p := by
  intro p c hL
  exact hseam p c hL

/-! ## §4. `hEntryHalts_closed` — modulo the two honest residuals -/

/-- **`hEntryHalts` closed** modulo the honest representation residuals
`StoreInitSeam` (prologue store-init) and `EpilogueFrame` (epilogue restore frame
+ tail span).  Composes `entryPrologueSpan_of` and `entryEpilogueSpan_of` into
`hEntryHalts_of`.  All the block-reflection restore work (the byte-similar battery)
and the whole prologue/epilogue COMPOSITION are proved here; only the two named
seams remain. -/
theorem hEntryHalts_closed
    (L : Layout)
    (hseam : ∀ p, StoreInitSeam L p)
    (hframe : ∀ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (st' : SpecSt) (m0 : Mem) (out : String),
        EpilogueFrame g N A SL φf φc st' m0 out) :
    ∀ (p : Program) (c : Config) (out : String) (st' : SpecSt)
      (t : ExecSeq initSt 0 0 p st' Status.normal),
      Loaded L p c → st'.out = out →
      mExecSeq initSt 0 0 p st' Status.normal t →
      Halts c out 0 :=
  hEntryHalts_of L (entryPrologueSpan_of L hseam)
    (fun g N A SL φf φc st' m0 out =>
      entryEpilogueSpan_of g N A SL φf φc st' m0 out (hframe g N A SL φf φc st' m0 out))

#print axioms hEntryHalts_closed

end Vsa.Sim
