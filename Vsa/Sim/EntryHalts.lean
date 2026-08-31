import Vsa.Sim.TermEntry
import Vsa.Sim.TermSimAssembly
import Vsa.Sim.LayoutInstance

/-!
# Layer 8 — `hEntryHalts` discharged down to two decodable span seams

`TermSimClose.termSimClosed` reduces `InterpSim.term_sim` to the single named
residual `hEntryHalts` (the M6 program-entry bridge):

```
∀ p c out st' t,
  Loaded L p c → st'.out = out →
  mExecSeq initSt 0 0 p st' .normal t → Halts c out 0
```

`Vsa/Sim/TermEntry.lean`'s `entryHalts` already reduced THAT to a single named
`hPrologue` residual (the exit-0 side — `cleanExitTail`/`ExitTailChain0` — is
LANDED there).  This file supplies `hPrologue` for the **concrete**
`interpRunLayout` (`Vsa/Sim/LayoutInstance.lean`), composing it out of the two
genuine `interp_run` span seams around the received `mExecSeq` datum:

```
   [Loaded → SegEntry@loopHead]        (EntryPrologueSpan — G + setjmp-C + store-init)
 ≫ [SegEntry@loopHead → SegExit@exit]  (the mExecSeq Triple the recursor hands us)
 ≫ [SegExit@exit → interp_run cont]    (EntryEpilogueSpan — G, the .normal return)
```

## The decoded `interp_run` entry span (`experiments/disasm.txt`, `interp_run`
   @ `0x800043ec`, symbol `interp_run`):

```
── PROLOGUE (EntryPrologueSpan front) ──────────────────────────────────────
800043ec:  addi sp,sp,-176         -- 176-byte frame
800043f0:  sd   a0,0(sp)           -- spill the interp* / AST-array base
800043f4:  addi a0,a0,16           --   (setjmp buf = interp+16)
800043f8:  sd   ra,168(sp) … 8000441c: sd a2,16(sp)   -- callee-saved + arg spills
80004424:  jal  setjmp             -- CALL setjmp  (SETJMP CALLEE SEAM)
── setjmp FIRST return: a0 = 0 ─────────────────────────────────────────────
80004428:  bnez a0,80004508        -- a0 = 0 ⇒ NOT taken (first return)  (fallthrough)
8000442c:  ld   a5,16(sp)          -- a5 = n (statement count)
80004430:  mv   s5,a0              -- s5 := a0 = 0   (the clean return value latch)
80004434:  blez a5,80004514        -- n ≤ 0 ⇒ empty program: jump to epilogue
80004438:  ld   a5,16(sp) …        -- s0 := AST base; s2 := s0 + 8·n (loop bound);
80004454:  j    8000448c           --   s3:=3; s4:=1; s6:=_impure_ptr; → LOOP HEAD
── LOOP HEAD (= SegEntry entry PC) ─────────────────────────────────────────
8000448c:  ld   a5,8(sp); ld s1,0(s0); …  -- the top-level statement dispatch loop;
           …                               --   body calls exec_stmt / value_print;
8000447c/80004480/80004488:  the .normal back-edge/exit tests.
── NORMAL EXIT (= SegExit exit PC) ─────────────────────────────────────────
80004488:  beq  s0,s2,80004514     -- s0 = loop bound ⇒ program done → epilogue
── EPILOGUE (EntryEpilogueSpan) ────────────────────────────────────────────
80004514:  ld   ra,168(sp) … 8000452c: ld s6,112(sp)
80004530:  mv   a0,s5              -- a0 := s5 = 0   (the clean interp_run return)
80004534:  ld   s5,120(sp); addi sp,sp,176
8000453c:  ret                     -- jr ra → 0x800045ec (main's jal interp_run link)
```

## What is a genuine seam vs. what is composed

* **`EntryPrologueSpan`** — the `Loaded → SegEntry@loopHead` Triple.  This carries
  the **G-class** `Loaded ↔ SegEntry` unification (from `interpRunLayout.atInterpRun`:
  PC = `0x800043ec`, `a0`/`a1` = AST base/len; establish `SegEntry` control state,
  the ghost frame, and — the genuine open work — the **store-init representation
  seam**: `ProgramRepr c.σ.mem a n p` ⟹ `StoreRepr … initSt.store` at the loop
  head, i.e. the single global frame with the three natives bound), the **C-class**
  `jal setjmp` callee splice (`setjmp` returns `0` on the first, non-`longjmp`
  entry — the `bnez a0` is NOT taken), and the straight-line loop-setup decode
  (`0x8000442c…0x8000448c`).  Held as a NAMED typed premise: it is discharged by
  the prologue-span decode (block-reflection over `[0x800043ec, 0x8000448c)`),
  the `setjmp` contract (`a0 ↦ 0` first-return), and `programRepr_to_storeRepr_init`
  (the AST/heap-init store seam).
* **the `mExecSeq` Triple** — handed to us by the `term_sim` recursor over the M4
  case bundle; instantiated at the layout ghosts the prologue produces and at
  `p = loopHeadPC`, `q = normalExitPC` (both FREE in `mExecSeq`'s `∀ p q`).
* **`EntryEpilogueSpan`** — the `SegExit@exit → interp_run-cont` Triple: the
  `.normal` epilogue (`0x80004514…0x8000453c`), landing at `ra0 = 0x800045ec`
  (main's `jal interp_run` link) with `a0 = s5 = 0`, `GoodState`, tick-bounded,
  `output = st'.out`, PLUS `ExitTailChain0 ra0 out` (the exit-0 tail residual,
  discharged concretely by `TermEntry.cleanExitTail`).  Pure straight-line
  restore + `ret`; block-reflection over `[0x80004514, 0x8000453c]`.

Composing `EntryPrologueSpan ≫ mExecSeq ≫ EntryEpilogueSpan` produces exactly the
`hPrologue` shape `entryHalts` consumes; `entryHalts` then produces the
`hEntryHalts` type `termSimClosed` demands.  So `hEntryHalts` is reduced to:

* `EntryPrologueSpan` (prologue decode + `setjmp` spec + store-init seam),
* `EntryEpilogueSpan` (epilogue decode + the `ExitTailChain0` tail residual).

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

set_option maxHeartbeats 400000
set_option maxRecDepth 1000000

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## The concrete span PCs (`interp_run`, `experiments/disasm.txt`) -/

/-- The top-level statement-loop head PC — where the `j 0x8000448c` at
`0x80004454` lands, and the PC at which the `mExecSeq` `SegEntry` motive applies
(the store representation established, the loop bound `s2 = s0 + 8·n` set). -/
def interpLoopHeadPC : Nat := 0x8000448c

/-- The normal-loop-completion PC — where the loop's `beq s0,s2` back-edge test
falls through to on program completion (`SegExit` exit PC).  On the `.normal`
path the return latch `s5 = 0` is carried into the epilogue. -/
def interpNormalExitPC : Nat := 0x80004514

/-- `main`'s `jal interp_run` link (`0x800045e8: jal interp_run` → next PC): the
`interp_run` normal-return continuation `ra0` that `ExitTailChain0`/`cleanExitTail`
consume. -/
def interpRetLinkPC : Nat := 0x800045ec

/-! ## Seam 1 — `EntryPrologueSpan` (Loaded → SegEntry@loopHead)

The prologue decode + `setjmp` first-return + store-init unification, packaged as
the `∃`-of-ghosts Triple postcondition landing `SegEntry` at the loop head.  This
is a NAMED typed premise: what discharges it is spelled out in the module doc
(block-reflection over `[0x800043ec, 0x8000448c)`, the `setjmp` contract, and the
`ProgramRepr → StoreRepr initSt` store-init seam). -/

/-- **The prologue span**, as a residual over the concrete `interpRunLayout`.
From a `Loaded`-config at `interp_run`'s entry, the machine runs the prologue
(frame setup, `jal setjmp` first-return with `a0 = 0`, `bnez` not taken, loop
setup) to the statement-loop head, establishing `SegEntry` there for SOME choice
of the layout ghosts, at PC `interpLoopHeadPC`, over the initial spec store
`initSt.store` (with `st = initSt`, `d = 0`, the global scope `env = 0`).

The ghosts (`g/N/A/SL/φf/φc/dLeft/aLeft/m0`) are `∃`-produced by the prologue (it
picks the concrete image geometry — via `LayoutInstance.geomFactsL` — and the
initial `StoreRepr` witness maps).  They are then fed to the `mExecSeq` Triple. -/
def EntryPrologueSpan (L : Layout) (p : Program) : Prop :=
  ∀ (c : Config), Loaded L p c →
    ∃ (c1 : Config)
      (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (dLeft aLeft : Nat) (m0 : Mem),
      Steps c c1 ∧
      -- the `∃`-bound ghost bundle is carried out so the SAME ghosts thread the
      -- `mExecSeq` Triple (`hbody`) and the epilogue span (`EntryEpilogueSpan`).
      SegEntry g N A SL φf φc initSt 0 dLeft aLeft interpLoopHeadPC m0 c1

/-! ## Seam 2 — `EntryEpilogueSpan` (SegExit@exit → interp_run continuation)

The `.normal` epilogue decode: from `SegExit` at the normal-loop-completion PC —
for the SAME ghosts the prologue produced, over the final spec store `st'.store`
— the machine runs the restore span + `ret` to `interp_run`'s return continuation
`ra0 = interpRetLinkPC` with `a0 = 0`, `GoodState`, tick-bounded, and
`output = st'.out`, together with the exit-0 tail residual `ExitTailChain0`.

Pure straight-line restore + `ret` (`[0x80004514, 0x8000453c]`), plus the exit-0
tail residual `TermEntry.ExitTailChain0` (discharged by `cleanExitTail`). -/

/-- **The epilogue span**, parameterized over the ghost bundle the prologue
produced.  Landing the `interp_run` normal-return continuation config the tail
consumes. -/
def EntryEpilogueSpan
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : SpecSt) (m0 : Mem) (out : String) : Prop :=
  st'.out = out →
    Triple
      (SegExit g N A SL φf φc initSt.store.frames.size initSt.store.closures.size
        st' interpNormalExitPC m0)
      (fun c => ExitTailChain0 (BitVec.ofNat 64 interpRetLinkPC) out ∧
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 interpRetLinkPC) ∧
        c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64))

/-! ## `hPrologue` assembled from the two spans + the `mExecSeq` datum -/

/-- **The `hPrologue` residual for the concrete `interpRunLayout`**, assembled
from `EntryPrologueSpan` and `EntryEpilogueSpan` (both NAMED, discharged by span
decode + the `setjmp`/store-init/`ExitTailChain0` residuals documented above),
composed AROUND the `mExecSeq` Triple the `term_sim` recursor hands us.

This is EXACTLY the `hPrologue` premise `TermEntry.entryHalts` consumes: from
`Loaded L p c`, `st'.out = out`, and the whole-program `.normal` `mExecSeq`
datum, produce the `interp_run` normal-return continuation config (`Steps c c1`,
`ExitTailChain0`, and the continuation control state with `a0 = 0`).

The composition is `callSeg`-shaped: prologue span (`Steps c c1` to `SegEntry`)
≫ `mExecSeq` (instantiated at the prologue's ghosts, `p = loopHeadPC`,
`q = normalExitPC`, giving `SegEntry → SegExit`) ≫ epilogue span
(`SegExit → continuation`). -/
theorem hPrologue_of
    (L : Layout)
    (hPre : ∀ p, EntryPrologueSpan L p)
    (hEpi : ∀ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (st' : SpecSt) (m0 : Mem) (out : String),
        EntryEpilogueSpan g N A SL φf φc st' m0 out) :
    ∀ (p : Program) (c : Config) (out : String) (st' : SpecSt)
      (t : ExecSeq initSt 0 0 p st' Status.normal),
      Loaded L p c → st'.out = out →
      mExecSeq initSt 0 0 p st' Status.normal t →
      ∃ (ra0 : BitVec 64) (c1 : Config),
        Steps c c1 ∧ ExitTailChain0 ra0 out ∧
        (GoodState c1.σ ∧ c1.tick < 2 ∧
          c1.σ.regs.get? Register.PC = some ra0 ∧
          c1.σ.regs.get? Register.x10 = some (0#64 : BitVec 64)) := by
  intro p c out st' t hL hout hm
  -- 1. Prologue span: Loaded → SegEntry@loopHead, producing the layout ghosts.
  obtain ⟨cH, g, N, A, SL, φf, φc, dLeft, aLeft, m0, hstepsH, hSeg⟩ := hPre p c hL
  -- 2. The `mExecSeq` Triple at those ghosts, `p := loopHeadPC`, `q := exitPC`.
  --    (`mExecSeq` quantifies its entry/exit PCs `p q : Nat` universally.)
  have hbody :
      Triple
        (SegEntry g N A SL φf φc initSt 0 dLeft aLeft interpLoopHeadPC m0)
        (SegExit g N A SL φf φc initSt.store.frames.size initSt.store.closures.size
          st' interpNormalExitPC m0) :=
    hm g N A SL φf φc dLeft aLeft interpLoopHeadPC interpNormalExitPC m0
  -- 3. Epilogue span: SegExit@exit → interp_run continuation (+ the tail residual).
  have hepi := hEpi g N A SL φf φc st' m0 out hout
  -- Compose: run the body Triple from cH, then the epilogue Triple.
  obtain ⟨cE, hstepsE, hSegExit⟩ := hbody cH hSeg
  obtain ⟨cR, hstepsR, hchain, hgood, htick, hpc, hx10⟩ := hepi cE hSegExit
  exact ⟨BitVec.ofNat 64 interpRetLinkPC, cR,
    (hstepsH.trans hstepsE).trans hstepsR, hchain, hgood, htick, hpc, hx10⟩

/-! ## `hEntryHalts` — the exact `termSimClosed` residual, discharged -/

/-- **`hEntryHalts` discharged** (conditional on the two span seams).  Composes
`hPrologue_of` with `TermEntry.entryHalts` to produce EXACTLY the
`termSimClosed.hEntryHalts` type: from `Loaded L p c`, `st'.out = out`, and the
whole-program `.normal` `mExecSeq` datum, the machine halts cleanly with exit
code 0 printing `out`.

Reduced to `EntryPrologueSpan` (prologue decode + `setjmp` first-return + the
`ProgramRepr → StoreRepr initSt` store-init seam) and `EntryEpilogueSpan`
(epilogue decode + `ExitTailChain0`).  The exit-store → HTIF-halt-0 core
(`exitStoreHalts0`), the clean-exit tail (`cleanExitTail`), and the whole
prologue/epilogue COMPOSITION are all proved here + in `TermEntry`; only the two
straight-line span decodes and the `setjmp`/store-init/`ExitTailChain0` typed
residuals remain. -/
theorem hEntryHalts_of
    (L : Layout)
    (hPre : ∀ p, EntryPrologueSpan L p)
    (hEpi : ∀ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (st' : SpecSt) (m0 : Mem) (out : String),
        EntryEpilogueSpan g N A SL φf φc st' m0 out) :
    ∀ (p : Program) (c : Config) (out : String) (st' : SpecSt)
      (t : ExecSeq initSt 0 0 p st' Status.normal),
      Loaded L p c → st'.out = out →
      mExecSeq initSt 0 0 p st' Status.normal t →
      Halts c out 0 :=
  entryHalts L (hPrologue_of L hPre hEpi)

end Vsa.Sim
