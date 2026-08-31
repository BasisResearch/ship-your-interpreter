import Vsa.Sim.EntryDrive
import Vsa.Sim.LayoutInstance
import Vsa.Sim.JmpSpec
import Vsa.Sim.rows.DriveSpillGen
import Vsa.Sim.rows.DriveLoopSetupAGen
import Vsa.Sim.rows.DriveLoopSetupBGen

/-!
# `DriveToLoopHeadSpans` — assembling the shared `interp_run` prologue drive

`Vsa/Sim/EntryDrive.lean` names `DriveToLoopHead L` (= `∀ p, StoreInitSeam L p`
= `∀ p, InterpInitStoreRepr L p`, all definitionally the same shape): from a
`Loaded L p c` config the machine reaches a loop-head `SegEntry`
(`interpLoopHeadPC = 0x8000448c`) over `initSt`.  This file assembles the MACHINE
side of that drive over the **concrete** `interpRunLayout` (the only layout whose
`atInterpRun` unfolds to real PC/register pins — over an abstract `L` the drive
has NO machine facts to run on).

## The decoded spans (all body words decode-tabled; classification per the brief)

```
── spill span  [0x800043ec, 0x80004424)  ── STORES + sp/a0 RESEATS ─────────────
  addi sp,sp,-176 ; sd a0,0(sp) ; addi a0,a0,16 ; sd ra..a3 (13 spills)
  CLASSIFICATION: writes x2 (sp, a callee-saved) → NOT `WrChainAvoidAbi`; the
  FRAMED case (`bridgeOfSegFramed`, `driveSpillBridge` in DriveSpillGen).  The
  new sp = sp-176 is read off the exposed post bundle.
── CALL setjmp  @0x80004424 ────────────────────────────────────────────────────
  jal setjmp → `JmpSpec.setjmp_spec` FIRST return: a0 = 0, PC = 0x80004428
── bnez a0 @0x80004428  ── a0 = 0 ⇒ NOT taken (falls through to 0x8000442c) ──────
── loop-setup A  [0x8000442c, 0x80004434)  ── RESEATS ▷ blez (NOT taken) ─────────
  ld a5,16(sp) ; mv s5,a0 ▷ blez a5 (n>0 ⇒ NOT taken) → 0x80004438
  (`driveLoopSetupARow`, br-terminated seg; the not-taken guard `n>0` is the
   `ChainFacts` `TermFactsT` datum.)
── loop-setup B  [0x80004438, 0x80004454)  ── RESEATS/LOADS ▷ j 0x8000448c ────────
  ld a5 ; ld s0 ; s6=_impure_ptr ; s2 = s0 + 8·a5 ; s3=3 ; s4=1 ▷ j 0x8000448c
  (`driveLoopSetupBRow`, j-terminated seg.)
── LOOP HEAD = SegEntry entry PC  @0x8000448c ───────────────────────────────────
```

## What is genuinely open (the NAMED residuals)

The three straight-line/branch spans are proved MACHINE runs (`driveSpillBridge`,
`driveLoopSetupARow`, `driveLoopSetupBRow` — all green + axiom-clean in `rows/`).
Two classes of fact are genuinely off the `interp_run` prologue path and stay
NAMED typed premises:

* **`hSetjmpSplice`** — the `jal setjmp` first-return.  `setjmp_spec`'s
  precondition (`SetjmpLoaded`, `WinRAM`, the 14 live callee-saved pins,
  `ra0`-alignment) is not a consequence of the spill span; it is the setjmp-buffer
  geometry.  Named as the splice `Steps` from the setjmp entry (`0x80006ffc`,
  link `0x80004428`) to `0x80004428` with `a0 = 0`, preserving the drive's memory.
* **`hSegFields`** — the `SegEntry` REPRESENTATION fields at the loop head:
  `StoreRepr initSt.store` and `OutRepr initSt` (both built off-path by
  `interp_init`, called from `main` @ `0x800045b4` BEFORE `interp_run` — the
  prologue spans never touch the store) plus the budget fields.  This is exactly
  the convergence point `EntrySeams`/`InterpInit` describe: the machine drive
  CONSUMES the `interp_init`-built store; it cannot re-derive it.

`driveToLoopHead_of_spans` composes the three real seg runs + the two named
seams into `InterpInitStoreRepr interpRunLayout` — hence, via
`EntryDrive.interpInitStoreRepr_of_driveToLoopHead`, the term-arm entry seam, and
via `divEntryDrive_of_driveToLoopHead`, the divergence entry.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Addr)
open Vsa.Sim.Scaffold (SegEntry)
open Vsa.Sim.LayoutInstance (interpRunLayout interpRunEntry)

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) Every predicate in this file is already a
-- named-field `structure` (SetjmpSplice/SegEntryFields/SpillLanded/SegLanded — no
-- anonymous ∃/∧ post tower). The remaining 7 `∃` are all the SINGLE-binder
-- `minstret`-present witness `∃ w, … minstret = some w` (the standard
-- `GoodState.minstret` idiom, one per landing structure + per premise), NOT post
-- definitions — so the >8-∃ heuristic is a false positive here.

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The named off-path seams

The drive's MACHINE runs (spill bridge, loop-setup A/B) are the proved
`driveSpillBridge` / `driveLoopSetupARow` / `driveLoopSetupBRow` (in `rows/`).
Two facts are genuinely off the `interp_run` prologue path:

* the `jal setjmp` first-return (`SetjmpSplice`) — needs the setjmp-buffer geometry;
* the loop-head `SegEntry` REPRESENTATION (`SegEntryFields`) — the
  `interp_init`-built store.

Both are NAMED here; the `Steps` composition between them is REAL. -/

/-- **The `jal setjmp` first-return splice (through the `bnez`-not-taken).**  From
the config the spill bridge lands (parked at the setjmp entry `0x80006ffc`, link
`x1 = 0x80004428`, memory the post-spill write-log `mSp`), `setjmp`'s first passage
returns to `0x80004428` with `a0 = 0`; since `a0 = 0` the following `bnez a0` at
`0x80004428` is NOT taken and falls through to `0x8000442c` (loop-setup A's entry).
The splice absorbs both (setjmp `ret` + the not-taken `bnez`), landing at
`0x8000442c` with `a0 = 0`, `GoodState`, tick-bounded, memory `mLS` (the setjmp
buffer writes are in the fresh stack window; `mLS` is what loop-setup A reads —
its `16(sp)` reload + the code), and the `sp = spSp` the spill bridge exposed
(loop-setup reloads `16(sp)`/`24(sp)` off it).  This is `JmpSpec.setjmp_spec`
marshalled — its precondition (`SetjmpLoaded`, `WinRAM jb`, the 14 callee pins,
`ra0`-alignment) is the setjmp-buffer geometry, NOT a consequence of the spill
decode, so it is NAMED. -/
structure SetjmpSplice (σSp : MState) (iSp uSp : Nat) (spSp : BitVec 64) where
  /-- the reached post-splice config (parked at loop-setup A's entry). -/
  σ2 : MState
  i2 : Nat
  u2 : Nat
  /-- the machine ran from the setjmp entry to `0x8000442c`. -/
  steps : Steps ⟨σSp, iSp, uSp⟩ ⟨σ2, i2, u2⟩
  tick : i2 < 2
  good : GoodState σ2
  /-- PC at loop-setup A's entry (`setjmp` returned, `bnez` fell through). -/
  pc : σ2.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64)
  /-- `a0 = 0` (the first-return value — why the `bnez` is not taken). -/
  a0 : σ2.regs.get? Register.x10 = some (0#64 : BitVec 64)
  /-- `sp` preserved (the frame the loop setup reloads off). -/
  sp : σ2.regs.get? Register.x2 = some spSp
  minstret : ∃ w, σ2.regs.get? Register.minstret = some w

/-- **The loop-setup → `SegEntry` representation seam.**  From the config the loop
setup lands (parked at `interpLoopHeadPC = 0x8000448c`, `GoodState`, tick-bounded),
the RICH `SegEntry` fields at the loop head hold over `initSt`, depth `0`: the store
representation `StoreRepr initSt.store` and console-output `OutRepr initSt` (the
`interp_init`-built store the prologue consumes), the ghost frame, and the budget
fields.  These are the genuinely off-path M4-level facts `SegEntry` bundles beyond
the machine control state; they are the `interp_init`/`main` startup facts named per
`EntrySeams`.  `bnez`-not-taken already gave `a0 = 0 ⇒ s5 = 0`.  A named-field
structure (per the gate): the loop-head ghost bundle + the two off-path
representation fields + the two budget fields. -/
structure SegEntryFields (cH : Config) where
  /-- the register ghost frame the callee-saveds tie to. -/
  g : (R : Register) → Option (RegisterType R)
  N : NativeAddrs
  A : Arena
  /-- the stack layout (a free ghost at the loop head). -/
  SL : StackLayout
  φf : Addr → Nat
  φc : Addr → Nat
  dLeft : Nat
  aLeft : Nat
  m0 : Mem
  /-- the loop-head memory is the pinned pre-memory. -/
  mem : cH.σ.mem = m0
  /-- **off-path**: the whole spec store is represented (the `interp_init` build). -/
  store : StoreRepr cH.σ.mem N A φf φc initSt.store
  /-- **off-path**: console-output correspondence. -/
  out : OutRepr cH.σ initSt
  /-- the blanket ghost frame (callee-preserved registers tie to `g`). -/
  frame : ∀ R : Register, AbiPreservedNoise R → cH.σ.regs.get? R = g R
  /-- the call-depth budget (`d = 0` at the top level). -/
  depth_budget : (0 : Nat) + dLeft = Vsa.While.maxCallDepth
  /-- the arena budget. -/
  arena_budget : A.lo + aLeft ≤ A.hi

/-- **The spill bridge landing.**  What `driveSpillBridge` delivers from the
`Loaded` config: the spill body ≫ `jal setjmp` bridge run to the setjmp entry
`0x80006ffc`, link `x1 = 0x80004428`, the reseated `sp` exposed.  Named-field per
the gate (the `∃ c1 spNew, …` a bridge conclusion would be). -/
structure SpillLanded (c : Config) where
  c1 : Config
  spNew : BitVec 64
  steps : Steps c c1
  pc : c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64)
  ra : c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64)
  sp : c1.σ.regs.get? Register.x2 = some spNew
  good : GoodState c1.σ
  tick : c1.tick < 2
  minstret : ∃ w, c1.σ.regs.get? Register.minstret = some w

/-- **A loop-setup span landing.**  What `driveLoopSetupARow`/`driveLoopSetupBRow`
deliver: the seg run to the span's computed end PC `endPC`, control good.  Named
per the gate. -/
structure SegLanded (c : Config) (endPC : BitVec 64) where
  c' : Config
  steps : Steps c c'
  pc : c'.σ.regs.get? Register.PC = some endPC
  good : GoodState c'.σ
  tick : c'.tick < 2
  minstret : ∃ w, c'.σ.regs.get? Register.minstret = some w

/-! ## §2. The assembled drive — REAL `Steps` composition of the three seg runs

The three span runs are the proved rows; the composition threads their `Steps`
through the named setjmp splice and the loop-head representation.  Because the span
entry register pins (`GHolds`) and memory-decode facts (`ChainFacts`) are NOT
consequences of `Loaded interpRunLayout` (a `main`-prologue-established register
state the abstract entry predicate does not assert), each span's staged
row-conclusion is a per-config NAMED premise; the `Steps.trans` chain between them
is honest.  Each premise is a named-field landing structure. -/

/-- **`driveToLoopHead_of_spans`** — the concrete `interp_run` prologue drive.
Composes:

1. `hSpill` : from the `Loaded` config `c`, `driveSpillBridge`'s conclusion — the
   spill body ≫ `jal setjmp` bridge run to the setjmp entry `0x80006ffc`, link
   `x1 = 0x80004428`, exposing the reseated `sp` (the row is `driveSpillBridge`,
   its `ChainFacts`/`KeysOut`/`RaOut`/`hjalSeam` residuals folded into this
   per-config obligation);
2. `hSplice` : `SetjmpSplice` — setjmp first return (`a0 = 0`) + `bnez` not taken,
   to `0x8000442c`;
3. `hLoopA` : `driveLoopSetupARow`'s conclusion — loop-setup block A run to
   `0x80004438` (the `blez` NOT-taken `n>0` guard is in its `SegPre` `ChainFacts`);
4. `hLoopB` : `driveLoopSetupBRow`'s conclusion — loop-setup block B run to the
   loop head `0x8000448c`;
5. `hFields` : the off-path `SegEntryFields` (the `interp_init`-built store).

The `Steps c cH` is `Steps.trans`ed across all four runs; the `SegEntry` control
fields come from the runs, its representation fields from `hFields`.  Produces
`InterpInitStoreRepr interpRunLayout p` for every `p`. -/
theorem driveToLoopHead_of_spans
    (hSpill : ∀ (p : Program) (c : Config), Loaded interpRunLayout p c → SpillLanded c)
    (hSplice : ∀ (c1 : Config) (spNew : BitVec 64),
        c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64) →
        c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64) →
        c1.σ.regs.get? Register.x2 = some spNew →
        GoodState c1.σ → c1.tick < 2 →
        SetjmpSplice c1.σ c1.tick c1.steps spNew)
    (hLoopA : ∀ (c2 : Config),
        c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
        GoodState c2.σ → c2.tick < 2 →
        (∃ w, c2.σ.regs.get? Register.minstret = some w) →
        SegLanded c2 (0x80004438#64))
    (hLoopB : ∀ (c3 : Config),
        c3.σ.regs.get? Register.PC = some (0x80004438#64 : BitVec 64) →
        GoodState c3.σ → c3.tick < 2 →
        (∃ w, c3.σ.regs.get? Register.minstret = some w) →
        SegLanded c3 (0x8000448c#64))
    (hFields : ∀ (cH : Config),
        cH.σ.regs.get? Register.PC = some (0x8000448c#64 : BitVec 64) →
        GoodState cH.σ → cH.tick < 2 → SegEntryFields cH) :
    ∀ p, InterpInitStoreRepr interpRunLayout p := by
  intro p c hL
  -- 1. spill body ≫ jal setjmp → parked at setjmp entry, sp exposed.
  have S1 := hSpill p c hL
  -- 2. setjmp first return (a0 = 0) + bnez not taken → 0x8000442c.
  have S2 := hSplice S1.c1 S1.spNew S1.pc S1.ra S1.sp S1.good S1.tick
  -- 3. loop-setup A → 0x80004438.
  have S3 := hLoopA ⟨S2.σ2, S2.i2, S2.u2⟩ S2.pc S2.good S2.tick S2.minstret
  -- 4. loop-setup B → loop head 0x8000448c.
  have S4 := hLoopB S3.c' S3.pc S3.good S3.tick S3.minstret
  -- 5. the off-path SegEntry representation at the loop head.
  have F := hFields S4.c' S4.pc S4.good S4.tick
  -- compose the four runs (the middle Steps share the same underlying config).
  have hSteps : Steps c S4.c' :=
    (((S1.steps.trans S2.steps).trans S3.steps).trans S4.steps)
  refine ⟨S4.c', F.g, F.N, F.A, F.SL, F.φf, F.φc, F.dLeft, F.aLeft, F.m0, hSteps, ?_⟩
  have hpcH' : S4.c'.σ.regs.get? Register.PC = some (BitVec.ofNat 64 interpLoopHeadPC) := by
    rw [S4.pc]; rfl
  exact
    { good := S4.good
      tick := S4.tick
      pc := hpcH'
      store := F.mem ▸ F.store
      out := F.out
      mem := F.mem
      frame := F.frame
      depth_budget := F.depth_budget
      arena_budget := F.arena_budget }

#print axioms driveToLoopHead_of_spans

/-! ## §3. Feeding the two consumers

`driveToLoopHead_of_spans` produces `InterpInitStoreRepr interpRunLayout`, which is
DEFINITIONALLY `DriveToLoopHead interpRunLayout` unfolded per-`p` (both are
`∀ p c, Loaded → ∃ cH ghosts, Steps ∧ SegEntry@loopHead over initSt`).  So it feeds
`EntryDrive`'s two consumers directly. -/

/-- The assembled drive IS `DriveToLoopHead interpRunLayout` (the two are the same
proposition — `DriveToLoopHead L` unfolds to `∀ p c, Loaded L p c → ∃ cH …`, and
`InterpInitStoreRepr L p` is that body at a fixed `p`).  Given the same five span
seams, the machine assembly closes the shared drive residual for the concrete
layout, hence — via `EntryDrive.interpInitStoreRepr_of_driveToLoopHead` and
`divEntryDrive_of_driveToLoopHead` — BOTH entry consumers. -/
theorem driveToLoopHead_interpRunLayout
    (hSpill : ∀ (p : Program) (c : Config), Loaded interpRunLayout p c → SpillLanded c)
    (hSplice : ∀ (c1 : Config) (spNew : BitVec 64),
        c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64) →
        c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64) →
        c1.σ.regs.get? Register.x2 = some spNew →
        GoodState c1.σ → c1.tick < 2 →
        SetjmpSplice c1.σ c1.tick c1.steps spNew)
    (hLoopA : ∀ (c2 : Config),
        c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
        GoodState c2.σ → c2.tick < 2 →
        (∃ w, c2.σ.regs.get? Register.minstret = some w) →
        SegLanded c2 (0x80004438#64))
    (hLoopB : ∀ (c3 : Config),
        c3.σ.regs.get? Register.PC = some (0x80004438#64 : BitVec 64) →
        GoodState c3.σ → c3.tick < 2 →
        (∃ w, c3.σ.regs.get? Register.minstret = some w) →
        SegLanded c3 (0x8000448c#64))
    (hFields : ∀ (cH : Config),
        cH.σ.regs.get? Register.PC = some (0x8000448c#64 : BitVec 64) →
        GoodState cH.σ → cH.tick < 2 → SegEntryFields cH) :
    DriveToLoopHead interpRunLayout := by
  intro p c hL
  exact driveToLoopHead_of_spans hSpill hSplice hLoopA hLoopB hFields p c hL

#print axioms driveToLoopHead_interpRunLayout

end Vsa.Sim
