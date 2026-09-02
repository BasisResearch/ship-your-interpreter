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

-- discipline: allow(R7-conj-tower-def) The predicates in this file are either
-- named-field `structure`s (SegEntryData/SegEntryFields — projected as DATA into
-- the `SegEntry` witness / the seg `SegPre`) or NAMED Prop-valued existential
-- `def`s (SpillLanded/SegLanded/SetjmpSplice/SetjmpGeom + BnezFallthrough/
-- SpRetSurvives). The latter MUST be `def … : Prop := ∃ data, props` rather than
-- `structure`: they carry a reached `Config` (DATA) yet are BUILT from a
-- `Triple`/`setjmp_spec` `Exists` (Type-valued structure ⇒ large elimination
-- forbidden) and CONSUMED in Prop goals (see observation
-- `landing-bundle-must-be-prop-existential`). Each is destructured ONCE at its
-- consumer's binder site via a flat named `obtain` pattern (no `.2.2.2` towers).

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
def SetjmpSplice (σSp : MState) (iSp uSp : Nat) (spSp : BitVec 64) : Prop :=
  ∃ (σ2 : MState) (i2 u2 : Nat),
    Steps ⟨σSp, iSp, uSp⟩ ⟨σ2, i2, u2⟩ ∧
    i2 < 2 ∧
    GoodState σ2 ∧
    σ2.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) ∧
    σ2.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧
    σ2.regs.get? Register.x2 = some spSp ∧
    (∃ w, σ2.regs.get? Register.minstret = some w)

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
  /-- **ITEM ZERO (falsity #12, shape 3), threaded wave 47e**: the `interp_run`
  image is pinned in `m0` (the `SeqSpanGround` feed; the discharger pins these
  bytes anyway — `InterpInit.interpInitStoreRepr_of_drive`'s amended premise). -/
  run_code : Vsa.Sim.Code.Interp_runLoaded m0

/-- **The spill bridge landing.**  What `driveSpillBridge` delivers from the
`Loaded` config: the spill body ≫ `jal setjmp` bridge run to the setjmp entry
`0x80006ffc`, link `x1 = 0x80004428`, the reseated `sp` exposed.  A Prop-valued
existential over the reached config (the `∃ c1 spNew, …` a bridge conclusion is);
consumed by `obtain` (destructuring a Prop into a Prop goal — legal).  It carries
DATA (`c1 : Config`), so it MUST be a Prop-valued `def`, not a `structure … : Prop`
(the WidenMeta gotcha: a `structure … : Prop` cannot project a data field, and a
Type-valued structure cannot be BUILT from a `Triple`'s `Exists` — large
elimination forbidden).  The named destructurer `SpillLanded.elim` below reads it. -/
def SpillLanded (c : Config) : Prop :=
  ∃ (c1 : Config) (spNew : BitVec 64),
    Steps c c1 ∧
    c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64) ∧
    c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64) ∧
    c1.σ.regs.get? Register.x2 = some spNew ∧
    GoodState c1.σ ∧
    c1.tick < 2 ∧
    (∃ w, c1.σ.regs.get? Register.minstret = some w)

/-- **A loop-setup span landing.**  What `driveLoopSetupARow`/`driveLoopSetupBRow`
deliver: the seg run to the span's computed end PC `endPC`, control good.  A
Prop-valued existential over the reached config (same rationale as `SpillLanded`).
Consumed by `obtain`; the named destructurer `SegLanded.elim` reads it. -/
def SegLanded (c : Config) (endPC : BitVec 64) : Prop :=
  ∃ (c' : Config),
    Steps c c' ∧
    c'.σ.regs.get? Register.PC = some endPC ∧
    GoodState c'.σ ∧
    c'.tick < 2 ∧
    (∃ w, c'.σ.regs.get? Register.minstret = some w)

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
  obtain ⟨c1, spNew, s1steps, s1pc, s1ra, s1sp, s1good, s1tick, _s1mi⟩ := hSpill p c hL
  -- 2. setjmp first return (a0 = 0) + bnez not taken → 0x8000442c.
  obtain ⟨σ2, i2, u2, s2steps, s2tick, s2good, s2pc, s2a0, s2sp, s2mi⟩ :=
    hSplice c1 spNew s1pc s1ra s1sp s1good s1tick
  -- 3. loop-setup A → 0x80004438.
  obtain ⟨cA, sAsteps, sApc, sAgood, sAtick, sAmi⟩ :=
    hLoopA ⟨σ2, i2, u2⟩ s2pc s2good s2tick s2mi
  -- 4. loop-setup B → loop head 0x8000448c.
  obtain ⟨cB, sBsteps, sBpc, sBgood, sBtick, sBmi⟩ :=
    hLoopB cA sApc sAgood sAtick sAmi
  -- 5. the off-path SegEntry representation at the loop head.
  have F := hFields cB sBpc sBgood sBtick
  -- compose the four runs (the middle Steps share the same underlying config).
  have hSteps : Steps c cB :=
    (((s1steps.trans s2steps).trans sAsteps).trans sBsteps)
  refine ⟨cB, F.g, F.N, F.A, F.SL, F.φf, F.φc, F.dLeft, F.aLeft, F.m0, hSteps,
    F.run_code, ?_⟩
  have hpcH' : cB.σ.regs.get? Register.PC = some (BitVec.ofNat 64 interpLoopHeadPC) := by
    rw [sBpc]; rfl
  exact
    { good := sBgood
      tick := sBtick
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
  -- re-run the span composition (as `driveToLoopHead_of_spans`), emitting the
  -- amended drive's `Interp_runLoaded m0` conjunct from `SegEntryFields.run_code`.
  obtain ⟨c1, spNew, s1steps, s1pc, s1ra, s1sp, s1good, s1tick, _s1mi⟩ := hSpill p c hL
  obtain ⟨σ2, i2, u2, s2steps, s2tick, s2good, s2pc, s2a0, s2sp, s2mi⟩ :=
    hSplice c1 spNew s1pc s1ra s1sp s1good s1tick
  obtain ⟨cA, sAsteps, sApc, sAgood, sAtick, sAmi⟩ :=
    hLoopA ⟨σ2, i2, u2⟩ s2pc s2good s2tick s2mi
  obtain ⟨cB, sBsteps, sBpc, sBgood, sBtick, sBmi⟩ :=
    hLoopB cA sApc sAgood sAtick sAmi
  have F := hFields cB sBpc sBgood sBtick
  have hSteps : Steps c cB :=
    (((s1steps.trans s2steps).trans sAsteps).trans sBsteps)
  refine ⟨cB, F.g, F.N, F.A, F.SL, F.φf, F.φc, F.dLeft, F.aLeft, F.m0, hSteps,
    F.run_code, ?_⟩
  have hpcH' : cB.σ.regs.get? Register.PC = some (BitVec.ofNat 64 interpLoopHeadPC) := by
    rw [sBpc]; rfl
  exact
    { good := sBgood
      tick := sBtick
      pc := hpcH'
      store := F.mem ▸ F.store
      out := F.out
      mem := F.mem
      frame := F.frame
      depth_budget := F.depth_budget
      arena_budget := F.arena_budget }

#print axioms driveToLoopHead_interpRunLayout

/-! ## §4. DISCHARGING the loop-setup premises from the proved rows

The two `SegLanded`-producing premises `hLoopA`/`hLoopB` above are the *coarse*
interface (they demand a whole seg run from a bare PC).  The concrete drive over
`interpRunLayout` has the two loop-setup spans PROVED as `driveLoopSetupARow` /
`driveLoopSetupBRow`.  This section wires those rows in, reducing each coarse
premise to exactly the seg-entry data the row consumes — the entry `GHolds` pin
list and the memory-decode `ChainFacts` (the honest residuals: a `main`-prologue
register state + a memory decode, neither a consequence of the bare `PC`).

The row-backed producers below are the *tight* interface: supplying them a
`SegLanded` is now equivalent to supplying the seg `SegPre` bundle, and the whole
`Steps`/end-PC content of the span is discharged by the row (no re-run). -/

/-- The seg-entry residual a loop-setup row genuinely needs beyond the bare PC:
the entry `GHolds` pin list `L`, its `KeysOK`, and the memory-decode `ChainFacts`
for the span's chain `seg` (with the entry memory pinned to `m0`).  This is a
`main`-prologue register state (`GHolds`) + a memory decode (`ChainFacts`) — the
per-config off-`Loaded` datum, named-field per the gate. -/
structure SegEntryData (seg : List BBlock) (L : GRegs)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (c : Config) : Prop where
  mem : c.σ.mem = m0
  hL : GHolds c.σ L
  keys : KeysOK (keysG L)
  facts : ChainFacts c.σ.mem c.σ.mem L lds seg

/-- **`hLoopA` discharged by the `driveLoopSetupA` seg via `segToTriple`.**  From
the seg-entry data at loop-setup A's entry (`GHolds [(2,sp),(10,a0)]` + its
`ChainFacts`), the SAME seg the proved row runs (`driveLoopSetupASeg`, ONE
`ChainOK` `decide`, `segToTriple` marshalling) reaches `0x80004438`, delivering a
`SegLanded` that carries the reached config's tick bound (`i' < 2`).  We go through
`segToTriple` directly (rather than the row's `Triple`) ONLY because the row's
`DriveLoopSetupAPost` does not surface `i' < 2` — the reached-config tick bound the
downstream setup-B/loop-head consumers need; it is the identical run, one `decide`,
no re-threaded machine sites. -/
theorem hLoopA_of_row
    (sp a0 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hData : ∀ (c2 : Config),
        c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
        GoodState c2.σ → c2.tick < 2 →
        (∃ w, c2.σ.regs.get? Register.minstret = some w) →
        SegEntryData driveLoopSetupASeg (driveLoopSetupAL sp a0) lds m0 c2) :
    ∀ (c2 : Config),
        c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
        GoodState c2.σ → c2.tick < 2 →
        (∃ w, c2.σ.regs.get? Register.minstret = some w) →
        SegLanded c2 (0x80004438#64) := by
  intro c2 hpc hG htick hmi
  have hd := hData c2 hpc hG htick hmi
  -- The tick-carrying post `Q c' := (control state @0x80004438, tick<2, minstret)`
  -- is EXACTLY `SegLanded c' 0x80004438`'s existential body at the reached config, so
  -- `Triple pre Q` applied to `c2` yields `SegLanded c2 0x80004438` directly.
  have hT : Triple (SegPre driveLoopSetupASeg (driveLoopSetupAL sp a0) lds 0x8000442c#64 m0)
      (fun c' => c'.σ.regs.get? Register.PC = some (0x80004438#64 : BitVec 64) ∧
        GoodState c'.σ ∧ c'.tick < 2 ∧
        (∃ w, c'.σ.regs.get? Register.minstret = some w)) := by
    apply segToTriple driveLoopSetupASeg (driveLoopSetupAL sp a0) lds 0x8000442c#64 m0 _
      (by have h : keysG (driveLoopSetupAL sp a0) = [2, 10] := rfl
          rw [h]; show ChainOK 0x8000442c#64 [2, 10] driveLoopSetupASeg; decide)
    intro σ' i' u' hG' hi' _hmem' hpc' hmi' _hregs
    refine ⟨?_, hG', hi', hmi'⟩
    rw [hpc']; rfl
  obtain ⟨c', hsteps, hpcE, hG', htickE, hmiE⟩ :=
    hT c2 ⟨hG, hd.mem, hpc, hmi, hd.hL, hd.keys, hd.facts, htick⟩
  exact ⟨c', hsteps, hpcE, hG', htickE, hmiE⟩

/-- **`hLoopB` discharged by the `driveLoopSetupB` seg via `segToTriple`.**  From
the seg-entry data at loop-setup B's entry (`GHolds [(2,sp),(3,gp)]` + its
`ChainFacts`), the SAME seg the proved row runs (`driveLoopSetupBSeg`) reaches the
loop head `0x8000448c`, delivering a `SegLanded` carrying the reached-config tick
bound.  Same rationale as `hLoopA_of_row` (the row's post drops `i' < 2`); identical
run, one `decide`. -/
theorem hLoopB_of_row
    (sp gp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hData : ∀ (c3 : Config),
        c3.σ.regs.get? Register.PC = some (0x80004438#64 : BitVec 64) →
        GoodState c3.σ → c3.tick < 2 →
        (∃ w, c3.σ.regs.get? Register.minstret = some w) →
        SegEntryData driveLoopSetupBSeg (driveLoopSetupBL sp gp) lds m0 c3) :
    ∀ (c3 : Config),
        c3.σ.regs.get? Register.PC = some (0x80004438#64 : BitVec 64) →
        GoodState c3.σ → c3.tick < 2 →
        (∃ w, c3.σ.regs.get? Register.minstret = some w) →
        SegLanded c3 (0x8000448c#64) := by
  intro c3 hpc hG htick hmi
  have hd := hData c3 hpc hG htick hmi
  have hT : Triple (SegPre driveLoopSetupBSeg (driveLoopSetupBL sp gp) lds 0x80004438#64 m0)
      (fun c' => c'.σ.regs.get? Register.PC = some (0x8000448c#64 : BitVec 64) ∧
        GoodState c'.σ ∧ c'.tick < 2 ∧
        (∃ w, c'.σ.regs.get? Register.minstret = some w)) := by
    apply segToTriple driveLoopSetupBSeg (driveLoopSetupBL sp gp) lds 0x80004438#64 m0 _
      (by have h : keysG (driveLoopSetupBL sp gp) = [2, 3] := rfl
          rw [h]; show ChainOK 0x80004438#64 [2, 3] driveLoopSetupBSeg; decide)
    intro σ' i' u' hG' hi' _hmem' hpc' hmi' _hregs
    refine ⟨?_, hG', hi', hmi'⟩
    rw [hpc']; rfl
  obtain ⟨c', hsteps, hpcE, hG', htickE, hmiE⟩ :=
    hT c3 ⟨hG, hd.mem, hpc, hmi, hd.hL, hd.keys, hd.facts, htick⟩
  exact ⟨c', hsteps, hpcE, hG', htickE, hmiE⟩

#print axioms hLoopA_of_row
#print axioms hLoopB_of_row

/-! ## §5. DISCHARGING the setjmp splice from `JmpSpec.setjmp_spec`

The `SetjmpSplice` premise is the `jal setjmp` first return.  The landed contract
is `JmpSpec.setjmp_spec` (`setjmp_pre → setjmp_post`, `a0 = 0`, `PC = ra0`).  This
section wires it in, reducing `hSplice` to exactly the setjmp-buffer geometry the
contract's precondition demands (`SetjmpLoaded`, `WinRAM jb`, the 14 live
callee-saved pins, `ra0`-alignment) — the honest off-`interp_run` residual (the
setjmp buffer is `&interp->on_error = a0`, its geometry a `main`/`interp_init`
startup fact, not a consequence of the spill decode).

The splice ALSO absorbs the following `bnez a0` at `0x80004428`: since `setjmp`'s
first passage returns `a0 = 0`, the `bnez` is NOT taken and falls through to
`0x8000442c` — that last not-taken branch step is the named `hBnez` residual (a
single `beq`-class step over the setjmp-post config).  `setjmp_spec` gives the ret;
`hBnez` gives the fallthrough. -/

/-- The not-taken `bnez a0` fallthrough obligation (`a0 = 0` ⇒ falls to
`0x8000442c`), as a single step over the setjmp-post config parked at `0x80004428`
with `a0 = 0`.  Named separately so it reads cleanly inside `SetjmpGeom`'s
existential and can be discharged on its own (one `beq`-class step). -/
def BnezFallthrough (spNew : BitVec 64) : Prop :=
  ∀ (σ' : MState) (i' u' : Nat),
    GoodState σ' → i' < 2 →
    σ'.regs.get? Register.PC = some (0x80004428#64 : BitVec 64) →
    σ'.regs.get? Register.x10 = some (0#64 : BitVec 64) →
    σ'.regs.get? Register.x2 = some spNew →
    (∃ w, σ'.regs.get? Register.minstret = some w) →
    ∃ (σ2 : MState) (i2 u2 : Nat),
      Steps ⟨σ', i', u'⟩ ⟨σ2, i2, u2⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) ∧
      σ2.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧
      σ2.regs.get? Register.x2 = some spNew ∧
      (∃ w, σ2.regs.get? Register.minstret = some w)

/-- The sp-survival residual: `sp = spNew` is preserved across the setjmp call.
This is TRUE (setjmp writes only `x10` + the buffer stores, never `x2`), but
`setjmp_post`'s frame is stated over `NotWrittenJmp`, which EXCLUDES `x2` (the
shared setjmp/longjmp union frame — longjmp writes `x2`), so it is not derivable
from the contract as landed.  Named per observations `setjmp-post-no-sp-frame`. -/
def SpRetSurvives (spNew : BitVec 64) : Prop :=
  ∀ (cR : Config),
    GoodState cR.σ →
    cR.σ.regs.get? Register.PC = some (0x80004428#64 : BitVec 64) →
    cR.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) →
    cR.σ.regs.get? Register.x2 = some spNew

/-- **The setjmp-buffer geometry residual, as a Prop-valued existential.**  It
carries DATA (the buffer address `jb`, the 14 saved values, the ghost frame `g`,
the pinned memory `m0`) so it MUST be a Prop-valued `def`, not a Type-valued
`structure` (a `structure` with a `g : (R:Register)→Option (RegisterType R)` field
next to the 12 `BitVec 64` value fields wedges universe inference; and a Prop-shaped
consumer cannot project a Type-structure's data anyway).  Consumed by `obtain` at
the top of `hSplice_of_setjmpSpec` (destructuring a Prop into a Prop goal — legal).
Exactly `setjmp_pre`'s content beyond the drive's control state, plus the two named
post-side residuals (`SpRetSurvives`, `BnezFallthrough`). -/
def SetjmpGeom (c1 : Config) (spNew : BitVec 64) : Prop :=
  ∃ (jb : BitVec 64)
    (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : BitVec 64)
    (g : (R : Register) → Option (RegisterType R))
    (m0 : Mem),
    c1.σ.mem = m0 ∧
    Code.SetjmpLoaded c1.σ.mem ∧
    c1.σ.regs.get? Register.x10 = some jb ∧
    (0x80004428#64 : BitVec 64).toNat % 4 = 0 ∧
    c1.σ.regs.get? Register.x8 = some s0v ∧
    c1.σ.regs.get? Register.x9 = some s1v ∧
    c1.σ.regs.get? Register.x18 = some s2v ∧
    c1.σ.regs.get? Register.x19 = some s3v ∧
    c1.σ.regs.get? Register.x20 = some s4v ∧
    c1.σ.regs.get? Register.x21 = some s5v ∧
    c1.σ.regs.get? Register.x22 = some s6v ∧
    c1.σ.regs.get? Register.x23 = some s7v ∧
    c1.σ.regs.get? Register.x24 = some s8v ∧
    c1.σ.regs.get? Register.x25 = some s9v ∧
    c1.σ.regs.get? Register.x26 = some s10v ∧
    c1.σ.regs.get? Register.x27 = some s11v ∧
    WinRAM jb ∧
    (∀ R : Register, NotWrittenJmp R → c1.σ.regs.get? R = g R) ∧
    SpRetSurvives spNew ∧
    BnezFallthrough spNew

/-- **`hSplice` discharged by `JmpSpec.setjmp_spec`.**  From the setjmp-buffer
geometry `SetjmpGeom` at the parked setjmp entry, `setjmp_spec`'s FIRST return
(`a0 = 0`, `PC = ra0 = 0x80004428`) runs; then the named not-taken `bnez` step
(`hGeom.bnez`) falls through to loop-setup A's entry `0x8000442c`, producing the
`SetjmpSplice`.  `setjmp_spec` is REUSED verbatim; the only residuals are the
buffer geometry + the single `bnez` step, both genuinely off the spill decode. -/
theorem hSplice_of_setjmpSpec
    (hGeom : ∀ (c1 : Config) (spNew : BitVec 64),
        c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64) →
        c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64) →
        c1.σ.regs.get? Register.x2 = some spNew →
        GoodState c1.σ → c1.tick < 2 →
        SetjmpGeom c1 spNew) :
    ∀ (c1 : Config) (spNew : BitVec 64),
        c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64) →
        c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64) →
        c1.σ.regs.get? Register.x2 = some spNew →
        GoodState c1.σ → c1.tick < 2 →
        SetjmpSplice c1.σ c1.tick c1.steps spNew := by
  intro c1 spNew hpc hra hsp hG htick
  -- Destructure the geometry existential (goal is the Prop `SetjmpSplice`, so this
  -- Prop-into-Prop elimination is legal).
  obtain ⟨jb, s0v, s1v, s2v, s3v, s4v, s5v, s6v, s7v, s8v, s9v, s10v, s11v, g, m0,
      gmem, gloaded, ga0, graA, gs0, gs1, gs2, gs3, gs4, gs5, gs6, gs7, gs8, gs9,
      gs10, gs11, gwin, gframe, gspRet, gbnez⟩ :=
    hGeom c1 spNew hpc hra hsp hG htick
  -- Run `setjmp_spec` (first return) from the geometry.
  obtain ⟨cR, hstepsR, hpostR⟩ :=
    setjmp_spec g jb (0x80004428#64) s0v s1v s2v s3v s4v s5v
      s6v s7v s8v s9v s10v s11v spNew m0 c1
      ⟨hG, gloaded, gmem, hpc, ga0, hra, graA, gs0, gs1, gs2, gs3,
        gs4, gs5, gs6, gs7, gs8, gs9, gs10, gs11, hsp, gwin,
        hG.minstret, htick, gframe⟩
  obtain ⟨hGR, htickR, hpcR, ha0R, _hmemR, hmiR, _hframeR⟩ := hpostR
  -- `sp = spNew` at the setjmp return: the named sp-survival residual (setjmp does not
  -- write x2, but the union-framed post cannot state it — observations
  -- `setjmp-post-no-sp-frame`).
  have hspR : cR.σ.regs.get? Register.x2 = some spNew := gspRet cR hGR hpcR ha0R
  -- Now the not-taken `bnez` fallthrough.
  obtain ⟨σ2, i2, u2, hsteps2, hi2, hG2, hpc2, ha02, hsp2, hmi2⟩ :=
    gbnez cR.σ cR.tick cR.steps hGR htickR hpcR ha0R hspR hmiR
  refine ⟨σ2, i2, u2, ?_, hi2, hG2, hpc2, ha02, hsp2, hmi2⟩
  have hstepsC : Steps ⟨c1.σ, c1.tick, c1.steps⟩ cR := hstepsR
  exact hstepsC.trans hsteps2

#print axioms hSplice_of_setjmpSpec

/-! ## §6. The capstone — `driveToLoopHead_closed` with the discharged premises removed

`driveToLoopHead_interpRunLayout` (§3) demanded FIVE premises, two of which — the
setjmp splice (`hSplice`) and the two loop-setup landings (`hLoopA`/`hLoopB`) — are
now DISCHARGED by the proved rows / the landed `setjmp_spec` (§4/§5).  This capstone
threads those dischargers in, leaving ONLY the honest residuals:

* `hSpill` — the spill-body ≫ `jal setjmp` bridge landing (the `driveSpillBridge`
  row's per-config obligation: a `main`-prologue register state + memory decode);
* `hGeom` — the setjmp-buffer geometry (`SetjmpGeom`: `setjmp_pre`'s content beyond
  the drive's control state, plus the sp-survival + `bnez`-fallthrough residuals,
  all off the `interp_run` prologue path — the `interp`-block/on_error geometry);
* `hDataA` / `hDataB` — the two loop-setup seg-entry data suppliers (`SegEntryData`:
  the entry `GHolds` pin list + memory-decode `ChainFacts` for each span);
* `hFields` — the loop-head `SegEntryFields` (the off-path `interp_init`-built store
  representation `StoreRepr`/`OutRepr` + budgets — consumed, not re-derived).

The `hSplice`/`hLoopA`/`hLoopB` obligations are GONE: they are supplied internally
by `hSplice_of_setjmpSpec hGeom` / `hLoopA_of_row … hDataA` / `hLoopB_of_row … hDataB`.
Everything downstream (`interpInitStoreRepr_of_driveToLoopHead`,
`divEntryDrive_of_driveToLoopHead`, both entry consumers) is unchanged. -/
theorem driveToLoopHead_closed
    (spA a0A : BitVec 64) (ldsA : List (List (BitVec 8)))
    (m0A : Std.ExtHashMap Nat (BitVec 8))
    (spB gpB : BitVec 64) (ldsB : List (List (BitVec 8)))
    (m0B : Std.ExtHashMap Nat (BitVec 8))
    (hSpill : ∀ (p : Program) (c : Config), Loaded interpRunLayout p c → SpillLanded c)
    (hGeom : ∀ (c1 : Config) (spNew : BitVec 64),
        c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64) →
        c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64) →
        c1.σ.regs.get? Register.x2 = some spNew →
        GoodState c1.σ → c1.tick < 2 →
        SetjmpGeom c1 spNew)
    (hDataA : ∀ (c2 : Config),
        c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
        GoodState c2.σ → c2.tick < 2 →
        (∃ w, c2.σ.regs.get? Register.minstret = some w) →
        SegEntryData driveLoopSetupASeg (driveLoopSetupAL spA a0A) ldsA m0A c2)
    (hDataB : ∀ (c3 : Config),
        c3.σ.regs.get? Register.PC = some (0x80004438#64 : BitVec 64) →
        GoodState c3.σ → c3.tick < 2 →
        (∃ w, c3.σ.regs.get? Register.minstret = some w) →
        SegEntryData driveLoopSetupBSeg (driveLoopSetupBL spB gpB) ldsB m0B c3)
    (hFields : ∀ (cH : Config),
        cH.σ.regs.get? Register.PC = some (0x8000448c#64 : BitVec 64) →
        GoodState cH.σ → cH.tick < 2 → SegEntryFields cH) :
    DriveToLoopHead interpRunLayout :=
  driveToLoopHead_interpRunLayout
    hSpill
    (hSplice_of_setjmpSpec hGeom)
    (hLoopA_of_row spA a0A ldsA m0A hDataA)
    (hLoopB_of_row spB gpB ldsB m0B hDataB)
    hFields

#print axioms driveToLoopHead_closed

end Vsa.Sim
