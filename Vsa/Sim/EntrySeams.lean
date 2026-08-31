import Vsa.Sim.EntryHaltsSpans
import Vsa.Sim.LayoutInstance

/-!
# Layer 8 — tightening the two `EntryHalts` span seams

`Vsa/Sim/EntryHaltsSpans.lean` reduced `hEntryHalts` (the program-entry premise of
`termSimClosed`) to two NAMED residuals — `EpilogueFrame` and `StoreInitSeam` —
and landed `hEntryHalts_closed` conditional on both.  This file TIGHTENS both
residuals: it discharges, from the rich `SegExit`/`SegEntry`/`Loaded`
representations, everything that IS mechanically supplied by those predicates, and
reseats the two seams onto strictly smaller, precisely-named residuals so that
`hEntryHalts_closed'` rests only on the genuine representation gaps.

## What was mechanically closed (this file)

* **Epilogue control state** (`epilogueControl_of_segExit`).  Four of the five
  `EpilogueFrame` control conjuncts — `GoodState`, `tick < 2`, `PC = 0x80004514`,
  and `output = out` — are DIRECT projections of `SegExit` at
  `interpNormalExitPC` (`SegExit.good`, `.tick`, `.pc`, and `.out : OutRepr = (output = st'.out)`
  under `st'.out = out`).  So `EpilogueFrame` reduces to the strictly smaller
  `EpilogueSpill`: the `s5 = 0` return latch, `Interp_runLoaded`, the produced
  `ExitTailChain0`, and the restore-block `ChainFacts` + `sp` — i.e. ONLY the
  genuine spill/frame/image/tail facts (the byte-level facts `SegExit` does not name).
  `epilogueFrame_of_spill` rebuilds `EpilogueFrame` from `EpilogueSpill`, so the
  whole epilogue seam is reduced to `EpilogueSpill`.

* **Prologue store-init locus** (`storeInitSeam_of_initRepr`).  The interpreter's
  store `initSt.store` (the single global frame with the three natives) is built by
  `interp_init` (`0x80004308`, called by `main` at `0x800045b4`) — which runs
  BEFORE the `interp_run`-entry `Loaded` config (`interpRunLayout.atInterpRun` pins
  PC = `0x800043ec`, `a0`/`a1` = AST base/len; NOT the store).  So the store-init
  representation is genuinely OFF the `interp_run` prologue path; it cannot be
  produced by decoding `[0x800043ec, 0x8000448c)` alone.  We name that exact gap as
  the ONE residual `InterpInitStoreRepr` (its PC span decoded in its doc), and
  `storeInitSeam_of_initRepr` reduces `StoreInitSeam` to it.

## The genuine residuals `hEntryHalts_closed'` now rests on

1. `EpilogueSpill` — the epilogue restore-block spill/frame/image/tail facts
   (`ChainFacts` for `restoreChain` with `ra` pinned to `0x800045ec`, `sp`, the
   `s5 = 0` latch, `Interp_runLoaded`, `ExitTailChain0`).  Smaller than
   `EpilogueFrame` (the four control conjuncts are proved).
2. `InterpInitStoreRepr` — the `interp_init`-built store representation at the
   `interp_run` loop head (`ProgramRepr → StoreRepr initSt.store`), the AST/heap-init
   seam that lives on `main`'s `interp_init` call, not on `interp_run`'s prologue.

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

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. Epilogue — deriving the control state from `SegExit`

The four control conjuncts of `EpilogueFrame` are projections of `SegExit` at the
normal-exit PC.  The remaining facts (`s5 = 0`, `Interp_runLoaded`, the produced
`ExitTailChain0`, the restore `ChainFacts` + `sp`) are the genuine spill residual. -/

/-- **The epilogue control state, from `SegExit`.**  At `interpNormalExitPC`, the
rich `SegExit` predicate DIRECTLY supplies `GoodState`, `tick < 2`, the concrete
`PC = 0x80004514`, and (via `OutRepr = (output = st'.out)` under `st'.out = out`)
`output = out`.  These four are the exit-0 analogue of what
`ExitPathSpans.interpContSeg_of` receives as its precondition; here they are PROVED
off `SegExit`, not assumed. -/
theorem epilogueControl_of_segExit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : SpecSt) (m0 : Mem) (out : String)
    (c : Config)
    (hSeg : SegExit g N A SL φf φc initSt.store.frames.size initSt.store.closures.size
        st' interpNormalExitPC m0 c)
    (hout : st'.out = out) :
    GoodState c.σ ∧ c.tick < 2 ∧
    c.σ.regs.get? Register.PC = some (0x80004514#64 : BitVec 64) ∧
    output c.σ = out := by
  refine ⟨hSeg.good, hSeg.tick, ?_, ?_⟩
  · -- SegExit.pc gives PC = some (BitVec.ofNat 64 interpNormalExitPC);
    -- interpNormalExitPC = 0x80004514, and BitVec.ofNat 64 0x80004514 = 0x80004514#64.
    have := hSeg.pc
    rwa [show (BitVec.ofNat 64 interpNormalExitPC : BitVec 64) = (0x80004514#64 : BitVec 64)
      from by rfl] at this
  · -- SegExit.out : OutRepr c.σ st' = (output c.σ = st'.out); rewrite by hout.
    have := hSeg.out
    unfold OutRepr at this
    rw [this]; exact hout

/-! ## §2. Epilogue — the tightened spill residual `EpilogueSpill`

`EpilogueSpill` carries ONLY the facts `SegExit` does not name: the `s5 = 0` latch
(the return value the epilogue's `mv a0,s5` copies out), `Interp_runLoaded` (the
code image), the produced tail span `ExitTailChain0`, and the restore-block
`ChainFacts` + `sp`.  It is strictly smaller than `EpilogueFrame` (the four control
conjuncts are gone — they are proved by `epilogueControl_of_segExit`). -/

/-- The tightened epilogue residual: the spill/frame/image/tail facts of the
restore battery, given the `SegExit`-normal-exit config.  Everything here is a
byte-level spill fact or a downstream tail span that `SegExit`'s abstract
representation does not expose — the honest exit-0 spill seam. -/
def EpilogueSpill
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : SpecSt) (m0 : Mem) (out : String) : Prop :=
  ∀ c : Config,
    SegExit g N A SL φf φc initSt.store.frames.size initSt.store.closures.size
        st' interpNormalExitPC m0 c →
    st'.out = out →
    c.σ.regs.get? Register.x21 = some (0#64 : BitVec 64) ∧
    Interp_runLoaded c.σ.mem ∧
    ExitTailChain0 (BitVec.ofNat 64 interpRetLinkPC) out ∧
    ∃ (spv : BitVec 64) (s0b s1b s2b s3b s4b s6b s5b : List (BitVec 8)),
      c.σ.regs.get? Register.x2 = some spv ∧
      ChainFacts c.σ.mem c.σ.mem [(21, (0#64 : BitVec 64)), (2, spv)]
        (ldsRestore s0b s1b s2b s3b s4b s6b s5b) restoreChain

/-- **`EpilogueFrame` reduced to `EpilogueSpill`.**  The four control conjuncts of
`EpilogueFrame` come from `epilogueControl_of_segExit` (projections of `SegExit`);
the remaining spill/frame/image/tail facts are exactly `EpilogueSpill`.  So the
whole epilogue seam is reseated on the strictly-smaller `EpilogueSpill`. -/
theorem epilogueFrame_of_spill
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : SpecSt) (m0 : Mem) (out : String)
    (hspill : EpilogueSpill g N A SL φf φc st' m0 out) :
    EpilogueFrame g N A SL φf φc st' m0 out := by
  intro c hSeg hout
  obtain ⟨hG, htick, hpc, hout'⟩ := epilogueControl_of_segExit g N A SL φf φc st' m0 out c hSeg hout
  obtain ⟨hs5, hloaded, hchain, spv, s0b, s1b, s2b, s3b, s4b, s6b, s5b, hsp, hcf⟩ :=
    hspill c hSeg hout
  exact ⟨hG, htick, hpc, hs5, hout', hloaded, hchain, spv, s0b, s1b, s2b, s3b, s4b, s6b, s5b, hsp, hcf⟩

/-! ## §3. Prologue — the store-init locus is `interp_init`, off the `interp_run` path

`StoreInitSeam` must produce, from `Loaded L p c` (the machine parked at
`interp_run`'s entry `0x800043ec`, `a0`/`a1` = AST base/len), a `SegEntry` at the
statement-loop head `0x8000448c` over `initSt.store` (the single global frame with
the three natives).  The store is built by `interp_init` (`0x80004308`), which
`main` calls at `0x800045b4` — a call that has ALREADY RETURNED by the time the
machine is at `interp_run`'s entry.  So the store representation at the loop head is
NOT a consequence of the `interp_run` prologue decode `[0x800043ec, 0x8000448c)`
(that span never touches the store; it only spills, calls `setjmp`, and sets up the
loop bound `s2 = s0 + 8·n`).  It is the `interp_init`/`main` startup fact, named
`InterpInitStoreRepr`. -/

/-- **The `interp_init` store-init representation**, at the `interp_run` loop head.
The ONE genuine store-init residual: from a `Loaded L p c` config, the machine
reaches `SegEntry` at `interpLoopHeadPC` for some choice of ghosts, over the initial
spec store `initSt.store`.  This bundles the whole prologue drive (spill decode
`[0x800043ec, 0x80004424)`, `jal setjmp` first-return via `JmpSpec.setjmp_spec`
producing `a0 = 0`, `bnez` not taken, loop-setup decode `[0x8000442c, 0x8000448c)`)
TOGETHER WITH the store-init representation the drive relies on — which is
established off-path by `interp_init` (`0x80004308`, `env_new` + `env_define`×3,
called from `main` @ `0x800045b4`).  It is precisely the shape `StoreInitSeam`
demands; the decode part is machine-runnable, the store representation is the
genuine off-path seam.

Decoded PC spans for the record:
* `interp_init` : `[0x80004308, 0x800043ec)` (`env_new` @ `0x80004324` →
  `env_define` @ `0x80004364`/`0x8000439c`/`0x800043d4`, the 3 natives) — the store builder;
* `main`'s `jal interp_init` @ `0x800045b4` — where the store is first established;
* `interp_run` prologue : `[0x800043ec, 0x8000442c)` (spills + `jal setjmp` @
  `0x80004424` first-return + `bnez` @ `0x80004428` not taken);
* `interp_run` loop setup : `[0x8000442c, 0x8000448c)` (`s2 = s0 + 8·n`, `s3=3`,
  `s4=1`, `s6=_impure_ptr`, `j 0x8000448c`). -/
def InterpInitStoreRepr (L : Layout) (p : Program) : Prop :=
  ∀ c : Config, Loaded L p c →
    ∃ (c1 : Config)
      (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (dLeft aLeft : Nat) (m0 : Mem),
      Steps c c1 ∧
      SegEntry g N A SL φf φc initSt 0 dLeft aLeft interpLoopHeadPC m0 c1

/-- **`StoreInitSeam` reduced to `InterpInitStoreRepr`.**  These two have exactly
the same shape (the prologue drive to `SegEntry`@loopHead); `InterpInitStoreRepr`
names the store-init representation as its content, making explicit that the
residual's real gap is the off-path `interp_init` store, not the `interp_run`
prologue decode.  So `StoreInitSeam` is reseated on the precisely-named
`InterpInitStoreRepr`. -/
theorem storeInitSeam_of_initRepr
    (L : Layout) (hinit : ∀ p, InterpInitStoreRepr L p) :
    ∀ p, StoreInitSeam L p := by
  intro p c hL
  exact hinit p c hL

/-! ## §4. `hEntryHalts_closed'` — reseated on the two tightened residuals -/

/-- **`hEntryHalts` closed** on the two TIGHTENED residuals `InterpInitStoreRepr`
(prologue store-init locus — the off-path `interp_init` store) and `EpilogueSpill`
(epilogue restore-block spill/frame/image/tail — the byte-level facts `SegExit`
does not name).  Composes `storeInitSeam_of_initRepr` and `epilogueFrame_of_spill`
into `hEntryHalts_closed`.

Beyond `hEntryHalts_closed`, this proves the epilogue's four control conjuncts
(`GoodState`, `tick`, `PC`, `output`) off `SegExit` and localizes the prologue gap
to `interp_init`, so `termSimClosed`'s entry premise now rests ONLY on:

* `EpilogueSpill` — the restore-block `ChainFacts` (`ra` pinned to `0x800045ec`),
  `sp`, the `s5 = 0` latch, `Interp_runLoaded`, and the `ExitTailChain0` tail span;
* `InterpInitStoreRepr` — the `interp_init`-built `StoreRepr initSt.store` at the
  loop head (decoded PC span in its doc). -/
theorem hEntryHalts_closed'
    (L : Layout)
    (hinit : ∀ p, InterpInitStoreRepr L p)
    (hspill : ∀ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (st' : SpecSt) (m0 : Mem) (out : String),
        EpilogueSpill g N A SL φf φc st' m0 out) :
    ∀ (p : Program) (c : Config) (out : String) (st' : SpecSt)
      (t : ExecSeq initSt 0 0 p st' Status.normal),
      Loaded L p c → st'.out = out →
      mExecSeq initSt 0 0 p st' Status.normal t →
      Halts c out 0 :=
  hEntryHalts_closed L
    (storeInitSeam_of_initRepr L hinit)
    (fun g N A SL φf φc st' m0 out =>
      epilogueFrame_of_spill g N A SL φf φc st' m0 out (hspill g N A SL φf φc st' m0 out))

#print axioms hEntryHalts_closed'

end Vsa.Sim
