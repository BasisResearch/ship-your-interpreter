import Vsa.Sim.InterpInit
import Vsa.Sim.DivCorrClose

/-!
# `EntryDrive` — the ONE shared `Loaded → SegEntry@loopHead` drive, feeding BOTH
the term-arm entry and the divergence entry

The entry endgame and the divergence correspondence rest on the SAME machine
content: the `interp_run` prologue drive from a `Loaded L p c` config to a
loop-head `SegEntry` (`interpLoopHeadPC = 0x8000448c`) over the initial spec store
`initSt` (`Vsa/Sim/EntryHalts.lean` + `Vsa/Sim/EntrySeams.lean` for the term arm;
`Vsa/Sim/DivCorrClose.lean`'s `DivEntryDrive` for divergence).  This file NAMES
that shared drive ONCE as `DriveToLoopHead L` and shows it supplies both consumers,
so the "shared crux" the brief flags is a single premise, not two.

## The drive content (spans verified against `experiments/disasm.txt:4463–4503`)

```
── straight-line spill span  [0x800043ec, 0x80004424) ──────────────────────
  addi sp,sp,-176 ; sd a0,0(sp) ; addi a0,a0,16 ; sd ra..a3 (13 spills)
── CALL setjmp  @0x80004424 ────────────────────────────────────────────────
  jal setjmp   → setjmp_spec FIRST return: a0 = 0, PC = 0x80004428
── bnez a0 @0x80004428  ── a0 = 0 ⇒ NOT taken (fallthrough) ─────────────────
── loop setup span  [0x8000442c, 0x8000448c)  ──────────────────────────────
  ld a5,16(sp) ; mv s5,a0 ; blez a5,exit (n>0 ⇒ not taken) ;
  ld a5 ; ld s0 ; s6=_impure_ptr ; s2 = s0 + 8·a5 ; s3=3 ; s4=1 ; j 0x8000448c
── LOOP HEAD = SegEntry entry PC  @0x8000448c ──────────────────────────────
```

ALL 25 straight-line words of the two spans are on the block-reflection decode
table (verified against `scripts/decode_index.tsv` 2026-08-31), so the spans are
`#derive_case` seg / genseg territory — no decode-batch rebuild.  The genuine
seams of the drive are: the two seg spans, the `jal setjmp` callSeg splice
(`JmpSpec.setjmp_spec`, first-return `a0 = 0`), the two not-taken branches, and —
the ONE off-`interp_run` fact — the store representation `StoreRepr initSt.store`
at the loop head, built by `interp_init` (`Vsa/Sim/InterpInit.lean`'s composition).

## What this file lands

* **`DriveToLoopHead L`** — the shared drive residual (`Loaded → ∃ cH ghosts,
  Steps c cH ∧ SegEntry@loopHead over initSt`).  The precise, decoded shape both
  entry arms need.
* **`interpInitStoreRepr_of_driveToLoopHead`** — feeds
  `InterpInit.interpInitStoreRepr_of_drive` (converting the `initSt` store form to
  the `storeAfterAssert` form by `initStore_eq_initSt`), closing
  `InterpInitStoreRepr L` (hence the term-arm entry seam) from `DriveToLoopHead`.
* **`divEntryDrive_of_driveToLoopHead`** — feeds `DivCorrClose.DivEntryDrive`
  (`Steps → StepsN` via `Steps.toN`, packing the loop-head reflection), closing the
  divergence entry from the SAME `DriveToLoopHead` + the loop-head reflection.

So the two endgame entry seams are UNIFIED: one drive, two consumers.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq Addr Stmt)
open Vsa.Sim.Scaffold (SegEntry)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The shared drive residual -/

/-- **The shared `interp_run` prologue drive.**  From `Loaded L p c` (machine at
`interp_run`'s entry `0x800043ec`, `a0`/`a1` = AST base/len), the machine reaches
(in some number of steps, for some layout ghosts) a loop-head `SegEntry`
(`interpLoopHeadPC`) over the initial spec store `initSt`, depth `0`, scope `0`.

This is the decoded drive whose spans (`[0x800043ec, 0x80004424)` spills,
`[0x8000442c, 0x8000448c)` loop setup) are ALL decode-tabled, whose `jal setjmp`
splice reuses `JmpSpec.setjmp_spec` (first-return `a0 = 0`), and whose store
representation is the off-path `interp_init` build.  It is the SINGLE machine
residual both the term-arm entry (`InterpInitStoreRepr`) and the divergence entry
(`DivEntryDrive`) rest on. -/
def DriveToLoopHead (L : Layout) : Prop :=
  ∀ (p : Program) (c : Config), Loaded L p c →
    ∃ (cH : Config)
      (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (dLeft aLeft : Nat) (m0 : Mem),
      Steps c cH ∧
      SegEntry g N A SL φf φc initSt 0 dLeft aLeft interpLoopHeadPC m0 cH

/-! ## §2. Consumer 1 — the term-arm entry (`InterpInitStoreRepr`) -/

/-- **`InterpInitStoreRepr` from the shared drive.**  `InterpInit.interpInitStoreRepr_of_drive`
wants the loop-head `SegEntry` phrased over the COMPOSED store
`{ store := storeAfterAssert, out := initSt.out }`; the shared `DriveToLoopHead`
phrases it over `initSt`.  These are equal by `initStore_eq_initSt`
(`storeAfterAssert = initSt.store`, and `initSt.out` on both), so the drive's
witness IS the one that lemma needs — a `rw` reindex.  Closes the term-arm entry
seam from `DriveToLoopHead`. -/
theorem interpInitStoreRepr_of_driveToLoopHead
    (L : Layout) (hDrive : DriveToLoopHead L) :
    ∀ p, InterpInitStoreRepr L p := by
  apply interpInitStoreRepr_of_drive L
  intro p c hL
  obtain ⟨cH, g, N, A, SL, φf, φc, dLeft, aLeft, m0, hSteps, hSeg⟩ := hDrive p c hL
  refine ⟨cH, g, N, A, SL, φf, φc, dLeft, aLeft, m0, hSteps, ?_⟩
  -- `initSt = { store := storeAfterAssert, out := initSt.out }` by `initStore_eq_initSt`.
  have hst : ({ store := storeAfterAssert, out := initSt.out } : SpecSt) = initSt := by
    rw [initStore_eq_initSt]
  rwa [hst]

/-! ## §3. Consumer 2 — the divergence entry (`DivEntryDrive`) -/

/-- **`DivCorrClose.DivEntryDrive` from the shared drive.**  The divergence entry
`divCorr Reflect c initSt 0 0 p` needs `∃ cH k …, StepsN k c cH ∧ SegEntry@loopHead
over initSt ∧ Reflect cH 0 p`.  `DriveToLoopHead` supplies the `Steps c cH ∧
SegEntry`; `Steps.toN` converts `Steps` to `StepsN k` for some `k`; the loop-head
reflection `Reflect cH 0 p` (the root: whole program `p` as the top-level statement
list, scope `0`) is the honest per-node reflection premise `hRefl0`.  Closes the
divergence entry from the SAME drive.

`hRefl0` is the ONLY extra datum beyond the shared drive: the fact that the reached
loop-head config reflects "executing `p` in the global scope" — the root case of the
loop-head reflection the divergence correspondence carries (named, per
`DivCorrClose`'s `Reflect` abstraction). -/
theorem divEntryDrive_of_driveToLoopHead
    (Reflect : Config → Addr → List Stmt → Prop)
    (L : Layout) (hDrive : DriveToLoopHead L)
    (hRefl0 : ∀ (p : Program) (c cH : Config),
      Loaded L p c →
      (∃ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (dLeft aLeft : Nat) (m0 : Mem),
        Steps c cH ∧
        SegEntry g N A SL φf φc initSt 0 dLeft aLeft interpLoopHeadPC m0 cH) →
      Reflect cH 0 p) :
    DivCorrClose.DivEntryDrive Reflect L := by
  intro p c hL
  obtain ⟨cH, g, N, A, SL, φf, φc, dLeft, aLeft, m0, hSteps, hSeg⟩ := hDrive p c hL
  obtain ⟨k, hStepsN⟩ := hSteps.toN
  refine ⟨cH, k, g, N, A, SL, φf, φc, dLeft, aLeft, m0, hStepsN, hSeg, ?_⟩
  exact hRefl0 p c cH hL ⟨g, N, A, SL, φf, φc, dLeft, aLeft, m0, hSteps, hSeg⟩

#print axioms DriveToLoopHead
#print axioms interpInitStoreRepr_of_driveToLoopHead
#print axioms divEntryDrive_of_driveToLoopHead

end Vsa.Sim
