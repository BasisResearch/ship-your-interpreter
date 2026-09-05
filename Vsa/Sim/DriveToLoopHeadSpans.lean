import Vsa.Sim.EntryDrive
import Vsa.Sim.LayoutInstance
import Vsa.Sim.JmpSpec
import Vsa.Sim.SegFrameFactsAuto
import Vsa.Sim.BridgeSegOut
import Vsa.Sim.SegEffect
import Vsa.Sim.WriteLogNF
import Vsa.Sim.rows.DriveSpillGen
import Vsa.Sim.rows.DriveLoopSetupAGen
import Vsa.Sim.rows.DriveLoopSetupBGen

/-!
# `DriveToLoopHeadSpans` — assembling the shared `interp_run` prologue drive

`Vsa/Sim/EntryDrive.lean` names `DriveToLoopHead L` for nonempty programs: from a
`Loaded L (s :: ss) c` config the machine reaches a loop-head `SegEntry`
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
open Vsa.Machine (MState Config Step Steps output)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Addr)
open Vsa.Sim.Scaffold (SegEntry SegExit)
open Vsa.Sim.LayoutInstance (interpRunLayout interpRunEntry stackSL)

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) The predicates in this file are either
-- named-field `structure`s (SegEntryData/SegEntryFields — projected as DATA into
-- the `SegEntry` witness / the seg `SegPre`) or NAMED Prop-valued existential
-- `def`s (SpillLanded/SegLanded/SetjmpSplice/SetjmpGeom). The latter MUST be
-- `def … : Prop := ∃ data, props` rather than
-- `structure`: they carry a reached `Config` (DATA) yet are BUILT from a
-- `Triple`/`setjmp_spec` `Exists` (Type-valued structure ⇒ large elimination
-- forbidden) and CONSUMED in Prop goals (see observation
-- `landing-bundle-must-be-prop-existential`). Each is destructured ONCE at its
-- consumer's binder site via a flat named `obtain` pattern (no `.2.2.2` towers).

local notation "SpecSt" => Vsa.While.St

/-! ## The decoded spill facts

The spill is one long basic block.  Keeping its `ProgFactsM` proof monolithic
creates a proof term deep enough to overflow the kernel.  These opaque suffix
lemmas make every decoded store an independently checked, shallow obligation.
-/

private theorem spillProgFacts_cons {mc m : Mem} {L : GRegs}
    {a : MInstr} {r : List MInstr}
    (hp : BytePinsM mc a) (hd : DecodeFactM a)
    (hm : MemFacts m L [] a)
    (ht : ProgFactsM mc (stepMemM m a L) (stepGM a L []) [] r) :
    ProgFactsM mc m L [] (a :: r) := by
  have hlds : stepLdsM a.kind [] = [] := by cases a.kind <;> rfl
  rw [ProgFactsM, hlds]
  exact ⟨hp, hd, hm, ht⟩

private theorem spillProg_4420 {mc m : Mem} {L : GRegs}
    (hcode : Code.Interp_runLoaded mc)
    (hsp : srcVal 2 L = 0x87ffff50#64) :
    ProgFactsM mc m L [] [(mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x80004420#64 0x00d13423#32)
    (Code.interp_run_at_80004420 hcode)
    DecodeTable.decode_00d13423
  · apply memFacts_sd_frame
    · rfl
    all_goals unfold eaddrM; rw [show (mkLine 0x80004420#64 0x00d13423#32).rs1 = 2 by rfl, hsp]; decide
  · trivial

private theorem spillProg_441c {mc m : Mem} {L : GRegs}
    (hcode : Code.Interp_runLoaded mc)
    (hsp : srcVal 2 L = 0x87ffff50#64) :
    ProgFactsM mc m L []
      [(mkLine 0x8000441c#64 0x00c13823#32),
       (mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x8000441c#64 0x00c13823#32)
    (Code.interp_run_at_8000441c hcode)
    DecodeTable.decode_00c13823
  · apply memFacts_sd_frame
    · rfl
    all_goals unfold eaddrM; rw [show (mkLine 0x8000441c#64 0x00c13823#32).rs1 = 2 by rfl, hsp]; decide
  · apply spillProg_4420 hcode
    exact (srcVal_stepGM_ne _ L [] 2 (by decide)).trans hsp

private theorem spillProg_4418 {mc m : Mem} {L : GRegs}
    (hcode : Code.Interp_runLoaded mc)
    (hsp : srcVal 2 L = 0x87ffff50#64) :
    ProgFactsM mc m L []
      [(mkLine 0x80004418#64 0x00b13c23#32),
       (mkLine 0x8000441c#64 0x00c13823#32),
       (mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x80004418#64 0x00b13c23#32)
    (Code.interp_run_at_80004418 hcode)
    DecodeTable.decode_00b13c23
  · apply memFacts_sd_frame
    · rfl
    all_goals unfold eaddrM; rw [show (mkLine 0x80004418#64 0x00b13c23#32).rs1 = 2 by rfl, hsp]; decide
  · apply spillProg_441c hcode
    exact (srcVal_stepGM_ne _ L [] 2 (by decide)).trans hsp

private theorem spillProg_4414 {mc m : Mem} {L : GRegs}
    (hcode : Code.Interp_runLoaded mc)
    (hsp : srcVal 2 L = 0x87ffff50#64) :
    ProgFactsM mc m L []
      [(mkLine 0x80004414#64 0x07613823#32),
       (mkLine 0x80004418#64 0x00b13c23#32),
       (mkLine 0x8000441c#64 0x00c13823#32),
       (mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x80004414#64 0x07613823#32)
    (Code.interp_run_at_80004414 hcode)
    DecodeTable.decode_07613823
  · apply memFacts_sd_frame
    · rfl
    all_goals unfold eaddrM; rw [show (mkLine 0x80004414#64 0x07613823#32).rs1 = 2 by rfl, hsp]; decide
  · apply spillProg_4418 hcode
    exact (srcVal_stepGM_ne _ L [] 2 (by decide)).trans hsp

private theorem spillProg_4410 {mc m : Mem} {L : GRegs}
    (hcode : Code.Interp_runLoaded mc)
    (hsp : srcVal 2 L = 0x87ffff50#64) :
    ProgFactsM mc m L []
      [(mkLine 0x80004410#64 0x07513c23#32),
       (mkLine 0x80004414#64 0x07613823#32),
       (mkLine 0x80004418#64 0x00b13c23#32),
       (mkLine 0x8000441c#64 0x00c13823#32),
       (mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x80004410#64 0x07513c23#32)
    (Code.interp_run_at_80004410 hcode)
    DecodeTable.decode_07513c23
  · apply memFacts_sd_frame
    · rfl
    all_goals unfold eaddrM; rw [show (mkLine 0x80004410#64 0x07513c23#32).rs1 = 2 by rfl, hsp]; decide
  · apply spillProg_4414 hcode
    exact (srcVal_stepGM_ne _ L [] 2 (by decide)).trans hsp

private theorem spillProg_440c {mc m : Mem} {L : GRegs}
    (hcode : Code.Interp_runLoaded mc)
    (hsp : srcVal 2 L = 0x87ffff50#64) :
    ProgFactsM mc m L []
      [(mkLine 0x8000440c#64 0x09413023#32),
       (mkLine 0x80004410#64 0x07513c23#32),
       (mkLine 0x80004414#64 0x07613823#32),
       (mkLine 0x80004418#64 0x00b13c23#32),
       (mkLine 0x8000441c#64 0x00c13823#32),
       (mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x8000440c#64 0x09413023#32)
    (Code.interp_run_at_8000440c hcode)
    DecodeTable.decode_09413023
  · apply memFacts_sd_frame
    · rfl
    all_goals unfold eaddrM; rw [show (mkLine 0x8000440c#64 0x09413023#32).rs1 = 2 by rfl, hsp]; decide
  · apply spillProg_4410 hcode
    exact (srcVal_stepGM_ne _ L [] 2 (by decide)).trans hsp

private theorem spillProg_4408 {mc m : Mem} {L : GRegs}
    (hcode : Code.Interp_runLoaded mc)
    (hsp : srcVal 2 L = 0x87ffff50#64) :
    ProgFactsM mc m L []
      [(mkLine 0x80004408#64 0x09313423#32),
       (mkLine 0x8000440c#64 0x09413023#32),
       (mkLine 0x80004410#64 0x07513c23#32),
       (mkLine 0x80004414#64 0x07613823#32),
       (mkLine 0x80004418#64 0x00b13c23#32),
       (mkLine 0x8000441c#64 0x00c13823#32),
       (mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x80004408#64 0x09313423#32)
    (Code.interp_run_at_80004408 hcode)
    DecodeTable.decode_09313423
  · apply memFacts_sd_frame
    · rfl
    all_goals unfold eaddrM; rw [show (mkLine 0x80004408#64 0x09313423#32).rs1 = 2 by rfl, hsp]; decide
  · apply spillProg_440c hcode
    exact (srcVal_stepGM_ne _ L [] 2 (by decide)).trans hsp

private theorem spillProg_4404 {mc m : Mem} {L : GRegs}
    (hcode : Code.Interp_runLoaded mc)
    (hsp : srcVal 2 L = 0x87ffff50#64) :
    ProgFactsM mc m L []
      [(mkLine 0x80004404#64 0x09213823#32),
       (mkLine 0x80004408#64 0x09313423#32),
       (mkLine 0x8000440c#64 0x09413023#32),
       (mkLine 0x80004410#64 0x07513c23#32),
       (mkLine 0x80004414#64 0x07613823#32),
       (mkLine 0x80004418#64 0x00b13c23#32),
       (mkLine 0x8000441c#64 0x00c13823#32),
       (mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x80004404#64 0x09213823#32)
    (Code.interp_run_at_80004404 hcode)
    DecodeTable.decode_09213823
  · apply memFacts_sd_frame
    · rfl
    all_goals unfold eaddrM; rw [show (mkLine 0x80004404#64 0x09213823#32).rs1 = 2 by rfl, hsp]; decide
  · apply spillProg_4408 hcode
    exact (srcVal_stepGM_ne _ L [] 2 (by decide)).trans hsp

private theorem spillProg_4400 {mc m : Mem} {L : GRegs}
    (hcode : Code.Interp_runLoaded mc)
    (hsp : srcVal 2 L = 0x87ffff50#64) :
    ProgFactsM mc m L []
      [(mkLine 0x80004400#64 0x08913c23#32),
       (mkLine 0x80004404#64 0x09213823#32),
       (mkLine 0x80004408#64 0x09313423#32),
       (mkLine 0x8000440c#64 0x09413023#32),
       (mkLine 0x80004410#64 0x07513c23#32),
       (mkLine 0x80004414#64 0x07613823#32),
       (mkLine 0x80004418#64 0x00b13c23#32),
       (mkLine 0x8000441c#64 0x00c13823#32),
       (mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x80004400#64 0x08913c23#32)
    (Code.interp_run_at_80004400 hcode)
    DecodeTable.decode_08913c23
  · apply memFacts_sd_frame
    · rfl
    all_goals unfold eaddrM; rw [show (mkLine 0x80004400#64 0x08913c23#32).rs1 = 2 by rfl, hsp]; decide
  · apply spillProg_4404 hcode
    exact (srcVal_stepGM_ne _ L [] 2 (by decide)).trans hsp

private theorem spillProg_43fc {mc m : Mem} {L : GRegs}
    (hcode : Code.Interp_runLoaded mc)
    (hsp : srcVal 2 L = 0x87ffff50#64) :
    ProgFactsM mc m L []
      [(mkLine 0x800043fc#64 0x0a813023#32),
       (mkLine 0x80004400#64 0x08913c23#32),
       (mkLine 0x80004404#64 0x09213823#32),
       (mkLine 0x80004408#64 0x09313423#32),
       (mkLine 0x8000440c#64 0x09413023#32),
       (mkLine 0x80004410#64 0x07513c23#32),
       (mkLine 0x80004414#64 0x07613823#32),
       (mkLine 0x80004418#64 0x00b13c23#32),
       (mkLine 0x8000441c#64 0x00c13823#32),
       (mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x800043fc#64 0x0a813023#32)
    (Code.interp_run_at_800043fc hcode)
    DecodeTable.decode_0a813023
  · apply memFacts_sd_frame
    · rfl
    all_goals unfold eaddrM; rw [show (mkLine 0x800043fc#64 0x0a813023#32).rs1 = 2 by rfl, hsp]; decide
  · apply spillProg_4400 hcode
    exact (srcVal_stepGM_ne _ L [] 2 (by decide)).trans hsp

private theorem spillProg_43f8 {mc m : Mem} {L : GRegs}
    (hcode : Code.Interp_runLoaded mc)
    (hsp : srcVal 2 L = 0x87ffff50#64) :
    ProgFactsM mc m L []
      [(mkLine 0x800043f8#64 0x0a113423#32),
       (mkLine 0x800043fc#64 0x0a813023#32),
       (mkLine 0x80004400#64 0x08913c23#32),
       (mkLine 0x80004404#64 0x09213823#32),
       (mkLine 0x80004408#64 0x09313423#32),
       (mkLine 0x8000440c#64 0x09413023#32),
       (mkLine 0x80004410#64 0x07513c23#32),
       (mkLine 0x80004414#64 0x07613823#32),
       (mkLine 0x80004418#64 0x00b13c23#32),
       (mkLine 0x8000441c#64 0x00c13823#32),
       (mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x800043f8#64 0x0a113423#32)
    (Code.interp_run_at_800043f8 hcode)
    DecodeTable.decode_0a113423
  · apply memFacts_sd_frame
    · rfl
    all_goals unfold eaddrM; rw [show (mkLine 0x800043f8#64 0x0a113423#32).rs1 = 2 by rfl, hsp]; decide
  · apply spillProg_43fc hcode
    exact (srcVal_stepGM_ne _ L [] 2 (by decide)).trans hsp

private theorem spillProg_43f4 {mc m : Mem} {L : GRegs}
    (hcode : Code.Interp_runLoaded mc)
    (hsp : srcVal 2 L = 0x87ffff50#64) :
    ProgFactsM mc m L []
      [(mkLine 0x800043f4#64 0x01050513#32),
       (mkLine 0x800043f8#64 0x0a113423#32),
       (mkLine 0x800043fc#64 0x0a813023#32),
       (mkLine 0x80004400#64 0x08913c23#32),
       (mkLine 0x80004404#64 0x09213823#32),
       (mkLine 0x80004408#64 0x09313423#32),
       (mkLine 0x8000440c#64 0x09413023#32),
       (mkLine 0x80004410#64 0x07513c23#32),
       (mkLine 0x80004414#64 0x07613823#32),
       (mkLine 0x80004418#64 0x00b13c23#32),
       (mkLine 0x8000441c#64 0x00c13823#32),
       (mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x800043f4#64 0x01050513#32)
    (Code.interp_run_at_800043f4 hcode)
    DecodeTable.decode_01050513
  · trivial
  · apply spillProg_43f8 hcode
    exact (srcVal_stepGM_ne _ L [] 2 (by decide)).trans hsp

private theorem spillProg_43f0 {mc m : Mem} {L : GRegs}
    (hcode : Code.Interp_runLoaded mc)
    (hsp : srcVal 2 L = 0x87ffff50#64) :
    ProgFactsM mc m L []
      [(mkLine 0x800043f0#64 0x00a13023#32),
       (mkLine 0x800043f4#64 0x01050513#32),
       (mkLine 0x800043f8#64 0x0a113423#32),
       (mkLine 0x800043fc#64 0x0a813023#32),
       (mkLine 0x80004400#64 0x08913c23#32),
       (mkLine 0x80004404#64 0x09213823#32),
       (mkLine 0x80004408#64 0x09313423#32),
       (mkLine 0x8000440c#64 0x09413023#32),
       (mkLine 0x80004410#64 0x07513c23#32),
       (mkLine 0x80004414#64 0x07613823#32),
       (mkLine 0x80004418#64 0x00b13c23#32),
       (mkLine 0x8000441c#64 0x00c13823#32),
       (mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x800043f0#64 0x00a13023#32)
    (Code.interp_run_at_800043f0 hcode)
    DecodeTable.decode_00a13023
  · apply memFacts_sd_frame
    · rfl
    all_goals unfold eaddrM; rw [show (mkLine 0x800043f0#64 0x00a13023#32).rs1 = 2 by rfl, hsp]; decide
  · apply spillProg_43f4 hcode
    exact (srcVal_stepGM_ne _ L [] 2 (by decide)).trans hsp

private theorem driveSpill_sp_after_addi
    (inp : BitVec 64) (stmts count : Nat)
    (s0 s1 s2 s3 s4 s5 s6 : BitVec 64) :
    srcVal 2
      (stepGM (mkLine 0x800043ec#64 0xf5010113#32)
        (driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry) 0x800045ec#64
          s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
          (BitVec.ofNat 64 count) 0#64) []) = 0x87ffff50#64 := by
  let a := mkLine 0x800043ec#64 0xf5010113#32
  let L := driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry) 0x800045ec#64
    s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts) (BitVec.ofNat 64 count) 0#64
  have hk : a.kind = .addi := by rfl
  have hrd : a.rd = 2 := by rfl
  have hrs1 : a.rs1 = 2 := by rfl
  have himm : a.imm = 0xf50#12 := by rfl
  have hentry : srcVal 2 L = BitVec.ofNat 64 LayoutInstance.spEntry := by rfl
  change srcVal 2 (stepGM a L []) = 0x87ffff50#64
  have hstep : srcVal 2 (stepGM a L []) = wvalM a L [] := by
    simp only [stepGM, hk, srcVal, lookupG, hrd, if_pos, Option.getD_some]
  rw [hstep]
  simp only [wvalM, hk]
  rw [hrs1, himm, hentry]
  decide

private theorem driveSpill_progFacts
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (s0 s1 s2 s3 s4 s5 s6 : BitVec 64) :
    ProgFactsM c.σ.mem c.σ.mem
      (driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry) 0x800045ec#64
        s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
        (BitVec.ofNat 64 count) 0#64) []
      [(mkLine 0x800043ec#64 0xf5010113#32),
       (mkLine 0x800043f0#64 0x00a13023#32),
       (mkLine 0x800043f4#64 0x01050513#32),
       (mkLine 0x800043f8#64 0x0a113423#32),
       (mkLine 0x800043fc#64 0x0a813023#32),
       (mkLine 0x80004400#64 0x08913c23#32),
       (mkLine 0x80004404#64 0x09213823#32),
       (mkLine 0x80004408#64 0x09313423#32),
       (mkLine 0x8000440c#64 0x09413023#32),
       (mkLine 0x80004410#64 0x07513c23#32),
       (mkLine 0x80004414#64 0x07613823#32),
       (mkLine 0x80004418#64 0x00b13c23#32),
       (mkLine 0x8000441c#64 0x00c13823#32),
       (mkLine 0x80004420#64 0x00d13423#32)] := by
  apply spillProgFacts_cons (a := mkLine 0x800043ec#64 0xf5010113#32)
    (Code.interp_run_at_800043ec F.run_code)
    DecodeTable.decode_f5010113
  · trivial
  · apply spillProg_43f0 F.run_code
    exact driveSpill_sp_after_addi inp stmts count s0 s1 s2 s3 s4 s5 s6

private theorem driveSpillSeg_eq : driveSpillSeg =
    [{ body :=
        [(mkLine 0x800043ec#64 0xf5010113#32),
         (mkLine 0x800043f0#64 0x00a13023#32),
         (mkLine 0x800043f4#64 0x01050513#32),
         (mkLine 0x800043f8#64 0x0a113423#32),
         (mkLine 0x800043fc#64 0x0a813023#32),
         (mkLine 0x80004400#64 0x08913c23#32),
         (mkLine 0x80004404#64 0x09213823#32),
         (mkLine 0x80004408#64 0x09313423#32),
         (mkLine 0x8000440c#64 0x09413023#32),
         (mkLine 0x80004410#64 0x07513c23#32),
         (mkLine 0x80004414#64 0x07613823#32),
         (mkLine 0x80004418#64 0x00b13c23#32),
         (mkLine 0x8000441c#64 0x00c13823#32),
         (mkLine 0x80004420#64 0x00d13423#32)],
       term := none }] := by
  rfl

/-- Exact decoded memory/decode facts for the spill block at a ready entry. -/
private theorem driveSpill_blockFacts
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (s0 s1 s2 s3 s4 s5 s6 : BitVec 64) :
    BBlockFacts c.σ.mem c.σ.mem
      (driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry) 0x800045ec#64
        s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
        (BitVec.ofNat 64 count) 0#64) []
      { body :=
          [(mkLine 0x800043ec#64 0xf5010113#32),
           (mkLine 0x800043f0#64 0x00a13023#32),
           (mkLine 0x800043f4#64 0x01050513#32),
           (mkLine 0x800043f8#64 0x0a113423#32),
           (mkLine 0x800043fc#64 0x0a813023#32),
           (mkLine 0x80004400#64 0x08913c23#32),
           (mkLine 0x80004404#64 0x09213823#32),
           (mkLine 0x80004408#64 0x09313423#32),
           (mkLine 0x8000440c#64 0x09413023#32),
           (mkLine 0x80004410#64 0x07513c23#32),
           (mkLine 0x80004414#64 0x07613823#32),
           (mkLine 0x80004418#64 0x00b13c23#32),
           (mkLine 0x8000441c#64 0x00c13823#32),
           (mkLine 0x80004420#64 0x00d13423#32)],
        term := none } := by
  exact ⟨driveSpill_progFacts F s0 s1 s2 s3 s4 s5 s6, trivial, trivial⟩

/-- Exact decoded memory/decode facts for the spill block at a ready entry. -/
theorem driveSpill_chainFacts
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (s0 s1 s2 s3 s4 s5 s6 : BitVec 64) :
    ChainFacts c.σ.mem c.σ.mem
      (driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry) 0x800045ec#64
        s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
        (BitVec.ofNat 64 count) 0#64) [] driveSpillSeg := by
  rw [driveSpillSeg_eq, ChainFacts]
  exact ⟨driveSpill_blockFacts F s0 s1 s2 s3 s4 s5 s6, trivial⟩

private theorem setjmpLoaded_of_agree (m m' : Mem)
    (h : Code.SetjmpLoaded m)
    (hag : ∀ k, 0x80006ffc ≤ k → k < 0x8000703c → m[k]? = m'[k]?) :
    Code.SetjmpLoaded m' := by
  simp only [Code.SetjmpLoaded, Code.setjmpChunk0] at h ⊢
  simp_all

/-- An outside-stack byte frame transports the interpreter image.  The seven
chunk reductions stay sealed behind `interpRunLoaded_of_agree`. -/
private theorem interpRunLoaded_of_stack_frame (m m' : Mem)
    (h : Code.Interp_runLoaded m)
    (hframe : ∀ k, ¬ (stackSL.lo ≤ k ∧ k < stackSL.hi) → m[k]? = m'[k]?) :
    Code.Interp_runLoaded m' := by
  apply loaded_interp_run_of_agree m m' h
  intro k hklo hkhi
  apply hframe k
  intro hk
  simp only [LayoutInstance.stackSL] at hk
  omega

/-- The same outside-stack frame transports the setjmp image. -/
private theorem setjmpLoaded_of_stack_frame (m m' : Mem)
    (h : Code.SetjmpLoaded m)
    (hframe : ∀ k, ¬ (stackSL.lo ≤ k ∧ k < stackSL.hi) → m[k]? = m'[k]?) :
    Code.SetjmpLoaded m' := by
  apply setjmpLoaded_of_agree m m' h
  intro k hklo hkhi
  apply hframe k
  intro hk
  simp only [LayoutInstance.stackSL] at hk
  omega

private def driveSpillTail : List MInstr :=
  [(mkLine 0x800043f0#64 0x00a13023#32),
   (mkLine 0x800043f4#64 0x01050513#32),
   (mkLine 0x800043f8#64 0x0a113423#32),
   (mkLine 0x800043fc#64 0x0a813023#32),
   (mkLine 0x80004400#64 0x08913c23#32),
   (mkLine 0x80004404#64 0x09213823#32),
   (mkLine 0x80004408#64 0x09313423#32),
   (mkLine 0x8000440c#64 0x09413023#32),
   (mkLine 0x80004410#64 0x07513c23#32),
   (mkLine 0x80004414#64 0x07613823#32),
   (mkLine 0x80004418#64 0x00b13c23#32),
   (mkLine 0x8000441c#64 0x00c13823#32),
   (mkLine 0x80004420#64 0x00d13423#32)]

/-- Address-only frame geometry.  Unlike `FrameBundle`, it does not require
unrelated sparse-memory bytes to be populated. -/
private structure SpillAddrGeom (base : BitVec 64) : Prop where
  hi : base.toNat + 0xb0 ≤ 0x100000000

private theorem spill_eaddr (a : MInstr) (L : GRegs) (base : BitVec 64)
    (hsrc : srcVal a.rs1 L = base)
    (hoff : (sign_extend (m := 64) a.imm : BitVec 64).toNat ≤ 0xa8)
    (G : SpillAddrGeom base) :
    (eaddrM a L).toNat =
      base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat := by
  unfold eaddrM
  rw [hsrc, BitVec.toNat_add]
  rw [Nat.mod_eq_of_lt (by have := G.hi; omega)]

private theorem wlogM_spill_offsets :
    ∀ (body : List MInstr) (L : GRegs) (lds : List (List (BitVec 8)))
      (base : BitVec 64) (G : SpillAddrGeom base),
      srcVal 2 L = base →
      (∀ a ∈ body, a.rd ≠ 2) →
      (∀ a ∈ body, (a.kind = .sw ∨ a.kind = .sd ∨ a.kind = .sb ∨ a.kind = .sh) →
        a.rs1 = 2 ∧ (sign_extend (m := 64) a.imm : BitVec 64).toNat ≤ 0xa8) →
      ∀ e ∈ wlogM body L lds,
        ∃ a, a ∈ body ∧
          (a.kind = .sw ∨ a.kind = .sd ∨ a.kind = .sb ∨ a.kind = .sh) ∧
          e.1 = base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat := by
  intro body
  induction body with
  | nil => intro L lds base G _ _ _ e he; simp only [wlogM, List.not_mem_nil] at he
  | cons a rest ih =>
    intro L lds base G h2 hrd hst e he
    rw [wlogM] at he
    cases hk : a.kind <;> rw [hk] at he <;> dsimp only [] at he <;>
      (try rw [← hk] at he) <;>
      first
        | (rcases List.mem_cons.mp he with rfl | he
           · obtain ⟨hrs1, hoff⟩ := hst a (List.mem_cons_self ..) (by rw [hk]; decide)
             refine ⟨a, List.mem_cons_self .., by rw [hk]; decide, ?_⟩
             show (eaddrM a L).toNat = _
             rw [spill_eaddr a L base (by rw [hrs1]; exact h2) hoff G]
           · obtain ⟨a', ha', hk', he'⟩ := ih L lds base G h2
               (fun x hx => hrd x (List.mem_cons_of_mem _ hx))
               (fun x hx => hst x (List.mem_cons_of_mem _ hx)) e he
             exact ⟨a', List.mem_cons_of_mem _ ha', hk', he'⟩)
        | (obtain ⟨a', ha', hk', he'⟩ :=
             ih (stepGM a L (lds.headD [])) (stepLdsM a.kind lds) base G
               (by rw [srcVal_stepGM_ne a L (lds.headD []) 2
                 (hrd a (List.mem_cons_self ..)).symm]; exact h2)
               (fun x hx => hrd x (List.mem_cons_of_mem _ hx))
               (fun x hx => hst x (List.mem_cons_of_mem _ hx)) e he
           exact ⟨a', List.mem_cons_of_mem _ ha', hk', he'⟩)

private theorem driveSpill_log_eq
    (inp : BitVec 64) (stmts count : Nat)
    (s0 s1 s2 s3 s4 s5 s6 : BitVec 64) :
    (evalBlocks driveSpillSeg
      (SegEvalState.init
        (driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry) 0x800045ec#64
          s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
          (BitVec.ofNat 64 count) 0#64) [])).log =
      wlogM driveSpillTail
        (stepGM (mkLine 0x800043ec#64 0xf5010113#32)
          (driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry) 0x800045ec#64
            s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
            (BitVec.ofNat 64 count) 0#64) []) [] := by
  rfl

/-- Every reflected spill write is inside the concrete C-stack region. -/
private theorem driveSpill_writeLog_out
    (m : Mem) (inp : BitVec 64) (stmts count : Nat)
    (s0 s1 s2 s3 s4 s5 s6 : BitVec 64) (k : Nat)
    (hk : ¬ (stackSL.lo ≤ k ∧ k < stackSL.hi)) :
    (writeLog m (evalBlocks driveSpillSeg
      (SegEvalState.init
        (driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry) 0x800045ec#64
          s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
          (BitVec.ofNat 64 count) 0#64) [])).log)[k]? = m[k]? := by
  rw [driveSpill_log_eq]
  apply writeLog_getElem_disjoint k
  · exact wlogM_widths driveSpillTail _ []
  · intro e he
    let L := driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry)
      0x800045ec#64 s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
        (BitVec.ofNat 64 count) 0#64
    let L' := stepGM (mkLine 0x800043ec#64 0xf5010113#32) L []
    have G : SpillAddrGeom (0x87ffff50#64 : BitVec 64) := by
      exact { hi := by decide }
    have h2 : srcVal 2 L' = (0x87ffff50#64 : BitVec 64) := by
      exact driveSpill_sp_after_addi inp stmts count s0 s1 s2 s3 s4 s5 s6
    obtain ⟨a, ha, hkind, haddr⟩ :=
      wlogM_spill_offsets driveSpillTail L' [] 0x87ffff50#64 G h2
        (by
          intro x hx
          simp only [driveSpillTail, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl <;> decide)
        (by
          intro x hx hkx
          simp only [driveSpillTail, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl
          all_goals
            first
            | decide
            | (exfalso; revert hkx; decide)) e he
    have hoff : (sign_extend (m := 64) a.imm : BitVec 64).toNat ≤ 0xa8 :=
      (by
        simp only [driveSpillTail, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl <;> decide)
    have hw := wlogM_widths driveSpillTail L' [] e he
    have hbase : (0x87ffff50#64 : BitVec 64).toNat = 0x87ffff50 := by decide
    simp only [LayoutInstance.stackSL] at hk
    rw [haddr, hbase]
    have hdis (w : Nat) (hw8 : w ≤ 8) :
        k < 0x87ffff50 + (sign_extend (m := 64) a.imm : BitVec 64).toNat ∨
          0x87ffff50 + (sign_extend (m := 64) a.imm : BitVec 64).toNat + w ≤ k := by
      by_cases hbefore :
          k < 0x87ffff50 + (sign_extend (m := 64) a.imm : BitVec 64).toNat
      · exact Or.inl hbefore
      · right
        have hkhi : 0x88000000 ≤ k := Nat.le_of_not_gt (fun hbelow =>
          hk ⟨by omega, hbelow⟩)
        omega
    rcases hw with hw | hw | hw | hw <;> rw [hw]
    · exact hdis 1 (by omega)
    · exact hdis 2 (by omega)
    · exact hdis 4 (by omega)
    · exact hdis 8 (by omega)

/-- Package the reflected spill log as a byte frame.  Downstream code-image
transport consumes this opaque theorem instead of reducing the whole block. -/
private theorem driveSpill_result_mem_out
    (m m' : Mem) (inp : BitVec 64) (stmts count : Nat)
    (s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (hmem : m' = writeLog m (evalBlocks driveSpillSeg
      (SegEvalState.init
        (driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry) 0x800045ec#64
          s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
          (BitVec.ofNat 64 count) 0#64) [])).log) :
    ∀ k, ¬ (stackSL.lo ≤ k ∧ k < stackSL.hi) → m[k]? = m'[k]? := by
  intro k hk
  rw [hmem]
  exact (driveSpill_writeLog_out m inp stmts count
    s0 s1 s2 s3 s4 s5 s6 k hk).symm

/-- Exact output-preserving `jal setjmp` site at `0x80004424`. -/
theorem site_80004424_interpRunO
    (s : MState) (i u : Nat) (vm : BitVec 64)
    (hG : GoodState s)
    (hpc : s.regs.get? Register.PC = some 0x80004424#64)
    (hmi : s.regs.get? Register.minstret = some vm)
    (hcode : Code.Interp_runLoaded s.mem) (hi : i < 2) :
    JalStepO 0x80006ffc#64 0x80004428#64 s i u := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Code.interp_run_at_80004424 hcode
  obtain ⟨s', i', hs, hi', hG', hm', hobs⟩ :=
    stepObs_jal s i u 0x80004424#64 vm 0x3d9020ef#32 0x002bd8#21
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt 0x80004424#64 4)
      0xef#8 0x20#8 0x90#8 0x3d#8 hG hpc hmi hb0 hb1 hb2 hb3
      (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (DecodeTable.decode_3d9020ef (afterPrelude s)
        (by rw [get?_afterPrelude s _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude s _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude s _ (by decide)]; exact hG.mseccfg))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by exact wX_bits_x1 _ (BitVec.addInt 0x80004424#64 4)) hi
  exact jalStepO_of_obs hs hi' hG' hm' hobs (by
    apply BitVec.eq_of_toNat_eq
    decide)

/-- Facts preserved by the spill, setjmp, and branch prefix.  The clean x21
latch is intentionally absent: loop-setup A establishes it later. -/
structure ReadyPrefixFacts (inp : BitVec 64) (c0 c1 : Config) : Prop where
  outside_writes : ∀ k, ¬ LayoutInstance.interpRunWriteFootprint inp k →
    c0.σ.mem[k]? = c1.σ.mem[k]?
  output : output c1.σ = output c0.σ
  run_code : Code.Interp_runLoaded c1.σ.mem

/-- Concrete setjmp-entry geometry retained by the spill producer. -/
def SetjmpGeom (c1 : Config) : Prop :=
  ∃ (jb : BitVec 64)
    (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : BitVec 64)
    (g : (R : Register) → Option (RegisterType R))
    (m0 : Mem),
    c1.σ.mem = m0 ∧
    Code.SetjmpLoaded c1.σ.mem ∧
    Code.Interp_runLoaded c1.σ.mem ∧
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
    (∀ R : Register, NotWrittenJmp R → c1.σ.regs.get? R = g R)

/-- Spill landing plus the entry memory/output/code preservation that the
setjmp prefix consumes. -/
def ReadySpillLanded (inp : BitVec 64) (c0 c : Config) : Prop :=
  ∃ (c1 : Config) (spNew : BitVec 64),
    Steps c c1 ∧
    c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64) ∧
    c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64) ∧
    c1.σ.regs.get? Register.x2 = some spNew ∧
    c1.σ.regs.get? Register.x10 = some (inp + 16#64) ∧
    GoodState c1.σ ∧ c1.tick < 2 ∧
    (∃ w, c1.σ.regs.get? Register.minstret = some w) ∧
    ReadyPrefixFacts inp c0 c1 ∧ SetjmpGeom c1

/-- Exact x2 projection from the reflected spill evaluator. -/
private theorem driveSpillEval_sp
    (inp : BitVec 64) (stmts count : Nat)
    (s0 s1 s2 s3 s4 s5 s6 : BitVec 64) :
    lookupG 2 (evalBlocks driveSpillSeg (SegEvalState.init
      (driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry) 0x800045ec#64
        s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
        (BitVec.ofNat 64 count) 0#64) [])).regs =
      some (0x87ffff50#64 : BitVec 64) := by
  let L := driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry)
    0x800045ec#64 s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
      (BitVec.ofNat 64 count) 0#64
  let first := mkLine 0x800043ec#64 0xf5010113#32
  rw [evalBlocks_regs, driveSpillSeg_eq]
  change lookupG 2 (runGM (first :: driveSpillTail) L []) = _
  rw [runGM, lookupG_runGM_preserved 2 driveSpillTail
    (by
      intro a ha
      simp only [driveSpillTail, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> decide)]
  change lookupG 2 (stepGM first L []) = _
  have hw : lookupG 2 (stepGM first L []) = some (wvalM first L []) :=
    lookupG_stepGM_writer first L [] (by decide) 2 (by rfl)
  rw [hw]
  have hs := driveSpill_sp_after_addi inp stmts count s0 s1 s2 s3 s4 s5 s6
  have hwval : wvalM first L [] = (0x87ffff50#64 : BitVec 64) := by
    simpa only [first, L, srcVal, hw, Option.getD_some] using hs
  exact congrArg some hwval

#print axioms driveSpillEval_sp

/-- Exact a0 projection from the reflected spill evaluator. -/
private theorem driveSpillEval_a0
    (inp : BitVec 64) (stmts count : Nat)
    (s0 s1 s2 s3 s4 s5 s6 : BitVec 64) :
    lookupG 10 (evalBlocks driveSpillSeg (SegEvalState.init
      (driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry) 0x800045ec#64
        s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
        (BitVec.ofNat 64 count) 0#64) [])).regs =
      some (inp + 16#64) := by
  let L := driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry)
    0x800045ec#64 s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
      (BitVec.ofNat 64 count) 0#64
  let pre :=
    [mkLine 0x800043ec#64 0xf5010113#32,
     mkLine 0x800043f0#64 0x00a13023#32]
  let writer := mkLine 0x800043f4#64 0x01050513#32
  let post :=
    [mkLine 0x800043f8#64 0x0a113423#32,
     mkLine 0x800043fc#64 0x0a813023#32,
     mkLine 0x80004400#64 0x08913c23#32,
     mkLine 0x80004404#64 0x09213823#32,
     mkLine 0x80004408#64 0x09313423#32,
     mkLine 0x8000440c#64 0x09413023#32,
     mkLine 0x80004410#64 0x07513c23#32,
     mkLine 0x80004414#64 0x07613823#32,
     mkLine 0x80004418#64 0x00b13c23#32,
     mkLine 0x8000441c#64 0x00c13823#32,
     mkLine 0x80004420#64 0x00d13423#32]
  rw [evalBlocks_regs, driveSpillSeg_eq]
  change lookupG 10 (runGM (pre ++ writer :: post) L []) = _
  rw [lookupG_runGM_after_writer pre writer post L [] (by decide) 10 (by rfl)
    (by
      intro a ha
      simp only [post, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> decide)]
  change some (srcVal 10 (runGM pre L []) +
    LeanRV64DExecutable.Functions.sign_extend 0x010#12) = some (inp + 16#64)
  rw [srcVal_runGM_ne 10 pre (by
    intro a ha
    simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> decide)]
  change some (inp + LeanRV64DExecutable.Functions.sign_extend 0x010#12) = _
  rw [show (LeanRV64DExecutable.Functions.sign_extend 0x010#12 : BitVec 64) =
    16#64 by decide]

#print axioms driveSpillEval_a0

/-- Opaque spill-body result, before the `jal setjmp`. -/
private def SpillBodyLanded (inp : BitVec 64) (stmts count : Nat)
    (c : Config) : Prop :=
  ∃ (cB : Config)
    (s0 s1 s2 s3 s4 s5 s6 : BitVec 64),
    Steps c cB ∧
    cB.σ.regs.get? Register.PC = some (0x80004424#64 : BitVec 64) ∧
    GoodState cB.σ ∧ cB.tick < 2 ∧
    (∃ w, cB.σ.regs.get? Register.minstret = some w) ∧
    (∀ k, ¬ (stackSL.lo ≤ k ∧ k < stackSL.hi) →
      c.σ.mem[k]? = cB.σ.mem[k]?) ∧
    output cB.σ = output c.σ ∧
    Code.Interp_runLoaded cB.σ.mem ∧ Code.SetjmpLoaded cB.σ.mem ∧
    cB.σ.regs.get? Register.x2 = some (0x87ffff50#64 : BitVec 64) ∧
    cB.σ.regs.get? Register.x10 = some (inp + 16#64) ∧
    (∀ R, AbiExceptSp R = true → cB.σ.regs.get? R = c.σ.regs.get? R)

/-- The exact reflected spill body produces its preservation carrier. -/
private theorem spillBodyLanded_of_ready
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft) :
    SpillBodyLanded inp stmts count c := by
  obtain ⟨s0, hs0⟩ := F.s0
  obtain ⟨s1, hs1⟩ := F.s1
  obtain ⟨s2, hs2⟩ := F.s2
  obtain ⟨s3, hs3⟩ := F.s3
  obtain ⟨s4, hs4⟩ := F.s4
  obtain ⟨s5, hs5⟩ := F.s5
  obtain ⟨s6, hs6⟩ := F.s6
  obtain ⟨vm, hmi⟩ := F.good.minstret
  let L := driveSpillL inp (BitVec.ofNat 64 LayoutInstance.spEntry)
    0x800045ec#64 s0 s1 s2 s3 s4 s5 s6 (BitVec.ofNat 64 stmts)
      (BitVec.ofNat 64 count) 0#64
  have hL : GHolds c.σ L := by
    exact ⟨F.interp_arg, F.sp, F.ra, hs0, hs1, hs2, hs3, hs4, hs5, hs6,
      F.stmts_arg, F.count_arg, F.repl_arg, trivial⟩
  have hkeys : KeysOK (keysG L) := by
    change KeysOK [10, 2, 1, 8, 9, 18, 19, 20, 21, 22, 11, 12, 13]
    decide
  have hwf : ChainOK 0x800043ec#64 (keysG L) driveSpillSeg := by
    change ChainOK 0x800043ec#64 [10, 2, 1, 8, 9, 18, 19, 20, 21, 22, 11, 12, 13]
      driveSpillSeg
    decide
  have hfacts : ChainFacts c.σ.mem c.σ.mem L [] driveSpillSeg := by
    exact driveSpill_chainFacts F s0 s1 s2 s3 s4 s5 s6
  let selected : GRegs :=
    [(2, 0x87ffff50#64), (10, inp + 16#64)]
  have hproj : GProjects
      (evalBlocks driveSpillSeg (SegEvalState.init L [])).regs selected := by
    refine ⟨?_, ?_, trivial⟩
    · simpa only [L] using
        driveSpillEval_sp inp stmts count s0 s1 s2 s3 s4 s5 s6
    · simpa only [L] using
        driveSpillEval_a0 inp stmts count s0 s1 s2 s3 s4 s5 s6
  obtain ⟨cB, S⟩ := segEval_selected_framed driveSpillSeg L []
    0x800043ec#64 vm (fun k => stackSL.lo ≤ k ∧ k < stackSL.hi)
    AbiExceptSp selected c F.good F.pc hmi hL hkeys hfacts hwf F.tick
    (by
      intro k hk
      simpa only [L] using
        (driveSpill_writeLog_out c.σ.mem inp stmts count
          s0 s1 s2 s3 s4 s5 s6 k hk).symm)
    (by decide) (by decide) hproj
  have hcode' : Code.Interp_runLoaded cB.σ.mem :=
    interpRunLoaded_of_stack_frame c.σ.mem cB.σ.mem F.run_code S.outside
  have hsetjmp' : Code.SetjmpLoaded cB.σ.mem :=
    setjmpLoaded_of_stack_frame c.σ.mem cB.σ.mem F.setjmp_code S.outside
  have hpc4424 : cB.σ.regs.get? Register.PC = some 0x80004424#64 := by
    simpa [L] using S.pc
  refine ⟨cB, s0, s1, s2, s3, s4, s5, s6,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact S.steps
  · exact hpc4424
  · exact S.good
  · exact S.tick
  · exact S.minstret
  · exact S.outside
  · unfold output
    exact congrArg (fun a : Array String => String.join a.toList) S.output
  · exact hcode'
  · exact hsetjmp'
  · exact S.selected_regs.1
  · exact S.selected_regs.2.1
  · exact S.reg_frame

#print axioms spillBodyLanded_of_ready

private def SpillJalLanded (inp : BitVec 64) (stmts count : Nat)
    (cB : Config) (s0 s1 s2 s3 s4 s5 s6 : BitVec 64) : Prop :=
  ∃ c1 : Config,
    Steps cB c1 ∧
    c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64) ∧
    c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64) ∧
    c1.σ.regs.get? Register.x2 = some (0x87ffff50#64 : BitVec 64) ∧
    c1.σ.regs.get? Register.x10 = some (inp + 16#64) ∧
    GoodState c1.σ ∧ c1.tick < 2 ∧
    (∃ w, c1.σ.regs.get? Register.minstret = some w) ∧
    c1.σ.mem = cB.σ.mem ∧ output c1.σ = output cB.σ ∧
    (∀ R, AbiPreserved R = true → c1.σ.regs.get? R = cB.σ.regs.get? R)

/-- Opaque exact `jal setjmp` landing from the reflected spill post-state. -/
private theorem spillJalLanded_of_fields
    {cB : Config} {inp : BitVec 64} {stmts count : Nat}
    (s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (hpc : cB.σ.regs.get? Register.PC = some (0x80004424#64 : BitVec 64))
    (hG : GoodState cB.σ) (hi : cB.tick < 2)
    (hmi : ∃ w, cB.σ.regs.get? Register.minstret = some w)
    (hcode : Code.Interp_runLoaded cB.σ.mem)
    (hspB : cB.σ.regs.get? Register.x2 =
      some (0x87ffff50#64 : BitVec 64))
    (ha0B : cB.σ.regs.get? Register.x10 = some (inp + 16#64)) :
    SpillJalLanded inp stmts count cB s0 s1 s2 s3 s4 s5 s6 := by
  obtain ⟨s', i', hjal, hi', hG', hmem', hout', hpc', hra', hmi',
      hnonra', habi'⟩ :=
    site_80004424_interpRunO cB.σ cB.tick cB.steps
      (Classical.choose hmi) hG hpc (Classical.choose_spec hmi) hcode hi
  have hsp' : s'.regs.get? Register.x2 = some (0x87ffff50#64 : BitVec 64) :=
    hnonra' 2 (by omega) (by omega) (by omega) _ hspB
  have ha0' : s'.regs.get? Register.x10 = some (inp + 16#64) :=
    hnonra' 10 (by omega) (by omega) (by omega) _ ha0B
  let c1 : Config := ⟨s', i', cB.steps + 1⟩
  refine ⟨c1, Steps.single hjal, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [c1] using hpc'
  · simpa [c1] using hra'
  · simpa [c1] using hsp'
  · simpa [c1] using ha0'
  · simpa [c1] using hG'
  · simpa [c1] using hi'
  · simpa [c1] using hmi'
  · simpa [c1] using hmem'
  · unfold output
    simpa [c1] using congrArg (fun a : Array String => String.join a.toList) hout'
  · simpa [c1] using habi'

#print axioms spillJalLanded_of_fields

private def ReadySpillPost (inp : BitVec 64) (c cB : Config) : Prop :=
  ∃ c1 : Config,
    Steps cB c1 ∧
    c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64) ∧
    c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64) ∧
    c1.σ.regs.get? Register.x2 = some (0x87ffff50#64 : BitVec 64) ∧
    c1.σ.regs.get? Register.x10 = some (inp + 16#64) ∧
    GoodState c1.σ ∧ c1.tick < 2 ∧
    (∃ w, c1.σ.regs.get? Register.minstret = some w) ∧
    ReadyPrefixFacts inp c c1 ∧ SetjmpGeom c1

/-- Package preservation and setjmp geometry after the opaque `jal` landing. -/
private theorem readySpillPost_of_fields
    {c cB : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (hstack : ∀ k, ¬ (stackSL.lo ≤ k ∧ k < stackSL.hi) →
      c.σ.mem[k]? = cB.σ.mem[k]?)
    (hout : output cB.σ = output c.σ)
    (hcode : Code.Interp_runLoaded cB.σ.mem)
    (hsetjmp : Code.SetjmpLoaded cB.σ.mem)
    (hframe : ∀ R, AbiExceptSp R = true →
      cB.σ.regs.get? R = c.σ.regs.get? R)
    (J : SpillJalLanded inp stmts count cB s0 s1 s2 s3 s4 s5 s6) :
    ReadySpillPost inp c cB := by
  obtain ⟨c1, hjal, hpc, hra, hsp, ha0, hG, hi, hmi, hmem, houtJ, habi⟩ := J
  obtain ⟨t0, ht0⟩ := F.s0
  obtain ⟨t1, ht1⟩ := F.s1
  obtain ⟨t2, ht2⟩ := F.s2
  obtain ⟨t3, ht3⟩ := F.s3
  obtain ⟨t4, ht4⟩ := F.s4
  obtain ⟨t5, ht5⟩ := F.s5
  obtain ⟨t6, ht6⟩ := F.s6
  obtain ⟨t7, ht7⟩ := F.s7
  obtain ⟨t8, ht8⟩ := F.s8
  obtain ⟨t9, ht9⟩ := F.s9
  obtain ⟨t10, ht10⟩ := F.s10
  obtain ⟨t11, ht11⟩ := F.s11
  have hbridge : ∀ R, AbiExceptSp R = true →
      c1.σ.regs.get? R = c.σ.regs.get? R := by
    intro R hR
    have hAbi : AbiPreserved R = true := by
      cases h : AbiPreserved R
      · exfalso
        unfold AbiExceptSp at hR
        simp only [h, Bool.false_and, Bool.false_eq_true] at hR
      · rfl
    exact (habi R hAbi).trans (hframe R hR)
  have P : ReadyPrefixFacts inp c c1 := by
    refine { outside_writes := ?_, output := houtJ.trans hout, run_code := ?_ }
    · intro k hk
      calc
        c.σ.mem[k]? = cB.σ.mem[k]? := hstack k (fun hs => hk (Or.inl hs))
        _ = c1.σ.mem[k]? := (congrArg (fun m : Mem => m[k]?) hmem).symm
    · exact hmem.symm ▸ hcode
  have G : SetjmpGeom c1 := by
    refine ⟨inp + 16#64, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11,
      (fun R => c1.σ.regs.get? R), c1.σ.mem, rfl, ?_, P.run_code, ha0, by decide,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, F.setjmp_geom, ?_⟩
    · exact hmem.symm ▸ hsetjmp
    · exact (hbridge Register.x8 (by decide)).trans ht0
    · exact (hbridge Register.x9 (by decide)).trans ht1
    · exact (hbridge Register.x18 (by decide)).trans ht2
    · exact (hbridge Register.x19 (by decide)).trans ht3
    · exact (hbridge Register.x20 (by decide)).trans ht4
    · exact (hbridge Register.x21 (by decide)).trans ht5
    · exact (hbridge Register.x22 (by decide)).trans ht6
    · exact (hbridge Register.x23 (by decide)).trans ht7
    · exact (hbridge Register.x24 (by decide)).trans ht8
    · exact (hbridge Register.x25 (by decide)).trans ht9
    · exact (hbridge Register.x26 (by decide)).trans ht10
    · exact (hbridge Register.x27 (by decide)).trans ht11
    · intro R _
      rfl
  exact ⟨c1, hjal, hpc, hra, hsp, ha0, hG, hi, hmi, P, G⟩

#print axioms readySpillPost_of_fields

private theorem readySpillLanded_of_post {c cB : Config} {inp : BitVec 64}
    (hbody : Steps c cB) (P : ReadySpillPost inp c cB) :
    ReadySpillLanded inp c c := by
  obtain ⟨c1, hjal, hpc, hra, hsp, ha0, hG, hi, hmi, hprefix, hgeom⟩ := P
  exact ⟨c1, 0x87ffff50#64, hbody.trans hjal, hpc, hra, hsp, ha0,
    hG, hi, hmi, hprefix, hgeom⟩

/-- The exact `jal setjmp` upgrades the opaque spill-body carrier. -/
private theorem readySpillLanded_of_body
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (B : SpillBodyLanded inp stmts count c) : ReadySpillLanded inp c c := by
  obtain ⟨cB, s0, s1, s2, s3, s4, s5, s6,
    hbody, hpc, hG, hi, hmi, hstack, hout, hcode, hsetjmp, hsp, ha0, hframe⟩ := B
  have J : SpillJalLanded inp stmts count cB s0 s1 s2 s3 s4 s5 s6 :=
    spillJalLanded_of_fields s0 s1 s2 s3 s4 s5 s6 hpc hG hi hmi hcode hsp ha0
  exact readySpillLanded_of_post hbody
    (readySpillPost_of_fields F s0 s1 s2 s3 s4 s5 s6
      hstack hout hcode hsetjmp hframe J)

#print axioms readySpillLanded_of_body

/-- The exact spill body and its `jal setjmp` produce the preservation-aware
landing directly from the repaired `interp_run` boundary. -/
theorem readySpillLanded_of_ready
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft) :
    ReadySpillLanded inp c c :=
  readySpillLanded_of_body F (spillBodyLanded_of_ready F)

#print axioms readySpillLanded_of_ready

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

/-- Preservation-aware first-return setjmp/branch landing. -/
def ReadySetjmpSplice (inp : BitVec 64) (c0 c1 : Config)
    (spNew : BitVec 64) : Prop :=
  ∃ c2 : Config,
    Steps c1 c2 ∧
    c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) ∧
    c2.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧
    c2.σ.regs.get? Register.x2 = some spNew ∧
    GoodState c2.σ ∧ c2.tick < 2 ∧
    (∃ w, c2.σ.regs.get? Register.minstret = some w) ∧
    ReadyPrefixFacts inp c0 c2

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
structure SegEntryFields (p : Program) (cH : Config) where
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
  sp : BitVec 64
  aRet : BitVec 64
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
  /-- `mv s5,a0` after setjmp's first return records the clean return latch in
  the same ghost frame threaded through `mExecSeq`. -/
  return_latch : g Register.x21 = some (0#64 : BitVec 64)
  /-- The faithful top-level sequence entry at the reached loop head. -/
  seq_entry : ExecSeqEntryI .interpRun g N A SL φf φc
    initSt 0 0 p sp aRet m0 cH

/-- Facts preserved at a decoded landing after loop-setup A has established
the clean `setjmp` return latch. -/
structure ReadyLandingFacts (inp : BitVec 64) (c0 c1 : Config) : Prop
    extends ReadyPrefixFacts inp c0 c1 where
  return_latch : c1.σ.regs.get? Register.x21 = some (0#64 : BitVec 64)

/-- Concrete registers established by loop-setup B.  Their equations are the
machine cursor, array finish, and post-spill stack pointer; semantic AST facts
remain separate. -/
structure LoopHeadRegs (cH : Config)
    (sp cursor finish : BitVec 64) : Prop where
  sp_reg : cH.σ.regs.get? Register.x2 = some sp
  cursor_reg : cH.σ.regs.get? Register.x8 = some cursor
  finish_reg : cH.σ.regs.get? Register.x18 = some finish

/-- Construct the loop-head field package from the post-startup boundary and
the facts the decoded prologue must preserve or establish.  The ghost frame and
pinned memory are chosen at the reached state, eliminating separate frame and
memory-equality premises. -/
def segEntryFields_of_ready
    {c0 cH : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    {p : Program} (hne : p ≠ [])
    (F : LayoutInstance.InterpRunReadyFacts c0 stmts count inp N A φf φc aLeft)
    (hgood : GoodState cH.σ) (htick : cH.tick < 2)
    (hpc : cH.σ.regs.get? Register.PC = some (0x8000448c#64 : BitVec 64))
    (hframe : ∀ k, ¬ LayoutInstance.interpRunWriteFootprint inp k →
      c0.σ.mem[k]? = cH.σ.mem[k]?)
    (hout : output cH.σ = output c0.σ)
    (hcode : Code.Interp_runLoaded cH.σ.mem)
    (hlatch : cH.σ.regs.get? Register.x21 = some (0#64 : BitVec 64))
    (sp aRet : BitVec 64)
    (hcursor : ExecSeqCursorRepr .interpRun cH.σ.mem φf 0 p sp aRet cH.σ.regs.get?)
    (hhead : ExecSeqHeadGround .interpRun cH.σ.mem cH.σ.regs.get?
      stackSL A φf sp aRet initSt 0 0 p)
    (hminstret : ∃ v, cH.σ.regs.get? Register.minstret = some v) :
    SegEntryFields p cH := by
  let g : (R : Register) → Option (RegisterType R) := fun R => cH.σ.regs.get? R
  have hstore : StoreRepr cH.σ.mem N A φf φc initSt.store :=
    F.store_survives cH.σ.mem hframe
  have houtH : OutRepr cH.σ initSt := by
    exact hout.trans F.out
  have hsurv : ∀ m' : Mem,
      (∀ k, ¬ (stackSL.lo ≤ k ∧ k < stackSL.hi) →
        cH.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf φc initSt.store := by
    intro m' hm'
    apply F.store_survives m'
    intro k hk
    have hkStack : ¬ (stackSL.lo ≤ k ∧ k < stackSL.hi) := by
      intro hs
      exact hk (Or.inl hs)
    exact (hframe k hk).trans (hm' k hkStack)
  have hentryPC : execSeqEntryPC .interpRun p = 0x8000448c := by
    cases p with
    | nil => exact (hne rfl).elim
    | cons _ _ => rfl
  refine
    { g := g, N := N, A := A, SL := stackSL, φf := φf, φc := φc,
      dLeft := Vsa.While.maxCallDepth, aLeft := aLeft, sp := sp, aRet := aRet,
      m0 := cH.σ.mem, mem := rfl, store := hstore, out := houtH,
      frame := fun _ _ => rfl, depth_budget := by simp,
      arena_budget := F.arena_budget, run_code := hcode,
      return_latch := hlatch, seq_entry := ?_ }
  exact
    { good := hgood, tick := htick,
      pc := by rw [hentryPC]; exact hpc,
      store := hstore, env_valid := F.envValid,
      out := houtH, mem := rfl, code := hcode,
      cursor := hcursor, head_ground := hhead, store_survives := hsurv,
      stack_ram := by decide,
      stack_win := by
        show tohostAddr + 16 ≤ (0x87800000 : Nat)
        rw [tohostAddr_val]
        decide
      empty_status := fun hp => absurd hp hne,
      frame := fun _ _ => rfl, minstret := hminstret }

/-- Carrier-based form used by the row chain. -/
def segEntryFields_of_ready_landing
    {c0 cH : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    {p : Program} (hne : p ≠ [])
    (F : LayoutInstance.InterpRunReadyFacts c0 stmts count inp N A φf φc aLeft)
    (L : ReadyLandingFacts inp c0 cH)
    (hgood : GoodState cH.σ) (htick : cH.tick < 2)
    (hpc : cH.σ.regs.get? Register.PC = some (0x8000448c#64 : BitVec 64))
    (sp aRet cursor finish : BitVec 64)
    (_hregs : LoopHeadRegs cH sp cursor finish)
    (hcursor : ExecSeqCursorRepr .interpRun cH.σ.mem φf 0 p sp aRet cH.σ.regs.get?)
    (hhead : ExecSeqHeadGround .interpRun cH.σ.mem cH.σ.regs.get?
      stackSL A φf sp aRet initSt 0 0 p)
    (hminstret : ∃ v, cH.σ.regs.get? Register.minstret = some v) :
    SegEntryFields p cH :=
  segEntryFields_of_ready hne F hgood htick hpc L.outside_writes L.output
    L.run_code L.return_latch sp aRet hcursor hhead hminstret

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

/-- A landing tied back to the original ready configuration.  This is the
preservation-aware carrier needed to consume `InterpRunReadyFacts`. -/
def ReadySegLanded (inp : BitVec 64) (c0 c : Config) (endPC : BitVec 64) : Prop :=
  ∃ c' : Config,
    Steps c c' ∧
    c'.σ.regs.get? Register.PC = some endPC ∧
    GoodState c'.σ ∧ c'.tick < 2 ∧
    (∃ w, c'.σ.regs.get? Register.minstret = some w) ∧
    ReadyLandingFacts inp c0 c'

/-- Nonempty loop-head landing with the concrete loop-B register outputs. -/
def ReadyLoopHeadLanded (inp : BitVec 64) (c0 c : Config) : Prop :=
  ∃ (cH : Config) (sp cursor finish : BitVec 64),
    Steps c cH ∧
    cH.σ.regs.get? Register.PC = some (0x8000448c#64 : BitVec 64) ∧
    GoodState cH.σ ∧ cH.tick < 2 ∧
    (∃ w, cH.σ.regs.get? Register.minstret = some w) ∧
    ReadyLandingFacts inp c0 cH ∧ LoopHeadRegs cH sp cursor finish

/- The zero-count polarity of the same setup-A block.  It branches directly to
the normal epilogue instead of entering the statement loop. -/
#derive_case driveLoopEmptySeg chain
  [(0x8000442c#64, 0x01013783#32),
   (0x80004430#64, 0x00050a93#32)]
    terminator ⟨0x80004434#64, 0x0ef05063#32, 0x63#8, 0x50#8, 0xf0#8, 0x0e#8,
      .br bop.BGE true, 0, 15, 0x00e0#13, 0#21, 0#12⟩

/-- The empty-route setup row.  Its only non-mechanical inputs are the loaded
count word and the true branch guard, both contained in the supplied
`ChainFacts`. -/
theorem hLoopEmpty_of_row
    (sp a0 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hData : ∀ (c2 : Config),
        c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
        GoodState c2.σ → c2.tick < 2 →
        (∃ w, c2.σ.regs.get? Register.minstret = some w) →
        c2.σ.mem = m0 ∧
        GHolds c2.σ (driveLoopSetupAL sp a0) ∧
        KeysOK (keysG (driveLoopSetupAL sp a0)) ∧
        ChainFacts c2.σ.mem c2.σ.mem (driveLoopSetupAL sp a0) lds
          driveLoopEmptySeg) :
    ∀ (c2 : Config),
        c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
        GoodState c2.σ → c2.tick < 2 →
        (∃ w, c2.σ.regs.get? Register.minstret = some w) →
        SegLanded c2 (0x80004514#64) := by
  intro c2 hpc hG htick hmi
  obtain ⟨hdmem, hdL, hdkeys, hdfacts⟩ := hData c2 hpc hG htick hmi
  have hT : Triple
      (SegPre driveLoopEmptySeg (driveLoopSetupAL sp a0) lds 0x8000442c#64 m0)
      (fun c' => c'.σ.regs.get? Register.PC = some (0x80004514#64 : BitVec 64) ∧
        GoodState c'.σ ∧ c'.tick < 2 ∧
        (∃ w, c'.σ.regs.get? Register.minstret = some w)) := by
    apply segToTriple driveLoopEmptySeg (driveLoopSetupAL sp a0) lds
      0x8000442c#64 m0 _
      (by
        have h : keysG (driveLoopSetupAL sp a0) = [2, 10] := rfl
        rw [h]
        show ChainOK 0x8000442c#64 [2, 10] driveLoopEmptySeg
        decide)
    intro σ' i' u' hG' hi' _hmem' hpc' hmi' _hregs
    refine ⟨?_, hG', hi', hmi'⟩
    rw [hpc']
    rfl
  obtain ⟨c', hsteps, hpcE, hG', htickE, hmiE⟩ :=
    hT c2 ⟨hG, hdmem, hpc, hmi, hdL, hdkeys, hdfacts, htick⟩
  exact ⟨c', hsteps, hpcE, hG', htickE, hmiE⟩

/-- Representation and frame data needed after the empty-count branch has
landed directly at the normal epilogue. -/
structure EmptyExitFields (cE : Config) where
  g : (R : Register) → Option (RegisterType R)
  N : NativeAddrs
  A : Arena
  SL : StackLayout
  φf : Addr → Nat
  φc : Addr → Nat
  m0 : Mem
  run_code : Code.Interp_runLoaded m0
  return_latch : g Register.x21 = some (0#64 : BitVec 64)
  exit : SegExit g N A SL φf φc initSt.store.frames.size
    initSt.store.closures.size initSt interpNormalExitPC m0 cE

/-- Build the empty-route epilogue fields from `InterpRunReadyFacts`.  The only
dynamic facts required are stack-only memory change, output preservation, code
preservation, and the clean setjmp latch. -/
def emptyExitFields_of_ready
    {c0 cE : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c0 stmts count inp N A φf φc aLeft)
    (hgood : GoodState cE.σ) (htick : cE.tick < 2)
    (hpc : cE.σ.regs.get? Register.PC = some (0x80004514#64 : BitVec 64))
    (hframe : ∀ k, ¬ LayoutInstance.interpRunWriteFootprint inp k →
      c0.σ.mem[k]? = cE.σ.mem[k]?)
    (hout : output cE.σ = output c0.σ)
    (hcode : Code.Interp_runLoaded cE.σ.mem)
    (hlatch : cE.σ.regs.get? Register.x21 = some (0#64 : BitVec 64)) :
    EmptyExitFields cE := by
  let g : (R : Register) → Option (RegisterType R) := fun R => cE.σ.regs.get? R
  have hstore : StoreRepr cE.σ.mem N A φf φc initSt.store :=
    F.store_survives cE.σ.mem hframe
  have houtE : OutRepr cE.σ initSt := hout.trans F.out
  refine
    { g := g, N := N, A := A, SL := stackSL, φf := φf, φc := φc,
      m0 := cE.σ.mem, run_code := hcode, return_latch := hlatch,
      exit := ?_ }
  refine
    { good := hgood, tick := htick,
      pc := by simpa [interpNormalExitPC] using hpc,
      store := ⟨φf, φc, PhiExtends.refl φf _, PhiExtends.refl φc _, hstore⟩,
      out := houtE, frame := fun _ _ _ => rfl,
      memFrame := fun _ _ _ => rfl, stackWin := ?_ }
  intro k hk
  simp [interpNormalExitPC, Vsa.Sim.Scaffold.stackScratchTop] at hk

/-- Carrier-based empty-exit construction used by the decoded route. -/
def emptyExitFields_of_ready_landing
    {c0 cE : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c0 stmts count inp N A φf φc aLeft)
    (L : ReadyLandingFacts inp c0 cE)
    (hgood : GoodState cE.σ) (htick : cE.tick < 2)
    (hpc : cE.σ.regs.get? Register.PC = some (0x80004514#64 : BitVec 64)) :
    EmptyExitFields cE :=
  emptyExitFields_of_ready F hgood htick hpc L.outside_writes L.output
    L.run_code L.return_latch

/-- Assemble the direct empty-program bypass from the shared spill/setjmp
prefix, the proved taken-polarity setup row, and the reduced epilogue fields. -/
theorem entryEmptySpan_of_spans
    (hSpill : ∀ (c : Config), Loaded interpRunLayout [] c → SpillLanded c)
    (hSplice : ∀ (c1 : Config) (spNew : BitVec 64),
      c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64) →
      c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64) →
      c1.σ.regs.get? Register.x2 = some spNew →
      GoodState c1.σ → c1.tick < 2 →
      SetjmpSplice c1.σ c1.tick c1.steps spNew)
    (hLoopEmpty : ∀ (c2 : Config),
      c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
      GoodState c2.σ → c2.tick < 2 →
      (∃ w, c2.σ.regs.get? Register.minstret = some w) →
      SegLanded c2 (0x80004514#64))
    (hFields : ∀ (cE : Config),
      cE.σ.regs.get? Register.PC = some (0x80004514#64 : BitVec 64) →
      GoodState cE.σ → cE.tick < 2 → EmptyExitFields cE) :
    EntryEmptySpan interpRunLayout := by
  intro c hL
  obtain ⟨c1, spNew, s1steps, s1pc, s1ra, s1sp, s1good, s1tick, _s1mi⟩ :=
    hSpill c hL
  obtain ⟨σ2, i2, u2, s2steps, s2tick, s2good, s2pc, _s2a0, _s2sp, s2mi⟩ :=
    hSplice c1 spNew s1pc s1ra s1sp s1good s1tick
  let c2 : Config := ⟨σ2, i2, u2⟩
  obtain ⟨cE, sEsteps, sEpc, sEgood, sEtick, _sEmi⟩ :=
    hLoopEmpty c2 s2pc s2good s2tick s2mi
  have F := hFields cE sEpc sEgood sEtick
  exact ⟨cE, F.g, F.N, F.A, F.SL, F.φf, F.φc, F.m0,
    (s1steps.trans s2steps).trans sEsteps, F.run_code, F.return_latch, F.exit⟩

/-- Ready-boundary form of the empty route.  A preservation-aware taken-branch
landing removes the former whole `EmptyExitFields` supplier. -/
theorem entryEmptySpan_of_ready_spans
    (hSpill : ∀ (c : Config), Loaded interpRunLayout [] c → SpillLanded c)
    (hSplice : ∀ (c1 : Config) (spNew : BitVec 64),
      c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64) →
      c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64) →
      c1.σ.regs.get? Register.x2 = some spNew →
      GoodState c1.σ → c1.tick < 2 →
      SetjmpSplice c1.σ c1.tick c1.steps spNew)
    (hLoopEmpty : ∀ (inp : BitVec 64) (c0 c2 : Config),
      c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
      GoodState c2.σ → c2.tick < 2 →
      (∃ w, c2.σ.regs.get? Register.minstret = some w) →
      ReadySegLanded inp c0 c2 (0x80004514#64)) :
    EntryEmptySpan interpRunLayout := by
  intro c hL
  have hLoaded := hL
  obtain ⟨_stmts, _count, _hprog, inp, N, A, φf, φc, aLeft, F0⟩ := hL
  obtain ⟨c1, spNew, s1steps, s1pc, s1ra, s1sp, s1good, s1tick, _s1mi⟩ :=
    hSpill c hLoaded
  obtain ⟨σ2, i2, u2, s2steps, s2tick, s2good, s2pc, _s2a0, _s2sp, s2mi⟩ :=
    hSplice c1 spNew s1pc s1ra s1sp s1good s1tick
  let c2 : Config := ⟨σ2, i2, u2⟩
  obtain ⟨cE, sEsteps, sEpc, sEgood, sEtick, _sEmi, L⟩ :=
    hLoopEmpty inp c c2 s2pc s2good s2tick s2mi
  let E := emptyExitFields_of_ready_landing F0 L sEgood sEtick sEpc
  exact ⟨cE, E.g, E.N, E.A, E.SL, E.φf, E.φc, E.m0,
    (s1steps.trans s2steps).trans sEsteps, E.run_code, E.return_latch, E.exit⟩

/-- Empty-program capstone.  The taken `blez` machine run is discharged by the
new polarity row; the shared setjmp splice remains the same named input as the
nonempty drive. -/
theorem entryEmptySpan_closed
    (spA a0A : BitVec 64) (ldsA : List (List (BitVec 8)))
    (m0A : Std.ExtHashMap Nat (BitVec 8))
    (hSpill : ∀ (c : Config), Loaded interpRunLayout [] c → SpillLanded c)
    (hSplice : ∀ (c1 : Config) (spNew : BitVec 64),
      c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64) →
      c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64) →
      c1.σ.regs.get? Register.x2 = some spNew →
      GoodState c1.σ → c1.tick < 2 →
      SetjmpSplice c1.σ c1.tick c1.steps spNew)
    (hData : ∀ (c2 : Config),
      c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
      GoodState c2.σ → c2.tick < 2 →
      (∃ w, c2.σ.regs.get? Register.minstret = some w) →
      c2.σ.mem = m0A ∧ GHolds c2.σ (driveLoopSetupAL spA a0A) ∧
      KeysOK (keysG (driveLoopSetupAL spA a0A)) ∧
      ChainFacts c2.σ.mem c2.σ.mem (driveLoopSetupAL spA a0A) ldsA
        driveLoopEmptySeg)
    (hFields : ∀ (cE : Config),
      cE.σ.regs.get? Register.PC = some (0x80004514#64 : BitVec 64) →
      GoodState cE.σ → cE.tick < 2 → EmptyExitFields cE) :
    EntryEmptySpan interpRunLayout :=
  entryEmptySpan_of_spans hSpill hSplice
    (hLoopEmpty_of_row spA a0A ldsA m0A hData) hFields

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
    (hFields : ∀ (p : Program) (cH : Config),
        cH.σ.regs.get? Register.PC = some (0x8000448c#64 : BitVec 64) →
        GoodState cH.σ → cH.tick < 2 → SegEntryFields p cH) :
    ∀ s ss, InterpInitStoreRepr interpRunLayout (s :: ss) := by
  intro s ss c hL
  -- 1. spill body ≫ jal setjmp → parked at setjmp entry, sp exposed.
  obtain ⟨c1, spNew, s1steps, s1pc, s1ra, s1sp, s1good, s1tick, _s1mi⟩ :=
    hSpill (s :: ss) c hL
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
  have F := hFields (s :: ss) cB sBpc sBgood sBtick
  -- compose the four runs (the middle Steps share the same underlying config).
  have hSteps : Steps c cB :=
    (((s1steps.trans s2steps).trans sAsteps).trans sBsteps)
  refine ⟨cB, F.g, F.N, F.A, F.SL, F.φf, F.φc, F.dLeft, F.aLeft,
    F.sp, F.aRet, F.m0, hSteps, F.run_code, F.return_latch, ?_, F.seq_entry⟩
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

`driveToLoopHead_of_spans` produces `InterpInitStoreRepr interpRunLayout` for
each nonempty program.  It feeds the nonempty term and divergence consumers. -/

/-- The assembled nonempty drive is `DriveToLoopHead interpRunLayout`.  Given the same five span
seams, the machine assembly closes the shared drive residual for the concrete
layout, hence — via `EntryDrive.interpInitStoreRepr_of_driveToLoopHead` and
`divEntryDriveNonempty_of_driveToLoopHead` — both nonempty entry consumers. -/
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
    (hFields : ∀ (p : Program) (cH : Config),
        cH.σ.regs.get? Register.PC = some (0x8000448c#64 : BitVec 64) →
        GoodState cH.σ → cH.tick < 2 → SegEntryFields p cH) :
    DriveToLoopHead interpRunLayout := by
  intro s ss c hL
  -- re-run the span composition (as `driveToLoopHead_of_spans`), emitting the
  -- amended drive's `Interp_runLoaded m0` conjunct from `SegEntryFields.run_code`.
  obtain ⟨c1, spNew, s1steps, s1pc, s1ra, s1sp, s1good, s1tick, _s1mi⟩ :=
    hSpill (s :: ss) c hL
  obtain ⟨σ2, i2, u2, s2steps, s2tick, s2good, s2pc, s2a0, s2sp, s2mi⟩ :=
    hSplice c1 spNew s1pc s1ra s1sp s1good s1tick
  obtain ⟨cA, sAsteps, sApc, sAgood, sAtick, sAmi⟩ :=
    hLoopA ⟨σ2, i2, u2⟩ s2pc s2good s2tick s2mi
  obtain ⟨cB, sBsteps, sBpc, sBgood, sBtick, sBmi⟩ :=
    hLoopB cA sApc sAgood sAtick sAmi
  have F := hFields (s :: ss) cB sBpc sBgood sBtick
  have hSteps : Steps c cB :=
    (((s1steps.trans s2steps).trans sAsteps).trans sBsteps)
  refine ⟨cB, F.g, F.N, F.A, F.SL, F.φf, F.φc, F.dLeft, F.aLeft,
    F.sp, F.aRet, F.m0, hSteps, F.run_code, F.return_latch, ?_, F.seq_entry⟩
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

/-- Preservation-aware nonempty drive.  It consumes the real ready witness and
an enriched loop-B landing.  The sole semantic bridge left explicit is turning
the represented statement array plus concrete loop registers into the indexed
cursor/head predicates. -/
theorem driveToLoopHead_of_ready_spans
    (hSpill : ∀ (p : Program) (c : Config),
      Loaded interpRunLayout p c → SpillLanded c)
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
    (hLoopB : ∀ (s : Vsa.While.Stmt) (ss : List Vsa.While.Stmt)
      (inp : BitVec 64) (c0 c3 : Config),
      Loaded interpRunLayout (s :: ss) c0 →
      c3.σ.regs.get? Register.PC = some (0x80004438#64 : BitVec 64) →
      GoodState c3.σ → c3.tick < 2 →
      (∃ w, c3.σ.regs.get? Register.minstret = some w) →
      ReadyLoopHeadLanded inp c0 c3)
    (hSeqGround : ∀ (s : Vsa.While.Stmt) (ss : List Vsa.While.Stmt) (c0 cH : Config)
      (stmts count : Nat) (inp : BitVec 64) (N : NativeAddrs) (A : Arena)
      (φf φc : Addr → Nat) (aLeft : Nat)
      (sp cursor finish : BitVec 64),
      ProgramRepr c0.σ.mem stmts count (s :: ss) →
      LayoutInstance.InterpRunReadyFacts c0 stmts count inp N A φf φc aLeft →
      ReadyLandingFacts inp c0 cH → LoopHeadRegs cH sp cursor finish →
      ∃ aRet : BitVec 64,
        ExecSeqCursorRepr .interpRun cH.σ.mem φf 0 (s :: ss)
          sp aRet cH.σ.regs.get? ∧
        ExecSeqHeadGround .interpRun cH.σ.mem cH.σ.regs.get?
          stackSL A φf sp aRet initSt 0 0 (s :: ss)) :
    DriveToLoopHead interpRunLayout := by
  intro s ss c hL
  have hLoaded := hL
  obtain ⟨stmts, count, hprog, inp, N, A, φf, φc, aLeft, F0⟩ := hL
  obtain ⟨c1, spNew, s1steps, s1pc, s1ra, s1sp, s1good, s1tick, _s1mi⟩ :=
    hSpill (s :: ss) c hLoaded
  obtain ⟨σ2, i2, u2, s2steps, s2tick, s2good, s2pc, _s2a0, _s2sp, s2mi⟩ :=
    hSplice c1 spNew s1pc s1ra s1sp s1good s1tick
  let c2 : Config := ⟨σ2, i2, u2⟩
  obtain ⟨cA, sAsteps, sApc, sAgood, sAtick, sAmi⟩ :=
    hLoopA c2 s2pc s2good s2tick s2mi
  obtain ⟨cH, sp, cursor, finish, sBsteps, sBpc, sBgood, sBtick,
      sBmi, L, R⟩ := hLoopB s ss inp c cA hLoaded sApc sAgood sAtick sAmi
  obtain ⟨aRet, hcursor, hhead⟩ :=
    hSeqGround s ss c cH stmts count inp N A φf φc aLeft
      sp cursor finish hprog F0 L R
  let Fields := segEntryFields_of_ready_landing (p := s :: ss)
    (by simp) F0 L sBgood sBtick sBpc sp aRet cursor finish R
      hcursor hhead sBmi
  have hSteps : Steps c cH :=
    (((s1steps.trans s2steps).trans sAsteps).trans sBsteps)
  exact ⟨cH, Fields.g, Fields.N, Fields.A, Fields.SL, Fields.φf, Fields.φc,
    Fields.dLeft, Fields.aLeft, Fields.sp, Fields.aRet, Fields.m0,
    hSteps, Fields.run_code, Fields.return_latch,
    { good := sBgood, tick := sBtick,
      pc := by simpa [interpLoopHeadPC] using sBpc,
      store := Fields.store, out := Fields.out, mem := Fields.mem,
      frame := Fields.frame, depth_budget := Fields.depth_budget,
      arena_budget := Fields.arena_budget }, Fields.seq_entry⟩

/-- Route-indexed nonempty entry assembly.  The prefix reaches setup-B with a
ready landing; the decoded B producer preserves it and exposes loop registers.
Only the semantic statement/cursor bridge remains separate. -/
theorem driveToLoopHead_of_ready_routes
    (hSetupA : ∀ (s : Vsa.While.Stmt) (ss : List Vsa.While.Stmt) (c : Config)
      (stmts count : Nat) (inp : BitVec 64) (N : NativeAddrs) (A : Arena)
      (φf φc : Addr → Nat) (aLeft : Nat),
      ProgramRepr c.σ.mem stmts count (s :: ss) →
      LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft →
      ReadySegLanded inp c c (0x80004438#64))
    (hLoopB : ∀ (s : Vsa.While.Stmt) (ss : List Vsa.While.Stmt) (c cA : Config)
      (stmts count : Nat) (inp : BitVec 64) (N : NativeAddrs) (A : Arena)
      (φf φc : Addr → Nat) (aLeft : Nat),
      ProgramRepr c.σ.mem stmts count (s :: ss) →
      LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft →
      ReadyLandingFacts inp c cA →
      cA.σ.regs.get? Register.PC = some (0x80004438#64 : BitVec 64) →
      GoodState cA.σ → cA.tick < 2 →
      (∃ w, cA.σ.regs.get? Register.minstret = some w) →
      ReadyLoopHeadLanded inp c cA)
    (hSeqGround : ∀ (s : Vsa.While.Stmt) (ss : List Vsa.While.Stmt) (c cH : Config)
      (stmts count : Nat) (inp : BitVec 64) (N : NativeAddrs) (A : Arena)
      (φf φc : Addr → Nat) (aLeft : Nat)
      (sp cursor finish : BitVec 64),
      ProgramRepr c.σ.mem stmts count (s :: ss) →
      LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft →
      ReadyLandingFacts inp c cH → LoopHeadRegs cH sp cursor finish →
      ∃ aRet : BitVec 64,
        ExecSeqCursorRepr .interpRun cH.σ.mem φf 0 (s :: ss)
          sp aRet cH.σ.regs.get? ∧
        ExecSeqHeadGround .interpRun cH.σ.mem cH.σ.regs.get?
          stackSL A φf sp aRet initSt 0 0 (s :: ss)) :
    DriveToLoopHead interpRunLayout := by
  intro s ss c hLoaded
  obtain ⟨stmts, count, hprog, inp, N, A, φf, φc, aLeft, F⟩ := hLoaded
  obtain ⟨cA, hstepsA, hpcA, hgoodA, htickA, hmiA, LA⟩ :=
    hSetupA s ss c stmts count inp N A φf φc aLeft hprog F
  obtain ⟨cH, sp, cursor, finish, hstepsB, hpcH, hgoodH, htickH, hmiH, LH, RH⟩ :=
    hLoopB s ss c cA stmts count inp N A φf φc aLeft hprog F LA
      hpcA hgoodA htickA hmiA
  obtain ⟨aRet, hcursor, hhead⟩ :=
    hSeqGround s ss c cH stmts count inp N A φf φc aLeft
      sp cursor finish hprog F LH RH
  let Fields := segEntryFields_of_ready_landing (p := s :: ss)
    (by simp) F LH hgoodH htickH hpcH sp aRet cursor finish RH
      hcursor hhead hmiH
  exact ⟨cH, Fields.g, Fields.N, Fields.A, Fields.SL, Fields.φf, Fields.φc,
    Fields.dLeft, Fields.aLeft, Fields.sp, Fields.aRet, Fields.m0,
    hstepsA.trans hstepsB, Fields.run_code, Fields.return_latch,
    { good := hgoodH, tick := htickH,
      pc := by simpa [interpLoopHeadPC] using hpcH,
      store := Fields.store, out := Fields.out, mem := Fields.mem,
      frame := Fields.frame, depth_budget := Fields.depth_budget,
      arena_budget := Fields.arena_budget }, Fields.seq_entry⟩

/-- Route-indexed empty entry assembly.  The full taken route lands at the
normal epilogue with a ready carrier, from which the initial store/output exit
package is constructed directly. -/
theorem entryEmptySpan_of_ready_route
    (hEmpty : ∀ (c : Config) (stmts count : Nat) (inp : BitVec 64)
      (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat) (aLeft : Nat),
      ProgramRepr c.σ.mem stmts count [] →
      LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft →
      ReadySegLanded inp c c (0x80004514#64)) :
    EntryEmptySpan interpRunLayout := by
  intro c hLoaded
  obtain ⟨stmts, count, hprog, inp, N, A, φf, φc, aLeft, F⟩ := hLoaded
  obtain ⟨cE, hsteps, hpcE, hgoodE, htickE, _hmiE, LE⟩ :=
    hEmpty c stmts count inp N A φf φc aLeft hprog F
  let E := emptyExitFields_of_ready_landing F LE hgoodE htickE hpcE
  exact ⟨cE, E.g, E.N, E.A, E.SL, E.φf, E.φc, E.m0,
    hsteps, E.run_code, E.return_latch, E.exit⟩

#print axioms driveToLoopHead_interpRunLayout
#print axioms driveToLoopHead_of_ready_routes
#print axioms entryEmptySpan_of_ready_route

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

private theorem driveLoopSetupA_noWrites
    (m : Mem) (sp : BitVec 64) (lds : List (List (BitVec 8))) :
    writeLog m (evalBlocks driveLoopSetupASeg
      (SegEvalState.init (driveLoopSetupAL sp 0#64) lds)).log = m := by
  rfl

private theorem driveLoopEmpty_noWrites
    (m : Mem) (sp : BitVec 64) (lds : List (List (BitVec 8))) :
    writeLog m (evalBlocks driveLoopEmptySeg
      (SegEvalState.init (driveLoopSetupAL sp 0#64) lds)).log = m := by
  rfl

private theorem driveLoopSetupB_noWrites
    (m : Mem) (sp gp : BitVec 64) (lds : List (List (BitVec 8))) :
    writeLog m (evalBlocks driveLoopSetupBSeg
      (SegEvalState.init (driveLoopSetupBL sp gp) lds)).log = m := by
  rfl

/-- Direct-data form of the setup-A row. -/
theorem hLoopA_ready_of_data
    (inp : BitVec 64) (c0 : Config)
    (sp : BitVec 64) (lds : List (List (BitVec 8))) (m0 : Mem)
    (c2 : Config) (P : ReadyPrefixFacts inp c0 c2)
    (hpc : c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64))
    (hG : GoodState c2.σ) (htick : c2.tick < 2)
    (hmi : ∃ w, c2.σ.regs.get? Register.minstret = some w)
    (D : SegEntryData driveLoopSetupASeg (driveLoopSetupAL sp 0#64) lds m0 c2) :
    ReadySegLanded inp c0 c2 (0x80004438#64) := by
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hregs, _hframe⟩ :=
    segEval_sound driveLoopSetupASeg c2.σ c2.tick c2.steps 0x8000442c#64 vm
      (driveLoopSetupAL sp 0#64) lds hG hpc hvm D.hL D.keys D.facts
      (by
        have h : keysG (driveLoopSetupAL sp 0#64) = [2, 10] := rfl
        rw [h]
        show ChainOK 0x8000442c#64 [2, 10] driveLoopSetupASeg
        decide) htick
  let c' : Config := ⟨σ', i', c2.steps + evalBlocksFuel driveLoopSetupASeg⟩
  have hmem2 : σ'.mem = c2.σ.mem :=
    hmem'.trans (driveLoopSetupA_noWrites c2.σ.mem sp lds)
  have hlk : lookupG 21 (evalBlocks driveLoopSetupASeg
      (SegEvalState.init (driveLoopSetupAL sp 0#64) lds)).regs = some 0#64 := by
    rfl
  have hlatch : σ'.regs.get? Register.x21 = some (0#64 : BitVec 64) := by
    exact gholds_lookup _ hregs hlk
  refine ⟨c', hsteps, ?_, hG', hi', hmi', ?_⟩
  · simpa [c'] using hpc'
  · refine { outside_writes := ?_, output := ?_, run_code := ?_, return_latch := hlatch }
    · intro k hk
      exact (P.outside_writes k hk).trans (congrArg (fun m : Mem => m[k]?) hmem2.symm)
    · unfold output
      exact (congrArg (fun a : Array String => String.join a.toList) hout').trans P.output
    · rw [hmem2]
      exact P.run_code

/-- Direct-data taken `blez` row.  The shared setup body establishes x21=0
before branching to the normal exit. -/
theorem hLoopEmpty_ready_of_data
    (inp : BitVec 64) (c0 : Config)
    (sp : BitVec 64) (lds : List (List (BitVec 8))) (m0 : Mem)
    (c2 : Config) (P : ReadyPrefixFacts inp c0 c2)
    (hpc : c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64))
    (hG : GoodState c2.σ) (htick : c2.tick < 2)
    (hmi : ∃ w, c2.σ.regs.get? Register.minstret = some w)
    (D : SegEntryData driveLoopEmptySeg (driveLoopSetupAL sp 0#64) lds m0 c2) :
    ReadySegLanded inp c0 c2 (0x80004514#64) := by
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hregs, _hframe⟩ :=
    segEval_sound driveLoopEmptySeg c2.σ c2.tick c2.steps 0x8000442c#64 vm
      (driveLoopSetupAL sp 0#64) lds hG hpc hvm D.hL D.keys D.facts
      (by
        have h : keysG (driveLoopSetupAL sp 0#64) = [2, 10] := rfl
        rw [h]
        show ChainOK 0x8000442c#64 [2, 10] driveLoopEmptySeg
        decide) htick
  let cE : Config := ⟨σ', i', c2.steps + evalBlocksFuel driveLoopEmptySeg⟩
  have hmem2 : σ'.mem = c2.σ.mem :=
    hmem'.trans (driveLoopEmpty_noWrites c2.σ.mem sp lds)
  have hlk : lookupG 21 (evalBlocks driveLoopEmptySeg
      (SegEvalState.init (driveLoopSetupAL sp 0#64) lds)).regs = some 0#64 := by
    rfl
  have hlatch : σ'.regs.get? Register.x21 = some (0#64 : BitVec 64) :=
    gholds_lookup _ hregs hlk
  refine ⟨cE, hsteps, ?_, hG', hi', hmi', ?_⟩
  · simpa [cE] using hpc'
  · refine { outside_writes := ?_, output := ?_, run_code := ?_, return_latch := hlatch }
    · intro k hk
      exact (P.outside_writes k hk).trans
        (congrArg (fun m : Mem => m[k]?) hmem2.symm)
    · unfold output
      exact (congrArg (fun a : Array String => String.join a.toList) hout').trans
        P.output
    · rw [hmem2]
      exact P.run_code

/-- Loop-setup A upgrades the prefix carrier to a ready landing.  Its decoded
`mv s5,a0`, with the first-return `a0 = 0`, establishes the x21 latch. -/
theorem hLoopA_ready_of_row
    (inp : BitVec 64) (c0 : Config)
    (sp : BitVec 64) (lds : List (List (BitVec 8))) (m0 : Mem)
    (hData : ∀ (c2 : Config),
      c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
      GoodState c2.σ → c2.tick < 2 →
      (∃ w, c2.σ.regs.get? Register.minstret = some w) →
      SegEntryData driveLoopSetupASeg (driveLoopSetupAL sp 0#64) lds m0 c2) :
    ∀ (c2 : Config), ReadyPrefixFacts inp c0 c2 →
      c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
      GoodState c2.σ → c2.tick < 2 →
      (∃ w, c2.σ.regs.get? Register.minstret = some w) →
      ReadySegLanded inp c0 c2 (0x80004438#64) := by
  intro c2 P hpc hG htick hmi
  exact hLoopA_ready_of_data inp c0 sp lds m0 c2 P hpc hG htick hmi
    (hData c2 hpc hG htick hmi)

/-- Loop-setup B preserves the ready carrier and exposes the concrete stack,
cursor, and finish registers required at the sequence loop head. -/
theorem hLoopB_ready_of_row
    (inp : BitVec 64) (c0 : Config)
    (sp gp : BitVec 64) (lds : List (List (BitVec 8))) (m0 : Mem)
    (hData : ∀ (c3 : Config),
      c3.σ.regs.get? Register.PC = some (0x80004438#64 : BitVec 64) →
      GoodState c3.σ → c3.tick < 2 →
      (∃ w, c3.σ.regs.get? Register.minstret = some w) →
      SegEntryData driveLoopSetupBSeg (driveLoopSetupBL sp gp) lds m0 c3) :
    ∀ (c3 : Config), ReadyLandingFacts inp c0 c3 →
      c3.σ.regs.get? Register.PC = some (0x80004438#64 : BitVec 64) →
      GoodState c3.σ → c3.tick < 2 →
      (∃ w, c3.σ.regs.get? Register.minstret = some w) →
      ReadyLoopHeadLanded inp c0 c3 := by
  intro c3 P hpc hG htick hmi
  obtain ⟨vm, hvm⟩ := hmi
  have D := hData c3 hpc hG htick ⟨vm, hvm⟩
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hregs, hframe⟩ :=
    segEval_sound driveLoopSetupBSeg c3.σ c3.tick c3.steps 0x80004438#64 vm
      (driveLoopSetupBL sp gp) lds hG hpc hvm D.hL D.keys D.facts
      (by
        have h : keysG (driveLoopSetupBL sp gp) = [2, 3] := rfl
        rw [h]
        show ChainOK 0x80004438#64 [2, 3] driveLoopSetupBSeg
        decide) htick
  let cH : Config := ⟨σ', i', c3.steps + evalBlocksFuel driveLoopSetupBSeg⟩
  let outL := (evalBlocks driveLoopSetupBSeg
    (SegEvalState.init (driveLoopSetupBL sp gp) lds)).regs
  let cursor := (lookupG 8 outL).getD 0#64
  let finish := (lookupG 18 outL).getD 0#64
  have hmem3 : σ'.mem = c3.σ.mem :=
    hmem'.trans (driveLoopSetupB_noWrites c3.σ.mem sp gp lds)
  have hspL : lookupG 2 outL = some sp := by rfl
  have hcursorL : lookupG 8 outL = some cursor := by rfl
  have hfinishL : lookupG 18 outL = some finish := by rfl
  have hspR : σ'.regs.get? Register.x2 = some sp := gholds_lookup _ hregs hspL
  have hcursorR : σ'.regs.get? Register.x8 = some cursor := gholds_lookup _ hregs hcursorL
  have hfinishR : σ'.regs.get? Register.x18 = some finish := gholds_lookup _ hregs hfinishL
  have hlatchEq : σ'.regs.get? Register.x21 = c3.σ.regs.get? Register.x21 :=
    hframe Register.x21 (by decide) (by decide)
  have L : ReadyLandingFacts inp c0 cH := by
    refine { outside_writes := ?_, output := ?_, run_code := ?_, return_latch := hlatchEq.trans P.return_latch }
    · intro k hk
      simpa [cH] using
        (P.outside_writes k hk).trans (congrArg (fun m : Mem => m[k]?) hmem3.symm)
    · unfold output
      simpa [cH] using
        (congrArg (fun a : Array String => String.join a.toList) hout').trans P.output
    · simpa [cH] using (hmem3.symm ▸ P.run_code)
  have R : LoopHeadRegs cH sp cursor finish := by
    exact { sp_reg := by simpa [cH] using hspR, cursor_reg := by simpa [cH] using hcursorR, finish_reg := by simpa [cH] using hfinishR }
  refine ⟨cH, sp, cursor, finish, hsteps, ?_, hG', hi', hmi', L, R⟩
  · simpa [cH] using hpc'

#print axioms hLoopA_of_row
#print axioms hLoopB_of_row
#print axioms hLoopA_ready_of_row
#print axioms hLoopB_ready_of_row

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
    GoodState σ' → Code.Interp_runLoaded σ'.mem → i' < 2 →
    σ'.regs.get? Register.PC = some (0x80004428#64 : BitVec 64) →
    σ'.regs.get? Register.x10 = some (0#64 : BitVec 64) →
    σ'.regs.get? Register.x2 = some spNew →
    (∃ w, σ'.regs.get? Register.minstret = some w) →
    ∃ (σ2 : MState) (i2 u2 : Nat),
      Steps ⟨σ', i', u'⟩ ⟨σ2, i2, u2⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.mem = σ'.mem ∧ σ2.sailOutput = σ'.sailOutput ∧
      σ2.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) ∧
      σ2.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧
      σ2.regs.get? Register.x2 = some spNew ∧
      (∃ w, σ2.regs.get? Register.minstret = some w)

/-- The concrete `bnez a0` first-return fallthrough. -/
theorem bnezFallthrough_of_loaded (spNew : BitVec 64) : BnezFallthrough spNew := by
  intro σ i u hG hload hi hpc ha0 hsp hmi
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Code.interp_run_at_80004428 hload
  have hx10 : (afterNextPC (afterPrelude σ) 0x80004428#64).regs.get? Register.x10 =
      some (0#64 : BitVec 64) := by
    rw [get?_afterNextPC σ 0x80004428#64 _ (by decide) (by decide)]
    exact ha0
  have hexec :
      (execute (instruction.BTYPE (0x00e0#13, regidx.Regidx 0x00#5,
        regidx.Regidx 0x0a#5, bop.BNE))).run
          (afterNextPC (afterPrelude σ) 0x80004428#64) =
        .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ 0x80004428#64) :=
    execute_btype_bne_nottaken (0x00e0#13) (regidx.Regidx 0x0a#5)
      (regidx.Regidx 0x00#5) (0#64) (0#64)
      (afterNextPC (afterPrelude σ) 0x80004428#64)
      (rX_bits_x10 _ _ hx10) (rX_bits_zero _) (by decide)
  obtain ⟨σ2, i2, hs, hi2, hG2, hmem2, hobs⟩ :=
    stepObs_branch_nottaken σ i u 0x80004428#64 vm 0x00e0#13
      (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5) bop.BNE
      0x0e051063#32 0x63#8 0x10#8 0x05#8 0x0e#8 hG hpc hvm
      (by decide) (by decide)
      (DecodeTable.decode_0e051063 (afterPrelude σ)
        (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
      hexec hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi
  refine ⟨σ2, i2, u + 1, Steps.single hs, hi2, hG2, hmem2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hobs.out]
  · simpa using obs_branch_nottaken_pc hobs
  · exact obs_branch_nottaken_other' hobs Register.x10 (by decide) ha0
  · exact obs_branch_nottaken_other' hobs Register.x2 (by decide) hsp
  · exact obs_branch_nottaken_minstret hobs

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
        SetjmpGeom c1) :
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
      gmem, gloaded, grun, ga0, graA, gs0, gs1, gs2, gs3, gs4, gs5, gs6, gs7, gs8, gs9,
      gs10, gs11, gwin, gframe⟩ :=
    hGeom c1 spNew hpc hra hsp hG htick
  -- Run `setjmp_spec` (first return) from the geometry.
  obtain ⟨cR, hstepsR, hpostR⟩ :=
    setjmp_spec g jb (0x80004428#64) s0v s1v s2v s3v s4v s5v
      s6v s7v s8v s9v s10v s11v spNew m0 c1.σ.sailOutput c1
      ⟨hG, gloaded, grun, gmem, rfl, hpc, ga0, hra, graA, gs0, gs1, gs2, gs3,
        gs4, gs5, gs6, gs7, gs8, gs9, gs10, gs11, hsp, gwin,
        hG.minstret, htick, gframe⟩
  obtain ⟨hGR, htickR, hpcR, ha0R, hspR, _hmemR, hrunR, _houtR, hmiR, _hframeR⟩ := hpostR
  -- Now the not-taken `bnez` fallthrough.
  obtain ⟨σ2, i2, u2, hsteps2, hi2, hG2, _hmem2, _hout2,
      hpc2, ha02, hsp2, hmi2⟩ :=
    bnezFallthrough_of_loaded spNew cR.σ cR.tick cR.steps hGR hrunR htickR
      hpcR ha0R hspR hmiR
  refine ⟨σ2, i2, u2, ?_, hi2, hG2, hpc2, ha02, hsp2, hmi2⟩
  have hstepsC : Steps ⟨c1.σ, c1.tick, c1.steps⟩ cR := hstepsR
  exact hstepsC.trans hsteps2

/-- The concrete setjmp spec and decoded not-taken `bnez` preserve the full
entry prefix carrier. -/
theorem readySetjmpSplice_of_geom
    {inp : BitVec 64} {c0 c1 : Config} {spNew : BitVec 64}
    (P : ReadyPrefixFacts inp c0 c1)
    (G : SetjmpGeom c1)
    (hpc : c1.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64))
    (hra : c1.σ.regs.get? Register.x1 = some (0x80004428#64 : BitVec 64))
    (hsp : c1.σ.regs.get? Register.x2 = some spNew)
    (hinp : c1.σ.regs.get? Register.x10 = some (inp + 16#64))
    (hinp16 : (inp + 16#64).toNat = inp.toNat + 16)
    (hgood : GoodState c1.σ) (htick : c1.tick < 2) :
    ReadySetjmpSplice inp c0 c1 spNew := by
  obtain ⟨jb, s0v, s1v, s2v, s3v, s4v, s5v, s6v, s7v, s8v, s9v, s10v,
      s11v, g, m0, gmem, gloaded, grun, ga0, graA, gs0, gs1, gs2, gs3, gs4,
      gs5, gs6, gs7, gs8, gs9, gs10, gs11, gwin, gframe⟩ := G
  have hjb : jb = inp + 16#64 := by
    exact Option.some.inj (ga0.symm.trans hinp)
  obtain ⟨cR, hstepsR, hpostR⟩ :=
    setjmp_spec g jb 0x80004428#64 s0v s1v s2v s3v s4v s5v
      s6v s7v s8v s9v s10v s11v spNew m0 c1.σ.sailOutput c1
      ⟨hgood, gloaded, grun, gmem, rfl, hpc, ga0, hra, graA, gs0, gs1, gs2,
        gs3, gs4, gs5, gs6, gs7, gs8, gs9, gs10, gs11, hsp, gwin,
        hgood.minstret, htick, gframe⟩
  obtain ⟨hGR, htickR, hpcR, ha0R, hspR, hmemR, hrunR, houtR, hmiR,
      _hframeR⟩ := hpostR
  obtain ⟨σ2, i2, u2, hsteps2, hi2, hG2, hmem2, hout2, hpc2, ha02,
      hsp2, hmi2⟩ :=
    bnezFallthrough_of_loaded spNew cR.σ cR.tick cR.steps hGR hrunR htickR
      hpcR ha0R hspR hmiR
  let c2 : Config := ⟨σ2, i2, u2⟩
  have P2 : ReadyPrefixFacts inp c0 c2 := by
    refine { outside_writes := ?_, output := ?_, run_code := ?_ }
    · intro k hk
      have hkbuf : k < jb.toNat ∨ jb.toNat + 112 ≤ k := by
        rw [hjb]
        by_cases hlo : k < (inp + 16#64).toNat
        · exact Or.inl hlo
        · right
          apply Nat.le_of_not_gt
          intro hhi
          apply hk
          right
          rw [hinp16] at hlo hhi
          exact ⟨Nat.le_of_not_gt hlo, hhi⟩
      have hbuf := setjmpBuf_out m0 jb 0x80004428#64 s0v s1v s2v s3v s4v
        s5v s6v s7v s8v s9v s10v s11v spNew k hkbuf
      calc
        c0.σ.mem[k]? = c1.σ.mem[k]? := P.outside_writes k hk
        _ = m0[k]? := congrArg (fun m : Mem => m[k]?) gmem
        _ = cR.σ.mem[k]? := hbuf.symm.trans
          (congrArg (fun m : Mem => m[k]?) hmemR).symm
        _ = σ2.mem[k]? := (congrArg (fun m : Mem => m[k]?) hmem2).symm
        _ = c2.σ.mem[k]? := rfl
    · have hout21 : output c2.σ = output c1.σ := by
        unfold output
        simpa [c2] using congrArg (fun a : Array String => String.join a.toList)
          (hout2.trans houtR)
      exact hout21.trans P.output
    · simpa [c2] using (hmem2.symm ▸ hrunR)
  refine ⟨c2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, P2⟩
  · exact hstepsR.trans hsteps2
  · simpa [c2] using hpc2
  · simpa [c2] using ha02
  · simpa [c2] using hsp2
  · simpa [c2] using hG2
  · simpa [c2] using hi2
  · simpa [c2] using hmi2

/-- The interpreter object's first field offset does not wrap. -/
private theorem interpInput_add16_toNat
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft) :
    (inp + 16#64).toNat = inp.toNat + 16 := by
  rw [BitVec.toNat_add]
  rw [show (16#64 : BitVec 64).toNat = 16 by decide]
  have hram := F.interp_geom.in_ram
  simp only [RSub, ramRegion, ramLo, ramHi] at hram
  rw [Nat.mod_eq_of_lt (by omega)]

/-- Compose the exact spill and setjmp prefix with one concrete setup-A row
datum.  This is the nonempty `hSetupA` producer consumed by the route-indexed
top-level theorem. -/
theorem readySetupA_of_ready
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (hDataA : ∀ (c2 : Config) (sp : BitVec 64),
      ReadyPrefixFacts inp c c2 →
      c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
      c2.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) →
      c2.σ.regs.get? Register.x2 = some sp →
      GoodState c2.σ → c2.tick < 2 →
      (∃ w, c2.σ.regs.get? Register.minstret = some w) →
      ∃ lds : List (List (BitVec 8)),
        SegEntryData driveLoopSetupASeg (driveLoopSetupAL sp 0#64)
          lds c2.σ.mem c2) :
    ReadySegLanded inp c c (0x80004438#64) := by
  obtain ⟨c1, spNew, hspill, hpc1, hra1, hsp1, hinp1, hgood1, htick1,
      hmi1, P1, G1⟩ := readySpillLanded_of_ready F
  have hinp16 := interpInput_add16_toNat F
  obtain ⟨c2, hsplice, hpc2, ha02, hsp2, hgood2, htick2, hmi2, P2⟩ :=
    readySetjmpSplice_of_geom P1 G1 hpc1 hra1 hsp1 hinp1 hinp16 hgood1 htick1
  obtain ⟨lds, D⟩ :=
    hDataA c2 spNew P2 hpc2 ha02 hsp2 hgood2 htick2 hmi2
  obtain ⟨cA, hA, hpcA, hgoodA, htickA, hmiA, LA⟩ :=
    hLoopA_ready_of_data inp c spNew lds c2.σ.mem c2 P2 hpc2 hgood2
      htick2 hmi2 D
  exact ⟨cA, (hspill.trans hsplice).trans hA, hpcA, hgoodA, htickA, hmiA, LA⟩

/-- Compose the same exact prefix with the taken zero-count setup row. -/
theorem readyEmpty_of_ready
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (hDataE : ∀ (c2 : Config) (sp : BitVec 64),
      ReadyPrefixFacts inp c c2 →
      c2.σ.regs.get? Register.PC = some (0x8000442c#64 : BitVec 64) →
      c2.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) →
      c2.σ.regs.get? Register.x2 = some sp →
      GoodState c2.σ → c2.tick < 2 →
      (∃ w, c2.σ.regs.get? Register.minstret = some w) →
      ∃ lds : List (List (BitVec 8)),
        SegEntryData driveLoopEmptySeg (driveLoopSetupAL sp 0#64)
          lds c2.σ.mem c2) :
    ReadySegLanded inp c c (0x80004514#64) := by
  obtain ⟨c1, spNew, hspill, hpc1, hra1, hsp1, hinp1, hgood1, htick1,
      hmi1, P1, G1⟩ := readySpillLanded_of_ready F
  have hinp16 := interpInput_add16_toNat F
  obtain ⟨c2, hsplice, hpc2, ha02, hsp2, hgood2, htick2, hmi2, P2⟩ :=
    readySetjmpSplice_of_geom P1 G1 hpc1 hra1 hsp1 hinp1 hinp16 hgood1 htick1
  obtain ⟨lds, D⟩ :=
    hDataE c2 spNew P2 hpc2 ha02 hsp2 hgood2 htick2 hmi2
  obtain ⟨cE, hE, hpcE, hgoodE, htickE, hmiE, LE⟩ :=
    hLoopEmpty_ready_of_data inp c spNew lds c2.σ.mem c2 P2 hpc2 hgood2
      htick2 hmi2 D
  exact ⟨cE, (hspill.trans hsplice).trans hE, hpcE, hgoodE, htickE, hmiE, LE⟩

#print axioms hSplice_of_setjmpSpec
#print axioms readySetjmpSplice_of_geom
#print axioms readySetupA_of_ready
#print axioms readyEmpty_of_ready

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
Everything downstream uses the nonempty drive; the empty route is separate. -/
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
        SetjmpGeom c1)
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
    (hFields : ∀ (p : Program) (cH : Config),
        cH.σ.regs.get? Register.PC = some (0x8000448c#64 : BitVec 64) →
        GoodState cH.σ → cH.tick < 2 → SegEntryFields p cH) :
    DriveToLoopHead interpRunLayout :=
  driveToLoopHead_interpRunLayout
    hSpill
    (hSplice_of_setjmpSpec hGeom)
    (hLoopA_of_row spA a0A ldsA m0A hDataA)
    (hLoopB_of_row spB gpB ldsB m0B hDataB)
    hFields

#print axioms driveToLoopHead_closed

end Vsa.Sim
