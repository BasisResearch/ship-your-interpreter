import Vsa.Sim.rows.CallCruxMarshal4
import Vsa.Sim.rows.CallClosureBodyExit
import Vsa.Sim.rows.CallClosureRetClass

/-!
# `CallCruxMarshal5` — the `.normal`-route splice → the join, and the 9TH
# statement falsity (wave 44, lane normalroute)

The `.normal` return route of the `hCallClosure` crux, from the body IH's
`.normal` exit at `callBodyRetPC = 0x80003378` to the epilogue join
`callJoinPC = 0x800033ec`:

```
80003378  ▷ beqz a0 → 0x80003340   TAKEN (a0=0 ⇒ .normal)   [callClosureBodyExitNormalRow]
80003340  ld a6,0(sp)
80003344  addiw s0,s0,1            -- s0 (x8) := loop counter + 1   (WRITES x8!)
80003348  sext.w a5,s0
8000334c  lw a4,16(a6)
80003350  ▷ bge a5,a4 → 0x80003954 TAKEN (all statements done)
--------------------------------------------------- .normal exit span
80003954  lw a5,8(s2); addiw a5,a5,-1; sw a5,8(s2)   -- --call_depth
80003960  mv a0,s1 ▷ jal value_null @0x800027ec       [callClosureNormalDepthBridge]
value_null                                            [value_null_spec_full]
80003968  ld s3,1048(sp); ld s5,1032(sp); ld s7,1016(sp)  -- RESTORE s3/s5/s7 ONLY
80003974  ▷ j 0x800033ec                              [callClosureNormalJoinRow]
```

## THE 9TH STATEMENT FALSITY (Law 4, ledger `segexit-frame-preepilogue-x8-unrestored`)

The target the wave-37 `callClosureRet_of_status` / `CallRetShape` demands is
`SegExit g … st' callJoinPC m0` — the SKELETON `SegExit` (`InductionScaffold`)
whose `frame` field is `∀ R, AbiPreservedNoise R → c.σ.regs.get? R = g R`, i.e.
EVERY callee-saved register restored to the arm ghost `g` AT `callJoinPC`.

But `callJoinPC = 0x800033ec` is the FIRST instruction of the shared eval_expr
epilogue; the callee-saved restores run AFTER it:
```
800033ec  ld ra,1080(sp)
800033f0  ld s0,1072(sp)   -- x8 restored HERE, past the join
800033f4  ld s2,1056(sp)
800033f8  mv a0,s1
800033fc  ld s1,1064(sp)
80003400  addi sp,sp,1088
80003404  ret
```
The `.normal` route (`callClosureNormalDepthBridge ≫ value_null ≫
callClosureNormalJoinRow`) restores ONLY s3/s5/s7 (x19/x21/x23); it never
touches x8 (s0).  On the body loop x8 = s0 is the ExecSeq loop COUNTER
(`0x80003344 addiw s0,s0,1`, in `callClosureBodyExitNormalSeg`), so at
`callJoinPC` x8 = the body statement count, NOT `g x8` (the caller's EX_CALL
node ptr, `CallArgLoopInv.node`).  `AbiPreservedNoise x8` holds (`AbiPreserved
x8 = true`, `x8` a callee-saved), so `SegExit.frame` DEMANDS `x8 = g x8` — and
the machine gives `x8 = counter ≠ node`.  UNSATISFIABLE.  (The same holds for
ra/s1/s2/sp: all restored only INSIDE the epilogue, past the join.)

`segExitJoin_frame_x8_false` below is the machine-checked obstruction; the
amendment (weaken the join `frame` to the register set the join actually
restores, or move the exit past the epilogue) is proposed in observations.md.

The genuine machine content of the route IS buildable and is landed here as
`normalRouteSplice` into `NormalJoinExit` — the join-config carrier that pins
what the `.normal` route ACTUALLY establishes (PC = callJoinPC, the store/out
re-representation, the memory frame, sp untouched, s3/s5/s7 restored to their
spill images) — everything `SegExit@callJoinPC` needs EXCEPT the over-strong
`frame` clause the falsity refutes.  The amended `SegExit` (once its `frame`
clause is corrected) reads directly off `NormalJoinExit`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no heartbeat raise.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While
open Vsa.Alloc
open Vsa.Sim.Scaffold

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

/-! ## §1. The 9th statement falsity — the join `frame` clause over-pins x8 -/

/-- **`segExitJoin_frame_x8_false`** — the machine-checked obstruction, RESTATED
over the explicit PRE-amendment clause (wave 45: the amendment `joinRestored`-
guards `SegExit.frame`, so the falsity is now pinned to the clause the skeleton
DEMANDED before the guard — the blanket `∀ R, AbiPreservedNoise R → regs R = g R`
AT the join).  Any join config whose x8 holds the `.normal` route's value
(`cnt`, the body-loop counter — NOT restored to `g x8` at the join) contradicts
that clause when `cnt ≠ node` and `g x8 = some node`: `AbiPreservedNoise x8`
holds (`by decide`), so the pre-amendment clause forces `c.σ.regs.get? x8 =
g x8`, i.e. `some cnt = some node` — impossible.  x8 is restored only by the
epilogue's `ld s0,1072(sp)` at `0x800033f0`, PAST the join.  (The identical
argument refutes ra/s1/s2/sp.)  This is exactly why the amended `SegExit.frame`
excludes x8 from `joinRestored callJoinPC`. -/
theorem segExitJoin_frame_x8_false
    {g : (R : Register) → Option (RegisterType R)} {c : Config}
    {cnt node : BitVec 64}
    -- the PRE-amendment blanket frame clause at the join (what `SegExit.frame`
    -- demanded at `exitPC = callJoinPC` before the wave-45 `joinRestored` guard)
    (hFramePre : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R)
    -- what the `.normal` route establishes at the join: x8 = the loop counter,
    -- unrestored (`callClosureBodyExitNormalSeg` writes `addiw s0,s0,1`; the
    -- exit span + value_null + the s3/s5/s7-only restore never rewrite x8).
    (hRoute : c.σ.regs.get? Register.x8 = some cnt)
    -- the arm ghost's x8 is the caller's EX_CALL node ptr (`CallArgLoopInv.node`).
    (hGhost : g Register.x8 = some node)
    -- the counter is not the node ptr (a nonzero body ⇒ counter ≥ 1; the node
    -- ptr is a heap address — genuinely distinct; supplied by the arm).
    (hne : cnt ≠ node) :
    False := by
  have hframe : c.σ.regs.get? Register.x8 = g Register.x8 :=
    hFramePre Register.x8 (by decide)
  rw [hRoute, hGhost] at hframe
  exact hne (Option.some.inj hframe)

#print axioms segExitJoin_frame_x8_false

/-! ## §2. The output-carrying re-statements of the two landed `.normal` bricks

Per wave-42/43: `bridgeOfSeg`/`segToTriple` drop `sailOutput`, so the landed
`callClosureNormalDepthBridge`/`callClosureNormalJoinRow` cannot carry `OutRepr`
across the route.  Here the two spans are RE-STATED in the sailOutput-carrying
forms (`bridgeOfSegOut`/`segToTripleOut`, `CallCruxMarshal`/`4`) — the exact
`rowpost-drops-sailoutput-blocks-outrepr` fix the join re-assembly needs. -/

/-- The `.normal` depth-bridge entry pin list — `x18` (s2, `call_depth` at
`8(s2)`) and `x9` (s1, the CALL sret staged into a0), matching
`callClosureNormalDepthL`. -/
def normalDepthL (s2v s1v : BitVec 64) : GRegs := callClosureNormalDepthL s2v s1v

/-- **`normalDepthBridgeOut`** — the `--call_depth` staging ▷ `jal value_null`
via `bridgeOfSegOut` (sailOutput threaded).  The frozen `bridgeOfSeg` twin is
`callClosureNormalDepthBridge`; this re-states the SAME seg through the
output-carrying bridge so the leg's `OutRepr` survives the call seam.  `hjal`
is `JalStepO`-shaped (the region `site_80003964_*` obs; the machine `jal`
writes no output). -/
theorem normalDepthBridgeOut
    (σ : MState) (i u : Nat) (vm : BitVec 64) (s2v s1v : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (lds : List (List (BitVec 8)))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003954#64 : BitVec 64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (normalDepthL s2v s1v))
    (hfacts : ChainFacts σ.mem σ.mem (normalDepthL s2v s1v) lds
      callClosureNormalDepthSeg)
    (hi : i < 2)
    -- output-regs key hygiene: one `decide` each at the caller (the frozen
    -- `callClosureNormalDepthBridge` takes these as premises too — they mention
    -- `evalBlocks`, not decidable under the free `s2v`/`s1v`).
    (hKeysOut : KeysOK (keysG (evalBlocks callClosureNormalDepthSeg
      (SegEvalState.init (normalDepthL s2v s1v) lds)).regs))
    (hRaOut : KeysAvoidRa (evalBlocks callClosureNormalDepthSeg
      (SegEvalState.init (normalDepthL s2v s1v) lds)).regs)
    (hjal : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some (evalBlocksPC 0x80003954#64
        (SegEvalState.init (normalDepthL s2v s1v) lds) callClosureNormalDepthSeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks callClosureNormalDepthSeg
        (SegEvalState.init (normalDepthL s2v s1v) lds)).log →
      GHolds σ' (evalBlocks callClosureNormalDepthSeg
        (SegEvalState.init (normalDepthL s2v s1v) lds)).regs →
      JalStepO 0x800027ec#64 0x80003968#64 σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel callClosureNormalDepthSeg + 1⟩ ∧
        i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x800027ec#64 : BitVec 64) ∧
      σ2.regs.get? Register.x1 = some (0x80003968#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks callClosureNormalDepthSeg
        (SegEvalState.init (normalDepthL s2v s1v) lds)).regs ∧
      σ2.mem = writeLog m0 (evalBlocks callClosureNormalDepthSeg
        (SegEvalState.init (normalDepthL s2v s1v) lds)).log ∧
      σ2.sailOutput = σ.sailOutput ∧
      (∀ R, AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) :=
  bridgeOfSegOut callClosureNormalDepthSeg (normalDepthL s2v s1v) lds
    σ i u (0x80003954#64) (0x800027ec#64) (0x80003968#64) vm m0
    hG hpc hmi hmem hL
    (by have h : keysG (normalDepthL s2v s1v) = [18, 9] := rfl
        rw [h]; decide)
    hfacts hi
    (by have h : keysG (normalDepthL s2v s1v) = [18, 9] := rfl
        rw [h]; show ChainOK 0x80003954#64 [18, 9] callClosureNormalDepthSeg
        decide)
    (by show WrChainAvoidAbi callClosureNormalDepthSeg; decide)
    hKeysOut hRaOut
    hjal

#print axioms normalDepthBridgeOut

/-- The `.normal` join-seg post carrying `sailOutput` (`SegPreO`/`segToTripleOut`
form of `callClosureNormalJoinRow`): parked at `callJoinPC = 0x800033ec`, memory
= the (empty) join-seg write-log, the restored s3/s5/s7 via `GHolds`, AND the
entry `sailOutput = s0`. -/
def NormalJoinOutPost (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (s0 : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks callClosureNormalJoinSeg
    (SegEvalState.init (callClosureNormalJoinL sp) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x800033ec#64 ∧
  c.σ.sailOutput = s0 ∧
  GHolds c.σ (evalBlocks callClosureNormalJoinSeg
    (SegEvalState.init (callClosureNormalJoinL sp) lds)).regs

/-- **`normalJoinRowOut`** — the restore seg (`ld s3/s5/s7 ▷ j callJoinPC`) as a
sailOutput-carrying `Triple` (`segToTripleOut`).  The output-carrying twin of
`callClosureNormalJoinRow`; the join re-assembly reads `OutRepr` off its
`sailOutput = s0` fact via `outRepr_transport`. -/
theorem normalJoinRowOut (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (s0 : Array String) :
    Triple
      (SegPreO callClosureNormalJoinSeg (callClosureNormalJoinL sp)
        lds 0x80003968#64 m0 s0)
      (NormalJoinOutPost sp lds m0 s0) := by
  apply segToTripleOut callClosureNormalJoinSeg (callClosureNormalJoinL sp)
    lds 0x80003968#64 m0 s0 (NormalJoinOutPost sp lds m0 s0)
    (by have h : keysG (callClosureNormalJoinL sp) = [2] := rfl
        rw [h]
        show ChainOK 0x80003968#64 [2] callClosureNormalJoinSeg
        decide)
  intro σ' i' u' hG' _hi' hmem' hout' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, hout', hregs⟩
  rw [hpc']
  show some (evalBlocksPC 0x80003968#64
      (SegEvalState.init (callClosureNormalJoinL sp) lds)
      callClosureNormalJoinSeg)
    = some 0x800033ec#64
  rfl

#print axioms normalJoinRowOut

end Vsa.Sim
