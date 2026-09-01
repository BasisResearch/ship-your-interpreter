import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg
import Vsa.Sim.ArmSegSplitEval
import Vsa.Sim.rows.CallClosureSplice

/-!
# `ArgsHeadArmStagePre` — the `argsHead` eval-child staging field (Wave 41)

The LAST eval-child staging field of `EvalChildStages`
(`ArmSegSplitEval.lean`).  Unlike the 3-instruction arm heads
(unary/binary/assign/call), the `argsHead` arm is the EX_CALL **arg-loop body**:
from the arg-loop head `evalArgsLoopPC = 0x800031dc` (where `AEntryC (e :: es)`'s
`SegEntry` sits) the machine loads the head arg node from the args array, sets up
the recursive `eval_expr` ABI args, and reaches `jal eval_expr @0x80003220` — the
recursive call that evaluates the head argument `e`.  The field must land at
`JalPreBundle e` (the rich `jal`-landing repr).

## The honest split (mirrors wave-37 `callF` — dispatch residual + landed span)

`AEntryC (e :: es)` gives a bare `SegEntry` at `evalArgsLoopPC`; it carries NONE of
the arg-loop pins (a6=index, a5=argc, s0=call node, s2=interp, a3=env), nor the
head-arg node's `ExprRepr`.  Those live in `CallArgLoopInv` (the crux's loop
invariant at `evalArgsLoopPC`, `rows/CallClosureSplice.lean`) — which this file is
the FIRST consumer of, plus the head-arg-node `ExprRepr` correspondence (an
arg-NODE-vector fact, genuinely upstream; see observation
`argshead-exprrepr-of-head-arg-node-not-in-loopinv`).  So:

* **`ArgsHeadDispatch`** — the named dispatch residual: `AEntryC (e :: es) →`
  the machine at `CallArgLoopInv` (fresh loop, `vsPre = []`, `n ≥ 1`) with the
  head-arg node staged.  The analog of `CallArmDispatch`.

* **`argsHeadBodySeg`** (`#derive_case`) + **`bridgeOfSeg`** — the straight-line
  arg-loop body `0x800031dc → 0x8000321c` run + the `jal eval_expr @0x80003220`
  seam, FREE modulo the one `ChainOK` decide + the region's `JalStep`.  The
  MANDATORY abstraction for this span (its literal purpose; a 16-site hand battery
  would trip the discipline gate) — modelled exactly on `LoopHeadArgSetupSeg`.

* **`ArgsHeadStagePre`** — the staging residual (consuming `CallArgLoopInv`):
  reaches `JalPreBundle e` from the loop head.  The `JalPreBundle`-marshalling
  half — the genuinely per-arm work — named as a typed premise (the body run +
  jal are proved; the marshalling of `GHolds`/`writeLog` into the `JalPreBundle`
  conjuncts is the residual, dischargeable from `CallArgLoopInv`'s `StoreRepr`/
  `memFrame`/`slots` + the head-node `ExprRepr`).

* **`argsHead_field_of_dispatch`** — composes them into the `EvalChildStages.argsHead`
  field shape (`AEntryC → LandedN 1 (JalPreBundle e)`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump beyond the seg-derivation budget the GEN idiom uses.  Axioms of every theorem
⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.ApproxArmReseat

namespace Vsa.Sim

set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

/-! ## §1. The arg-loop body seg `0x800031dc → 0x8000321c` (straight-line, jal-terminated at 0x80003220)

The 16-instruction body between the loop head and the recursive `jal eval_expr`,
decoded from `experiments/disasm.txt:3301-3317`.  A `#derive_case` seg exactly as
the GEN `loopHeadArgSetupSeg`; `bridgeOfSeg` runs it and takes the `jal` seam. -/
#derive_case argsHeadBodySeg chain
  [(0x800031dc#64, 0x01043603#32),  -- ld a2,16(s0)      (args array base)
   (0x800031e0#64, 0x0008059b#32),  -- sext.w a1,a6      (index, sign-extended)
   (0x800031e4#64, 0x00381713#32),  -- slli a4,a6,0x3    (8*i)
   (0x800031e8#64, 0x00e60633#32),  -- add a2,a2,a4      (&args[i] node ptr)
   (0x800031ec#64, 0x00159713#32),  -- slli a4,a1,0x1    (2*i)
   (0x800031f0#64, 0x00b70733#32),  -- add a4,a4,a1      (3*i)
   (0x800031f4#64, 0x00063603#32),  -- ld a2,0(a2)       (head arg NODE)
   (0x800031f8#64, 0x00371713#32),  -- slli a4,a4,0x3    (24*i)
   (0x800031fc#64, 0x00f13c23#32),  -- sd a5,24(sp)      (spill argc)
   (0x80003200#64, 0x3d070793#32),  -- addi a5,a4,976    (24*i + 976 slot off)
   (0x80003204#64, 0x02010713#32),  -- addi a4,sp,32     (stack value-array base)
   (0x80003208#64, 0x00e78733#32),  -- add a4,a5,a4      (&slot @sp+32+24*i+976)
   (0x8000320c#64, 0x00090593#32),  -- mv a1,s2          (a1 := interp*)
   (0x80003210#64, 0x04010513#32),  -- addi a0,sp,64     (a0 := sret @sp+64)
   (0x80003214#64, 0x01013823#32),  -- sd a6,16(sp)      (spill index)
   (0x80003218#64, 0x00d13423#32),  -- sd a3,8(sp)       (spill env)
   (0x8000321c#64, 0x00e13023#32)]  -- sd a4,0(sp)       (spill slot ptr)

/-- The `argsHeadBody` entry pin list — the registers the body READS before writing:
`x2` (sp), `x8` (s0, call node), `x16` (a6, index), `x15` (a5, argc), `x18` (s2,
interp), `x13` (a3, env). -/
def argsHeadBodyL (sp s0 a6 a5 s2 a3 : BitVec 64) : GRegs :=
  [(2, sp), (8, s0), (16, a6), (15, a5), (18, s2), (13, a3)]

/-! ## §2. The body ≫ jal bridge (`bridgeOfSeg`)

`argsHeadBodyBridge` — the arg-loop body run ≫ `jal eval_expr @0x80003220`
(link `0x80003224`, target `eval_expr` entry `0x80003164` via imm `0x1f45`), via
`bridgeOfSeg`.  The seg run + ABI frame are FREE; `hfacts` (one `chain_facts` at
the caller) and `hjalSeam` (the call-seam `JalStep` off the `eval_expr` jal-site
obs) are the only region-specific residuals.  Modelled on `loopHeadArgSetupBridge`. -/
theorem argsHeadBodyBridge
    (σ : MState) (i u : Nat) (vminstret : BitVec 64)
    (sp s0 a6 a5 s2 a3 : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x800031dc#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (argsHeadBodyL sp s0 a6 a5 s2 a3))
    (hfacts : ChainFacts σ.mem σ.mem (argsHeadBodyL sp s0 a6 a5 s2 a3) [] argsHeadBodySeg)
    (hi : i < 2)
    (hKeysOut : KeysOK (keysG (evalBlocks argsHeadBodySeg
      (SegEvalState.init (argsHeadBodyL sp s0 a6 a5 s2 a3) [])).regs))
    (hRaOut : KeysAvoidRa (evalBlocks argsHeadBodySeg
      (SegEvalState.init (argsHeadBodyL sp s0 a6 a5 s2 a3) [])).regs)
    (hjalSeam : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some
        (evalBlocksPC 0x800031dc#64 (SegEvalState.init (argsHeadBodyL sp s0 a6 a5 s2 a3) [])
          argsHeadBodySeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks argsHeadBodySeg
        (SegEvalState.init (argsHeadBodyL sp s0 a6 a5 s2 a3) [])).log →
      GHolds σ' (evalBlocks argsHeadBodySeg
        (SegEvalState.init (argsHeadBodyL sp s0 a6 a5 s2 a3) [])).regs →
      JalStep 0x80003164#64 0x80003224#64 σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel argsHeadBodySeg + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x80003164#64 : BitVec 64) ∧
      σ2.regs.get? Register.x1 = some (0x80003224#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks argsHeadBodySeg
        (SegEvalState.init (argsHeadBodyL sp s0 a6 a5 s2 a3) [])).regs ∧
      σ2.mem = writeLog m0 (evalBlocks argsHeadBodySeg
        (SegEvalState.init (argsHeadBodyL sp s0 a6 a5 s2 a3) [])).log ∧
      (∀ R, Vsa.Alloc.AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSeg argsHeadBodySeg (argsHeadBodyL sp s0 a6 a5 s2 a3) []
    σ i u (0x800031dc#64) (0x80003164#64) (0x80003224#64) vminstret m0
    hG hpc hminstret hmem hL
    (by have h : keysG (argsHeadBodyL sp s0 a6 a5 s2 a3) = [2, 8, 16, 15, 18, 13] := rfl
        rw [h]; decide)
    hfacts hi
    (by have h : keysG (argsHeadBodyL sp s0 a6 a5 s2 a3) = [2, 8, 16, 15, 18, 13] := rfl
        rw [h]; show ChainOK 0x800031dc#64 [2, 8, 16, 15, 18, 13] argsHeadBodySeg; decide)
    (by show WrChainAvoidAbi argsHeadBodySeg; decide)
    hKeysOut hRaOut
  exact hjalSeam

#print axioms argsHeadBodyBridge

/-! ## §3. The loop-head bundle + the two named residuals + the field composer

The `argsHead` field of `EvalChildStages` is `AEntryC (e :: es) → LandedN 1
(JalPreBundle e)`.  We split it (mirroring wave-37 `callF_field_of_dispatch`) into:

* `ArgsLoopHeadInv` — the config predicate at the loop head bundling the crux's
  `CallArgLoopInv` (fresh loop, `vsPre = []`, `n ≥ 1`) with the head-arg node's
  `ExprRepr` (the arg-NODE-vector fact `CallArgLoopInv` does not carry; observation
  `argshead-exprrepr-of-head-arg-node-not-in-loopinv`).

* `ArgsHeadDispatch` — the dispatch residual: `AEntryC (e :: es) → LandedN 0 c
  (ArgsLoopHeadInv …)`.  `AEntryC`'s `SegEntry` already sits AT `evalArgsLoopPC`
  (`0x800031dc`), so this is the zero-step re-packaging that establishes the
  arg-loop pins (a6=0, a5=argc, s0=node, s2=interp, a3=env) and the head-node
  `ExprRepr`.  The analog of `CallArmDispatch`; genuinely upstream (SegEntry is
  pin-agnostic).

* `ArgsHeadStagePre` — the staging residual consuming `ArgsLoopHeadInv`: run the
  body (`argsHeadBodyBridge`) and marshal into `JalPreBundle e`.  The
  `JalPreBundle`-marshalling half (`GHolds out.regs`/`writeLog out.log` → the
  `JalPreBundle` conjuncts, off `CallArgLoopInv`'s `StoreRepr`/`memFrame`/`slots` +
  the head-node `ExprRepr`) is the genuinely per-arm residual, named per Law 2. -/

/-- **The arg-loop-head bundle** — `CallArgLoopInv` at the FRESH loop (`vsPre = []`)
plus the head-arg node's `ExprRepr`.  The state `argsHead` stages from: at
`evalArgsLoopPC = 0x800031dc`, no args evaluated yet (`vsPre = []`), argc `n ≥ 1`
(so the head arg `e` exists), all the loop pins live, and the head-arg node's
address `aHead` (read out of the args array at `16(s0)`) represents `e`. -/
def ArgsLoopHeadInv
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (e : Expr) (es : List Expr)
    (sp cnode ip envp aHead : BitVec 64) (m0 : Mem) (c : Config) : Prop :=
  CallArgLoopInv N A SL φf φc st [] (e :: es).length sp cnode ip envp m0 c ∧
  ExprRepr c.σ.mem aHead.toNat e

/-- **The `argsHead` staging residual** — from the loop-head bundle at ANY config
`c'`, run the body (`argsHeadBodyBridge`) and marshal into `JalPreBundle e`.  Named
as a typed premise (Law 2): the body run + jal are PROVED (`argsHeadBodyBridge`,
§2); the residual is the marshalling of the computed `GHolds`/`writeLog` into the
`JalPreBundle` conjuncts.  What it consumes from the loop-head bundle:
* `CallArgLoopInv.node`/`.slots`/`.memFrame` — the args-array base (`16(s0)`) and
  the head-arg node read (`ld a2,0(a2)`), supplied as the `lds` load-list to
  `argsHeadBodyBridge` (whose seg abstracts `ld` reads via `lds`); tied to
  `ExprRepr … e` (the bundle's second conjunct);
* `CallArgLoopInv.store`/`.out` — `StoreRepr`/`OutRepr` for `JalPreBundle`;
* the lowered-frame geometry (`sp`/`SL`/`A` bounds, `subsret = sp+64` alignment,
  the sret/arena/table disjointness) — the SAME ~25 side conditions
  `blockB_call_stagePre` takes; these are NOT all in `CallArgLoopInv`, so the
  bundle/dispatch-residual must carry them (see the report's residual note).
Strictly smaller than the field: it starts AT the loop head with all pins live,
not at the abstract `AEntryC`.  Universally quantified over the config so it
composes after a `LandedN` prefix. -/
def ArgsHeadStagePre
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
    (sp cnode ip envp aHead : BitVec 64) (m0 : Mem) : Prop :=
  ∀ c' : Config,
    ArgsLoopHeadInv N A SL φf φc st e es sp cnode ip envp aHead m0 c' →
    LandedN 1 c' (fun c'' => JalPreBundle e c'' st d env)

/-- **The `argsHead` dispatch residual** — `AEntryC (e :: es) → LandedN 0` to the
loop-head bundle.  `AEntryC`'s `SegEntry` sits at `evalArgsLoopPC`; this residual
establishes the arg-loop pins + the head-arg node's `ExprRepr` (the arg-NODE-vector
fact, genuinely upstream — supplied where the EX_CALL arm materialises the args
array).  The analog of `CallArmDispatch`. -/
def ArgsHeadDispatch (e : Expr) (es : List Expr) (st : Vsa.While.St)
    (d : Nat) (env : Addr) (c : Config) : Prop :=
  AEntryC c st d env (e :: es) →
  ∃ (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp cnode ip envp aHead : BitVec 64) (m0 : Mem),
    LandedN 0 c (ArgsLoopHeadInv N A SL φf φc st e es sp cnode ip envp aHead m0) ∧
    ArgsHeadStagePre N A SL φf φc st d env e es sp cnode ip envp aHead m0

/-- **The `EvalChildStages.argsHead` field, machine-composed.**  From
`AEntryC (e :: es)` plus the dispatch residual `ArgsHeadDispatch`, the composer
lands (zero-step) at the loop-head bundle, then the staging residual runs the body
and marshals into `JalPreBundle e`.  Exactly the field type
`argsHead : AEntryC (e :: es) → LandedN 1 (JalPreBundle e)`. -/
theorem argsHead_field_of_dispatch
    (e : Expr) (es : List Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hDisp : ArgsHeadDispatch e es st d env c)
    (hAE : AEntryC c st d env (e :: es)) :
    LandedN 1 c (fun c' => JalPreBundle e c' st d env) := by
  obtain ⟨N, A, SL, φf, φc, sp, cnode, ip, envp, aHead, m0, hLanded0, hStage⟩ := hDisp hAE
  -- zero-step landing at the loop-head bundle, then the staging residual (∀ config).
  have hcomp : LandedN (0 + 1) c (fun c' => JalPreBundle e c' st d env) :=
    LandedN.bind hLanded0 (fun c' hInv => hStage c' hInv)
  exact LandedN.weakenCount (by omega) hcomp

#print axioms argsHead_field_of_dispatch

end Vsa.Sim
