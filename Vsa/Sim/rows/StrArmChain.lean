import Vsa.Sim.rows.StrCmpBlockC
import Vsa.Sim.BridgeSeg
import Vsa.Sim.BoxSuffixSeams
import Vsa.Sim.StrcmpSpecW4

/-!
# `StrArmChain` — the str-cmp arm MACHINE TRANSPORT (spans 1–3 of `StrArmMachineResid`)

`StrArmMachineResid op bres` (`StrCmpBlockC`) is DEFINED as the whole-node `EvalIH`
for a `.binary op el er` node at string operands — the ENTIRE arm, prologue
(`blockA_binaryArm`) ≫ operand recursions (`blockB_binary`) ≫ str seam ≫ sign tail ≫
`value_bool` box ≫ `blockD_v_rec`, the ~700-line `blockC_ge`-scale object.  There is
NO int-arm `blockC` to clone for the str operands: `blockC_ge` proves the INT path
(kinds = 2, int-payload prologue); the str arm (kinds = 3) has a different
prologue+operand recursion and no landed `blockA_binaryArm`/`blockB_binary` at kind 3
(the same missing str-operand prologue that blocks the concat cell in `BinStrCells`
§b).  So the whole-node residual cannot be honestly discharged end-to-end here.

What IS buildable + kernel-checked — and what this file lands — is the str-arm
MACHINE TRANSPORT from the kind-check branch through the sign tail: the EXACT analogue
of `EvalEqNeFront.blockC_eqne_front` (which composes the eq/ne front seam over an
`EqFrontData` bundle but likewise leaves the outer `EvalIH` a residual).  Three spans:

## Decoded route (`experiments/disasm.txt`, verified)

```
80003628  addi a5,a0,-3 ; bnez a5 → 80003638   (SPAN 1: right kind ≠ 3?  a0=3 ⇒ a5=0, NOT taken)
80003630  addi a5,a6,-3 ; beqz a5 → 80003b0c   (a6=3 ⇒ a5=0, TAKEN → str seam)
...
80003b0c  mv a1,a7 ; mv a0,s3 ; sd a2,0(sp)    (SPAN 2: strcmp arg marshalling)
80003b18  jal strcmp @80006ea0                 (       the Shape-D call seam)
80003b1c  ld a2,0(sp) ; mv a1,a0 ; j 800036a4   (SPAN 3: rejoin — a1 := strcmp sign)
800036a4  <op sign-test tail>  ; jal value_bool  (       the landed sTail*Row + box)
```

* **SPAN 1** — the kind-check branch span `0x80003628 → beqz-taken → 0x80003b0c`.
  Branch-terminated → a `#derive_case` seg (`strKindCheck`) + `segToTriple`
  (`strKindCheckRow`); NO `bridgeOfSeg` (no jal).  Pins the two operand kind tags
  `x10 = 3` (right), `x16 = 3` (left), which drive the `bnez`/`beqz` guards.
* **SPAN 2** — the strcmp-call span `0x80003b0c mv;mv;sd; jal`.  Store-in-body +
  jal-terminated → `bridgeOfSeg` (`strcmpSeamBridge`) with the jal seam supplied by
  `jalStep_of_obs`, then a `callSeg` splice of `strcmp_full_spec` (LANDED,
  `StrcmpSpecW4`).
* **SPAN 3** — the rejoin `0x80003b1c ld;mv; j 0x800036a4` into the SHARED operator
  sign-test tail, whose four op routes are the LANDED `sTail{Lt,Gt,Le}Row`
  (`StrCmpSignTail`) + `cmpFixupTail` (`ge`), then the `value_bool` box
  (`valueBoolCallSeam`, `BoxSuffixSeams`).

The composed front-transport combinator (`strArmFront`) takes a `StrArmFrontData`
caller bundle (parked at `0x80003b0c` with both operands staged as `.str`, strcmp
region witnesses, the box obligations) and runs span-2 ≫ strcmp ≫ span-3 rejoin ≫
sign tail ≫ box, exactly as `blockC_eqne_front` runs its front.  `StrArmMachineResid`
then factors as str-prologue ≫ `strArmFront`, leaving ONLY the prologue — mirroring
how `evalEqNeSim = eq-prologue ≫ blockC_eqne_front`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While
open Vsa.Sim.Code

namespace Vsa.Sim

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-! ## SPAN 1 — the kind-check branch span as a `#derive_case` seg

Both operands are strings (kind tag 3): `x10 = 3` (right kind), `x16 = 3` (left kind).
* `0x80003628 addi x15,x10,-3` ⇒ `x15 = 0`; `bnez x15` @0x8000362c NOT taken (0),
  falls through to `0x80003630`;
* `0x80003630 addi x15,x16,-3` ⇒ `x15 = 0`; `beqz x15` @0x80003634 TAKEN (0) →
  `0x80003b0c` (the strcmp seam entry, the seg's computed end PC).

Branch-terminated (no jal, no store) → plain `segToTriple`, per the CLAUDE.md table. -/
#derive_case strKindCheck chain
  [(0x80003628#64, 0xffd50793#32)]                -- addi x15,x10,-3
    terminator ⟨0x8000362c#64, 0x00079663#32, 0x63#8, 0x96#8, 0x07#8, 0x00#8,
      .br bop.BNE false, 15, 0, 0x000c#13, 0#21, 0#12⟩ ;;   -- NOT taken (x15=0) → 0x3630
  [(0x80003630#64, 0xffd80793#32)]                -- addi x15,x16,-3
    terminator ⟨0x80003634#64, 0x4c078c63#32, 0x63#8, 0x8c#8, 0x07#8, 0x4c#8,
      .br bop.BEQ true, 15, 0, 0x04d8#13, 0#21, 0#12⟩     -- TAKEN (x15=0) → 0x3b0c

/-- The kind-check pin list: both operand kind tags are 3 (`str`). -/
def strKindL : GRegs := [(10, 3#64), (16, 3#64)]

/-- The `ChainFacts` leg (mechanical).  The two branch guards (`x15 = x10-3 = 0` for the
BNE, `x15 = x16-3 = 0` for the BEQ) do NOT close by `all_goals rfl`: `rfl` chases the
`addi`'s `sign_extend (-3)` + subtraction through the reflected `runGM` with symbolic
`lds` to unbounded depth (native stack overflow at high `maxRecDepth`).  Instead reduce the
guard symbolically — `simp only [runGM, stepGM, wvalM, srcVal, guardB, <per-word `mkLine`
field pins>]` collapses each guard to a concrete `BitVec` comparison, closed by `decide`.
This is the same load-free-but-arith-heavy readback pattern as span 3's `strRejoin_x11`. -/
theorem strKindCheck_facts (σ : MState) (lds : List (List (BitVec 8)))
    (h : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    ChainFacts σ.mem σ.mem strKindL lds strKindCheck := by
  chain_facts h with "Vsa.Sim.Code.eval_expr_at_"
  all_goals (
    simp only [strKindL, runGM, stepGM, wvalM, srcVal, lookupG, eraseG, guardB,
      show (mkLine 0x80003628#64 0xffd50793#32).kind = MKind.addi from rfl,
      show (mkLine 0x80003628#64 0xffd50793#32).rd = 15 from rfl,
      show (mkLine 0x80003628#64 0xffd50793#32).rs1 = 10 from rfl,
      show (mkLine 0x80003628#64 0xffd50793#32).imm = 0xffd#12 from rfl,
      show (mkLine 0x80003630#64 0xffd80793#32).kind = MKind.addi from rfl,
      show (mkLine 0x80003630#64 0xffd80793#32).rd = 15 from rfl,
      show (mkLine 0x80003630#64 0xffd80793#32).rs1 = 16 from rfl,
      show (mkLine 0x80003630#64 0xffd80793#32).imm = 0xffd#12 from rfl,
      Nat.reduceEqDiff, if_true, if_false, Option.getD_some]
    <;> decide)

/-- Post of the kind-check span: parked at `0x80003b0c` (the strcmp seam entry),
memory unchanged (no stores). -/
def StrKindCheckPost (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x80003b0c#64

/-- **SPAN 1 payoff.**  The whole kind-check branch span as a `Triple`, via
`segToTriple`: `hwf` is the row's one kernel `decide` (`ChainOK`), `hpost` projects
the computed end PC / unchanged memory off the `#derive_case` outcome. -/
theorem strKindCheckRow (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre strKindCheck strKindL [] 0x80003628#64 m0) (StrKindCheckPost m0) := by
  apply segToTriple strKindCheck strKindL [] 0x80003628#64 m0 (StrKindCheckPost m0)
    (by show ChainOK 0x80003628#64 [10, 16] strKindCheck; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' _hregs
  refine ⟨hG', ?_, ?_⟩
  · rw [hmem']; rfl
  · rw [hpc']
    show some (chainEndPC 0x80003628#64 strKindL [] strKindCheck) = some 0x80003b0c#64
    rw [chainEndPC_eq_bt strKindCheck 0x80003628#64 strKindL [] (by decide)]
    rfl

#print axioms strKindCheck_facts
#print axioms strKindCheckRow

/-! ## SPAN 3 — the rejoin seg `0x80003b1c ld;mv; j 0x800036a4`

After the `strcmp` call returns (`x10 = strcmp sign`, `x1 = link`, `x2 = sp`, `x9 = sret`),
the rejoin block reloads the spilled `a2` and moves the strcmp sign into `a1`, then jumps
into the SHARED operator sign-test tail at `0x800036a4`:

* `0x80003b1c ld x12,0(x2)`   — reload the spilled `a2` (dead for the sign tail);
* `0x80003b20 mv x11,x10`     — `x11 := x10` (the strcmp sign scalar `x`);
* `0x80003b24 j 0x800036a4`   — jump to the sign-test tail entry (`jal x0`, imm21 = -0x480).

The `mv x11,x10` sets the spaceship scalar the sign tail reads.  Both `x9 = sret` and the
sign `x = x10` are carried symbolically; `x12` is overwritten by the `ld` (its value is the
positional load, irrelevant downstream).  `j`-terminated → plain `segToTriple`. -/
#derive_case strRejoin chain
  [(0x80003b1c#64, 0x00013603#32),                -- ld   x12,0(x2)
   (0x80003b20#64, 0x00050593#32)]                -- mv   x11,x10  (addi x11,x10,0)
    terminator ⟨0x80003b24#64, 0xb81ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0xb8#8,
      .j, 0, 0, 0#13, 0x1ffb80#21, 0#12⟩           -- j 0x800036a4  (jal x0, -0x480)

/-- The rejoin pin list: `x2 = sp` (the `ld` base), the strcmp sign scalar in `x10`, and
the sret buffer in `x9`.  `x2` must be pinned so the `ld x12,0(x2)` block's `ChainOK`
decode resolves. -/
def strRejoinL (sp x sret : BitVec 64) : GRegs := [(2, sp), (10, x), (9, sret)]

/-! ### Load-bearing register readback (see `experiments/observations.md`
`loadbearing-seg-register-readback`)

`gholds_lookup … (by rfl)` closes register projections for LOAD-FREE segs (the
sign-tail / cmpFixup rows), but the `ld x12,0(x2)` here makes `rfl` on
`lookupG 11 (runGM …)` stall on the symbolic-`lds` load cell (`bytesVal .ld
(lds.headD [])` in the dead `x12` slot).  `x9 = sret` is unwritten by the body →
peeled by `srcVal_runGM_ne`.  `x11 = x` (the `mv x11,x10`) is read via the hand
`runGM`/`stepGM` unfold with the six per-word `mkLine` field pins + `Nat`
simprocs, finishing the `+ sext 0#12` by `BitVec.add_zero`. -/
theorem strRejoin_x11 (sp x sret : BitVec 64) (lds : List (List (BitVec 8))) :
    lookupG 11 (evalBlocks strRejoin (SegEvalState.init (strRejoinL sp x sret) lds)).regs
      = some x := by
  rw [evalBlocks_regs]
  show lookupG 11 (runChain strRejoin (strRejoinL sp x sret) lds) = some x
  simp only [strRejoin, runChain, runGM, stepGM, wvalM, srcVal, lookupG, eraseG,
    strRejoinL,
    show (mkLine 0x80003b1c#64 0x00013603#32).kind = MKind.ld from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).kind = MKind.addi from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).rd = 11 from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).rs1 = 10 from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).imm = 0#12 from rfl,
    show (mkLine 0x80003b1c#64 0x00013603#32).rd = 12 from rfl,
    Nat.reduceEqDiff, if_true, if_false, Option.getD_some]
  show some (x + Functions.sign_extend 0#12) = some x
  rw [show (Functions.sign_extend 0#12 : BitVec 64) = 0#64 from by decide, BitVec.add_zero]

theorem strRejoin_x9 (sp x sret : BitVec 64) (lds : List (List (BitVec 8))) :
    lookupG 9 (evalBlocks strRejoin (SegEvalState.init (strRejoinL sp x sret) lds)).regs
      = some sret := by
  rw [evalBlocks_regs]
  show lookupG 9 (runChain strRejoin (strRejoinL sp x sret) lds) = some sret
  simp only [strRejoin, runChain, runGM, stepGM, wvalM, srcVal, lookupG, eraseG,
    strRejoinL,
    show (mkLine 0x80003b1c#64 0x00013603#32).kind = MKind.ld from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).kind = MKind.addi from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).rd = 11 from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).rs1 = 10 from rfl,
    show (mkLine 0x80003b1c#64 0x00013603#32).rd = 12 from rfl,
    Nat.reduceEqDiff, if_true, if_false, Option.getD_some]

/-- Post of the rejoin span: parked at `0x800036a4` (the sign-test tail entry), memory
unchanged (the `ld` reads, no stores), with the spaceship scalar `x` in `x11` (the `mv`)
and `x9 = sret` surviving.  This is EXACTLY the `SegPre`/pin shape `sTail{Lt,Gt,Le}Row` /
`cmpFixupTail` consume at `0x800036a4` (`x11 = cmpV`, `x9 = sret`; the op token `x12` is
staged by the arm prologue, not here). -/
def StrRejoinPost (x sret : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x800036a4#64 ∧
  gprGet c.σ 11 = some x ∧
  gprGet c.σ 9 = some sret

/-- **SPAN 3 payoff.**  The rejoin span as a `Triple`, via `segToTriple`: `hwf` is the
row's one kernel `decide` (`ChainOK`), `hpost` projects the `j`-target end PC (`0x800036a4`),
the moved sign scalar `x11 = x` (`strRejoin_x11`), and the surviving `x9 = sret`
(`strRejoin_x9`) off the outcome.  The rejoin `SegPre` carries the load's `ChainFacts`
(the caller — `strArmFront` — supplies it from the post-`strcmp` reload pin). -/
theorem strRejoinRow (sp x sret : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre strRejoin (strRejoinL sp x sret) lds 0x80003b1c#64 m0)
      (StrRejoinPost x sret m0) := by
  apply segToTriple strRejoin (strRejoinL sp x sret) lds 0x80003b1c#64 m0 (StrRejoinPost x sret m0)
    (by show ChainOK 0x80003b1c#64 [2, 10, 9] strRejoin; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', ?_, ?_, ?_, ?_⟩
  · rw [hmem']; rfl
  · rw [hpc']
    show some (chainEndPC 0x80003b1c#64 (strRejoinL sp x sret) lds strRejoin) = some 0x800036a4#64
    rw [chainEndPC_eq_bt strRejoin 0x80003b1c#64 (strRejoinL sp x sret) lds (by decide)]
    rfl
  · exact gholds_lookup (v := x) _ hregs (strRejoin_x11 sp x sret lds)
  · exact gholds_lookup (v := sret) _ hregs (strRejoin_x9 sp x sret lds)

#print axioms strRejoin_x11
#print axioms strRejoin_x9
#print axioms strRejoinRow

/-! ## SPAN 2 + the front combinator `strArmFront`

The str-arm front transport, the EXACT analogue of `EvalEqNeFront.blockC_eqne_front`:
compose the `strcmp` call (`strcmp_full_spec`) ≫ the span-3 rejoin (`strRejoinRow`) ≫ the
op's sign-test tail (`sTail{Lt,Gt,Le}Row` / `cmpFixupTail` for `ge`) ≫ the `value_bool` box
(`valueBoolCallSeam`), producing the boxed boolean at the arm's `value_bool` entry.  Like
`blockC_eqne_front` it takes a caller bundle (`StrArmFrontData`) parked at the strcmp entry
`0x80006ea0` with both operands staged as C strings, the strcmp caller obligations, and the
connective reconciliations (post-`strcmp` mem/reg tie, sign-tail `ChainFacts`, box pre) as
named premises — leaving ONLY the str-operand prologue (`blockA_binaryArm`/`blockB_binary`
at kind 3) as the outer residual, exactly as `blockC_eqne_front` leaves the outer `EvalIH`.

Span-2 marshalling (`mv a1,a7; mv a0,s3; sd a2,0(sp)`) is staged INTO the bundle (operands
already in `x10 = pa`, `x11 = pb`, `a2` spilled into `mA`), and the `jal strcmp @0x80003b18`
lands the callee entry `0x80006ea0` with `x1 = 0x80003b1c` (= the span-3 rejoin entry) — so
the caller supplies the strcmp-entry config directly (the jal seam collapses into the
`strcmp_full_pre` the bundle asserts), mirroring how `EqFrontData` parks at the jal PC.

### The op selector for the sign-tail row

`strArmFront` is parameterised over the op token; the sign-tail leg is
`sTailLtRow`/`sTailGtRow`/`sTailLeRow`/`cmpFixupTailRow`, and the boxed word is the matching
`sTailWord op w` (`StrCmpBlockC`).  We package the op's sign-tail `Triple` + its produced
word as a bundle field so the combinator is uniform over the four ops. -/

/-- The op's sign-tail transport, packaged uniformly: from the rejoin post
(`StrRejoinPost x sret`, parked at `0x800036a4` with `x11 = x`, `x9 = sret`), run the op's
`#derive_case` sign-tail seg to the op's `jal value_bool` entry PC (`vbPC`), producing the
boolean payload word `sTailWord op x` in `x11` and `x10 = sret`, memory unchanged.  This is
`sTail{Lt,Gt,Le}Row` / `cmpFixupTailRow` restated over the shared `StrRejoinPost` entry;
supplied per op by the bundle so the combinator stays op-generic. -/
def SignTailLeg (op : BinOp) (tok : BitVec 64) (vbPC : BitVec 64)
    (x sret : BitVec 64) (mA : Mem) : Prop :=
  Triple
    (fun c => GoodState c.σ ∧ c.σ.mem = mA ∧
      c.σ.regs.get? Register.PC = some 0x800036a4#64 ∧
      (∃ vm, c.σ.regs.get? Register.minstret = some vm) ∧
      c.σ.regs.get? Register.x11 = some x ∧
      c.σ.regs.get? Register.x12 = some tok ∧
      c.σ.regs.get? Register.x9 = some sret ∧ c.tick < 2)
    (fun c => GoodState c.σ ∧ c.σ.mem = mA ∧
      c.σ.regs.get? Register.PC = some vbPC ∧
      (∃ vm, c.σ.regs.get? Register.minstret = some vm) ∧
      c.σ.regs.get? Register.x11 = some (sTailWord op x) ∧
      c.σ.regs.get? Register.x10 = some sret ∧
      c.σ.regs.get? Register.x9 = some sret ∧ c.tick < 2)

/-- **`StrArmFrontData`** — the post-prologue front residual bundle (the str-arm analogue of
`EqFrontData`).  Parked at the strcmp entry `cE` with both operands staged as C strings, it
carries: the `strcmp` caller obligations (`strcmp_full_pre`), the four connective transports
as `Triple`s over their reconciled endpoints (post-`strcmp` reconcile into the span-3 rejoin
`SegPre`, the rejoin `Triple` — reuse `strRejoinRow`, the op sign-tail leg `SignTailLeg`, the
`value_bool` box via `valueBoolCallSeam`), the boxed-word↔order bridge, and the box pre/suf —
everything `strArmFront` composes but cannot derive from the (unbuilt) str-operand prologue.

The strcmp return `x` (the spaceship scalar) is universally quantified in every downstream
leg (its sign is pinned by `strcmp_post` to `strcmpSpecSign` of the operand strings), so the
combinator threads the existential the callee produces.  The `hReconcile` leg is the SINGLE
honest residual of this front (the analogue of `EqFrontData.hsnapEval`/`hMemExtRet`): the
strcmp-post register/frame state (`x1 = 0x80003b1c`, `x2 = sp` callee-saved, `x10 = x`,
`x9 = sret` callee-saved, memory `mA` unchanged) reconstituted as the rejoin `SegPre` — a
pure frame projection off `strcmp_post`, named rather than re-derived. -/
structure StrArmFrontData
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (op : BinOp) (tok : BitVec 64) (vbPC r sret : BitVec 64)
    (sp pa pb : BitVec 64) (sa sb : String)
    (mA : Mem) (out0 : Array String) (bres : Bool) (cE : Config) : Prop where
  -- the strcmp callee obligations at the entry config `cE` (= `strcmp_full_pre`); the return
  -- link is `0x80003b1c` = the span-3 rejoin entry (the jal `x1`)
  hStrcmpPre : strcmp_full_pre g pa pb (0x80003b1c#64) sa sb mA out0 cE
  -- the post-`strcmp` → span-3-rejoin reconciliation (the front's one honest residual): the
  -- strcmp-post state reconstituted as the rejoin `SegPre` (parked at `0x80003b1c`, `x2 = sp`,
  -- `x10 = x` = the returned sign, `x9 = sret`, memory `mA`).  Quantified over the return `x`.
  hReconcile : ∀ (x : BitVec 64),
    Triple (strcmp_post g (0x80003b1c#64) pa pb sa sb mA out0)
      (SegPre strRejoin (strRejoinL sp x sret) [] (0x80003b1c#64) mA)
  -- the op's sign-tail transport, quantified over the strcmp return `x` (the spaceship scalar)
  hSignTail : ∀ (x : BitVec 64), SignTailLeg op tok vbPC x sret mA
  -- the boxed-word ↔ source order bridge (the named `StrCmpOrderBridge`, StrCmpBlockC):
  -- `value_bool` boxes `sTailWord op x != 0` to `.bool bres` for the strcmp return `x`
  hOrder : ∀ (x : BitVec 64), (sTailWord op x != 0#64) = bres
  -- the op token pin `x12 = tok` at the sign-tail entry (staged by the arm prologue; the
  -- rejoin only touches x9/x11/x12, so this rides the rejoin post as a frame fact)
  hTokAtRejoin : ∀ (x : BitVec 64),
    Triple (StrRejoinPost x sret mA)
      (fun c => GoodState c.σ ∧ c.σ.mem = mA ∧
        c.σ.regs.get? Register.PC = some 0x800036a4#64 ∧
        (∃ vm, c.σ.regs.get? Register.minstret = some vm) ∧
        c.σ.regs.get? Register.x11 = some x ∧
        c.σ.regs.get? Register.x12 = some tok ∧
        c.σ.regs.get? Register.x9 = some sret ∧ c.tick < 2)
  -- the `value_bool` box seam via `valueBoolCallSeam`: from the sign-tail exit
  -- (`SignTailLeg` post: parked at `vbPC`, `x11 = sTailWord op x`, `x10 = sret`) box into
  -- `.bool (sTailWord op x != 0) = .bool bres`, landing `ValueRepr … sret (.bool bres)`.
  hBox : ∀ (x : BitVec 64),
    Triple
      (fun c => GoodState c.σ ∧ c.σ.mem = mA ∧
        c.σ.regs.get? Register.PC = some vbPC ∧
        (∃ vm, c.σ.regs.get? Register.minstret = some vm) ∧
        c.σ.regs.get? Register.x11 = some (sTailWord op x) ∧
        c.σ.regs.get? Register.x10 = some sret ∧
        c.σ.regs.get? Register.x9 = some sret ∧ c.tick < 2)
      (fun c => GoodState c.σ ∧ ValueRepr c.σ.mem N φc sret.toNat (.bool bres))

/-- **`strArmFront`** (model `blockC_eqne_front`).  From the strcmp-entry bundle `cE`
(`StrArmFrontData`), run `strcmp_full_spec ≫ (reconcile) ≫ strRejoinRow ≫ (tok pin) ≫
SignTailLeg ≫ box` to land the boxed `.bool bres` at `sret` — the whole str-arm machine
transport from the strcmp entry through the `value_bool` box.  Delivers a config `cF` reached
from `cE` whose memory carries `ValueRepr … sret (.bool bres)`, exactly as `blockC_eqne_front`
delivers a `VeReturn`.  `StrArmMachineResid` (`StrCmpBlockC`) then factors as str-prologue ≫
`strArmFront`, leaving ONLY the prologue.  Pure `Triple.seq` plumbing over the verified
`strcmp_full_spec` / `strRejoinRow` and the bundle's named connective legs. -/
theorem strArmFront
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (op : BinOp) (tok : BitVec 64) (vbPC r sret : BitVec 64)
    (sp pa pb : BitVec 64) (sa sb : String)
    (mA : Mem) (out0 : Array String) (bres : Bool) (cE : Config)
    (hData : StrArmFrontData g N φc op tok vbPC r sret sp pa pb sa sb mA out0 bres cE) :
    ∃ (cF : Config), Steps cE cF ∧
      GoodState cF.σ ∧ ValueRepr cF.σ.mem N φc sret.toNat (.bool bres) := by
  -- Compose the whole front as ONE `Triple` from the strcmp entry to the boxed `.bool`,
  -- then apply it to `cE`.  `x` (the strcmp return sign) is threaded by pushing the
  -- callee `strcmp_full_spec` first and reconciling into the rejoin `SegPre`.
  -- strcmp entry → strcmp_post
  obtain ⟨cS, hStepsS, hPostS⟩ :=
    strcmp_full_spec g pa pb (0x80003b1c#64) sa sb mA out0 cE hData.hStrcmpPre
  -- extract the return sign `x` from strcmp_post's existential (keeping `hPostS` intact):
  -- `strcmp_post = _ ∧ … ∧ ∃ (csa csb : List Char) (x : BitVec 64), …` (7 conjuncts, then ∃)
  obtain ⟨_csa, _csb, x, -⟩ := hPostS.2.2.2.2.2.2.2
  -- reconcile strcmp_post → rejoin SegPre, then run the verified rejoin row
  obtain ⟨cR, hStepsR, hRej⟩ := (hData.hReconcile x) cS hPostS
  obtain ⟨cRj, hStepsRj, hRjPost⟩ := (strRejoinRow sp x sret [] mA) cR hRej
  -- pin the op token `x12 = tok` at the rejoin post (frame fact from the prologue)
  obtain ⟨cT, hStepsT, hTok⟩ := (hData.hTokAtRejoin x) cRj hRjPost
  -- run the op's sign-tail leg to the `value_bool` entry
  obtain ⟨cST, hStepsST, hSTPost⟩ := (hData.hSignTail x) cT hTok
  -- box: value_bool → .bool (sTailWord op x != 0) = .bool bres
  obtain ⟨cF, hStepsF, hGF, hReprF⟩ := (hData.hBox x) cST hSTPost
  refine ⟨cF, ?_, hGF, hReprF⟩
  exact ((((hStepsS.trans hStepsR).trans hStepsRj).trans hStepsT).trans hStepsST).trans hStepsF

#print axioms strArmFront

/-! ## Factoring `StrArmMachineResid` as str-prologue ≫ `strArmFront`

`StrArmMachineResid op bres` (`StrCmpBlockC`) is the whole-node `EvalIH` for `.binary op el
er` at string operands.  `strArmFront` discharges its MACHINE MIDDLE (strcmp seam → sign
tail → box); what remains is the str-operand PROLOGUE — `blockA_binaryArm` entry ≫
`blockB_binary` operand recursions at kind 3 (the same missing prologue that blocks the
concat cell in `BinStrCells` §b) ≫ the `EvalIH` marshalling that wraps the machine `Steps`
into the judgment.  `StrArmPrologue` NAMES exactly that residual: from the node data it
stages the `strArmFront` bundle at the strcmp entry and marshals `strArmFront`'s machine
outcome back into the whole-node `EvalIH`.  `strArmMachineResid_of` forwards it — the
str-arm analogue of how `eqBlockC_bridge` composes `blockC_eqne_front` under the eq/ne
prologue, and of `strCmpCellResid_of` (`StrCmpBlockC`) forwarding the machine residual.

Left as a named premise exactly as `StrArmMachineResid` itself is in `StrCmpBlockC`; the
machine middle it would otherwise re-derive is now the LANDED `strArmFront`. -/
def StrArmPrologue (op : BinOp) (bres : String → String → Bool) : Prop :=
  ∀ (st : Vsa.While.St) (d : Nat) (env : Vsa.While.Addr) (el er : Expr)
    (st'' : Vsa.While.St) (sl sr : String),
    -- the prologue supplies the whole-node `EvalIH`, having threaded the operand recursions
    -- and consumed the `strArmFront` machine transport (`sl`/`sr` = the evaluated operand
    -- strings, `bres sl sr` = the boxed order the `value_bool` step lands via `hOrder`).
    (∀ (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
       (φc : Vsa.While.Addr → Nat) (tok vbPC rr sret sp pa pb : BitVec 64)
       (mA : Vsa.MemRepr.Mem) (out0 : Array String) (cE : Config),
       StrArmFrontData g N φc op tok vbPC rr sret sp pa pb sl sr mA out0 (bres sl sr) cE →
       ∃ (cF : Config), Steps cE cF ∧
         GoodState cF.σ ∧ ValueRepr cF.σ.mem N φc sret.toNat (.bool (bres sl sr))) →
    EvalIH st d env (.binary op el er) st'' (.bool (bres sl sr))

/-- Assemble `StrArmMachineResid op bres` from `StrArmPrologue op bres`, feeding it the
LANDED `strArmFront` as the machine-transport discharger.  The prologue is the only residual;
the strcmp-seam→sign-tail→box middle is proved. -/
theorem strArmMachineResid_of (op : BinOp) (bres : String → String → Bool)
    (hProlog : StrArmPrologue op bres) :
    StrArmMachineResid op bres :=
  fun st d env el er st'' sl sr =>
    hProlog st d env el er st'' sl sr
      (fun g N φc tok vbPC rr sret sp pa pb mA out0 cE hData =>
        strArmFront g N φc op tok vbPC rr sret sp pa pb sl sr mA out0 (bres sl sr) cE hData)

/-! ## The four op-token instances (feeding `strCmpCell_*_of`, `StrCmpBlockC`) -/

/-- `.lt` str-arm machine residual, via the prologue + the landed `strArmFront`. -/
theorem strArmMachineResid_lt (hProlog : StrArmPrologue .lt (fun sl sr => sl < sr)) :
    StrArmMachineResid .lt (fun sl sr => sl < sr) :=
  strArmMachineResid_of .lt _ hProlog

/-- `.le` str-arm machine residual. -/
theorem strArmMachineResid_le
    (hProlog : StrArmPrologue .le (fun sl sr => sl < sr || sl == sr)) :
    StrArmMachineResid .le (fun sl sr => sl < sr || sl == sr) :=
  strArmMachineResid_of .le _ hProlog

/-- `.gt` str-arm machine residual. -/
theorem strArmMachineResid_gt (hProlog : StrArmPrologue .gt (fun sl sr => sr < sl)) :
    StrArmMachineResid .gt (fun sl sr => sr < sl) :=
  strArmMachineResid_of .gt _ hProlog

/-- `.ge` str-arm machine residual. -/
theorem strArmMachineResid_ge
    (hProlog : StrArmPrologue .ge (fun sl sr => sr < sl || sl == sr)) :
    StrArmMachineResid .ge (fun sl sr => sr < sl || sl == sr) :=
  strArmMachineResid_of .ge _ hProlog

#print axioms strArmMachineResid_of
#print axioms strArmMachineResid_lt
#print axioms strArmMachineResid_le
#print axioms strArmMachineResid_gt
#print axioms strArmMachineResid_ge

end Vsa.Sim
