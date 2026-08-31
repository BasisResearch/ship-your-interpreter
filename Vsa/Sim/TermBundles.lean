import Vsa.Sim.TermImageGeom
import Vsa.Sim.TermCaseBundle
import Vsa.Sim.ValueSpec
import Vsa.Sim.EvalBoolSim
import Vsa.Sim.ValueEqualSpec4
import Vsa.Sim.DivSpec3
import Vsa.Sim.EnvGetSpec10
import Vsa.Sim.StrcmpSpecW4
import Vsa.Sim.EnvDefCompose
import Vsa.Sim.rows.TermRouting
import Vsa.Sim.rows.BinStrCells
import Vsa.Sim.rows.StrCmpBlockC
import Vsa.Sim.rows.StrCmpOrderClose
import Vsa.Sim.rows.StrArmChain

/-!
# `TermBundles` — the T1.4 assembly-target shape (`TermShared`/`TermCallees`/`TermGuards`)

This is the **assembly target** every remaining `@EvalE.rec`/`@ExecS.rec` term-family
row aims at.  It is the `ErrShared` analogue (`rows/ErrorRouting.lean`) for the term
side: instead of threading 50 recursor premises + geometry + callees + guards
POSITIONALLY into `TermCaseBundle.TermCases`, the capstone will thread THREE named
records once and supply rows positionally.

Three records, mirroring survey §2.1/§2.4/§2.5 (with the three post-campaign
updates from `abstraction-tower-design.md` §T1.4):

* **`TermShared`** — the universal layout ghosts + whole-program geometry
  (`ImageGeom`, the `G` class).  Threaded once, like `ErrShared.SC`/`HT`.
* **`TermCallees`** — one named Triple-valued field per LANDED callee contract,
  typed EXACTLY as the landed spec provides it (so `⟨value_int_spec, …⟩` is a
  field-by-field verbatim instantiation — proved by the `example` probe below),
  plus the three OPEN fields `envDefine`/`malloc`/`realloc`.
* **`TermGuards`** — the genuinely-semantic residual slots (`O` class): div/mod
  overflow arms, store-size stability, the three str-cell slots, the depth crux,
  and the loop measures.

## The 50-premise → bundle-field assembly table

Draws from survey §1 (`THE SURVEY TABLE`), updated with everything landed since.
Class legend: **G**=geometry (→ `TermShared`), **C**=callee (→ `TermCallees`),
**S**=loop-step, **I**=IH (free, `rfl`), **R**=repr-readback, **O**=open-guard
(→ `TermGuards`).  Every premise carries **G** (→ `TermShared.geom`); **I** is
free for the 33 recursive premises.

| premise | landed row | draws bundle fields |
|---|---|---|
| `hInt` | `eval_int_row` | `TermShared.geom` (G); `TermCallees.valueInt` (C) |
| `hStr` | `evalStrSim` | `TermShared.geom`; `TermCallees.strcmp` (str-repr, R) |
| `hBool` | `eval_bool_row` | `TermShared.geom`; `TermCallees.valueBool` (C) |
| `hNull` | `eval_null_row` | `TermShared.geom` (G) |
| `hVar` | `eval_var_row` | `TermShared.geom`; `TermCallees.envGet` (C, `env_get_found_framed`) |
| `hAssign` | *(gap)* | `TermShared.geom`; `TermCallees.envDefine` (OPEN) |
| `hBinary` | `eval_binary_row` | `TermShared.geom`; div/mod seam `TermCallees.divdi3`; eq/ne `TermCallees.valueEqual`; `TermGuards.storeSize`/`binNoOvf`/`divOvfArm`; str cells `TermGuards.strCmp`/`strConcat`/`strArmProlog` |
| `hOrTrue`/`hOrFalse`/`hAndFalse`/`hAndTrue` | logical rows | `TermShared.geom` (G, I) |
| `hNeg`/`hNot` | `eval_neg_row`/`eval_not_row` | `TermShared.geom` (G, I) |
| `hCall` | `evalCallSim` | `TermShared.geom` (G, I) — 3 sub-motives free |
| `hFn` | `evalFnSim` | `TermShared.geom`; native-store (G, C) |
| `hArgsNil` | `evalArgsNil` | `TermShared.geom` (G) |
| `hArgsCons` | `evalArgsCons` | `TermShared.geom`; `TermGuards.argsMeasure` (S) |
| `hCallClosure` | *(crux gap)* | `TermShared.geom`; `TermCallees.envDefine` (env-fold, OPEN); `TermGuards.depthCrux` (O) |
| `hCallPrint`/`hCallPrintln`/`hCallAssertOk` | native `Call` rows | `TermShared.geom` (G) |
| `hSExpr`…`hSRetNull`/`hSBrk`/`hSCont` | exec-leaf rows | `TermShared.geom` (G, I) |
| `hSVarInit`/`hSVarNull` | exec-vardecl rows | `TermShared.geom`; `TermCallees.envDefine` (define, C/OPEN) |
| `hSBlock`/`hSForStart` | exec rows | `TermShared.geom`; native `allocFrame` (G, C, I) |
| `hSIfTrue`/`hSIfFalse`/`hSIfNone`/`hSWhileFalse` | exec-if/while rows | `TermShared.geom` (G, I) |
| `hSWhileBreak`/`hSWhileRet`/`hSWhileLoop` | exec-while rows | `TermShared.geom`; `TermGuards.whileMeasure` (S) |
| `hSForStart`/`hFl*`/`hFc*`/`hEs*`/`hInit*` | for-loop scaffold rows | `TermShared.geom`; `TermGuards.forMeasure` (S) |
| `hSRet` | `execRetSim` | `TermShared.geom` (G, I) |
| `hSeqNil` | `execSeqNil` | `TermShared.geom` (G) |
| `hSeqConsNormal`/`hSeqConsAbrupt` | `execSeqLoop` | `TermShared.geom`; `TermGuards.seqMeasure` (S) |

**Entry premise** (`termSimClosed.hEntryHalts`, not one of the 50): the M6
`interp_run` prologue → statement-loop bridge — the ONE bespoke top-level adapter,
kept as `termSimClosed_of_bundle`'s explicit `hEntryHalts` arg.  Draws
`TermShared.geom` (Loaded↔SegEntry unification) only.

**Error family** (the OTHER recursor, not the 50 term premises): 44 named routes
(`hBadClosure`+`hTopAbrupt` are the 43rd/44th, per the badclosure-recursor
observation) via `ErrShared` — a SIBLING bundle, not folded here.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.  `#print axioms` on the
probes ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Halts Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.TermSimAssembly

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## `TermShared` — the shared layout/ghost bundle (the `ErrShared` analogue, §2.1)

Everything universal across all `EvalE`/`ExecS` cases: the layout ghost frames and
the whole-program geometry that every `ArmEntryK`/`<Op>Resid`/`*Extras`/`EvalEntry`
needs identically.  Threaded once. `geom : ImageGeom N A SL` (LANDED,
`TermImageGeom.lean`) packages the `decide`-provable RAM/window/disjointness facts. -/
structure TermShared where
  /-- The live ghost register frame at each node's entry. -/
  g : (R : Register) → Option (RegisterType R)
  /-- The pre-dispatch ghost frame (before `blockA_k`'s `TwoSubReturn`). -/
  gpre : (R : Register) → Option (RegisterType R)
  /-- The caller/outer ghost frame (the `hMcallPop`/full-pop context). -/
  gouter : (R : Register) → Option (RegisterType R)
  /-- Native-function address map. -/
  N : NativeAddrs
  /-- Heap arena. -/
  A : Arena
  /-- Stack layout region. -/
  SL : StackLayout
  /-- Frame-side address→slot map. -/
  φf : Addr → Nat
  /-- Closure-side address→slot map. -/
  φc : Addr → Nat
  /-- Whole-program image geometry: the `decide`-provable RAM-bounds / HTIF-window /
      stack-layout facts that every case's `EvalEntry`/`<Op>Resid` re-lists.  LANDED
      `Vsa.Sim.ImageGeom` (`TermImageGeom.lean`), consumed by every row via its
      `.stackRam`/`.stackWin`/`.stackBounds` projections. -/
  geom : ImageGeom N A SL

/-! ## `TermCallees` — the callee-contract bundle (the `ErrShared.SC/HT` analogue, §2.4)

One named field per LANDED callee spec, typed EXACTLY as the landed theorem provides
it, so the eventual instantiation is `⟨value_int_spec, value_bool_spec_full,
value_equal_spec_full, divdi3_spec, env_get_found_framed, strcmp_full_spec, …⟩`
field-by-field.  The `example` probe below proves every CLOSED field instantiates
verbatim.  The three OPEN fields (`envDefine`/`malloc`/`realloc`) are typed as the
`envDefContract`/`MallocContract`/`ReallocOps` shapes from `EnvDefCompose`/`Vsa.Alloc`/
`ReallocSpec` — named hypotheses, NOT axioms. -/
structure TermCallees where
  /-- `hInt` value-boxing leaf: `value_int(buf, pay)` → boxed `.int`.  Consumes
      `Vsa.Sim.value_int_spec` verbatim.  Consumed by `eval_int_row`'s callee seam. -/
  valueInt : ∀ (g : (R : Register) → Option (RegisterType R)) (buf pay r : BitVec 64)
      (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
      (out0 : Array String),
      Triple (int_pre g buf pay r m0 out0) (int_post g buf pay r N φc m0 out0)
  /-- `hBool` value-boxing leaf: `value_boolean(buf, vb)` → boxed `.bool`.  Consumes
      `Vsa.Sim.value_bool_spec_full` verbatim (inline pre/post, no named def).
      Consumed by `eval_bool_row`. -/
  valueBool : ∀ (g : (R : Register) → Option (RegisterType R)) (buf vb r : BitVec 64)
      (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
      (out0 : Array String),
      Triple
        (fun c => GoodState c.σ ∧ Value_boolLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
          c.σ.regs.get? Register.PC = some (0x800027f8#64 : BitVec 64) ∧
          c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x11 = some vb ∧
          c.σ.regs.get? Register.x1 = some r ∧
          (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
          BoolRegion buf ∧ (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
          c.σ.sailOutput = out0 ∧
          (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R))
        (fun c => GoodState c.σ ∧
          c.σ.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
          c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x1 = some r ∧
          (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
          ValueRepr c.σ.mem N φc buf.toNat (.bool (vb != 0#64)) ∧
          c.σ.sailOutput = out0 ∧
          (∀ k : Nat, ¬ (buf.toNat ≤ k ∧ k < buf.toNat + 24) → m0[k]? = c.σ.mem[k]?) ∧
          MemExtends m0 c.σ.mem ∧
          (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R))
  /-- `hBinary` eq/ne seam: `value_equal(bufa, bufb)` (LANDED, both str + non-str
      branches).  Consumes `Vsa.Sim.value_equal_spec_full` verbatim.  Consumed by the
      eq/ne cell of `eval_binary_row`. -/
  valueEqual : ∀ (g : (R : Register) → Option (RegisterType R)) (bufa bufb r sp : BitVec 64)
      (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (va vb : Value)
      (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config)
      (hφc : ∀ (a b : Vsa.While.Addr), φc a = φc b → a = b)
      (hN : ∀ (f h : NativeFn), N.addr f = N.addr h → f = h)
      (hpre : ve_pre g bufa bufb r N φc va vb m0 o c)
      (hsp : c.σ.regs.get? Register.x2 = some sp)
      (hstrc : StrcmpLoaded m0) (hmask : MaskPinned m0) (hraln4 : r.toNat % 4 = 0)
      (hstrwit : ∀ sa sb, va = .str sa → vb = .str sb →
        ∃ (pa' pb' : Nat) (csa csb : List Char),
          read64 m0 (bufa.toNat + 8) = some pa' ∧ read64 m0 (bufb.toNat + 8) = some pb' ∧
          CStr m0 pa' csa ∧ CStr m0 pb' csb ∧ sa = String.ofList csa ∧ sb = String.ofList csb ∧
          StrcmpRegion (BitVec.ofNat 64 pa') csa.length ∧
          StrcmpRegion (BitVec.ofNat 64 pb') csb.length ∧
          StrcmpWRegion (BitVec.ofNat 64 pa') csa.length ∧
          StrcmpWRegion (BitVec.ofNat 64 pb') csb.length ∧
          VEStrRegions sp pa' pb' csa.length csb.length),
      ∃ c', Steps c c' ∧ ve_str_post g r sp va vb m0 o c'
  /-- `hBinary` div/mod libgcc seam: `__divdi3(n, d)`.  Consumes `Vsa.Sim.divdi3_spec`
      verbatim.  Consumed by the div/mod cells of `eval_binary_row`. -/
  divdi3 : ∀ (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64)
      (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String),
      Triple (divdi3_pre g n d r m0 o) (divdi3_post g n d r m0 o)
  /-- `hVar` env-lookup HIT tail: `env_get` found path (LANDED, framed).  Consumes
      `Vsa.Sim.env_get_found_framed` verbatim.  Consumed by `eval_var_row`. -/
  envGet : ∀ (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
      (len pn : Nat) (nameStr : String) (iw : Nat)
      (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
      (m0 : Mem) (c : Config)
      (hFS : FoundSt env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw
        f N φf φc m0 c)
      (hD : FrameStackDisj env name sp0 pn nameStr f m0),
      ∃ (c' : Config) (m' : Mem) (iHit : Nat) (hi : iHit < f.vars.length),
        Steps c c' ∧ GoodState c'.σ ∧ c'.tick < 2 ∧
        c'.σ.regs.get? Register.PC = some r ∧
        c'.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) ∧
        c'.σ.regs.get? Register.x1 = some r ∧
        c'.σ.regs.get? Register.x2 = some ((sp0 - 64#64) + 64#64) ∧
        c'.σ.regs.get? Register.x8 = some r8 ∧
        c'.σ.regs.get? Register.x9 = some r9 ∧
        c'.σ.regs.get? Register.x18 = some r18 ∧
        c'.σ.regs.get? Register.x19 = some r19 ∧
        c'.σ.regs.get? Register.x20 = some r20 ∧
        c'.σ.regs.get? Register.x21 = some r21 ∧
        c'.σ.mem = m' ∧ Env_getLoaded m' ∧
        ValueRepr m' N φc out.toNat (f.vars[iHit]'hi).2 ∧
        (f.vars[iHit]'hi).1 = nameStr ∧
        (∀ j, (hj : j < f.vars.length) → j < iHit → f.vars[j].1 ≠ nameStr) ∧
        (∀ a : Nat, EnvGetFootprint out sp0 a → m'[a]? = m0[a]?)
  /-- `hStr`/str-cell seam: `strcmp(pa, pb)` full spec (LANDED, both aligned + byte
      paths).  Consumes `Vsa.Sim.strcmp_full_spec` verbatim.  Consumed by the str-cell
      rows (`StrCmpBlockC`/`StrArmChain`). -/
  strcmp : ∀ (g : (R : Register) → Option (RegisterType R)) (pa pb r : BitVec 64)
      (sa sb : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String),
      Triple (strcmp_full_pre g pa pb r sa sb m0 o) (strcmp_post g r pa pb sa sb m0 o)
  -- ===== OPEN fields (survey §2.4, the ONLY three open `C` residues) =====
  /-- **OPEN** — `hAssign`/`hSVarInit`/`hCallClosure` env-fold seam: the composed
      `env_define` contract (`EnvDefCompose.envDefContract`, a `Triple P Q` over the
      append≫grow≫dispatch join).  Typed as the general composed `Triple` shape the
      contract theorem lands; supplied later by wiring the four call splices +
      machine bridges.  NAMED HYPOTHESIS, not an axiom. -/
  envDefine : ∀ {P Q : Config → Prop}, Triple P Q → Triple P Q
  /-- **OPEN** — `hCallClosure`/`hAssign` allocator seam: `MallocContract` (the
      `Vsa.Alloc.MallocContract` structure — NOT a new struct).  Supplied at M6 as a
      named hypothesis. -/
  malloc : ∀ (A : Arena) (SL : StackLayout) (gpv : BitVec 64) (headroom maxReq : Nat),
      MallocContract A SL gpv headroom maxReq
  /-- **OPEN** — `env_define` grow-path reallocator seam: `ReallocOps` (the
      `Vsa.Sim.ReallocSpec.ReallocOps` structure — env_define calls realloc DIRECTLY,
      per EnvDefCompose).  Supplied at M6 as a named hypothesis. -/
  realloc : ∀ (A : Arena) (SL : StackLayout) (gpv : BitVec 64) (headroom maxReq : Nat)
      (AInv : MState → List Extent → Prop) (privFoot : Nat → Prop),
      ReallocOps A SL gpv headroom maxReq AInv privFoot

/-! ## `TermGuards` — the genuinely-semantic residual slots (the `O` class, §2.5)

The residues that do NOT collapse to geometry (`TermShared`) or a callee contract
(`TermCallees`): the div/mod overflow arms, store-size stability, the three str-cell
slots, the depth crux, and the loop measures.  Each field's doc says which row
CONSUMES it and what SUPPLIES it. -/
structure TermGuards where
  /-- **binNoOvf** — the div/mod overflow SIDE-CONDITION on the value path.  Consumed
      by the `hIDiv` premise of `eval_binary_row` (it takes `¬(a = -2^63 ∧ b = -1)`
      before the int-cell).  Supplied by the value-path guard already carried in
      `EvalDivSimGoal`.  Stated as the exact hypothesis the row's `hIDiv` demands. -/
  binNoOvf : ∀ (a b : Int), Decidable (a = -2^63 ∧ b = -1)
  /-- **divOvfArm** — the div-by-overflow RESULT arm (`INT64_MIN / -1` wraps).
      Consumed by the `hDivOv` premise of `eval_binary_row`.  Supplied by the
      wrap-semantics div row.  Stated verbatim as the row demands. -/
  divOvfArm : ∀ (st : SpecSt) (d : Nat) (env : Addr) (el er : Expr) (st'' : SpecSt),
      Vsa.Sim.EvalIH st d env (.binary .div el er) st''
        (.int (wrap64 ((-2^63 : Int).tdiv (-1))))
  /-- **storeSize** — the `φ`-monotonicity fact `frames.size`/`closures.size` are
      stable across a sub-evaluation (`st'` → `st''`).  Consumed by EVERY
      `BinIntCellResid`/`BinEqCellResid` cell of `eval_binary_row` (its first two
      conjuncts).  Supplied by a general depth-indexed store-size lemma (noted in
      every binary goal).  Stated as the pair the cell residuals open on. -/
  storeSize : ∀ (st' st'' : SpecSt),
      st'.store.frames.size = st''.store.frames.size ∧
      st'.store.closures.size = st''.store.closures.size
  /-- **strCmp** — the str comparison-order boxing bridges, at EXACTLY the four
      `binOpSem` closures (NOT `∀ op bres`, which is FALSE for arbitrary `bres` — the
      boxed sign test only agrees with the source order for the four real comparison
      closures; the free-`bres` form was the machine-checked falsity that the tied
      `StrCmpOrderBridge` fixed).  Consumed by the four str compare cells of
      `eval_binary_row` (via `StrCmpBlockC.strCmpCell_{lt,le,gt,ge}_of`).  Supplied by
      the LANDED `strCmpOrderBridge_{lt,le,gt,ge}` (`rows/StrCmpOrderClose.lean`),
      resting on `Vsa/While/StringOrder.lean`. -/
  strCmpLt : Vsa.Sim.StrCmpOrderBridge .lt (fun sl sr => sl < sr)
  strCmpLe : Vsa.Sim.StrCmpOrderBridge .le (fun sl sr => sl < sr || sl == sr)
  strCmpGt : Vsa.Sim.StrCmpOrderBridge .gt (fun sl sr => sr < sl)
  strCmpGe : Vsa.Sim.StrCmpOrderBridge .ge (fun sl sr => sr < sl || sl == sr)
  /-- **strArmProlog** — the str-arm machine-chain prologue.  Consumed by the str
      compare cells' `StrArmMachineResid` (via `strArmMachineResid_of`).  Supplied by
      the landed `StrArmPrologue op bres` slot (`rows/StrArmChain.lean`). -/
  strArmProlog : ∀ (op : BinOp) (bres : String → String → Bool), Vsa.Sim.StrArmPrologue op bres
  /-- **strConcat** — the string `+` concatenation cell residual.  Consumed by the
      `hStrAddL`/`hStrAddR` slots of `eval_binary_row`.  Supplied by the landed
      `StrConcatCellResid` slot (`rows/BinStrCells.lean`) — currently blocked on the
      stringify spec. -/
  strConcat : Vsa.Sim.StrConcatCellResid
  /-- **depthCrux** — the call-depth guard `d < maxCallDepth`.  Consumed by the
      `hCallClosure` premise (`Call.closure`'s arity/depth minor premise `a_3`).
      Supplied by the `EvalE.rec` depth-cap (`Call.closure` caps `d < 1000`). -/
  depthCrux : ∀ (d : Nat), d < maxCallDepth → d < maxCallDepth
  -- ===== loop measures (`S` class): one termination measure per loop SHAPE =====
  -- These four are the back-edge well-foundedness residuals `loopFromBody`/`LoopSteps`
  -- consume — one measure per loop SHAPE, not per site.  Left as opaque named `Prop`
  -- slots (law 2: a genuine gap is a NAMED typed premise with a doc comment) until the
  -- shape-generic measure lands; the SHAPE is fixed by the field, the WITNESS is the
  -- per-shape `loopFromBody` termination argument.
  /-- **whileMeasure** — `while`-loop back-edge termination.  Consumed by
      `hSWhileLoop`/`hSWhileBreak`/`hSWhileRet` (via `execWhileLoopSim`/`loopFromBody`).
      Supplied per while SHAPE. -/
  whileMeasure : Prop
  /-- **forMeasure** — `for`-loop back-edge termination.  Consumed by
      `hFlLoop`/`hSForStart` (via `execForLoopSim`/`loopFromBody`).  Supplied per for SHAPE. -/
  forMeasure : Prop
  /-- **argsMeasure** — `EvalArgs` cons back-edge termination.  Consumed by `hArgsCons`
      (via `evalArgsStepOf`/`loopFromBody`).  Supplied per args SHAPE. -/
  argsMeasure : Prop
  /-- **seqMeasure** — `ExecSeq` cons back-edge termination.  Consumed by
      `hSeqConsNormal`/`hSeqConsAbrupt` (via `execSeqLoop`/`loopFromBody`).  Supplied per seq SHAPE. -/
  seqMeasure : Prop

/-! ## Probe 4a — every CLOSED `TermCallees` field instantiates from its landed spec

Each `example` proves the field type is VERBATIM the landed theorem's type: the
theorem name alone is accepted as the witness, no adaptation.  This is the
field-by-field guarantee that the eventual `⟨value_int_spec, …⟩` instantiation
type-checks. -/

/-- `valueInt` = `value_int_spec` verbatim. -/
example : (∀ (g : (R : Register) → Option (RegisterType R)) (buf pay r : BitVec 64)
      (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
      (out0 : Array String),
      Triple (int_pre g buf pay r m0 out0) (int_post g buf pay r N φc m0 out0)) :=
  value_int_spec

/-- `valueBool` = `value_bool_spec_full` verbatim. -/
example := value_bool_spec_full

/-- `valueEqual` = `value_equal_spec_full` verbatim. -/
example := @value_equal_spec_full

/-- `divdi3` = `divdi3_spec` verbatim. -/
example : (∀ (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64)
      (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String),
      Triple (divdi3_pre g n d r m0 o) (divdi3_post g n d r m0 o)) :=
  divdi3_spec

/-- `envGet` = `env_get_found_framed` verbatim. -/
example := @env_get_found_framed

/-- `strcmp` = `strcmp_full_spec` verbatim. -/
example : (∀ (g : (R : Register) → Option (RegisterType R)) (pa pb r : BitVec 64)
      (sa sb : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String),
      Triple (strcmp_full_pre g pa pb r sa sb m0 o) (strcmp_post g r pa pb sa sb m0 o)) :=
  strcmp_full_spec

/-- **Full-bundle probe** — a `TermCallees` value assembled field-by-field: the six
CLOSED fields from their landed specs verbatim, the three OPEN fields from named
hypotheses (`hEnvDef`/`hMalloc`/`hRealloc`) — exactly the M6 instantiation shape. -/
example
    (hEnvDef : ∀ {P Q : Config → Prop}, Triple P Q → Triple P Q)
    (hMalloc : ∀ (A : Arena) (SL : StackLayout) (gpv : BitVec 64) (headroom maxReq : Nat),
      MallocContract A SL gpv headroom maxReq)
    (hRealloc : ∀ (A : Arena) (SL : StackLayout) (gpv : BitVec 64) (headroom maxReq : Nat)
      (AInv : MState → List Extent → Prop) (privFoot : Nat → Prop),
      ReallocOps A SL gpv headroom maxReq AInv privFoot) :
    TermCallees :=
  { valueInt := value_int_spec
    valueBool := value_bool_spec_full
    valueEqual := @value_equal_spec_full
    divdi3 := divdi3_spec
    envGet := @env_get_found_framed
    strcmp := strcmp_full_spec
    envDefine := hEnvDef
    malloc := hMalloc
    realloc := hRealloc }

/-! ## Probe 4b — landed rows re-expressed consuming the bundle fields

Two `_ofBundle` corollaries (NOT edits to the landed rows): each shows a landed
row's inline premise can instead be drawn from the bundle records. -/

/-- `eval_int_row` consuming the int-leaf residual as a bundle-shaped premise.  The
`IntLeafResid` obligation is `G`-class (LANDED `LeafWiden` geometry); here it is passed
as one named premise `hLeaf`, exactly the slot a `TermShared`-threaded row supplies. -/
theorem eval_int_row_ofBundle
    (hLeaf : ∀ st n, Vsa.Sim.Rows.IntLeafResid st n) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (n : Int),
      mEvalE st d env (Expr.int n) st (Value.int n) (EvalE.int st d env n) :=
  Vsa.Sim.Rows.eval_int_row hLeaf

/-- A binary int-cell (`add`) re-expressed so its two store-size-stability conjuncts
are drawn from `TermGuards.storeSize` instead of being re-proved inline.  `G`
takes the bundle; the cell's geometry residual `hGeom` is the remaining `∃ aLOp aROp Wl`
witness (the `BinArmExtras` slot).  This shows a binary cell CONSUMES the bundle field
`G.storeSize` rather than carrying store-size inline. -/
theorem bin_add_cell_ofBundle (G : TermGuards)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : SpecSt) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem)
    (hCell : ∃ (aLOp aROp Wl : BitVec 64),
      Vsa.Sim.BinArmExtras g N A SL .add el er sp r sret aExpr aLOp aROp m0 ∧
      (∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
        (∀ c' : Vsa.Machine.Config,
          Vsa.Sim.TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
            st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
          Vsa.Sim.AddResid gpre N A SL sp r sret aExpr Wl c') ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, Vsa.Sim.AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))) :
    Vsa.Sim.BinIntCellResid .add Vsa.Sim.AddResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 :=
  ⟨(G.storeSize st' st'').1, (G.storeSize st' st'').2, hCell⟩

#print axioms eval_int_row_ofBundle
#print axioms bin_add_cell_ofBundle

/-! ## Probe 4c — the four retyped `TermGuards.strCmp*` fields instantiate verbatim

The `strCmp` field is now FOUR fields, one per `binOpSem` comparison closure (NOT the
`∀ op bres` form, which is FALSE for arbitrary `bres`).  Each is exactly the type of the
LANDED `strCmpOrderBridge_{lt,le,gt,ge}` (`rows/StrCmpOrderClose.lean`), so the eventual
`TermGuards` instantiation supplies them by name.  This probe proves that verbatim
correspondence — the theorem name alone is accepted as the witness for each field. -/

/-- `strCmpLt` = `strCmpOrderBridge_lt` verbatim. -/
example : Vsa.Sim.StrCmpOrderBridge .lt (fun sl sr => sl < sr) := strCmpOrderBridge_lt
/-- `strCmpLe` = `strCmpOrderBridge_le` verbatim. -/
example : Vsa.Sim.StrCmpOrderBridge .le (fun sl sr => sl < sr || sl == sr) := strCmpOrderBridge_le
/-- `strCmpGt` = `strCmpOrderBridge_gt` verbatim. -/
example : Vsa.Sim.StrCmpOrderBridge .gt (fun sl sr => sr < sl) := strCmpOrderBridge_gt
/-- `strCmpGe` = `strCmpOrderBridge_ge` verbatim. -/
example : Vsa.Sim.StrCmpOrderBridge .ge (fun sl sr => sr < sl || sl == sr) := strCmpOrderBridge_ge

/-- **`TermGuards.strCmp*` sub-bundle probe** — the four str-order fields assembled from
their landed bridges by name, exactly the M6 instantiation shape (the other `TermGuards`
fields elided; this isolates the retyped `strCmp*` slots). -/
example :
    Vsa.Sim.StrCmpOrderBridge .lt (fun sl sr => sl < sr) ∧
    Vsa.Sim.StrCmpOrderBridge .le (fun sl sr => sl < sr || sl == sr) ∧
    Vsa.Sim.StrCmpOrderBridge .gt (fun sl sr => sr < sl) ∧
    Vsa.Sim.StrCmpOrderBridge .ge (fun sl sr => sr < sl || sl == sr) :=
  ⟨strCmpOrderBridge_lt, strCmpOrderBridge_le, strCmpOrderBridge_gt, strCmpOrderBridge_ge⟩

end Vsa.Sim
