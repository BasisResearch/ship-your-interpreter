import Vsa.Sim.InductionScaffold
import Vsa.Sim.BlockTerm
import Vsa.Sim.DecodeTable.Batch08Part19
import Vsa.Sim.Code.Native_assert
import Vsa.Sim.Code.Native_print
import Vsa.Sim.Code.Native_println
import Vsa.Sim.Code.Value_truthy
import Vsa.Sim.Code.Value_null
import Vsa.Sim.Code.Value_int
import Vsa.Sim.Code.Env_new
import Vsa.Sim.Code.Env_define
import Vsa.Sim.Code.Strlen
import Vsa.Sim.Code.Memcpy
import Vsa.Sim.ReallocSpec
import Vsa.Sim.HeapOps
import Vsa.Sim.CallExternalContracts
import Vsa.Sim.ConsoleStream
import Vsa.Sim.rows.StoreWF

/-!
# Layer 4 — M4: OPENING the `call` subsystem (`EvalE.call`)

`EvalE.call` is the last `EvalE` constructor and the interpreter's crux: it
bridges `EvalE → EvalArgs → Call → (closure body via ExecSeq | native)`. Unlike
`exec_stmt`, there is **no separate `call_value` symbol** — the whole callee
evaluation, argument-array construction, native/closure dispatch, and the
closure-body loop are compiled **inline into the `EX_CALL` arm of `eval_expr`**
(jump-table slot 6 → `0x800031b0`). This file is the SURVEY + FOUNDATION: it
records the decode, fills the `InductionScaffold` `SegEntry`/`SegExit` skeletons
for the `EvalArgs`/`Call` relations with real PCs, and lands the first reachable
sub-piece — `EvalArgs.nil` — GREEN (the empty-argument-list no-op, the analog of
`execSeqNil` on the statement side).

## Decoded `EX_CALL` arm (`while-riscv-htif.elf`, inside `eval_expr`)

The arm runs entirely in `eval_expr`'s 1088-byte frame (`s0 = Expr*`,
`s1 = sret`, `s2 = env`). The `.call f args` node layout: `+8 = f` (callee
Expr*), `+16 = args` (Expr** array base), `+24 = argc` (arg count word).

### (1) Callee evaluation — `EvalE f → fv` (`0x800031b0 … 0x800031bc`)
```
800031b0:  ld   a2,8(a2)          -- a2 = e->f           (callee Expr*)
800031b4:  addi a0,sp,96          -- sret_f  = sp+96     (callee-value buffer)
800031b8:  sd   a3,0(sp)          -- spill env (a3) to sp+0
800031bc:  jal  eval_expr         -- fv := eval f        (ra = 0x800031c0)
```
So `fv` lands in the 24-byte buffer at `sp+96`. This is one `motive_EvalE` IH
(reuse `armTail_rec`/`SubEvalReturn`) on the callee sub-expression.

### (2) Argument-array construction — `EvalArgs args → vs`
Bounds + init (`0x800031c0 … 0x800031d8`):
```
800031c0:  lw   a5,24(s0)         -- a5 = argc = e->argc
800031c4:  li   a4,32
800031c8:  blt  a4,a5 → 0x80003fb0-- argc>32 ⇒ runtime_error (arg cap; M5)
800031cc:  sd   s7,1016(sp)       -- spill s7
800031d0:  ld   a3,0(sp)          -- reload env
800031d4:  li   a6,0              -- a6 = i = 0          (arg index)
800031d8:  blez a5,0x80003254     -- argc≤0 ⇒ SKIP loop (EvalArgs.nil path!)
```
The **`EvalArgs.nil` case is exactly `argc ≤ 0`**: the machine branches straight
past the loop to the dispatch at `0x80003254` with the argument array left empty
(`vs = []`), store/output unchanged. That branch target `0x80003254` is the
`EvalArgs` loop's *continuation* PC (`evalArgsContPC`), and the loop head is
`0x800031dc` (`evalArgsLoopPC`).

Loop body (`0x800031dc … 0x80003250`, `EvalArgs.cons` per iteration):
```
800031dc:  ld   a2,16(s0)         -- a2 = args base (e->args)
800031e0:  sext.w a1,a6           -- a1 = i (widen)
800031e4:  slli a4,a6,0x3         -- a4 = i*8
800031e8:  add  a2,a2,a4          -- a2 = &args[i]
800031ec:  slli a4,a1,0x1  …      -- a4 = i*3   (3 words per stored Value)
800031f4:  ld   a2,0(a2)          -- a2 = args[i]        (i-th arg Expr*)
800031fc:  sd   a5,24(sp)         -- save argc across the recursive call
80003200:  addi a5,a4,976         -- a5 = i*24 + 976     (Value-array slot off)
80003204:  addi a4,sp,32
80003208:  add  a4,a5,a4          -- a4 = &argstore[i]   (sp+32 + i*24 + 976)
8000320c:  mv   a1,s2             -- a1 = env
80003210:  addi a0,sp,64          -- sret_arg = sp+64    (per-arg value buffer)
…spills i (sp+16), env (sp+8), &argstore[i] (sp+0)…
80003220:  jal  eval_expr         -- vs[i] := eval args[i]   (ra=0x80003224)
80003224…80003250:  reload the 24-byte value (sp+64,72,80) and store the three
          words to argstore[i] (a4-768, -760, -752, i.e. sp+32+i*24+208);
          i++ ; bne a6,a5 → 0x800031dc   (back-edge while i≠argc)
```
So the argument vector is materialised into a stack Value-array; each iteration
is one `motive_EvalE` IH on `args[i]` followed by a 24-byte copy — the classic
`consNormal`-shaped body (analog of the `block`-loop `armExec_rec`).

### (3) `call_value` dispatch — native vs closure (`0x80003254 … 0x800032b0`)
```
80003254:  ld   a4,96(sp)         -- a4 = fv word0 (kind || …); a3 = fv+8; a6 = fv+16
…stage fv's 24 bytes into sp+120/128/136 (callee spill)…
80003268:  lw   a4,96(sp)         -- a4 = fv->kind
80003274:  li   a2,5
8000327c:  beq  a4,a2 → 0x800039e0 -- kind==5 (VAL_NATIVE) ⇒ native path
80003280:  li   a2,4
80003284:  bne  a4,a2 → 0x80003da4 -- kind!=4 (VAL_CLOSURE) ⇒ runtime_error (M5)
```
`fv->kind`: `4 = VAL_CLOSURE`, `5 = VAL_NATIVE`. Anything else is a
"not callable" runtime error (underivable in the spec). So `Value.closure`/
`Value.native` are the only two `Call` shapes, matching the spec.

### (4) The closure path — `Call.closure` (`0x80003288 … 0x80003974`)
```
80003288:  ld   a4,0(a3)          -- a4 = *(fv+8) = Closure* cd     (s5 := cd)
80003294:  lw   a4,24(a4)         -- a4 = cd->arity (param count)
80003298:  bne  a5,a4 → 0x80003d60-- arity mismatch ⇒ runtime_error
                                  --   (a5 = argc; spec: vs.length = params.length)
8000329c:  lw   a4,8(s2)          -- a4 = interp->call_depth
800032a0:  li   a2,1000           --   MAX_CALL_DEPTH  (= maxCallDepth!)
800032a4:  addiw a4,a4,1          -- ++call_depth
800032a8:  sw   a4,8(s2)          --   store back
800032b0:  blt  a2,a4 → 0x80003ca4-- if call_depth>1000 ⇒ runtime_error
                                  --   (spec: d < maxCallDepth, run body at d+1)
800032b4:  ld   a0,8(a3)          -- a0 = cd->env  (captured environment)
800032bc:  jal  env_new           -- frame := env_new(cd->env)   (s3 := new frame)
                                  --   = Store.allocFrame (some cd.env)
--- param-binding loop 0x800032cc … 0x80003320 (bind params[i] := vs[i]) ---
800032dc…: ld the 24-byte vs[i] from the arg Value-array, ld cd->params[i] name,
           jal env_define(frame,name,pv)     -- = Store.define frame x v
           i++ ; bne s6,a5 → 0x800032dc      (fold over params.zip vs)
--- body sret staging + the body ExecSeq loop 0x80003324 … 0x80003974 ---
80003324:  addi a0,sp,144         -- body sret buffer
80003328:  jal  value_null        -- default return value = null
8000332c:  ld   a6,32(s5)         -- a6 = cd->body (Stmt** array)   (Block node)
80003330:  li   s0,0              -- i = 0
80003334:  lw   a5,16(a6)         -- count = cd->body->count
80003338:  bgtz a5 → 0x80003354   -- enter loop iff count>0
8000333c:  j    0x80003954        -- empty body ⇒ normal exit
--- body loop 0x80003354 … 0x80003378 ---
80003354:  ld   a5,8(a6)          -- stmts base
80003358:  slli a4,s0,0x3         -- i*8
80003364:  ld   a1,0(a5)          -- a1 = body[i]  (Stmt*)
80003368:  mv   a2,s3             -- a2 = frame
8000336c:  mv   a0,s2             -- a0 = interp
80003374:  jal  exec_stmt         -- status := exec_stmt(body[i])   (ExecSeq!)
80003378:  beqz a0 → 0x80003340   -- status==normal ⇒ next stmt
                                  -- else: 0x8000337c dec call_depth; classify
                                  --   status<=1 (brk/cont escape) ⇒ runtime_error
                                  --   status==3 (ret) ⇒ 0x8000339c: copy the
                                  --     24-byte return value from sp+144 into
                                  --     *s1 (the CALL's own sret) ; j 0x800033ec
--- normal-body exit 0x80003954 … 0x80003974 ---
80003954:  lw a5,8(s2); addiw a5,a5,-1; sw   -- --call_depth
80003960:  mv a0,s1 ; jal value_null          -- return value = null
80003974:  j  0x800033ec                       -- epilogue (mv a0,s1 ; ret)
```
This is the `Call.closure` constructor end-to-end:
`allocFrame (some cd.env)` (env_new) → bind `params.zip vs` (env_define fold) →
run `cd.body` as an **`ExecSeq` at depth `d+1`** (the `exec_stmt` loop, exactly
the `block`-arm loop shape — reuse `execSeqLoop`/`armExec_rec`) → `.normal`
returns `null`, `.ret v` returns `v`, `brk`/`cont` are runtime errors
(underivable). `d < maxCallDepth` is the `blt a2,a4` guard; the body runs at
`call_depth+1`; the epilogue `--call_depth`s back.

### (5) The native path — `Call.print`/`println`/`assertOk` (`0x800039e0`)
```
800039e0:  mv   a4,a1             -- a4 = argc
800039e4:  mv   a2,a5             -- a2 = arg Value-array base
800039e8:  mv   a1,s2             -- a1 = interp
800039ec:  addi a3,sp,240         -- a3 = scratch
800039f0:  mv   a0,s1             -- a0 = CALL sret
800039f4:  jalr a6                -- a6 = fv->fn  (the native fn ptr) — indirect!
800039f8:  ld   s7,1016(sp) ; j 0x800033ec
```
The native is dispatched by an **indirect `jalr a6`** where `a6 = fv+16` is the
stored C function pointer (`native_print`/`native_println`/`native_assert`,
symbols at `0x80002ed4`/`0x80002f7c`/`0x80002df4`). Each returns `value_null`
into the sret and appends to the console:
* `native_print`  — loops the `argc` values, `value_print` each separated by a
  single space (`li a0,32`), no trailing newline ⇒ `printArgs` + no `"\n"`
  (`Call.print`).
* `native_println` — calls `native_print` then `fputc('\n')` ⇒ `printArgs` +
  `"\n"` (`Call.println`).
* `native_assert` — `value_truthy(args[0])`; if false ⇒ runtime_error (message
  arg optional: `argc∈{1,2}`), else `value_null` ⇒ `Call.assertOk`
  (`vs=[v]∨vs=[v,m]`, `v.truthy=true`).

## Decoded PC map (constants below)
| relation / event            | PC          |
|-----------------------------|-------------|
| `EX_CALL` arm entry         | `0x800031b0`|
| callee `jal eval_expr` (ra) | `0x800031c0`|
| arg-loop head               | `0x800031dc`|
| arg-loop `jal eval_expr`(ra)| `0x80003224`|
| arg-loop continuation       | `0x80003254`|
| `fv` kind dispatch          | `0x80003254`|
| native branch (kind 5)      | `0x800039e0`|
| closure branch (kind 4)     | `0x80003288`|
| `jal env_new` (ra)          | `0x800032c0`|
| param-bind loop head        | `0x800032dc`|
| body `ExecSeq` loop head    | `0x80003354`|
| body `jal exec_stmt` (ra)   | `0x80003378`|
| closure/native join → epi   | `0x800033ec`|

## What lands here
* the PC constants,
* `EvalArgs`/`Call` motive shapes filled with real PCs (via the scaffold
  `SegEntry`/`SegExit`, exposed as `EvalArgsEntry`/`EvalArgsExit` /
  `CallEntry`/`CallExit` abbreviations at the decoded PCs),
* **`evalArgsNil`** — the `EvalArgs.nil` case, GREEN and UNCONDITIONAL
  (the loaded taken branch from `0x800031d8` to `0x80003254`).

Per-constructor difficulty/plan for the follow-up is in the module doc at the
bottom. NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Scaffold

local notation "SpecSt" => Vsa.While.St

private theorem abiNoise_noiseRegs_call {R : Register} (hR : AbiPreservedNoise R) :
    ∀ rr ∈ noiseRegs, (rr == R) = false := by
  obtain ⟨_, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  intro rr hrr
  simp only [noiseRegs, List.mem_cons, List.not_mem_nil, or_false] at hrr
  rcases hrr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-! ## Decoded PC constants for the `EX_CALL` arm -/

/-- Jump-table slot 6 target: the `EX_CALL` arm entry in `eval_expr`. -/
def callArmPC : Nat := 0x800031b0
/-- Link address after the callee `jal eval_expr`. -/
def callCalleeRetPC : Nat := 0x800031c0
/-- The argument-evaluation loop head (about to evaluate `args[i]`). -/
def evalArgsLoopPC : Nat := 0x800031dc
/-- Constructor-specific argument entry.  Empty lists start at the `blez`
decision; nonempty lists start at the loop body reached by its fallthrough. -/
def evalArgsEntryPC : List Expr → Nat
  | [] => 0x800031d8
  | _ :: _ => evalArgsLoopPC
/-- Link address after the per-argument `jal eval_expr`. -/
def evalArgsRetPC : Nat := 0x80003224
/-- The argument-evaluation loop continuation = the `fv` kind dispatch. The
`EvalArgs.nil` (`argc ≤ 0`) branch jumps straight here. -/
def evalArgsContPC : Nat := 0x80003254
/-- `fv->kind` dispatch (native vs closure) — same PC as the arg-loop cont. -/
def callDispatchPC : Nat := 0x80003254
/-- The native branch (`fv->kind == 5`, `VAL_NATIVE`). -/
def callNativePC : Nat := 0x800039e0
/-- The closure branch (`fv->kind == 4`, `VAL_CLOSURE`). -/
def callClosurePC : Nat := 0x80003288
/-- Link address after `jal env_new` (the call-frame allocation). -/
def callEnvNewRetPC : Nat := 0x800032c0
/-- The parameter-binding loop head (`env_define` fold over `params.zip vs`). -/
def callParamBindPC : Nat := 0x800032dc
/-- The closure body `ExecSeq` loop head (about to run `body[i]`). -/
def callBodyLoopPC : Nat := 0x80003354
/-- Link address after the body `jal exec_stmt`. -/
def callBodyRetPC : Nat := 0x80003378
/-- The closure/native join into the shared `eval_expr` epilogue. -/
def callJoinPC : Nat := 0x800033ec

/-! ## `EvalArgs` entry/exit (the `SegEntry`/`SegExit` skeletons at real PCs)

`EvalArgsEntry g … st d ss sp r m0` = the machine at the arg-loop head with the
remaining argument list `ss` still to evaluate; `EvalArgsExit g … st' m0` at the
loop continuation with the (materialised) argument vector in place. We reuse the
scaffold `SegEntry`/`SegExit` (whole-store `StoreRepr`, `OutRepr`, budgets),
instantiated at the decoded `evalArgsLoopPC`/`evalArgsContPC`. The arg *vector*
placement in the stack Value-array is a per-case field of the eventual `cons`
proof; the `nil` case (below) needs only the shared control state. -/

/-- The `EvalArgs` loop-head entry predicate (scaffold `SegEntry` at
`evalArgsLoopPC`, budgets threaded as in `motive_EvalArgs`). -/
abbrev EvalArgsEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem) : Config → Prop :=
  SegEntry g N A SL φf φc st d dLeft aLeft evalArgsLoopPC m0

/-- The `EvalArgs` loop-continuation exit predicate (scaffold `SegExit` at
`evalArgsContPC`). -/
abbrev EvalArgsExit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : SpecSt) (m0 : Mem) : Config → Prop :=
  SegExit g N A SL φf φc nf nc st' evalArgsContPC m0

/-! The generic `SegEntry`/`SegExit` pair does not mention the argument list or
the produced values.  These indexed wrappers carry the minimum concrete ABI
facts used by the argument loop. -/

/-- A materialised stack array of 24-byte `Value` objects. -/
def ArgVecRepr (m : Mem) (N : NativeAddrs) (φc : Addr → Nat)
    (base : Nat) : List Value → Prop
  | [] => True
  | v :: vs =>
      ValueRepr m N φc base v ∧ ArgVecRepr m N φc (base + 24) vs

@[simp] theorem argVecRepr_nil (m : Mem) (N : NativeAddrs) (φc : Addr → Nat)
    (base : Nat) : ArgVecRepr m N φc base [] := trivial

theorem argVecRepr_cons (m : Mem) (N : NativeAddrs) (φc : Addr → Nat)
    (base : Nat) (v : Value) (vs : List Value)
    (hv : ValueRepr m N φc base v)
    (hvs : ArgVecRepr m N φc (base + 24) vs) :
    ArgVecRepr m N φc base (v :: vs) := ⟨hv, hvs⟩

/-- Every byte in an exact memory window is present. -/
def BytesPresent (m : Mem) (base width : Nat) : Prop :=
  ∀ j : Nat, j < width → ∃ b, m[base + j]? = some b

/-- A fully materialised 24-byte `Value` object. `ValueRepr` alone pins
semantic fields but deliberately leaves padding bytes unconstrained. -/
def ValueBytes (m : Mem) (base : Nat) : Prop := BytesPresent m base 24

/-- Every byte in the exact `24 * |vs|` argument-vector window is present. -/
def ArgVecBytes (m : Mem) (base : Nat) (vs : List Value) : Prop :=
  BytesPresent m base (24 * vs.length)

@[simp] theorem argVecBytes_nil (m : Mem) (base : Nat) :
    ArgVecBytes m base [] := by
  intro j hj
  simp at hj

/-- Loaded code image for the concrete argument-loop span. -/
structure EvalArgsSpanGround (m0 : Mem) : Prop where
  loaded : Vsa.Sim.Code.Eval_exprLoaded m0

/-- Static resources that the recursive argument body must retain.  These are
the facts erased by the former bare `SegEntry` motive. -/
structure EvalArgsSemanticGround
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (sp sret : BitVec 64) (m0 : Mem) : Prop where
  stack : StackOK SL sp (1088 + 1088)
  code : InterpCodeLoaded m0
  valueInt : Vsa.Sim.Code.Value_intLoaded m0
  nbs : NBSPins m0
  storeBodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  storeSurv : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
      ¬ (sp.toNat + 64 ≤ k ∧ k < sp.toNat + 88) → m0[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  spill : Scaffold.EntryImage callDispatchPC g m0

/-- Exact child resources for the current argument suffix.  These are the
facts needed to build the recursive `EvalEntry` after the staging `jal`. -/
structure EvalArgsHeadGround
    (A : Arena) (SL : StackLayout) (st : SpecSt) (d : Nat)
    (es : List Expr) (prefixLen : Nat) (sp argsBase : BitVec 64)
    (m : Mem) : Prop where
  head : ∀ e tail, es = e :: tail → ∃ aHead : BitVec 64,
    read64 m (argsBase.toNat + 8 * prefixLen) = some aHead.toNat ∧
    ExprRepr m aHead.toNat e ∧
    EvalGround m SL A sp (sp + 64#64) aHead.toNat e
  budget : ∀ e tail, es = e :: tail →
    StackOK SL sp
      (e.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  bodies : ∀ e tail, es = e :: tail →
    Expr.bodiesBound Vsa.While.perCallBudget e = true
  childSret : ValueBytes m (sp.toNat + 64)

/-- All currently generated native/closure helper images needed below call
dispatch.  `value_print` and newlib IO remain explicit contract frontiers: no
loaded predicates exist for them yet. -/
structure CallCodeGround (m0 : Mem) : Prop where
  nativeAssert : Vsa.Sim.Code.Native_assertLoaded m0
  nativePrint : Vsa.Sim.Code.Native_printLoaded m0
  nativePrintln : Vsa.Sim.Code.Native_printlnLoaded m0
  valueTruthy : Vsa.Sim.Code.Value_truthyLoaded m0
  valueNull : Vsa.Sim.Code.Value_nullLoaded m0
  envNew : Vsa.Sim.Code.Env_newLoaded m0
  envDefine : Vsa.Sim.Code.Env_defineLoaded m0
  strlen : Vsa.Sim.Code.StrlenLoaded m0
  memcpy : Vsa.Sim.Code.MemcpyLoaded m0

/-- Store representation survives native stack/HTIF effects. -/
structure CallStoreGround
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (m0 : Mem) : Prop where
  survive : ∀ m' : Mem,
    (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
      ¬ (tohostAddr ≤ k ∧ k < tohostAddr + 16) → m0[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store

/-- Allocator contract carried to closure dispatch.  The existential witnesses
are the concrete global-pointer and allocator bounds used by `env_new`. -/
structure CallAllocatorContracts (A : Arena) (SL : StackLayout) where
  gpv : BitVec 64
  headroom : Nat
  maxReq : Nat
  malloc : MallocContract A SL gpv headroom maxReq
  realloc : ReallocOps A SL gpv headroom maxReq malloc.AInv malloc.privFoot

/-- The allocator ledger and represented semantic store are tied to one
concrete machine state. -/
def CallHeapGround
    (A : Arena) (SL : StackLayout)
    (phiF phiC : Addr → Nat) (store : Store) (c : Config) : Prop :=
  ∃ K : CallAllocatorContracts A SL,
    c.σ.regs.get? Register.x3 = some K.gpv ∧
    ∃ exts, K.malloc.AInv c.σ exts ∧ HeapArena A exts ∧
      StoreHeapOwned c.σ.mem phiF phiC exts store

/-- Memory-only portion of the heap invariant.  Unlike allocator `AInv`, it
survives reflected register-only spans by definitional memory equality. -/
def CallStoreHeapOwned
    (A : Arena) (phiF phiC : Addr → Nat) (store : Store) (m : Mem) : Prop :=
  ∃ exts, HeapArena A exts ∧ StoreHeapOwned m phiF phiC exts store

/-- Store and argument-payload ownership retained by the parameter fold. -/
def CallFoldHeapOwned
    (A : Arena) (phiF phiC : Addr → Nat) (store : Store)
    (argBase : Nat) (vs : List Value) (m : Mem) : Prop :=
  ∃ exts, HeapArena A exts ∧ StoreHeapOwned m phiF phiC exts store ∧
    ValuesHeapOwned m exts argBase vs

/-- The allocator contract at the initial call-dispatch state. -/
def CallAllocatorGround
    (A : Arena) (SL : StackLayout)
    (phiF phiC : Addr → Nat) (st : SpecSt) (sp : BitVec 64)
    (vs : List Value) (c : Config) : Prop :=
  ∃ K : CallAllocatorContracts A SL,
    c.σ.regs.get? Register.x3 = some K.gpv ∧
    ∃ exts, K.malloc.AInv c.σ exts ∧ HeapArena A exts ∧
      StoreHeapOwned c.σ.mem phiF phiC exts st.store ∧
      ValuesHeapOwned c.σ.mem exts (sp.toNat + 240) vs

/-- Exact output callees required by `value_print`. -/
def CallNativeContracts (SL : StackLayout) : Prop :=
  Nonempty (CallIOContracts SL)

/-- Concrete result/spill geometry shared by native and closure routes. -/
structure CallAbiGround
    (g : (R : Register) → Option (RegisterType R))
    (SL : StackLayout) (sp sret : BitVec 64) (m : Mem) : Prop where
  sretBytes : ValueBytes m sret.toNat
  sretStack : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  sretAlign : sret.toNat % 8 = 0
  slotStack : SL.lo ≤ sp.toNat + 1016 ∧ sp.toNat + 1024 ≤ SL.hi
  slotAlign : (sp.toNat + 1016) % 8 = 0
  gp : ∃ w, g Register.x3 = some w
  s0 : ∃ w, g Register.x8 = some w
  s1 : ∃ w, g Register.x9 = some w
  s2 : ∃ w, g Register.x18 = some w
  s7 : ∃ w, g Register.x23 = some w
  codeStack : ∀ a : Nat, 0x80003164 ≤ a → a < 0x80003fe0 →
    ¬ (SL.lo ≤ a ∧ a < SL.hi)

/-- The machine interpreter's mutable depth field matches the semantic depth. -/
def CallDepthGround (d : Nat) (c : Config) : Prop :=
  ∃ interp : BitVec 64,
    c.σ.regs.get? Register.x18 = some interp ∧
    read32 c.σ.mem (interp.toNat + 8) = some d

/-- Loaded code image and the pre-dispatch caller spill image. -/
structure CallSpanGround
    (g : (R : Register) → Option (RegisterType R)) (m0 : Mem) : Prop where
  loaded : Vsa.Sim.Code.Eval_exprLoaded m0
  spill : Scaffold.EntryImage callDispatchPC g m0
  callees : CallCodeGround m0

/-- The concrete control point for a recursive argument suffix.  The fresh
empty-prefix case still visits the initial `blez`; a nonempty prefix is already
inside the do-while loop, and its empty suffix has fallen through to dispatch. -/
def evalArgsCursorPC (esPrefix es : List Expr) : Nat :=
  if esPrefix = [] then evalArgsEntryPC es
  else if es = [] then evalArgsContPC else evalArgsLoopPC

/-- Indexed argument-loop entry after `esPrefix` has produced `vsPrefix`.

Unlike the old fresh-only boundary, this is closed under the recursive tail:
`a6 = |vsPrefix|`, `a5 = |esPrefix ++ es|`, the call node still represents the
whole expression vector, and the already-produced value prefix remains in the
machine argument vector. -/
def EvalArgsPrefixEntryI
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (esPrefix es : List Expr) (vsPrefix : List Value)
    (dLeft aLeft : Nat) (m0 : Mem) : Config → Prop :=
  fun c =>
    esPrefix.length = vsPrefix.length ∧
    SegEntry g N A SL φf φc st d dLeft aLeft
      (evalArgsCursorPC esPrefix es) m0 c ∧
    EvalArgsSpanGround m0 ∧
    ∃ (sp cnode argsBase : BitVec 64) (f : Expr),
      c.σ.regs.get? Register.x2 = some sp ∧
      c.σ.regs.get? Register.x8 = some cnode ∧
      c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env)) ∧
      c.σ.regs.get? Register.x15 =
        some (BitVec.ofNat 64 (esPrefix ++ es).length) ∧
      c.σ.regs.get? Register.x16 = some (BitVec.ofNat 64 vsPrefix.length) ∧
      ValueBytes c.σ.mem (sp.toNat + 96) ∧
      read64 c.σ.mem (cnode.toNat + 16) = some argsBase.toNat ∧
      ExprArrayRepr c.σ.mem argsBase.toNat (esPrefix ++ es).length (esPrefix ++ es) ∧
      ExprRepr c.σ.mem cnode.toNat (.call f (esPrefix ++ es)) ∧
      ArgVecRepr c.σ.mem N φc (sp.toNat + 240) vsPrefix ∧
      ArgVecBytes c.σ.mem (sp.toNat + 240) vsPrefix ∧
      ∃ sret : BitVec 64,
        c.σ.regs.get? Register.x9 = some sret ∧
        EvalArgsSemanticGround g N A SL φf φc st sp sret m0 ∧
        (∃ lo hi, AstRegionSpec c.σ.mem SL A sret.toNat cnode.toNat
          (.call f (esPrefix ++ es)) lo hi) ∧
        EvalArgsHeadGround A SL st d es esPrefix.length sp argsBase c.σ.mem ∧
        StoreClosuresBounded st.store ∧
        ValuesClosuresBounded st.store.closures.size vsPrefix

/-- Fresh argument-loop entry.  This compatibility name is the empty-prefix
instance of `EvalArgsPrefixEntryI`. -/
abbrev EvalArgsEntryI
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (es : List Expr)
    (dLeft aLeft : Nat) (m0 : Mem) : Config → Prop :=
  EvalArgsPrefixEntryI g N A SL φf φc st d env [] es [] dLeft aLeft m0

theorem EvalArgsPrefixEntryI.semanticBounds
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {esPrefix es : List Expr} {vsPrefix : List Value}
    {dLeft aLeft : Nat} {m0 : Mem} {c : Config}
    (h : EvalArgsPrefixEntryI g N A SL φf φc st d env
      esPrefix es vsPrefix dLeft aLeft m0 c) :
    StoreClosuresBounded st.store ∧
      ValuesClosuresBounded st.store.closures.size vsPrefix := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _hregion, _hhead, hbounds⟩
  exact hbounds

/-- Exit from the argument loop with exactly `vs` in the caller's value array. -/
def EvalArgsExitI
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st' : SpecSt) (vs : List Value) (m0 : Mem) : Config → Prop :=
  fun c =>
    SegExit g N A SL φf φc nf nc st' evalArgsContPC m0 c ∧
    ∃ (sp : BitVec 64) (φc' : Addr → Nat),
      c.σ.regs.get? Register.x2 = some sp ∧
      PhiExtends φc φc' nc ∧
      ValueBytes c.σ.mem (sp.toNat + 96) ∧
      ArgVecRepr c.σ.mem N φc' (sp.toNat + 240) vs ∧
      ArgVecBytes c.σ.mem (sp.toNat + 240) vs ∧
      StoreClosuresBounded st'.store ∧
      ValuesClosuresBounded st'.store.closures.size vs

/-- Rebase an indexed argument exit from later store sizes to earlier ones.
The represented store and value vector already use maps valid on the larger
prefix, so `PhiExtends.mono` supplies the smaller caller boundary. -/
theorem evalArgsExitI_mono
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {nf nc nf' nc' : Nat} {st' : SpecSt} {vs : List Value} {m0 : Mem}
    {c : Config}
    (hnf : nf ≤ nf') (hnc : nc ≤ nc')
    (h : EvalArgsExitI g N A SL φf φc nf' nc' st' vs m0 c) :
    EvalArgsExitI g N A SL φf φc nf nc st' vs m0 c := by
  rcases h with ⟨hseg, sp, φc', hsp, hpc, hbytes, hvec, hvecBytes⟩
  have hseg' : SegExit g N A SL φf φc nf nc st' evalArgsContPC m0 c := by
    obtain ⟨φf'', φc'', hpf'', hpc'', hstore⟩ := hseg.store
    exact
      { good := hseg.good
        tick := hseg.tick
        pc := hseg.pc
        store := ⟨φf'', φc'', PhiExtends.mono hnf hpf'',
          PhiExtends.mono hnc hpc'', hstore⟩
        out := hseg.out
        frame := hseg.frame
        memFrame := hseg.memFrame
        stackWin := hseg.stackWin }
  exact ⟨hseg', sp, φc', hsp, PhiExtends.mono hnc hpc, hbytes, hvec, hvecBytes⟩

/-- Rebase an argument exit across maps extended by one recursive child. -/
theorem evalArgsExitI_rebase
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {φf φc φf' φc' : Addr → Nat} {nf nc : Nat}
    {st' : SpecSt} {vs : List Value} {m0 : Mem} {c : Config}
    (hpf : PhiExtends φf φf' nf) (hpc : PhiExtends φc φc' nc)
    (h : EvalArgsExitI g N A SL φf' φc' nf nc st' vs m0 c) :
    EvalArgsExitI g N A SL φf φc nf nc st' vs m0 c := by
  rcases h with ⟨hseg, sp, φcOut, hsp, hpcOut, hbytes, hvec, hvecBytes⟩
  obtain ⟨φfOut, φcStore, hpfOut, hpcStore, hstore⟩ := hseg.store
  have hseg' : SegExit g N A SL φf φc nf nc st' evalArgsContPC m0 c :=
    { good := hseg.good
      tick := hseg.tick
      pc := hseg.pc
      store := ⟨φfOut, φcStore, hpf.trans hpfOut, hpc.trans hpcStore, hstore⟩
      out := hseg.out
      frame := hseg.frame
      memFrame := hseg.memFrame
      stackWin := hseg.stackWin }
  exact ⟨hseg', sp, φcOut, hsp, hpc.trans hpcOut, hbytes, hvec, hvecBytes⟩

/-! ## `Call` entry/exit (the fval-dispatch `SegEntry`/`SegExit` at real PCs)

`CallEntry` = the machine at the `fv->kind` dispatch (`callDispatchPC`) with the
argument vector materialised and `fv` staged; `CallExit` at the join into the
epilogue (`callJoinPC`) with the return value in the CALL's sret. Filled from the
scaffold skeleton; the ABI details of `fv`/`vs`/result placement are per-case
fields of the eventual `closure`/native proofs. -/

/-- The `Call` dispatch-entry predicate (scaffold `SegEntry` at `callDispatchPC`). -/
abbrev CallEntryP
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem) : Config → Prop :=
  SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0

/-- The `Call` join-exit predicate (scaffold `SegExit` at `callJoinPC`). -/
abbrev CallExitP
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : SpecSt) (m0 : Mem) : Config → Prop :=
  SegExit g N A SL φf φc nf nc st' callJoinPC m0

/-- Concrete call-dispatch entry.  It ties the semantic callee and argument
vector to the three stack regions read by the binary. -/
def CallEntryI
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem) : Config → Prop :=
  fun c =>
    SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0 c ∧
    CallSpanGround g m0 ∧
    CallStoreGround N A SL φf φc st c.σ.mem ∧
    CallAllocatorGround A SL φf φc st sp vs c ∧
    CallNativeContracts SL ∧
    StackOK SL sp 4096 ∧
    CallAbiGround g SL sp sret c.σ.mem ∧
    CallDepthGround d c ∧
    c.σ.regs.get? Register.x2 = some sp ∧
    c.σ.regs.get? Register.x9 = some sret ∧
    c.σ.regs.get? Register.x15 = some (BitVec.ofNat 64 vs.length) ∧
    ValueRepr c.σ.mem N φc (sp.toNat + 96) fv ∧
    ValueBytes c.σ.mem (sp.toNat + 96) ∧
    ArgVecRepr c.σ.mem N φc (sp.toNat + 240) vs ∧
    ArgVecBytes c.σ.mem (sp.toNat + 240) vs ∧
    StoreClosuresBounded st.store ∧
    ValueClosuresBounded st.store.closures.size fv ∧
    ValuesClosuresBounded st.store.closures.size vs ∧
    -- The call boundary is after CRT/newlib initialization.
    ConsoleStream c.σ.mem

/-- The existing call-entry facts, named at the same configuration and maps. -/
structure CallEntryFacts
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem) (c : Config) : Prop where
  seg : SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0 c
  span : CallSpanGround g m0
  store : CallStoreGround N A SL φf φc st c.σ.mem
  allocator : CallAllocatorGround A SL φf φc st sp vs c
  nativeContracts : CallNativeContracts SL
  stack : StackOK SL sp 4096
  abi : CallAbiGround g SL sp sret c.σ.mem
  depth : CallDepthGround d c
  stackPointer : c.σ.regs.get? Register.x2 = some sp
  resultPointer : c.σ.regs.get? Register.x9 = some sret
  count : c.σ.regs.get? Register.x15 = some (BitVec.ofNat 64 vs.length)
  callee : ValueRepr c.σ.mem N φc (sp.toNat + 96) fv
  calleeBytes : ValueBytes c.σ.mem (sp.toNat + 96)
  args : ArgVecRepr c.σ.mem N φc (sp.toNat + 240) vs
  argsBytes : ArgVecBytes c.σ.mem (sp.toNat + 240) vs
  storeBounded : StoreClosuresBounded st.store
  valueBounded : ValueClosuresBounded st.store.closures.size fv
  valuesBounded : ValuesClosuresBounded st.store.closures.size vs
  console : ConsoleStream c.σ.mem

/-- Destructure the landed call-entry conjunction once. -/
theorem CallEntryI.facts
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {fv : Value} {vs : List Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem} {c : Config}
    (h : CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c) :
    CallEntryFacts g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c := by
  obtain ⟨seg, span, store, allocator, nativeContracts, stack, abi, depth,
    stackPointer, resultPointer, count, callee, calleeBytes, args, argsBytes,
    storeBounded, valueBounded, valuesBounded, console⟩ := h
  exact ⟨seg, span, store, allocator, nativeContracts, stack, abi, depth,
    stackPointer, resultPointer, count, callee, calleeBytes, args, argsBytes,
    storeBounded, valueBounded, valuesBounded, console⟩

#print axioms CallEntryI.facts

theorem CallEntryI.storeBounded
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {fv : Value} {vs : List Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem} {c : Config}
    (h : CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c) :
    StoreClosuresBounded st.store := h.facts.storeBounded

theorem CallEntryI.valueBounded
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {fv : Value} {vs : List Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem} {c : Config}
    (h : CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c) :
    ValueClosuresBounded st.store.closures.size fv :=
  h.facts.valueBounded

theorem CallEntryI.valuesBounded
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {fv : Value} {vs : List Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem} {c : Config}
    (h : CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c) :
    ValuesClosuresBounded st.store.closures.size vs :=
  h.facts.valuesBounded

theorem CallEntryI.console
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {fv : Value} {vs : List Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem} {c : Config}
    (h : CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c) :
    ConsoleStream c.σ.mem :=
  h.facts.console

theorem CallEntryI.spanGround
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {fv : Value} {vs : List Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem} {c : Config}
    (h : CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c) :
    CallSpanGround g m0 := h.facts.span

theorem CallEntryI.entryImage
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {fv : Value} {vs : List Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem} {c : Config}
    (h : CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c) :
    Scaffold.EntryImage callDispatchPC g m0 := h.spanGround.spill

theorem CallEntryI.calleeCode
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {fv : Value} {vs : List Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem} {c : Config}
    (h : CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c) :
    CallCodeGround m0 := h.spanGround.callees

theorem CallEntryI.allocator
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {fv : Value} {vs : List Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem} {c : Config}
    (h : CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c) :
    CallAllocatorGround A SL φf φc st sp vs c := h.facts.allocator

theorem CallEntryI.storeHeapOwned
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {fv : Value} {vs : List Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem} {c : Config}
    (h : CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c) :
    CallStoreHeapOwned A φf φc st.store c.σ.mem := by
  obtain ⟨K, _hgp, exts, _hinv, harena, howned, _hvalues⟩ := h.allocator
  exact ⟨exts, harena, howned⟩

theorem CallEntryI.valuesHeapOwned
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {fv : Value} {vs : List Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem} {c : Config}
    (h : CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c) :
    ∃ exts, HeapArena A exts ∧ StoreHeapOwned c.σ.mem φf φc exts st.store ∧
      ValuesHeapOwned c.σ.mem exts (sp.toNat + 240) vs := by
  obtain ⟨K, _hgp, exts, _hinv, harena, howned, hvalues⟩ := h.allocator
  exact ⟨exts, harena, howned, hvalues⟩

theorem CallEntryI.ioContracts
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {fv : Value} {vs : List Value}
    {dLeft aLeft : Nat} {sp sret : BitVec 64} {m0 : Mem} {c : Config}
    (h : CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c) :
    CallNativeContracts SL := h.facts.nativeContracts

/-- Concrete call result at the pre-epilogue join. -/
def CallExitI
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st' : SpecSt) (v : Value) (sret : BitVec 64)
    (m0 : Mem) : Config → Prop :=
  fun c =>
    SegExit g N A SL φf φc nf nc st' callJoinPC m0 c ∧
    ∃ φc' : Addr → Nat,
      PhiExtends φc φc' nc ∧ ValueRepr c.σ.mem N φc' sret.toNat v

/-! ## `evalArgsNil` — exact loaded `EvalArgs.nil` branch -/

/-- The real empty-argument terminator at `0x800031d8`: `bge x0,x15,+0x7c`.
The `taken` bit records the semantic branch choice, not an instruction bit. -/
def evalArgsNilTerm : TInstr :=
  ⟨0x800031d8#64, 0x06f05e63#32,
    0x63#8, 0x5e#8, 0xf0#8, 0x06#8,
    .br bop.BGE true, 0, 15, 0x007c#13, 0#21, 0#12⟩

/-- Exact indexed nil-argument span.  It executes the loaded branch at
`0x800031d8` and lands at the real call dispatch `0x80003254`. -/
theorem evalArgsNil
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (dLeft aLeft : Nat) (m0 : Mem)
    (_hArgs : EvalArgs st d env [] st []) :
    Triple
      (EvalArgsEntryI g N A SL φf φc st d env [] dLeft aLeft m0)
      (EvalArgsExitI g N A SL φf φc st.store.frames.size
        st.store.closures.size st [] m0) := by
  intro c hc
  rcases hc with ⟨_, hseg, hground, sp, cnode, argsBase, f, hsp, hx8, henv,
    hargc, hidx, hfvBytes, hargsBase, hargs, hcall, _, _, _sret, _hsret,
    _hsemantic, _hregion, _hhead, hcb, _hvs⟩
  obtain ⟨vmi, hmi⟩ := hseg.good.minstret
  have hcode : Vsa.Sim.Code.Eval_exprLoaded c.σ.mem := by
    rw [hseg.mem]
    exact hground.loaded
  obtain ⟨hb0, hb1, hb2, hb3⟩ :=
    Vsa.Sim.Code.eval_expr_at_800031d8 hcode
  have hpin : GHolds c.σ [(15, 0#64)] := by
    simpa [GHolds, gprGet] using hargc
  have hdec : DecodeFactT evalArgsNilTerm := by
    intro σ hmisa hpriv hsec
    exact Vsa.Sim.DecodeTable.decode_06f05e63 σ hmisa hpriv hsec
  obtain ⟨σ', i', hstep, hi', hgood', hmem', hout', hpc', _hmi', _hpins', hframe'⟩ :=
    term_step_bt evalArgsNilTerm c.σ c.tick c.steps vmi
      [(15, 0#64)] [15] hseg.good hseg.pc hmi hpin (by decide)
      (by simp [keysG]) hb0 hb1 hb2 hb3 hdec (by decide) (by rfl) hseg.tick
  let c' : Config := ⟨σ', i', c.steps + 1⟩
  have hsteps : Vsa.Machine.Steps c c' := Vsa.Machine.Steps.single hstep
  refine ⟨c', hsteps, ?_⟩
  constructor
  · refine
      { good := hgood'
        tick := hi'
        pc := ?_
        store := ?_
        out := ?_
        frame := ?_
        memFrame := ?_
        stackWin := ?_ }
    · simpa [evalArgsNilTerm, tgtPCT, tgtPC0, evalArgsContPC, callDispatchPC] using hpc'
    · refine ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, ?_⟩
      rw [hmem']
      exact hseg.store
    · exact outRepr_of_sailOutput_eq hout' hseg.out
    · intro R hR _
      exact (hframe' R (abiNoise_noiseRegs_call hR)).trans (hseg.frame R hR)
    · intro a haSL haA
      rw [hmem', hseg.mem]
    · intro k hk
      simp [stackScratchTop, evalArgsContPC] at hk
  · refine ⟨sp, φc, ?_, PhiExtends.refl _ _, ?_, argVecRepr_nil _ _ _ _, ?_⟩
    · exact (hframe' Register.x2 (by decide)).trans hsp
    · rw [hmem']
      exact hfvBytes
    · exact ⟨argVecBytes_nil _ _, hcb, by simp [ValuesClosuresBounded]⟩

/-- Empty semantic suffix at any loop cursor.  At the fresh cursor this is the
real `blez` branch.  After a nonempty prefix the loop has already fallen through
to `evalArgsContPC`, so the correct machine run is zero steps while preserving
the accumulated vector. -/
theorem evalArgsNilPrefix
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (esPrefix : List Expr) (vsPrefix : List Value)
    (hlen : esPrefix.length = vsPrefix.length)
    (dLeft aLeft : Nat) (m0 : Mem)
    (hArgs : EvalArgs st d env [] st []) :
    Triple
      (EvalArgsPrefixEntryI g N A SL φf φc st d env
        esPrefix [] vsPrefix dLeft aLeft m0)
      (EvalArgsExitI g N A SL φf φc st.store.frames.size
        st.store.closures.size st (vsPrefix ++ []) m0) := by
  cases hp : esPrefix with
  | nil =>
    cases hv : vsPrefix with
    | nil =>
      simpa [EvalArgsPrefixEntryI, evalArgsCursorPC] using
        (evalArgsNil g N A SL φf φc st d env dLeft aLeft m0 hArgs)
    | cons v vs => simp [hp, hv] at hlen
  | cons e es =>
    intro c hc
    rcases hc with ⟨_, hseg, _hground, sp, cnode, argsBase, f, hsp, _hx8,
      _henv, _hargc, _hidx, hfvBytes, _hargsBase, _hargs, _hcall,
      hprefix, hprefixBytes, _sret, _hsret, _hsemantic, _hregion, _hhead, hcb, hvs⟩
    have hseg' : SegEntry g N A SL φf φc st d dLeft aLeft evalArgsContPC m0 c := by
      simpa [evalArgsCursorPC, hp] using hseg
    have hexit : SegExit g N A SL φf φc st.store.frames.size
        st.store.closures.size st evalArgsContPC m0 c :=
      { good := hseg'.good
        tick := hseg'.tick
        pc := hseg'.pc
        store := ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, hseg'.store⟩
        out := hseg'.out
        frame := fun R hR _ => hseg'.frame R hR
        memFrame := fun a _ _ => by rw [hseg'.mem]
        stackWin := fun _ _ _ _ a _ _ _ => by rw [hseg'.mem] }
    refine ⟨c, Vsa.Machine.Steps.refl c, hexit, sp, φc, hsp,
      PhiExtends.refl _ _, hfvBytes, ?_, ?_⟩
    · simpa using hprefix
    · exact ⟨by simpa using hprefixBytes, hcb, by simpa using hvs⟩

/-! ## Per-constructor difficulty / plan for the `call` subsystem

Ordered easiest → hardest; each is a minor premise of the mutual recursor.

1. **`EvalArgs.nil`** — DONE here (`evalArgsNil`), UNCONDITIONAL. One loaded
   taken branch from `0x800031d8` to `evalArgsContPC`.

2. **`EvalE.fn`** (closure allocation, near-leaf) — EX_FN arm; one `env_new`-less
   allocation: `jal make_closure`/`allocClosure` writes a `ClosureData⟨env,name,
   params,body⟩` into the closures arena and returns a `.closure a`. Pattern =
   the leaf cases (`evalIntSim`) + a `StoreRepr`-extension over the closures
   array (the FIRST time φc is genuinely non-identity for an `EvalE` leaf). Needs
   a `make_closure`/`allocClosure` callee contract analogous to `env_new_spec`
   (fresh 32-ish-byte Closure record; `PhiExtends` on the closures array). No
   recursion. ~leaf-sized once the alloc contract exists.

3. **`Call.print` / `Call.println`** (native) — the `jalr a6` indirect native
   dispatch at `callNativePC`. Needs: (a) `fv->fn = native_{print,println}` addr
   from `ValueRepr (.native …)` (the `NativeAddrs` correspondence — already a
   `StoreRepr` ghost); (b) a `native_print`/`native_println` callee contract
   (`0x80002ed4`/`0x80002f7c`): appends `printArgs`/`+"\n"` to the console
   (`OutRepr` extension) and returns `value_null`. The output-append is the
   novel bit — reuse the HTIF/`OutRepr` machinery. `value_print`/`stringify`
   sub-contracts (`0x80002fc0`) are the real work (they route through
   `snprintf`/`strcpy`, already specced for `%lld`).

4. **`Call.assertOk`** (native) — `native_assert` (`0x80002df4`): `value_truthy`
   (already specced) on `args[0]`; truthy ⇒ `value_null`, no output. The falsy /
   arity-error paths are runtime errors (underivable). Simplest native (no
   console append), but shares the `jalr a6` + native-addr plumbing with (3).

5. **`EvalArgs.cons`** — the arg-loop body (`evalArgsLoopPC …`): one
   `motive_EvalE` IH on `args[i]` (reuse `armTail_rec`/`SubEvalReturn`, sret =
   `sp+64`) + a 24-byte copy into the stack Value-array slot
   (`sp+32+i*24+208`) + `i++` back-edge. This is a `Triple.loop` over the arg
   index (measure `argc - i`), the arg-array analog of the `block`-loop
   `execSeqLoop`. Threads the growing `vs` vector; needs an `ArgVecRepr` (the
   materialised Value-array ↔ `vs : List Value`).

6. **`EvalE.call`** — composes (1)/(5) + callee IH + (2)/(3)/(4): callee eval IH
   (`armTail_rec`, sret `sp+96`) ≫ `EvalArgs` loop (5) ≫ `Call` dispatch. The
   arm's blockA (jump-table slot 6 landing at `callArmPC`) + the fval-kind
   `beq`/`bne` dispatch (native/closure/error) + join at `callJoinPC` ≫ the
   shared `eval_expr` epilogue (`blockD_v`). Three sub-relation IHs
   (`motive_EvalE` for `f`, `motive_EvalArgs` for `args`, `motive_Call` for the
   call). This is the recursor minor premise for `EvalE.call`.

7. **`Call.closure`** (HARDEST — the crux) — `callClosurePC`: arity check
   (`argc = cd.arity`) + depth guard (`d < maxCallDepth`, the `blt a2,a4` at
   `0x800032b0`, `++call_depth`) + `env_new` call-frame
   (`allocFrame (some cd.env)`, reuse `env_new_spec`) + param-bind fold
   (`env_define` loop, reuse the `env_define` contract — the OPEN M3 residual
   noted in `execVarDeclSim`) + **the body `ExecSeq` at depth `d+1`** (the
   `exec_stmt` loop at `callBodyLoopPC`, reuse `execSeqLoop`/`armExec_rec` — the
   SAME machinery as `block`) + return (`.normal` ⇒ `value_null`; `.ret v` ⇒ copy
   24-byte body-sret into the CALL sret) + `--call_depth`. The `motive_ExecSeq`
   IH for the body drops straight in. The depth budget (`SegEntry.depth_budget`)
   is exactly the scaffold field that bites here. Blocked on the `env_define`
   composed contract (independent M3-scale effort) and the recursive
   `motive_ExecSeq` body IH (statement family — already largely built).
-/

#print axioms evalArgsNil

end Vsa.Sim
