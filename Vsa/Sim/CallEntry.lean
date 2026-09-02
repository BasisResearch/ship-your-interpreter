import Vsa.Sim.InductionScaffold

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
  (zero-step identity `Triple` at the shared continuation PC, exactly like
  `execSeqNil`).

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

/-! ## Decoded PC constants for the `EX_CALL` arm -/

/-- Jump-table slot 6 target: the `EX_CALL` arm entry in `eval_expr`. -/
def callArmPC : Nat := 0x800031b0
/-- Link address after the callee `jal eval_expr`. -/
def callCalleeRetPC : Nat := 0x800031c0
/-- The argument-evaluation loop head (about to evaluate `args[i]`). -/
def evalArgsLoopPC : Nat := 0x800031dc
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

/-! ## `evalArgsNil` — the `EvalArgs.nil` case (FIRST GREEN PIECE)

The empty argument list produces `vs = []` with the store and output unchanged.
On the machine this is the `argc ≤ 0` branch (`blez a5, 0x80003254` at
`0x800031d8`): control has already fallen through the loop to the dispatch
continuation, so — modelled at the shared loop-head/continuation PC — the entry
predicate for `ss = []` literally IS the exit predicate for the unchanged state.
Hence `evalArgsNil` is the zero-step identity `Triple`, exactly like
`execSeqNil`. The `EvalArgs.nil` derivation is threaded (unused, as the spec
constructor has no premises), matching the `motive_EvalArgs` minor-premise shape.

NOTE the shared-PC modelling: we state it at `evalArgsContPC` (the loop's
continuation and the dispatch entry) — the `argc ≤ 0` branch has already landed
there, so entry = exit is honest. The `cons` case will thread the arg-loop head
`evalArgsLoopPC` and land here after the last iteration. -/

/-- The `EvalArgs.nil` minor premise: an empty argument list is a no-op that
leaves the spec state unchanged (`vs = []`, same store/output). Zero-step
identity `Triple` at the dispatch continuation PC. UNCONDITIONAL, axiom-clean. -/
theorem evalArgsNil
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (dLeft aLeft : Nat) (m0 : Mem)
    (_hArgs : EvalArgs st d env [] st []) :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft evalArgsContPC m0)
      (EvalArgsExit g N A SL φf φc st.store.frames.size st.store.closures.size st m0) := by
  intro c hc
  refine ⟨c, .refl c, ?_⟩
  exact
    { good := hc.good
      tick := hc.tick
      pc := hc.pc
      store := ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, hc.store⟩
      out := hc.out
      -- wave-45 guarded frame: the full `SegEntry.frame` supplies every
      -- register, so the `joinRestored` guard is ignored.
      frame := fun R hR _ => hc.frame R hR
      memFrame := fun a _ _ => by rw [hc.mem]
      -- zero-step identity: the memory IS the entry `m0`, so the stack window
      -- survives trivially at ANY tabled exit PC.
      stackWin := fun _ _ _ _ a _ _ _ => by rw [hc.mem] }

/-! ## Per-constructor difficulty / plan for the `call` subsystem

Ordered easiest → hardest; each is a minor premise of the mutual recursor.

1. **`EvalArgs.nil`** — DONE here (`evalArgsNil`), UNCONDITIONAL. Zero-step
   identity at `evalArgsContPC`.

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

end Vsa.Sim
