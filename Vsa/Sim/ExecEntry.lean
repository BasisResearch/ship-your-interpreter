import Vsa.RuntimeRepr
import Vsa.MemRepr
import Vsa.Alloc
import Vsa.Triple
import Vsa.Sim.GoodState
import Vsa.Sim.Regions
import Vsa.Sim.Code.Exec_stmt
import Vsa.Sim.InterpEntry

/-!
# Layer 4 — the `ExecEntry`/`ExecExit` machine-side predicates for `exec_stmt`

Opens the **statement** family of the Layer-4 simulation induction, the analog
of `Vsa/Sim/InterpEntry.lean` for the *expression* side. Where the expression
side proves a `Triple (EvalEntry …) (EvalExit … v)` per `EvalE` constructor, the
statement side proves a `Triple (ExecEntry …) (ExecExit … status)` per `ExecS`
constructor. The compiled `exec_stmt` is a SEPARATE function from `eval_expr`, so
it needs its own entry/exit infrastructure (its own prologue, dispatch and
epilogue).

## The `exec_stmt` ABI (decoded from `while-riscv-htif.elf`, entry `0x80003fe0`)

```
80003fe0:  addi sp,sp,-176        -- 176-byte stack frame (much smaller than eval_expr's 1088)
80003fe4:  sd   s0,160(sp)        -- spill callee-saved s0
80003fe8:  sd   s1,152(sp)        --   … s1
80003fec:  sd   s2,144(sp)        --   … s2
80003ff0:  sd   s3,136(sp)        --   … s3
80003ff4:  sd   ra,168(sp)        --   … ra
80003ff8:  mv   s0,a1             -- s0 = a1 = Stmt*   (ABI arg 1)
80003ffc:  mv   s1,a0             -- s1 = a0 = interp* (ABI arg 0)
80004000:  mv   s3,a2             -- s3 = a2 = env      (ABI arg 2)
80004004:  mv   s2,a3             -- s2 = a3 = retslot  (ABI arg 3, the *Value out for `ret`)
80004008:  li   a6,8             -- kind bound (max Stmt tag)
8000400c:  auipc a4,0x16          -- a4 := jump-table base …
80004010:  addi  a4,a4,-84       -- … = 0x80019fb8   (CSWTCH.18+0x90)
80004014:  lw    a5,0(s0)         -- a5 = stmt->kind
80004018:  bltu  a6,a5,0x80004090 -- kind > 8 → default (return normal=0)
8000401c:  lwu   a5,0(s0)         -- a5 = kind (zero-extended)
80004020:  slli  a5,a5,0x2        -- a5 = 4*kind
80004024:  add   a5,a5,a4         -- a5 = table + 4*kind
80004028:  lw    a5,0(a5)         -- a5 = (int32) table[kind]     (signed slot)
8000402c:  add   a5,a5,a4         -- a5 = table + slot  = arm PC
80004030:  jr    a5               -- dispatch
```

**Convention**: `exec_stmt(interp*, Stmt*, Env, Value* retslot) → int status`.
* `a0 (x10)` = `interp*`   (the interpreter context; `s1 := a0`).
* `a1 (x11)` = `Stmt*`      (the statement node, with `StmtRepr`; `s0 := a1`).
* `a2 (x12)` = `Env` machine address (`φf` of the spec `env`; `s3 := a2`).
* `a3 (x13)` = `Value* retslot` — where a `ret v` stores its value (`s2 := a3`).
* `ra (x1)`  = return address.
* **return value** `a0 (x10)` = the STATUS CODE (see `StatusCode` below), NOT a
  pointer. This is the crucial difference from `eval_expr` (which returns the
  sret pointer). A `ret v` writes `*retslot := v` and returns status 3.

## The statement-kind dispatch (a jump table on the `Stmt` tag)

`exec_stmt` dispatches on `stmt->kind` (`StmtKind` in `ast.h`) through a
`.rodata` jump table at `0x80019fb8` (`CSWTCH.18+0x90`), 9 signed-32 slots
(kinds 0..8). The bound check `bltu 8, kind` sends any tag > 8 to the default
`return 0`. Arm PC = `table + (int32) table[kind]`. Decoded slots (rodata bytes
`b8a1feff 20a1feff d4a1feff 30a2feff 84a0feff 7ca2feff 68a1feff e0a0feff 00a1feff`):

| kind | `StmtKind` / `Stmt` ctor | arm PC        | maps to `ExecS` ctor(s)               |
|------|--------------------------|---------------|----------------------------------------|
| 0    | `expr`                   | `0x80004170`  | `ExecS.expr`                           |
| 1    | `varDecl`                | `0x800040d8`  | `ExecS.varInit` / `varNull`            |
| 2    | `block`                  | `0x8000418c`  | `ExecS.block`                          |
| 3    | `ifStmt`                 | `0x800041e8`  | `ExecS.ifTrue` / `ifFalse` / `ifNone`  |
| 4    | `whileStmt`              | `0x8000403c`  | `ExecS.whileFalse`/`Break`/`Ret`/`Loop`|
| 5    | `forStmt`                | `0x80004234`  | `ExecS.forStart`                       |
| 6    | `ret`                    | `0x80004120`  | `ExecS.ret` / `retNull`                |
| 7    | `brk`                    | `0x80004098`  | `ExecS.brk`                            |
| 8    | `cont`                   | `0x800040b8`  | `ExecS.cont`                           |

## The status return encoding (register `a0` at each `ret`)

The spec `Status` (`normal | brk | cont | ret v`) maps to the C `int` status:

| `Status`   | `a0` value | site producing it                                       |
|------------|-----------|----------------------------------------------------------|
| `normal`   | `0`       | `0x80004090: li a0,0` → shared epilogue `0x8000409c`     |
| `brk`      | `1`       | `0x80004098: li a0,1` → falls into shared epilogue       |
| `cont`     | `2`       | `0x800040cc: li a0,2` (own epilogue copy `0x800040b8`)   |
| `ret v`    | `3`       | `0x80004164: li a0,3` (own epilogue copy `0x80004150`);  |
|            |           | before that `*retslot := v` (three `sd` at `s2+{0,8,16}`)|

The three epilogues all restore `ra`/`s0`/`s1`/`s2`/`s3` from `[sp+{168,160,
152,144,136}]`, `addi sp,sp,176`, `ret` — differing only in the `li a0,N` they
set. The `brk` arm (`0x80004098`) is the shortest: `li a0,1; <epilogue>`.

## The arm bodies (recursion structure — which callees each arm reaches)

* **`expr` (0x80004170)**: `ld a2,8(s0)` (`stmt->expr`), `addi a0,sp,16`
  (sret buffer), `mv a1,s1` (interp), `jal eval_expr`; `li a0,0`; `j 0x8000409c`.
  → one `EvalIH` sub-call, then `normal`.
* **`varDecl` (0x800040d8)**: if `stmt->init` present: `jal eval_expr` then
  `jal env_define`; else `jal value_null` then `env_define`. → `normal`.
* **`ret` (0x80004120)**: if `stmt->expr` present: `jal eval_expr` into a local,
  copy the 24 bytes to `*s2` (retslot), `li a0,3`, own epilogue; else
  `jal value_null` then same. → `ret v`.
* **`block` (0x8000418c)**: `jal env_new` (allocate inner frame), loop over the
  statement array calling `exec_stmt` recursively (`0x800041c4`), abort on
  non-normal. → `ExecSeq` in the inner frame.
* **`ifStmt` (0x800041e8)**: eval cond, `jal value_truthy`; if true re-dispatch
  the `then` branch by falling back into the dispatch at `0x80004014` with
  `s0 := stmt->thn`; else `s0 := stmt->els` (or return normal if none).
* **`whileStmt` (0x8000403c)**: eval cond, `value_truthy`, recurse body, loop.
* **`forStmt` (0x80004234)**: `jal env_new`, run init, then the cond/body/step
  loop.
* **`brk` (0x80004098)** / **`cont` (0x800040b8)**: no callee, just set the
  status and return.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-- Machine entry PC of `exec_stmt`. -/
def execStmtEntry : Nat := 0x80003fe0

/-- End of the `exec_stmt` text region (exclusive), from the symbol table
(`exec_stmt` at `0x80003fe0`, size `808 = 0x328`). -/
def execStmtEnd : Nat := 0x80004308

/-- The statement-kind jump-table base (`0x80019fb8`, `CSWTCH.18+0x90`). Distinct
from the expression-side `jumpTableBase` (`0x80019f58`). -/
def stmtJumpTableBase : Nat := 0x80019fb8

/-! ## `StatusCode` — the spec `Status` ↔ machine `a0` return-code correspondence

`exec_stmt` returns a small `int` in `a0` encoding the abrupt-completion status.
The `ret v` case additionally writes `v` into the caller-provided `retslot`
(`a3`), so its correspondence is stated in `ExecExit` (the `retslot` buffer holds
`ValueRepr v`), not here. -/
def StatusCode : Status → BitVec 64
  | .normal => 0#64
  | .brk    => 1#64
  | .cont   => 2#64
  | .ret _  => 3#64

@[simp] theorem statusCode_normal : StatusCode .normal = 0#64 := rfl
@[simp] theorem statusCode_brk : StatusCode .brk = 1#64 := rfl
@[simp] theorem statusCode_cont : StatusCode .cont = 2#64 := rfl
@[simp] theorem statusCode_ret (v : Value) : StatusCode (.ret v) = 3#64 := rfl

/-! ## Per-kind arm entry PCs (decoded from the jump table, see the module doc). -/
def execArmExpr    : BitVec 64 := 0x80004170#64
def execArmVarDecl : BitVec 64 := 0x800040d8#64
def execArmBlock   : BitVec 64 := 0x8000418c#64
def execArmIf      : BitVec 64 := 0x800041e8#64
def execArmWhile   : BitVec 64 := 0x8000403c#64
def execArmFor     : BitVec 64 := 0x80004234#64
def execArmRet     : BitVec 64 := 0x80004120#64
def execArmBrk     : BitVec 64 := 0x80004098#64
def execArmCont    : BitVec 64 := 0x800040b8#64

/-! ## The statement-kind jump-table slot pin

Mirrors the expression-side `IntSlotPinned`/`NullSlotPinned`. The dispatch reads
the four bytes of the `kind`-th slot (`lw a5,0(table + 4*kind)`), a `.rodata`
word NOT part of `Exec_stmtLoaded`. `StmtSlotPinned k armPC m` pins the four
bytes of slot `k` and asserts `stmtJumpTableBase + (Int32)slot = armPC`. -/
structure StmtSlotPinned (k : Nat) (armPC : BitVec 64) (m : Mem) : Prop where
  b0 : ∃ b0 b1 b2 b3 : BitVec 8,
    m[(stmtJumpTableBase + 4 * k + 0 : Nat)]? = some b0 ∧
    m[(stmtJumpTableBase + 4 * k + 1 : Nat)]? = some b1 ∧
    m[(stmtJumpTableBase + 4 * k + 2 : Nat)]? = some b2 ∧
    m[(stmtJumpTableBase + 4 * k + 3 : Nat)]? = some b3 ∧
    (BitVec.ofNat 64 stmtJumpTableBase +
      sign_extend (m := 64) (((b3.append b2).append b1).append b0)) = armPC

/-! ## `ExecEntry` — the machine precondition at `exec_stmt`'s entry PC

Mirrors `EvalEntry` (`InterpEntry.lean`), adapted for statements:
* the result is a `Status`, not a `Value` — computed in `ExecExit`;
* the sret buffer of `eval_expr` is replaced by the `retslot` (`a3`, only
  written on the `ret` arm);
* carries `StoreRepr`/`OutRepr` at entry (a statement can mutate the store via
  `varDecl`/`assign`/`block`, and grow the output via `print`, so both are
  threaded and re-established at exit with EXTENDED φ-maps);
* the kind dispatch uses `stmtJumpTableBase` and a `StmtSlotPinned` slot.

Parameters (ghosts, ∀-bound in the simulation lemma):
* `g` — blanket callee-preserved register ghost frame;
* `N`/`A`/`SL`/`φf`/`φc` — as on the expression side;
* `st` — spec pre-state; `d` — call depth; `env` — spec scope `Addr`; `s` — the
  `Stmt` being executed;
* `sp`/`r` — entry sp / return address; `aInterp` — `interp*` (`a0`); `aStmt` —
  `Stmt` node address (`a1`); `aEnv` — scope machine address (`a2`); `aRet` —
  the `retslot` machine address (`a3`);
* `m0` — pinned pre-memory. -/
structure ExecEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : St) (d : Nat) (env : Addr) (s : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop where
  /-- Pinned control state. -/
  good : GoodState c.σ
  /-- Tick parity invariant. -/
  tick : c.tick < 2
  /-- PC at `exec_stmt`'s entry. -/
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 execStmtEntry)
  /-- ABI arg 0: `interp*`. -/
  a0 : c.σ.regs.get? Register.x10 = some aInterp
  /-- ABI arg 1: the `Stmt` node address. -/
  a1 : c.σ.regs.get? Register.x11 = some aStmt
  /-- ABI arg 2: the scope machine address. -/
  a2 : c.σ.regs.get? Register.x12 = some aEnv
  /-- ABI arg 3: the `retslot` (`*Value` out for `ret`). -/
  a3 : c.σ.regs.get? Register.x13 = some aRet
  /-- Return address. -/
  ra : c.σ.regs.get? Register.x1 = some r
  /-- Return address 4-aligned (for the epilogue `ret`). -/
  ra_align : r.toNat % 4 = 0
  /-- Entry stack pointer. -/
  spReg : c.σ.regs.get? Register.x2 = some sp
  /-- `sp` is a good C stack pointer with 176 + callee headroom. -/
  stackOK : StackOK SL sp (176 + 1088)
  /-- `minstret` present. -/
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  /-- Machine memory is the pinned `m0`. -/
  mem : c.σ.mem = m0
  /-- `exec_stmt` loaded. -/
  code : Exec_stmtLoaded c.σ.mem
  /-- The `Stmt` node at `aStmt` represents `s`. Its `read32 aStmt = kind`. -/
  stmt : StmtRepr c.σ.mem aStmt.toNat s
  /-- The whole spec store is represented. -/
  store : StoreRepr c.σ.mem N A φf φc st.store
  /-- **`StoreRepr` survives any memory change confined to the stack window
  `[SL.lo, sp)`.** The represented frames/closures and their strings live in the
  arena/AST regions, disjoint from the C-stack scribble; so the prologue spills
  (all inside `[SL.lo, sp)`) leave the store re-representable. (Mirror of
  `EvalEntry.store_survives`, minus the sret buffer — the brk/cont/dispatch path
  writes only the stack window.) -/
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  /-- Console output correspondence. -/
  out : OutRepr c.σ st
  /-- The blanket ghost frame. -/
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R
  /-- The `exec_stmt` code region is disjoint from the stack scribble
  `[SL.lo, sp)`. -/
  code_stack_disjoint : sp.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo
  /-- The stack region is in RAM and above the HTIF window. -/
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  /-- **The `Stmt` node is disjoint from the stack region.** The dispatch reads
  `read32 aStmt` (the kind, `lw`/`lwu a5,0(s0)`); its bytes survive the prologue
  spills because the AST lives outside `[SL.lo, sp)`. -/
  stmt_stack_disjoint : aStmt.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aStmt.toNat
  /-- **The `Stmt` node is an 8-aligned 16-byte slot in RAM above HTIF.** The
  dispatch's `lw a5,0(s0)`/`lwu a5,0(s0)` (kind, 4-aligned) need these. -/
  stmt_align : aStmt.toNat % 8 = 0
  stmt_ram : 0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 16 ≤ 0x100000000
  stmt_win : tohostAddr + 16 ≤ aStmt.toNat
  /-- The four callee-saved registers spilled by the prologue (`s0`(x8),
  `s1`(x9), `s2`(x18), `s3`(x19)) are defined at entry. -/
  spill_defined : (∃ v, c.σ.regs.get? Register.x8 = some v) ∧
    (∃ v, c.σ.regs.get? Register.x9 = some v) ∧
    (∃ v, c.σ.regs.get? Register.x18 = some v) ∧
    (∃ v, c.σ.regs.get? Register.x19 = some v)

/-! ## `ExecExit` — the machine postcondition at `exec_stmt`'s return PC

The status code is in `a0`; `sp`/callee-saved restored; store and output
re-represented for the spec post-state `st'` with extended φ-maps; memory outside
the arena/stack window framed to `m0`. On the `ret v` arm the `retslot` buffer at
`aRet` additionally holds `ValueRepr v` (stated as a disjunct keyed on
`status`). -/
structure ExecExit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)          -- the ENTRY maps
    (st' : St) (status : Status)
    (sp r aRet : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop where
  /-- Control state re-established. -/
  good : GoodState c.σ
  /-- Tick parity still `< 2`. -/
  tick : c.tick < 2
  /-- PC at the return target (bit-0-cleared `r`, the `ret` semantics). -/
  pc : c.σ.regs.get? Register.PC =
    some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1)
  /-- Result register: the status code. -/
  a0 : c.σ.regs.get? Register.x10 = some (StatusCode status)
  /-- Return address preserved. -/
  ra : c.σ.regs.get? Register.x1 = some r
  /-- `sp` restored to entry. -/
  spReg : c.σ.regs.get? Register.x2 = some sp
  /-- `minstret` present. -/
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  /-- **The store is re-represented** for `st'.store` with extended maps. -/
  store : ∃ (φf' φc' : Addr → Nat),
    PhiExtends φf φf' st'.store.frames.size ∧
    PhiExtends φc φc' st'.store.closures.size ∧
    StoreRepr c.σ.mem N A φf' φc' st'.store
  /-- Console output correspondence for `st'`. -/
  out : OutRepr c.σ st'
  /-- On the `ret v` arm the `retslot` holds `ValueRepr v` (extended `φc`). Other
  statuses leave `retslot` unconstrained. -/
  retval : ∀ v, status = .ret v →
    ∃ φc', PhiExtends φc φc' st'.store.closures.size ∧
      ValueRepr c.σ.mem N φc' aRet.toNat v
  /-- The blanket ghost frame: every callee-preserved register restored to `g R`. -/
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R
  /-- Memory outside the arena and the stack window `[SL.lo, sp)` is unchanged
  from `m0`, except the `retslot` buffer `[aRet, aRet+24)` (written only on
  `ret`). -/
  memFrame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
    ¬ (A.lo ≤ a ∧ a < A.hi) →
    (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ c.σ.mem[a]? = m0[a]?

end Vsa.Sim
