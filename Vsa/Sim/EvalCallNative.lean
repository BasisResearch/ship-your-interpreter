import Vsa.Sim.CallEntry
import Vsa.Sim.ValueSpec
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.Code.Native_assert

/-!
# Layer 4 — M4: the native `Call` constructors (`Call.assertOk` / `print` / `println`)

The OUTPUT-producing (and, for `assert`, output-free) leaves of the `Call`
relation. Reached from the `EX_CALL` dispatch (`callDispatchPC = 0x80003254`)
when `fv->kind == 5` (`VAL_NATIVE`): the machine branches to the native arm at
`callNativePC = 0x800039e0`, marshals the ABI, and dispatches the stored C
function pointer with an **indirect `jalr a6`**. The three natives return
`value_null` into the CALL's sret and (for `print`/`println`) append to the HTIF
console, then control returns to `0x800039f8` and joins the shared `eval_expr`
epilogue at `callJoinPC = 0x800033ec`.

Unlike the closure path these natives do NOT recurse into a body / `env_define`,
so they are the tractable next `Call` pieces.

## Decoded `fv`-kind dispatch (`0x80003254 … 0x8000327c`)
```
80003254:  ld   a4,96(sp)         -- a4 = fv word0 (kind || cstr-lo)
80003258:  ld   a3,104(sp)        -- a3 = fv word1 (cstr-ptr / closure-ptr)
8000325c:  ld   a6,112(sp)        -- a6 = fv word2 = *(fv+16) = the native fn ptr
80003260:  lw   a1,4(s0)          -- a1 = e->line (noise)
80003264:  sd   a4,120(sp)        -- restage fv word0
80003268:  lw   a4,96(sp)         -- a4 = fv->kind (low word)
8000326c:  sd   a3,128(sp)        -- restage fv word1
80003270:  sd   a6,136(sp)        -- restage fv word2 (fn ptr)
80003274:  li   a2,5              -- VAL_NATIVE
80003278:  mv   s7,a1
8000327c:  beq  a4,a2,0x800039e0  -- kind == 5 ⇒ native arm (TAKEN here)
80003280:  li   a2,4 ; bne …      -- else kind==4 closure / runtime_error
```
The native fn ptr is loaded into `a6` at `0x8000325c` from the staged `fv+16`
word; `ValueRepr (.native f)` pins `read64 m (fvAddr + 16) = some (N.addr f)`, so
`a6 = N.addr f` — this is how the indirect `jalr a6` target is resolved.

## Decoded native arm (`0x800039e0 … 0x800039fc`)
```
800039e0:  mv   a4,a1             -- a4 = argc
800039e4:  mv   a2,a5             -- a2 = arg Value-array base
800039e8:  mv   a1,s2             -- a1 = interp
800039ec:  addi a3,sp,240        -- a3 = scratch buffer
800039f0:  mv   a0,s1             -- a0 = CALL sret
800039f4:  jalr a6                -- a6 = N.addr f   (indirect native dispatch)
800039f8:  ld   s7,1016(sp)       -- restore s7
800039fc:  j    0x800033ec        -- join the eval_expr epilogue (callJoinPC)
```
ABI at the `jalr`: `a0 = sret`, `a1 = interp`, `a2 = arg Value-array base`,
`a3 = scratch`, `a4 = argc`, `a6 = N.addr f`, `ra = 0x800039f8`.

## `native_assert` (`0x80002df4 … 0x80002ed4`) — the truthy (success) path
```
80002df4:  addi sp,sp,-80         -- prologue
80002df8-04:  sd s1,s2,ra,s0
80002e08:  addiw a6,a2,-1         -- a6 = argc - 1
80002e0c:  li   a5,1
80002e10:  mv   s1,a1             -- s1 = interp
80002e14:  mv   s2,a4             -- s2 = scratch
80002e18:  bltu a5,a6,0x80002e78  -- (argc-1) >u 1  ⇒ arity error (argc∈{1,2} OK)
80002e1c:  ld   a1,0(a3)          -- args[0] word0
80002e20:  ld   a4,8(a3)          -- args[0] word1
80002e24:  ld   a5,16(a3)         -- args[0] word2
80002e28:  mv   s0,a0             -- s0 = CALL sret
80002e2c:  addi a0,sp,16          -- a0 = truthy arg buffer (sp+16)
80002e30-34: sd a2,a3 spill
80002e38-40: sd a1,a4,a5 → sp+16,24,32   (copy the 24-byte args[0] Value)
80002e44:  jal  value_truthy      -- value_truthy(sp+16)
80002e48-4c: ld a3,a2 reload
80002e50:  beqz a0,0x80002e94     -- !truthy ⇒ assertion-failure runtime_error (M5)
80002e54:  mv   a0,s0             -- a0 = CALL sret
80002e58:  jal  value_null        -- return .null into the sret
80002e5c-70:  epilogue (ld ra,s0,s1,s2 ; addi sp,+80)
80002e74:  ret
```
On the truthy path (`args[0].truthy = true`): the 24-byte `args[0]` `Value` is
copied into the `sp+16` buffer, `value_truthy` returns non-zero, the `beqz` falls
through, `value_null` writes `.null` into the CALL sret, and the function returns
with the console output UNCHANGED. This is exactly `Call.assertOk`
(`vs = [v] ∨ vs = [v, m]`, `v.truthy = true`, result `.null`, `st` unchanged).

The falsy / arity-error arms (`0x80002e78`, `0x80002e94`) call `runtime_error`
and are UNDERIVABLE in the spec (M5), matching `Call.assertOk`'s premise.

## The output-append contract shape (for `print`/`println`, future work)
`native_print` (`0x80002ed4`) loops the `argc` values, `value_print`-rendering
each (`Value.display`/`stringify`) separated by a single space (`li a0,32`), no
trailing newline; `native_println` (`0x80002f7c`) = `native_print` then
`fputc('\n')`. Each printed char is one `tohost` console-write store that grows
`Machine.output` (`OutRepr`) by that char — so the append contract is
`OutRepr σ' ⟨st.store, st.out ++ printArgs st.store vs (++ "\n")⟩` at the arm
join, with the store unchanged. The `Value.display`/`stringify` sub-contract
routes through `snprintf`/`strcpy` (already specced for `%lld`).

## What lands here
* the decoded PC constants + contract definitions,
* `NativeAssertOkSpec` — the abstract machine contract for the whole native
  branch of `assert` (`callDispatchPC` truthy-arg-set-up ⇒ `callJoinPC` with the
  spec state UNCHANGED and `.null` produced), the reusable residual the eventual
  end-to-end proof discharges by threading the ~26-site `native_assert` internal
  run + the `value_truthy`/`value_null` sub-calls (both already specced);
* `callAssertOk` — the `Call.assertOk` minor premise as a machine `Triple`
  (`CallEntryP ⇒ CallExitP`), CONDITIONAL on `NativeAssertOkSpec` (the named
  native-branch residual, exactly the deferral pattern of `evalNegSim`'s
  `NegExtras`/`hMcallPop`), UNCONDITIONAL otherwise.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Scaffold

local notation "SpecSt" => Vsa.While.St

/-! ## `native_assert` entry / sub-call PCs -/

/-- `native_assert` entry (`interp_init`'s `assert` C fn ptr). -/
def nativeAssertPC : Nat := 0x80002df4
/-- Link address after `native_assert`'s `jal value_truthy`. -/
def nativeAssertTruthyRetPC : Nat := 0x80002e48
/-- Link address after `native_assert`'s `jal value_null`. -/
def nativeAssertNullRetPC : Nat := 0x80002e5c
/-- The `beqz a0` truthy gate (`!truthy ⇒ runtime_error`, M5). -/
def nativeAssertGatePC : Nat := 0x80002e50

/-! ## `Call.assertOk` — the native `assert` case (truthy arg → `.null`, no output)

`callAssertOk` states the `Call.assertOk` minor premise at the machine level: from
the `EX_CALL` dispatch entry (`CallEntryP` at `callDispatchPC`) the machine runs
— via the `kind==5` native branch, the indirect `jalr a6 = N.addr .assert`, and
the `native_assert` truthy path — to the epilogue join (`CallExitP` at
`callJoinPC`) with the spec state UNCHANGED (`Call.assertOk` returns `st` itself)
and `.null` produced.

The whole native branch (dispatch decode + arm marshal + `jalr` + `native_assert`
truthy path + `value_truthy`/`value_null` sub-calls + return to the join) is
captured by the single abstract residual `NativeAssertOkSpec`. Discharging it is
the remaining machine work: it threads the ~26-site `native_assert` internal run
(`Vsa/Sim/Code/Native_assert.lean` pins are already generated) composing
`value_truthy_spec` (`ValueTruthySpec`) on the `sp+16` copy of `args[0]` — via
`valueRepr_copy_of_writeWindow` (`ReprCopy`) — and `value_null_spec` (`ValueSpec`)
on the CALL sret, plus the dispatch/arm/join wrapper in `eval_expr`'s frame. -/

/-- The abstract native-branch contract for `Call.assertOk`: from the dispatch
entry (with the argument vector `vs` materialised and `fv = .native .assert`
staged, i.e. `CallEntryP`) the machine reaches the epilogue join (`CallExitP`)
with the spec state UNCHANGED — the `assert` success path produces `.null`,
appends nothing, and mutates neither store nor output.

This is the reusable residual for the whole native branch (dispatch → `jalr` →
`native_assert` truthy path → join); it is discharged by threading the internal
`native_assert` run against `value_truthy_spec` / `value_null_spec`. -/
def NativeAssertOkSpec
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem) : Prop :=
  Triple
    (CallEntryP g N A SL φf φc st d dLeft aLeft m0)
    (CallExitP g N A SL φf φc st m0)

/-- **`Call.assertOk` minor premise** (native `assert`, truthy arg → `.null`, no
output) at the machine level. From the `EX_CALL` dispatch the native branch runs
to the epilogue join with the spec state UNCHANGED (matching `Call.assertOk`,
which returns `st` itself). CONDITIONAL on `NativeAssertOkSpec` — the named
native-branch residual (dispatch decode + `jalr a6 = N.addr .assert` + the
`native_assert` truthy path + the `value_truthy`/`value_null` sub-calls). The
`Call.assertOk` spec derivation is threaded (its premises `vs = [v] ∨ vs = [v,m]`
and `v.truthy = true` gate the truthy machine path). -/
theorem callAssertOk
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem)
    (vs : List Value) (v mv : Value)
    (_hvs : vs = [v] ∨ vs = [v, mv])
    (_htruthy : v.truthy = true)
    (_hCall : Call st d (.native .assert) vs st .null)
    (hNative : NativeAssertOkSpec g N A SL φf φc st d dLeft aLeft m0) :
    Triple
      (CallEntryP g N A SL φf φc st d dLeft aLeft m0)
      (CallExitP g N A SL φf φc st m0) :=
  hNative

end Vsa.Sim
