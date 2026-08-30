import Vsa.Sim.CallEntry
import Vsa.Sim.ValueSpec
import Vsa.Sim.Htif
import Vsa.Sim.HtifLift
import Vsa.Sim.Code.Native_print
import Vsa.Sim.Code.Native_println

/-!
# Layer 4 — M4: the OUTPUT natives `Call.print` / `Call.println`

The console-output leaves of the `Call` relation — the HTIF path on which
`term_sim`'s output-correctness rests. Sibling to `Call.assertOk`
(`Vsa/Sim/EvalCallNative.lean`), which shares the same native dispatch but
appends nothing; here the natives grow `Machine.output` by the rendered
arguments.

Reached from the same `EX_CALL` dispatch (`callDispatchPC = 0x80003254`) when
`fv->kind == 5` (`VAL_NATIVE`): the machine branches to the native arm at
`callNativePC = 0x800039e0`, marshals the ABI, and dispatches the stored C
function pointer with an **indirect `jalr a6`** (`a6 = N.addr f` pinned by
`ValueRepr (.native f)` — see `EvalCallNative.lean` for the shared decode).
For `print` the target is `native_print` (`0x80002ed4`); for `println`,
`native_println` (`0x80002f7c`). Both return `value_null` into the CALL sret
and join the shared `eval_expr` epilogue at `callJoinPC = 0x800033ec`.

## Decoded `native_print` (`0x80002ed4 … 0x80002f78`)
```
80002ed4:  addi sp,sp,-80          -- prologue
80002ed8:  sd   s4,32(sp)
80002edc:  sd   ra,72(sp)
80002ee0:  mv   s4,a0              -- s4 = CALL sret
80002ee4:  blez a2,0x80002f60      -- argc <= 0 ⇒ skip loop straight to value_null
80002ee8-f4:  sd s0,s1,s2,s3 spill
80002ef8:  mv   s0,a3              -- s0 = arg Value-array base
80002efc:  mv   s3,a2              -- s3 = argc
80002f00:  li   s1,0              -- s1 = i (arg counter)
80002f04:  addi s2,gp,1120        -- s2 = &_impure_ptr (stdout FILE*)
80002f08:  j    0x80002f1c         -- enter loop body at the FIRST value (skips the leading space)
--- back-edge 0x80002f0c (only reached for i>=1): print the SEPARATOR space first
80002f0c:  ld   a5,0(s2)          -- a5 = *_impure_ptr
80002f10:  addi s0,s0,24          -- advance to args[i]
80002f14:  ld   a1,16(a5)         -- a1 = stdout
80002f18:  jal  0x800062e0        -- fputc(' ', stdout)   [a0 = 32 carried from prior iter]
--- loop body 0x80002f1c: render args[i]
80002f1c:  ld   a5,0(s2)
80002f20-2c:  ld a3,a4,a5 = args[i] words 0/1/2 (24-byte Value)
80002f28:  ld   a1,16(a5)         -- a1 = stdout
80002f30:  mv   a0,sp             -- a0 = scratch Value buffer (sp)
80002f34-3c:  sd a3,a4,a5 → sp,sp+8,sp+16   (copy the 24-byte Value)
80002f40:  addiw s1,s1,1         -- i++
80002f44:  jal  0x800028fc        -- value_print(sp)  = Value.display, chars → fputc → HTIF
80002f48:  li   a0,32             -- a0 = ' ' for the NEXT iteration's separator
80002f4c:  bne  s3,s1,0x80002f0c  -- i != argc ⇒ loop (printing a space then the next value)
80002f50-5c:  ld s0,s1,s2,s3 restore
80002f60:  mv   a0,s4             -- a0 = CALL sret
80002f64:  jal  0x800027ec        -- value_null → .null into sret
80002f68-74:  epilogue
80002f78:  ret
```
The `j 0x80002f1c` at `0x80002f08` enters at the *body* on the first value, so
the leading space is skipped; every subsequent value is preceded by exactly one
`fputc(' ')`. That is precisely
`printArgs s vs = String.intercalate " " (vs.map (Value.display s))` — each
`value_print` renders one `Value.display`, single spaces between. The store is
untouched; only `Machine.output` grows.

## Decoded `native_println` (`0x80002f7c … 0x80002fbc`)
```
80002f7c:  addi sp,sp,-48 ; sd s0,ra ; mv s0,a0 (sret) ; mv a0,sp
80002f90:  jal  0x80002ed4        -- native_print(...)  (appends printArgs)
80002f94:  ld   a5,1120(gp)       -- _impure_ptr
80002f98:  li   a0,10             -- '\n'
80002f9c:  ld   a1,16(a5)         -- stdout
80002fa0:  jal  0x800062e0        -- fputc('\n', stdout)   (appends "\n")
80002fa4:  mv   a0,s0 ; jal value_null ; epilogue ; ret
```
So `native_println` = `native_print` then one more `fputc('\n')`: the output
append is `printArgs ++ "\n"`, exactly `Call.println`.

## The HTIF output-append primitive
Each printed char is one `tohost` console-write store. `htif_store_putchar`
(`Vsa/Sim/Htif.lean`) says such a store pushes `String.singleton (Char.ofNat
c.toNat)` to `σ.sailOutput`; `mem_write_value_tohost_putchar`
(`Vsa/Sim/HtifLift.lean`) lifts that through `mem_write_value`. Since
`Machine.output σ = String.join σ.sailOutput.toList` (`Vsa/Machine.lean`) and
`OutRepr σ st ↔ Machine.output σ = st.out` (`Vsa/RuntimeRepr.lean`), composing
these over the print loop (measure = remaining chars / remaining args) grows
`Machine.output` by exactly `printArgs st.store vs` (`native_println` adds the
trailing `"\n"`). The per-`Value.display` character stream for `int`s routes
through the already-specced `%lld`/`snprintf` path; `str`/`bool`/`null` render
their literal bytes.

## What lands here
* the decoded PC constants for both natives,
* `NativePrintSpec` / `NativePrintlnSpec` — the abstract machine contracts for
  the whole native branch of `print` / `println` (`callDispatchPC` with the arg
  vector `vs` materialised and `fv = .native .print/.println` staged ⇒
  `callJoinPC` with the store UNCHANGED, `.null` produced, and the console
  output grown by `printArgs st.store vs` `(++ "\n")`) — the reusable residuals
  the eventual end-to-end proof discharges by threading the print loop against
  `htif_store_putchar` / `value_print` / the `%lld` render path,
* `callPrint` / `callPrintln` — the `Call.print` / `Call.println` minor premises
  as machine `Triple`s (`CallEntryP ⇒ CallExitP` with the OUTPUT-APPENDED exit
  state), CONDITIONAL on the named residual, UNCONDITIONAL otherwise. This is
  the deferral pattern of `callAssertOk`'s `NativeAssertOkSpec`.

**The output-append contract** (the core of `term_sim` output-correctness): the
exit predicate `CallExitP … ⟨st.store, st.out ++ printArgs st.store vs⟩` carries
`OutRepr σ' ⟨st.store, st.out ++ printArgs st.store vs⟩`, i.e. `Machine.output
σ' = st.out ++ printArgs st.store vs` — the machine's HTIF console has grown by
exactly the spec's rendered arguments, with the store unchanged.

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

/-! ## `native_print` / `native_println` entry / sub-call PCs -/

/-- `native_print` entry (`interp_init`'s `print` C fn ptr). -/
def nativePrintPC : Nat := 0x80002ed4
/-- `native_print`'s loop body (the first-value entry, jumped to from `0x80002f08`). -/
def nativePrintBodyPC : Nat := 0x80002f1c
/-- `native_print`'s loop back-edge (prints the separator space for `i ≥ 1`). -/
def nativePrintSepPC : Nat := 0x80002f0c
/-- `native_print`'s post-loop `value_null` return. -/
def nativePrintNullPC : Nat := 0x80002f60

/-- `native_println` entry (`interp_init`'s `println` C fn ptr). -/
def nativePrintlnPC : Nat := 0x80002f7c
/-- Link address after `native_println`'s `jal native_print`. -/
def nativePrintlnPrintRetPC : Nat := 0x80002f94
/-- Link address after `native_println`'s `jal fputc` (the trailing `'\n'`). -/
def nativePrintlnNewlineRetPC : Nat := 0x80002fa4

/-! ## `Call.print` — the native `print` case (render args, space-separated) -/

/-- The abstract native-branch contract for `Call.print`: from the dispatch
entry (with the argument vector `vs` materialised and `fv = .native .print`
staged, i.e. `CallEntryP`) the machine reaches the epilogue join with the store
UNCHANGED, `.null` produced, and the console output grown by exactly
`printArgs st.store vs` — the exit state is `⟨st.store, st.out ++ printArgs
st.store vs⟩` (`CallExitP` at that state).

This is the reusable residual for the whole native `print` branch (dispatch →
`jalr a6 = N.addr .print` → the `native_print` loop → `value_null` → join). Its
discharge threads the print loop (measure = remaining args) composing each
`value_print` render (`Value.display`; `int` via the `%lld`/`snprintf` path) and
each `fputc` against the HTIF console-write append primitive
(`htif_store_putchar` / `mem_write_value_tohost_putchar`). The OUTPUT-APPEND is
the novel content: `OutRepr σ' ⟨st.store, st.out ++ printArgs st.store vs⟩`. -/
def NativePrintSpec
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem) (vs : List Value) : Prop :=
  Triple
    (CallEntryP g N A SL φf φc st d dLeft aLeft m0)
    (CallExitP g N A SL φf φc st.store.frames.size st.store.closures.size ⟨st.store, st.out ++ printArgs st.store vs⟩ m0)

/-- **`Call.print` minor premise** (native `print`, render args space-separated,
append to console → `.null`) at the machine level. From the `EX_CALL` dispatch
the native branch runs to the epilogue join with the store UNCHANGED, `.null`
produced, and the console output grown by `printArgs st.store vs` — matching
`Call.print`, whose post-state is `⟨st.store, st.out ++ printArgs st.store vs⟩`.
CONDITIONAL on `NativePrintSpec` — the named native-branch residual (dispatch
decode + `jalr a6 = N.addr .print` + the `native_print` loop + the per-char HTIF
appends + `value_null`). The `Call.print` spec derivation is threaded (its
post-state fixes the output-appended exit state). -/
theorem callPrint
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem)
    (vs : List Value)
    (_hCall : Call st d (.native .print) vs
      ⟨st.store, st.out ++ printArgs st.store vs⟩ .null)
    (hNative : NativePrintSpec g N A SL φf φc st d dLeft aLeft m0 vs) :
    Triple
      (CallEntryP g N A SL φf φc st d dLeft aLeft m0)
      (CallExitP g N A SL φf φc st.store.frames.size st.store.closures.size ⟨st.store, st.out ++ printArgs st.store vs⟩ m0) :=
  hNative

/-! ## `Call.println` — the native `println` case (`print` then a trailing `"\n"`) -/

/-- The abstract native-branch contract for `Call.println`: as `NativePrintSpec`,
but the exit output is grown by `printArgs st.store vs ++ "\n"` — the
`native_println` path calls `native_print` then `fputc('\n')`. Its discharge is
`NativePrintSpec`'s threading plus the single trailing-newline HTIF append. -/
def NativePrintlnSpec
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem) (vs : List Value) : Prop :=
  Triple
    (CallEntryP g N A SL φf φc st d dLeft aLeft m0)
    (CallExitP g N A SL φf φc st.store.frames.size st.store.closures.size ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ m0)

/-- **`Call.println` minor premise** (native `println`, render args
space-separated then a trailing newline, append to console → `.null`) at the
machine level. From the `EX_CALL` dispatch the native branch runs to the
epilogue join with the store UNCHANGED, `.null` produced, and the console output
grown by `printArgs st.store vs ++ "\n"` — matching `Call.println`, whose
post-state is `⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩`. CONDITIONAL
on `NativePrintlnSpec` — the named native-branch residual (`= NativePrintSpec`
plus the trailing `fputc('\n')` HTIF append). -/
theorem callPrintln
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem)
    (vs : List Value)
    (_hCall : Call st d (.native .println) vs
      ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ .null)
    (hNative : NativePrintlnSpec g N A SL φf φc st d dLeft aLeft m0 vs) :
    Triple
      (CallEntryP g N A SL φf φc st d dLeft aLeft m0)
      (CallExitP g N A SL φf φc st.store.frames.size st.store.closures.size ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ m0) :=
  hNative

end Vsa.Sim
