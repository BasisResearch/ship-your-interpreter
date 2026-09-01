import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac

/-!
# `ValuePrintArms` — the six `value_print` case arms as `#derive_case` segs (wave 44)

`value_print` (`0x800028fc … 0x800029ac`) dispatches on the ValueKind through a
`.rodata` jump table (`jr a5`, base `0x80019f10`) into six straight-line arms,
each ending in a **`j` tail-call** into a newlib IO function (`fprintf` /
`fwrite` / `fputs` — value_print does NOT return itself for these arms; the IO
fn returns to value_print's caller).  So each arm is a `#derive_case` seg ending
in a `.j` terminator whose concrete target IS the callee entry — `segToTriple`
parks the run AT that entry with the ABI args pinned, and the three callee
contracts (`FprintfContract`/`FwriteContract`/`FputsContract`, §Contracts) are
the genuine machine frontier below this file (no code image / site battery
exists for any of them yet — named typed premises with doc comments, the
wave-39 native-observation route).

Arm map (kind → handler → callee), from the ELF `.rodata` table + disasm:
* kind 0 `null`    → `0x8000295c` → `j fwrite`  (prints `"null"`)
* kind 1 `bool`    → `0x80002974` → `j fputs`   (`"true"`/`"false"`, inner `beqz`)
* kind 2 `int`     → `0x80002990` → `j fprintf` (fmt `0x800192c0`, the `%lld` path)
* kind 3 `str`     → `0x800029a4` → `j fputs`
* kind 4 `closure` → `0x80002928` → `j fprintf` (fmt `0x800192c8`, inner `beqz`)
* kind 5 `native`  → `0x80002948` → `j fprintf` (fmt `0x800192d8`)

DECODE NOTE (dispatch head, NOT this file): the jump-table span's first
instruction `lwu a5,0(a0)` (`0x80002908`, word `00056783`) has no `MKind` in the
SegEval block decoder (`decodeM` LOAD group = lw/ld/lbu only, no `lwu`) — see
observation `lwu-missing-from-block-decoder`.  The dispatch head therefore stays
a NAMED residual until `.lwu` lands.  The arms below are all `lwu`-free and land
now.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## The `closure` arm `0x80002928 → j fprintf@0x800061c0` (inner `beqz`)

`ld a5,8(a0)` (closure ptr) ; `ld a5,0(a5)` (deref) ; `ld a2,8(a5)` (the
`fn_expr`-derived word) ; `beqz a2,0x800029b0`.  If `a2 ≠ 0` (the normal case:
a valid closure carries a non-null `fn_expr`) it falls through `mv a0,a1 ;
auipc a1 ; addi a1,a1,-1652` (`a1 = 0x800192c8`, the closure fmt) then
`j fprintf`.  The `a2 = 0` branch exits our span to `0x800029b0` (a separate
`j fwrite` tail, kind's degenerate print) — NOT built here (own mini-arm).
`beqz a2` is `beq a2,x0` (rs1=12, rs2=0). -/
#derive_case vpClosureArm chain
  [(0x80002928#64, 0x00853783#32),                 -- ld   a5,8(a0)
   (0x8000292c#64, 0x0007b783#32),                 -- ld   a5,0(a5)
   (0x80002930#64, 0x0087b603#32)]                 -- ld   a2,8(a5)
    terminator ⟨0x80002934#64, 0x06060e63#32, 0x63#8, 0x0e#8, 0x06#8, 0x06#8,
      .br bop.BEQ false, 12, 0, 0x007c#13, 0#21, 0#12⟩ ;;
  [(0x80002938#64, 0x00058513#32),                 -- mv   a0,a1
   (0x8000293c#64, 0x00017597#32),                 -- auipc a1,0x17
   (0x80002940#64, 0x98c58593#32)]                 -- addi a1,a1,-1652 (closure fmt)
    terminator ⟨0x80002944#64, 0x07d0306f#32, 0x6f#8, 0x30#8, 0xd0#8, 0x07#8,
      .j, 0, 0, 0#13, 0x387c#21, 0#12⟩

/-- `closure`-arm entry: `a0 = pv`, `a1 = stream`. -/
def vpClosureL (pv stream : BitVec 64) : GRegs := [(10, pv), (11, stream)]

/-- Parked at `fprintf`'s entry after the (non-null) `closure` arm:
`PC = 0x800061c0`, frame in `GHolds` (`a0 = stream`, `a1 = 0x800192c8` the
closure fmt, `a2 = ` the `fn_expr` word). -/
def VpClosureArmPost (pv stream : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x800061c0#64 ∧
  GHolds c.σ (evalBlocks vpClosureArm (SegEvalState.init (vpClosureL pv stream) lds)).regs

theorem vpClosureArmRow (pv stream : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre vpClosureArm (vpClosureL pv stream) lds 0x80002928#64 m0)
      (VpClosureArmPost pv stream lds m0) := by
  apply segToTriple vpClosureArm (vpClosureL pv stream) lds 0x80002928#64 m0
    (VpClosureArmPost pv stream lds m0)
    (by show ChainOK 0x80002928#64 [10, 11] vpClosureArm; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  exact ⟨hG', by rw [hmem']; rfl, by rw [hpc']; rfl, hregs⟩

/-! ## The `int` arm `0x80002990 → j fprintf@0x800061c0`

`ld a2,8(a0)` (the int payload) ; `mv a0,a1` (`a1` = the FILE* stream) ;
`auipc a1 ; addi a1,a1,-1752` (`a1 = 0x800192c0`, the `"%lld"` format string) ;
`j fprintf`.  Ends parked at `fprintf`'s entry with `a0 = stream`, `a1 = fmt`,
`a2 = the int payload word`. -/
#derive_case vpIntArm chain
  [(0x80002990#64, 0x00853603#32),                 -- ld   a2,8(a0)
   (0x80002994#64, 0x00058513#32),                 -- mv   a0,a1  (addi a0,a1,0)
   (0x80002998#64, 0x00017597#32),                 -- auipc a1,0x17
   (0x8000299c#64, 0x92858593#32)]                 -- addi a1,a1,-1752
    terminator ⟨0x800029a0#64, 0x0210306f#32, 0x6f#8, 0x30#8, 0x10#8, 0x02#8,
      .j, 0, 0, 0#13, 0x3820#21, 0#12⟩

/-- The `int`-arm entry pin list: `a0 = pv` (the `Value*`), `a1 = stream` (the
FILE* pointer the caller of `value_print` passed).  `a2`/`a4` are recomputed
inside the arm. -/
def vpIntL (pv stream : BitVec 64) : GRegs := [(10, pv), (11, stream)]

/-- **Parked at `fprintf`'s entry** after the `int` arm: `PC = 0x800061c0`,
memory unchanged (no stores), the whole computed register frame surviving in
`GHolds` so the caller reads the ABI args (`a0 = stream`, `a1 = 0x800192c0` the
`"%lld"` fmt, `a2 = ` the sign-extended int payload) off `out.regs` — exactly
the `MallocArgPost`/`GHolds`-carrying shape (avoids forcing `lookupG` reduction
in this row; the concrete arg values close by `decide` at the caller via
`gholds_lookup`, or via the `vpInt_*` accessors below). -/
def VpIntArmPost (pv stream : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x800061c0#64 ∧
  GHolds c.σ (evalBlocks vpIntArm (SegEvalState.init (vpIntL pv stream) lds)).regs

/-- **The `int` arm as a `Triple`** — `segToTriple` folds the seg→Triple
marshalling; `hwf` is the one kernel `decide`, `hpost` projects the parked-at-
`fprintf` post off the computed outcome.  `lds` (one 8-byte load for `ld a2,8(a0)`)
stays abstract; the caller supplies the int-payload bytes. -/
theorem vpIntArmRow (pv stream : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre vpIntArm (vpIntL pv stream) lds 0x80002990#64 m0)
      (VpIntArmPost pv stream lds m0) := by
  apply segToTriple vpIntArm (vpIntL pv stream) lds 0x80002990#64 m0
    (VpIntArmPost pv stream lds m0)
    (by show ChainOK 0x80002990#64 [10, 11] vpIntArm; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  exact ⟨hG', by rw [hmem']; rfl, by rw [hpc']; rfl, hregs⟩

/-! ## The `bool` arm `0x80002974 → j fputs@0x80006500` (inner `beqz` on the flag)

`lw a5,8(a0)` (the bool payload) ; `auipc a0 ; addi a0,a0,1688` (`a0 = 0x80019010`,
the `"false"` literal) ; `beqz a5,0x8000298c`.  If `a5 = 0` (`false`) the branch is
TAKEN straight to the `j fputs` at `0x8000298c` with `a0 = "false"`; if `a5 ≠ 0`
(`true`) it falls through to `auipc a0 ; addi a0,a0,1668` (`a0 = 0x80019008`, the
`"true"` literal) then `j fputs`.  Two rows, guard polarity fixed per bool value
(the `beq a5,x0` guard rides in the caller's `ChainFacts`, discharged from the
`ValueRepr.bool` payload).  `beqz a5` is `beq a5,x0` (rs1=15, rs2=0). -/

/- The `bool`-TRUE arm (`a5 ≠ 0`, `beqz` NOT taken): fall through the `"true"`
block into `j fputs`. -/
#derive_case vpBoolTrueArm chain
  [(0x80002974#64, 0x00852783#32),                 -- lw   a5,8(a0)
   (0x80002978#64, 0x00016517#32),                 -- auipc a0,0x16
   (0x8000297c#64, 0x69850513#32)]                 -- addi a0,a0,1688 ("false")
    terminator ⟨0x80002980#64, 0x00078663#32, 0x63#8, 0x86#8, 0x07#8, 0x00#8,
      .br bop.BEQ false, 15, 0, 0x000c#13, 0#21, 0#12⟩ ;;
  [(0x80002984#64, 0x00016517#32),                 -- auipc a0,0x16
   (0x80002988#64, 0x68450513#32)]                 -- addi a0,a0,1668 ("true")
    terminator ⟨0x8000298c#64, 0x3750306f#32, 0x6f#8, 0x30#8, 0x50#8, 0x37#8,
      .j, 0, 0, 0#13, 0x3b74#21, 0#12⟩

/- The `bool`-FALSE arm (`a5 = 0`, `beqz` TAKEN): jump straight to `j fputs`
with `a0 = "false"`.  Block 2 is the bare `j fputs` (empty body). -/
#derive_case vpBoolFalseArm chain
  [(0x80002974#64, 0x00852783#32),                 -- lw   a5,8(a0)
   (0x80002978#64, 0x00016517#32),                 -- auipc a0,0x16
   (0x8000297c#64, 0x69850513#32)]                 -- addi a0,a0,1688 ("false")
    terminator ⟨0x80002980#64, 0x00078663#32, 0x63#8, 0x86#8, 0x07#8, 0x00#8,
      .br bop.BEQ true, 15, 0, 0x000c#13, 0#21, 0#12⟩ ;;
  [] terminator ⟨0x8000298c#64, 0x3750306f#32, 0x6f#8, 0x30#8, 0x50#8, 0x37#8,
      .j, 0, 0, 0#13, 0x3b74#21, 0#12⟩

/-- `bool`-arm entry: `a0 = pv`.  (`a1` = stream unused; fputs writes stdout.) -/
def vpBoolL (pv : BitVec 64) : GRegs := [(10, pv)]

/-- Parked at `fputs`'s entry after the `bool`-TRUE arm: `PC = 0x80006500`,
`a0 = 0x80019008` (`"true"`), frame in `GHolds`. -/
def VpBoolTrueArmPost (pv : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x80006500#64 ∧
  GHolds c.σ (evalBlocks vpBoolTrueArm (SegEvalState.init (vpBoolL pv) lds)).regs

theorem vpBoolTrueArmRow (pv : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre vpBoolTrueArm (vpBoolL pv) lds 0x80002974#64 m0)
      (VpBoolTrueArmPost pv lds m0) := by
  apply segToTriple vpBoolTrueArm (vpBoolL pv) lds 0x80002974#64 m0
    (VpBoolTrueArmPost pv lds m0)
    (by show ChainOK 0x80002974#64 [10] vpBoolTrueArm; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  exact ⟨hG', by rw [hmem']; rfl, by rw [hpc']; rfl, hregs⟩

/-- Parked at `fputs`'s entry after the `bool`-FALSE arm: `PC = 0x80006500`,
`a0 = 0x80019010` (`"false"`), frame in `GHolds`. -/
def VpBoolFalseArmPost (pv : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x80006500#64 ∧
  GHolds c.σ (evalBlocks vpBoolFalseArm (SegEvalState.init (vpBoolL pv) lds)).regs

theorem vpBoolFalseArmRow (pv : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre vpBoolFalseArm (vpBoolL pv) lds 0x80002974#64 m0)
      (VpBoolFalseArmPost pv lds m0) := by
  apply segToTriple vpBoolFalseArm (vpBoolL pv) lds 0x80002974#64 m0
    (VpBoolFalseArmPost pv lds m0)
    (by show ChainOK 0x80002974#64 [10] vpBoolFalseArm; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  exact ⟨hG', by rw [hmem']; rfl, by rw [hpc']; rfl, hregs⟩

/-! ## The `str` arm `0x800029a4 → j fputs@0x80006500`

`ld a0,8(a0)` (the `char*` string pointer becomes the fputs arg) ; `j fputs`. -/
#derive_case vpStrArm chain
  [(0x800029a4#64, 0x00853503#32)]                 -- ld a0,8(a0)
    terminator ⟨0x800029a8#64, 0x3590306f#32, 0x6f#8, 0x30#8, 0x90#8, 0x35#8,
      .j, 0, 0, 0#13, 0x3b58#21, 0#12⟩

/-- `str`-arm entry: `a0 = pv` (the `Value*`); `a1 = stream` unused (fputs
writes to `stdout`, resolved inside `fputs`). -/
def vpStrL (pv : BitVec 64) : GRegs := [(10, pv)]

/-- Parked at `fputs`'s entry after the `str` arm: `PC = 0x80006500`, `a0 = ` the
loaded string pointer (`ld a0,8(a0)` — the sign-extended 8-byte payload), the
frame surviving in `GHolds`. -/
def VpStrArmPost (pv : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x80006500#64 ∧
  GHolds c.σ (evalBlocks vpStrArm (SegEvalState.init (vpStrL pv) lds)).regs

theorem vpStrArmRow (pv : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre vpStrArm (vpStrL pv) lds 0x800029a4#64 m0) (VpStrArmPost pv lds m0) := by
  apply segToTriple vpStrArm (vpStrL pv) lds 0x800029a4#64 m0 (VpStrArmPost pv lds m0)
    (by show ChainOK 0x800029a4#64 [10] vpStrArm; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  exact ⟨hG', by rw [hmem']; rfl, by rw [hpc']; rfl, hregs⟩

/-! ## The `native` arm `0x80002948 → j fprintf@0x800061c0`

`ld a2,8(a0)` (the native's name string pointer) ; `mv a0,a1` (stream) ;
`auipc a1 ; addi a1,a1,-1656` (`a1 = 0x800192d8`, the `"<native %s>"` fmt) ;
`j fprintf`. -/
#derive_case vpNativeArm chain
  [(0x80002948#64, 0x00853603#32),                 -- ld   a2,8(a0)
   (0x8000294c#64, 0x00058513#32),                 -- mv   a0,a1
   (0x80002950#64, 0x00017597#32),                 -- auipc a1,0x17
   (0x80002954#64, 0x98858593#32)]                 -- addi a1,a1,-1656
    terminator ⟨0x80002958#64, 0x0690306f#32, 0x6f#8, 0x30#8, 0x90#8, 0x06#8,
      .j, 0, 0, 0#13, 0x3868#21, 0#12⟩

/-- `native`-arm entry: `a0 = pv`, `a1 = stream`. -/
def vpNativeL (pv stream : BitVec 64) : GRegs := [(10, pv), (11, stream)]

/-- Parked at `fprintf`'s entry after the `native` arm: `PC = 0x800061c0`,
frame in `GHolds` (`a0 = stream`, `a1 = 0x800192d8` the native fmt, `a2 = ` the
name pointer). -/
def VpNativeArmPost (pv stream : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x800061c0#64 ∧
  GHolds c.σ (evalBlocks vpNativeArm (SegEvalState.init (vpNativeL pv stream) lds)).regs

theorem vpNativeArmRow (pv stream : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre vpNativeArm (vpNativeL pv stream) lds 0x80002948#64 m0)
      (VpNativeArmPost pv stream lds m0) := by
  apply segToTriple vpNativeArm (vpNativeL pv stream) lds 0x80002948#64 m0
    (VpNativeArmPost pv stream lds m0)
    (by show ChainOK 0x80002948#64 [10, 11] vpNativeArm; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  exact ⟨hG', by rw [hmem']; rfl, by rw [hpc']; rfl, hregs⟩

/-! ## The `null` arm `0x8000295c → j fwrite@0x80005260`

`mv a3,a1` (stream → fwrite's 4th arg) ; `li a2,4` (nmemb) ; `li a1,1` (size) ;
`auipc a0 ; addi a0,a0,1712` (`a0 = 0x80019018`, the `"null"` literal) ;
`j fwrite`.  So `fwrite("null", 1, 4, stream)`. -/
#derive_case vpNullArm chain
  [(0x8000295c#64, 0x00058693#32),                 -- mv   a3,a1
   (0x80002960#64, 0x00400613#32),                 -- li   a2,4
   (0x80002964#64, 0x00100593#32),                 -- li   a1,1
   (0x80002968#64, 0x00016517#32),                 -- auipc a0,0x16
   (0x8000296c#64, 0x6b050513#32)]                 -- addi a0,a0,1712
    terminator ⟨0x80002970#64, 0x0f10206f#32, 0x6f#8, 0x20#8, 0x10#8, 0x0f#8,
      .j, 0, 0, 0#13, 0x28f0#21, 0#12⟩

/-- `null`-arm entry: `a1 = stream` (the only live input; `a0` is overwritten). -/
def vpNullL (stream : BitVec 64) : GRegs := [(11, stream)]

/-- Parked at `fwrite`'s entry after the `null` arm: `PC = 0x80005260`, frame in
`GHolds` (`a0 = 0x80019018` the `"null"` buffer, `a1 = 1` size, `a2 = 4` nmemb,
`a3 = stream`). -/
def VpNullArmPost (stream : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x80005260#64 ∧
  GHolds c.σ (evalBlocks vpNullArm (SegEvalState.init (vpNullL stream) lds)).regs

theorem vpNullArmRow (stream : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre vpNullArm (vpNullL stream) lds 0x8000295c#64 m0)
      (VpNullArmPost stream lds m0) := by
  apply segToTriple vpNullArm (vpNullL stream) lds 0x8000295c#64 m0
    (VpNullArmPost stream lds m0)
    (by show ChainOK 0x8000295c#64 [11] vpNullArm; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  exact ⟨hG', by rw [hmem']; rfl, by rw [hpc']; rfl, hregs⟩

#print axioms vpIntArmRow
#print axioms vpStrArmRow
#print axioms vpNativeArmRow
#print axioms vpNullArmRow
#print axioms vpBoolTrueArmRow
#print axioms vpBoolFalseArmRow
#print axioms vpClosureArmRow

end Vsa.Sim

