import Vsa.Sim.rows.StringifyStrdupTail

/-!
# `StringifyIntTail` — the int-branch `StringifyContract` discharge (Wave-35, Residual 3)

The str-branch `StringifyContract` landed as `stringifyContract_of_call` at
`v := .str s` (`stringifyContract_of_call` is `v`-generic; the str face reads off
`stringifyDisplay_str`).  This file closes the INT branch's `StringifyContract`
(`v := .int n`) the SAME way — through the SHARED strdup tail — factoring it to the
one honest int-specific machine residual.

## What is shared vs. int-specific

`stringify` funnels EVERY kind into ONE shared strdup tail at `0x80003044`
(`strlen ▸ malloc ▸ memcpy`, composed axiom-clean in
`stringifyStrdupTailContract`).  The int branch's ONLY difference from str is the
buffer-landing step:

```
800030c0  ld   a3,8(a0)                        -- a3 = the long-long payload
800030c4  addi s1,sp,16 ; mv a0,s1 ; a2=fmt ; li a1,64
800030d8  jal  snprintf@80005c44               -- snprintf(buf,64,"%lld",n)  [snprintf_lld_spec, LANDED]
800030dc  j    80003044                        -- join the SHARED strdup tail
```

`snprintf_lld_spec` (`SnprintfSpec42`, LANDED) proves the buffer holds
`(Vsa.While.intToString n).toUTF8 ++ [0]` — i.e. `CString buf (Vsa.While.intToString n)` — and
`display (.int n) = Vsa.While.intToString n` (`stringifyDisplay_int`, GREEN).  So the WHOLE
int call is `dispatch ▸ int-arm-staging ▸ snprintf ▸ j-join ▸ strdup-tail`, landing
`StrdupTailExit rRet (Vsa.While.intToString n) = StrdupTailExit rRet ((Value.int n).display store)`.

Feeding THAT whole-call Triple into the `v`-generic `stringifyContract_of_call`
yields `StringifyContract … (.int n)`.  The composition here is pure algebra; the
only unbuilt content is the int-branch machine seam (the kind-ladder dispatch to the
int arm `0x800030c0`, the `ld/addi/mv/li` snprintf-arg staging, the `snprintf` entry
marshalling into `snprintf_lld_spec`, and the `j 0x80003044` join onto the shared
tail).  We name it precisely as ONE typed residual `IntBranchCallResid` — NOT new
snprintf machinery (which is LANDED), but the int-arm dispatch/staging seam that
splices the two landed halves.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.While (Value Store Addr)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc

namespace Vsa.Sim

/-! ## `IntBranchCallResid` — the one honest int-branch machine seam

The whole-`stringify(.int n)`-call Triple, from the callee-entry setup `Pentry sp r`
(the caller landing `ValueRepr (.int n)` at `aVal`, `mem = m0`) to
`StrdupTailExit rRet (Vsa.While.intToString n)`.  Its interior is `snprintf_lld_spec` (LANDED)
▸ `stringifyStrdupTailContract` (LANDED); the residual is the int-arm dispatch +
snprintf-arg staging + `j`-join seam that composes them.  Named, not fabricated. -/
def IntBranchCallResid
    (n : Int) (rRet : BitVec 64) (Pentry : BitVec 64 → BitVec 64 → Config → Prop) : Prop :=
  ∀ (sp r : BitVec 64), Triple (Pentry sp r) (StrdupTailExit rRet (Vsa.While.intToString n))

/-- **`StringifyContract` for `.int n`, discharged** through the shared strdup tail.
Given the int-branch whole-call Triple `IntBranchCallResid` (interior =
`snprintf_lld_spec` ▸ `stringifyStrdupTailContract`, both LANDED) and an entry-config
supplier, `StringifyContract … (.int n)` holds.  This is `stringifyContract_of_call`
at `v := .int n`, using `stringifyDisplay_int` (`display (.int n) = Vsa.While.intToString n`)
to align `StrdupTailExit rRet (Vsa.While.intToString n)` with the `v`-generic tail exit
`StrdupTailExit rRet ((Value.int n).display store)`. -/
theorem stringifyContract_int_of_call
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (store : Store) (aVal : Nat) (n : Int) (m0 : Mem)
    (rRet : BitVec 64) (Pentry : BitVec 64 → BitVec 64 → Config → Prop)
    (call : IntBranchCallResid n rRet Pentry)
    (entry : ∀ (sp r : BitVec 64), ∃ c, Pentry sp r c) :
    StringifyContract g N A SL φf φc store aVal (.int n) m0 :=
  -- `stringifyContract_of_call` wants `call : ∀ sp r, Triple (Pentry sp r)
  -- (StrdupTailExit rRet ((Value.int n).display store))`.  `(Value.int n).display
  -- store = Vsa.While.intToString n` (`stringifyDisplay_int`), so `IntBranchCallResid` IS that
  -- Triple after the display rewrite.
  stringifyContract_of_call g N A SL φf φc store aVal (.int n) m0 rRet Pentry
    (fun sp r => by
      rw [stringifyDisplay_int]; exact call sp r)
    entry

#print axioms IntBranchCallResid
#print axioms stringifyContract_int_of_call

/-! ## The int-branch call from the two landed halves

`IntBranchCallResid` decomposes as the int-arm dispatch/staging seam ▸
`snprintf_lld_spec` ▸ the `j`-join ▸ `stringifyStrdupTailContract`.  The two callee
halves are LANDED; the composer below reduces `IntBranchCallResid` to exactly the
two straight-line machine seams (arm-staging into `snprintf`, and the `j 0x80003044`
join landing the strdup-tail entry `P`), stated as named Shape-A residuals.

* `intArmSnprintf` — `dispatch/int-arm staging ▸ snprintf ▸ j-join` : lands the
  NUL-terminated buffer `CString buf (Vsa.While.intToString n)` at the shared-tail entry `Ptail`.
* `strdupTail` — the LANDED `stringifyStrdupTailContract`, `Ptail → StrdupTailExit`.

`IntBranchCallResid` is their `Triple.seq`.  Both are named; the FIRST is the honest
int-arm machine seam (unbuilt straight-line), the SECOND is the composed tail
(LANDED). -/
theorem intBranchCallResid_of_halves
    (n : Int) (rRet : BitVec 64) (Pentry : BitVec 64 → BitVec 64 → Config → Prop)
    (Ptail : BitVec 64 → BitVec 64 → Config → Prop)
    (intArmSnprintf : ∀ (sp r : BitVec 64), Triple (Pentry sp r) (Ptail sp r))
    (strdupTail : ∀ (sp r : BitVec 64), Triple (Ptail sp r) (StrdupTailExit rRet (Vsa.While.intToString n))) :
    IntBranchCallResid n rRet Pentry :=
  fun sp r => Triple.seq (intArmSnprintf sp r) (strdupTail sp r)

#print axioms intBranchCallResid_of_halves

end Vsa.Sim
