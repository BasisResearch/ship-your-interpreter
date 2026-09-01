import Vsa.Sim.rows.ConcatMallocArg
import Vsa.Sim.rows.ConcatMemcpyArg
import Vsa.Sim.rows.ConcatStrcpyArg
import Vsa.Sim.rows.StrcpyContractInhab

/-!
# `ConcatCBlockStaging` — the concat C-block staging segs + the assembly plan

Task #71 Part 3 (partial, per the brief's "land the staging segs + callee splices
pairwise and name the final assembly" fallback for the largest heap composition).

`StrConcatCBlockResid` (`Vsa/Sim/rows/StrConcatHeap.lean`) is the whole-node
`EvalIH` for `.binary .add el er` carrying the two operand `stringify` contracts as
hypotheses.  Its bespoke machine content is the byte-exact concat C-block splice
`0x80003a20 → 0x80003ae0` (disasm confirmed):

```
80003a40  jal stringify   → s2/s3  (LEFT  → fresh char* of L.display)    [HYP: StringifyContract]
80003a68  jal stringify   → s0/s5  (RIGHT → fresh char* of R.display)    [HYP: StringifyContract]
80003a74  mv a0,s2 ; jal strlen    → s2 = |L.display|                    [strlen_spec_framed]
80003a80  mv a0,s0 ; jal strlen    → a0 = |R.display|                    [strlen_spec_framed]
80003a88  add a0,s2,a0 ; addi a0,a0,1 ; jal malloc → s0 = new            [MallocContract.spec]   ← concatMallocArgRow
80003a9c  beqz a0 → 80003e28       (OOM; arena no-OOM ⇒ not taken)
80003aa0  mv a2,s2 ; mv a1,s3 ; jal memcpy(new, L, |L|)                  [memcpy_spec_framed_byte] ← concatMemcpyArgRow
80003ab4  add a0,s0,s2 ; mv a1,s5 ; jal strcpy(new+|L|, R)  (copies R+NUL)[StrcpyContractCpw]      ← concatStrcpyArgRow
80003abc  mv a0,s3 ; jal free ; mv a0,s5 ; jal free                      [MallocContract.freeSpec ×2]
80003ad0  mv a1,s0 ; mv a0,s1 ; jal value_str@8000281c ; j 800033ec      [value_str_spec_full]
```

## LANDED here (green + axiom-clean seg-layer staging bodies)

The three distinctive arg-staging spans between the callees, each a self-contained
`#derive_case` seg over `lds` parked at its `jal` seam (the `strdupStrlenArgSeg`
idiom — NO stringify code pins needed, they are fallthrough spans):

| span | seg row | marshals |
|------|---------|----------|
| `0x80003a88 add a0,s2,a0 ; addi a0,a0,1` | `concatMallocArgRow` | size `|L|+|R|+1` → `a0` |
| `0x80003aa0 mv a2,s2 ; mv a1,s3`         | `concatMemcpyArgRow` | `a2 = |L|`, `a1 = L` |
| `0x80003aac mv a1,s5 ; add a0,s0,s2`     | `concatStrcpyArgRow` | `a1 = R`, `a0 = new + |L|` |

## The final assembly — NAMED (not built)

The concat C-block Triple is `callSeg`/`Triple.seq` over the seven callee splices,
threading the staging segs above between them.  All seven callee contracts EXIST:
the two `stringify` are the `StrConcatCBlockResid` HYPOTHESES; `strlen_spec_framed`,
`MallocContract.spec`, `memcpy_spec_framed_byte`, `MallocContract.freeSpec`,
`value_str_spec_full` are landed; and **`strcpy` is now Part 2's
`StrcpyContractCpw`** (`StrcpyContractInhab.lean`, the sound-frame contract inhabited
from `strcpy_full_spec`).  What remains for the LIVE `StrConcatCBlockResid` is:

* the ~7-way `callSeg`/`Triple.seq` assembly of these splices into the C-block
  Triple (the Shape-D algebra, like `EnvDefCompose`'s append composition but one
  callee longer, with two `free` no-ops popping the two scratch `exts`);
* the two `free` `exts`-pop threading (`MallocContract.freeSpec`, wave-26 contract);
* the `EvalIH`-level marshalling (`blockA_binaryArm ≫ blockB_binary(two EvalIH) ≫
  C-block ≫ blockD_v_rec`) that lifts the C-block Triple to the whole-node
  `EvalIH` `StrConcatCBlockResid` demands — the standard binary-arm pipeline;
* the remaining strlen-arg staging segs (`0x80003a74`/`0x80003a80`, the two
  `mv a0,sX` ▷ jal strlen prefixes — identical to `concatMemcpyArg`, generable by
  `genseg` when the assembly consumes them) and the two `stringify`-arg staging
  spills (`0x80003a2c..0x80003a40`, `0x80003a58..0x80003a68`).

This file is the seg-layer floor for that assembly; the assembly + `EvalIH` lift is
`StrConcatCBlockResid` itself, left as the one named machine residual per the brief.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-- `concatMallocArgRow` re-exported by name: the malloc-arg staging span as a
`Triple` (size `|L|+|R|+1` marshalled into `a0`, parked at the `jal malloc` seam
`0x80003a90`).  = the landed `concatMallocArgRow`. -/
theorem concatCBlock_mallocArg_seg (s2 a0 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre concatMallocArgSeg (concatMallocArgL s2 a0) lds 0x80003a88#64 m0)
      (ConcatMallocArgPost s2 a0 lds m0) :=
  concatMallocArgRow s2 a0 lds m0

/-- `concatMemcpyArgRow` re-exported by name: the memcpy-arg staging span (`a2 =
|L|`, `a1 = L`, parked at the `jal memcpy` seam `0x80003aa8`). -/
theorem concatCBlock_memcpyArg_seg (s2 s3 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre concatMemcpyArgSeg (concatMemcpyArgL s2 s3) lds 0x80003aa0#64 m0)
      (ConcatMemcpyArgPost s2 s3 lds m0) :=
  concatMemcpyArgRow s2 s3 lds m0

/-- `concatStrcpyArgRow` re-exported by name: the strcpy-arg staging span (`a1 =
R`, `a0 = new + |L|`, parked at the `jal strcpy` seam `0x80003ab4`).  Feeds Part 2's
`StrcpyContractCpw` splice. -/
theorem concatCBlock_strcpyArg_seg (s5 s0 s2 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre concatStrcpyArgSeg (concatStrcpyArgL s5 s0 s2) lds 0x80003aac#64 m0)
      (ConcatStrcpyArgPost s5 s0 s2 lds m0) :=
  concatStrcpyArgRow s5 s0 s2 lds m0

#print axioms concatCBlock_mallocArg_seg
#print axioms concatCBlock_memcpyArg_seg
#print axioms concatCBlock_strcpyArg_seg

end Vsa.Sim
