import Vsa.Sim.rows.ConcatCBlockStaging
import Vsa.Sim.rows.CStringAppend
import Vsa.Sim.DeriveCallSeg

/-!
# `ConcatHeapCore` — the concat C-block `strlen×2 ≫ malloc ≫ memcpy ≫ strcpy ≫ free×2 ≫ value_str` splice

Task #82 Part 2.  `StrConcatCBlockResid` (`Vsa/Sim/rows/StrConcatHeap.lean`,
READ-ONLY) is the whole-node `EvalIH` for `.binary .add el er` carrying the two
operand `stringify` contracts as hypotheses; its bespoke machine content is the
byte-exact concat C-block `0x80003a20 → 0x80003ae0` (disasm confirmed in
`ConcatCBlockStaging.lean`):

```
80003a74  mv a0,s2 ; jal strlen    → s2 = |L.display|                    [strlen framed]
80003a80  mv a0,s0 ; jal strlen    → a0 = |R.display|                    [strlen framed]
80003a88  add a0,s2,a0 ; addi a0,a0,1 ; jal malloc → s0 = new            [MallocContract.spec]  ← concatMallocArgRow
80003a9c  beqz a0 → 80003e28       (OOM; arena no-OOM ⇒ not taken)       [M.nonNull_of_bounded]
80003aa0  mv a2,s2 ; mv a1,s3 ; jal memcpy(new, L, |L|)                  [memcpy framed byte]   ← concatMemcpyArgRow
80003ab4  add a0,s0,s2 ; mv a1,s5 ; jal strcpy(new+|L|, R)  (copies R+NUL)[StrcpyContractCpw]    ← concatStrcpyArgRow
80003abc  mv a0,s3 ; jal free ; mv a0,s5 ; jal free                      [MallocContract.freeSpec ×2]
80003ad0  mv a1,s0 ; mv a0,s1 ; jal value_str@8000281c ; j 800033ec      [value_str_spec_full]
```

## What this file lands

`concatHeapCore` is the **pure `callSeg`/`Triple.seq` algebra** that composes the
eight callee segments (two `strlen`, `malloc`, `memcpy`, `strcpy`, two `free`,
`value_str`) over their seven inter-callee seams — EXACTLY the shape of
`stringifyStrdupTailContract` (`StringifyStrdupTail.lean`) at larger scale (one
callee shorter there; the append path `env_define` in `EnvDefCompose.lean` is the
other model).  Each callee contract and each seam bridge is a NAMED hypothesis —
the callees are threaded, never re-proved — and the whole C-block is the nested
`callSeg` tower.  Split into three named sub-chains (front / middle / tail) composed
at the end, so no single elaboration carries the whole eight-deep tower.

The concluding `CString new (sL ++ sR)` fact the `value_str` box needs is
`concatReadback` (`CStringAppend.lean`, already landed): the memcpy byte-post's
NUL-free left run glued to the strcpy post's NUL-terminated right tail — supplied
as the tail seam's readback obligation, mechanical.

The seam predicates `S1..S7` are abstract `Config → Prop` (the concrete boundaries
are the staging-seg posts + callee entry/exit predicates from
`ConcatCBlockStaging`/the framed contracts); phrasing `concatHeapCore` over them
keeps this file pure composition algebra — the seam bridges and callee contracts are
the caller's to supply (they are the honest remaining machine content), exactly as
`stringifyStrdupTailContract` takes its four bridges + `strlenFramed`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa.Machine (Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-! ## Front sub-chain: `strlen(L) ≫ strlen(R) ≫ malloc`

Three callees, two seams.  `P` is the C-block entry (both operands stringified:
`s3 = L-ptr`, `s5 = R-ptr`, the two `CString`s as facts); `S1` the state after
`strlen(L)` (`s2 = |L|`), `S2` after `strlen(R)` (`a0 = |R|`), `Sfront` the malloc
post (`s0 = new`).  Each callee is `Triple Si-entry Si-exit`; the seams
(`mv a0,sX` arg staging, the `add;addi` malloc-size marshalling
`concatMallocArgRow`) are the prefix Triples. -/
theorem concatFront {P S1 S1' S2 S2' Smpre Sfront : Config → Prop}
    (strlenL : Triple S1 S1')          -- strlen(L) callee
    (strlenR : Triple S2 S2')          -- strlen(R) callee
    (malloc  : Triple Smpre Sfront)    -- malloc callee (size already marshalled into Smpre)
    (seam0 : Triple P S1)              -- entry ▷ mv a0,s2 ; jal strlen(L)
    (seam1 : Triple S1' S2)            -- |L|→s2 ; mv a0,s0 ; jal strlen(R)
    (seamM : Triple S2' Smpre) :       -- add a0,s2,a0 ; addi a0,a0,1  (concatMallocArgRow, into malloc pre)
    Triple P Sfront :=
  -- (P ≫ strlen(L)) ≫ (strlen(R)) ≫ (malloc-size seam ≫ malloc)
  callSeg (callSeg seam0 strlenL seam1) strlenR (Triple.seq seamM malloc)

/-! ## Middle sub-chain: `memcpy ≫ strcpy`

Two callees, one seam between (the `add a0,s0,s2 ; mv a1,s5` strcpy-dst marshalling,
`concatStrcpyArgRow`).  `Sfront` (malloc post, non-null pruned) ▷ the memcpy arg
staging (`mv a2,s2 ; mv a1,s3`, `concatMemcpyArgRow`) ▷ memcpy ▷ strcpy staging ▷
strcpy.  `Smid` is the strcpy post (`CString new+|L| R`, the right tail with NUL). -/
theorem concatMiddle {Sfront M1 M1' M2 M2' Smid : Config → Prop}
    (memcpy : Triple M1 M1')           -- memcpy(new, L, |L|) callee
    (strcpy : Triple M2 M2')           -- strcpy(new+|L|, R) callee
    (seamMc : Triple Sfront M1)        -- malloc post ▷ mv a2,s2 ; mv a1,s3 ; jal memcpy
    (seamSc : Triple M1' M2)           -- memcpy post ▷ add a0,s0,s2 ; mv a1,s5 ; jal strcpy
    (seamEnd : Triple M2' Smid) :      -- strcpy post ▷ (into the free/box tail)
    Triple Sfront Smid :=
  callSeg (callSeg seamMc memcpy seamSc) strcpy seamEnd

/-! ## Tail sub-chain: `free(L-buf) ≫ free(R-buf) ≫ value_str`

Two `free`s (each popping a scratch-buffer `ext`; the arena's `freeSpec` — memory
frame no-ops on the public heap, `exts`-pop) then `value_str` boxes the fresh
`new` pointer into a `.str` value.  `Smid` (strcpy post) ▷ free-arg (`mv a0,s3`) ▷
free ▷ free-arg (`mv a0,s5`) ▷ free ▷ value_str-arg (`mv a1,s0 ; mv a0,s1`) ▷
value_str ▷ `j 800033ec`.  `Q` is the boxed `.str (sL ++ sR)` result (the whole-node
exit); the `value_str` seam carries the `concatReadback` CString obligation. -/
theorem concatTail {Smid F1 F1' F2 F2' V V' Q : Config → Prop}
    (free1 : Triple F1 F1')            -- free(L-buf) callee (ext popped)
    (free2 : Triple F2 F2')            -- free(R-buf) callee (ext popped)
    (valueStr : Triple V V')           -- value_str box callee
    (seamF1 : Triple Smid F1)          -- strcpy post ▷ mv a0,s3 ; jal free
    (seamF2 : Triple F1' F2)           -- ▷ mv a0,s5 ; jal free
    (seamV  : Triple F2' V)            -- ▷ mv a1,s0 ; mv a0,s1 ; jal value_str  (concatReadback)
    (seamQ  : Triple V' Q) :           -- value_str post ▷ j 800033ec  → boxed .str result
    Triple Smid Q :=
  callSeg (callSeg (callSeg seamF1 free1 seamF2) free2 seamV) valueStr seamQ

/-! ## `concatHeapCore` — the whole C-block, front ≫ middle ≫ tail

The three sub-chains composed at their shared seam predicates `Sfront` (malloc post)
and `Smid` (strcpy post) by two `Triple.seq`s.  This is the entire concat C-block
machine Triple as pure `callSeg` algebra over the eight named callee contracts + the
seven seam bridges — the model being `stringifyStrdupTailContract` (four bridges)
scaled to the concat's larger callee set, with the two `free` `exts`-pops threaded as
the `free1`/`free2` callee contracts. -/
theorem concatHeapCore
    {P S1 S1' S2 S2' Smpre Sfront M1 M1' M2 M2' Smid
     F1 F1' F2 F2' V V' Q : Config → Prop}
    -- front callees + seams
    (strlenL : Triple S1 S1') (strlenR : Triple S2 S2')
    (malloc : Triple Smpre Sfront)
    (seam0 : Triple P S1) (seam1 : Triple S1' S2) (seamM : Triple S2' Smpre)
    -- middle callees + seams
    (memcpy : Triple M1 M1') (strcpy : Triple M2 M2')
    (seamMc : Triple Sfront M1) (seamSc : Triple M1' M2) (seamEnd : Triple M2' Smid)
    -- tail callees + seams
    (free1 : Triple F1 F1') (free2 : Triple F2 F2') (valueStr : Triple V V')
    (seamF1 : Triple Smid F1) (seamF2 : Triple F1' F2) (seamV : Triple F2' V)
    (seamQ : Triple V' Q) :
    Triple P Q :=
  Triple.seq
    (Triple.seq
      (concatFront strlenL strlenR malloc seam0 seam1 seamM)
      (concatMiddle memcpy strcpy seamMc seamSc seamEnd))
    (concatTail free1 free2 valueStr seamF1 seamF2 seamV seamQ)

#print axioms concatFront
#print axioms concatMiddle
#print axioms concatTail
#print axioms concatHeapCore

end Vsa.Sim
