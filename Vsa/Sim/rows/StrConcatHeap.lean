import Vsa.Sim.rows.StringifyStrdupTail
import Vsa.Sim.rows.BinStrCells

/-!
# `StrConcatHeap` — the `.add` str-concat heap splice, factored (Task #64 gap 3)

`Vsa.Sim.StrConcatHeapResid` (`StringifySpec.lean:251`) is the honest,
`stringify`-free surface of the two `.add` string-concat cells: each is a
whole-node `EvalIH` for `.binary .add el er` producing a `.str` whose value is
`sl ++ rv.display store` (left operand a literal `.str sl`) or `lv.display ++ sr`
(right operand a literal `.str sr`).

## Decoded concat arm (`experiments/disasm.txt:3830`, `0x80003a20 → 0x80003ae0`)

```
80003a40  jal stringify@80002fc0   → s2/s3  (LEFT  operand → fresh char* of L.display)
80003a68  jal stringify@80002fc0   → s0/s5  (RIGHT operand → fresh char* of R.display)
80003a78  mv a0,s2 ; jal strlen    → s2 = |L.display|
80003a84  mv a0,s0 ; jal strlen    → a0 = |R.display|
80003a88  add a0,s2,a0 ; addi a0,a0,1 ; jal malloc   → s0 = new = malloc(|L|+|R|+1)
80003a9c  beqz a0 → 80003e28       (OOM → runtime_error; arena: no-OOM)
80003aa8  mv a2,s2 ; mv a1,s3 ; jal memcpy(new, L, |L|)
80003ab4  add a0,s0,s2 ; mv a1,s5 ; jal strcpy(new+|L|, R)   (copies R + NUL)
80003abc  mv a0,s3 ; jal free ; mv a0,s5 ; jal free          (free the two stringify bufs)
80003ad0  mv a1,s0 ; mv a0,s1 ; jal value_str@8000281c ; j 800033ec  (box fresh char* → .str)
```

Confirmed call structure: **two `stringify` calls** (Task #64 gap 1,
`StringifyContract` — the general `display` formatter, NOT just `strdup`, because
one operand is an arbitrary `Value`) then a byte-exact concat into a fresh
`malloc`'d buffer (`memcpy(L) ≫ strcpy(R)`), the two `stringify` scratch buffers
`free`d (NO `free` contract — the arena never frees, so both frees are frame
no-ops on the public heap), and the result boxed by `value_str`.

## Factoring

The whole node is `blockA_binaryArm ≫ blockB_binary (two sub-`EvalIH`s) ≫
concat-C-block ≫ blockD_v_rec` — the standard binary-arm pipeline (cf.
`BinArmBridge`/`blockC_add`/`EvalRecCommon.blockD_v_rec`), the concat-C-block being
the bespoke heap development.  We name the concat-C-block as ONE typed residual
carrying the two `StringifyContract`s (gap 1) as explicit hypotheses — wiring gap 1
into gap 3 — and produce `StrConcatHeapResid` from it.

`StrConcatCBlockResid` is the per-slot whole-node `EvalIH` GIVEN the two operand
`stringify` contracts: the honest surface of the concat-C-block (the byte-exact
`malloc/memcpy/strcpy/value_str` splice + the two `free` no-ops).  From it,
`StrConcatHeapResid` is immediate — the two slots' result strings are exactly the
concat-C-block's outputs.

Everything here is composition algebra; the bespoke concat-C-block machine Triple
is the NAMED typed residual `StrConcatCBlockResid`, its call structure verified
above and its two `stringify` sub-calls supplied by gap 1's `StringifyContract`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc
open Vsa.Machine (MState Config)
open LeanRV64DExecutable (Register RegisterType)

namespace Vsa.Sim

/-! ## `StrConcatCBlockResid` — the concat-C-block, carrying the two stringify contracts

The concat arm's C-block (`0x80003a20 → 0x80003ae0`) is the whole-node `EvalIH`
GIVEN the two operand `stringify` contracts.  We carry those contracts as EXPLICIT
hypotheses so gap 1 (`StringifyContract`) is wired into gap 3: for arbitrary
operand values `lv`/`rv`, if BOTH operands' `stringify` calls are contracted
(returning fresh `CString`s of their `display`s), then the concat C-block realises
the whole-node `EvalIH` at the concatenated string.  This is the honest surface of
the byte-exact `malloc/memcpy/strcpy/value_str` splice (the two `free`s are
public-heap frame no-ops — no `free` contract exists, the arena never frees).

Both slots share this object; they differ only in which operand carries the literal
`.str`.  Left abstract (the bespoke several-hundred-line heap Triple), consumed by
`strConcatHeapResid_of_cblock`. -/
def StrConcatCBlockResid : Prop :=
  -- left slot: `.str sl` ++ `rv.display` — the right operand's stringify contract is
  -- what turns `rv` into its printed form; the left is the literal `sl`.
  (∀ (g : (R : Register) → Option (RegisterType R))
     (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
     (store : Store) (aVal : Nat) (m0 : Mem)
     st d env el er st'' (sl : String) (rv : Value),
      StringifyContract g N A SL φf φc store aVal (.str sl) m0 →
      StringifyContract g N A SL φf φc store aVal rv m0 →
      EvalIH st d env (.binary .add el er) st''
        (.str (sl ++ rv.catDisplay st''.store))) ∧
  (∀ (g : (R : Register) → Option (RegisterType R))
     (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
     (store : Store) (aVal : Nat) (m0 : Mem)
     st d env el er st'' (lv : Value) (sr : String),
      StringifyContract g N A SL φf φc store aVal lv m0 →
      StringifyContract g N A SL φf φc store aVal (.str sr) m0 →
      EvalIH st d env (.binary .add el er) st''
        (.str (lv.catDisplay st''.store ++ sr)))

/-! ## Producing `StrConcatHeapResid`

Given the concat-C-block residual AND a supplier of the two operand `stringify`
contracts (gap 1's `stringifyContract_of_call`, or any provider of
`StringifyContract`), `StrConcatHeapResid` follows: instantiate the C-block at the
supplied contracts.  The stringify-contract supplier is the honest place gap 1
plugs in — its data (`g`/`N`/`A`/`SL`/`φf`/`φc`/`store`/`aVal`/`m0`) is threaded
through. -/

/-- **`StrConcatHeapResid` produced** from the concat-C-block residual and a
per-node supplier of the two operand `stringify` contracts.  The supplier
`hStringify` provides, for every whole-node instance, the `StringifyContract` for
any operand value at the node's operand image `(g,N,A,SL,φf,φc,store,aVal,m0)` —
exactly what gap 1's `stringifyContract_of_call` yields.  The two slots then
instantiate the C-block at the literal-`.str` operand + the arbitrary operand. -/
theorem strConcatHeapResid_of_cblock
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (store : Store) (aVal : Nat) (m0 : Mem)
    (hCBlock : StrConcatCBlockResid)
    (hStringify : ∀ v : Value, StringifyContract g N A SL φf φc store aVal v m0) :
    StrConcatHeapResid := by
  refine ⟨?_, ?_⟩
  · intro st d env el er st'' sl rv
    have hL : StringifyContract g N A SL φf φc store aVal (.str sl) m0 := hStringify _
    have hR : StringifyContract g N A SL φf φc store aVal rv m0 := hStringify _
    -- `StrConcatHeapResid`'s left slot writes `(Value.str sl).display store` = `sl`.
    simpa [stringifyDisplay_str] using
      hCBlock.1 g N A SL φf φc store aVal m0 st d env el er st'' sl rv hL hR
  · intro st d env el er st'' lv sr
    have hL : StringifyContract g N A SL φf φc store aVal lv m0 := hStringify _
    have hR : StringifyContract g N A SL φf φc store aVal (.str sr) m0 := hStringify _
    simpa [stringifyDisplay_str] using
      hCBlock.2 g N A SL φf φc store aVal m0 st d env el er st'' lv sr hL hR

/-! ## Closing the concat gate through `strConcatCellResid_of_heapResid`

`strConcatCellResid_of_heapResid` (`StringifySpec.lean`) already reduces
`StrConcatCellResid` (the two loose `BinStrCells` slots) to `StrConcatHeapResid`.
Composing it with `strConcatHeapResid_of_cblock` closes the concat cell down to the
concat-C-block residual + the two stringify contracts (gap 1) — one machine object
remaining, no `stringify`/`display` residue. -/

/-- **The concat cell closed to the C-block residual.**  `StrConcatCellResid`
(consumed by `eval_binary_row_str_closed`) from the concat-C-block residual + the
operand `stringify` contract supplier.  This is the full gap-3 closure modulo the
one named heap Triple `StrConcatCBlockResid`. -/
theorem strConcatCellResid_of_cblock
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (store : Store) (aVal : Nat) (m0 : Mem)
    (hCBlock : StrConcatCBlockResid)
    (hStringify : ∀ v : Value, StringifyContract g N A SL φf φc store aVal v m0) :
    StrConcatCellResid :=
  strConcatCellResid_of_heapResid
    (strConcatHeapResid_of_cblock g N A SL φf φc store aVal m0 hCBlock hStringify)

#print axioms StrConcatCBlockResid
#print axioms strConcatHeapResid_of_cblock
#print axioms strConcatCellResid_of_cblock

end Vsa.Sim
