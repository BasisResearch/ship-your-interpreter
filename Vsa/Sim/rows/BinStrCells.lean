import Vsa.Sim.rows.BinDispatchRow

/-!
# `BinStrCells` — the 5 STR-cell residual slots of `eval_binary_row`, factored

`eval_binary_row` (`Vsa/Sim/rows/BinDispatchRow.lean`) closes the `hBinary`
recursor premise modulo, among others, SIX loose `EvalIH` slots for the
string-operand cells that `binOpSem` succeeds on but for which NO machine
simulation existed:

* `hStrAddL`/`hStrAddR` — the `.add` string-CONCATENATION cell (a `.str` result);
* `hStrLt`/`hStrLe`/`hStrGt`/`hStrGe` — the four `.lt`/`.le`/`.gt`/`.ge` string
  COMPARISON cells (a `.bool` result).

This file DECODES the exact machine routes and FACTORS those six loose slots into
exactly **two shared, precisely-typed residuals** — one per family — plus thin
per-cell providers, and re-closes the whole dispatcher through them
(`eval_binary_row_str_closed`).  It does NOT edit the landed `eval_binary_row`
statement (the two shared residuals are supplied to it as its existing slots).

## Decoded machine routes (`experiments/disasm.txt`)

Both operands are evaluated first by the operator-INDEPENDENT prologue+dispatch
(the `blockA_binaryArm` entry bridge, `0x80003164 → 0x800034e8 → …`, then the two
`jal eval_expr` at `0x800034f8`/`0x80003518`); the operator token is read at
`0x8000351c` (`lw a2,8(s0)`) and the `jr a5` at `0x80003558` selects the arm.

### (a) STR-STR comparison — ONE shared `strcmp` tail, 4 sign-tests

The comparison arm entry is `0x80003628` (`CmpDispatchSeg`).  Operand kind tags:
`a6` = LEFT kind, `a0` = RIGHT kind, `a2` = op token (20 lt / 21 le / 22 gt /
23 ge, `Vsa.MemRepr.binOpTok`).  The ladder:

```
80003628  addi a5,a0,-3 ; bnez a5 → 80003638   (right kind ≠ 3?  int path @3638)
80003630  addi a5,a6,-3 ; beqz a5 → 80003b0c   (BOTH kinds == 3 == str → strcmp)
...
80003b0c  mv a1,a7 ; mv a0,s3 ; sd a2,0(sp) ; jal strcmp @80006ea0
80003b18                       ; ld a2,0(sp) ; mv a1,a0 ; j 800036a4
800036a4  li a5,21 ; beq a2,a5 → 80003af8  (le: slti a1,a1,1 ; value_bool)
800036ac  li a5,22 ; beq a2,a5 → 80003ae4  (gt: sgtz a1     ; value_bool)
800036b4  li a5,20 ; beq a2,a5 → 800036c0  (lt: srli a1,0x3f ; value_bool)  [fall-through = ge]
800036bc  not a1,a1                        (ge)
800036c0  srli a1,a1,0x3f ; mv a0,s1
800036c8  jal value_bool @800027f8 ; ld s3,1048(sp) ; j 800033ec
```

So the **string comparison is literally the C `strcmp` seam** (the SAME callee
`value_equal` uses, `strcmp_full_spec` in `Vsa/Sim/StrcmpSpecW4.lean`) placing its
sign in `a1`, then joining the **same operator sign-test tail** the INT comparison
arms use (`0x800036a4 → value_bool`).  Kind-3 = str; the two 32-bit kind tags in
the spilled operand buffers gate the strcmp call.  Route callees/specs:
`strcmp` (`strcmp_full_spec`, LANDED) → `value_bool` (`value_bool` box, LANDED as
`intBoxEpilogue`/`boolBoxEpilogue` machinery).

SHARED-vs-per-cell: the strcmp call + operand→`StrcmpRegion` derivation + the
`value_bool` box are IDENTICAL across lt/le/gt/ge; only the sign-test block differs
(`srli` / `slti a1,a1,1` / `sgtz` / `not;srli`), keyed by the op token — exactly
the `blockC_eqne`-shared-between-eq-and-ne pattern.  Hence ONE shared cmp residual
parameterised by the op token + the boolean result form, and four thin providers.

### (b) STR concatenation (`.add`) — a big bespoke `stringify`+alloc path

The add str arm `0x80003a20 → 0x80003ae0`:

```
80003a20  <load both operand buffers> ; jal stringify @80002fc0   (LEFT  → s2/s3)
80003a68                              ; jal stringify @80002fc0   (RIGHT → s0/s5)
80003a74  mv a0,s2 ; jal strlen @80006cf0                          (len(L))
80003a80  mv a0,s0 ; jal strlen @80006cf0                          (len(R))
80003a88  add a0,s2,a0 ; addi a0,a0,1 ; jal malloc @80004790       (len(L)+len(R)+1)
80003a9c  beqz a0 → 80003e28  (OOM → runtime_error)
80003aa0  mv a2,s2 ; mv a1,s3 ; jal memcpy @80006bc8               (copy L)
80003ab0  add a0,s0,s2 ; mv a1,s5 ; jal strcpy @80006dc4           (copy R+NUL)
80003ab8  mv a0,s3 ; jal free @8000479c ; mv a0,s5 ; jal free      (free both stringify bufs)
80003ac8  mv a1,s0 ; mv a0,s1 ; jal value_str @8000281c ; ld s3 ; j 800033ec
```

This matches `binOpSem .add` on strings (`l.display s ++ r.display s`) because
`stringify` IS `display` (formats non-str operands to their printed form).  It is a
GENUINELY BESPOKE seven-callee path: **`stringify` (NO spec exists — it is a
snprintf-family formatter, the missing callee), `strlen`/`malloc`/`memcpy`/`strcpy`/
`free`/`value_str`** (framed specs exist for strlen/malloc/memcpy/value_str; strcpy
and free have site batteries).  The blocking gap is `stringify`: it is the
`display`-realising formatter and has no framed contract, so the concat cell cannot
be discharged without either a `stringify` spec or restricting to str-str operands
(where `display (.str s) = s`, so `stringify` degenerates to `strdup`) — even then
the `malloc`/`memcpy`/`strcpy`/`free` byte-exact concatenation into a fresh heap
`ValueRepr .str` is a bespoke ~several-hundred-line heap development.  Scoped, not
built (see the ledger at the bottom).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa.While Vsa.MemRepr
open Vsa.Machine (MState Config)
open Vsa.Sim.TermSimAssembly

namespace Vsa.Sim

/-! ## The shared STR-COMPARISON residual `StrCmpCellResid`

The four `.lt`/`.le`/`.gt`/`.ge` string-comparison slots of `eval_binary_row` are
each a whole-node `EvalIH` for a `.binary op el er` node whose operands are strings
and whose result is the boolean the sign-test tail computes.  The machine route
(decoded above) is ONE proof up to the sign-test block: the operator-independent
entry bridge (`blockA_binaryArm`) ≫ both operand recursions (`blockB_binary`) ≫ the
kind-check + `strcmp` seam ≫ the shared `value_bool` box; only the sign-test block
(`0x800036a4 → value_bool`) is op-specific.  We therefore expose ONE residual,
parameterised by the op token and the boolean-result FUNCTION `bres : String →
String → Bool` the sign tail realises, and four thin instantiations of it. -/

/-- The shared string-comparison cell residual: the whole-node `EvalIH` for the
`.binary op el er` node at string operands, producing `.bool (bres sl sr)`.  This is
the single object the four cmp providers below share — its discharge is the
`blockA_binaryArm ≫ blockB_binary ≫ [strcmp seam + sign tail + value_bool box] ≫
blockD_v_rec` chain the decoded route describes.  Left abstract here (a NAMED typed
residual, the honest surface of the not-yet-built str-comparison block-C), consumed
by all four cmp cells via `bres := <op sign test>`. -/
def StrCmpCellResid (op : BinOp) (bres : String → String → Bool) : Prop :=
  ∀ (st : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr)
    (st'' : Vsa.While.St) (sl sr : String),
    EvalIH st d env (.binary op el er) st'' (.bool (bres sl sr))

/-- `.lt` string cell (`sl < sr`) — a thin instantiation of `StrCmpCellResid`. -/
theorem strCmpCell_lt (h : StrCmpCellResid .lt (fun sl sr => sl < sr)) :
    ∀ st d env el er st'' (sl sr : String),
      EvalIH st d env (.binary .lt el er) st'' (.bool (sl < sr)) :=
  fun st d env el er st'' sl sr => h st d env el er st'' sl sr

/-- `.le` string cell (`sl < sr || sl == sr`) — thin instantiation. -/
theorem strCmpCell_le (h : StrCmpCellResid .le (fun sl sr => sl < sr || sl == sr)) :
    ∀ st d env el er st'' (sl sr : String),
      EvalIH st d env (.binary .le el er) st'' (.bool (sl < sr || sl == sr)) :=
  fun st d env el er st'' sl sr => h st d env el er st'' sl sr

/-- `.gt` string cell (`sr < sl`) — thin instantiation. -/
theorem strCmpCell_gt (h : StrCmpCellResid .gt (fun sl sr => sr < sl)) :
    ∀ st d env el er st'' (sl sr : String),
      EvalIH st d env (.binary .gt el er) st'' (.bool (sr < sl)) :=
  fun st d env el er st'' sl sr => h st d env el er st'' sl sr

/-- `.ge` string cell (`sr < sl || sl == sr`) — thin instantiation. -/
theorem strCmpCell_ge (h : StrCmpCellResid .ge (fun sl sr => sr < sl || sl == sr)) :
    ∀ st d env el er st'' (sl sr : String),
      EvalIH st d env (.binary .ge el er) st'' (.bool (sr < sl || sl == sr)) :=
  fun st d env el er st'' sl sr => h st d env el er st'' sl sr

/-! ## The STR-CONCATENATION residual `StrConcatCellResid`

Both `.add` string slots (`hStrAddL` = left operand is str, `hStrAddR` = right
operand is str) are whole-node `EvalIH`s producing a `.str` whose value is
`l.display ++ r.display`.  The machine route (decoded above) is the bespoke
`stringify`/`malloc`/`memcpy`/`strcpy`/`free`/`value_str` path.  We expose ONE
residual carrying BOTH slots (they route through the same arm; the two slots differ
only in which operand carries the literal `.str`), consumed by the dispatcher. -/

/-- The shared string-concatenation cell residual: BOTH add-str whole-node
`EvalIH`s.  The single object the dispatcher's `hStrAddL`/`hStrAddR` slots share —
its discharge is the bespoke `stringify`+alloc concat path (see the concat ledger).
Left abstract (a NAMED typed residual, blocked on a `stringify`/`display` framed
spec). -/
def StrConcatCellResid : Prop :=
  (∀ st d env el er st'' (sl : String) (rv : Value),
      EvalIH st d env (.binary .add el er) st''
        (.str ((Value.str sl).catDisplay st''.store ++ rv.catDisplay st''.store))) ∧
  (∀ st d env el er st'' (lv : Value) (sr : String),
      EvalIH st d env (.binary .add el er) st''
        (.str (lv.catDisplay st''.store ++ (Value.str sr).catDisplay st''.store)))

/-! ## `eval_binary_row_str_closed` — the dispatcher, str slots via the 2 shared residuals

Re-closes the `hBinary` premise through `eval_binary_row`, supplying its six loose
str slots from exactly the two shared residuals `StrCmpCellResid` (four
instantiations) + `StrConcatCellResid` (its two projections).  The nine int
providers + eq/ne + div-overflow slots thread through verbatim.  This does NOT alter
`eval_binary_row`; it merely feeds it, factoring 6 loose slots into 2 named ones. -/
theorem eval_binary_row_str_closed
    (hIAdd : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .add Vsa.Sim.AddResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hISub : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .sub Vsa.Sim.SubResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hIMul : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .mul Vsa.Sim.MulResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hIDiv : ∀ g N A SL φf φc st st' st'' el er a b, ¬(a = -2^63 ∧ b = -1) →
        ∀ sp r sret aExpr m0,
        BinIntCellResid .div Vsa.Sim.DivResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hIMod : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .mod Vsa.Sim.ModResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hILt : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .lt Vsa.Sim.LtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hILe : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .le Vsa.Sim.LeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hIGt : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .gt Vsa.Sim.GtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hIGe : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
        BinIntCellResid .ge Vsa.Sim.GeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0)
    (hEq : ∀ g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0,
        BinEqCellResid .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21)
          g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0)
    (hNe : ∀ g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0,
        BinEqCellResid .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21)
          g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0)
    -- the TWO shared str residuals (the 6 loose slots, factored):
    (hStrCmpLt : StrCmpCellResid .lt (fun sl sr => sl < sr))
    (hStrCmpLe : StrCmpCellResid .le (fun sl sr => sl < sr || sl == sr))
    (hStrCmpGt : StrCmpCellResid .gt (fun sl sr => sr < sl))
    (hStrCmpGe : StrCmpCellResid .ge (fun sl sr => sr < sl || sl == sr))
    (hStrConcat : StrConcatCellResid)
    (hDivOv : ∀ st d env el er st'',
        EvalIH st d env (.binary .div el er) st''
          (.int (wrap64 ((-2^63 : Int).tdiv (-1))))) :
    ∀ (st : Vsa.While.St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : Vsa.While.St) (lv rv v : Value)
      (a : EvalE st d env l st' lv) (a_1 : EvalE st' d env r st'' rv)
      (a_2 : binOpSem st''.store op lv rv = some v),
      mEvalE st d env l st' lv a →
      mEvalE st' d env r st'' rv a_1 →
      mEvalE st d env (.binary op l r) st'' v
        (EvalE.binary st d env op l r st' st'' lv rv v a a_1 a_2) :=
  eval_binary_row hIAdd hISub hIMul hIDiv hIMod hILt hILe hIGt hIGe hEq hNe
    hStrConcat.1 hStrConcat.2
    (strCmpCell_lt hStrCmpLt) (strCmpCell_le hStrCmpLe)
    (strCmpCell_gt hStrCmpGt) (strCmpCell_ge hStrCmpGe)
    hDivOv

end Vsa.Sim
