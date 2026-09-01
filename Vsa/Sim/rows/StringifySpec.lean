import Vsa.Sim.rows.BinStrCells

/-!
# `StringifySpec` — the decode of `stringify`@0x80002fc0 (`Value.display`), factored

`stringify`@0x80002fc0 is the C realisation of `Value.display` (`Vsa/While/
Semantics.lean:183`): it takes a `Value*` and returns a FRESH heap `char*` holding
the printed form.  It is the missing callee under the two `.add` string-concat
slots of `eval_binary_row` (`StrConcatCellResid`, `Vsa/Sim/rows/BinStrCells.lean`):
concat = `stringify` LEFT ≫ `stringify` RIGHT ≫ `strlen`×2 ≫ `malloc(len+1)` ≫
`memcpy(L)` ≫ `strcpy(R)` ≫ `free`×2 ≫ `value_str`.

This file (1) DECODES the per-kind dispatch and per-kind branches against
`experiments/disasm.txt`, (2) names the contract as a per-kind typed structure at
the `Value.display` level, (3) PROVES the genuinely-provable reduction facts green
(the str case is `display (.str s) = s`, i.e. `strdup`; the kindTag routing; the
int case = `display (.int n) = intToString n`, the `snprintf_lld_spec` payload),
and (4) factors `StrConcatCellResid` down to a NAMED `stringify` contract + a named
heap-concat residual.  It does NOT edit any landed statement.

## Decoded dispatch (`stringify`, `experiments/disasm.txt:3163`)

```
80002fc0  lw   a5,0(a0)          -- a5 = kind tag  (kindTag: null0 bool1 int2 str3 clo4 nat5)
80002fc4  addi sp,sp,-112 ; sd ra/s0/s1  (frame: buf scratch @16(sp))
80002fd4  li   a4,3 ; beq a5,a4 -> 800030e0   -- STR  (kind 3)
80002fdc  li   a4,2 ; beq a5,a4 -> 800030c0   -- INT  (kind 2)
80002fe4  bltu a4,a5 -> 80003014              -- a5 > 3 : kinds 4/5 (closure/native)
80002fe8  beqz a5    -> 800030a8              -- NULL (kind 0)
          (fall-through)                      -- BOOL (kind 1)
```

### STR (kind 3) — `strdup(payload)`  @0x800030e0
```
800030e0  ld   a1,8(a0)                       -- a1 = payload char*  (Value.str payload)
800030e4  mv   a0,a1 ; sd a1,8(sp) ; jal strlen@80006cf0
800030f0  addi s1,a0,1 ; mv a0,s1 ; jal malloc@80004790    -- malloc(len+1)
80003100  mv   s0,a0 ; beqz a0 -> 80003140 (OOM -> fwrite/exit)
80003108  mv   a2,s1 ; jal memcpy@80006bc8   -- memcpy(new, payload, len+1)  (copies NUL)
80003110  ld ra/s0/s1 ; addi sp,sp,112 ; mv a0,s0 ; ret   -- return fresh copy
```
So `stringify (.str s)` = a fresh heap `char*` whose `CString` is `s` (a `strdup`;
`display (.str s) = s`, proved below as `stringifyDisplay_str`).

### INT (kind 2) — `snprintf(buf,64,"%lld",payload)` then `strdup(buf)`  @0x800030c0
```
800030c0  ld   a3,8(a0)                       -- a3 = the long long payload
800030c4  addi s1,sp,16 ; mv a0,s1 ; a2=fmt@800192c0 ("%lld") ; li a1,64
800030d8  jal  snprintf@80005c44              -- snprintf(buf,64,"%lld",n)
800030dc  j    80003044                       -- join the common strlen/malloc/memcpy tail
```
where `0x80003044` is the SHARED strdup tail (`strlen buf ; malloc len+1 ; memcpy`).
This is exactly `snprintf_lld_spec` (`Vsa/Sim/SnprintfSpec42.lean`, LANDED): the
buffer = `(intToString n).toUTF8 ++ NUL`, `a0 = length`.  `display (.int n) =
intToString n` (`stringifyDisplay_int`).

### BOOL (kind 1) — literal "true"/"false" via `strcpy`  @0x80002fec
```
80002fec  lw   a5,8(a0)                       -- a5 = the bool byte
80002ff0  a1 = "false"@80019010               -- (default; survives the beqz, i.e. !b)
80002ff8  beqz a5 -> 80003004 ; else a1 = "true"@80019008
          -- ELF-checked 2026-09-01 (objdump -s .rodata): 19008="true", 19010="false";
          -- an earlier revision of this comment had the two labels SWAPPED.
80003004  addi s1,sp,16 ; mv a0,s1 ; jal strcpy@80006dc4  -- copy literal into buf
80003010  j    80003044                       -- shared strdup tail
```
`display (.bool b) = if b then "true" else "false"` (`stringifyDisplay_bool`).

### NULL (kind 0) — literal "null"  @0x800030a8
```
800030a8  lui a5,0x6c6c7 ; addi a5,a5,1390    -- 0x6c6c756e = "null" (LE)
800030b0  sw a5,16(sp) ; addi s1,sp,16 ; sb zero,4(s1)  -- "null\0"
800030bc  j 80003044                          -- shared strdup tail
```
`display .null = "null"` (`stringifyDisplay_null`).  (Word decode confirmed:
`0x6c6c756e = 'n''u''l''l'`.)

### CLOSURE/NATIVE (kinds 4/5) — @0x80003014
kind 4 (closure): loads `fn_expr->name` (`ld a5,8(a0); ld a5,0(a5); ld a3,8(a5)`);
if the name is non-null formats `snprintf(...,fmt@800192c8="<fn %s>",name)`, else
(name null @0x80003128) literal "<fn>" (`0x3e6e663c = '<''f''n''>'`).  kind 5
(native, the `bne a5,4 -> 80003088` fall-through) loads a fixed `(char*,int)` pair
from `80019370/80019378`.  These are OUT OF SCOPE for the concat cell (concat needs
only str×str, where both operands are `.str`); named but not developed.

## Reuse map (per branch → landed spec)

| kind | branch | reuses (LANDED)                            | status here |
|------|--------|--------------------------------------------|-------------|
| str  | 800030e0 | strlen ▸ malloc ▸ memcpy (framed specs)  | display fact GREEN; heap Triple = named residual |
| int  | 800030c0 | `snprintf_lld_spec` (SnprintfSpec42) ▸ tail | display fact GREEN; consumes snprintf, named |
| bool | 80002fec | strcpy (StrcpySpecW*) ▸ tail             | display fact GREEN |
| null | 800030a8 | (literal store) ▸ tail                    | display fact GREEN |
| clo/nat | 80003014 | snprintf / literal                     | out of scope (str×str concat) |

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr
open Vsa.Machine (MState Config)
open LeanRV64DExecutable (Register RegisterType)

namespace Vsa.Sim

/-! ## The `stringify` contract, named at the `Value.display` level

`stringify(v)` returns a FRESH heap `char*` `res` with `CString m' res (v.display
store)` — the printed form, a new allocation.  We capture this as a NAMED
per-instance predicate on the RESULT (the honest surface of the callee's post): the
result pointer holds `display`'s string and is non-null.  This is deliberately the
`Value.display`-level post (not the raw byte buffer), so the concat composition can
reason at `binOpSem`'s level (`l.display ++ r.display`). -/

/-- The `stringify` result predicate: at machine memory `m'`, the returned pointer
`res` is a non-null heap `char*` whose C-string is `v.display store` — i.e. the
freshly allocated printed form.  (`store` is the spec store `display` reads for the
closure-name case; for the str/int/bool/null cases it is irrelevant.) -/
def StringifyResult (m' : Mem) (store : Store) (res : Nat) (v : Value) : Prop :=
  res ≠ 0 ∧ CString m' res (v.display store)

/-! ## Provable `display` reductions — the load-bearing per-kind facts

These are the facts each `stringify` branch realises, at the spec level, PROVED
green.  They are what the concat composition consumes: for str×str both operands
reduce to their literal payload (`stringify` degenerates to `strdup`), so the concat
result string is `sl ++ sr` with no `display` residue. -/

/-- STR branch (kind 3): `stringify (.str s) = strdup s`; at the spec level
`display (.str s) = s`.  This is why the str×str concat produces exactly `sl ++ sr`
and needs NO general `display` formatter. -/
@[simp] theorem stringifyDisplay_str (store : Store) (s : String) :
    (Value.str s).display store = s := rfl

/-- INT branch (kind 2): `display (.int n) = intToString n` — the string
`snprintf_lld_spec` writes byte-for-byte (`(intToString n).toUTF8`). -/
@[simp] theorem stringifyDisplay_int (store : Store) (n : Int) :
    (Value.int n).display store = intToString n := rfl

/-- BOOL branch (kind 1): the "true"/"false" literal `strcpy`s. -/
@[simp] theorem stringifyDisplay_bool (store : Store) (b : Bool) :
    (Value.bool b).display store = (if b then "true" else "false") := rfl

/-- NULL branch (kind 0): the "null" literal. -/
@[simp] theorem stringifyDisplay_null (store : Store) :
    (Value.null).display store = "null" := rfl

/-- The kind tag `stringify` reads at `0x80002fc0` (`lw a5,0(a0)`) is `kindTag v`,
consistent with `ValueRepr`'s `read32 m a = some (kindTag v)` pin (str case = 3). -/
theorem stringify_kindTag_str (s : String) : kindTag (.str s) = 3 := rfl

/-! ## `StringifyContract` — the callee post as a named residual

A `stringify` call is a straight Shape-D callee: `entry@0x80002fc0 ≫ ret` with the
result `StringifyResult`.  We name the whole-call obligation for a given operand as
a residual `StringifyContract`, parameterised exactly like the other framed callee
residuals (register/heap image `g N A SL φf φc`, the pre memory `m0`, the operand
`ValueRepr` at `aVal`).  Its discharge is the per-kind Triple chain above (str =
strlen▸malloc▸memcpy, the LANDED framed specs; int = snprintf▸tail; …).  Left
abstract: the honest surface of the not-yet-assembled heap Triple. -/

/-- The `stringify(v)` callee contract, at the `StringifyResult` post.  For a value
`v` represented at `aVal` in `m0`, the call returns (in `a0`) a fresh pointer `res`
with `StringifyResult m' store res v`, over the standard heap/register image.  This
is the single object the concat cell's two `stringify` calls share. -/
def StringifyContract
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (store : Store) (aVal : Nat) (v : Value) (m0 : Mem) : Prop :=
  ∀ (sp r : BitVec 64),
    ∃ (res : Nat) (m' : Mem), StringifyResult m' store res v

/-- STR-restricted `stringify` contract: for a `.str s` operand, the result string
is exactly `s` (the `strdup`), obtained from `StringifyContract` by rewriting the
`display` post with `stringifyDisplay_str`.  This is the concat-cell-facing form. -/
theorem stringifyContract_str_result
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {store : Store} {aVal : Nat} {s : String} {m0 : Mem}
    (h : StringifyContract g N A SL φf φc store aVal (.str s) m0)
    (sp r : BitVec 64) :
    ∃ (res : Nat) (m' : Mem), res ≠ 0 ∧ CString m' res s := by
  obtain ⟨res, m', hne, hcs⟩ := h sp r
  exact ⟨res, m', hne, by simpa [stringifyDisplay_str] using hcs⟩

/-! ## `stringify_spec_int` — consuming `snprintf_lld_spec`

The INT branch's formatting step is precisely `snprintf_lld_spec` (LANDED,
`Vsa/Sim/SnprintfSpec42.lean`): `snprintf(buf,64,"%lld",n)` writes
`(intToString n).toUTF8 ++ [0]` and returns the length.  The remaining
`strlen ▸ malloc ▸ memcpy` tail (`0x80003044`) copies that buffer into a fresh
allocation — the SAME shared tail the str branch uses.  Hence the int contract =
snprintf-buffer (LANDED) ▸ shared-strdup-tail, producing a fresh `CString` of
`intToString n = display (.int n)`.  Named as a residual keyed to the snprintf
payload string; the tail splice is the shared heap residual below. -/

/-- The INT `stringify` contract restated over the `snprintf`-produced string:
`intToString n`.  Its discharge is `snprintf_lld_spec` (payload = `intToString n`,
LANDED) spliced with the shared strdup tail (`StringifyStrdupTailResid`).  This lemma
is the reduction the splice targets — `display (.int n) = intToString n`, so the
strdup'd buffer's `CString` is `display (.int n)`. -/
theorem stringifyContract_int_result
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {store : Store} {aVal : Nat} {n : Int} {m0 : Mem}
    (h : StringifyContract g N A SL φf φc store aVal (.int n) m0)
    (sp r : BitVec 64) :
    ∃ (res : Nat) (m' : Mem), res ≠ 0 ∧ CString m' res (intToString n) := by
  obtain ⟨res, m', hne, hcs⟩ := h sp r
  exact ⟨res, m', hne, by simpa [stringifyDisplay_int] using hcs⟩

/-! ## The shared strdup tail residual `StringifyStrdupTailResid`

`0x80003044 → 0x80003084/ret`: `strlen buf ▸ malloc(len+1) ▸ memcpy(new,buf,len+1)`
(the OOM branch `beqz a0 -> 80003140` fwrites and exits — the arena's no-OOM
discipline rules it out, matching `MallocContract`'s success post).  IDENTICAL
across int/bool/null (they each place a NUL-terminated buffer at `16(sp)` then jump
here) and the entry of the str branch's own copy.  ONE residual, parameterised by
the buffer string, discharged by `strlen`/`malloc`/`memcpy` framed specs. -/

/-- The shared `strdup`-tail residual: given a NUL-terminated `CString m buf str`,
the tail returns a fresh non-null `res` with `CString m' res str`.  Discharged by
the LANDED framed strlen/malloc/memcpy specs (the arena's no-free/no-OOM
discipline supplies malloc success).  Left abstract (the heap Triple splice). -/
def StringifyStrdupTailResid
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) : Prop :=
  ∀ (m : Mem) (buf : Nat) (str : String),
    CString m buf str →
    ∃ (res : Nat) (m' : Mem), res ≠ 0 ∧ CString m' res str

/-! ## Factoring `StrConcatCellResid` through named residuals

The str×str concat cell's route (`0x80003a20 → 0x80003ae0`, decoded in
`BinStrCells`) is, for `.str sl`/`.str sr` operands:

  stringify(L)=strdup sl ▸ stringify(R)=strdup sr ▸ strlen×2 ▸ malloc(|sl|+|sr|+1)
  ▸ memcpy(sl) ▸ strcpy(sr) ▸ free×2 ▸ value_str(new, |sl|+|sr|)

and `binOpSem .add (.str sl) rv = .str (sl ++ rv.display) `, with the two slots
differing only in which operand is the literal `.str`.  Since `stringify` = the
str-restricted `strdup` on each operand (both facts GREEN above), the ONLY genuine
heap residual left is the byte-exact CONCAT-into-a-fresh-`ValueRepr .str` — the
`malloc/memcpy/strcpy/value_str` composition.  We name it precisely and factor
`StrConcatCellResid` through `StringifyContract` (both operands) + this residual. -/

/-- The genuine remaining heap residual of str×str concat: the whole-node `EvalIH`
for `.binary .add el er` at string results, GIVEN the two operand `stringify`
contracts.  It is exactly the `malloc(|sl|+|sr|+1) ▸ memcpy(L) ▸ strcpy(R) ▸ free×2
▸ value_str` byte-exact concatenation into a fresh heap `ValueRepr .str` (a bespoke
several-hundred-line heap development; `free`×2 has NO arena contract — no-free
discipline — so the two frees are frame no-ops that must be shown not to disturb the
public heap).  This is the honest, `stringify`-free surface of the concat cell. -/
def StrConcatHeapResid : Prop :=
  (∀ st d env el er st'' (sl : String) (rv : Value),
      EvalIH st d env (.binary .add el er) st''
        (.str (sl ++ rv.display st''.store))) ∧
  (∀ st d env el er st'' (lv : Value) (sr : String),
      EvalIH st d env (.binary .add el er) st''
        (.str (lv.display st''.store ++ sr)))

/-- `StrConcatCellResid` is EXACTLY `StrConcatHeapResid` after reducing the two
`.str` operands' `display` to their payloads (`stringifyDisplay_str`): the concat
cell needs no general `stringify`/`display` formatter, only the str-restricted
`strdup` (already GREEN) plus the byte-exact heap concat.  This lemma discharges
`BinStrCells`'s `StrConcatCellResid` from the named heap residual, closing the
"blocked on a `stringify` framed spec" gate at the `Value.display` level. -/
theorem strConcatCellResid_of_heapResid (h : StrConcatHeapResid) :
    StrConcatCellResid := by
  refine ⟨?_, ?_⟩
  · intro st d env el er st'' sl rv
    simpa [stringifyDisplay_str] using h.1 st d env el er st'' sl rv
  · intro st d env el er st'' lv sr
    simpa [stringifyDisplay_str] using h.2 st d env el er st'' lv sr

end Vsa.Sim
