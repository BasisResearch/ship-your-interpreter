import Vsa.Sim.rows.StringifyStrdupTail

/-!
# `StringifyBridge` — stringify ↔ `Value.catDisplay`: the literal byte pins,
the per-kind branch closures, and the whole-`∀ v` contract assembler

The concat cell's `∀ v` stringify supplier (`strConcatHeapResid_of_cblock`'s
`hStringify`) needs `StringifyContract` at EVERY `Value` constructor.  The str
and int branches are closed (`stringifyContract_of_call` /
`stringifyContract_int_of_call`); this file closes the remaining spec-side
surface:

* **§1 `AsciiZAt` + `cstring_of_asciiZAt`** — ONE generic fold from a pinned
  NUL-terminated ASCII byte run to `CString` (the fact every literal branch
  reads back; factors the four per-literal `CStr.cons` chains into one lemma).
* **§2 the `.rodata` literal pins** — `BoolNullLitsLoaded` /
  `NativeFnLitLoaded`, byte-for-byte off the sha-guarded proof ELF
  (`c/while-riscv-htif.elf`, file offset = VA − `0x80000000` + `0x1000`):
  `0x80019008 = "true\0"`, `0x80019010 = "false\0"`, `0x80019018 = "null\0"`
  (the run1-brief pin fix — an older doc had true/false SWAPPED — re-verified
  2026-09-01 against the raw bytes), `0x80019370 = "<native fn>\0"`.
* **§3 the literal `CString` facts** — `cstring_true_of` / `cstring_false_of`
  / `cstring_null_of` / `cstring_nativeFn_of` (what the bool arm's `strcpy`
  SOURCE and the value-print `fwrite("null")` arm read), plus the null
  branch's in-place word decomposition `cstring_null_of_wordBytes`
  (`sw 0x6c6c756e ; sb zero` — `stringify`'s null arm materialises the
  literal rather than reading `.rodata`).
* **§4 the bool/null/native branch closures** — `BoolBranchCallResid` /
  `NullBranchCallResid` / `NativeBranchCallResid` + their
  `stringifyContract_*_of_call` dischargers through the SHARED strdup tail,
  mirroring `StringifyIntTail` exactly (each branch's honest residual = ONE
  named arm-staging seam; the tail is the landed
  `stringifyStrdupTailContract`).  The NATIVE branch renders the NAMELESS
  `"<native fn>"` — `Value.catDisplay`, NOT `Value.display` (falsity
  `stringify-native-name-mismatch`, empirically confirmed on the Sail-model
  emulator 2026-09-01: `println("x" + println)` prints `x<native fn>`).
* **§5 `stringifyContract_of_kinds`** — the `∀ v` assembler: six
  per-constructor suppliers → the exact `hStringify` premise
  `strConcatHeapResid_of_cblock` consumes.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.While (Value Store Addr NativeFn)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc

namespace Vsa.Sim

/-! ## §1 `AsciiZAt` — a pinned NUL-terminated ASCII byte run, folded to `CString`

The single generic reader every literal branch shares: a list of nonzero ASCII
bytes at `a` followed by a NUL is a `CStr`/`CString` of the corresponding
codepoint string.  (Factored per Law 3: four hand `CStr.cons` chains — true /
false / null / `<native fn>` — become one fold + one `decide` each.) -/

/-- The bytes `bs` (each nonzero ASCII) at `a, a+1, …`, then a NUL terminator. -/
def AsciiZAt (m : Mem) : Nat → List (BitVec 8) → Prop
  | a, [] => m[a]? = some 0
  | a, b :: bs => m[a]? = some b ∧ b ≠ 0 ∧ b.toNat < 128 ∧ AsciiZAt m (a + 1) bs

/-- Fold an `AsciiZAt` run into the `CStr` of its codepoint chars.  (This is the
named consumer of `AsciiZAt`'s cons cell — all other consumers go through
`cstring_of_asciiZAt`.) -/
theorem cstr_of_asciiZAt (m : Mem) :
    ∀ (bs : List (BitVec 8)) (a : Nat), AsciiZAt m a bs →
      CStr m a (bs.map (fun b => Char.ofNat b.toNat))
  | [], _, h => CStr.nil h
  | _ :: bs, a, h => CStr.cons h.1 h.2.1 h.2.2.1 (cstr_of_asciiZAt m bs (a + 1) h.2.2.2)

/-- `AsciiZAt` run + a (decidable) string identification ⇒ `CString`. -/
theorem cstring_of_asciiZAt {m : Mem} {bs : List (BitVec 8)} {a : Nat} {s : String}
    (h : AsciiZAt m a bs)
    (hs : s = String.ofList (bs.map (fun b => Char.ofNat b.toNat))) :
    CString m a s :=
  ⟨_, cstr_of_asciiZAt m bs a h, hs⟩

/-! ## §2 the `.rodata` literal byte pins

Byte-for-byte off the proof ELF (sha256
`b146c6edb76ea9a0f0f30be381f8176ed2de9717e1ae9b37feff4b2b9ca1d0f0`), re-read
2026-09-01: file offset `0x1a008` = VA `0x80019008`.  The bool arm of
`stringify` (`0x80002ff0/80002ff8`) stages `a1 = 0x80019010` ("false", the
fall-through default) or `a1 = 0x80019008` ("true"); `value_print`'s null arm
`fwrite`s from `0x80019018`; `stringify`'s kind-5 default arm copies from
`0x80019370`. -/

/-- `"true\0"` @ `0x80019008`, `"false\0"` @ `0x80019010`, `"null\0"` @
`0x80019018` (ELF-checked; the OLD prose that swapped true/false was wrong). -/
def BoolNullLitsLoaded (mem : Mem) : Prop :=
  AsciiZAt mem 0x80019008 [0x74, 0x72, 0x75, 0x65] ∧
  AsciiZAt mem 0x80019010 [0x66, 0x61, 0x6c, 0x73, 0x65] ∧
  AsciiZAt mem 0x80019018 [0x6e, 0x75, 0x6c, 0x6c]

/-- `"<native fn>\0"` @ `0x80019370` — the NAMELESS native rendering
`stringify`'s default arm copies (`interp.c:101`). -/
def NativeFnLitLoaded (mem : Mem) : Prop :=
  AsciiZAt mem 0x80019370
    [0x3c, 0x6e, 0x61, 0x74, 0x69, 0x76, 0x65, 0x20, 0x66, 0x6e, 0x3e]

/-! ## §3 the literal `CString` facts -/

theorem cstring_true_of {m : Mem} (h : BoolNullLitsLoaded m) :
    CString m 0x80019008 "true" :=
  cstring_of_asciiZAt h.1 (by decide)

theorem cstring_false_of {m : Mem} (h : BoolNullLitsLoaded m) :
    CString m 0x80019010 "false" :=
  cstring_of_asciiZAt h.2.1 (by decide)

theorem cstring_null_of {m : Mem} (h : BoolNullLitsLoaded m) :
    CString m 0x80019018 "null" :=
  cstring_of_asciiZAt h.2.2 (by decide)

theorem cstring_nativeFn_of {m : Mem} (h : NativeFnLitLoaded m) :
    CString m 0x80019370 "<native fn>" :=
  cstring_of_asciiZAt h (by decide)

/-- The bool literal, selected: the arm's staged source pointer holds exactly
`(Value.bool b).catDisplay store` (=`stringifyDisplay_bool`), at
`0x80019008`/`0x80019010` by `b`.  The single fact the bool arm's `strcpy`
splice consumes. -/
theorem cstring_boolLit_of {m : Mem} (h : BoolNullLitsLoaded m) (b : Bool) :
    CString m (if b then 0x80019008 else 0x80019010) (if b then "true" else "false") := by
  cases b
  · exact cstring_false_of h
  · exact cstring_true_of h

/-- **The null arm's in-place literal** (`0x800030a8`): `sw a5,16(sp)` with
`a5 = 0x6c6c756e` then `sb zero,4(s1)` writes exactly the little-endian bytes
`'n' 'u' 'l' 'l' 0` at `buf` — for ANY `buf` whose five bytes read back so,
`CString m buf "null"`.  (Word decode: `0x6c6c756e = 'n''u''l''l'` LE.) -/
theorem cstring_null_of_wordBytes {m : Mem} {buf : Nat}
    (h0 : m[buf]? = some 0x6e) (h1 : m[buf + 1]? = some 0x75)
    (h2 : m[buf + 2]? = some 0x6c) (h3 : m[buf + 3]? = some 0x6c)
    (h4 : m[buf + 4]? = some 0) :
    CString m buf "null" :=
  cstring_of_asciiZAt
    (bs := [0x6e, 0x75, 0x6c, 0x6c])
    ⟨h0, by decide, by decide, h1, by decide, by decide, h2, by decide, by decide,
     h3, by decide, by decide, h4⟩
    (by decide)

/-! ## §4 the bool / null / native branch closures through the shared strdup tail

Exactly the `StringifyIntTail` shape: each branch's whole-call Triple from the
callee-entry setup `Pentry sp r` to `StrdupTailExit rRet <literal>`; its
interior is the branch's literal staging (`strcpy` from §3's pinned source, or
the null arm's word store, §3's `cstring_null_of_wordBytes`) ≫ the LANDED
`stringifyStrdupTailContract`.  Each residual is the ONE named arm seam; the
`_of_halves` composers split it at the shared-tail entry. -/

/-- The bool-branch whole-call residual: entry ≫ (kind dispatch ≫ literal
`strcpy` from §3's `cstring_boolLit_of` source ≫ `j 0x80003044`) ≫ strdup tail,
landing the boxed literal.  Named, not fabricated (cf. `IntBranchCallResid`). -/
def BoolBranchCallResid (b : Bool) (rRet : BitVec 64)
    (Pentry : BitVec 64 → BitVec 64 → Config → Prop) : Prop :=
  ∀ (sp r : BitVec 64),
    Triple (Pentry sp r) (StrdupTailExit rRet (if b then "true" else "false"))

/-- The null-branch whole-call residual (word-store literal, §3's
`cstring_null_of_wordBytes` interior). -/
def NullBranchCallResid (rRet : BitVec 64)
    (Pentry : BitVec 64 → BitVec 64 → Config → Prop) : Prop :=
  ∀ (sp r : BitVec 64), Triple (Pentry sp r) (StrdupTailExit rRet "null")

/-- The native-branch whole-call residual: the kind-5 default arm copies the
NAMELESS `"<native fn>"` (§3's `cstring_nativeFn_of` source) — the
`catDisplay` rendering, NOT `display`'s named form. -/
def NativeBranchCallResid (rRet : BitVec 64)
    (Pentry : BitVec 64 → BitVec 64 → Config → Prop) : Prop :=
  ∀ (sp r : BitVec 64), Triple (Pentry sp r) (StrdupTailExit rRet "<native fn>")

/-- **`StringifyContract` for `.bool b`, discharged** through the shared strdup
tail (`stringifyContract_of_call` at `v := .bool b`, aligned by
`stringifyDisplay_bool`). -/
theorem stringifyContract_bool_of_call
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (store : Store) (aVal : Nat) (b : Bool) (m0 : Mem)
    (rRet : BitVec 64) (Pentry : BitVec 64 → BitVec 64 → Config → Prop)
    (call : BoolBranchCallResid b rRet Pentry)
    (entry : ∀ (sp r : BitVec 64), ∃ c, Pentry sp r c) :
    StringifyContract g N A SL φf φc store aVal (.bool b) m0 :=
  stringifyContract_of_call g N A SL φf φc store aVal (.bool b) m0 rRet Pentry
    (fun sp r => by rw [stringifyDisplay_bool]; exact call sp r)
    entry

/-- **`StringifyContract` for `.null`, discharged** (aligned by
`stringifyDisplay_null`). -/
theorem stringifyContract_null_of_call
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (store : Store) (aVal : Nat) (m0 : Mem)
    (rRet : BitVec 64) (Pentry : BitVec 64 → BitVec 64 → Config → Prop)
    (call : NullBranchCallResid rRet Pentry)
    (entry : ∀ (sp r : BitVec 64), ∃ c, Pentry sp r c) :
    StringifyContract g N A SL φf φc store aVal .null m0 :=
  stringifyContract_of_call g N A SL φf φc store aVal .null m0 rRet Pentry
    (fun sp r => by rw [stringifyDisplay_null]; exact call sp r)
    entry

/-- **`StringifyContract` for `.native w`, discharged** (aligned by
`stringifyDisplay_native` — the `catDisplay` nameless form; this is the
constructor the display→catDisplay amendment makes TRUE). -/
theorem stringifyContract_native_of_call
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (store : Store) (aVal : Nat) (w : NativeFn) (m0 : Mem)
    (rRet : BitVec 64) (Pentry : BitVec 64 → BitVec 64 → Config → Prop)
    (call : NativeBranchCallResid rRet Pentry)
    (entry : ∀ (sp r : BitVec 64), ∃ c, Pentry sp r c) :
    StringifyContract g N A SL φf φc store aVal (.native w) m0 :=
  stringifyContract_of_call g N A SL φf φc store aVal (.native w) m0 rRet Pentry
    (fun sp r => by rw [stringifyDisplay_native]; exact call sp r)
    entry

/-- Bool branch from its two halves: the named arm seam (dispatch ≫ literal
`strcpy` ≫ `j`-join, landing the tail entry `Ptail`) ≫ the composed tail. -/
theorem boolBranchCallResid_of_halves
    (b : Bool) (rRet : BitVec 64)
    (Pentry Ptail : BitVec 64 → BitVec 64 → Config → Prop)
    (armSeam : ∀ (sp r : BitVec 64), Triple (Pentry sp r) (Ptail sp r))
    (strdupTail : ∀ (sp r : BitVec 64),
      Triple (Ptail sp r) (StrdupTailExit rRet (if b then "true" else "false"))) :
    BoolBranchCallResid b rRet Pentry :=
  fun sp r => Triple.seq (armSeam sp r) (strdupTail sp r)

/-- Null branch from its two halves. -/
theorem nullBranchCallResid_of_halves
    (rRet : BitVec 64) (Pentry Ptail : BitVec 64 → BitVec 64 → Config → Prop)
    (armSeam : ∀ (sp r : BitVec 64), Triple (Pentry sp r) (Ptail sp r))
    (strdupTail : ∀ (sp r : BitVec 64),
      Triple (Ptail sp r) (StrdupTailExit rRet "null")) :
    NullBranchCallResid rRet Pentry :=
  fun sp r => Triple.seq (armSeam sp r) (strdupTail sp r)

/-- Native branch from its two halves. -/
theorem nativeBranchCallResid_of_halves
    (rRet : BitVec 64) (Pentry Ptail : BitVec 64 → BitVec 64 → Config → Prop)
    (armSeam : ∀ (sp r : BitVec 64), Triple (Pentry sp r) (Ptail sp r))
    (strdupTail : ∀ (sp r : BitVec 64),
      Triple (Ptail sp r) (StrdupTailExit rRet "<native fn>")) :
    NativeBranchCallResid rRet Pentry :=
  fun sp r => Triple.seq (armSeam sp r) (strdupTail sp r)

/-! ## §5 the `∀ v` contract assembler

`strConcatHeapResid_of_cblock` (`rows/StrConcatHeap.lean`) consumes
`hStringify : ∀ v : Value, StringifyContract g N A SL φf φc store aVal v m0`.
Assemble it from six per-constructor suppliers — the four literal/formatted
branches closed above (+ `StringifyIntTail`), the str strdup branch, and the
closure branch (the `"<fn %s>"`/`"<fn>"` snprintf arm; its supplier is
`stringifyContract_of_call` at `v := .closure a`, residual = its arm seam). -/

/-- The `∀ v` stringify-contract supplier from per-constructor suppliers —
exactly the `hStringify` premise of `strConcatHeapResid_of_cblock`. -/
theorem stringifyContract_of_kinds
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {store : Store} {aVal : Nat} {m0 : Mem}
    (hNull : StringifyContract g N A SL φf φc store aVal .null m0)
    (hBool : ∀ b, StringifyContract g N A SL φf φc store aVal (.bool b) m0)
    (hInt : ∀ n, StringifyContract g N A SL φf φc store aVal (.int n) m0)
    (hStr : ∀ s, StringifyContract g N A SL φf φc store aVal (.str s) m0)
    (hClosure : ∀ a, StringifyContract g N A SL φf φc store aVal (.closure a) m0)
    (hNative : ∀ w, StringifyContract g N A SL φf φc store aVal (.native w) m0) :
    ∀ v : Value, StringifyContract g N A SL φf φc store aVal v m0
  | .null => hNull
  | .bool b => hBool b
  | .int n => hInt n
  | .str s => hStr s
  | .closure a => hClosure a
  | .native w => hNative w

#print axioms cstr_of_asciiZAt
#print axioms cstring_of_asciiZAt
#print axioms cstring_true_of
#print axioms cstring_false_of
#print axioms cstring_null_of
#print axioms cstring_nativeFn_of
#print axioms cstring_boolLit_of
#print axioms cstring_null_of_wordBytes
#print axioms stringifyContract_bool_of_call
#print axioms stringifyContract_null_of_call
#print axioms stringifyContract_native_of_call
#print axioms boolBranchCallResid_of_halves
#print axioms nullBranchCallResid_of_halves
#print axioms nativeBranchCallResid_of_halves
#print axioms stringifyContract_of_kinds

end Vsa.Sim
