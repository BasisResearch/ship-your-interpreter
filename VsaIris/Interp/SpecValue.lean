import VsaIris.Interp.SpecEval
import VsaIris.Interp.Abort
import VsaIris.Vsa.NewlibOut

/-!
# The value helpers and the natives: the statements (lane H2)

INTERP_DESIGN.md §9 H2. The statements only (MachCSL `Spec<F>`: callers take
a spec as a hypothesis, never a proof import, `claude-notes/spec-modules.md`).
The proofs are `ProofValue*.lean`.

Every helper is stated in lane G's register-file form (`SpecEval.helperSpec`):
the body's registers are ONE valuation `regFile rv` with argument pins, the
code image `codeRes` (which covers these functions: `gen_interp_steps.py`)
comes with the call, and the post keeps every register outside `clob`. A
symbolic run (`SWP`, `wp_swpF`) consumes exactly this shape, and an arm
calls such a helper with `ms_callHelper`.

* `value_null`, `value_bool`, `value_str` (and lane G's `valueIntSpec`): a
  value constructed in the result slot (`valAt`).
* `value_truthy`: `a0 = Value.truthy`.
* `value_equal`: `a0 = Value.equal`; strings through `strcmp` (callee spec
  `strcmpSpecV`), closures by the store's address map (`storeRepr`), natives
  by the injectivity of their entry addresses (`NativeInj`).
* `value_print`, `native_print`, `native_println`: the console grows by
  `Value.display`/`printArgs` (+ `"\n"`), through newlib's stdout calls
  (`Newlib.OutHoles`, an `IrisHoles` field).
* `native_assert`: returns `null` when the argument list is `[v]` or `[v, m]`
  with `v` truthy, and aborts through `runtime_error` otherwise
  (`fnSpecAbort`; the abort resource carries the failure, so a total caller
  holding `Call.assertOk`'s premises discharges it by a pure fact).
* `stringify`: a fresh heap block holding `Value.catDisplay` as a C string,
  or (uncounted regime only) the out-of-memory exit.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Stdio VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-! ## Entries, clobbers, stack needs -/

abbrev valueNullPC : BitVec 64 := 0x800027ec#64
abbrev valueBoolPC : BitVec 64 := 0x800027f8#64
abbrev valueStrPC : BitVec 64 := 0x8000281c#64
abbrev valueTruthyPC : BitVec 64 := 0x8000282c#64
abbrev valueEqualPC : BitVec 64 := 0x8000285c#64
abbrev valuePrintPC : BitVec 64 := 0x800028fc#64
abbrev nativeAssertPC : BitVec 64 := 0x80002df4#64
abbrev nativePrintPC : BitVec 64 := 0x80002ed4#64
abbrev nativePrintlnPC : BitVec 64 := 0x80002f7c#64
abbrev stringifyPC : BitVec 64 := 0x80002fc0#64

/-- The callee entries H2 calls. -/
abbrev strcmpPCV : BitVec 64 := 0x80006ea0#64

/-- The registers a call may clobber: the temporaries and the arguments. -/
abbrev callerSaved : List Nat := [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- Stack below `sp`: `value_print` tail-calls newlib (`fprintf`'s need,
`NewlibOut.lean`), the natives add their frames. -/
def printNeed : Nat := fprintfNeed
def nativePrintNeed : Nat := 80 + printNeed
def nativePrintlnNeed : Nat := 48 + nativePrintNeed

/-- The machine entry addresses of the natives are distinct (the concrete
image's: `InterpRunPhysicalFacts`). `value_equal` compares natives by them. -/
def NativeInj (N : NativeAddrs) : Prop := ∀ f g, N.addr f = N.addr g → f = g

section Defs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-! ## Values in memory -/

/-- The window of `n` consecutive 24-byte values from `a` (a native's
`args`, inside `eval_expr`'s frame): 8-aligned, RAM, off the HTIF words. -/
structure ArgsGeom (a : BitVec 64) (n : Nat) : Prop where
  al : a.toNat % 8 = 0
  lo : Vsa.Sim.tohostAddr + 16 ≤ a.toNat
  hi : a.toNat + 24 * n ≤ 0x100000000

/-- `n` consecutive represented values from `a` (a native's `args`). -/
def valsAt (N : NativeAddrs) (a : Nat) (vs : List Value) : IProp GF :=
  sepL vs.zipIdx (fun p => valAt N (a + 24 * p.2) p.1)

/-- What `Value.display st v` reads besides the value's words: for a closure,
the closure object's first word (its `EX_FN` node) and the node's name field,
read-only, with the read geometry the loads need (`ReadOK`, as in lane G's
`astEG`). This is `closOwn` (without the environment link) plus geometry:
`closOwn`/`astE` carry no geometry, so the supplier is the one that built the
closure (`EX_FN`: a heap block and the program's AST, both readable).
Every other value is displayed from its own words. -/
def dispRes (st : Store) : Value → IProp GF
  | .closure ca => iprop(∃ (cd : ClosureData) (p q : Nat) (img : Nat → BitVec 8) (P : Nat → Prop)
      (m : Mem), ⌜st.closures[ca]? = some cd ∧ imgLE img p 8 = q ∧
        (∀ k, InExt (p, 16) k → ReadOK k) ∧ ExprReprWithin m P q (.fn cd.name cd.params cd.body) ∧
        (∀ k, P k → ReadOK k)⌝ ∗
      closAt ca p ∗ roImg (InExt (p, 16)) img ∗ roOn P m)
  | _ => iprop(emp)

instance (st : Store) (v : Value) : Persistent (dispRes (GF := GF) st v) := by
  cases v <;> unfold dispRes <;> infer_instance

/-- `dispRes` of every argument. -/
def dispResL (st : Store) (vs : List Value) : IProp GF := sepL vs (dispRes st)

instance (st : Store) (vs : List Value) : Persistent (dispResL (GF := GF) st vs) := by
  unfold dispResL; infer_instance

/-- The window of a stack region: `n` bytes below `s`. -/
abbrev stackAt (s : BitVec 64) (n : Nat) : IProp GF :=
  iprop(stackScratch s n ∗ ⌜StackGeom s n⌝)

end Defs

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (M : MachineModel) (N : NativeAddrs)

/-! ## Callee specs (hypotheses; other lanes prove them) -/

/-- `strcmp(p, q)`: `a0` is zero exactly when the strings are equal (H3; the
shape of H1's `strcmpSpec`, in register-file form). The word loads over-read
up to seven bytes past each NUL, which H1's `strAt` window (`StrWin`)
covers. -/
def strcmpSpecV (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (p q : BitVec 64) (x y : String),
    helperSpec M Wp strcmpPCV callerSaved (fun rv => rv 10 = p ∧ rv 11 = q)
      iprop(strAt p.toNat x ∗ strAt q.toNat y)
      (fun rv' => iprop(⌜rv' 10 = 0#64 ↔ x = y⌝)))

instance (Wp : MachWP (GF := GF) M) : Persistent (strcmpSpecV M Wp) := by
  unfold strcmpSpecV; infer_instance

/-! ## The constructors -/

/-- `value_null(sret)` (`sw zero,0(a0); sd zero,8(a0); ret`). -/
def valueNullSpec (Wp : MachWP (GF := GF) M) (p : BitVec 64) : IProp GF :=
  helperSpec M Wp valueNullPC [] (fun rv => rv 10 = p) iprop(slot24 p.toNat ∗ ⌜SlotGeom p⌝)
    (fun _ => valAt N p.toNat .null)

/-- `value_bool(sret, b)`: `b != 0`. -/
def valueBoolSpec (Wp : MachWP (GF := GF) M) (p b : BitVec 64) : IProp GF :=
  helperSpec M Wp valueBoolPC [11, 15] (fun rv => rv 10 = p ∧ rv 11 = b)
    iprop(slot24 p.toNat ∗ ⌜SlotGeom p⌝) (fun _ => valAt N p.toNat (.bool (b != 0#64)))

/-- `value_str(sret, q)`: the slot points at the (persistent) string. -/
def valueStrSpec (Wp : MachWP (GF := GF) M) (p q : BitVec 64) (x : String) : IProp GF :=
  helperSpec M Wp valueStrPC [15] (fun rv => rv 10 = p ∧ rv 11 = q)
    iprop(slot24 p.toNat ∗ ⌜SlotGeom p ∧ q.toNat ≠ 0⌝ ∗ strAt q.toNat x)
    (fun _ => valAt N p.toNat (.str x))

/-! ## Truthiness and equality -/

/-- `value_truthy(v)` (`v` by reference: `a0` points at a copy). -/
def valueTruthySpec (Wp : MachWP (GF := GF) M) (p : BitVec 64) (v : Value) : IProp GF :=
  helperSpec M Wp valueTruthyPC [10, 14, 15] (fun rv => rv 10 = p)
    iprop(valAt N p.toNat v ∗ ⌜SlotGeom p⌝)
    (fun rv' => iprop(valAt N p.toNat v ∗ ⌜rv' 10 = if v.truthy then 1#64 else 0#64⌝))

/-- `value_equal(a, b)` (both by reference). The strings go through `strcmp`
below `sp` (16 bytes of frame); closures compare by the store's address map. -/
def valueEqualSpec (Wp : MachWP (GF := GF) M) (pa pb s : BitVec 64) (a b : Value) (st : Store)
    (B : List (Nat × Nat)) : IProp GF :=
  helperSpec M Wp valueEqualPC callerSaved (fun rv => rv 10 = pa ∧ rv 11 = pb ∧ rv 2 = s)
    iprop(valAt N pa.toNat a ∗ valAt N pb.toNat b ∗ ⌜SlotGeom pa ∧ SlotGeom pb ∧ NativeInj N⌝ ∗
      storeRepr N st B ∗ stackAt s 16 ∗ strcmpSpecV M Wp)
    (fun rv' => iprop(valAt N pa.toNat a ∗ valAt N pb.toNat b ∗ storeRepr N st B ∗ stackAt s 16 ∗
      ⌜rv' 10 = if Value.equal a b then 1#64 else 0#64⌝))

/-! ## Printing -/

/-- `value_print(v, stdout)`: the console grows by `Value.display st v`. The
arm tail-calls newlib (`Newlib.OutHoles`), so the stack it lends is `fprintf`'s. -/
def valuePrintSpec (Wp : MachWP (GF := GF) M) (p s : BitVec 64) (v : Value) (st : Store)
    (o : String) : IProp GF :=
  helperSpec M Wp valuePrintPC callerSaved
    (fun rv => rv 10 = p ∧ rv 11 = stdoutFile ∧ rv 2 = s)
    iprop(valAt N p.toNat v ∗ ⌜SlotGeom p⌝ ∗ dispRes st v ∗ binImg ∗ stdioOwn ∗ consoleOwn o ∗
      stackAt s printNeed)
    (fun _ => iprop(valAt N p.toNat v ∗ stdioOwn ∗ consoleOwn (o ++ v.display st) ∗
      stackAt s printNeed))

/-- `native_print(sret, in, argc, args, line)`: prints the arguments separated
by spaces (`printArgs`) and returns `null`. -/
def nativePrintSpec (Wp : MachWP (GF := GF) M) (sret args s : BitVec 64) (vs : List Value)
    (st : Store) (o : String) : IProp GF :=
  helperSpec M Wp nativePrintPC callerSaved
    (fun rv => rv 10 = sret ∧ rv 12 = BitVec.ofNat 64 vs.length ∧ rv 13 = args ∧ rv 2 = s)
    iprop(slot24 sret.toNat ∗ ⌜SlotGeom sret ∧ ArgsGeom args vs.length ∧ vs.length < 2 ^ 31⌝ ∗
      valsAt N args.toNat vs ∗ dispResL st vs ∗ binImg ∗ stdioOwn ∗ consoleOwn o ∗
      stackAt s nativePrintNeed)
    (fun _ => iprop(valAt N sret.toNat .null ∗ valsAt N args.toNat vs ∗ stdioOwn ∗
      consoleOwn (o ++ printArgs st vs) ∗ stackAt s nativePrintNeed))

/-- `native_println(sret, in, argc, args, line)`: `native_print`, then a
newline. -/
def nativePrintlnSpec (Wp : MachWP (GF := GF) M) (sret args s : BitVec 64) (vs : List Value)
    (st : Store) (o : String) : IProp GF :=
  helperSpec M Wp nativePrintlnPC callerSaved
    (fun rv => rv 10 = sret ∧ rv 12 = BitVec.ofNat 64 vs.length ∧ rv 13 = args ∧ rv 2 = s)
    iprop(slot24 sret.toNat ∗ ⌜SlotGeom sret ∧ ArgsGeom args vs.length ∧ vs.length < 2 ^ 31⌝ ∗
      valsAt N args.toNat vs ∗ dispResL st vs ∗ binImg ∗ stdioOwn ∗ consoleOwn o ∗
      stackAt s nativePrintlnNeed)
    (fun _ => iprop(valAt N sret.toNat .null ∗ valsAt N args.toNat vs ∗ stdioOwn ∗
      consoleOwn (o ++ printArgs st vs ++ "\n") ∗ stackAt s nativePrintlnNeed))

end Specs

end VsaIris.Interp
