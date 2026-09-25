import VsaIris.Interp.SpecStringify
import VsaIris.Interp.HeapCall

/-!
# The concatenation arm's callee specs (lane E2)

String `+` (`eval_binary`, `interp.c:117-123`) runs `stringify` on both
operands, `strlen` on both renderings, `malloc`, `memcpy` of the left
rendering, `strcpy` of the right one, `free` of both renderings and
`value_str`. The renderings are FRESH heap blocks the arm owns and frees, so
`strlen`/`strcpy` read them through ownership, not through the persistent
`strAt` of `strlenSpec`/`strcpySpec`. Their word loads read up to seven bytes
past the NUL, inside the block's chunk, which the allocator's footprint owns
(`heapFoot`): the specs below lend the live list `heapRes … ρ H`, with the
block live in it, and hand it back unchanged. Suppliers: H3's
`strlen_specOwnedW` run and newlib's `strcpy` run, with the slack carved from
`heapRes` (recorded in `PROOF_CLOSURE_PLAN.md`).

* `stringifySpecT`: `stringify` in the counted regime RETURNS (`malloc` never
  answers NULL there, `mallocRes`). `stringifySpec` is `fnSpecAbort`, whose
  abort branch a total-mode caller cannot discharge; H2's `stringify_spec`
  takes the counted OOM branch to a contradiction in every arm
  (`sg_strMalloc` and its siblings), so the supplier is that proof with the
  abort continuation dropped.
* `stringifySpecP`: `stringifySpec` whose abort also returns the value's
  slot. The slot is in the calling arm's frame; `abortRes` returns only the
  stack below `stringify`'s `sp`, and an `eval_expr` arm aborts with its whole
  stack. The OOM path of `stringify` still owns the slot (it only reads it).
* `CatDispSupply`: a closure operand is displayable from the store, lane E4's
  `DispSupply` premise (the same statement; integration keeps one name).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym VsaIris.Newlib VsaIris.Stdio
open Vsa.While Vsa.RuntimeRepr

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (M : MachineModel) (N : NativeAddrs)

/-- A heap string the arm owns: its block `(q, len + 1)` is live in `H`. -/
structure HeapStr (H : List (Nat × Nat)) (q : BitVec 64) (x : String) : Prop where
  live : (q.toNat, x.toList.length + 1) ∈ H
  align : q.toNat % 16 = 0

/-- **`strlen(q)` of an owned heap string** (H3): the length, the string and
the allocator's footprint unchanged. -/
def strlenHeapSpec (Wp : MachWP (GF := GF) M) (q : BitVec 64) (x : String) (ρ : Regime)
    (H : List (Nat × Nat)) : IProp GF :=
  helperSpec M Wp strlenPC callerSaved (fun rv => rv 10 = q)
    iprop(binImg ∗ ⌜HeapStr H q x⌝ ∗ strOwn q.toNat x ∗ heapRes vsaLayoutP vsaRoomB ρ H)
    (fun rv' => iprop(⌜rv' 10 = BitVec.ofNat 64 x.length⌝ ∗ strOwn q.toNat x ∗
      heapRes vsaLayoutP vsaRoomB ρ H))

/-- **`strcpy(d, q)` of an owned heap string** into an owned buffer of
`len + 1` bytes (H3/newlib): the buffer holds the string. -/
def strcpyHeapSpec (Wp : MachWP (GF := GF) M) (d q : BitVec 64) (y : String) (ρ : Regime)
    (H : List (Nat × Nat)) : IProp GF :=
  helperSpec M Wp strcpyPC callerSaved (fun rv => rv 10 = d ∧ rv 11 = q)
    iprop(binImg ∗ ⌜HeapStr H q y ∧ RamWin d.toNat (y.toList.length + 1) ∧ htifLo + 16 ≤ d.toNat⌝ ∗
      blockOwn d.toNat (y.toList.length + 1) ∗ strOwn q.toNat y ∗
      heapRes vsaLayoutP vsaRoomB ρ H)
    (fun _ => iprop((∃ img, ownImg (InExt (d.toNat, y.toList.length + 1)) img ∗
        ⌜CStrImg img d.toNat y⌝) ∗ strOwn q.toNat y ∗ heapRes vsaLayoutP vsaRoomB ρ H))

/-- A helper that returns OR aborts, in register-file form: `helperSpec`'s
two sides, and `A` on abort. -/
def helperSpecA (Wp : MachWP (GF := GF) M) (entry : BitVec 64) (clob : List Nat)
    (pins : (Nat → BitVec 64) → Prop) (Pre : IProp GF)
    (Post : (Nat → BitVec 64) → IProp GF) (A : IProp GF) : IProp GF :=
  iprop(∀ rv : Nat → BitVec 64, fnSpecAbort Wp entry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ regFile rv ∗ ⌜pins rv⌝ ∗ codeRes ∗ Pre))
    (fun _ => iprop(∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ clob → rv' x = rv x⌝ ∗ Post rv'))
    A)

/-- What `stringify(&v)` takes: the value, its display resources, the heap at
`ρ` with the rendering's `c` credits, the console and its stack. -/
def stringifyPre (p s : BitVec 64) (v : Value) (st : Store) (ρ : Regime)
    (H : List (Nat × Nat)) (c : Nat) (o : String) : IProp GF :=
  iprop(valAt N p.toNat v ∗
    ⌜SlotGeom p ∧ vsaChg ((strRender st v).toList.length + 1) c⌝ ∗ dispRes st v ∗ binImg ∗
    heapRes vsaLayoutP vsaRoomB (ρ.plus c) H ∗ stdioOwn ∗ consoleOwn o ∗ stackAt s stringifyNeed)

/-- What `stringify(&v)` returns: the value, the rendering in a fresh block
`(q, len + 1)` (`q = a0`) live in the heap, the console and the stack. -/
def stringifyPost (p s : BitVec 64) (v : Value) (st : Store) (ρ : Regime)
    (H : List (Nat × Nat)) (o : String) (q : BitVec 64) : IProp GF :=
  iprop(valAt N p.toNat v ∗ strOwn q.toNat (strRender st v) ∗
    ⌜FreshBlock vsaLayoutP H q.toNat ((strRender st v).toList.length + 1) ∧ q.toNat % 16 = 0⌝ ∗
    heapRes vsaLayoutP vsaRoomB ρ ((q.toNat, (strRender st v).toList.length + 1) :: H) ∗
    stdioOwn ∗ consoleOwn o ∗ stackAt s stringifyNeed)

/-- **`stringify(&v)` in the counted regime** (H2): it returns
(`stringifySpec`'s return branch at `ρ = counted k`). -/
def stringifySpecT (Wp : MachWP (GF := GF) M) (p s : BitVec 64) (v : Value) (st : Store)
    (k : Nat) (H : List (Nat × Nat)) (c : Nat) (o : String) : IProp GF :=
  helperSpec M Wp stringifyPC callerSaved (fun rv => rv 10 = p ∧ rv 2 = s)
    (stringifyPre N p s v st (.counted k) H c o)
    (fun rv' => stringifyPost N p s v st (.counted k) H o (rv' 10))

/-- **`stringify(&v)` that may abort** (H2): `stringifySpec`, whose abort
also hands back the value's slot (the caller's frame bytes: an `eval_expr`
arm's abort rebuilds its whole stack, `evalSpecP_body`). -/
def stringifySpecP (Wp : MachWP (GF := GF) M) (inp : Nat) (p s : BitVec 64) (v : Value)
    (st : Store) (ρ : Regime) (H : List (Nat × Nat)) (c : Nat) (o : String) : IProp GF :=
  helperSpecA M Wp stringifyPC callerSaved (fun rv => rv 10 = p ∧ rv 2 = s)
    (stringifyPre N p s v st ρ H c o)
    (fun rv' => stringifyPost N p s v st ρ H o (rv' 10))
    iprop(abortRes N vsaLayoutP vsaRoomB inp s stringifyNeed ∗ slot24 p.toNat)

/-- A closure the store owns is displayable (lane E4's `DispSupply`). -/
def CatDispSupply : Prop :=
  ∀ (s : Store) (B : List (Nat × Nat)) (ca p : Nat),
    storeRepr (GF := GF) N s B ∗ closAt ca p ⊢ storeRepr N s B ∗ dispRes s (.closure ca)

end Specs

end VsaIris.Interp
