import VsaIris.Interp.SpecValue
import VsaIris.Interp.HeapCall

/-!
# `stringify`'s statement (lane H2)

`stringify(v)` (`interp.c:84-106`, `0x80002fc0`) renders a value for string
`+`: a string is copied, every other kind is rendered into a 64-byte stack
buffer (`strcpy` of a constant, `snprintf("%lld")`, `snprintf("<fn %s>")`,
inline stores) and copied. The copy is `strlen`, `malloc(len + 1)` and
`memcpy`. `malloc` may return NULL in partial mode; the machine then prints
the out-of-memory message and exits (`oom80003140`, H5's `wp_oomBlock`), so
the spec is a `fnSpecAbort`.

The rendering is `Value.catDisplay`, except that `snprintf` cuts a named
closure's `"<fn name>"` at 63 characters (`strRender`, INTERP_DESIGN.md Q8).

Callee specs taken as hypotheses (the way lane G takes `valueIntSpec` and
lane H1 takes `strlenSpec`/`memcpySpec`): H1's `strlenSpec` and
`memcpySpec` for the string arm (the string is read-only), and
`memcpySpecOwned`/`strcpySpec` below for the buffer.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym VsaIris.Newlib VsaIris.Stdio
open Vsa.While Vsa.RuntimeRepr

/-- A closure's name, if the value is a named closure. -/
def closName (st : Store) : Value → Option String
  | .closure ca => (st.closures[ca]?).bind ClosureData.name
  | _ => none

/-- **What `stringify` renders**: `Value.catDisplay` (`strRender_eq`), with a named closure's
`"<fn name>"` cut at 63 characters by `snprintf(buf, 64, …)`. -/
def strRender (st : Store) (v : Value) : String :=
  match closName st v with
  | some x => fnRender x
  | none => v.catDisplay st

/-- `stringify` renders exactly the semantics' concatenation form (Q8). -/
theorem strRender_eq (st : Store) (v : Value) : strRender st v = v.catDisplay st := by
  unfold strRender closName
  cases v with
  | closure ca =>
    cases h : st.closures[ca]? with
    | none => simp [Value.catDisplay, h]
    | some cd =>
      cases hn : cd.name <;> simp [Value.catDisplay, h, hn, fnRender_eq]
  | _ => rfl

/-- `stringify`'s stack: its 112-byte frame and `snprintf`'s need below it
(the largest callee: `malloc` takes 512, the out-of-memory block 768). -/
def stringifyNeed : Nat := 112 + snprintfNeed

abbrev strcpyPC : BitVec 64 := 0x80006dc4#64

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (M : MachineModel) (N : NativeAddrs)

/-- An owned block holding a C string. -/
def strOwn (q : Nat) (x : String) : IProp GF :=
  iprop(∃ img, ownImg (InExt (q, x.toList.length + 1)) img ∗ ⌜CStrImg img q x⌝)

/-- `memcpy(dst, src, n)` from an OWNED source, handed back unchanged, into a
destination above the HTIF words; the code context `binImg` in the precondition. -/
def memcpySpecOwned (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (dst src : BitVec 64) (n : Nat) (img : Nat → BitVec 8), fnSpecW Wp memcpyPC
    (fun r => iprop(⌜r.toNat % 4 = 0 ∧ RamWin dst.toNat n ∧ htifLo + 16 ≤ dst.toNat ∧
        RamWin src.toNat n⌝ ∗
      (10 : Nat) ↦ᵣ dst ∗ (11 : Nat) ↦ᵣ src ∗ (12 : Nat) ↦ᵣ BitVec.ofNat 64 n ∗
      clobbered argClob ∗ blockOwn dst.toNat n ∗ ownImg (InExt (src.toNat, n)) img ∗ binImg))
    (fun _ => iprop((10 : Nat) ↦ᵣ dst ∗ clobbered retClob ∗
      ownImg (InExt (dst.toNat, n)) (fun a => img (a - dst.toNat + src.toNat)) ∗
      ownImg (InExt (src.toNat, n)) img)))

instance (Wp : MachWP (GF := GF) M) : Persistent (memcpySpecOwned M Wp) := by
  unfold memcpySpecOwned; infer_instance

/-- `strcpy(dst, src)` of a read-only C string into an owned buffer above the
HTIF words. -/
def strcpySpec (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (dst src : BitVec 64) (x : String) (n : Nat), fnSpecW Wp strcpyPC
    (fun r => iprop(⌜r.toNat % 4 = 0 ∧ RamWin dst.toNat n ∧ x.toList.length + 1 ≤ n ∧
        htifLo + 16 ≤ dst.toNat⌝ ∗
      (10 : Nat) ↦ᵣ dst ∗ (11 : Nat) ↦ᵣ src ∗ clobbered (12 :: argClob) ∗ blockOwn dst.toNat n ∗
      strAt src.toNat x))
    (fun _ => iprop((10 : Nat) ↦ᵣ dst ∗ clobbered retClob ∗
      (∃ img, ownImg (InExt (dst.toNat, n)) img ∗ ⌜CStrImg img dst.toNat x⌝))))

instance (Wp : MachWP (GF := GF) M) : Persistent (strcpySpec M Wp) := by
  unfold strcpySpec; infer_instance

/-- **`stringify(&v)`**, a function that returns OR aborts, in regime `ρ`
(`malloc`'s `c` credits when counted). It returns a fresh heap block holding
`strRender st v` and a NUL, the value and the rest untouched; in partial mode
an out-of-memory `malloc` aborts with H5's `abortRes` over its stack and the
value's slot, only in the uncounted regime (`⌜ρ = .uncounted⌝`). -/
def stringifySpec (Wp : MachWP (GF := GF) M) (inp : Nat) (p s : BitVec 64) (v : Value)
    (st : Store) (ρ : Regime) (H : List (Nat × Nat)) (c : Nat) (o : String) : IProp GF :=
  iprop(∀ rv : Nat → BitVec 64, fnSpecAbort Wp stringifyPC
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ regFile rv ∗ ⌜rv 10 = p ∧ rv 2 = s⌝ ∗ codeRes ∗
      valAt N p.toNat v ∗
      ⌜SlotGeom p ∧ vsaChg ((strRender st v).toList.length + 1) c⌝ ∗ dispRes st v ∗ binImg ∗
      heapRes vsaLayoutP vsaRoomB (ρ.plus c) H ∗ stdioOwn ∗ consoleOwn o ∗
      stackAt s stringifyNeed))
    (fun _ => iprop(∃ (rv' : Nat → BitVec 64) (q : BitVec 64), regFile rv' ∗
      ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = rv x⌝ ∗ ⌜rv' 10 = q⌝ ∗
      valAt N p.toNat v ∗ strOwn q.toNat (strRender st v) ∗
      ⌜FreshBlock vsaLayoutP H q.toNat ((strRender st v).toList.length + 1) ∧ q.toNat % 16 = 0⌝ ∗
      heapRes vsaLayoutP vsaRoomB ρ ((q.toNat, (strRender st v).toList.length + 1) :: H) ∗
      stdioOwn ∗ consoleOwn o ∗ stackAt s stringifyNeed))
    (iprop(⌜ρ = .uncounted⌝ ∗ abortRes N vsaLayoutP vsaRoomB inp s stringifyNeed ∗
      slot24 p.toNat)))

end Specs

end VsaIris.Interp
