import VsaIris.Interp.Repr
import VsaIris.CallAbort
import VsaIris.Vsa.Console
import Vsa.Sim.Code.FixedImage
import Vsa.Sim.LayoutInstance
import VsaIris.Vsa.HeapShape

/-!
# `IrisHoles.newlib`: the newlib calls on the error and exit paths (H5)

INTERP_DESIGN.md Q4: the newlib formatter and stdio writer stay unproved for
now. Each is an exact Iris statement about the fixed binary, a field of
`NewlibHolesAt` (hence of `IrisHoles`) with a row in `VsaIris/HOLES.md`:

* `snprintf` (`0x80005c44`) with a format whose conversions are `%s`/`%d`:
  `runtime_error`'s two calls, and `interp_run`'s top-level status messages;
* `fprintf` (`0x800061c0`) to `stderr` with such a format: `main`'s
  `fprintf(stderr, "%s\n", in->err_msg)`;
* `fwrite` (`0x80005260`) to `stderr`: the out-of-memory message (gcc turned
  `fprintf(stderr, "out of memory\n")` into `fwrite(msg, 1, 14, stderr)`);
* `exitHandlers`: the newlib interior of `exit` (`0x80004778`–`0x80004788`:
  `__call_exitprocs(e, 0)`, then the installed `__stdio_exit_handler`).

Every statement holds for both WPs (`∀ Wp`), so the total route's `exit(0)`
uses the same fields. `stderr` output reaches the console: `_write` ignores
its descriptor and stores to `tohost`, so `fprintf`/`fwrite` hand back
`consoleOwn (o ++ o')` for some `o'`.

After a write to `stderr` its `FILE` object has left VSA's `ExitRuntimeData`
state (`__swsetup_r` sets `__SWR`, `__smakebuf_r` installs the one-byte
buffer). That state is `Ierr`, a parameter of `NewlibHolesAt` that the
discharge fixes: `NewlibHoles := ∃ Ierr, NewlibHolesAt Ierr`, and
`NewlibHoles.at` instantiates it at `stdioErr`, a choice of such an `Ierr`.

The stack needs are measured frame chains of the binary, rounded up:
`snprintf` 272 + `_svfprintf_r` 592 + `__ssprint_r` 64 = 928;
`fprintf` 80 + `_vfprintf_r` 592 + `__sbprintf` 1264 + `_vfprintf_r` 592 +
the write path ≈ 3200; `fwrite` 112 + `__sfvwrite_r` 96 + `__swsetup_r` 32 +
`__smakebuf_r` 160 + `__swhatbuf_r` 160 + `_fstat_r` 16 + `_fstat` 16 = 592;
`__call_exitprocs` 96, `_fwalk_sglue` 80 + `_fclose_r` 32 + `__sflush_r` 48 +
`__swrite` 48 + `_write_r` 16 = 224.
-/

namespace VsaIris.Newlib

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Interp VsaIris.Stdio VsaIris.Inst

/-- newlib's runtime data and the allocator's globals are disjoint: the two
owners of `.data`/`.bss`. -/
theorem stdioFoot_off_alloc (a : Nat) (h : stdioFoot a) : ¬ VsaHeap.allocGlobal a := by
  unfold stdioFoot InRange at h
  unfold VsaHeap.allocGlobal VsaHeap.InRange
  omega

/-! ## The image, the registers, the call frame -/

/-- `.text` and `.rodata` of the fixed binary (`Vsa.Sim.Code.FixedTextLoaded`,
`FixedRodataLoaded`). -/
def textDom (a : Nat) : Prop := 0x80000000 ≤ a ∧ a < 0x80018be0
def rodataDom (a : Nat) : Prop := 0x80018be0 ≤ a ∧ a < 0x8001acf0

def textByte (a : Nat) : BitVec 8 := Vsa.Sim.Code.fixedTextByte (a - 0x80000000)
def rodataByte (a : Nat) : BitVec 8 := Vsa.Sim.Code.fixedRodataByte (a - 0x80018be0)

/-- The code bytes the newlib functions fetch are present. -/
def CodeLive (live : Nat → Prop) : Prop := ∀ a, textDom a → live a

/-- `gp` at `_start`'s value (`__global_pointer$`). -/
def gpV : BitVec 64 := 0x8001b510#64

def calleeSaved : List Nat := [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
def tmpRegs : List Nat := [5, 6, 7, 28, 29, 30, 31]
def argRegs : List Nat := [10, 11, 12, 13, 14, 15, 16, 17]

section Frame

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The argument registers from `a0`: the given values, the rest at any
value. -/
def argsAt (vs : List (BitVec 64)) : IProp GF :=
  iprop(sepL (vs.zipIdx) (fun p => (10 + p.2) ↦ᵣ p.1) ∗ clobbered (argRegs.drop vs.length))

/-- The binary's `.text` and `.rodata`, persistent. -/
def binImg : IProp GF := iprop(roImg textDom textByte ∗ roImg rodataDom rodataByte)

instance : Persistent (binImg (GF := GF)) := by unfold binImg; infer_instance

/-- The stack pointer of a call with `need` bytes of scratch: 16-aligned, in
RAM, the scratch above the HTIF words. -/
structure SpIn (s : BitVec 64) (need : Nat) : Prop where
  lo : Vsa.Sim.tohostAddr + 16 + need ≤ s.toNat
  hi : s.toNat ≤ 0x88000000
  align : s.toNat % 16 = 0

/-- What a newlib callee borrows besides its arguments: the stack pointer and
`need` bytes below it, the callee-saved registers `saved` at `cs` (spilled
and restored), the temporaries, `gp`, and the image. -/
def callFrame (s : BitVec 64) (need : Nat) (saved : List Nat) (cs : Nat → BitVec 64) :
    IProp GF :=
  iprop(sp ↦ᵣ s ∗ stackScratch s need ∗ sepL saved (fun r => r ↦ᵣ cs r) ∗
    clobbered tmpRegs ∗ gp ↦ᵣ□ gpV ∗ binImg)

/-- A NUL-terminated string written into the owned `n`-byte buffer at `dst`. -/
def cstrBuf (dst n : Nat) : IProp GF :=
  iprop(∃ img, ownImg (InExt (dst, n)) img ∗ ⌜∃ k, k < n ∧ img (dst + k) = 0⌝)

/-- Bytes a formatter reads: read-only on `Sro`, exclusively owned on
`Sown`, both at the image `rd`. -/
def readable (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8) : IProp GF :=
  iprop(roImg Sro rd ∗ ownImg Sown rd)

end Frame

/-! ## Formats -/

/-- A conversion the error messages use. -/
inductive Conv where
  | str
  | int
  deriving DecidableEq

/-- The conversions of a format, or `none` if it has one other than `%s`/`%d`
(`'%' = 0x25`, `'s' = 0x73`, `'d' = 0x64`). -/
def parseFmt : List (BitVec 8) → Option (List Conv)
  | [] => some []
  | b :: rest =>
    if b = 0x25#8 then
      match rest with
      | c :: r =>
        if c = 0x73#8 then (Conv.str :: ·) <$> parseFmt r
        else if c = 0x64#8 then (Conv.int :: ·) <$> parseFmt r
        else none
      | [] => none
    else parseFmt rest

/-- The bytes at `p` in `rd` are `bs` followed by a NUL, all inside `R`. -/
structure CStrCov (R : Nat → Prop) (rd : Nat → BitVec 8) (p : Nat) (bs : List (BitVec 8)) :
    Prop where
  bytes : ∀ i (h : i < bs.length), R (p + i) ∧ rd (p + i) = bs[i] ∧ bs[i] ≠ 0
  nul : R (p + bs.length) ∧ rd (p + bs.length) = 0

/-- A format with bytes `bytes` and conversions `convs`, and its arguments,
are safe to print: the format is a C string in `R` with only `%s`/`%d`
conversions, one argument each, and every `%s` argument is a C string in
`R`. -/
structure FmtArgsAt (R : Nat → Prop) (rd : Nat → BitVec 8) (fmt : BitVec 64)
    (args : List (BitVec 64)) (bytes : List (BitVec 8)) (convs : List Conv) : Prop where
  fmt_str : CStrCov R rd fmt.toNat bytes
  parse : parseFmt bytes = some convs
  arity : convs.length ≤ args.length
  strs : ∀ i (h : i < convs.length), convs[i] = .str →
    ∃ t, CStrCov R rd (args[i]'(Nat.lt_of_lt_of_le h arity)).toNat t

/-- Some format bytes and conversions make `fmt` and `args` safe to print. -/
def FmtArgsOK (R : Nat → Prop) (rd : Nat → BitVec 8) (fmt : BitVec 64)
    (args : List (BitVec 64)) : Prop :=
  ∃ bytes convs, FmtArgsAt R rd fmt args bytes convs

/-! ## The entries and the stack needs -/

def snprintfEntry : BitVec 64 := 0x80005c44#64
def fprintfEntry : BitVec 64 := 0x800061c0#64
def fwriteEntry : BitVec 64 := 0x80005260#64
/-- `exit`'s `jal __call_exitprocs` and its `mv a0,s0` after the handler. -/
def exitHandlersPC : BitVec 64 := 0x80004778#64
def exitHandlersEnd : BitVec 64 := 0x80004788#64

/-- `stderr`: `__sf[2]`, `_impure_data._stderr` (`Vsa.Sim.exitStderr`). -/
def stderrFile : BitVec 64 := 0x8001bbd8#64

def snprintfNeed : Nat := 1024
def fprintfNeed : Nat := 4096
def fwriteNeed : Nat := 768
def exitHandlersNeed : Nat := 512

/-! ## The statements -/

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- `snprintf(dst, n, fmt, args…)`, `0 < n < 2^31`: writes a C string into
`dst[0, n)`, reads the format and its `%s` arguments, keeps newlib's runtime
data in its boundary state, prints nothing, returns. -/
def snprintfSpec (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (s dst n fmt : BitVec 64) (args : List (BitVec 64)) (cs : Nat → BitVec 64)
    (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8) : IProp GF :=
  fnSpecW Wp snprintfEntry
    (fun _ => iprop(argsAt ([dst, n, fmt] ++ args) ∗ blockOwn dst.toNat n.toNat ∗
      readable Sro Sown rd ∗ stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗ cstrBuf dst.toNat n.toNat ∗ readable Sro Sown rd ∗
      stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))

/-- `fprintf(stderr, fmt, args…)`: prints some string, reads the format and
its `%s` arguments, leaves newlib's data in the post-`stderr`-write state
`Ierr`, returns. -/
def fprintfSpec (Ierr : (Nat → BitVec 8) → Prop) (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s fmt : BitVec 64) (args : List (BitVec 64))
    (cs : Nat → BitVec 64) (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8) (o : String) :
    IProp GF :=
  fnSpecW Wp fprintfEntry
    (fun _ => iprop(argsAt ([stderrFile, fmt] ++ args) ∗ readable Sro Sown rd ∗ stdioOwn ∗
      consoleOwn o ∗ callFrame s fprintfNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗ readable Sro Sown rd ∗ stdioAt Ierr ∗
      (∃ o', consoleOwn (o ++ o')) ∗ callFrame s fprintfNeed calleeSaved cs))

/-- `fwrite(ptr, 1, n, stderr)`: prints some string, reads `ptr[0, n)`,
leaves newlib's data in `Ierr`, returns. -/
def fwriteSpec (Ierr : (Nat → BitVec 8) → Prop) (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s ptr n : BitVec 64) (cs : Nat → BitVec 64)
    (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8) (o : String) : IProp GF :=
  fnSpecW Wp fwriteEntry
    (fun _ => iprop(argsAt [ptr, 1#64, n, stderrFile] ∗ readable Sro Sown rd ∗ stdioOwn ∗
      consoleOwn o ∗ callFrame s fwriteNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗ readable Sro Sown rd ∗ stdioAt Ierr ∗
      (∃ o', consoleOwn (o ++ o')) ∗ callFrame s fwriteNeed calleeSaved cs))

/-- The newlib interior of `exit(e)`: from `jal __call_exitprocs` at
`0x80004778` (`a0 = s0 = e`, `a1 = 0`, `sp` after `exit`'s prologue) to its
`mv a0,s0` at `0x80004788`, with `s0` still `e`. Runs from newlib's boundary
state or from `Ierr`; may print (the `stderr`/`stdout` close path). -/
def exitHandlersSpec (Ierr : (Nat → BitVec 8) → Prop) (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s e r : BitVec 64) (cs : Nat → BitVec 64)
    (o : String) (Φ : Nat × String → IProp GF) : IProp GF :=
  iprop(PC ↦ᵣ exitHandlersPC ∗ ra ↦ᵣ r ∗ (8 : Nat) ↦ᵣ e ∗ argsAt [e, 0#64] ∗
      stdioAt (fun img => StdioOK img ∨ Ierr img) ∗ consoleOwn o ∗
      callFrame s exitHandlersNeed (calleeSaved.drop 1) cs ∗
      (PC ↦ᵣ exitHandlersEnd -∗ (∃ w, ra ↦ᵣ w) -∗ (8 : Nat) ↦ᵣ e -∗ clobbered argRegs -∗
        stdioAt (fun _ => True) -∗ (∃ o', consoleOwn (o ++ o')) -∗
        callFrame s exitHandlersNeed (calleeSaved.drop 1) cs -∗ Wp.W Φ)
    -∗ Wp.W Φ)

end Specs

/-! ## The holes -/

/-- The newlib statements at the post-`stderr`-write state `Ierr`, for every
Iris instance, every `live` set holding the code, and both WPs. -/
structure NewlibHolesAt (Ierr : (Nat → BitVec 8) → Prop) : Prop where
  /-- `snprintf` with a `%s`/`%d` format (`runtime_error`, `interp_run`). -/
  snprintf : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s dst n fmt : BitVec 64) (args : List (BitVec 64))
    (cs : Nat → BitVec 64) (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8),
    CodeLive live → args.length ≤ 5 → 0 < n.toNat → n.toNat < 2 ^ 31 →
    FmtArgsOK (fun a => Sro a ∨ Sown a) rd fmt args → SpIn s snprintfNeed →
    ⊢ snprintfSpec live Wp s dst n fmt args cs Sro Sown rd
  /-- `fprintf(stderr, …)` with a `%s`/`%d` format (`main`'s error line). -/
  fprintf : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s fmt : BitVec 64) (args : List (BitVec 64))
    (cs : Nat → BitVec 64) (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8) (o : String),
    CodeLive live → args.length ≤ 6 → FmtArgsOK (fun a => Sro a ∨ Sown a) rd fmt args →
    SpIn s fprintfNeed →
    ⊢ fprintfSpec Ierr live Wp s fmt args cs Sro Sown rd o
  /-- `fwrite(ptr, 1, n, stderr)` (the out-of-memory message). -/
  fwrite : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s ptr n : BitVec 64) (cs : Nat → BitVec 64)
    (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8) (o : String),
    CodeLive live → (∀ i, i < n.toNat → Sro (ptr.toNat + i) ∨ Sown (ptr.toNat + i)) →
    SpIn s fwriteNeed →
    ⊢ fwriteSpec Ierr live Wp s ptr n cs Sro Sown rd o
  /-- The newlib interior of `exit`. -/
  exitHandlers : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s e r : BitVec 64) (cs : Nat → BitVec 64)
    (o : String) (Φ : Nat × String → IProp GF),
    CodeLive live → SpIn s exitHandlersNeed →
    ⊢ exitHandlersSpec Ierr live Wp s e r cs o Φ

/-- **`IrisHoles.newlib`**: the newlib statements hold at some post-write
state. -/
def NewlibHoles : Prop := ∃ Ierr, NewlibHolesAt Ierr

/-- The post-`stderr`-write state the holes are instantiated at. -/
def stdioErr (img : Nat → BitVec 8) : Prop := ∃ h : NewlibHoles, Classical.choose h img

theorem NewlibHoles.at (h : NewlibHoles) : NewlibHolesAt stdioErr := by
  have e : stdioErr = Classical.choose h :=
    funext fun img => propext ⟨fun ⟨_, hi⟩ => hi, fun hi => ⟨h, hi⟩⟩
  rw [e]
  exact Classical.choose_spec h

end VsaIris.Newlib
