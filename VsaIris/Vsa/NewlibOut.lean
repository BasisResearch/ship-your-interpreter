import VsaIris.Vsa.Newlib
import VsaIris.Interp.Repr

/-!
# `IrisHoles.out`: newlib's stdout calls (H2)

`value_print` and the natives print through newlib's stdio: `fputs`,
`fputc`, `fwrite` and `fprintf` on `stdout`. `stdout` is unbuffered at every
boundary (`ConsoleStream`, part of `StdioOK`: `_w = 0`, a one-byte buffer,
the `__swrite` callback), so each call reaches `_write`'s `tohost` store
(`putcSite`) before it returns, and newlib's data is back in its boundary
state. `stringify`'s named-closure arm renders through
`snprintf(buf, 64, "<fn %s>", name)`.

INTERP_DESIGN.md Q4: like H5's `NewlibHoles`, these stay unproved for now.
Each is an exact Iris statement about the fixed binary, in H5's calling
convention (`argsAt`, `callFrame`), a field of `OutHoles` (hence of
`IrisHoles`) with a row in `VsaIris/HOLES.md`. Unlike H5's `stderr` calls,
these are exact about what they print: the console grows by the fragment.

Stack needs are measured frame chains of the binary (`fputs` 576, `fputc`
528, `fwrite` 608, `fprintf` 3200), rounded up; `snprintf`'s is H5's.
-/

namespace VsaIris.Newlib

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Interp VsaIris.Stdio VsaIris.Inst
open Vsa.While

def fputsEntry : BitVec 64 := 0x80006500#64
def fputcEntry : BitVec 64 := 0x800062e0#64

/-- `stdout`'s `FILE` (`__sf[1]`, `Vsa.Sim.consoleStdout`). -/
def stdoutFile : BitVec 64 := 0x8001bb20#64

theorem stdoutFile_eq : stdoutFile.toNat = Vsa.Sim.consoleStdout := rfl

def outNeed : Nat := 768

/-- `"<fn " ++ name ++ ">"` as `snprintf` leaves it in a 64-byte buffer: at
most 63 characters. `Value.catDisplay` does not cut (INTERP_DESIGN.md Q8). -/
def fnRender (x : String) : String := String.ofList (("<fn " ++ x ++ ">").toList.take 63)

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- `fprintf(stdout, fmt, arg)`'s formats in `value_print`, and the fragment
each prints (VSA's `FprintfGround`): `"%lld"`, `"<fn %s>"`, `"<native fn %s>"`. -/
def fprintfOut (fmt arg : BitVec 64) (frag : String) : IProp GF :=
  iprop(⌜fmt = 0x800192c0#64 ∧ frag = intToString arg.toInt⌝ ∨
    (∃ name, ⌜fmt = 0x800192c8#64 ∧ frag = "<fn " ++ name ++ ">"⌝ ∗ strAt arg.toNat name) ∨
    (∃ name, ⌜fmt = 0x800192d8#64 ∧ frag = "<native fn " ++ name ++ ">"⌝ ∗ strAt arg.toNat name))

instance (fmt arg : BitVec 64) (frag : String) : Persistent (fprintfOut (GF := GF) fmt arg frag) := by
  unfold fprintfOut; infer_instance

/-- A stdout call: arguments `args`, the read-only input `R`; the console grows
by `frag` and newlib's data stays in its boundary state. -/
def outSpec (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live)) (entry : BitVec 64)
    (args : List (BitVec 64)) (R : IProp GF) (s : BitVec 64) (need : Nat) (cs : Nat → BitVec 64)
    (o frag : String) : IProp GF :=
  fnSpecW Wp entry
    (fun _ => iprop(argsAt args ∗ R ∗ stdioOwn ∗ consoleOwn o ∗ callFrame s need calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗ stdioOwn ∗ consoleOwn (o ++ frag) ∗
      callFrame s need calleeSaved cs))

/-- `snprintf(buf, 64, "<fn %s>", name)`: the rendering, cut to 63 characters,
and a NUL, in `buf[0, 64)`. -/
def snprintfFnSpec (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (s buf name : BitVec 64) (x : String) (cs : Nat → BitVec 64) : IProp GF :=
  fnSpecW Wp snprintfEntry
    (fun _ => iprop(argsAt [buf, 64#64, 0x800192c8#64, name] ∗ blockOwn buf.toNat 64 ∗
      strAt name.toNat x ∗ stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗
      (∃ img, ownImg (InExt (buf.toNat, 64)) img ∗ ⌜CStrImg img buf.toNat (fnRender x)⌝) ∗
      stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))

/-- `snprintf(buf, 64, "%lld", i)`: the decimal digits and a NUL in
`buf[0, 64)` (at most 20 characters, so never cut). -/
def snprintfIntSpec (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (s buf i : BitVec 64) (cs : Nat → BitVec 64) : IProp GF :=
  fnSpecW Wp snprintfEntry
    (fun _ => iprop(argsAt [buf, 64#64, 0x800192c0#64, i] ∗ blockOwn buf.toNat 64 ∗
      stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗
      (∃ img, ownImg (InExt (buf.toNat, 64)) img ∗ ⌜CStrImg img buf.toNat (intToString i.toInt)⌝) ∗
      stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))

end Specs

/-- **newlib's stdout calls at the binary** (`IrisHoles.out`), for every Iris
instance, every `live` set holding the code, and both WPs. -/
structure OutHoles : Prop where
  /-- `fputs(str, stdout)` prints the string. -/
  fputs : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (str s : BitVec 64) (cs : Nat → BitVec 64)
    (frag o : String), CodeLive live → SpIn s outNeed →
    ⊢ outSpec live Wp fputsEntry [str, stdoutFile] (strAt str.toNat frag) s outNeed cs o frag
  /-- `fputc(c, stdout)` prints the character. -/
  fputc : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (c : BitVec 8) (s : BitVec 64)
    (cs : Nat → BitVec 64) (o : String), CodeLive live → SpIn s outNeed →
    ⊢ outSpec live Wp fputcEntry [BitVec.zeroExtend 64 c, stdoutFile] iprop(emp) s outNeed cs o
        (toString (Char.ofNat c.toNat))
  /-- `fwrite(buf, 1, n, stdout)` of a C string's `n` bytes prints them. -/
  fwrite : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (buf s : BitVec 64) (cs : Nat → BitVec 64)
    (frag o : String), CodeLive live → SpIn s fwriteNeed →
    ⊢ outSpec live Wp fwriteEntry [buf, 1#64, BitVec.ofNat 64 frag.toList.length, stdoutFile]
        (strAt buf.toNat frag) s fwriteNeed cs o frag
  /-- `fprintf(stdout, fmt, arg)` with `value_print`'s formats. -/
  fprintf : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (fmt arg s : BitVec 64) (cs : Nat → BitVec 64)
    (frag o : String), CodeLive live → SpIn s fprintfNeed →
    ⊢ outSpec live Wp fprintfEntry [stdoutFile, fmt, arg] (fprintfOut fmt arg frag) s fprintfNeed
        cs o frag
  /-- `snprintf(buf, 64, "<fn %s>", name)` renders into the buffer. -/
  snprintfFn : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s buf name : BitVec 64) (x : String)
    (cs : Nat → BitVec 64), CodeLive live → SpIn s snprintfNeed →
    ⊢ snprintfFnSpec live Wp s buf name x cs
  /-- `snprintf(buf, 64, "%lld", i)` renders the integer into the buffer. -/
  snprintfInt : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s buf i : BitVec 64) (cs : Nat → BitVec 64),
    CodeLive live → SpIn s snprintfNeed → ⊢ snprintfIntSpec live Wp s buf i cs

end VsaIris.Newlib
