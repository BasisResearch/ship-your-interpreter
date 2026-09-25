import VsaIris.Vsa.Newlib
import VsaIris.Interp.Repr

/-!
# `OutHoles`: newlib's stdout calls (H2), all proved

`value_print` and the natives print through newlib's stdio: `fputs`,
`fputc`, `fwrite` and `fprintf` on `stdout`. `stdout` is unbuffered at every
boundary (`ConsoleStreamAt o`, part of `StdioOK`: `_w = 0`, a one-byte buffer,
the `__swrite` callback), so each call reaches `_write`'s `tohost` store
(`putcSite`) before it returns, and newlib's data is back in its boundary
state. The precondition `stdioOwn` admits both orientations: the first
console write of a run starts from `_flags = 0x000a` (`interp_run`'s entry,
`ConsoleBoot`) and its `ORIENT` block sets `__SORD`
(`Stdio.StdioOKAt.orient`, `VsaIris/Vsa/StdioOrient.lean`); every later one
starts from `0x200a`. The postcondition is the oriented state, weakened to
`stdioOwn`. `stringify`'s named-closure arm renders through
`snprintf(buf, 64, "<fn %s>", name)`.

INTERP_DESIGN.md Q4: like H5's `NewlibHoles`, these stay unproved for now.
Each is an exact Iris statement about the fixed binary, in H5's calling
convention (`argsAt`, `callFrame`), a field of `OutHoles`, since discharged
(`OutHoles.proved`; `IrisHoles` was then removed). Unlike H5's `stderr` calls,
these are exact about what they print: the console grows by the fragment.
The `snprintf` statements are proved (`VsaIris.Sym.snprintfInt_out`,
`VsaIris.Sym.snprintfFn_out`, `Vsa/SnpHoles.lean`) for a stack and buffer
above newlib's data.
`fputs`, `fputc` and `fwrite` are proved (`VsaIris.Sym.fputc_out`,
`Vsa/Stdout/OutSpec.lean`; `VsaIris.Sym.fputs_out`, `VsaIris.Sym.fwrite_out`,
`Vsa/Stdout/StrOut.lean`) for a stack above `.bss`; `fprintf` with `fprintfOut`'s formats is proved
(`VsaIris.Sym.Fp.fprintf_out`, `Vsa/Fprintf/Out.lean`) for a stack above
`0x80100000` with `interpText` live.

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
most 63 characters. The semantics renders a named closure the same way
(`Vsa.While.fnCatRender`, Q8). -/
def fnRender (x : String) : String := String.ofList (("<fn " ++ x ++ ">").toList.take 63)

theorem fnRender_eq (x : String) : fnRender x = Vsa.While.fnCatRender x := rfl

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
by `frag` and newlib's data stays in its boundary state. `stdioOwn` holds
`StdioOK`, either `stdout` orientation: a first call from `0x000a` is
covered. The call borrows libgloss's `errno` (`_write_r` clears it on every
write; an allocator global, lent by `ErrnoOwn.heapRes_errno`). -/
def outSpec (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live)) (entry : BitVec 64)
    (args : List (BitVec 64)) (R : IProp GF) (s : BitVec 64) (need : Nat) (cs : Nat → BitVec 64)
    (o frag : String) : IProp GF :=
  fnSpecW Wp entry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt args ∗ R ∗ stdioW ∗ consoleOwn o ∗
      callFrame s need calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗ stdioW ∗ consoleOwn (o ++ frag) ∗
      callFrame s need calleeSaved cs))

/-- `snprintf(buf, 64, "<fn %s>", name)`: the rendering, cut to 63 characters,
and a NUL, in `buf[0, 64)`. -/
def snprintfFnSpec (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (s buf name : BitVec 64) (x : String) (cs : Nat → BitVec 64) : IProp GF :=
  fnSpecW Wp snprintfEntry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt [buf, 64#64, 0x800192c8#64, name] ∗ blockOwn buf.toNat 64 ∗
      strAt name.toNat x ∗ stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗
      (∃ img, ownImg (InExt (buf.toNat, 64)) img ∗ ⌜CStrImg img buf.toNat (fnRender x)⌝) ∗
      stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))

/-- `snprintf(buf, 64, "%lld", i)`: the decimal digits and a NUL in
`buf[0, 64)` (at most 20 characters, so never cut). -/
def snprintfIntSpec (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (s buf i : BitVec 64) (cs : Nat → BitVec 64) : IProp GF :=
  fnSpecW Wp snprintfEntry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt [buf, 64#64, 0x800192c0#64, i] ∗ blockOwn buf.toNat 64 ∗
      stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗
      (∃ img, ownImg (InExt (buf.toNat, 64)) img ∗ ⌜CStrImg img buf.toNat (intToString i.toInt)⌝) ∗
      stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))

end Specs

/-- **newlib's stdout calls at the binary** (`OutHoles`), for every Iris
instance, every `live` set holding the code, and both WPs. -/
structure OutHoles : Prop where

/-- Every stdout call and `snprintf` rendering is proved (`Vsa/Stdout/`,
`Vsa/Fprintf/Out.lean`, `Vsa/SnpHoles.lean`); nothing is left assumed. -/
theorem OutHoles.proved : OutHoles := ⟨⟩

end VsaIris.Newlib
