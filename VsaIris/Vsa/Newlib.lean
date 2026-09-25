import VsaIris.Vsa.BinImg
import VsaIris.CallAbort
import VsaIris.Vsa.Console
import Vsa.Sim.Code.FixedImage
import Vsa.Sim.LayoutInstance
import VsaIris.Vsa.HeapShape
import VsaIris.Vsa.StdioErr

/-!
# `IrisHoles.newlib`: the newlib calls on the error and exit paths (H5)

INTERP_DESIGN.md Q4: the newlib formatter and stdio writer stay unproved for
now. Each is an exact Iris statement about the fixed binary, a field of
`NewlibHolesAt` (hence of `IrisHoles`) with a row in `VsaIris/HOLES.md`:

* `snprintf` (`0x80005c44`) with a format whose conversions are `%s`/`%d`:
  `runtime_error`'s two calls, and `interp_run`'s top-level status messages;
* `fprintf` (`0x800061c0`) to `stderr` with `main`'s format: `main`'s
  `fprintf(stderr, "%s\n", in->err_msg)` (its only call);
* (`fwrite` (`0x80005260`) to `stderr`, the out-of-memory message, is proved:
  `Stderr/FwriteSpec.lean`, lane N3);
* `exitHandlers`: the newlib interior of `exit` (`0x80004778`–`0x80004788`:
  `__call_exitprocs(e, 0)`, then the installed `__stdio_exit_handler`).

Every statement holds for both WPs (`∀ Wp`), so the total route's `exit(0)`
uses the same fields. Every precondition's `StdioOK` admits `stdout` unoriented
(`_flags = 0x000a`, no console write yet: a run that printed nothing reaches
`exit` so) or oriented (`0x200a`); see `Vsa.Sim.ConsoleStreamAt`. `stderr` output reaches the console: `_write` ignores
its descriptor and stores to `tohost`, so `fprintf`/`fwrite` hand back
`consoleOwn (o ++ o')` for some `o'`.

After a write to `stderr` its `FILE` object has left VSA's `ExitRuntimeData`
state (`__swsetup_r` sets `__SWR`, `__smakebuf_r` installs the one-byte
buffer). That state is `Ierr`, a parameter of `NewlibHolesAt`; lane N3 fixed
it to `StdioErrOK` (`StdioErr.lean`), the state `fwrite` provably leaves:
`NewlibHoles := NewlibHolesAt StdioErrOK`.

The stack needs are measured frame chains of the binary, rounded up:
`snprintf` 272 + `_svfprintf_r` 592 + `__ssprint_r` 64 = 928;
`fprintf` 80 + `_vfprintf_r` 592 + `__sbprintf` 1264 + `_vfprintf_r` 592 +
the write path ≈ 3200; `fwrite` 112 + `__sfvwrite_r` 96 + `__swsetup_r` 32 +
`__smakebuf_r` 160 + `__swhatbuf_r` 160 + `_fstat_r` 16 + `_fstat` 16 = 592;
`__call_exitprocs` 96, `_fwalk_sglue` 80 + `_fclose_r` 32 + `__sflush_r` 48 +
`__swrite` 48 + `_lseek_r`/`_write_r` 16 + 16 = 240. `exit` runs at
`main`'s stack top, where the 256 bytes below its own frame are `err_msg`: the
rest of `struct Interp` below is read-only (`globals`, the `jmp_buf`), so
`exitHandlersNeed` cannot exceed 256.
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

/-- A NUL within `n` bytes of `p`, all inside `R`, makes a C string there: the
bytes before the first NUL. -/
theorem cstrCov_of_nul {R : Nat → Prop} {rd : Nat → BitVec 8} {p : Nat} :
    ∀ {n : Nat}, (∀ i, i < n → R (p + i)) → (∃ k, k < n ∧ rd (p + k) = 0) →
      ∃ t, CStrCov R rd p t
  | 0, _, ⟨_, hk, _⟩ => absurd hk (Nat.not_lt_zero _)
  | n + 1, hR, h => by
    by_cases h' : ∃ k, k < n ∧ rd (p + k) = 0
    · exact cstrCov_of_nul (fun i hi => hR i (by omega)) h'
    · obtain ⟨k, hk, h0⟩ := h
      have hkn : k = n := by
        apply Classical.byContradiction; intro hne; exact h' ⟨k, by omega, h0⟩
      subst hkn
      refine ⟨(List.range k).map (fun i => rd (p + i)), ⟨fun i hi => ?_, ?_⟩⟩
      · have hi' : i < k := by simpa using hi
        refine ⟨hR i (by omega), by simp, ?_⟩
        simpa using fun hz => h' ⟨i, hi', hz⟩
      · simp only [List.length_map, List.length_range]
        exact ⟨hR k (by omega), h0⟩

/-- A C string of the fixed `.rodata`, read through any `rd` that agrees with
the image there. The byte facts are one `decide` over the image. -/
theorem cstrCov_rodata {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) {p : Nat} {bs : List (BitVec 8)}
    (hb : ∀ i (h : i < bs.length), rodataDom (p + i) ∧ rodataByte (p + i) = bs[i] ∧ bs[i] ≠ 0)
    (hn : rodataDom (p + bs.length) ∧ rodataByte (p + bs.length) = 0) : CStrCov R rd p bs where
  bytes i h := by
    obtain ⟨hd, hbv, hnz⟩ := hb i h
    obtain ⟨hR, hrd⟩ := hro _ hd
    exact ⟨hR, hrd.trans hbv, hnz⟩
  nul := by
    obtain ⟨hR, hrd⟩ := hro _ hn.1
    exact ⟨hR, hrd.trans hn.2⟩

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
def exitHandlersNeed : Nat := 256

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

/-- `main`'s error-line format `"%s\n"` (`0x800195e0`, `.rodata`). -/
def errLineFmt : BitVec 64 := 0x800195e0#64

/-- `fprintf(stderr, "%s\n", p)` (`main`'s error line): prints some string,
reads the NUL-terminated string at `p` inside the owned `n`-byte buffer
(handed back unchanged), clears `errno`, leaves newlib's data in the
post-`stderr`-write state `StdioErrOK`, returns (to an aligned address). -/
def fprintfSpec (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live)) (s p : BitVec 64)
    (n : Nat) (bv : Nat → BitVec 8) (cs : Nat → BitVec 64) (o : String) : IProp GF :=
  fnSpecW Wp fprintfEntry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt [stderrFile, errLineFmt, p] ∗
      ownImg (InExt (p.toNat, n)) bv ∗ stdioOwn ∗ errnoOwn ∗ consoleOwn o ∗
      callFrame s fprintfNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗ ownImg (InExt (p.toNat, n)) bv ∗ stdioAt StdioErrOK ∗
      errnoOwn ∗ (∃ o', consoleOwn (o ++ o')) ∗ callFrame s fprintfNeed calleeSaved cs))

/-- `fwrite(ptr, 1, n, stderr)`: prints some string, reads `ptr[0, n)`,
clears `errno`, leaves newlib's data in the post-write state `StdioErrOK`,
returns (to an aligned return address; lane N3: proved, `Stderr/FwriteSpec.lean`). -/
def fwriteSpec (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s ptr n : BitVec 64) (cs : Nat → BitVec 64)
    (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8) (o : String) : IProp GF :=
  fnSpecW Wp fwriteEntry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt [ptr, 1#64, n, stderrFile] ∗ readable Sro Sown rd ∗
      stdioOwn ∗ errnoOwn ∗ consoleOwn o ∗ callFrame s fwriteNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗ readable Sro Sown rd ∗ stdioAt StdioErrOK ∗ errnoOwn ∗
      (∃ o', consoleOwn (o ++ o')) ∗ callFrame s fwriteNeed calleeSaved cs))

/-- The newlib interior of `exit(e)`: from `jal __call_exitprocs` at
`0x80004778` (`a0 = s0 = e`, `a1 = 0`, `sp` after `exit`'s prologue) to its
`mv a0,s0` at `0x80004788`, with `s0` still `e`. Runs from newlib's boundary
state or from `Ierr`. From `Ierr` it may print (the `stderr` close path). From
the boundary state (`quiet`: no `stderr` write happened) it prints nothing:
`stdout` is unbuffered (`main`'s `setvbuf(stdout, 0, _IONBF, 0)`), so no
stream has pending bytes to flush. `term_sim`'s `exit(0)` needs this. It owns
`errno` (`errnoOwn`): `_close_r` clears it on each of the three closes. -/
def exitHandlersSpec (Ierr : (Nat → BitVec 8) → Prop) (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s e r : BitVec 64) (cs : Nat → BitVec 64)
    (o : String) (Φ : Nat × String → IProp GF) (quiet : Bool) : IProp GF :=
  iprop(PC ↦ᵣ exitHandlersPC ∗ ra ↦ᵣ r ∗ (8 : Nat) ↦ᵣ e ∗ argsAt [e, 0#64] ∗
      stdioAt (fun img => StdioOK img ∨ (quiet = false ∧ Ierr img)) ∗ errnoOwn ∗ consoleOwn o ∗
      callFrame s exitHandlersNeed (calleeSaved.drop 1) cs ∗
      (PC ↦ᵣ exitHandlersEnd -∗ (∃ w, ra ↦ᵣ w) -∗ (8 : Nat) ↦ᵣ e -∗ clobbered argRegs -∗
        stdioAt (fun _ => True) -∗ errnoOwn -∗
        (∃ o', ⌜quiet = true → o' = ""⌝ ∗ consoleOwn (o ++ o')) -∗
        callFrame s exitHandlersNeed (calleeSaved.drop 1) cs -∗ Wp.W Φ)
    -∗ Wp.W Φ)

end Specs

/-! ## The holes -/

/-- The assumed newlib statements at the post-`stderr`-write state `Ierr`,
for every Iris instance, every `live` set holding the code, and both WPs. -/
structure NewlibCoreAt (Ierr : (Nat → BitVec 8) → Prop) : Prop where
  /-- `snprintf` with a `%s`/`%d` format (`runtime_error`, `interp_run`). -/
  snprintf : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s dst n fmt : BitVec 64) (args : List (BitVec 64))
    (cs : Nat → BitVec 64) (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8),
    CodeLive live → args.length ≤ 5 → 0 < n.toNat → n.toNat < 2 ^ 31 →
    FmtArgsOK (fun a => Sro a ∨ Sown a) rd fmt args → SpIn s snprintfNeed →
    ⊢ snprintfSpec live Wp s dst n fmt args cs Sro Sown rd
  /-- `fprintf(stderr, "%s\n", p)` (`main`'s error line): a NUL within the
  `n < 2^30` owned bytes at `p`, in RAM, whose word-at-a-time `strlen` stays off
  the `tohost` cells; the frame above newlib's data. -/
  fprintf : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s p : BitVec 64) (n : Nat) (bv : Nat → BitVec 8)
    (cs : Nat → BitVec 64) (o : String),
    CodeLive live → (∃ k, k < n ∧ bv (p.toNat + k) = 0) → n < 2 ^ 30 →
    0x80000000 ≤ p.toNat → p.toNat + n + 8 ≤ 0x100000000 →
    (p.toNat + n + 8 ≤ Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 8 ≤ p.toNat) →
    SpIn s fprintfNeed → 0x80100000 ≤ s.toNat - fprintfNeed →
    ⊢ fprintfSpec live Wp s p n bv cs o

/-- The newlib statements the proofs use: the assumed ones and `exit`'s
interior, which `ExitH/Iris.lean` proves from `CloseReady` (`NewlibCore.full`). -/
structure NewlibHolesAt (Ierr : (Nat → BitVec 8) → Prop) : Prop extends NewlibCoreAt Ierr where
  /-- The newlib interior of `exit` (proved: `ExitH.exitHandlers_spec`). -/
  exitHandlers : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (s e r : BitVec 64) (cs : Nat → BitVec 64)
    (o : String) (Φ : Nat × String → IProp GF) (quiet : Bool),
    CodeLive live → SpIn s exitHandlersNeed →
    ⊢ exitHandlersSpec Ierr live Wp s e r cs o Φ quiet

/-- **`IrisHoles.newlib`**: the assumed newlib statements at the post-`stderr`-write
state `StdioErrOK` (lane N3: the state `fwrite` provably leaves,
`Stderr/FwriteSpec.lean`). `exit`'s interior is proved from it (`NewlibCore.full`). -/
def NewlibCore : Prop := NewlibCoreAt StdioErrOK

/-- The newlib statements the proofs use, at `StdioErrOK`. -/
def NewlibHoles : Prop := NewlibHolesAt StdioErrOK

/-- The post-`stderr`-write state. -/
abbrev stdioErr (img : Nat → BitVec 8) : Prop := StdioErrOK img

theorem NewlibHoles.at (h : NewlibHoles) : NewlibHolesAt stdioErr := h

end VsaIris.Newlib
