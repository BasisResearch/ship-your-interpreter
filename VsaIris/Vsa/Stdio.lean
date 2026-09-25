import VsaIris.MallocRun
import VsaIris.Vsa.ImpureRO
import Vsa.Sim.ExitRuntimeData
import Vsa.Sim.LocaleData
import Vsa.Sim.StderrStream

/-!
# newlib's runtime data (INTERP_DESIGN.md §4.2, package H5)

`printf`-family calls, `fwrite` and `exit` read and write newlib's global
state: the reentrancy record `_impure_data`, the three `FILE` objects `__sf`,
the `__sglue` list, the `atexit` list and its lock, and the stdio exit
handler. The allocator owns its own globals (`VsaHeap.allocGlobal`, which
includes the reentrancy record's `_errno` word). `stdioFoot` is every other
byte of `.data`/`.bss` from `__sglue` to `__bss_end`, so the two footprints
partition that range (`nm c/while-riscv-htif.elf`).

`StdioOK` is the state the interpreter keeps at every boundary: VSA's
`ConsoleStream` (stdout's `FILE`, unbuffered, `_w = 0`, the `__swrite`
callback) and `ExitRuntimeData` (empty `atexit` list, the installed
`stdio_exit_handler`, idle stdin/stderr) and `_impure_data._stderr`.
`InterpRunPhysicalFacts.console` and `.exit_runtime` supply the first two at
the boundary; the `stderr` pointer is not yet a boundary field
(INTERP_DESIGN.md Q6).
-/

namespace VsaIris.Stdio

open Iris Iris.BI Iris.Std Iris.ProofMode
open Vsa.MemRepr Vsa.Sim

/-- `lo ≤ a < hi`. -/
def InRange (lo hi a : Nat) : Prop := lo ≤ a ∧ a < hi

/-- newlib's runtime data outside the allocator's globals: `__sglue`,
`_impure_data` without `_errno`, the locale records, `_impure_ptr`, the
`atexit` lock, `__stdio_exit_handler`, the lock words, `__atexit`,
`_PathLocale`, `initial_env`, `__sf`, the locale buffers and `__atexit0`. -/
def stdioFoot (a : Nat) : Prop :=
  InRange 0x8001b520 0x8001b538 a ∨ InRange 0x8001b53c 0x8001b960 a ∨
  InRange 0x8001b970 0x8001b990 a ∨ InRange 0x8001b9b0 0x8001ba08 a ∨
  InRange 0x8001ba0c 0x8001ba18 a ∨ InRange 0x8001ba68 0x8001c168 a

/-- `_impure_data._stderr` (`reent + 24`) points at `__sf[2]`. `main`'s error
line loads its stream from there (`ld a0,24(a5)`); neither `ConsoleStream`
nor `ExitRuntimeData` pins it. -/
def stderrPtrAddr : Nat := consoleReent + 24

/-- The runtime data the interpreter keeps at every boundary, read off an
image of `stdioFoot`: any memory agreeing with the image there satisfies
`ConsoleStream`, `ExitRuntimeData` and the `stderr` pointer (all read only
inside `stdioFoot`). -/
def StdioOK (img : Nat → BitVec 8) : Prop :=
  ∀ m : Mem, (∀ a, stdioFoot a → m[a]? = some (img a)) →
    ConsoleStream m ∧ ExitRuntimeData m ∧ read64 m stderrPtrAddr = some exitStderr ∧
      LocaleData m ∧ StderrStream m

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The bytes of newlib's data `stdioAt` owns exclusively: all but `_impure_ptr`. -/
def stdioExcl (a : Nat) : Prop := stdioFoot a ∧ ¬ impureW a

/-- newlib's runtime data at some image satisfying `P`: `_impure_ptr`
read-only, every other byte exclusively owned. -/
def stdioAt (P : (Nat → BitVec 8) → Prop) : IProp GF :=
  iprop(∃ img, ⌜P img ∧ ImpureImg img⌝ ∗ ownSet stdioExcl (fun a => a ↦ₘ img a) ∗ impureRO)

/-- newlib's runtime data in its boundary state. -/
abbrev stdioOwn : IProp GF := stdioAt StdioOK

theorem stdioAt_mono {P Q : (Nat → BitVec 8) → Prop} (h : ∀ img, P img → Q img) :
    stdioAt (GF := GF) P ⊢ stdioAt Q := by
  unfold stdioAt
  iintro ⟨%img, %⟨hp, hi⟩, H, #Hr⟩
  iexists img
  iframe H Hr
  ipureintro
  exact ⟨h img hp, hi⟩

/-- `_impure_ptr` out of newlib's data, persistently. -/
theorem stdioAt_impure (P : (Nat → BitVec 8) → Prop) :
    stdioAt (GF := GF) P ⊢ stdioAt P ∗ impureRO := by
  unfold stdioAt
  iintro ⟨%img, %hp, H, #Hr⟩
  isplitl [H]
  · iexists img
    iframe H Hr
    ipureintro
    exact hp
  · iexact Hr

end Own

end VsaIris.Stdio
