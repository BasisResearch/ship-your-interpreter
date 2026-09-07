import Vsa.Sim.ConsoleStream
import Vsa.RuntimeRepr

/-!
Initialized exit data at the concrete interpreter-entry snapshot.

Source: c/while-riscv-htif.elf, SHA256
b146c6edb76ea9a0f0f30be381f8176ed2de9717e1ae9b37feff4b2b9ca1d0f0.
The fields describe memory reads, without execution or preservation premises.

The initial boundary supplies this record. Actual interpreter/native effects
must reestablish it at the reached main continuation. The close sequence then
consumes it and intentionally changes FILE flags and stdout cursor/counts.
-/

open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim

def exitAtexitAddr : Nat := 0x8001b9f8
def exitAtexitLockAddr : Nat := 0x8001b978
def exitStdioHandlerAddr : Nat := 0x8001b9b0
def exitStdioHandler : Nat := 0x80005d18
def exitGlueAddr : Nat := 0x8001b520
def exitStdin : Nat := 0x8001ba68
def exitStderr : Nat := 0x8001bbd8
def exitSclose : Nat := 0x8000f0c0
def exitMainSavedS0 : Nat := 0x87fffff0

/-- The initialized stdin/stderr fields actually read by the empty close path.
`readCount` and `savedReadCount` prevent the seek branch of `__sflush_r`.
The zero auxiliary pointers and concrete flags prevent the free branches.
These are byte-memory reads; the branch claims still require machine proofs. -/
structure ExitIdleFile (m : Mem) (file flags descriptor : Nat) : Prop where
  flags_read : readLE m (file + 16) 2 = some flags
  descriptor_read : readLE m (file + 18) 2 = some descriptor
  readCount : read32 m (file + 8) = some 0
  savedReadCount : read32 m (file + 112) = some 0
  cookie : read64 m (file + 48) = some file
  closeCallback : read64 m (file + 80) = some exitSclose
  ungetcBuffer : read64 m (file + 88) = some 0
  lineBuffer : read64 m (file + 120) = some 0
  lock : read64 m (file + 160) = some 0
  lockMode : read32 m (file + 176) = some 0

/-- Additional initialized runtime data, extending the separately supplied
ConsoleStream invariant. No exact value is needed for the atexit lock argument: the reached
recursive-lock stubs do not dereference it. The stdio handler is the actual
nonzero value installed by global_stdio_init, not the zero ELF initializer. -/
structure ExitRuntimeData (m : Mem) : Prop where
  atexit : read64 m exitAtexitAddr = some 0
  atexitLock : ∃ word : Nat, read64 m exitAtexitLockAddr = some word
  stdioHandler : read64 m exitStdioHandlerAddr = some exitStdioHandler
  glueNext : read64 m exitGlueAddr = some 0
  glueCount : read32 m (exitGlueAddr + 8) = some 3
  glueFiles : read64 m (exitGlueAddr + 16) = some exitStdin
  stdin : ExitIdleFile m exitStdin 4 0
  stderr : ExitIdleFile m exitStderr 0x12 2
  stdoutClose : read64 m (consoleStdout + 80) = some exitSclose
  stdoutUngetc : read64 m (consoleStdout + 88) = some 0
  stdoutLine : read64 m (consoleStdout + 120) = some 0

/-- A finite union of half-open byte extents `(base, size)`. -/
def ExitRegionFoot (regions : List (Nat × Nat)) (address : Nat) : Prop :=
  ∃ region ∈ regions, region.1 ≤ address ∧ address < region.1 + region.2

def exitIdleFileRegions (file : Nat) : List (Nat × Nat) :=
  [(file + 8, 4), (file + 16, 2), (file + 18, 2),
   (file + 48, 8), (file + 80, 8), (file + 88, 8),
   (file + 112, 4), (file + 120, 8), (file + 160, 8),
   (file + 176, 4)]

/-- Exactly the bytes supporting the newly added fields. Excludes padding,
errno, lock pointees, and fields already maintained by ConsoleStream. -/
def exitRuntimeExtraRegions : List (Nat × Nat) :=
  [(exitAtexitAddr, 8), (exitAtexitLockAddr, 8),
   (exitStdioHandlerAddr, 8), (exitGlueAddr, 8),
   (exitGlueAddr + 8, 4), (exitGlueAddr + 16, 8),
   (consoleStdout + 80, 8), (consoleStdout + 88, 8),
   (consoleStdout + 120, 8)] ++
  exitIdleFileRegions exitStdin ++ exitIdleFileRegions exitStderr

def ExitRuntimeExtraFoot : Nat → Prop :=
  ExitRegionFoot exitRuntimeExtraRegions

/-- Exact byte support of the existing ConsoleStream record. This is a read
support, not a claim that printing leaves every byte unchanged. In particular,
the buffer byte may change while its existence is preserved. -/
def exitConsoleReadRegions : List (Nat × Nat) :=
  [(consoleImpurePtrAddr, 8), (consoleReent + 16, 8),
   (consoleReent + 72, 8), (consoleStdout, 8),
   (consoleStdout + 8, 4), (consoleStdout + 12, 4),
   (consoleStdout + 16, 2), (consoleStdout + 18, 2),
   (consoleStdout + 24, 8), (consoleStdout + 32, 4),
   (consoleStdout + 40, 4), (consoleStdout + 48, 8),
   (consoleStdout + 64, 8), (consoleStdout + 160, 8),
   (consoleStdout + 176, 4), (consoleBuf, 1)]

/-- Support for every memory fact in ExitRuntimeData. -/
def ExitRuntimeDataFoot : Nat → Prop :=
  ExitRuntimeExtraFoot

/-- Support for ExitRuntimeData and the separately maintained ConsoleStream. -/
def ExitRuntimeWithConsoleFoot : Nat → Prop :=
  ExitRegionFoot (exitRuntimeExtraRegions ++ exitConsoleReadRegions)

/-- Whole fixed .text and .rodata coverage. Values come from separate generated
image predicates; these extents specify protection, not arbitrary byte data. -/
def exitFixedImageRegions : List (Nat × Nat) :=
  [(0x80000000, 0x18be0), (0x80018be0, 0x2110)]

def ExitFixedImageFoot : Nat → Prop :=
  ExitRegionFoot exitFixedImageRegions

/-- Preserve until main reloads its pair at 0x800045f0/0x800045f4. The exit
routine subsequently reuses this stack space, so protection expires there. -/
def exitMainSavedRegions : List (Nat × Nat) :=
  [(exitMainSavedS0, 16)]

def ExitMainSavedFoot : Nat → Prop :=
  ExitRegionFoot exitMainSavedRegions

/-- Extra unchanged bytes needed through the interpreter. ConsoleStream has
its own invariant: requiring equality of its entire byte support would
incorrectly restrict the mutable output buffer. Native output proofs must
establish this extra frame from their actual writes; ConsoleFoot exclusion
alone does not suffice for stdout's new close/auxiliary-pointer fields. -/
def exitProtectedRegions : List (Nat × Nat) :=
  exitFixedImageRegions ++ exitRuntimeExtraRegions ++ exitMainSavedRegions

def ExitProtectedFoot : Nat → Prop :=
  ExitRegionFoot exitProtectedRegions

/-- Public boundary name: bytes protected through the interpreter, before
the reached main/exit continuation consumes the saved pair and runtime data. -/
def ProtectedInitialByte : Nat → Prop :=
  ExitProtectedFoot

/-- Concrete geometry only: every protected extent is outside the arena.
Existing console/stack/allocator geometry obligations remain separate.
This imposes no allocator implementation, success, or resource bound. -/
def ExitArenaDisjoint (arena : Arena) : Prop :=
  ∀ address, ProtectedInitialByte address →
    ¬ (arena.lo ≤ address ∧ address < arena.hi)

end Vsa.Sim
