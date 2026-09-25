import VsaIris.Vsa.StdioRead
import VsaIris.DlHeap

/-!
# newlib's data after a `stderr` write, and `errno` (lane N3)

* **`errno`** (`Stdio.errnoFoot`, N1) is also written on the close path
  (`_fstat_r`, `_close_r`), so the stderr specs borrow `errnoOwn` too.
* **`StdioErrOK`**: the state a single `fwrite`/`fprintf` to `stderr` leaves.
  `stderr`'s `FILE` has been oriented (`__SORD`), set up for writing (`__SWR`)
  and given its one-byte unbuffered buffer `_nbuf` (`__smakebuf_r`), with no
  byte pending (`_p = _bf._base`). Every other field `exit`'s close path reads
  is as in `StdioOK` (`CloseCommon`).
-/

namespace VsaIris.Stdio

open Vsa.MemRepr Vsa.Sim

/-- `stderr`'s `FILE` after one unbuffered write: flags
`__SORD | __SRW | __SWR | __SNBF` (`0x201a`), the one-byte buffer `_nbuf`
(`file + 119`) installed with nothing pending, and the fields `_fclose_r`
reads as at the boundary. -/
structure ErrWrittenFile (m : Mem) (file : Nat) : Prop where
  flags_read : readLE m (file + 16) 2 = some 0x201a
  descriptor_read : readLE m (file + 18) 2 = some 2
  cursor : read64 m file = some (file + 119)
  base : read64 m (file + 24) = some (file + 119)
  cookie : read64 m (file + 48) = some file
  closeCallback : read64 m (file + 80) = some exitSclose
  ungetcBuffer : read64 m (file + 88) = some 0
  lineBuffer : read64 m (file + 120) = some 0
  lock : read64 m (file + 160) = some 0
  lockMode : read32 m (file + 176) = some 0

/-- What `exit`'s close path reads besides `stderr`'s `FILE`: VSA's
`ConsoleStream` and `ExitRuntimeData` without its `stderr` field. -/
structure CloseCommon (m : Mem) : Prop where
  console : ConsoleStream m
  atexit : read64 m exitAtexitAddr = some 0
  stdioHandler : read64 m exitStdioHandlerAddr = some exitStdioHandler
  glueNext : read64 m exitGlueAddr = some 0
  glueCount : read32 m (exitGlueAddr + 8) = some 3
  glueFiles : read64 m (exitGlueAddr + 16) = some exitStdin
  stdin : ExitIdleFile m exitStdin 4 0
  stdoutClose : read64 m (consoleStdout + 80) = some exitSclose
  stdoutUngetc : read64 m (consoleStdout + 88) = some 0
  stdoutLine : read64 m (consoleStdout + 120) = some 0

theorem CloseCommon.of_exitRuntimeData {m : Mem} (hc : ConsoleStream m) (h : ExitRuntimeData m) :
    CloseCommon m :=
  ⟨hc, h.atexit, h.stdioHandler, h.glueNext, h.glueCount, h.glueFiles, h.stdin, h.stdoutClose,
    h.stdoutUngetc, h.stdoutLine⟩

/-- **newlib's data after one write to `stderr`**, read off an image of
`stdioFoot` like `StdioOK`. -/
def StdioErrOK (img : Nat → BitVec 8) : Prop :=
  ∀ m : Mem, (∀ a, stdioFoot a → m[a]? = some (img a)) →
    CloseCommon m ∧ ErrWrittenFile m exitStderr ∧ read64 m stderrPtrAddr = some exitStderr

/-- The two states `exit`'s close path starts from, as one read-off
description: the common part and `stderr` idle or written. -/
def CloseReady (img : Nat → BitVec 8) : Prop :=
  ∀ m : Mem, (∀ a, stdioFoot a → m[a]? = some (img a)) →
    CloseCommon m ∧ (ExitIdleFile m exitStderr 0x12 2 ∨ ErrWrittenFile m exitStderr)

theorem StdioOK.closeReady {img : Nat → BitVec 8} (h : StdioOK img) : CloseReady img :=
  fun m hm => by
    obtain ⟨hc, hx, _⟩ := h m hm
    exact ⟨CloseCommon.of_exitRuntimeData hc hx, .inl hx.stderr⟩

theorem StdioErrOK.closeReady {img : Nat → BitVec 8} (h : StdioErrOK img) : CloseReady img :=
  fun m hm => by
    obtain ⟨hc, hx, _⟩ := h m hm
    exact ⟨hc, .inr hx⟩

end VsaIris.Stdio
