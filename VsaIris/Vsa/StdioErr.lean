import VsaIris.Vsa.StdioRead
import VsaIris.DlHeap

namespace VsaIris.Stdio

open Vsa.MemRepr Vsa.Sim

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

structure CloseCommon (o : Bool) (m : Mem) : Prop where
  console : ConsoleStreamAt o m
  atexit : read64 m exitAtexitAddr = some 0
  stdioHandler : read64 m exitStdioHandlerAddr = some exitStdioHandler
  glueNext : read64 m exitGlueAddr = some 0
  glueCount : read32 m (exitGlueAddr + 8) = some 3
  glueFiles : read64 m (exitGlueAddr + 16) = some exitStdin
  stdin : ExitIdleFile m exitStdin 4 0
  stdoutClose : read64 m (consoleStdout + 80) = some exitSclose
  stdoutUngetc : read64 m (consoleStdout + 88) = some 0
  stdoutLine : read64 m (consoleStdout + 120) = some 0

theorem CloseCommon.of_exitRuntimeData {o : Bool} {m : Mem} (hc : ConsoleStreamAt o m)
    (h : ExitRuntimeData m) : CloseCommon o m :=
  ⟨hc, h.atexit, h.stdioHandler, h.glueNext, h.glueCount, h.glueFiles, h.stdin, h.stdoutClose,
    h.stdoutUngetc, h.stdoutLine⟩

def StdioErrOKAt (o : Bool) (img : Nat → BitVec 8) : Prop :=
  ∀ m : Mem, (∀ a, stdioFoot a → m[a]? = some (img a)) →
    CloseCommon o m ∧ ErrWrittenFile m exitStderr ∧ read64 m stderrPtrAddr = some exitStderr

def StdioErrOK (img : Nat → BitVec 8) : Prop := ∃ o, StdioErrOKAt o img

def CloseReadyAt (o : Bool) (img : Nat → BitVec 8) : Prop :=
  ∀ m : Mem, (∀ a, stdioFoot a → m[a]? = some (img a)) →
    CloseCommon o m ∧ (ExitIdleFile m exitStderr 0x12 2 ∨ ErrWrittenFile m exitStderr)

def CloseReady (img : Nat → BitVec 8) : Prop := ∃ o, CloseReadyAt o img

theorem StdioOK.closeReady {img : Nat → BitVec 8} (h : StdioOK img) : CloseReady img :=
  let ⟨o, h⟩ := h
  ⟨o, fun m hm => by
    obtain ⟨hc, hx, _⟩ := h m hm
    exact ⟨CloseCommon.of_exitRuntimeData hc hx, .inl hx.stderr⟩⟩

theorem StdioErrOK.closeReady {img : Nat → BitVec 8} (h : StdioErrOK img) : CloseReady img :=
  let ⟨o, h⟩ := h
  ⟨o, fun m hm => by
    obtain ⟨hc, hx, _⟩ := h m hm
    exact ⟨hc, .inr hx⟩⟩

end VsaIris.Stdio
