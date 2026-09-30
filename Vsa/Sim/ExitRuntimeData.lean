import Vsa.Sim.ConsoleStream
import Vsa.RuntimeRepr

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

def ExitRegionFoot (regions : List (Nat × Nat)) (address : Nat) : Prop :=
  ∃ region ∈ regions, region.1 ≤ address ∧ address < region.1 + region.2

def exitIdleFileRegions (file : Nat) : List (Nat × Nat) :=
  [(file + 8, 4), (file + 16, 2), (file + 18, 2),
   (file + 48, 8), (file + 80, 8), (file + 88, 8),
   (file + 112, 4), (file + 120, 8), (file + 160, 8),
   (file + 176, 4)]

def exitRuntimeExtraRegions : List (Nat × Nat) :=
  [(exitAtexitAddr, 8), (exitAtexitLockAddr, 8),
   (exitStdioHandlerAddr, 8), (exitGlueAddr, 8),
   (exitGlueAddr + 8, 4), (exitGlueAddr + 16, 8),
   (consoleStdout + 80, 8), (consoleStdout + 88, 8),
   (consoleStdout + 120, 8)] ++
  exitIdleFileRegions exitStdin ++ exitIdleFileRegions exitStderr

def ExitRuntimeExtraFoot : Nat → Prop :=
  ExitRegionFoot exitRuntimeExtraRegions

def exitFixedImageRegions : List (Nat × Nat) :=
  [(0x80000000, 0x18be0), (0x80018be0, 0x2110)]

def exitMainSavedRegions : List (Nat × Nat) :=
  [(exitMainSavedS0, 16)]

def exitProtectedRegions : List (Nat × Nat) :=
  exitFixedImageRegions ++ exitRuntimeExtraRegions ++ exitMainSavedRegions

def ExitProtectedFoot : Nat → Prop :=
  ExitRegionFoot exitProtectedRegions

def ProtectedInitialByte : Nat → Prop :=
  ExitProtectedFoot

end Vsa.Sim
