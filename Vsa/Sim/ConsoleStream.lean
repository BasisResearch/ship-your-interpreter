import Vsa.MemRepr
import Vsa.Sim.ReprSurvival
import Vsa.Sim.ValueSpec

/-!
# Initialized newlib stdout state

This is the post-CRT state used by the fixed interpreter image. It is not an
ELF-static predicate: CRT initialization changes the reentrancy record and the
`FILE` object before entering `interp_run`.

The pinned fields are exactly those followed by the successful output path:
`fputc -> _putc_r -> __swbuf_r -> _fflush_r -> __sflush_r -> __swrite ->
_write_r -> _write`.
The one-byte backing buffer may contain the most recently printed byte.
-/

open Vsa.MemRepr

namespace Vsa.Sim

def consoleImpurePtrAddr : Nat := 0x8001b970
def consoleReent : Nat := 0x8001b538
def consoleStdout : Nat := 0x8001bb20
def consoleBuf : Nat := 0x8001bb97
def consoleSinit : Nat := 0x80005d2c
def consoleSwrite : Nat := 0x8000efd4

/-- `stdout`'s `_flags`: `__SWR | __SNBF` (`0x000a`) as `main`'s
`setvbuf(stdout, 0, _IONBF, 0)` leaves it, and `0x200a` once a write has
oriented the stream (`__SORD`, set by `ORIENT` at the head of `_fputs_r`,
`_fwrite_r`, `_vfprintf_r` and `__swbuf_r`; `Vsa.Sim.ConsoleOrient`). -/
@[reducible] def consoleFlags (oriented : Bool) : Nat := if oriented then 0x200a else 0x000a

/-- The high byte of `consoleFlags`. -/
@[reducible] def consoleFlag1 (oriented : Bool) : BitVec 8 := if oriented then 0x20#8 else 0x00#8

/-- Initialized stdout state at interpreter and native-call boundaries, at
orientation `oriented`. The `_w = 0`, one-byte buffer, and `__swrite` callback
force `fputc` down the terminal-write path rather than allowing an arbitrary
buffered `FILE`. `interp_run`'s entry is unoriented (`ConsoleBoot`); the first
write orients it and every later boundary is `ConsoleStream`. -/
structure ConsoleStreamAt (oriented : Bool) (m : Mem) : Prop where
  impure : read64 m consoleImpurePtrAddr = some consoleReent
  stdout : read64 m (consoleReent + 16) = some consoleStdout
  sinit : read64 m (consoleReent + 72) = some consoleSinit
  cursor : read64 m (consoleStdout + 0) = some consoleBuf
  readCount : read32 m (consoleStdout + 8) = some 0
  writeCount : read32 m (consoleStdout + 12) = some 0
  flags : readLE m (consoleStdout + 16) 2 = some (consoleFlags oriented)
  flag0 : m[consoleStdout + 16]? = some 0x0a#8
  flag1 : m[consoleStdout + 17]? = some (consoleFlag1 oriented)
  fd : readLE m (consoleStdout + 18) 2 = some 1
  base : read64 m (consoleStdout + 24) = some consoleBuf
  bufSize : read32 m (consoleStdout + 32) = some 1
  lineBufSize : read32 m (consoleStdout + 40) = some 0
  cookie : read64 m (consoleStdout + 48) = some consoleStdout
  writer : read64 m (consoleStdout + 64) = some consoleSwrite
  lock : read64 m (consoleStdout + 160) = some 0
  lockMode : read32 m (consoleStdout + 176) = some 0
  bufferByte : ∃ b : BitVec 8, m[consoleBuf]? = some b

/-- `stdout` at `interp_run`'s entry (`_flags = 0x000a`, not yet oriented). -/
abbrev ConsoleBoot (m : Mem) : Prop := ConsoleStreamAt false m

end Vsa.Sim
