import Vsa.MemRepr
import Vsa.Sim.ReprSurvival
import Vsa.Sim.ValueSpec

open Vsa.MemRepr

namespace Vsa.Sim

def consoleImpurePtrAddr : Nat := 0x8001b970
def consoleReent : Nat := 0x8001b538
def consoleStdout : Nat := 0x8001bb20
def consoleBuf : Nat := 0x8001bb97
def consoleSinit : Nat := 0x80005d2c
def consoleSwrite : Nat := 0x8000efd4

@[reducible] def consoleFlags (oriented : Bool) : Nat := if oriented then 0x200a else 0x000a

@[reducible] def consoleFlag1 (oriented : Bool) : BitVec 8 := if oriented then 0x20#8 else 0x00#8

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

abbrev ConsoleBoot (m : Mem) : Prop := ConsoleStreamAt false m

end Vsa.Sim
