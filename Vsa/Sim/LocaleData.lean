import Vsa.Sim.ConsoleStream

open Vsa.MemRepr

namespace Vsa.Sim

def localeMbtowcAddr : Nat := 0x8001b880
def localeMbMaxAddr : Nat := 0x8001b8f8
def localeDecPointAddr : Nat := 0x8001b898

def asciiMbtowc : Nat := 0x80012268

def decPointStr : Nat := 0x80019770

structure LocaleData (m : Mem) : Prop where
  mbtowc : read64 m localeMbtowcAddr = some asciiMbtowc
  mbMax : readLE m localeMbMaxAddr 1 = some 1
  decPoint : read64 m localeDecPointAddr = some decPointStr

end Vsa.Sim
