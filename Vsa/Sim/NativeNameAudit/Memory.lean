import Vsa.Sim.OutputAliasTrace

/-! Initial finite overlays for the mutable binding-name audit. -/

namespace Vsa.Sim.NativeNameAudit

open Vsa.MemRepr Vsa.Machine Vsa.Sim.OutputAliasLoaded

def nativeNameLog : List WEntry :=
  [(0x81000048, 8, 0x8001bb91#64),
   (0x8001bb91, 1, 0x70#64), (0x8001bb92, 1, 0x72#64),
   (0x8001bb93, 1, 0x69#64), (0x8001bb94, 1, 0x6e#64),
   (0x8001bb95, 1, 0x74#64), (0x8001bb96, 1, 0x6c#64),
   (0x8001bb97, 1, 0x6e#64),
   (0x82000008, 8, 0x82000020#64),
   (0x820000a8, 8, 0x820000c0#64),
   (0x820000c0, 8, 0x006e6c746e697270#64)]

def nativeNameMem : Mem := writeLog snapshotMem nativeNameLog
def nativeNameConfig : Config := physicalConfig nativeNameMem

theorem nativeName_lookup (a : Nat) :
    nativeNameMem[a]? = logRead snapshotInitialRead nativeNameLog a :=
  snapshot_logRead nativeNameLog a

end Vsa.Sim.NativeNameAudit
