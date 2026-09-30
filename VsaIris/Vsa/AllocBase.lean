import VsaIris.Vsa.HeapRoom
import VsaIris.Vsa.AllocCode
import VsaIris.Vsa.MallocConsumer

namespace VsaIris.VsaHeap

open VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

def allocHeadroom : Nat := 512

structure SpOKA (s : BitVec 64) : Prop where
  lo : Vsa.Sim.tohostAddr + 16 + allocHeadroom ≤ s.toNat
  hi : s.toNat ≤ 0x100000000
  align : s.toNat % 16 = 0

abbrev AllocLive (live : Nat → Prop) : Prop := ∀ p ∈ allocText, live p.1

end VsaIris.VsaHeap
