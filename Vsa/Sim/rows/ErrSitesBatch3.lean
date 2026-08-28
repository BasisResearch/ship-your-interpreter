import Vsa.Sim.DeriveErrorSite
import Vsa.Sim.DecodeTable

namespace Vsa.Sim

#derive_error_site errSite_80003b54
  (0x80003b54#64, 0xa54ff0ef#32, 0x1ff254#21)
  (0xef#8, 0xf0#8, 0x4f#8, 0xa5#8)
  Vsa.Sim.DecodeTable.decode_a54ff0ef

#derive_error_site errSite_80003c7c
  (0x80003c7c#64, 0x92cff0ef#32, 0x1ff12c#21)
  (0xef#8, 0xf0#8, 0xcf#8, 0x92#8)
  Vsa.Sim.DecodeTable.decode_92cff0ef

#derive_error_site errSite_80003d5c
  (0x80003d5c#64, 0x84cff0ef#32, 0x1ff04c#21)
  (0xef#8, 0xf0#8, 0xcf#8, 0x84#8)
  Vsa.Sim.DecodeTable.decode_84cff0ef

#derive_error_site errSite_80003f58
  (0x80003f58#64, 0xe51fe0ef#32, 0x1fee50#21)
  (0xef#8, 0xe0#8, 0x1f#8, 0xe5#8)
  Vsa.Sim.DecodeTable.decode_e51fe0ef

#print axioms errSite_80003b54
#print axioms errSite_80003c7c
#print axioms errSite_80003d5c
#print axioms errSite_80003f58

end Vsa.Sim
