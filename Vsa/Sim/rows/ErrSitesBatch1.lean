import Vsa.Sim.DeriveErrorSite
import Vsa.Sim.DecodeTable

namespace Vsa.Sim

#derive_error_site errSite_80002ebc
  (0x80002ebc#64, 0xeedff0ef#32, 0x1ffeec#21)
  (0xef#8, 0xf0#8, 0xdf#8, 0xee#8)
  Vsa.Sim.DecodeTable.decode_eedff0ef

#derive_error_site errSite_80003bc8
  (0x80003bc8#64, 0x9e0ff0ef#32, 0x1ff1e0#21)
  (0xef#8, 0xf0#8, 0x0f#8, 0x9e#8)
  Vsa.Sim.DecodeTable.decode_9e0ff0ef

#derive_error_site errSite_80003ce8
  (0x80003ce8#64, 0x8c0ff0ef#32, 0x1ff0c0#21)
  (0xef#8, 0xf0#8, 0x0f#8, 0x8c#8)
  Vsa.Sim.DecodeTable.decode_8c0ff0ef

#derive_error_site errSite_80003de8
  (0x80003de8#64, 0xfc1fe0ef#32, 0x1fefc0#21)
  (0xef#8, 0xe0#8, 0x1f#8, 0xfc#8)
  Vsa.Sim.DecodeTable.decode_fc1fe0ef

#derive_error_site errSite_80003fdc
  (0x80003fdc#64, 0xdcdfe0ef#32, 0x1fedcc#21)
  (0xef#8, 0xe0#8, 0xdf#8, 0xdc#8)
  Vsa.Sim.DecodeTable.decode_dcdfe0ef

#print axioms errSite_80002ebc
#print axioms errSite_80003bc8
#print axioms errSite_80003ce8
#print axioms errSite_80003de8
#print axioms errSite_80003fdc

end Vsa.Sim
