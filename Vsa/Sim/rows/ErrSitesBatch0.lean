import Vsa.Sim.DeriveErrorSite
import Vsa.Sim.DecodeTable

namespace Vsa.Sim

#derive_error_site errSite_80002e90
  (0x80002e90#64, 0xf19ff0ef#32, 0x1fff18#21)
  (0xef#8, 0xf0#8, 0x9f#8, 0xf1#8)
  Vsa.Sim.DecodeTable.decode_f19ff0ef

#derive_error_site errSite_80003b9c
  (0x80003b9c#64, 0xa0cff0ef#32, 0x1ff20c#21)
  (0xef#8, 0xf0#8, 0xcf#8, 0xa0#8)
  Vsa.Sim.DecodeTable.decode_a0cff0ef

#derive_error_site errSite_80003cc4
  (0x80003cc4#64, 0x8e4ff0ef#32, 0x1ff0e4#21)
  (0xef#8, 0xf0#8, 0x4f#8, 0x8e#8)
  Vsa.Sim.DecodeTable.decode_8e4ff0ef

#derive_error_site errSite_80003da0
  (0x80003da0#64, 0x808ff0ef#32, 0x1ff008#21)
  (0xef#8, 0xf0#8, 0x8f#8, 0x80#8)
  Vsa.Sim.DecodeTable.decode_808ff0ef

#derive_error_site errSite_80003fac
  (0x80003fac#64, 0xdfdfe0ef#32, 0x1fedfc#21)
  (0xef#8, 0xe0#8, 0xdf#8, 0xdf#8)
  Vsa.Sim.DecodeTable.decode_dfdfe0ef

#print axioms errSite_80002e90
#print axioms errSite_80003b9c
#print axioms errSite_80003cc4
#print axioms errSite_80003da0
#print axioms errSite_80003fac

end Vsa.Sim
