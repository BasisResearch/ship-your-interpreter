import Vsa.Sim.DeriveErrorSite
import Vsa.Sim.DecodeTable

namespace Vsa.Sim

#derive_error_site errSite_80003950
  (0x80003950#64, 0xc58ff0ef#32, 0x1ff458#21)
  (0xef#8, 0xf0#8, 0x8f#8, 0xc5#8)
  Vsa.Sim.DecodeTable.decode_c58ff0ef

#derive_error_site errSite_80003c10
  (0x80003c10#64, 0x998ff0ef#32, 0x1ff198#21)
  (0xef#8, 0xf0#8, 0x8f#8, 0x99#8)
  Vsa.Sim.DecodeTable.decode_998ff0ef

#derive_error_site errSite_80003d14
  (0x80003d14#64, 0x894ff0ef#32, 0x1ff094#21)
  (0xef#8, 0xf0#8, 0x4f#8, 0x89#8)
  Vsa.Sim.DecodeTable.decode_894ff0ef

#derive_error_site errSite_80003e98
  (0x80003e98#64, 0xf11fe0ef#32, 0x1fef10#21)
  (0xef#8, 0xe0#8, 0x1f#8, 0xf1#8)
  Vsa.Sim.DecodeTable.decode_f11fe0ef

#print axioms errSite_80003950
#print axioms errSite_80003c10
#print axioms errSite_80003d14
#print axioms errSite_80003e98

end Vsa.Sim
