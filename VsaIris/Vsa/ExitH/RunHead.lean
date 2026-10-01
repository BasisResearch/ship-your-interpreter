import VsaIris.Vsa.ExitH.Tac

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout VsaIris.Sym.XH VsaIris.Sym.Win

/-! The exit path up to the third stream: `exit` → `__call_exitprocs` → `stdio_exit_handler` →
`_fwalk_sglue(_fclose_r)` over stdin and the console stream. 300 instructions, proved once for
every console flags word satisfying `ConFlags`; no stderr field is read before the last state. -/

#ix_piece exitHead_01 {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    {fl s e : BitVec 64} (hs : ExitSp s) (h2 : R 2 = s) (h8 : R 8 = e) (h11 : R 11 = 0#64)
    (hF : ConFlags fl) (hC : CloseMt fl Mt)
    (hk : ∀ R' Mt', ExitEnd R s e R' → NW live ∅ [] (exitS s) Q 0x80004788#64 R' Mt') :
    NW live ∅ [] (exitS s) Q 0x80004778#64 R Mt
  by xh_start 20 using []

#ix_piece exitHead_02 from exitHead_01 by xh_step 20 using []

#ix_piece exitHead_03 from exitHead_02 by xh_step 20 using []

#ix_piece exitHead_04 from exitHead_03 by xh_step 20 using []

#ix_piece exitHead_05 from exitHead_04 by xh_step 20 using []

#ix_piece exitHead_06 from exitHead_05 by xh_step 20 using []

#ix_piece exitHead_07 from exitHead_06 by xh_step 20 using []

#ix_piece exitHead_08 from exitHead_07 by xh_step 20 using []

#ix_piece exitHead_09 from exitHead_08 by xh_step 20 using []

#ix_piece exitHead_10 from exitHead_09 by xh_step 20 using []

#ix_piece exitHead_11 from exitHead_10 by xh_step 20 using []

#ix_piece exitHead_12 from exitHead_11 by xh_step 20 using []

#ix_piece exitHead_13 from exitHead_12 by xh_step 20 using []

#ix_piece exitHead_14 from exitHead_13 by xh_step 20 using []

#ix_piece exitHead_15 from exitHead_14 by xh_step 20 using []

#nx_chain exitHead_chain := [exitHead_01, exitHead_02, exitHead_03, exitHead_04, exitHead_05, exitHead_06, exitHead_07, exitHead_08, exitHead_09, exitHead_10, exitHead_11, exitHead_12, exitHead_13, exitHead_14, exitHead_15]

end VsaIris.Sym
