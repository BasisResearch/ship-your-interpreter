import VsaIris.Vsa.ExitH.RunHead

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout VsaIris.Sym.XH

/-! The exit path from the third stream on, stderr written (flags `0x201a`). -/

#ix_branch exitWritten_01 (hE : ErrWrittenMt Mt) from exitHead_15 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.base, hE.p, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitWritten_02 from exitWritten_01 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.base, hE.p, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitWritten_03 from exitWritten_02 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.base, hE.p, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitWritten_04 from exitWritten_03 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.base, hE.p, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitWritten_05 from exitWritten_04 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.base, hE.p, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitWritten_06 from exitWritten_05 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.base, hE.p, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitWritten_07 from exitWritten_06 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.base, hE.p, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitWritten_08 from exitWritten_07 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.base, hE.p, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitWritten_end from exitWritten_08 by xh_end

#ix_chain exitWrittenTail_chain := [exitWritten_01, exitWritten_02, exitWritten_03, exitWritten_04, exitWritten_05, exitWritten_06, exitWritten_07, exitWritten_08, exitWritten_end]

theorem exitWritten_chain {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    {fl s e : BitVec 64} (hs : ExitSp s) (h2 : R 2 = s) (h8 : R 8 = e) (h11 : R 11 = 0#64)
    (hF : ConFlags fl) (hC : CloseMt fl Mt) (hE : ErrWrittenMt Mt)
    (hk : ∀ R' Mt', ExitEnd R s e R' → NW live ∅ [] (exitS s) Q 0x80004788#64 R' Mt') :
    NW live ∅ [] (exitS s) Q 0x80004778#64 R Mt := by
  refine exitHead_chain hlive hs h2 h8 h11 hF hC hk ?_
  intros
  apply exitWrittenTail_chain hlive hs h2 h8 h11 hF hC hk <;> assumption

end VsaIris.Sym
