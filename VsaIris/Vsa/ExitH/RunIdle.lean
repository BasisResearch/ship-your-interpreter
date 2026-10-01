import VsaIris.Vsa.ExitH.RunHead

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout VsaIris.Sym.XH VsaIris.Sym.Win

/-! The exit path from the third stream on, stderr never written (flags `0x12`). -/

#ix_branch exitIdle_01 (hE : ErrIdleMt Mt) from exitHead_15 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.r, hE.ur, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitIdle_02 from exitIdle_01 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.r, hE.ur, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitIdle_03 from exitIdle_02 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.r, hE.ur, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitIdle_04 from exitIdle_03 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.r, hE.ur, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitIdle_05 from exitIdle_04 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.r, hE.ur, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitIdle_06 from exitIdle_05 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.r, hE.ur, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitIdle_07 from exitIdle_06 by xh_step 20 using [hE.flagsU, hE.flags, hE.fd, hE.r, hE.ur, hE.cookie, hE.close, hE.ub, hE.lb, hE.lock, hE.mode]

#ix_piece exitIdle_end from exitIdle_07 by xh_end

#ix_chain exitIdleTail_chain := [exitIdle_01, exitIdle_02, exitIdle_03, exitIdle_04, exitIdle_05, exitIdle_06, exitIdle_07, exitIdle_end]

theorem exitIdle_chain {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    {fl s e : BitVec 64} (hs : ExitSp s) (h2 : R 2 = s) (h8 : R 8 = e) (h11 : R 11 = 0#64)
    (hF : ConFlags fl) (hC : CloseMt fl Mt) (hE : ErrIdleMt Mt)
    (hk : ∀ R' Mt', ExitEnd R s e R' → NW live ∅ [] (exitS s) Q 0x80004788#64 R' Mt') :
    NW live ∅ [] (exitS s) Q 0x80004778#64 R Mt := by
  refine exitHead_chain hlive hs h2 h8 h11 hF hC hk ?_
  intros
  apply exitIdleTail_chain hlive hs h2 h8 h11 hF hC hk <;> assumption

end VsaIris.Sym
