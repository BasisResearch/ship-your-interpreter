import VsaIris.Vsa.Stdout.Win
import VsaIris.Vsa.Stderr.VfpEntry
import VsaIris.Vsa.Stderr.SwsetupErr
import VsaIris.Vsa.Carry

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout VsaIris.Sym.Win

abbrev vfpErrMt (Mt : Mem) (sp : BitVec 64) : Mem :=
  swsetupErrMt (writeLog (writeLog Mt [(0x8001bc88, 4, 0#64)]) [(0x8001bbe8, 2, 0x2012#64)]) sp
    0x8000abd8#64

structure VfpHead (R R' : Nat → BitVec 64) : Prop where
  sp_eq : R' 2 = R 2
  s0 : R' 8 = R 8
  s4 : R' 20 = R 20
  s6 : R' 22 = R 22
  keep : ∀ x ∈ [9, 18, 19, 21, 23, 24, 25, 26, 27], R' x = R x

set_option hygiene false in

macro "vfperr_step" k:num : tactic => `(tactic| (nx_runB hlive using [h2, h8, h20, hsinit, hflU, hflS, hmode,
  hlock, hfd, hbase, BitVec.add_assoc, BitVec.zero_add] at 0x8000f230 0x8000a944 #steps $k))

#ix_piece vfpErr_01 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) (t : String) (Mt : Mem) (R : Nat → BitVec 64)
    (s : BitVec 64) (need : Nat) (sp : BitVec 64)
    (hs1 : s.toNat - need + 384 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat)
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (h2 : R 2 = sp) (h8 : R 8 = 0x8001b538#64) (h20 : R 20 = 0x8001bbd8#64)
    (hDt : ldv .ld Dt 0x8001b970 = 0x8001b538#64)
    (hsinit : ldv .ld Mt 0x8001b580 = 0x80005d2c#64)
    (hflU : ldv .lhu Mt 0x8001bbe8 = 0x12#64) (hflS : ldv .lh Mt 0x8001bbe8 = 0x12#64)
    (hmode : ldv .lw Mt 0x8001bc88 = 0#64) (hlock : ldv .ld Mt 0x8001bc78 = 0#64)
    (hfd : ldv .lh Mt 0x8001bbea = 2#64) (hbase : ldv .ld Mt 0x8001bbf0 = 0#64)
    (hk : ∀ R', VfpHead R R' → SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs
      (outS s need) Q t 0x8000a944#64 R' (vfpErrMt Mt sp)) :
    SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs (outS s need) Q t
      0x8000a8d0#64 R Mt by
  nx_win sp 384 592; vfperr_step 33

#ix_piece vfpErr_02 from vfpErr_01 by
  refine swsetupErr_run (hlive := hlive) (t := t) (s := s) (need := need) (hs3 := hs3) (hs4 := hs4)
    (hDt := hDt) (ra := 0x8000abd8#64) (sp := sp) (hs1 := hs1) (h1 := ?h1) (h2 := ?h2) (hs2 := ?hs2)
    (hal := hal) (hra := by decide) (h10 := ?h10) (h11 := ?h11) (hsinit := ?hsinit) (hflU := ?hflU)
    (hflS := ?hflS) (hfd := ?hfd) (hbase := ?hbase) (hk := fun R' hR => ?_)
  all_goals try carry_close [h2, hsinit, hfd, hbase]
  nx_ret hR
  nx_runB hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19, rk20, rk21, rk22, rk23, rk24, rk25, rk26,
    rk27, h2, h8, h20, BitVec.add_assoc, BitVec.zero_add] at 0x8000a944 #steps 6
  refine hk _ ⟨?_, ?_, ?_, ?_, ?_⟩ <;> carry_close [rk2, rk8, rk20, rk22, h2, h8, h20, rk9, rk18, rk19, rk21,
    rk23, rk24, rk25, rk26, rk27]

#ix_chain vfpErr_run := [vfpErr_01, vfpErr_02]

end VsaIris.Sym
