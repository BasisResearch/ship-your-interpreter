import VsaIris.Vsa.Stderr.VfpEntry
import VsaIris.Vsa.Stderr.SwsetupErr

/-!
# `_vfprintf_r` on `stderr`: the stream's first-write setup (lane N3)

From `0x8000a8d0` (`VfpEntry`) on the idle `stderr` (flags `__SRW | __SNBF`,
no lock, `_flags2 = 0`): the (no-op) lock, orientation (`__SORD`), then
`cantwrite` → `__swsetup_r` (`swsetupErr_run`); the stream is not the
unbuffered-and-writable shape `__sbprintf` takes (`flags & 0x1a ≠ 0x0a`, it
is `__SRW` too), so the run reaches `0x8000a944`, the direct path's
initialization, which N5's format loop starts from.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

/-- The memory at `0x8000a944`: orientation (`_flags2`'s lock bit cleared,
`__SORD` set), then `__swsetup_r`'s writes (`swsetupErrMt`). -/
abbrev vfpErrMt (Mt : Mem) (sp : BitVec 64) : Mem :=
  swsetupErrMt (writeLog (writeLog Mt [(0x8001bc88, 4, 0#64)]) [(0x8001bbe8, 2, 0x2012#64)]) sp
    0x8000abd8#64

/-- The registers at `0x8000a944`: `sp`, `s0`/`s4`/`s6` (`reent`, `fp`,
`fmt`), the other callee-saved registers as at `0x8000a8d0`. -/
structure VfpHead (R R' : Nat → BitVec 64) : Prop where
  sp_eq : R' 2 = R 2
  s0 : R' 8 = R 8
  s4 : R' 20 = R 20
  s6 : R' 22 = R 22
  keep : ∀ x ∈ [9, 18, 19, 21, 23, 24, 25, 26, 27], R' x = R x

set_option hygiene false in
/-- One piece of the setup run. -/
macro "vfperr_step" : tactic => `(tactic| (nx_runB hlive using [h2, h8, h20, hsinit, hflU, hflS, hmode,
  hlock, hfd, hbase, BitVec.add_assoc, BitVec.zero_add] at 0x8000f230 0x8000a944))

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
  vfperr_step

#ix_piece vfpErr_02 from vfpErr_01 by
  refine swsetupErr_run (hlive := hlive) (t := t) (s := s) (need := need) (hs3 := hs3) (hs4 := hs4)
    (hDt := hDt) (ra := 0x8000abd8#64) (sp := sp) (hs1 := hs1) (h1 := ?h1) (h2 := ?h2) (hs2 := ?hs2)
    (hal := hal) (hra := by decide) (h10 := ?h10) (h11 := ?h11) (hsinit := ?hsinit) (hflU := ?hflU)
    (hflS := ?hflS) (hfd := ?hfd) (hbase := ?hbase) (hk := fun R' hR => ?_)
  all_goals (try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h2]; done))
  case hs2 => omega
  case hsinit => nx_mem; exact hsinit
  case hflU | hflS => nx_mem; decide
  case hfd => nx_mem; exact hfd
  case hbase => nx_mem; exact hbase
  nx_ret hR
  nx_runB hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19, rk20, rk21, rk22, rk23, rk24, rk25, rk26,
    rk27, h2, h8, h20, BitVec.add_assoc, BitVec.zero_add] at 0x8000a944
  refine hk _ ⟨?_, ?_, ?_, ?_, fun x hx => ?_⟩
  all_goals (try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, rk2, rk8, rk20, rk22,
    h2, h8, h20]; done))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, rk9, rk18, rk19, rk21, rk23, rk24,
      rk25, rk26, rk27]

/-! **`vfpErr_run`**: `_vfprintf_r` on the idle `stderr`, `0x8000a8d0` → `0x8000a944`. -/
#ix_chain vfpErr_run := [vfpErr_01, vfpErr_02]

end VsaIris.Sym
