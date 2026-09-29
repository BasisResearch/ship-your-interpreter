import Vsa.Compiler.SimFnEntry

/-!
# Function exit

`fnPost`: the null result for a body that completes normally, then the return
that restores the caller's return address, frame, stack pointer and depth
from the function's stack frame.
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While LeanRV64DExecutable.Functions

section
variable {code : List Ins} (hR : RTLoaded code)
include hR

/-- From the return (index 2 of `fnPost`). -/
theorem run_fnRet {fs' sp' d qp : Nat} (hseg : Seg code qp (fnPost fs')) {L : GRegs} {m : Mem}
    {o : Array String} (hsp : Has L spR (BitVec.ofNat 64 sp')) (hdep : Has L depR (BitVec.ofNat 64 (d + 1)))
    (hlo : stackLo ≤ sp') (hhi : sp' + fs' ≤ stackHi) (hal : sp' % 16 = 0) (hfs : fs' ≤ 1936) (hfs0 : 16 ≤ fs')
    (hra : (rdW m sp').toNat % 4 = 0) :
    Reaches code ⟨pcOf (qp + 2), L, m, o⟩ (fun B => B.pc = rdW m sp' ∧ B.mem = m ∧ B.out = o ∧
      Has B.regs envR (rdW m (sp' + 8)) ∧ Has B.regs spR (BitVec.ofNat 64 (sp' + fs')) ∧
      Has B.regs depR (BitVec.ofNat 64 d) ∧ Keep [ra, t6, envR, spR, depR] L B.regs) := by
  have hL : stackLo = 0xE0000000 := rfl
  have hH : stackHi = 0x100000000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have k2 := has_mem hsp (by decide); have e2 := srcVal_of_has hsp
  have k24 := has_mem hdep (by decide); have e24 := srcVal_of_has hdep
  simp only [spR, depR] at k2 e2 k24 e24
  have n0 : (BitVec.ofNat 64 sp').toNat = sp' := toNat_ofNat_lt (by omega)
  have n8 : (BitVec.ofNat 64 (sp' + 8)).toNat = sp' + 8 := toNat_ofNat_lt (by omega)
  have l0 : LdOK sp' := by unfold LdOK; omega
  have l8 : LdOK (sp' + 8) := by unfold LdOK; omega
  apply run_jumps hR.fits ((hseg.drop 2).cast (pos' := qp + 2) rfl)
  wp_simp [fnPost, k2, e2, k24, e24, n0, n8, l0, l8]
  exact ⟨hra, reach_here ⟨rfl, rfl, rfl, by reg_simp [], by reg_simp [], by reg_simp [],
    by reg_simp []; exact Keep.refl _ _⟩⟩

/-- From the start of `fnPost`: the null result, then the return. -/
theorem run_fnNull {fs' sp' d qp : Nat} (hseg : Seg code qp (fnPost fs')) {L : GRegs} {m : Mem}
    {o : Array String} (hsp : Has L spR (BitVec.ofNat 64 sp')) (hdep : Has L depR (BitVec.ofNat 64 (d + 1)))
    (hlo : stackLo ≤ sp') (hhi : sp' + fs' ≤ stackHi) (hal : sp' % 16 = 0) (hfs : fs' ≤ 1936) (hfs0 : 16 ≤ fs')
    (hra : (rdW m sp').toNat % 4 = 0) :
    Reaches code ⟨pcOf qp, L, m, o⟩ (fun B => B.pc = rdW m sp' ∧ B.mem = m ∧ B.out = o ∧
      Has B.regs envR (rdW m (sp' + 8)) ∧ Has B.regs spR (BitVec.ofNat 64 (sp' + fs')) ∧
      Has B.regs depR (BitVec.ofNat 64 d) ∧ Keep [a0, a1, ra, t6, envR, spR, depR] L B.regs ∧
      Has B.regs a0 0 ∧ Has B.regs a1 0) := by
  apply run_block hR.fits hseg 0 2 qp rfl (KP := fun L' m' o' => L' = gset (gset L 10 0) 11 0 ∧ m' = m ∧ o' = o)
    (fun L' m' o' ⟨h1, h2, h3⟩ => ?_) (by simp [fnPost])
  · simp only [fnPost, List.drop_zero, List.take_succ_cons, List.take_zero]
    wp_simp []
    all_goals exact ⟨rfl, rfl, rfl⟩
  · subst h1 h2 h3
    refine reaches_mono (run_fnRet hR hseg (by reg_simp []; exact hsp) (by reg_simp []; exact hdep) hlo hhi hal hfs hfs0
      hra) ?_
    rintro B ⟨g1, g2, g3, g4, g5, g6, g7⟩
    exact ⟨g1, g2, g3, g4, g5, g6, (Keep.gset (Keep.gset (Keep.refl _ L) (by decide)) (by decide)).trans
      (g7.mono (by decide)), g7.has (by decide) (by reg_simp []), g7.has (by decide) (by reg_simp [])⟩

end

end Vsa.Compiler
