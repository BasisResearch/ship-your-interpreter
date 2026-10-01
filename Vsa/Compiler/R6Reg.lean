import Vsa.Compiler.RTBase
import Vsa.Compiler.R6Layout

namespace Vsa.Compiler

open Vsa.Sim

theorem Has.wp {L : GRegs} {n : Nat} {v : BitVec 64} (h : Has L n v) {k : Nat}
    (hk : n = k := by (try simp only [a0, a1, a2, a3, a4, a5, a6, a7, t0, t1, t2, t3, t4, t5, t6, s2, s3, s4,
      s5, s6, s9, s10, s11, ra, spR, hpO, envR, hpF, depR]); rfl)
    (hn : k ≠ 0 := by decide) : k ∈ keysG L ∧ srcVal k L = v := by
  subst hk; exact ⟨has_mem h hn, srcVal_of_has h⟩


theorem frame_consts : frameBase = 0x80100000 ∧ frameEnd = 0x90000000 ∧ tohostAddr = 0x8001ad00 :=
  ⟨rfl, rfl, rfl⟩

theorem obj_consts : objBase = 0x90000000 ∧ objEnd = 0xE0000000 ∧ tohostAddr = 0x8001ad00 := ⟨rfl, rfl, rfl⟩

attribute [rt_pos] psPos itPos cpPos scPos trPos nfPos dpPos csPos ccPos addPos subPos mulPos divPos modPos
  cmpPos eqPos

end Vsa.Compiler
