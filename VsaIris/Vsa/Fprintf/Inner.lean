import VsaIris.Vsa.Fprintf.End

/-!
# `_vfprintf_r` on `__sbprintf`'s stack `FILE` (lane N5)

The `FILE`-dependent part of `_vfprintf_r`'s prologue on the stack `FILE`
(`0x8000a8d0` → `0x8000a944`, `vfp_fileSb`): the reent's `__sinit` done,
the (stub) lock taken, `__SWR` set with a buffer, `__SNBF|__SRW` clear (no
`__sbprintf` again). The memory is unchanged.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem vfp_fileSb (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp f : BitVec 64} {need : Nat} {pend : List (BitVec 8)}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hf1 : sp.toNat + 592 ≤ f.toNat) (hf2 : f.toNat + 1208 ≤ s.toNat) (hfa : f.toNat % 8 = 0)
    (h2 : R 2 = sp) (h8 : R 8 = 0x8001b538#64) (h20 : R 20 = f) (hF : SbFile Mt f pend)
    (hk : ∀ R' : Nat → BitVec 64, (∀ x ∈ [2, 3, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], R' x = R x) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a944#64 R' Mt) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a8d0#64 R Mt := by
  have hB0 : f + 184#64 ≠ 0#64 := fun h => by
    have := congrArg BitVec.toNat h; rw [toNat_add_lit (by omega)] at this; simp at this
  have hB0' : (f + 184#64 = 0#64) = False := eq_false hB0
  nf_go 3 [14] hlive using [h2, h8, h20, hF.flags, hF.flagsU, hF.flags2, hF.base, hF.sinit, hB0', BitVec.add_assoc]
    at 2147526980
  refine hk _ fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp <;>
    first | rfl | assumption

end VsaIris.Sym.Fp
