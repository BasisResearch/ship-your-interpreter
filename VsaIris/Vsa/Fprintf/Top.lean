import VsaIris.Vsa.Stdout.Win
import VsaIris.Vsa.Fprintf.Outer
import VsaIris.Interp.SymFront
import VsaIris.Vsa.Carry

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout VsaIris.Sym.Win

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

def FpReg (sf : Nat) (a : Nat) : Prop :=
  (sf - 2880 ≤ a ∧ a < sf + 80) ∨ (0x8001bb30 ≤ a ∧ a < 0x8001bb32) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c)

theorem fprintf_wrap (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sf : BitVec 64} {need N : Nat} {bytes : List (BitVec 8)}
    (hs1 : s.toNat - need + 1024 ≤ sf.toNat) (hs2 : sf.toNat + 80 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sf.toNat % 16 = 0) (hra : (R 1).toNat % 4 = 0)
    (h2 : R 2 = sf + 80#64) (himp : ldv .ld Dt 0x8001b970 = 0x8001b538#64)
    (hDA : Cover (· ∈ DA) 0x8001b970 0x8001b978)
    (hO : ∀ (R0 : Nat → BitVec 64) (Mt0 : Mem), R0 2 = sf → R0 10 = 0x8001b538#64 → R0 11 = R 10 →
      R0 12 = R 11 → R0 13 = sf + 32#64 → R0 1 = 0x80006204#64 →
      Frame Mt0 Mt (fun a => sf.toNat ≤ a ∧ a < sf.toNat + 80) → ldv .ld Mt0 (sf + 32#64).toNat = R 12 →
      (∀ R' M', R' 10 = BitVec.ofNat 64 N → R' 2 = sf → R' 1 = 0x80006204#64 → (∀ x ∈ vfpSaved, R' x = R0 x) →
        Frame M' Mt0 (OuterReg (sf.toNat - 592)) → ldv .lh M' 0x8001bb30 = 0x200a#64 →
        SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs bytes) 0x80006204#64 R' M') →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a884#64 R0 Mt0)
    (hk : ∀ R' M', RetOK R R' (BitVec.ofNat 64 N) → Frame M' Mt (FpReg sf.toNat) →
      ldv .lh M' 0x8001bb30 = 0x200a#64 → SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs bytes) (R 1) R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x800061c0#64 R Mt := by
  nx_win sf 1024 80; have e : sf + 80#64 + 18446744073709551536#64 = sf := by rw [BitVec.add_assoc]; simp
  xrun hlive using [h2, e, himp, BitVec.add_assoc] at 2147526788
  refine hO _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ fun R1 M1 e10 e2 e1 ek hfr1 hfl1 => ?_
  all_goals try carry_close
  · frame_chain
  have l24 : ldv .ld M1 (sf + 24#64).toNat = R 1 := by carry_close [hfr1.ldv]
  xrun hlive using [e2, e10, l24, BitVec.add_assoc]
  refine hk _ _ (retOK_of (by carry_close [e10]) ?_) ?_ hfl1
  · simp (config := {decide := true}) only [iRegs, callClob, List.forall_mem_cons, List.forall_mem_nil, ne_eq,
      not_true_eq_false, false_implies, true_implies, implies_true, true_and, and_true]
    carry_close [ek, h2]
  · refine Frame.trans ?_ (hfr1.mono ?_)
    · repeat (refine Frame.snoc ?_ ?_)
      all_goals first | exact Frame.refl _ _ | region_close
    · region_close

end VsaIris.Sym.Fp
