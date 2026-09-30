import VsaIris.Vsa.Tools
import VsaIris.Vsa.MallocConsumer

namespace VsaIris.Inst.EnvNew

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Step MState)
open Vsa.Sim Vsa.MemRepr

theorem storeFact {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr}
    {bs : List (BitVec 8)} (base : BitVec 64) (off size : Nat)
    (hlo : 0x80000000 ≤ base.toNat) (hhi : base.toNat + size ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ base.toNat) (halign : base.toNat % 8 = 0)
    (hk : a.kind = .sd) (hsrc : srcVal a.rs1 L = base)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ size) (hoff8 : off % 8 = 0) : MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat = base.toNat + off := by
    unfold eaddrM
    rw [hsrc, BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by omega)]
  unfold MemFacts
  rw [hk]
  exact ⟨by rw [hea]; omega, by rw [hea]; omega, by rw [hea]; omega, by rw [hea]; omega⟩

end VsaIris.Inst.EnvNew
