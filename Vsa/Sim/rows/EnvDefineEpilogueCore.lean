import Vsa.Sim.SegFrameFactsAuto
import Vsa.Sim.PinW

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 1000000

@[simp] theorem epiKind0 : (mkLine 0x80002aec#64 0x03813083#32).kind = .ld := by decide
@[simp] theorem epiKind1 : (mkLine 0x80002af0#64 0x03013403#32).kind = .ld := by decide
@[simp] theorem epiKind2 : (mkLine 0x80002af4#64 0x02813483#32).kind = .ld := by decide
@[simp] theorem epiKind3 : (mkLine 0x80002af8#64 0x02013903#32).kind = .ld := by decide
@[simp] theorem epiKind4 : (mkLine 0x80002afc#64 0x01813983#32).kind = .ld := by decide
@[simp] theorem epiKind5 : (mkLine 0x80002b00#64 0x01013a03#32).kind = .ld := by decide
@[simp] theorem epiKind6 : (mkLine 0x80002b04#64 0x00813a83#32).kind = .ld := by decide
@[simp] theorem epiKind7 : (mkLine 0x80002b08#64 0x00013b03#32).kind = .ld := by decide

private theorem envDefineMemFactsLd
    {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr}
    (sp : BitVec 64) (off : Nat) {bs : List (BitVec 8)}
    (hlo : 0x80000000 ≤ sp.toNat) (hhi : sp.toNat + 64 ≤ 0x100000000)
    (hhtif : tohostAddr + 16 ≤ sp.toNat) (halign : sp.toNat % 8 = 0)
    (hk : a.kind = .ld) (hsrc : srcVal a.rs1 L = sp)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 64) (hoff8 : off % 8 = 0)
    (hpins : LPins8 m (sp.toNat + off) bs) : MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat = sp.toNat + off := by
    unfold eaddrM
    rw [hsrc, BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by omega)]
  unfold MemFacts
  rw [hk]
  exact ⟨⟨by rw [hea]; omega, by rw [hea]; omega, by rw [hea]; right; omega⟩,
    by rw [hea]; exact hpins⟩

end Vsa.Sim
