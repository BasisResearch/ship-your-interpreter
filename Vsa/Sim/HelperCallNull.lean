import Vsa.Sim.HelperCall
import Vsa.Sim.EvalNullSim

/-!
# `HelperCallNull` — the `value_null` adapter of the helper-call layer

`value_null(buf)` writes the null tag into a 24-byte buffer and returns.  From
a `HelperCall.Parked` state at its entry with `a0 = buf`, the return is
route-ready at the link PC with the buffer representing `.null`
(`value_null_spec_full`).
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-- ABI-preserved registers are outside the value-store helpers' write set. -/
theorem notWrittenV_of_abiPreserved (R : Register) (hR : AbiPreserved R = true) :
    NotWrittenV R := by
  cases R <;> simp_all [AbiPreserved, NotWrittenV]

namespace HelperCall

/-- The `value_null` helper returns with the buffer holding `.null`; only the
buffer changed. -/
theorem nullReturn_of_parked (H : HelperCall) (C : H.Cert)
    (hentry : H.entry = 0x800027ec#64)
    {L : GRegs} {lds : List (List (BitVec 8))} {mR : Mem} {out : Array String}
    {gC : (R : Register) → Option (RegisterType R)} {cfg : Config}
    (hP : H.Parked L lds mR out gC cfg)
    {buf esp s0 s1 s2 s3 : BitVec 64}
    (h10 : lookupG 10 (H.out L lds).regs = some buf)
    (h2 : lookupG 2 (H.out L lds).regs = some esp)
    (h8 : lookupG 8 (H.out L lds).regs = some s0)
    (h9 : lookupG 9 (H.out L lds).regs = some s1)
    (h18 : lookupG 18 (H.out L lds).regs = some s2)
    (h19 : lookupG 19 (H.out L lds).regs = some s3)
    (hregion : NullRegion buf)
    (hloaded : Value_nullLoaded (writeLog mR (H.out L lds).log))
    (N : NativeAddrs) (φc : Addr → Nat) :
    ∃ cfg' : Config, Steps cfg cfg' ∧
      H.Return gC buf esp s0 s1 s2 s3 (writeLog mR (H.out L lds).log) cfg'.σ.mem
        (fun k => buf.toNat ≤ k ∧ k < buf.toNat + 24) out cfg' ∧
      ValueRepr cfg'.σ.mem N φc buf.toNat .null := by
  have ha0 : cfg.σ.regs.get? Register.x10 = some buf := by
    simpa only [gprGet] using gholds_lookup _ hP.regs h10
  have hsp : cfg.σ.regs.get? Register.x2 = some esp := by
    simpa only [gprGet] using gholds_lookup _ hP.regs h2
  have hs0 : cfg.σ.regs.get? Register.x8 = some s0 := by
    simpa only [gprGet] using gholds_lookup _ hP.regs h8
  have hs1 : cfg.σ.regs.get? Register.x9 = some s1 := by
    simpa only [gprGet] using gholds_lookup _ hP.regs h9
  have hs2 : cfg.σ.regs.get? Register.x18 = some s2 := by
    simpa only [gprGet] using gholds_lookup _ hP.regs h18
  have hs3 : cfg.σ.regs.get? Register.x19 = some s3 := by
    simpa only [gprGet] using gholds_lookup _ hP.regs h19
  have hretAl : (BitVec.update (H.retPC + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [C.ret_clean]; exact C.ret_align
  obtain ⟨cN, hsN, hG, hpc, ha0', hra, hmi, htick, hv, hout, hm, hf, hext⟩ :=
    value_null_spec_full (fun R => cfg.σ.regs.get? R) buf H.retPC N φc
      (writeLog mR (H.out L lds).log) out cfg
      ⟨hP.good, by rw [hP.mem]; exact hloaded, hP.mem, by rw [hP.pc, hentry], ha0, hP.ra,
        hP.minstret, hP.tick, hregion, hretAl, hP.out, fun _ _ => rfl⟩
  refine ⟨cN, hsN, ⟨?_, fun k hk => (hm k hk).symm, hext⟩, hv⟩
  exact
    { good := hG
      tick := htick
      pc := by rw [hpc, C.ret_clean]
      a0 := ha0'
      ra := hra
      minstret := hmi
      mem := rfl
      out := hout
      sp := (hf Register.x2 (notWrittenV_of_abiPreserved _ (by decide))).trans hsp
      s0 := (hf Register.x8 (notWrittenV_of_abiPreserved _ (by decide))).trans hs0
      s1 := (hf Register.x9 (notWrittenV_of_abiPreserved _ (by decide))).trans hs1
      s2 := (hf Register.x18 (notWrittenV_of_abiPreserved _ (by decide))).trans hs2
      s3 := (hf Register.x19 (notWrittenV_of_abiPreserved _ (by decide))).trans hs3
      frame := fun R hR => (hf R (notWrittenV_of_abiPreserved R hR)).trans (hP.frame R hR) }

#print axioms nullReturn_of_parked

end HelperCall

end Vsa.Sim
