import Vsa.Sim.EnvGetReflected.EnvGetCallFrame
import Vsa.Sim.DeriveMeta
import Vsa.Sim.EnvGetSpec3
import Vsa.Sim.StrcmpSpecCond

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr

#derive_destructurer Vsa.Sim.strcmp_post fields good pc ra mem out tick frame comparison

namespace Vsa.Sim

namespace EnvGetReflected

theorem kept_abi : ∀ R, kept R = true → Vsa.Alloc.AbiPreserved R = true := by
  have h : ∀ R ∈ [Register.x3, Register.x4, Register.x22, Register.x23,
      Register.x24, Register.x25, Register.x26, Register.x27],
      Vsa.Alloc.AbiPreserved R = true := by decide
  intro R hR
  exact h R (by simpa [kept, Bool.or_eq_true, beq_iff_eq, or_assoc] using hR)

/-- The call prefix writes only argument registers and the return address. -/
theorem CallResult.abi_frame
    {cursor name : BitVec 64} {lds : List (List (BitVec 8))}
    {before after : Config} (h : CallResult cursor name lds before after) :
    ∀ R, Vsa.Alloc.AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R := by
  intro R hR
  exact h.frame R (noise_avoids abiPreserved_noise hR)
    (wrChain_avoids (by show WrChainAvoids Vsa.Alloc.AbiPreserved env_getX2c60Seg; decide) hR)
    (regAvoids_ne hR (by decide))

/-- A completed comparison retains its semantic result and the outer register frame. -/
structure CompareResult
    (g : (R : Register) → Option (RegisterType R))
    (pa name : BitVec 64) (sa sb : String) (before after : Config) : Prop where
  steps : Steps before after
  post : strcmp_post.Parts g 0x80002c6c#64 pa name sa sb
    before.σ.mem before.σ.sailOutput after
  abi_frame : ∀ R, Vsa.Alloc.AbiPreserved R = true →
    after.σ.regs.get? R = before.σ.regs.get? R

theorem CompareResult.kept_frame
    {g : (R : Register) → Option (RegisterType R)}
    {pa name : BitVec 64} {sa sb : String} {before after : Config}
    (h : CompareResult g pa name sa sb before after) :
    ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R :=
  fun R hR => h.abi_frame R (kept_abi R hR)

/-- Compose the call's actual endpoint with the conditional comparison spec. -/
theorem CallResult.compare
    {cursor name : BitVec 64} {lds : List (List (BitVec 8))}
    {before called : Config} (h : CallResult cursor name lds before called)
    {pa : BitVec 64} {sa sb : String}
    (hentry : StrcmpEntryCond called.σ.regs.get? pa name 0x80002c6c#64 sa sb
      before.σ.mem before.σ.sailOutput called) :
    ∃ after, CompareResult called.σ.regs.get? pa name sa sb before after := by
  obtain ⟨after, hs, hp⟩ := strcmp_full_spec_cond called.σ.regs.get?
    pa name 0x80002c6c#64 sa sb before.σ.mem before.σ.sailOutput called hentry
  have hpost := strcmp_post.destruct called.σ.regs.get? 0x80002c6c#64
    pa name sa sb before.σ.mem before.σ.sailOutput after hp
  refine ⟨after, { steps := h.run.trans hs, post := hpost, abi_frame := ?_ }⟩
  intro R hR
  exact (hpost.frame R (notWrittenStrcmp_of_abiPreserved R hR)).trans (h.abi_frame R hR)

#print axioms kept_abi
#print axioms CallResult.abi_frame
#print axioms CompareResult.kept_frame
#print axioms CallResult.compare

end EnvGetReflected

#print axioms strcmp_post.destruct
#print axioms strcmp_post.mk'

end Vsa.Sim
