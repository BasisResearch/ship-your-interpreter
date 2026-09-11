import Vsa.Sim.EnvGetReflected.EnvGetOwnedFrameState

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected

/-- Read the represented non-null parent from the reached frame. -/
theorem FrameState.parent_read
    {env name out pn ra sp : BitVec 64}
    {f : Vsa.While.Frame} {query : String} {N : NativeAddrs}
    {phiF phiC : Vsa.While.Addr → Nat} {parent : Vsa.While.Addr} {c : Config}
    (h : FrameState env name out pn ra sp f query N phiF phiC c)
    (hparent : f.parent = some parent) :
    read64 c.σ.mem (env.toNat + 24) = some (phiF parent) ∧ phiF parent ≠ 0 := by
  obtain ⟨_count, _capacity, _arrays, hread⟩ := h.frame
  simpa only [hparent] using hread

theorem kept_parent : ∀ R, kept R = true → parentKeep R = true :=
  kept_of_members (by decide)

/-- The taken parent edge retains the observations needed by the next frame. -/
structure FrameParentResult (parent name out ra sp : BitVec 64)
    (before after : Config) : Prop extends ParentResult parent true before after where
  registers : FrameRegisters parent name out ra sp after

theorem FrameParentResult.kept_frame
    {parent name out ra sp : BitVec 64} {before after : Config}
    (h : FrameParentResult parent name out ra sp before after) :
    ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R :=
  fun R hR => h.frame R (kept_parent R hR)

/-- A semantic parent selects the taken machine edge without a pointer oracle. -/
theorem frame_parent
    {env name out pn ra sp : BitVec 64}
    {f : Vsa.While.Frame} {query : String} {N : NativeAddrs}
    {phiF phiC : Vsa.While.Addr → Nat} {parent : Vsa.While.Addr} {c : Config}
    (h : FrameState env name out pn ra sp f query N phiF phiC c)
    (hpc : c.σ.regs.get? Register.PC = some 0x80002cc4#64)
    (hparent : f.parent = some parent) :
    ∃ after, FrameParentResult (BitVec.ofNat 64 (phiF parent)) name out ra sp c after := by
  obtain ⟨hread, hnonnull⟩ := h.parent_read hparent
  have hsmall := read64_lt_eg4 c.σ.mem (env.toNat + 24) (phiF parent) hread
  have hptr : (BitVec.ofNat 64 (phiF parent)).toNat = phiF parent := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  have hne : BitVec.ofNat 64 (phiF parent) ≠ (0#64) := by
    intro hz
    apply hnonnull
    have hn := congrArg BitVec.toNat hz
    simpa only [hptr] using hn
  obtain ⟨after, present, hp⟩ := parent_branch env (BitVec.ofNat 64 (phiF parent)) c
    h.good hpc h.tick h.env4 h.loadedG
    (by have := h.header_lo; omega) h.header_hi
    (Or.inr (by have := h.header_htif; omega)) (by rw [hptr]; exact hread)
  have ht : present = true := hp.present_iff.mpr hne
  subst present
  exact ⟨after, { hp with registers := h.registers.after_parent hp }⟩

#print axioms FrameState.parent_read
#print axioms kept_parent
#print axioms FrameParentResult.kept_frame
#print axioms frame_parent

end Vsa.Sim.EnvGetReflected
