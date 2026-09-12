import EnvGetLookupSource
import EnvGetCopyFramed
import EnvGetRestore
import Vsa.Sim.EnvGetRecursive

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- Reached-frame and caller geometry needed by the copy and restore tail. -/
structure HitTailGeom (env out sp : BitVec 64) (pv i : Nat) (shared : Nat → Prop)
    : Prop extends CopyGeom env out pv i where
  stackLo : 0x80000000 ≤ sp.toNat
  stackHi : sp.toNat + 64 ≤ 0x100000000
  stackHtif : tohostAddr + 16 ≤ sp.toNat
  outputSpill : out.toNat + 24 ≤ sp.toNat ∨ sp.toNat + 64 ≤ out.toNat
  sharedOutput : ∀ k, shared k → ¬ (out.toNat ≤ k ∧ k < out.toNat + 24)

/-- A completed successful tail, with ownership and the caller frame from
the same copy/restore execution. -/
structure HitTailResult (N : NativeAddrs) (phiC : Vsa.While.Addr → Nat)
    (shared : Nat → Prop) (v : Vsa.While.Value)
    (out sp r0 r8 r9 r18 r19 r20 r21 : BitVec 64) (src : Nat)
    (before after : Config) : Prop where
  steps : Steps before after
  good : GoodState after.σ
  tick : after.tick < 2
  loaded : Code.Env_getLoaded after.σ.mem
  pc : after.σ.regs.get? Register.PC = some r0
  regs : GHolds after.σ (restoreRegs sp 1#64 r0 r8 r9 r18 r19 r20 r21)
  value : ValueWordRepr after.σ.mem N phiC out.toNat v
  owned : ValueOwned after.σ.mem shared out.toNat v
  mem : after.σ.mem = copy3Log before.σ.mem src out.toNat
  extendsMemory : MemExtends before.σ.mem after.σ.mem
  outside : ∀ k, ¬ (out.toNat ≤ k ∧ k < out.toNat + 24) → after.σ.mem[k]? = before.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  kept_frame : ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Copy the machine-selected owned binding and return through the saved frame. -/
theorem hit_tail
    {N : NativeAddrs} {A : Arena} {phiF phiC : Vsa.While.Addr → Nat}
    {shared : Nat → Prop} {s : Vsa.While.Store} {query : String} {v : Vsa.While.Value}
    {out sp : BitVec 64} {fa : Nat} {f : Vsa.While.Frame} {i pv : Nat} {c : Config}
    (h : OwnedLookupHit N A phiF phiC shared s query v out sp fa f i pv c)
    (geom : HitTailGeom (BitVec.ofNat 64 (phiF fa)) out sp pv i shared)
    (r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (halign : r0.toNat % 4 = 0)
    (hsaved : PrologueSaved c.σ.mem sp r0 r8 r9 r18 r19 r20 r21) :
    ∃ after, HitTailResult N phiC shared v out sp r0 r8 r9 r18 r19 r20 r21
      (pv + 24 * i) c after := by
  have hvalues : read64 c.σ.mem ((BitVec.ofNat 64 (phiF fa)).toNat + 16) = some pv := by
    rw [h.envPointer]
    exact h.source.values
  obtain ⟨copied, hc⟩ := copy_framed (BitVec.ofNat 64 (phiF fa)) out sp pv i c
    geom.toCopyGeom h.good h.loaded h.pc h.regs h.stack h.tick hvalues h.access.words
  have hw : ValueWordRepr c.σ.mem N phiC (pv + 24 * i) v :=
    ⟨h.source.repr, h.access.words⟩
  obtain ⟨hv, ho, hext⟩ := copy_value hc.mem geom.sharedOutput hw h.source.owned
  have hsaved' : PrologueSaved copied.σ.mem sp r0 r8 r9 r18 r19 r20 r21 :=
    hsaved.transport (fun k hk => hc.outside k (by have := geom.outputSpill; omega))
  obtain ⟨after, hr⟩ := restore_framed sp 1#64 r0 r8 r9 r18 r19 r20 r21 copied
    hc.good hc.loaded hc.pc hc.stack hc.result hc.tick
    geom.stackLo geom.stackHi geom.stackHtif halign hsaved'
  exact ⟨after,
    { steps := hc.steps.trans hr.steps
      good := hr.good, tick := hr.tick
      loaded := hr.mem.symm ▸ hc.loaded
      pc := hr.pc, regs := hr.regs
      value := hr.mem.symm ▸ hv
      owned := hr.mem.symm ▸ ho
      mem := hr.mem.trans hc.mem
      extendsMemory := hr.mem.symm ▸ hext
      outside := fun k hk => (congrArg (fun m : Mem => m[k]?) hr.mem).trans (hc.outside k hk)
      output := hr.output.trans hc.output
      kept_frame := fun R hR => (hr.kept_frame R hR).trans (hc.kept_frame R hR) }⟩

/-- Project the inherited value post from the same owned, framed return. -/
theorem HitTailResult.toValuePost
    {N : NativeAddrs} {phiC : Vsa.While.Addr → Nat} {shared : Nat → Prop}
    {v : Vsa.While.Value} {out sp r0 r8 r9 r18 r19 r20 r21 : BitVec 64}
    {src : Nat} {before after : Config}
    (h : HitTailResult N phiC shared v out sp r0 r8 r9 r18 r19 r20 r21 src before after) :
    EnvGetValuePost N phiC out sp r0 r8 r9 r18 r19 r20 r21
      before.σ.sailOutput v before.σ.mem after := by
  obtain ⟨hr, hsp, h8, h9, h18, h19, h20, h21, hfound, _⟩ := h.regs
  obtain ⟨d0, d1, d2, hd0, hd1, hd2⟩ := h.value.raw
  exact
    { good := h.good, tick := h.tick, pc := h.pc
      found := by simpa [gprGet] using hfound
      ra := by simpa [gprGet] using hr
      sp := by simpa [gprGet] using hsp
      s0 := by simpa [gprGet] using h8
      s1 := by simpa [gprGet] using h9
      s2 := by simpa [gprGet] using h18
      s3 := by simpa [gprGet] using h19
      s4 := by simpa [gprGet] using h20
      s5 := by simpa [gprGet] using h21
      output := h.output
      mem := ⟨after.σ.mem, d0.toNat, d1.toNat, d2.toNat, rfl, h.loaded,
        h.value.repr, hd0, hd1, hd2, h.outside⟩ }

#print axioms hit_tail
#print axioms HitTailResult.toValuePost

end Vsa.Sim.EnvGetReflected
