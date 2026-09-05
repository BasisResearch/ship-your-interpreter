import Vsa.Sim.EnvDefCompose

/-! Shared call facts without a function-specific spill image. -/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.Alloc Vsa.MemRepr

namespace Vsa.Sim

/-- Register, stack, allocator, and tick facts shared by ordinary callee seams. -/
structure CalleeFrame (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (c : Config) : Prop where
  spReg : c.σ.regs.get? Register.x2 = some sp
  stackOK : StackOK SL sp headroom
  gp : c.σ.regs.get? Register.x3 = some gpv
  abi : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R
  allocator : AInv c.σ exts
  tick : c.tick < 2

/-- Rebuild the shared frame from a callee's preserved registers and invariant. -/
theorem CalleeFrame.of_preserved
    {SL : StackLayout} {gpv : BitVec 64} {headroom : Nat}
    {AInv : MState → List (Nat × Nat) → Prop} {exts : List (Nat × Nat)}
    {sp : BitVec 64} {gm : (R : Register) → Option (RegisterType R)}
    {c c' : Config} (h : CalleeFrame SL gpv headroom AInv exts sp gm c)
    (habi : ∀ R, AbiPreserved R = true → c'.σ.regs.get? R = gm R)
    (hinv : AInv c'.σ exts) (htick : c'.tick < 2) :
    CalleeFrame SL gpv headroom AInv exts sp gm c' :=
  { spReg := (habi _ (by decide)).trans ((h.abi _ (by decide)).symm.trans h.spReg)
    stackOK := h.stackOK
    gp := (habi _ (by decide)).trans ((h.abi _ (by decide)).symm.trans h.gp)
    abi := habi
    allocator := hinv
    tick := htick }

/-- `strlen` preserves the shared frame; no spill layout is involved. -/
theorem calleeFrameStrlen (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (namePtr r : BitVec 64) (name : String) (m0 : Mem)
    (hstable : ∀ (a b : MState),
      a.regs.get? Register.x3 = b.regs.get? Register.x3 →
      (∀ k : Nat, a.mem[k]? = b.mem[k]?) → AInv a exts → AInv b exts) :
    Triple
      (fun c => strlen_pre namePtr r name m0 c ∧ CalleeFrame SL gpv headroom AInv exts sp gm c)
      (fun c => strlen_post r name m0 c ∧ CalleeFrame SL gpv headroom AInv exts sp gm c) := by
  intro c ⟨hpre, hf⟩
  have hpreCopy := hpre
  obtain ⟨_, _, hmem, _, _, _, _, _, _, _, _, _⟩ := hpreCopy
  obtain ⟨c', hs, hp, habi, htick⟩ := strlen_spec_framed namePtr r name m0 gm c ⟨hpre, hf.abi⟩
  have hpCopy := hp
  obtain ⟨_, _, _, _, hmem'⟩ := hpCopy
  refine ⟨c', hs, hp, hf.of_preserved habi ?_ htick⟩
  apply hstable c.σ c'.σ _ _ hf.allocator
  · exact (hf.abi _ (by decide)).trans (habi _ (by decide)).symm
  · intro k; rw [hmem, hmem']

/-- Byte-path `memcpy` preserves the shared frame under footprint stability. -/
theorem calleeFrameMemcpy (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (n : Nat) (m0 : Mem) (bs : Nat → BitVec 8)
    (halign : r.toNat % 4 = 0)
    (hroute : (src.toNat ^^^ dst.toNat) % 8 ≠ 0 ∨ n < 8)
    (hstable : ∀ (a b : MState),
      a.regs.get? Register.x3 = b.regs.get? Register.x3 →
      (∀ k, k < dst.toNat ∨ dst.toNat + n ≤ k → a.mem[k]? = b.mem[k]?) →
      AInv a exts → AInv b exts) :
    Triple
      (fun c => PreDispatch gm r dst src n m0 bs c ∧ CalleeFrame SL gpv headroom AInv exts sp gm c)
      (fun c => (∃ g', memcpy_bytepath_post g' r dst n m0 bs c) ∧
        CalleeFrame SL gpv headroom AInv exts sp gm c) := by
  intro c ⟨hpre, hf⟩
  obtain ⟨c', hs, ⟨g', hp⟩, habi⟩ :=
    memcpy_spec_framed_byte gm r dst src n m0 bs halign hroute c ⟨hpre, hf.abi⟩
  have hpCopy := hp
  obtain ⟨_, _, _, _, _, _, htick, _⟩ := hpCopy
  refine ⟨c', hs, ⟨g', hp⟩, hf.of_preserved habi ?_ htick⟩
  apply hstable c.σ c'.σ _ _ hf.allocator
  · exact (hf.abi _ (by decide)).trans (habi _ (by decide)).symm
  · intro k hk
    exact (hpre.meminv.outside k hk).trans
      (memcpy_framed_ainv_stable g' r dst n m0 bs c' hp k hk).symm

#print axioms calleeFrameStrlen
#print axioms calleeFrameMemcpy

end Vsa.Sim
