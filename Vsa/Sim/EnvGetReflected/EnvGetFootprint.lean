import Vsa.Sim.EnvGetRecursive
import Vsa.Sim.ExitFootprint

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- The recursive lookup's memory facts at its actual return. -/
structure EnvGetReturnedMemory
    (N : NativeAddrs) (φc : Addr → Nat) (out : BitVec 64)
    (v : Value) (m0 m : Mem) : Prop where
  code : Code.Env_getLoaded m
  value : ValueRepr m N φc out.toNat v
  words : ∃ w0 w1 w2, read64 m out.toNat = some w0 ∧
    read64 m (out.toNat + 8) = some w1 ∧
    read64 m (out.toNat + 16) = some w2
  footprint : MemFootprint (resultSlot out.toNat) m0 m

/-- Destructure the legacy memory post once, identifying its witness with the
returned configuration's memory. -/
theorem EnvGetValuePost.returnedMemory
    {N : NativeAddrs} {φc : Addr → Nat}
    {out sp ret r8 r9 r18 r19 r20 r21 : BitVec 64}
    {out0 : Array String} {v : Value} {m0 : Mem} {c : Config}
    (h : EnvGetValuePost N φc out sp ret r8 r9 r18 r19 r20 r21
      out0 v m0 c) : EnvGetReturnedMemory N φc out v m0 c.σ.mem := by
  obtain ⟨m, w0, w1, w2, hmem, hcode, hvalue, hw0, hw1, hw2, hframe⟩ := h.mem
  rw [hmem]
  exact ⟨hcode, hvalue, ⟨w0, w1, w2, hw0, hw1, hw2⟩, ⟨hframe⟩⟩

/-- A recursive lookup writes its result slot and the prologue's spill
window. Parent-frame traversal adds no write window. -/
theorem EnvGetValuePost.entryFootprint
    {N : NativeAddrs} {φc : Addr → Nat}
    {out sp0 ret r8 r9 r18 r19 r20 r21 : BitVec 64}
    {out0 : Array String} {v : Value} {m0 m9 : Mem} {c : Config}
    (h : EnvGetValuePost N φc out (sp0 - 64#64) ret r8 r9 r18 r19 r20 r21
      out0 v m9 c)
    (hspill : ∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧
      k < (sp0 - 64#64).toNat + 64) → m9[k]? = m0[k]?) :
    MemFootprint (fun k =>
      ((sp0 - 64#64).toNat ≤ k ∧ k < (sp0 - 64#64).toNat + 64) ∨
      resultSlot out.toNat k) m0 c.σ.mem :=
  (MemFootprint.mk hspill).trans h.returnedMemory.footprint

/-- Fit the lookup's exact write windows into its evaluator caller's stack.
This includes the recursive parent-chain path. -/
theorem EnvGetValuePost.callerFootprint
    {N : NativeAddrs} {φc : Addr → Nat}
    {sp ret r8 r9 r18 r19 r20 r21 : BitVec 64}
    {SL : StackLayout} {out0 : Array String} {v : Value}
    {m0 m9 : Mem} {c : Config}
    (h : EnvGetValuePost N φc ((sp - 1088#64) + 0xf0#64)
      ((sp - 1088#64) - 64#64) ret r8 r9 r18 r19 r20 r21 out0 v m9 c)
    (hspill : ∀ k, ¬ (((sp - 1088#64) - 64#64).toNat ≤ k ∧
      k < ((sp - 1088#64) - 64#64).toNat + 64) → m9[k]? = m0[k]?)
    (hroom : SL.lo + 1152 ≤ sp.toNat) :
    MemFootprint (stackWin SL sp.toNat) m0 c.σ.mem := by
  have h1088 : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have := sp.isLt
    change ((2 ^ 64 - 1088) + sp.toNat) % 2 ^ 64 = sp.toNat - 1088
    omega
  have h1152 : ((sp - 1088#64) - 64#64).toNat = sp.toNat - 1152 := by
    rw [BitVec.toNat_sub, h1088]
    have := sp.isLt
    change ((2 ^ 64 - 64) + (sp.toNat - 1088)) % 2 ^ 64 = sp.toNat - 1152
    omega
  have hout : ((sp - 1088#64) + 0xf0#64).toNat = sp.toNat - 848 := by
    rw [BitVec.toNat_add, h1088]
    have := sp.isLt
    change (sp.toNat - 1088 + 240) % 2 ^ 64 = sp.toNat - 848
    omega
  exact h.entryFootprint hspill |>.mono (by
    intro k hk
    change SL.lo ≤ k ∧ k < sp.toNat
    rcases hk with hs | hr
    · rw [h1152] at hs
      omega
    · change ((sp - 1088#64) + 0xf0#64).toNat ≤ k ∧
        k < ((sp - 1088#64) + 0xf0#64).toNat + 24 at hr
      rw [hout] at hr
      omega)

/-- Successful recursive lookup with the prologue frame retained at the same
return configuration as the represented value. -/
structure EnvGetEntryPost
    (N : NativeAddrs) (φc : Addr → Nat)
    (out sp0 ret r8 r9 r18 r19 r20 r21 : BitVec 64)
    (out0 : Array String) (v : Value) (m0 m9 : Mem) (c : Config) : Prop
    extends EnvGetValuePost N φc out (sp0 - 64#64) ret r8 r9 r18 r19 r20 r21
      out0 v m9 c where
  spill : ∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧
    k < (sp0 - 64#64).toNat + 64) → m9[k]? = m0[k]?

theorem EnvGetEntryPost.footprint
    {N : NativeAddrs} {φc : Addr → Nat}
    {out sp0 ret r8 r9 r18 r19 r20 r21 : BitVec 64}
    {out0 : Array String} {v : Value} {m0 m9 : Mem} {c : Config}
    (h : EnvGetEntryPost N φc out sp0 ret r8 r9 r18 r19 r20 r21
      out0 v m0 m9 c) :
    MemFootprint (fun k =>
      ((sp0 - 64#64).toNat ≤ k ∧ k < (sp0 - 64#64).toNat + 64) ∨
      resultSlot out.toNat k) m0 c.σ.mem :=
  h.toEnvGetValuePost.entryFootprint h.spill

/-- Compose the arm-entry frame with the lookup's exact write windows. -/
theorem EnvGetEntryPost.callerFootprint
    {N : NativeAddrs} {φc : Addr → Nat} {SL : StackLayout}
    {sp ret r8 r9 r18 r19 r20 r21 : BitVec 64}
    {out0 : Array String} {v : Value} {m0 ment m9 : Mem} {c : Config}
    (h : EnvGetEntryPost N φc ((sp - 1088#64) + 0xf0#64) (sp - 1088#64)
      ret r8 r9 r18 r19 r20 r21 out0 v ment m9 c)
    (hentry : MemFootprint (stackWin SL sp.toNat) m0 ment)
    (hroom : SL.lo + 1152 ≤ sp.toNat) :
    MemFootprint (stackWin SL sp.toNat) m0 c.σ.mem :=
  (hentry.trans (h.toEnvGetValuePost.callerFootprint h.spill hroom)).mono
    (fun _ hk => hk.elim id id)

/-- Named result adapter for the landed recursive entry theorem. -/
theorem env_get_lookup_from_entry_framed
    (s : Store) (a : Addr) (v : Value)
    (name out sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (nameStr : String) (N : NativeAddrs) (A : Arena)
    (φf φc : Addr → Nat) (m0 : Mem) (c : Config) (len pn : Nat)
    (hChain : LookupChain s nameStr s.frames.size a v)
    (hEntry : PrologueHeadSt (BitVec.ofNat 64 (φf a)) name out sp0 r0
      r8 r9 r18 r19 r20 r21 len pn m0 c)
    (hStoreSurv : ∀ m',
      (∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧
        k < (sp0 - 64#64).toNat + 64) → m'[k]? = m0[k]?) →
      StoreRepr m' N A φf φc s)
    (hFactsSurv : ∀ m',
      (∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧
        k < (sp0 - 64#64).toNat + 64) → m'[k]? = m0[k]?) →
      EnvGetChainFacts name out (sp0 - 64#64) r0 r8 r9 r18 r19 r20 r21
        nameStr N φf φc m' s)
    (hStrcmpSurv : ∀ m',
      (∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧
        k < (sp0 - 64#64).toNat + 64) → m'[k]? = m0[k]?) →
      StrcmpLoaded m') :
    ∃ c' m9, Steps c c' ∧
      EnvGetEntryPost N φc out sp0 r0 r8 r9 r18 r19 r20 r21
        c.σ.sailOutput v m0 m9 c' := by
  obtain ⟨c', m9, hs, hpost, hspill⟩ :=
    env_get_lookup_from_entry s a v name out sp0 r0 r8 r9 r18 r19 r20 r21
      nameStr N A φf φc m0 c len pn hChain hEntry hStoreSurv hFactsSurv hStrcmpSurv
  exact ⟨c', m9, hs, { toEnvGetValuePost := hpost, spill := hspill }⟩

#print axioms EnvGetEntryPost.footprint
#print axioms EnvGetEntryPost.callerFootprint
#print axioms env_get_lookup_from_entry_framed
#print axioms EnvGetValuePost.returnedMemory
#print axioms EnvGetValuePost.entryFootprint
#print axioms EnvGetValuePost.callerFootprint

end Vsa.Sim
