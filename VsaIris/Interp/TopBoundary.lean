import VsaIris.Interp.World
import VsaIris.Vsa.Console
import VsaIris.Vsa.BinImg
import VsaIris.Interp.Code

/-!
# Adequacy's inputs at the boundary (lane A)

INTERP_DESIGN.md §5.2-§5.4. What `vsa_adequacy_exit` / `vsa_adequacyP_nonzero`
take besides the WP: the `live` set (the fixed binary's `.text` and
`.rodata`, present by `FixedTextLoaded`/`FixedRodataLoaded`), the global
invariant `VsaOk` at the loaded configuration, and the register map with its
agreement. The register map is the entry configuration's `PC` and general
registers; `sepL_of_regMap` turns adequacy's big-op over it into one
points-to per register.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode Iris.BI.BigSepM
open VsaIris VsaIris.Inst VsaIris.Sym
open Vsa.Sim Vsa.Sim.LayoutInstance

/-! ## The live set -/

/-- The bytes every run fetches or loads without owning them: the binary's
`.text` and `.rodata` except the embedded script `[0x80018be0, 0x80018da6)`
(never read; not pinned by `FixedRodataLoaded`), `_impure_ptr` (the helpers'
code lists `envText` and `allocText` load it) and the stack segment
(`stringify`'s `strlen` reads its stack buffer through the run's read-only
text). All are present in the loaded configuration (`topLive_present`). -/
def topLive (a : Nat) : Prop :=
  (0x80000000 ≤ a ∧ a < 0x8001acf0 ∧ ¬ (0x80018be0 ≤ a ∧ a < 0x80018da6)) ∨
    (0x8001b970 ≤ a ∧ a < 0x8001b978) ∨ (0x87800000 ≤ a ∧ a < 0x88000000)

theorem interpText_all :
    VsaIris.Sym.interpText.all (fun p => (0x80000000 ≤ p.1 && p.1 < 0x8001acf0 &&
      !(0x80018be0 ≤ p.1 && p.1 < 0x80018da6))) = true := by decide +kernel

theorem topLive_interp : ∀ p ∈ VsaIris.Sym.interpText, topLive p.1 := by
  intro p hp
  have h := List.all_eq_true.1 interpText_all p hp
  refine .inl ⟨?_, ?_, ?_⟩ <;> revert h <;> simp <;> omega

theorem topLive_code : Newlib.CodeLive topLive := by
  intro a ha
  unfold Newlib.textDom at ha
  exact .inl ⟨ha.1, by omega, by omega⟩

/-- The live bytes are present in a loaded configuration. -/
theorem topLive_present {m : Vsa.MemRepr.Mem} (ht : Code.FixedTextLoaded m)
    (hr : Code.FixedRodataLoaded m) (hi : Code.ImageStaticsLoaded m)
    (hs : ∀ k, stackSL.lo ≤ k → k < stackSL.hi → ∃ b : BitVec 8, m[k]? = some b) :
    ∀ a, topLive a → (m[a]?).isSome := by
  intro a ha
  rcases ha with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  rotate_left
  · have hp := Code.imageStatics_impurePtr_range hi
    unfold Code.imgImpurePtr at hp
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := hp
    obtain ⟨k, hk, rfl⟩ : ∃ k, k < 8 ∧ a = 0x8001b970 + k := ⟨a - 0x8001b970, by omega, by omega⟩
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show (0x8001b970 : Nat) + 0 = 0x8001b970 from rfl, e0]; rfl
    · rw [e1]; rfl
    · rw [e2]; rfl
    · rw [e3]; rfl
    · rw [e4]; rfl
    · rw [e5]; rfl
    · rw [e6]; rfl
    · rw [e7]; rfl
  · obtain ⟨b, hb⟩ := hs a h1 h2
    rw [hb]; rfl
  by_cases h : a < 0x80018be0
  · have := ht (a - 0x80000000) (by unfold Code.fixedTextSize; omega)
    rw [show Code.fixedTextBase + (a - 0x80000000) = a by unfold Code.fixedTextBase; omega] at this
    rw [this]; rfl
  · rw [hr.byteAt (by omega) h2]; rfl

/-! ## The global invariant at the boundary -/

/-- **`VsaOk` at a loaded configuration.** Every general register is present
by the boundary field `InterpRunReadyFacts.gprs`. -/
theorem vsaOk_of_ready {c : Vsa.Machine.Config} {stmts count : Nat} {inp : BitVec 64}
    {N : Vsa.RuntimeRepr.NativeAddrs} {A : Vsa.RuntimeRepr.Arena} {φf φc : Vsa.While.Addr → Nat}
    {aLeft : Nat} (F : InterpRunReadyFacts c stmts count inp N A φf φc aLeft) :
    VsaOk topLive c where
  good := F.good
  tick := F.tick
  gpr := F.gprs
  live := topLive_present F.text_image F.rodata_image F.statics F.stack_bytes
  htifIdle := F.htif_payload

/-! ## The register map -/

/-- The finite register map holding `rv` on exactly the registers of `l`. -/
def regMap (rv : Nat → BitVec 64) : List Nat → NatMap (BitVec 64)
  | [] => ∅
  | r :: rest => PartialMap.insert (regMap rv rest) r (rv r)

theorem regMap_get? (rv : Nat → BitVec 64) :
    ∀ (l : List Nat) (k : Nat),
      PartialMap.get? (regMap rv l) k = if k ∈ l then some (rv k) else none
  | [], k => by simp [regMap, LawfulPartialMap.get?_empty]
  | a :: rest, k => by
    simp only [regMap, Iris.Std.LawfulPartialMap.get?_insert, regMap_get? rv rest k,
      List.mem_cons]
    by_cases h : a = k
    · subst h; simp
    · simp [h, Ne.symm h]

/-- The map agrees with the configuration it is read off. -/
theorem regAgree_regMap {M : MachineModel} (σ : M.State) (l : List Nat) :
    RegAgree M (regMap (M.reg σ) l) σ := by
  intro k v hk
  rw [regMap_get?] at hk
  by_cases hm : k ∈ l
  · rw [if_pos hm] at hk; exact Option.some.inj hk
  · rw [if_neg hm] at hk; exact absurd hk (by simp)

/-- The registers adequacy hands the client: `PC` and `x1`–`x31`. -/
def topRegs : List Nat := VsaIris.PC :: List.range' 1 31

theorem topRegs_nodup : topRegs.Nodup := by decide

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **One points-to per register** out of adequacy's big-op. -/
theorem sepL_of_regMap (rv : Nat → BitVec 64) :
    ∀ (l : List Nat), l.Nodup →
      ([∗map] k ↦ v ∈ regMap rv l, iprop(k ↦ᵣ v)) ⊢ sepL (GF := GF) l (fun r => r ↦ᵣ rv r)
  | [], _ => by
    rw [sepL_nil]
    exact (bigSepM_eqv_empty (M := NatMap) rfl).1
  | a :: rest, hnd => by
    rw [List.nodup_cons] at hnd
    have hnone : PartialMap.get? (regMap rv rest) a = none := by
      rw [regMap_get?, if_neg hnd.1]
    rw [show regMap rv (a :: rest) = PartialMap.insert (regMap rv rest) a (rv a) from rfl,
      sepL_cons]
    refine (bigSepM_insert (M := NatMap) hnone).1.trans ?_
    iintro ⟨Ha, Hr⟩
    iframe Ha
    iapply sepL_of_regMap rv rest hnd.2 $$ Hr

end

end VsaIris.Interp
