import VsaIris.Interp.Bridge

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProofMode Iris.BI.BigSepM
open VsaIris
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

def imgMap (img : Nat → BitVec 8) : List Nat → NatMap (BitVec 8)
  | [] => ∅
  | a :: rest => PartialMap.insert (imgMap img rest) a (img a)

theorem imgMap_get? (img : Nat → BitVec 8) :
    ∀ (l : List Nat) (k : Nat),
      PartialMap.get? (imgMap img l) k = if k ∈ l then some (img k) else none
  | [], k => by simp [imgMap, LawfulPartialMap.get?_empty]
  | a :: rest, k => by
    simp only [imgMap, Iris.Std.LawfulPartialMap.get?_insert, imgMap_get? img rest k,
      List.mem_cons]
    by_cases h : a = k
    · subst h; simp
    · simp [h, Ne.symm h]

theorem memAgree_imgMap {M : MachineModel} {img : Nat → BitVec 8} {σ : M.State}
    {l : List Nat} (h : ∀ a ∈ l, M.mem σ a = img a) : MemAgree M (imgMap img l) σ := by
  intro k v hk
  rw [imgMap_get?] at hk
  by_cases hm : k ∈ l
  · rw [if_pos hm] at hk; rw [h k hm, Option.some.inj hk]
  · rw [if_neg hm] at hk; exact absurd hk (by simp)

section Boundary

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem sepL_of_memMap (img : Nat → BitVec 8) :
    ∀ (l : List Nat), l.Nodup →
      ([∗map] k ↦ v ∈ imgMap img l, iprop(k ↦ₘ v)) ⊢ sepL (GF := GF) l (fun a => a ↦ₘ img a)
  | [], _ => by
    rw [sepL_nil]
    exact (bigSepM_eqv_empty (M := NatMap) rfl).1
  | a :: rest, hnd => by
    rw [List.nodup_cons] at hnd
    have hnone : PartialMap.get? (imgMap img rest) a = none := by
      rw [imgMap_get?, if_neg hnd.1]
    rw [show imgMap img (a :: rest) = PartialMap.insert (imgMap img rest) a (img a) from rfl,
      sepL_cons]
    refine (bigSepM_insert (M := NatMap) hnone).1.trans ?_
    iintro ⟨Ha, Hr⟩
    iframe Ha
    iapply sepL_of_memMap img rest hnd.2 $$ Hr

theorem ownImg_of_memMap {S : Nat → Prop} {img : Nat → BitVec 8} {l : List Nat}
    (hnd : l.Nodup) (hmem : ∀ a, a ∈ l ↔ S a) :
    ([∗map] k ↦ v ∈ imgMap img l, iprop(k ↦ₘ v)) ⊢ ownImg (GF := GF) S img := by
  unfold ownImg ownSet
  iintro H
  iexists l
  isplitr
  · ipureintro; exact ⟨hnd, hmem⟩
  iapply sepL_of_memMap img l hnd $$ H

end Boundary

end VsaIris.Interp
