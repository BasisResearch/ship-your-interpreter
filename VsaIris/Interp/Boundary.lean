import VsaIris.Interp.Bridge

/-!
# The boundary: byte ownership out of the initial memory map (package R)

Adequacy hands the client `[∗map] k ↦ v ∈ mm, k ↦ₘ v` for ANY finite byte map
`mm` that agrees with the initial machine memory (`MemAgree`, a *partial*
agreement — the client picks which bytes it wants to own). This file turns
that big-op into the two resources the §3 predicates are built from:

* `ownImg S img` — exclusive bytes at their image values (`ownImg_of_memMap`);
* `roOn P m` — the read-only view the persistent predicates need
  (`roOn_of_memMap`, one `|==>` discard).

`imgMap img l` is the finite map over the address list `l`; `extAddrs` and
`blockAddrs` enumerate an extent and a block list, so a concrete boundary
names its owned bytes as a list of extents and nothing else.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProofMode Iris.BI.BigSepM
open VsaIris
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-! ## Address lists -/

/-- Every address of one extent. -/
def extAddrs (e : Nat × Nat) : List Nat := (List.range e.2).map (e.1 + ·)

theorem mem_extAddrs {e : Nat × Nat} {a : Nat} : a ∈ extAddrs e ↔ InExt e a := by
  unfold extAddrs InExt
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨a - e.1, by omega, by omega⟩

theorem extAddrs_nodup (e : Nat × Nat) : (extAddrs e).Nodup :=
  List.Pairwise.map (fun i => e.1 + i) (fun a b h => by omega) List.nodup_range

/-- Every address of a list of blocks. -/
def blockAddrs (bl : List (Nat × Nat)) : List Nat := bl.flatMap extAddrs

theorem mem_blockAddrs {bl : List (Nat × Nat)} {a : Nat} :
    a ∈ blockAddrs bl ↔ BlocksCover bl a := by
  unfold blockAddrs BlocksCover
  simp only [List.mem_flatMap, mem_extAddrs]

/-- Pairwise-disjoint blocks enumerate without repeats. -/
theorem blockAddrs_nodup {bl : List (Nat × Nat)} (h : bl.Pairwise ExtDisj) :
    (blockAddrs bl).Nodup := by
  induction bl with
  | nil => simp [blockAddrs]
  | cons b bs ih =>
    rw [List.pairwise_cons] at h
    simp only [blockAddrs, List.flatMap_cons]
    refine List.nodup_append.2 ⟨extAddrs_nodup b, ih h.2, ?_⟩
    intro a ha a' ha' hab
    subst hab
    obtain ⟨b', hb', hin⟩ := mem_blockAddrs.1 ha'
    exact h.1 b' hb' a (mem_extAddrs.1 ha) hin

/-! ## The finite byte map of an address list -/

/-- The finite byte map holding `img` on exactly the addresses of `l`. -/
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

/-- The map agrees with any memory holding the image on `l`. -/
theorem memAgree_imgMap {M : MachineModel} {img : Nat → BitVec 8} {σ : M.State}
    {l : List Nat} (h : ∀ a ∈ l, M.mem σ a = img a) : MemAgree M (imgMap img l) σ := by
  intro k v hk
  rw [imgMap_get?] at hk
  by_cases hm : k ∈ l
  · rw [if_pos hm] at hk; rw [h k hm, Option.some.inj hk]
  · rw [if_neg hm] at hk; exact absurd hk (by simp)

section Boundary

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **Carving.** The boundary's big-op over `imgMap img l` is exactly the
`sepL` of its bytes. -/
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

/-- **Exclusive bytes** out of the boundary map. -/
theorem ownImg_of_memMap {S : Nat → Prop} {img : Nat → BitVec 8} {l : List Nat}
    (hnd : l.Nodup) (hmem : ∀ a, a ∈ l ↔ S a) :
    ([∗map] k ↦ v ∈ imgMap img l, iprop(k ↦ₘ v)) ⊢ ownImg (GF := GF) S img := by
  unfold ownImg ownSet
  iintro H
  iexists l
  isplitr
  · ipureintro; exact ⟨hnd, hmem⟩
  iapply sepL_of_memMap img l hnd $$ H

/-- **A read-only view** out of the boundary map: one discard. -/
theorem roOn_of_memMap {P : Nat → Prop} {img : Nat → BitVec 8} {m : Mem} {l : List Nat}
    (hnd : l.Nodup) (hmem : ∀ a, a ∈ l ↔ P a) (hag : ∀ k, P k → m[k]? = some (img k)) :
    ([∗map] k ↦ v ∈ imgMap img l, iprop(k ↦ₘ v)) ⊢ |==> roOn (GF := GF) P m := by
  iintro H
  iapply roOn_of_ownImg hag
  iapply ownImg_of_memMap hnd hmem $$ H

end Boundary

#print axioms sepL_of_memMap
#print axioms ownImg_of_memMap
#print axioms roOn_of_memMap

end VsaIris.Interp
