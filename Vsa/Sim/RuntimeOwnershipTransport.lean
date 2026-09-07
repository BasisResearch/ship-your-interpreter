import Vsa.Sim.AstFootprintTransport
import Vsa.Sim.RuntimeOwnershipInitial

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- Any bounded read window within a covered extent is covered. -/
theorem extent_covers {P : Nat → Prop} {p n off width : Nat}
    (hc : ∀ k, ExtentByte (p, n) k → P k) (hw : off + width ≤ n) :
    Covers P (p + off) width := by
  intro i hi
  apply hc
  unfold ExtentByte
  dsimp
  omega

/-- Shared payload ownership and its pointer word survive covered-byte agreement. -/
theorem ValueOwned.transport {m m' : Mem} {P shared : Nat → Prop} {a : Nat} {v : Value}
    (h : ValueOwned m shared a v) (ha : AgreeP P m m')
    (hh : ∀ k, valHeader a k → P k) (hs : ∀ k, shared k → P k) :
    ValueOwned m' shared a v := by
  have hp : read64 m (a + 8) = read64 m' (a + 8) :=
    (extent_covers hh (by decide : 8 + 8 ≤ 24)).read64_eq ha
  cases v <;> simp only [ValueOwned] at h ⊢
  all_goals first
    | exact True.intro
    | (obtain ⟨p, hr, hc⟩ := h
       exact ⟨p, hp.symm.trans hr, hc.transport (fun k hk => ha k (hs k hk))⟩)

/-- Preserve all frame ownership facts, including copied names and value payloads. -/
theorem FrameOwned.transport {m m' : Mem} {phiF : Addr → Nat} {alloc : Allocations}
    {shared P : Nat → Prop} {fa : Addr} {f : Vsa.While.Frame}
    (h : FrameOwned m phiF alloc shared fa f) (ha : AgreeP P m m')
    (hf : FrameFootprintCovered m phiF fa f P) (hs : ∀ k, shared k → P k) :
    FrameOwned m' phiF alloc shared fa f := by
  have hc := (extent_covers hf.header (by decide : 4 + 4 ≤ 32)).read32_eq ha
  have hn := (extent_covers hf.header (by decide : 8 + 8 ≤ 32)).read64_eq ha
  have hv := (extent_covers hf.header (by decide : 16 + 8 ≤ 32)).read64_eq ha
  obtain ⟨a, arrays⟩ := h.arrays
  refine ⟨h.record, ⟨a, ?_⟩, ?_⟩
  · refine ⟨hc.symm.trans arrays.capRead, hn.symm.trans arrays.namesRead,
      hv.symm.trans arrays.valuesRead, arrays.bound, arrays.names, arrays.values, ?_⟩
    intro i hi
    obtain ⟨q, hq, key⟩ := arrays.keys i hi
    have heq := read64_agreeP ha
      (hf.slots a.names a.values arrays.namesRead arrays.valuesRead i hi).1
    exact ⟨q, heq.symm.trans hq, key.allocated,
      key.immutable.transport (fun k hk => ha k (hs k hk))⟩
  · intro pv hpv i hi
    have hpv0 := hv.trans hpv
    exact (h.values pv hpv0 i hi).transport ha
      (hf.slots a.names pv arrays.namesRead hpv0 i hi).2 hs

/-- Ownership supplies the existing frame-footprint carrier from allocation coverage. -/
theorem StoreOwned.frameFootprint {m : Mem} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {shared P : Nat → Prop} {s : Store}
    (h : StoreOwned m phiF phiC alloc shared s)
    (ha : ∀ role p n, Allocated alloc role p n → ∀ k, ExtentByte (p, n) k → P k)
    (hs : ∀ k, shared k → P k) {fa : Addr} (hf : fa < s.frames.size) :
    FrameFootprintCovered m phiF fa s.frames[fa] P := by
  apply (h.frames fa hf).footprint
  · exact ha _ _ _ (h.frames fa hf).record
  · intro p n hp
    rcases hp with hn | hv
    · exact ha _ _ _ hn
    · exact ha _ _ _ hv
  · exact hs

/-- General store ownership transport also preserves pointer-dependent closure footprints. -/
theorem StoreOwned.transport {m m' : Mem} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {shared P : Nat → Prop} {s : Store}
    (h : StoreOwned m phiF phiC alloc shared s) (hag : AgreeP P m m')
    (ha : ∀ role p n, Allocated alloc role p n → ∀ k, ExtentByte (p, n) k → P k)
    (hs : ∀ k, shared k → P k) : StoreOwned m' phiF phiC alloc shared s := by
  refine ⟨?_, h.closures, h.valueClosures, h.capturedEnvs, ?_⟩
  · intro fa hf
    exact (h.frames fa hf).transport hag (h.frameFootprint ha hs hf) hs
  · intro ca hc q hq k hk
    have heq : read64 m (phiC ca) = read64 m' (phiC ca) := by
      simpa only [Nat.add_zero] using
        (extent_covers (ha _ _ _ (h.closures ca hc))
          (by decide : 0 + 8 ≤ 16)).read64_eq hag
    have hq0 := heq.trans hq
    exact h.closureAsts ca hc q hq0 k
      (hk.pullback hag (fun j hj => hs j (h.closureAsts ca hc q hq0 j hj)))

/-- The same owned-byte agreement preserves the semantic store representation. -/
theorem StoreOwned.repr_transport {m m' : Mem} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {shared P : Nat → Prop} {s : Store}
    (h : StoreOwned m phiF phiC alloc shared s) (hr : StoreRepr m N A phiF phiC s)
    (hag : AgreeP P m m')
    (ha : ∀ role p n, Allocated alloc role p n → ∀ k, ExtentByte (p, n) k → P k)
    (hs : ∀ k, shared k → P k) : StoreRepr m' N A phiF phiC s := by
  apply storeRepr_agreeP hag
    (fun fa hf => (h.frameFootprint ha hs hf).header)
    (fun fa hf => (h.frameFootprint ha hs hf).slots)
    (fun fa hf => (h.frameFootprint ha hs hf).names)
    (fun fa hf => (h.frameFootprint ha hs hf).values)
    (fun ca hc => ha _ _ _ (h.closures ca hc)) ?_ hr
  intro ca hc q hq he
  exact exprRepr_agreeP hag (fun k hk => hs k (h.closureAsts ca hc q hq k hk)) he

/-- Ledger geometry and reservations stay fixed while represented bytes are preserved. -/
theorem HeapOwned.transport {m m' : Mem} {A : Arena} {exts : List Extent}
    {phiF phiC : Addr → Nat} {alloc : Allocations}
    {shared readable writes P : Nat → Prop} {s : Store}
    (h : HeapOwned A exts m phiF phiC alloc shared readable writes s)
    (hag : AgreeP P m m')
    (ha : ∀ role p n, Allocated alloc role p n → ∀ k, ExtentByte (p, n) k → P k)
    (hs : ∀ k, shared k → P k) :
    HeapOwned A exts m' phiF phiC alloc shared readable writes s :=
  ⟨h.ledger, h.immutable, h.reserved, h.store.transport hag ha hs⟩

/-- Preserve all three copied words, including semantically unused padding. -/
theorem valueWordsTotal_transport {m m' : Mem} {P : Nat → Prop} {a : Nat}
    (h : ValueWordsTotal m a) (ha : AgreeP P m m')
    (hh : ∀ k, valHeader a k → P k) : ValueWordsTotal m' a := by
  obtain ⟨d0, d1, d2, h0, h1, h2⟩ := h
  have e0 : read64 m a = read64 m' a := by
    simpa only [Nat.add_zero] using
      (extent_covers hh (by decide : 0 + 8 ≤ 24)).read64_eq ha
  have e1 := (extent_covers hh (by decide : 8 + 8 ≤ 24)).read64_eq ha
  have e2 := (extent_covers hh (by decide : 16 + 8 ≤ 24)).read64_eq ha
  exact ⟨d0, d1, d2, e0.symm.trans h0, e1.symm.trans h1, e2.symm.trans h2⟩

/-- Preserve array access readiness using the store's owned footprint. -/
theorem StoreArraysReady.transport {m m' : Mem} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {shared P : Nat → Prop} {s : Store}
    (h : StoreArraysReady m phiF s) (ho : StoreOwned m phiF phiC alloc shared s)
    (hag : AgreeP P m m')
    (ha : ∀ role p n, Allocated alloc role p n → ∀ k, ExtentByte (p, n) k → P k)
    (hs : ∀ k, shared k → P k) : StoreArraysReady m' phiF s := by
  have hn : ∀ fa, fa < s.frames.size →
      read64 m (phiF fa + 8) = read64 m' (phiF fa + 8) := fun fa hf =>
    (extent_covers (ho.frameFootprint ha hs hf).header
      (by decide : 8 + 8 ≤ 32)).read64_eq hag
  have hv : ∀ fa, fa < s.frames.size →
      read64 m (phiF fa + 16) = read64 m' (phiF fa + 16) := fun fa hf =>
    (extent_covers (ho.frameFootprint ha hs hf).header
      (by decide : 16 + 8 ≤ 32)).read64_eq hag
  refine ⟨fun fa hf pn hp => h.namesAligned fa hf pn ((hn fa hf).trans hp),
    fun fa hf pv hp => h.valuesAligned fa hf pv ((hv fa hf).trans hp), ?_⟩
  intro fa hf pv hp i hi
  have hp0 := (hv fa hf).trans hp
  obtain ⟨a, arrays⟩ := (ho.frames fa hf).arrays
  exact valueWordsTotal_transport (h.valueWords fa hf pv hp0 i hi) hag
    ((ho.frameFootprint ha hs hf).slots a.names pv arrays.namesRead hp0 i hi).2

#print axioms extent_covers
#print axioms ValueOwned.transport
#print axioms FrameOwned.transport
#print axioms StoreOwned.frameFootprint
#print axioms StoreOwned.transport
#print axioms StoreOwned.repr_transport
#print axioms HeapOwned.transport
#print axioms valueWordsTotal_transport
#print axioms StoreArraysReady.transport

end Vsa.Sim.RuntimeOwnership
