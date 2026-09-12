import Vsa.Sim.EnvGetSpec9
import Vsa.Sim.RuntimeOwnershipLookup
import SharedReadGeometry

open LeanRV64DExecutable Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim
open RuntimeOwnership

/-- Shared-byte geometry supplies the word loop's slack without alignment. -/
theorem strcmpWSlack_of_shared {shared : Nat → Prop} {SL : StackLayout}
    (hG : SharedReadGeom shared SL) {p : BitVec 64} {len : Nat}
    (hbytes : ∀ k, k ≤ len → shared (p.toNat + k)) : StrcmpWSlack p len := by
  have h0 := hG.ram _ (hbytes 0 (Nat.zero_le _))
  have hl := hG.ram _ (hbytes len (Nat.le_refl _))
  have hc := shared_string_window (by decide : 0x80006ea0 < 0x80006fcc) hG.code hbytes
  have ht := shared_string_window (by omega : tohostAddr < tohostAddr + 8) hG.htif hbytes
  exact ⟨by omega, by omega, by omega, hc, ht⟩

/-- The actual CString fixes the length used by each scan-region request. -/
theorem RuntimeOwnership.SharedCString.strcmpSlack
    {m : Mem} {shared : Nat → Prop} {SL : StackLayout} {p : Nat} {s : String}
    (h : SharedCString m shared p s) (hG : SharedReadGeom shared SL) :
    ∀ cs, CStr m p cs → StrcmpWSlack (BitVec.ofNat 64 p) cs.length := by
  intro cs hcs
  obtain ⟨cs0, hcs0, hs⟩ := h.repr
  have heq := cstr_unique_eg9 m p cs cs0 hcs hcs0
  subst cs
  have hp := hG.ram _ (h.bytes 0 (Nat.zero_le _))
  have hptr : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply strcmpWSlack_of_shared hG
  intro k hk
  rw [hptr]
  exact h.bytes k (by rw [hs, String.length_ofList]; exact hk)

/-- An actual names-array read selects the owned binding string at that slot. -/
theorem RuntimeOwnership.FrameOwned.bindingString
    {m : Mem} {phiF : Addr → Nat} {alloc : Allocations} {shared : Nat → Prop}
    {fa : Addr} {f : Vsa.While.Frame} {pn q i : Nat}
    (h : FrameOwned m phiF alloc shared fa f)
    (hpn : read64 m (phiF fa + 8) = some pn)
    (hi : i < f.vars.length) (hq : read64 m (pn + 8 * i) = some q) :
    SharedCString m shared q f.vars[i].1 := by
  obtain ⟨a, ha⟩ := h.arrays
  have hnames : a.names = pn := Option.some.inj (ha.namesRead.symm.trans hpn)
  obtain ⟨q0, hq0, hkey⟩ := ha.keys i hi
  rw [hnames] at hq0
  have heq : q0 = q := Option.some.inj (hq0.symm.trans hq)
  simpa only [heq] using hkey.immutable

/-- Ownership supplies the repaired scan carrier for every occupied binding.
The caller provides the actual query string and the fixed mask bytes. -/
theorem RuntimeOwnership.FrameOwned.scanNames
    {m : Mem} {phiF : Addr → Nat} {alloc : Allocations} {shared : Nat → Prop}
    {fa : Addr} {f : Vsa.While.Frame} {pn : Nat} {name : BitVec 64} {s : String}
    {A : Arena} {SL : StackLayout} {exts : List Extent}
    (h : FrameOwned m phiF alloc shared fa f)
    (hl : Ledger A exts alloc) (hG : SharedReadGeom shared SL)
    (hlo : 0x80000000 ≤ A.lo) (hhi : A.hi ≤ 0x100000000)
    (hht : tohostAddr + 8 ≤ A.lo)
    (hpn : read64 m (phiF fa + 8) = some pn) (halign : pn % 8 = 0)
    (hname : SharedCString m shared name.toNat s) (hmask : MaskPinned m) :
    ScanNames m pn name s f := by
  obtain ⟨a, ha⟩ := h.arrays
  have hnames : a.names = pn := Option.some.inj (ha.namesRead.symm.trans hpn)
  have hslot : ∀ i, i < f.vars.length → A.contains (pn + 8 * i) 8 := by
    intro i hi
    simpa only [hnames] using ha.names.slot_in_arena hl (Nat.lt_of_lt_of_le hi ha.bound)
  have hquery : ∀ cs, CStr m name.toNat cs → StrcmpWSlack name cs.length := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hname.strcmpSlack hG
  have hbinding : ∀ i, (hi : i < f.vars.length) → ∀ q,
      read64 m (pn + 8 * i) = some q → ∀ cs, CStr m q cs →
      StrcmpWSlack (BitVec.ofNat 64 q) cs.length := by
    intro i hi q hq
    exact (h.bindingString hpn hi hq).strcmpSlack hG
  refine
    { maskPinned := hmask
      nameCStr := hname.repr
      nameRegB := fun cs hcs => (hquery cs hcs).toRegion
      nameRegW := hquery
      bindPtr := ?_
      bindRegB := fun i hi q hq cs hcs => (hbinding i hi q hq cs hcs).toRegion
      bindRegW := hbinding
      slotLo := ?_
      slotHi := ?_
      slotHtif := ?_
      slotAlign := fun i _ => by omega }
  · intro i hi
    obtain ⟨q, hq, hk⟩ := ha.keys i hi
    exact ⟨q, by simpa only [hnames] using hq, hk.immutable.repr⟩
  · intro i hi
    have hs := hslot i hi
    exact Nat.le_trans hlo hs.1
  · intro i hi
    have hs := hslot i hi
    exact Nat.le_trans hs.2 hhi
  · intro i hi
    exact Or.inr (Nat.le_trans hht (hslot i hi).1)

#print axioms strcmpWSlack_of_shared
#print axioms RuntimeOwnership.SharedCString.strcmpSlack
#print axioms RuntimeOwnership.FrameOwned.bindingString
#print axioms RuntimeOwnership.FrameOwned.scanNames

end Vsa.Sim
