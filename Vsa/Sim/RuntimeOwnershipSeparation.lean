import Vsa.Sim.RuntimeOwnership

/-! Derive the old append/set byte-footprint interfaces from allocation roles.
The geometry arguments are data facts. No machine transition is a premise. -/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- A byte in a different role's allocation avoids every subwindow of the
written allocation. This is the common append/set interval argument. -/
theorem Ledger.outsideWindow {A : Arena} {exts : List Extent} {alloc : Allocations}
    (h : Ledger A exts alloc) {r s : Role} {p n q size lo width : Nat}
    (hr : Allocated alloc r p n) (hs : Allocated alloc s q size) (hne : r ≠ s)
    (hsub : ∀ k, lo ≤ k ∧ k < lo + width → ExtentByte (q, size) k) :
    ∀ k, ExtentByte (p, n) k → k < lo ∨ lo + width ≤ k := by
  intro k hk
  have hd := h.separated r s p n q size hr hs hne
  change p + n ≤ q ∨ q + size ≤ p at hd
  change p ≤ k ∧ k < p + n at hk
  have hn : ¬ (lo ≤ k ∧ k < lo + width) := by
    intro hw
    have hb := hsub k hw
    change q ≤ k ∧ k < q + size at hb
    omega
  omega

/-- A whole frame outside an unrelated mutable allocation, including all
indirect immutable payloads. Target frame slots use the finer adapter below. -/
theorem FrameOwned.outsideWindow
    {m : Mem} {phiF : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {fa : Addr} {f : Vsa.While.Frame}
    {A : Arena} {exts : List Extent}
    (h : FrameOwned m phiF alloc shared fa f) (hl : Ledger A exts alloc)
    (hm : Immutable alloc shared readable writes)
    {role : Role} {p n lo width : Nat}
    (ha : Allocated alloc role p n) (hmut : Role.mutable role)
    (hframe : Role.frame fa ≠ role) (hnames : Role.names fa ≠ role)
    (hvalues : Role.values fa ≠ role)
    (hsub : ∀ k, lo ≤ k ∧ k < lo + width → ExtentByte (p, n) k) :
    FrameFootprintCovered m phiF fa f (fun k => k < lo ∨ lo + width ≤ k) := by
  apply h.footprint
  · exact hl.outsideWindow h.record ha hframe hsub
  · intro q size hq
    rcases hq with hn | hv
    · exact hl.outsideWindow hn ha hnames hsub
    · exact hl.outsideWindow hv ha hvalues hsub
  · exact hm.outsideWindow hmut ha hsub

private theorem payload_inter {m : Mem} {P Q : Nat → Prop} {a : Nat} {v : Value}
    (hp : ValuePayloadCovered P m a v) (hq : ValuePayloadCovered Q m a v) :
    ValuePayloadCovered (fun k => P k ∧ Q k) m a v := by
  cases v <;> simp only [ValuePayloadCovered] at hp hq ⊢
  all_goals first
    | exact True.intro
    | exact fun p hread k hk => ⟨hp p hread k hk, hq p hread k hk⟩

/-- Combine independent window exclusions without reconstructing representation. -/
theorem footprint_inter {m : Mem} {phiF : Addr → Nat} {fa : Addr}
    {f : Vsa.While.Frame} {P Q : Nat → Prop}
    (hp : FrameFootprintCovered m phiF fa f P)
    (hq : FrameFootprintCovered m phiF fa f Q) :
    FrameFootprintCovered m phiF fa f (fun k => P k ∧ Q k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun k hk => ⟨hp.header k hk, hq.header k hk⟩
  · intro pn pv hn hv i hi
    have p := hp.slots pn pv hn hv i hi
    have q := hq.slots pn pv hn hv i hi
    exact ⟨fun k hk => ⟨p.1 k hk, q.1 k hk⟩,
      fun k hk => ⟨p.2 k hk, q.2 k hk⟩⟩
  · exact fun pn pv hn hv i hi q hr k hk =>
      ⟨hp.names pn pv hn hv i hi q hr k hk,
       hq.names pn pv hn hv i hi q hr k hk⟩
  · exact fun pn pv hn hv i hi =>
      payload_inter (hp.values pn pv hn hv i hi) (hq.values pn pv hn hv i hi)

/-- The append separation field of the old store relation, now a consequence
of role geometry and immutable sharing. -/
theorem StoreOwned.appendSeparated
    {m : Mem} {phiF phiC : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {s : Store} {A : Arena} {exts : List Extent}
    (h : StoreOwned m phiF phiC alloc shared s) (hl : Ledger A exts alloc)
    (hm : Immutable alloc shared readable writes)
    (target : Addr) (ht : target < s.frames.size)
    (cap names vals : Nat)
    (hcap : read32 m (phiF target + 4) = some cap)
    (hnames : read64 m (phiF target + 8) = some names)
    (hvals : read64 m (phiF target + 16) = some vals)
    (happend : s.frames[target].vars.length < cap) :
    (∀ fa, (hf : fa < s.frames.size) → fa ≠ target →
      FrameFootprintCovered m phiF fa s.frames[fa]
        (AppendOutside (phiF target) names vals s.frames[target].vars.length)) ∧
    (∀ ca, (hc : ca < s.closures.size) →
      ClosureFootprintCovered m phiC ca s.closures[ca]
        (AppendOutside (phiF target) names vals s.frames[target].vars.length)) := by
  have htgt := h.frames target ht
  obtain ⟨a, ha⟩ := htgt.arrays
  have ec : a.cap = cap := Option.some.inj (ha.capRead.symm.trans hcap)
  have en : a.names = names := Option.some.inj (ha.namesRead.symm.trans hnames)
  have ev : a.values = vals := Option.some.inj (ha.valuesRead.symm.trans hvals)
  have hn : Allocated alloc (.names target) names (8 * cap) := by
    simpa only [ec, en] using ha.names.nonempty (by omega : 0 < a.cap)
  have hv : Allocated alloc (.values target) vals (24 * cap) := by
    simpa only [ec, ev] using ha.values.nonempty (by omega : 0 < a.cap)
  have nsub : ∀ k, names + 8 * s.frames[target].vars.length ≤ k ∧
      k < names + 8 * s.frames[target].vars.length + 8 → ExtentByte (names, 8 * cap) k := by
    intro k hk
    change names ≤ k ∧ k < names + 8 * cap
    omega
  have vsub : ∀ k, vals + 24 * s.frames[target].vars.length ≤ k ∧
      k < vals + 24 * s.frames[target].vars.length + 24 → ExtentByte (vals, 24 * cap) k := by
    intro k hk
    change vals ≤ k ∧ k < vals + 24 * cap
    omega
  have rsub : ∀ k, phiF target ≤ k ∧ k < phiF target + 4 →
      ExtentByte (phiF target, 32) k := by
    intro k hk
    change phiF target ≤ k ∧ k < phiF target + 32
    omega
  have hshared : ∀ k, shared k →
      AppendOutside (phiF target) names vals s.frames[target].vars.length k := by
    intro k hk
    exact ⟨hm.outsideWindow (by trivial) hn nsub k hk,
      hm.outsideWindow (by trivial) hv vsub k hk,
      hm.outsideWindow (by trivial) htgt.record rsub k hk⟩
  constructor
  · intro fa hf hne
    have hfa := h.frames fa hf
    have hfn := hfa.outsideWindow hl hm hn (by trivial)
      (by simp) (by simp [hne]) (by simp) nsub
    have hfv := hfa.outsideWindow hl hm hv (by trivial)
      (by simp) (by simp) (by simp [hne]) vsub
    have hfr := hfa.outsideWindow hl hm htgt.record (by trivial)
      (by simp [hne]) (by simp) (by simp) rsub
    exact footprint_inter hfn (footprint_inter hfv hfr)
  · intro ca hc
    apply h.closureFootprint hc
    · intro k hk
      exact ⟨hl.outsideWindow (h.closures ca hc) hn (by simp) nsub k hk,
        hl.outsideWindow (h.closures ca hc) hv (by simp) vsub k hk,
        hl.outsideWindow (h.closures ca hc) htgt.record (by simp) rsub k hk⟩
    · exact hshared

/-- The set separation field, including the target frame with exactly the
selected value header removed. All other value payloads remain protected. -/
theorem StoreOwned.setSeparated
    {m : Mem} {phiF phiC : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {s : Store} {A : Arena} {exts : List Extent}
    (h : StoreOwned m phiF phiC alloc shared s) (hl : Ledger A exts alloc)
    (hm : Immutable alloc shared readable writes)
    (target : Addr) (ht : target < s.frames.size)
    (hit : Nat) (hhit : hit < s.frames[target].vars.length) (vals : Nat)
    (hvals : read64 m (phiF target + 16) = some vals) :
    let slot := vals + 24 * hit
    TargetFrameFootprintCovered m phiF target s.frames[target] hit (SetOutside slot) ∧
      (∀ fa, (hf : fa < s.frames.size) → fa ≠ target →
        FrameFootprintCovered m phiF fa s.frames[fa] (SetOutside slot)) ∧
      (∀ ca, (hc : ca < s.closures.size) →
        ClosureFootprintCovered m phiC ca s.closures[ca] (SetOutside slot)) := by
  dsimp only
  have htgt := h.frames target ht
  obtain ⟨a, ha⟩ := htgt.arrays
  have ev : a.values = vals := Option.some.inj (ha.valuesRead.symm.trans hvals)
  have hpos : 0 < a.cap := by have := ha.bound; omega
  have hv : Allocated alloc (.values target) vals (24 * a.cap) := by
    simpa only [ev] using ha.values.nonempty hpos
  have hn := ha.names.nonempty hpos
  have vsub : ∀ k, vals + 24 * hit ≤ k ∧ k < vals + 24 * hit + 24 →
      ExtentByte (vals, 24 * a.cap) k := by
    intro k hk
    have := ha.bound
    change vals ≤ k ∧ k < vals + 24 * a.cap
    omega
  have hshared : ∀ k, shared k → SetOutside (vals + 24 * hit) k :=
    hm.outsideWindow (by trivial) hv vsub
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hl.outsideWindow htgt.record hv (by simp) vsub
    · intro pn pv hpn _ i hi k hk
      have en : a.names = pn := Option.some.inj (ha.namesRead.symm.trans hpn)
      apply hl.outsideWindow hn hv (by simp) vsub
      have := ha.bound
      change a.names ≤ pn + 8 * i + k ∧ pn + 8 * i + k < a.names + 8 * a.cap
      omega
    · intro pn pv hpn _ i hi q hq k hk
      have en : a.names = pn := Option.some.inj (ha.namesRead.symm.trans hpn)
      obtain ⟨q', hq', hs⟩ := ha.keys i hi
      have hqr : read64 m (pn + 8 * i) = some q' := by simpa only [en] using hq'
      have eq : q' = q := Option.some.inj (hqr.symm.trans hq)
      subst q'
      exact hshared _ (hs.immutable.bytes k hk)
    · intro pn pv _ hpv i _ hne k hk
      have ep : pv = vals := Option.some.inj (hpv.symm.trans hvals)
      change pv + 24 * i ≤ k ∧ k < pv + 24 * i + 24 at hk
      change k < vals + 24 * hit ∨ vals + 24 * hit + 24 ≤ k
      omega
    · intro pn pv _ hpv i hi _
      exact (htgt.values pv hpv i hi).covered hshared
  · intro fa hf hne
    exact (h.frames fa hf).outsideWindow hl hm hv (by trivial)
      (by simp) (by simp) (by simp [hne]) vsub
  · intro ca hc
    exact h.closureFootprint hc
      (hl.outsideWindow (h.closures ca hc) hv (by simp) vsub) hshared

#print axioms Ledger.outsideWindow
#print axioms FrameOwned.outsideWindow
#print axioms footprint_inter
#print axioms StoreOwned.appendSeparated
#print axioms StoreOwned.setSeparated

end Vsa.Sim.RuntimeOwnership
