import Vsa.Sim.HeapOwnershipGeometry
import Vsa.Sim.StoreInvariant

/-! Data-only ownership with empty arrays and shared immutable payloads.
No allocator or execution supplier is assumed.
`readable` and `writes` are byte predicates to instantiate at the calling
boundary. They do not state that execution terminates or allocation succeeds. -/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

inductive Role where
  | frame (fa : Addr)
  | names (fa : Addr)
  | values (fa : Addr)
  | binding (fa : Addr) (index : Nat)
  | closure (ca : Addr)
  deriving DecidableEq

def Role.mutable : Role → Prop
  | .binding _ _ => False
  | _ => True

abbrev Allocations := Role → Option Extent

def Allocated (alloc : Allocations) (role : Role) (p n : Nat) : Prop :=
  alloc role = some (p, n)

def ExtentByte (e : Extent) (k : Nat) : Prop := e.1 ≤ k ∧ k < e.1 + e.2

/-- Different allocation roles cannot designate overlapping extents.
Copied names have separate roles but are immutable after initialization. -/
structure Ledger (A : Arena) (exts : List Extent) (alloc : Allocations) : Prop where
  arena : HeapArena A exts
  live : ∀ role p n, Allocated alloc role p n → (p, n) ∈ exts
  separated : ∀ r s p n q size,
    Allocated alloc r p n → Allocated alloc s q size → r ≠ s →
    ExtDisjoint (p, n) (q, size)

/-- Shared payload bytes may alias each other, including suffix sharing.
They remain outside every mutable allocation and the caller's additional
write footprint (stack, allocator metadata, output, interpreter fields). -/
structure Immutable (alloc : Allocations) (shared readable writes : Nat → Prop) : Prop where
  readable : ∀ k, shared k → readable k
  outsideWrites : ∀ k, shared k → ¬ writes k
  outsideMutable : ∀ role p n, Role.mutable role → Allocated alloc role p n →
    ∀ k, shared k → ¬ ExtentByte (p, n) k

/-- Zero capacity has canonical NULL storage and consumes no live extent. -/
def ArrayOwned (alloc : Allocations) (role : Role) (p width cap : Nat) : Prop :=
  (cap = 0 ∧ p = 0) ∨ (0 < cap ∧ Allocated alloc role p (width * cap))

theorem ArrayOwned.empty {alloc : Allocations} {role : Role} {width : Nat} :
    ArrayOwned alloc role 0 width 0 := Or.inl ⟨rfl, rfl⟩

theorem ArrayOwned.nonempty {alloc : Allocations} {role : Role}
    {p width cap : Nat} (h : ArrayOwned alloc role p width cap) (hc : 0 < cap) :
    Allocated alloc role p (width * cap) := by
  rcases h with ⟨hz, _⟩ | ⟨_, ha⟩
  · omega
  · exact ha

/-- CString supplies byte presence. `shared` supplies geometry and stability. -/
structure SharedCString (m : Mem) (shared : Nat → Prop) (p : Nat) (s : String) : Prop where
  repr : CString m p s
  bytes : ∀ k, k ≤ s.length → shared (p + k)

/-- Binding keys are copied allocations, unlike native/AST payload pointers. -/
structure CopiedCString (m : Mem) (alloc : Allocations) (shared : Nat → Prop)
    (role : Role) (p : Nat) (s : String) : Prop where
  allocated : Allocated alloc role p (s.length + 1)
  immutable : SharedCString m shared p s

def ValueOwned (m : Mem) (shared : Nat → Prop) (a : Nat) : Value → Prop
  | .str s => ∃ p, read64 m (a + 8) = some p ∧ SharedCString m shared p s
  | .native f => ∃ p, read64 m (a + 8) = some p ∧
      SharedCString m shared p (nativeName f)
  | _ => True

/-- Existing copy/update consumers need the same indirect footprint, regardless
of whether the shared bytes originated in an allocation or in immutable AST. -/
theorem ValueOwned.covered {m : Mem} {shared P : Nat → Prop} {a : Nat} {v : Value}
    (h : ValueOwned m shared a v) (hP : ∀ k, shared k → P k) :
    ValuePayloadCovered P m a v := by
  cases v <;> simp only [ValueOwned, ValuePayloadCovered] at h ⊢
  all_goals first
    | exact True.intro
    | (obtain ⟨p, hp, hs⟩ := h
       intro q hq k hk
       have heq : p = q := Option.some.inj (hp.symm.trans hq)
       subst q
       exact hP _ (hs.bytes k hk))

/-- Runtime array pointers and their common capacity. -/
structure ArrayState where
  cap : Nat
  names : Nat
  values : Nat

/-- Reads and ownership of one frame's backing arrays. -/
structure FrameArraysOwned (m : Mem) (phiF : Addr → Nat) (alloc : Allocations)
    (shared : Nat → Prop) (fa : Addr) (f : Vsa.While.Frame) (a : ArrayState) : Prop where
  capRead : read32 m (phiF fa + 4) = some a.cap
  namesRead : read64 m (phiF fa + 8) = some a.names
  valuesRead : read64 m (phiF fa + 16) = some a.values
  bound : f.vars.length ≤ a.cap
  names : ArrayOwned alloc (.names fa) a.names 8 a.cap
  values : ArrayOwned alloc (.values fa) a.values 24 a.cap
  keys : ∀ i, (hi : i < f.vars.length) → ∃ q,
    read64 m (a.names + 8 * i) = some q ∧
    CopiedCString m alloc shared (.binding fa i) q f.vars[i].1

structure FrameOwned (m : Mem) (phiF : Addr → Nat) (alloc : Allocations)
    (shared : Nat → Prop) (fa : Addr) (f : Vsa.While.Frame) : Prop where
  record : Allocated alloc (.frame fa) (phiF fa) 32
  arrays : ∃ a, FrameArraysOwned m phiF alloc shared fa f a
  values : ∀ pv, read64 m (phiF fa + 16) = some pv →
    ∀ i, (hi : i < f.vars.length) → ValueOwned m shared (pv + 24 * i) f.vars[i].2

/-- Exact footprint adapter. Its hypotheses describe covered allocation bytes;
no whole-memory agreement or detached machine conclusion is required. -/
theorem FrameOwned.footprint {m : Mem} {phiF : Addr → Nat} {alloc : Allocations}
    {shared P : Nat → Prop} {fa : Addr} {f : Vsa.While.Frame}
    (h : FrameOwned m phiF alloc shared fa f)
    (hrecord : ∀ k, ExtentByte (phiF fa, 32) k → P k)
    (harrays : ∀ p n, (Allocated alloc (.names fa) p n ∨
      Allocated alloc (.values fa) p n) → ∀ k, ExtentByte (p, n) k → P k)
    (hshared : ∀ k, shared k → P k) :
    FrameFootprintCovered m phiF fa f P := by
  refine ⟨hrecord, ?_, ?_, ?_⟩
  · intro pn pv hpn hpv i hi
    obtain ⟨⟨cap, names, vals⟩, _, hn, hv, hc, hna, hva, _⟩ := h.arrays
    have en : names = pn := Option.some.inj (hn.symm.trans hpn)
    have ev : vals = pv := Option.some.inj (hv.symm.trans hpv)
    subst names
    subst vals
    change f.vars.length ≤ cap at hc
    have hpos : 0 < cap := by omega
    have ha := hna.nonempty hpos
    have hb := hva.nonempty hpos
    constructor
    · intro k hk
      apply harrays pn (8 * cap) (Or.inl ha)
      change pn ≤ pn + 8 * i + k ∧ pn + 8 * i + k < pn + 8 * cap
      omega
    · intro k hk
      apply harrays pv (24 * cap) (Or.inr hb)
      change pv + 24 * i ≤ k ∧ k < pv + 24 * i + 24 at hk
      change pv ≤ k ∧ k < pv + 24 * cap
      omega
  · intro pn pv hpn _ i hi q hq k hk
    obtain ⟨⟨_, names, _⟩, _, hn, _, _, _, _, hnames⟩ := h.arrays
    have en : names = pn := Option.some.inj (hn.symm.trans hpn)
    subst names
    obtain ⟨q', hq', hs⟩ := hnames i hi
    have eq : q' = q := Option.some.inj (hq'.symm.trans hq)
    subst q'
    exact hshared _ (hs.immutable.bytes k hk)
  · intro _ pv _ hpv i hi
    exact (h.values pv hpv i hi).covered hshared

/-- The old signed-capacity consumer admits zero directly. Positive capacities
retain exactly its live values-array arithmetic argument. -/
theorem FrameOwned.capSigned {m : Mem} {phiF : Addr → Nat} {alloc : Allocations}
    {shared : Nat → Prop} {fa : Addr} {f : Vsa.While.Frame} {A : Arena} {exts : List Extent}
    (h : FrameOwned m phiF alloc shared fa f) (hl : Ledger A exts alloc)
    {cap : Nat} (hc : read32 m (phiF fa + 4) = some cap) (hi : A.hi ≤ 2^32) :
    cap < 2^31 := by
  obtain ⟨⟨cap', pn, pv⟩, hc', _, _, _, _, hv, _⟩ := h.arrays
  have he : cap' = cap := Option.some.inj (hc'.symm.trans hc)
  subst cap'
  rcases hv with ⟨hz, _⟩ | ⟨_, ha⟩
  · change cap = 0 at hz
    omega
  · have hb := (hl.arena.1 _ (hl.live _ _ _ ha)).2
    change A.lo ≤ pv ∧ pv + 24 * cap ≤ A.hi at hb
    omega

structure StoreOwned (m : Mem) (phiF phiC : Addr → Nat) (alloc : Allocations)
    (shared : Nat → Prop) (s : Store) : Prop where
  frames : ∀ fa, (h : fa < s.frames.size) → FrameOwned m phiF alloc shared fa s.frames[fa]
  closures : ∀ ca, ca < s.closures.size → Allocated alloc (.closure ca) (phiC ca) 16
  valueClosures : StoreClosuresBounded s
  capturedEnvs : ∀ ca, (h : ca < s.closures.size) → s.closures[ca].env < s.frames.size
  closureAsts : ∀ ca, (h : ca < s.closures.size) → ∀ q,
    read64 m (phiC ca) = some q →
    ∀ k, ExprFp m q (.fn s.closures[ca].name s.closures[ca].params
      s.closures[ca].body) k → shared k

/-- Direct adapter for existing closure append/set transport consumers. -/
theorem StoreOwned.closureFootprint {m : Mem} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {shared P : Nat → Prop} {s : Store}
    (h : StoreOwned m phiF phiC alloc shared s) {ca : Addr} (hc : ca < s.closures.size)
    (hheader : ∀ k, ExtentByte (phiC ca, 16) k → P k)
    (hshared : ∀ k, shared k → P k) :
    ClosureFootprintCovered m phiC ca s.closures[ca] P := by
  refine ⟨hheader, ?_⟩
  intro q hq k hk
  exact hshared _ (h.closureAsts ca hc q hq k hk)

/-- Shared payloads avoid any subwindow of a mutable allocation. Instantiate
`P` with AppendOutside/SetOutside to supply the existing payload consumers. -/
theorem Immutable.outsideWindow {alloc : Allocations} {shared readable writes : Nat → Prop}
    (h : Immutable alloc shared readable writes) {role : Role} {p n lo size : Nat}
    (hm : Role.mutable role) (ha : Allocated alloc role p n)
    (hsub : ∀ k, lo ≤ k ∧ k < lo + size → ExtentByte (p, n) k) :
    ∀ k, shared k → k < lo ∨ lo + size ≤ k := by
  intro k hk
  have hn := h.outsideMutable role p n hm ha k hk
  have : ¬ (lo ≤ k ∧ k < lo + size) := fun hw => hn (hsub k hw)
  omega

/-- Canonical env_new needs only its allocated record and initialized reads.
No zero-sized name/value extent is requested. -/
theorem FrameOwned.empty {m : Mem} {phiF : Addr → Nat} {alloc : Allocations}
    {shared : Nat → Prop} {fa : Addr} {f : Vsa.While.Frame}
    (hr : Allocated alloc (.frame fa) (phiF fa) 32) (hf : f.vars = [])
    (hc : read32 m (phiF fa + 4) = some 0)
    (hn : read64 m (phiF fa + 8) = some 0)
    (hv : read64 m (phiF fa + 16) = some 0) :
    FrameOwned m phiF alloc shared fa f := by
  refine ⟨hr, ⟨⟨0, 0, 0⟩, hc, hn, hv, ?_, ArrayOwned.empty, ArrayOwned.empty, ?_⟩, ?_⟩
  · simp only [hf, List.length_nil, Nat.le_refl]
  · intro i hi
    simp only [hf, List.length_nil] at hi
    omega
  · intro _ _ i hi
    simp only [hf, List.length_nil] at hi
    omega

theorem SharedCString.transport {m m' : Mem} {shared : Nat → Prop} {p : Nat} {s : String}
    (h : SharedCString m shared p s) (ha : AgreeP shared m m') :
    SharedCString m' shared p s :=
  ⟨cstring_agreeP ha h.repr h.bytes, h.bytes⟩

/-- Shared bytes avoid an occupied slot inside a mutable values allocation. -/
theorem FrameOwned.sharedOutsideSet {m : Mem} {phiF : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {fa : Addr} {f : Vsa.While.Frame}
    (h : FrameOwned m phiF alloc shared fa f)
    (hm : Immutable alloc shared readable writes)
    {hit vals : Nat} (hi : hit < f.vars.length)
    (hv : read64 m (phiF fa + 16) = some vals) :
    ∀ k, shared k → SetOutside (vals + 24 * hit) k := by
  obtain ⟨⟨cap, _, pv⟩, _, _, hpv, hc, _, hva, _⟩ := h.arrays
  have he : pv = vals := Option.some.inj (hpv.symm.trans hv)
  subst pv
  change f.vars.length ≤ cap at hc
  have ha := hva.nonempty (by omega : 0 < cap)
  exact hm.outsideWindow (role := .values fa) (by trivial) ha (by
    intro k hk
    change vals ≤ k ∧ k < vals + 24 * cap
    omega)

/-- No execution hypothesis is needed to discharge the existing set payload
footprint: the destination is a subwindow of the target's mutable values. -/
theorem FrameOwned.payloadOutsideSet {m : Mem} {phiF : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {fa : Addr} {f : Vsa.While.Frame}
    (h : FrameOwned m phiF alloc shared fa f)
    (hm : Immutable alloc shared readable writes)
    {hit vals : Nat} (hi : hit < f.vars.length)
    (hv : read64 m (phiF fa + 16) = some vals) {a : Nat} {v : Value}
    (hsrc : ValueOwned m shared a v) :
    ValuePayloadCovered (SetOutside (vals + 24 * hit)) m a v :=
  hsrc.covered (h.sharedOutsideSet hm hi hv)

/-- The three in-capacity append stores are all inside mutable allocations. -/
theorem FrameOwned.payloadOutsideAppend {m : Mem} {phiF : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {fa : Addr} {f : Vsa.While.Frame}
    (h : FrameOwned m phiF alloc shared fa f)
    (hm : Immutable alloc shared readable writes)
    {cap names vals : Nat} (hc : read32 m (phiF fa + 4) = some cap)
    (hn : read64 m (phiF fa + 8) = some names)
    (hv : read64 m (phiF fa + 16) = some vals) (hcap : f.vars.length < cap)
    {a : Nat} {v : Value} (hsrc : ValueOwned m shared a v) :
    ValuePayloadCovered (AppendOutside (phiF fa) names vals f.vars.length) m a v := by
  obtain ⟨⟨cap', pn, pv⟩, hcap', hpn, hpv, _, hna, hva, _⟩ := h.arrays
  have ec : cap' = cap := Option.some.inj (hcap'.symm.trans hc)
  have en : pn = names := Option.some.inj (hpn.symm.trans hn)
  have ev : pv = vals := Option.some.inj (hpv.symm.trans hv)
  subst cap'
  subst pn
  subst pv
  have hnames := hna.nonempty (by omega : 0 < cap)
  have hvals := hva.nonempty (by omega : 0 < cap)
  have outNames := hm.outsideWindow (role := .names fa) (by trivial) hnames
    (lo := names + 8 * f.vars.length) (size := 8) (by
      intro k hk
      change names ≤ k ∧ k < names + 8 * cap
      omega)
  have outVals := hm.outsideWindow (role := .values fa) (by trivial) hvals
    (lo := vals + 24 * f.vars.length) (size := 24) (by
      intro k hk
      change vals ≤ k ∧ k < vals + 24 * cap
      omega)
  have outCount := hm.outsideWindow (role := .frame fa) (by trivial) h.record
    (lo := phiF fa) (size := 4) (by
      intro k hk
      change phiF fa ≤ k ∧ k < phiF fa + 32
      omega)
  exact hsrc.covered (fun k hk => ⟨outNames k hk, outVals k hk, outCount k hk⟩)

#print axioms FrameOwned.empty
#print axioms SharedCString.transport
#print axioms FrameOwned.sharedOutsideSet
#print axioms FrameOwned.payloadOutsideSet
#print axioms FrameOwned.payloadOutsideAppend
#print axioms ArrayOwned.nonempty
#print axioms ArrayOwned.empty
#print axioms ValueOwned.covered
#print axioms FrameOwned.footprint
#print axioms FrameOwned.capSigned
#print axioms StoreOwned.closureFootprint
#print axioms Immutable.outsideWindow

end Vsa.Sim.RuntimeOwnership
