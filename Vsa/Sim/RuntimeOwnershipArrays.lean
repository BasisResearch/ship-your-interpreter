import Vsa.Sim.RuntimeOwnershipTransport
import Vsa.Sim.RuntimeOwnershipRealloc
import Vsa.Sim.RuntimeOwnershipSeparation
import Vsa.Sim.RuntimeOwnershipCopy

/-!
# `RuntimeOwnershipArrays` — one frame's backing arrays replaced

`env_define`'s grow path (and the empty frame's first allocation) replaces the
target frame's `names`/`vals` arrays through `realloc`: the new extents are
fresh, the old slots are copied, every other allocation and every shared byte
is untouched.  This file lands the ownership and representation algebra of
that replacement, once, over the array-owned ledger (`ArrayOwned` admits the
empty `NULL` arrays of a fresh frame):

* `Ledger.replaceArray` / `Immutable.replaceArray` / `Reserved.replaceArray`
  — the ledger after one array role is replaced (grow or first allocation);
* `StoreOwned.replaceArrays` / `HeapOwned.replaceArrays` — ownership at the
  memory holding the replaced arrays;
* `frameRepr_replaceArrays` / `storeRepr_replaceArrays` — the semantic store
  is unchanged, represented with the new arrays.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- `(0, 0)` is never a live extent. -/
theorem heapArena_erase_zero {A : Arena} {exts : List Extent} (h : HeapArena A exts) :
    exts.erase (0, 0) = exts := by
  apply List.erase_of_not_mem
  intro hm
  have := (h.1 _ hm).1
  simp at this

/-- A byte-window copy stated through pointwise agreement with present bytes. -/
theorem copy_of_agree {m m' : Mem} {src dst n : Nat}
    (hag : ∀ k, k < n → m'[dst + k]? = m[src + k]?)
    (hpres : ∀ k, k < n → ∃ b, m[src + k]? = some b) :
    ∀ k, k < n → m'[dst + k]? = some ((m[src + k]?).getD 0) := by
  intro k hk
  obtain ⟨b, hb⟩ := hpres k hk
  rw [hag k hk, hb]
  rfl

/-- Every byte of a successful little-endian read is present. -/
theorem readLE_present {m : Mem} : ∀ (n a x : Nat), readLE m a n = some x →
    ∀ k, k < n → ∃ b, m[a + k]? = some b := by
  intro n
  induction n with
  | zero => intro a x _ k hk; omega
  | succ n ih =>
    intro a x hx k hk
    simp only [readLE, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
    obtain ⟨b, hb, rest, hrest, _⟩ := hx
    rcases Nat.eq_zero_or_pos k with hz | hpos
    · subst hz; exact ⟨b, by simpa using hb⟩
    · obtain ⟨b', hb'⟩ := ih (a + 1) rest hrest (k - 1) (by omega)
      exact ⟨b', by rw [show a + k = a + 1 + (k - 1) by omega]; exact hb'⟩

/-- A little-endian read through a byte-wise window agreement between two
addresses (no presence assumed: absent bytes agree as absent). -/
theorem readLE_shift {m m' : Mem} : ∀ (n a b : Nat),
    (∀ k, k < n → m'[b + k]? = m[a + k]?) → readLE m' b n = readLE m a n := by
  intro n
  induction n with
  | zero => intro a b _; rfl
  | succ n ih =>
    intro a b hag
    have hhead : m'[b]? = m[a]? := by simpa using hag 0 (Nat.succ_pos n)
    have htail : readLE m' (b + 1) n = readLE m (a + 1) n := by
      apply ih
      intro k hk
      have := hag (k + 1) (by omega)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    simp only [readLE, hhead, htail]

theorem read64_shift {m m' : Mem} {a b : Nat}
    (hag : ∀ k, k < 8 → m'[b + k]? = m[a + k]?) : read64 m' b = read64 m a :=
  readLE_shift 8 a b hag

theorem read32_shift {m m' : Mem} {a b : Nat}
    (hag : ∀ k, k < 4 → m'[b + k]? = m[a + k]?) : read32 m' b = read32 m a :=
  readLE_shift 4 a b hag

/-- A represented value moved by a byte-wise agreement of its 24-byte slot,
with its indirect payload untouched. -/
theorem valueRepr_shift {m m' : Mem} {N : NativeAddrs} {φc : Addr → Nat}
    {src dst : Nat} {v : Value}
    (hag : ∀ k, k < 24 → m'[dst + k]? = m[src + k]?)
    (hpay : ValuePayloadCovered (fun a => m[a]? = m'[a]?) m src v)
    (hv : ValueRepr m N φc src v) : ValueRepr m' N φc dst v := by
  have h32 : ∀ off, off + 4 ≤ 24 → read32 m' (dst + off) = read32 m (src + off) := by
    intro off hoff
    apply read32_shift
    intro k hk
    rw [show dst + off + k = dst + (off + k) by omega, show src + off + k = src + (off + k) by omega]
    exact hag (off + k) (by omega)
  have h64 : ∀ off, off + 8 ≤ 24 → read64 m' (dst + off) = read64 m (src + off) := by
    intro off hoff
    apply read64_shift
    intro k hk
    rw [show dst + off + k = dst + (off + k) by omega, show src + off + k = src + (off + k) by omega]
    exact hag (off + k) (by omega)
  have h32z : read32 m' dst = read32 m src := by
    simpa only [Nat.add_zero] using h32 0 (by omega)
  have hI64 : ∀ off, off + 8 ≤ 24 → readI64 m' (dst + off) = readI64 m (src + off) := by
    intro off hoff
    simp only [readI64, h64 off hoff]
  cases v with
  | null =>
    simp only [ValueRepr] at hv ⊢
    rw [h32z]; exact hv
  | bool b =>
    simp only [ValueRepr] at hv ⊢
    exact ⟨by rw [h32z]; exact hv.1, by rw [h32 8 (by omega)]; exact hv.2⟩
  | int n =>
    simp only [ValueRepr] at hv ⊢
    exact ⟨by rw [h32z]; exact hv.1, by rw [hI64 8 (by omega)]; exact hv.2⟩
  | str s =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨hk, p, hp, hpne, hcstr⟩ := hv
    exact ⟨by rw [h32z]; exact hk, p, by rw [h64 8 (by omega)]; exact hp, hpne,
      cstring_agreeP (P := fun a => m[a]? = m'[a]?) (fun a ha => ha) hcstr
        (fun k hk => hpay p hp k hk)⟩
  | closure ca =>
    simp only [ValueRepr] at hv ⊢
    exact ⟨by rw [h32z]; exact hv.1, by rw [h64 8 (by omega)]; exact hv.2.1, hv.2.2⟩
  | native f =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨hk, ⟨p, hp, hcstr⟩, h16⟩ := hv
    exact ⟨by rw [h32z]; exact hk,
      ⟨p, by rw [h64 8 (by omega)]; exact hp,
        cstring_agreeP (P := fun a => m[a]? = m'[a]?) (fun a ha => ha) hcstr
          (fun k hk => hpay p hp k hk)⟩,
      by rw [h64 16 (by omega)]; exact h16⟩

/-- Owned payload ownership moved with its slot. -/
theorem ValueOwned.shift {m m' : Mem} {shared : Nat → Prop} {src dst : Nat} {v : Value}
    (h : ValueOwned m shared src v)
    (hag : ∀ k, k < 24 → m'[dst + k]? = m[src + k]?)
    (ha : AgreeP shared m m') : ValueOwned m' shared dst v := by
  have h64 : read64 m' (dst + 8) = read64 m (src + 8) := by
    apply read64_shift
    intro k hk
    rw [show dst + 8 + k = dst + (8 + k) by omega, show src + 8 + k = src + (8 + k) by omega]
    exact hag (8 + k) (by omega)
  cases v <;> simp only [ValueOwned] at h ⊢
  all_goals first
    | exact True.intro
    | (obtain ⟨p, hp, hs⟩ := h
       exact ⟨p, by rw [h64]; exact hp, hs.transport ha⟩)

/-- The ledger after replacing one owned array role (empty or live). -/
theorem Ledger.replaceArray {A : Arena} {exts : List Extent} {alloc : Allocations}
    (h : Ledger A exts alloc) {role : Role} {pOld width cap pNew nNew : Nat}
    (hold : ArrayOwned alloc role pOld width cap) (hpos : 0 < nNew)
    (ha : A.contains pNew nNew)
    (hf : ∀ e ∈ exts, e ≠ (pOld, width * cap) → ExtDisjoint (pNew, nNew) e) :
    Ledger A ((pNew, nNew) :: exts.erase (pOld, width * cap)) (alloc.insert role pNew nNew) := by
  rcases hold with ⟨hz, hp⟩ | ⟨_, hal⟩
  · subst hz; subst hp
    rw [Nat.mul_zero, heapArena_erase_zero h.arena]
    apply h.insert hpos ha
    intro e he
    apply hf e he
    intro heq
    subst heq
    have := (h.arena.1 _ he).1
    simp at this
  · exact h.replace hal hpos ha hf

/-- Shared bytes stay outside every mutable allocation after the replacement. -/
theorem Immutable.replaceArray {A : Arena} {exts : List Extent} {alloc : Allocations}
    {shared readable writes : Nat → Prop}
    (h : Immutable alloc shared readable writes) (hl : Ledger A exts alloc)
    (hr : Reserved A exts shared) {role : Role} {pOld width cap pNew nNew : Nat}
    (hm : Role.mutable role) (hold : ArrayOwned alloc role pOld width cap)
    (ha : A.contains pNew nNew)
    (hf : ∀ e ∈ exts, e ≠ (pOld, width * cap) → ExtDisjoint (pNew, nNew) e) :
    Immutable (alloc.insert role pNew nNew) shared readable writes := by
  rcases hold with ⟨hz, hp⟩ | ⟨_, hal⟩
  · subst hz; subst hp
    apply h.insert hr ha
    intro e he
    apply hf e he
    intro heq
    subst heq
    have := (hl.arena.1 _ he).1
    simp at this
  · exact h.replace hl hr hm hal ha hf

/-- Reserved bytes survive the replacement through the surviving ledger. -/
theorem Reserved.replaceArray {A : Arena} {exts : List Extent} {alloc : Allocations}
    {shared readable writes : Nat → Prop}
    (h : Reserved A exts shared) (hl : Ledger A exts alloc)
    (hi : Immutable alloc shared readable writes) {role : Role}
    {pOld width cap pNew nNew : Nat}
    (hm : Role.mutable role) (hold : ArrayOwned alloc role pOld width cap) :
    Reserved A ((pNew, nNew) :: exts.erase (pOld, width * cap)) shared := by
  rcases hold with ⟨hz, hp⟩ | ⟨_, hal⟩
  · subst hz; subst hp
    rw [Nat.mul_zero, heapArena_erase_zero hl.arena]
    exact h.mono (fun e he => List.mem_cons_of_mem _ he)
  · exact h.replace hi hm hal

/-- An array role that is not the replaced one keeps its ownership. -/
theorem ArrayOwned.congr {alloc alloc' : Allocations} {role : Role} {p width cap : Nat}
    (h : ArrayOwned alloc role p width cap) (he : alloc' role = alloc role) :
    ArrayOwned alloc' role p width cap := by
  rcases h with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h2, by show alloc' role = _; rw [he]; exact h3⟩

/-- A frame's ownership is unchanged when its own roles are unchanged. -/
theorem FrameOwned.congrAlloc {m : Mem} {phiF : Addr → Nat} {alloc alloc' : Allocations}
    {shared : Nat → Prop} {fa : Addr} {f : Vsa.While.Frame}
    (h : FrameOwned m phiF alloc shared fa f)
    (hfr : alloc' (.frame fa) = alloc (.frame fa))
    (hn : alloc' (.names fa) = alloc (.names fa))
    (hv : alloc' (.values fa) = alloc (.values fa))
    (hb : ∀ i, alloc' (.binding fa i) = alloc (.binding fa i)) :
    FrameOwned m phiF alloc' shared fa f := by
  obtain ⟨a, harr⟩ := h.arrays
  refine ⟨?_, ⟨a, harr.capRead, harr.namesRead, harr.valuesRead, harr.bound,
    harr.names.congr hn, harr.values.congr hv, ?_⟩, h.values⟩
  · show alloc' (.frame fa) = _
    rw [hfr]
    exact h.record
  · intro i hi
    obtain ⟨q, hq, key⟩ := harr.keys i hi
    refine ⟨q, hq, ⟨?_, key.immutable⟩⟩
    show alloc' (.binding fa i) = _
    rw [hb]
    exact key.allocated

/-- **Ownership after replacing one frame's arrays.**  The other roles are
unchanged and covered by the agreement footprint `P` (as are the shared
bytes); the target's new arrays are owned by `alloc'`, its record reads the
new state, and the old slots are copied. -/
theorem StoreOwned.replaceArrays {m m' : Mem} {phiF phiC : Addr → Nat}
    {alloc alloc' : Allocations} {shared P : Nat → Prop} {s : Store} {fa : Addr}
    {a a' : ArrayState}
    (h : StoreOwned m phiF phiC alloc shared s) (hfa : fa < s.frames.size)
    (harr : FrameArraysOwned m phiF alloc shared fa s.frames[fa] a)
    (halloc : ∀ r, r ≠ .names fa → r ≠ .values fa → alloc' r = alloc r)
    (hnames' : ArrayOwned alloc' (.names fa) a'.names 8 a'.cap)
    (hvalues' : ArrayOwned alloc' (.values fa) a'.values 24 a'.cap)
    (hcap' : read32 m' (phiF fa + 4) = some a'.cap)
    (hnamesRead' : read64 m' (phiF fa + 8) = some a'.names)
    (hvaluesRead' : read64 m' (phiF fa + 16) = some a'.values)
    (hbound' : s.frames[fa].vars.length ≤ a'.cap)
    (hag : AgreeP P m m')
    (hP : ∀ role p n, role ≠ .frame fa → role ≠ .names fa → role ≠ .values fa →
      Allocated alloc role p n → ∀ k, ExtentByte (p, n) k → P k)
    (hs : ∀ k, shared k → P k)
    (hkeys : ∀ i, i < s.frames[fa].vars.length → ∀ k, k < 8 →
      m'[a'.names + 8 * i + k]? = m[a.names + 8 * i + k]?)
    (hvals : ∀ i, i < s.frames[fa].vars.length → ∀ k, k < 24 →
      m'[a'.values + 24 * i + k]? = m[a.values + 24 * i + k]?) :
    StoreOwned m' phiF phiC alloc' shared s := by
  have hsag : AgreeP shared m m' := fun k hk => hag k (hs k hk)
  refine ⟨?_, ?_, h.valueClosures, h.capturedEnvs, ?_⟩
  · intro fb hfb
    by_cases hne : fb = fa
    · subst hne
      refine ⟨?_, ⟨a', hcap', hnamesRead', hvaluesRead', hbound', hnames', hvalues', ?_⟩, ?_⟩
      · show alloc' (.frame fb) = _
        rw [halloc (.frame fb) nofun nofun]
        exact (h.frames fb hfb).record
      · intro i hi
        obtain ⟨q, hq, key⟩ := harr.keys i hi
        refine ⟨q, ?_, ⟨?_, key.immutable.transport hsag⟩⟩
        · rw [read64_shift (hkeys i hi)]; exact hq
        · show alloc' (.binding fb i) = _
          rw [halloc (.binding fb i) nofun nofun]
          exact key.allocated
      · intro pv hpv i hi
        have he : pv = a'.values := Option.some.inj (hpv.symm.trans hvaluesRead')
        subst he
        exact ((h.frames fb hfb).values a.values harr.valuesRead i hi).shift
          (hvals i hi) hsag
    · have hfp : FrameFootprintCovered m phiF fb s.frames[fb] P := by
        apply (h.frames fb hfb).footprint
        · exact hP (.frame fb) _ _ (fun e => hne (Role.frame.inj e)) nofun nofun
            (h.frames fb hfb).record
        · intro p n hp
          rcases hp with hn | hv
          · exact hP (.names fb) _ _ nofun (fun e => hne (Role.names.inj e)) nofun hn
          · exact hP (.values fb) _ _ nofun nofun (fun e => hne (Role.values.inj e)) hv
        · exact hs
      exact ((h.frames fb hfb).transport hag hfp hs).congrAlloc
        (halloc (.frame fb) nofun nofun) (halloc (.names fb) (fun e => hne (Role.names.inj e)) nofun)
        (halloc (.values fb) nofun (fun e => hne (Role.values.inj e)))
        (fun i => halloc (.binding fb i) nofun nofun)
  · intro ca hc
    show alloc' (.closure ca) = _
    rw [halloc (.closure ca) nofun nofun]
    exact h.closures ca hc
  · intro ca hc q hq k hk
    have heq : read64 m (phiC ca) = read64 m' (phiC ca) := by
      simpa only [Nat.add_zero] using
        (extent_covers (hP (.closure ca) _ _ nofun nofun nofun (h.closures ca hc))
          (by decide : 0 + 8 ≤ 16)).read64_eq hag
    have hq0 := heq.trans hq
    exact h.closureAsts ca hc q hq0 k
      (hk.pullback hag (fun j hj => hs j (h.closureAsts ca hc q hq0 j hj)))

/-- The semantic frame represented with its replaced arrays: the old slots
were copied byte-for-byte, the name strings and value payloads are untouched
(covered by `P`), and the record words the replacement did not write agree. -/
theorem frameRepr_replaceArrays {m m' : Mem} {N : NativeAddrs} {phiF phiC : Addr → Nat}
    {e : Nat} {f : Vsa.While.Frame} {P : Nat → Prop} {pn pv cap' pn' pv' : Nat}
    (hf : FrameRepr m N phiF phiC e f)
    (hpn : read64 m (e + 8) = some pn) (hpv : read64 m (e + 16) = some pv)
    (hcount' : read32 m' e = some f.vars.length)
    (hcap' : read32 m' (e + 4) = some cap') (hle : f.vars.length ≤ cap')
    (hpn' : read64 m' (e + 8) = some pn') (hpv' : read64 m' (e + 16) = some pv')
    (hparent : read64 m' (e + 24) = read64 m (e + 24))
    (hag : AgreeP P m m')
    (hnamesP : ∀ i, (hi : i < f.vars.length) → ∀ q, read64 m (pn + 8 * i) = some q →
      ∀ k, k ≤ (f.vars[i].1).length → P (q + k))
    (hpay : ∀ i, (hi : i < f.vars.length) →
      ValuePayloadCovered P m (pv + 24 * i) f.vars[i].2)
    (hkeys : ∀ i, i < f.vars.length → ∀ k, k < 8 →
      m'[pn' + 8 * i + k]? = m[pn + 8 * i + k]?)
    (hvals : ∀ i, i < f.vars.length → ∀ k, k < 24 →
      m'[pv' + 24 * i + k]? = m[pv + 24 * i + k]?) :
    FrameRepr m' N phiF phiC e f := by
  obtain ⟨_, _, ⟨pn0, pv0, hpn0, hpv0, hslots⟩, hpar⟩ := hf
  have en : pn0 = pn := Option.some.inj (hpn0.symm.trans hpn)
  have ev : pv0 = pv := Option.some.inj (hpv0.symm.trans hpv)
  subst en; subst ev
  refine ⟨hcount', ⟨cap', hcap', hle⟩, ⟨pn', pv', hpn', hpv', ?_⟩, ?_⟩
  · intro i hi
    obtain ⟨⟨q, hq, hqs⟩, hv⟩ := hslots i hi
    refine ⟨⟨q, ?_, cstring_agreeP hag hqs (hnamesP i hi q hq)⟩, ?_⟩
    · rw [read64_shift (hkeys i hi)]; exact hq
    · apply valueRepr_shift (hvals i hi) _ hv
      cases hvv : f.vars[i].2 with
      | str s =>
        intro p hp k hk
        have := hpay i hi
        rw [hvv] at this
        exact hag _ (this p hp k hk)
      | native g =>
        intro p hp k hk
        have := hpay i hi
        rw [hvv] at this
        exact hag _ (this p hp k hk)
      | null | bool | int | closure => trivial
  · cases hp : f.parent with
    | none =>
      simp only [hp] at hpar ⊢
      rw [hparent]; exact hpar
    | some pa =>
      simp only [hp] at hpar ⊢
      exact ⟨by rw [hparent]; exact hpar.1, hpar.2⟩

/-- The whole represented store after replacing one frame's arrays: the target
by `frameRepr_replaceArrays`, every other frame and closure through its
ownership footprint. -/
theorem storeRepr_replaceArrays {m m' : Mem} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {shared P : Nat → Prop}
    {s : Store} {fa : Addr} {pn pv cap' pn' pv' : Nat}
    (hr : StoreRepr m N A phiF phiC s) (h : StoreOwned m phiF phiC alloc shared s)
    (hfa : fa < s.frames.size)
    (hpn : read64 m (phiF fa + 8) = some pn) (hpv : read64 m (phiF fa + 16) = some pv)
    (hcount' : read32 m' (phiF fa) = some s.frames[fa].vars.length)
    (hcap' : read32 m' (phiF fa + 4) = some cap') (hle : s.frames[fa].vars.length ≤ cap')
    (hpn' : read64 m' (phiF fa + 8) = some pn') (hpv' : read64 m' (phiF fa + 16) = some pv')
    (hparent : read64 m' (phiF fa + 24) = read64 m (phiF fa + 24))
    (hag : AgreeP P m m')
    (hP : ∀ role p n, role ≠ .frame fa → role ≠ .names fa → role ≠ .values fa →
      Allocated alloc role p n → ∀ k, ExtentByte (p, n) k → P k)
    (hs : ∀ k, shared k → P k)
    (hkeys : ∀ i, i < s.frames[fa].vars.length → ∀ k, k < 8 →
      m'[pn' + 8 * i + k]? = m[pn + 8 * i + k]?)
    (hvals : ∀ i, i < s.frames[fa].vars.length → ∀ k, k < 24 →
      m'[pv' + 24 * i + k]? = m[pv + 24 * i + k]?) :
    StoreRepr m' N A phiF phiC s := by
  have hsag : AgreeP shared m m' := fun k hk => hag k (hs k hk)
  refine ⟨?_, ?_, hr.φf_inj, hr.φc_inj, hr.frames_arena, hr.closures_arena⟩
  · intro fb hfb
    by_cases hne : fb = fa
    · subst hne
      have hfo := h.frames fb hfb
      obtain ⟨a, harr⟩ := hfo.arrays
      have en : a.names = pn := Option.some.inj (harr.namesRead.symm.trans hpn)
      have ev : a.values = pv := Option.some.inj (harr.valuesRead.symm.trans hpv)
      apply frameRepr_replaceArrays (hr.frames fb hfb) hpn hpv hcount' hcap' hle hpn' hpv'
        hparent hag _ _ hkeys hvals
      · intro i hi q hq k hk
        obtain ⟨q', hq', key⟩ := harr.keys i hi
        rw [en] at hq'
        have := Option.some.inj (hq'.symm.trans hq)
        subst this
        exact hs _ (key.immutable.bytes k hk)
      · intro i hi
        have hv := hfo.values pv (by rw [← ev]; exact harr.valuesRead) i hi
        exact hv.covered hs
    · have hfp : FrameFootprintCovered m phiF fb s.frames[fb] P := by
        apply (h.frames fb hfb).footprint
        · exact hP (.frame fb) _ _ (fun e => hne (Role.frame.inj e)) nofun nofun
            (h.frames fb hfb).record
        · intro p n hp
          rcases hp with hn | hv
          · exact hP (.names fb) _ _ nofun (fun e => hne (Role.names.inj e)) nofun hn
          · exact hP (.values fb) _ _ nofun nofun (fun e => hne (Role.values.inj e)) hv
        · exact hs
      exact frameRepr_agreeP hag hfp.header hfp.slots hfp.names hfp.values (hr.frames fb hfb)
  · intro ca hc
    have hcov := hP (.closure ca) _ _ nofun nofun nofun (h.closures ca hc)
    apply closureRepr_agreeP hag
    · intro k hk
      exact hcov k hk
    · intro q hq hexpr
      apply exprRepr_agreeP hag
      · intro addr haddr
        exact hs addr (h.closureAsts ca hc q hq addr haddr)
      · exact hexpr
    · exact hr.closures ca hc

#print axioms heapArena_erase_zero
#print axioms copy_of_agree
#print axioms readLE_present
#print axioms readLE_shift
#print axioms valueRepr_shift
#print axioms ValueOwned.shift
#print axioms Ledger.replaceArray
#print axioms Immutable.replaceArray
#print axioms Reserved.replaceArray
#print axioms ArrayOwned.congr
#print axioms FrameOwned.congrAlloc
#print axioms StoreOwned.replaceArrays
#print axioms frameRepr_replaceArrays
#print axioms storeRepr_replaceArrays

end Vsa.Sim.RuntimeOwnership
