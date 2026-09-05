import Vsa.Sim.EnvCallBridge
import Vsa.Sim.ReprSurvival
import Vsa.Sim.HeapOps

/-!
# Exact footprint certificate for `env_set`

The machine overwrites one 24-byte `Value` slot.  `StoreRepr` does not imply
that this slot is disjoint from the objects reached by the other frames and
closures.  This file exposes that missing allocator/layout fact explicitly,
in the exact footprint shape consumed by `frameRepr_agreeP` and
`closureRepr_agreeP`.
-/

open Vsa
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While

namespace Vsa.Sim

/-- `Nodup` names determine their list index. -/
theorem index_unique_of_names_nodup
    {vars : List (String × Value)} (h : (vars.map Prod.fst).Nodup) :
    ∀ i j, (hi : i < vars.length) → (hj : j < vars.length) →
      vars[i].1 = vars[j].1 → i = j := by
  induction vars with
  | nil => intro i j hi; simp at hi
  | cons p rest ih =>
    have hhead : p.1 ∉ rest.map Prod.fst := (List.nodup_cons.mp h).1
    have htail : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp h).2
    intro i j hi hj heq
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        have hj' : j < rest.length := by simpa using hj
        exact (hhead (by rw [heq]; exact List.mem_map_of_mem (List.getElem_mem hj'))).elim
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        have hi' : i < rest.length := by simpa using hi
        exact (hhead (by rw [← heq]; exact List.mem_map_of_mem (List.getElem_mem hi'))).elim
      | succ j =>
        simp only [List.getElem_cons_succ] at heq
        exact congrArg Nat.succ (ih htail i j (by simpa using hi) (by simpa using hj) heq)

/-- The list-level invariant used by the semantic store implies the index-level
uniqueness premise used by `frameRepr_after_update`. -/
theorem frameUnique_of_frameNamesUnique {f : Vsa.While.Frame}
    (h : FrameNamesUnique f.vars) : FrameUnique f :=
  index_unique_of_names_nodup h

/-- Addresses outside the single 24-byte value slot changed by `env_set`. -/
def OutsideSetSlot (slot : Nat) (a : Nat) : Prop :=
  a < slot ∨ slot + 24 ≤ a

/-- Every byte read by one unchanged frame lies outside the updated slot. -/
structure FrameOutsideSetSlot
    (m : Mem) (N : NativeAddrs) (φf φc : Addr → Nat)
    (e slot : Nat) (f : Vsa.While.Frame) : Prop where
  header : ∀ k, envHeader e k → OutsideSetSlot slot k
  slots : ∀ pn pv, read64 m (e + 8) = some pn → read64 m (e + 16) = some pv →
    ∀ i, i < f.vars.length →
      (∀ k, k < 8 → OutsideSetSlot slot (pn + 8 * i + k)) ∧
      (∀ k, valHeader (pv + 24 * i) k → OutsideSetSlot slot k)
  names : ∀ pn pv, read64 m (e + 8) = some pn → read64 m (e + 16) = some pv →
    ∀ i, (hi : i < f.vars.length) → ∀ qn,
      read64 m (pn + 8 * i) = some qn →
      ∀ k, k ≤ (f.vars[i].1).length → OutsideSetSlot slot (qn + k)
  valueStrings : ∀ pn pv, read64 m (e + 8) = some pn →
    read64 m (e + 16) = some pv →
    ∀ i, (hi : i < f.vars.length) →
      ValuePayloadCovered (OutsideSetSlot slot) m
        (pv + 24 * i) f.vars[i].2

namespace FrameOutsideSetSlot

/-- An unchanged frame survives the single-slot write. -/
theorem survive
    {m m' : Mem} {N : NativeAddrs} {φf φc : Addr → Nat}
    {e slot : Nat} {f : Vsa.While.Frame}
    (h : FrameOutsideSetSlot m N φf φc e slot f)
    (hmem : AgreeP (OutsideSetSlot slot) m m')
    (hrepr : FrameRepr m N φf φc e f) :
    FrameRepr m' N φf φc e f :=
  frameRepr_agreeP hmem h.header h.slots h.names h.valueStrings hrepr

end FrameOutsideSetSlot

/-- Footprint of the target frame excluding its one overwritten value slot. -/
structure TargetFrameOutsideSetSlot
    (m : Mem) (N : NativeAddrs) (φf φc : Addr → Nat)
    (e slot : Nat) (f : Vsa.While.Frame) (hit : Nat) : Prop where
  header : ∀ k, envHeader e k → OutsideSetSlot slot k
  nameSlots : ∀ pn pv, read64 m (e + 8) = some pn → read64 m (e + 16) = some pv →
    ∀ i, i < f.vars.length → ∀ k, k < 8 →
      OutsideSetSlot slot (pn + 8 * i + k)
  names : ∀ pn pv, read64 m (e + 8) = some pn → read64 m (e + 16) = some pv →
    ∀ i, (hi : i < f.vars.length) → ∀ qn,
      read64 m (pn + 8 * i) = some qn →
      ∀ k, k ≤ (f.vars[i].1).length → OutsideSetSlot slot (qn + k)
  otherValueHeaders : ∀ pn pv, read64 m (e + 8) = some pn →
    read64 m (e + 16) = some pv → ∀ i, i < f.vars.length → i ≠ hit →
      ∀ k, valHeader (pv + 24 * i) k → OutsideSetSlot slot k
  otherValueStrings : ∀ pn pv, read64 m (e + 8) = some pn →
    read64 m (e + 16) = some pv → ∀ i, (hi : i < f.vars.length) → i ≠ hit →
      ValuePayloadCovered (OutsideSetSlot slot) m
        (pv + 24 * i) f.vars[i].2

namespace TargetFrameOutsideSetSlot

/-- Rebuild the target frame from its unchanged shell and the new value-slot
representation. -/
theorem rebuild
    {m m' : Mem} {N : NativeAddrs} {φf φc : Addr → Nat}
    {e slot : Nat} {f : Vsa.While.Frame} {x : String} {v : Value} {hit : Nat}
    (h : TargetFrameOutsideSetSlot m N φf φc e slot f hit)
    (hmem : AgreeP (OutsideSetSlot slot) m m')
    (hrepr : FrameRepr m N φf φc e f)
    (hhit : hit < f.vars.length) (hmatch : f.vars[hit].1 = x)
    (huniq : FrameNamesUnique f.vars)
    (hslot : ∀ pv, read64 m (e + 16) = some pv → slot = pv + 24 * hit)
    (hnew : ValueRepr m' N φc slot v) :
    FrameRepr m' N φf φc e
      { f with vars := f.vars.map (replaceBindingValue x v) } := by
  obtain ⟨hcount, ⟨cap, hcap, hcaple⟩, ⟨pn, pv, hpn, hpv, hbind⟩, hparent⟩ := hrepr
  have hslotEq := hslot pv hpv
  have hany : f.vars.any (fun p => p.1 == x) = true := by
    rw [List.any_eq_true]
    exact ⟨f.vars[hit], List.getElem_mem hhit, by simpa [hmatch]⟩
  have hfr : FrameRepr m' N φf φc e
      { f with vars :=
          if f.vars.any (fun p => p.1 == x) then
            f.vars.map fun p => if p.1 == x then (x, v) else p
          else f.vars ++ [(x, v)] } := by
    apply frameRepr_after_update m' N φf φc e f x v hit hhit hmatch
      (frameUnique_of_frameNamesUnique huniq)
    · rw [← read32_agreeP hmem (fun k hk => h.header _ ⟨by omega, by omega⟩)]
      exact hcount
    · refine ⟨cap, ?_, hcaple⟩
      rw [← read32_agreeP hmem (fun k hk => h.header _ ⟨by omega, by omega⟩)]
      exact hcap
    · rw [← read64_agreeP hmem (fun k hk => h.header _ ⟨by omega, by omega⟩)]
      exact hpn
    · rw [← read64_agreeP hmem (fun k hk => h.header _ ⟨by omega, by omega⟩)]
      exact hpv
    · intro i hi
      obtain ⟨⟨q, hq, hqstr⟩, _⟩ := hbind i hi
      refine ⟨q, ?_, ?_⟩
      · rw [← read64_agreeP hmem (h.nameSlots pn pv hpn hpv i hi)]
        exact hq
      · exact cstring_agreeP hmem hqstr (h.names pn pv hpn hpv i hi q hq)
    · rw [← hslotEq]
      exact hnew
    · intro i hi hne
      obtain ⟨_, hval⟩ := hbind i hi
      exact valueRepr_agreeP hmem (h.otherValueHeaders pn pv hpn hpv i hi hne)
        (h.otherValueStrings pn pv hpn hpv i hi hne) hval
    · cases hp : f.parent with
      | none =>
        simp only [hp] at hparent ⊢
        rw [← read64_agreeP hmem (fun k hk => h.header _ ⟨by omega, by omega⟩)]
        exact hparent
      | some pa =>
        simp only [hp] at hparent ⊢
        exact ⟨by
          rw [← read64_agreeP hmem (fun k hk => h.header _ ⟨by omega, by omega⟩)]
          exact hparent.1, hparent.2⟩
  rw [hany] at hfr
  exact hfr

end TargetFrameOutsideSetSlot

/-- Every byte read by one unchanged closure lies outside the updated slot.
The closure's AST representation is named separately because `StoreRepr`
does not bound AST storage inside the heap arena. -/
structure ClosureOutsideSetSlot
    (m m' : Mem) (φf : Addr → Nat) (p slot : Nat)
    (cd : ClosureData) : Prop where
  header : ∀ k, closHeader p k → OutsideSetSlot slot k
  expr : ∀ q, read64 m p = some q →
    ExprRepr m q (.fn cd.name cd.params cd.body) →
    ExprRepr m' q (.fn cd.name cd.params cd.body)

namespace ClosureOutsideSetSlot

/-- An unchanged closure survives the single-slot write. -/
theorem survive
    {m m' : Mem} {φf : Addr → Nat} {p slot : Nat} {cd : ClosureData}
    (h : ClosureOutsideSetSlot m m' φf p slot cd)
    (hmem : AgreeP (OutsideSetSlot slot) m m')
    (hrepr : ClosureRepr m φf p cd) : ClosureRepr m' φf p cd :=
  closureRepr_agreeP hmem h.header h.expr hrepr

end ClosureOutsideSetSlot

/-- Minimal whole-store separation premise for a one-slot update.  It covers
all non-target frames and every closure.  The target frame is reconstructed
separately from its unchanged shell and newly copied value slot. -/
structure StoreSetFootprint
    (m m' : Mem) (N : NativeAddrs) (φf φc : Addr → Nat)
    (store : Store) (target : Addr) (slot : Nat) : Prop where
  outside : AgreeP (OutsideSetSlot slot) m m'
  frames : ∀ fa, (hfa : fa < store.frames.size) → fa ≠ target →
    FrameOutsideSetSlot m N φf φc (φf fa) slot store.frames[fa]
  closures : ∀ ca, (hca : ca < store.closures.size) →
    ClosureOutsideSetSlot m m' φf (φc ca) slot store.closures[ca]

namespace StoreSetFootprint

/-- The global heap-separation invariant supplies the update-specific target
shell and all unchanged store footprints. -/
theorem of_heap_owned
    {m m' : Mem} {N : NativeAddrs} {φf φc : Addr → Nat}
    {exts : List Extent} {store : Store} {target : Addr}
    {hit vals slot : Nat}
    (ht : target < store.frames.size)
    (hhit : hit < store.frames[target].vars.length)
    (hvals : read64 m (φf target + 16) = some vals)
    (hslot : slot = vals + 24 * hit)
    (howned : StoreHeapOwned m φf φc exts store)
    (hag : AgreeP (OutsideSetSlot slot) m m') :
    StoreSetFootprint m m' N φf φc store target slot := by
  obtain ⟨htarget, hframes, hclosures⟩ :=
    howned.setSeparated target ht hit hhit vals hvals
  refine ⟨hag, ?_, ?_⟩
  · intro fa hfa hne
    have h := hframes fa hfa hne
    exact
      { header := by
          intro k hk
          simpa [OutsideSetSlot, SetOutside, hslot] using h.header k hk
        slots := by
          intro pn pv hpn hpv i hi
          simpa [OutsideSetSlot, SetOutside, hslot] using h.slots pn pv hpn hpv i hi
        names := by
          intro pn pv hpn hpv i hi q hq k hk
          simpa [OutsideSetSlot, SetOutside, hslot] using
            h.names pn pv hpn hpv i hi q hq k hk
        valueStrings := by
          intro pn pv hpn hpv i hi
          simpa [OutsideSetSlot, SetOutside, hslot] using h.values pn pv hpn hpv i hi }
  · intro ca hca
    have h := hclosures ca hca
    refine
      { header := by
          intro k hk
          simpa [OutsideSetSlot, SetOutside, hslot] using h.header k hk
        expr := ?_ }
    intro q hq hexpr
    apply exprRepr_agreeP hag
    · intro a ha
      simpa [OutsideSetSlot, SetOutside, hslot] using h.ast q hq a ha
    · exact hexpr

/-- The target shell certificate is the target component of the same global
separation invariant. -/
theorem target_of_heap_owned
    {m : Mem} {N : NativeAddrs} {φf φc : Addr → Nat}
    {exts : List Extent} {store : Store} {target : Addr}
    {hit vals slot : Nat}
    (ht : target < store.frames.size)
    (hhit : hit < store.frames[target].vars.length)
    (hvals : read64 m (φf target + 16) = some vals)
    (hslot : slot = vals + 24 * hit)
    (howned : StoreHeapOwned m φf φc exts store) :
    TargetFrameOutsideSetSlot m N φf φc (φf target) slot
      store.frames[target] hit := by
  have h := (howned.setSeparated target ht hit hhit vals hvals).1
  exact
    { header := by
        intro k hk
        simpa [OutsideSetSlot, SetOutside, hslot] using h.header k hk
      nameSlots := by
        intro pn pv hpn hpv i hi k hk
        simpa [OutsideSetSlot, SetOutside, hslot] using
          h.nameSlots pn pv hpn hpv i hi k hk
      names := by
        intro pn pv hpn hpv i hi q hq k hk
        simpa [OutsideSetSlot, SetOutside, hslot] using
          h.names pn pv hpn hpv i hi q hq k hk
      otherValueHeaders := by
        intro pn pv hpn hpv i hi hne k hk
        simpa [OutsideSetSlot, SetOutside, hslot] using
          h.otherValueHeaders pn pv hpn hpv i hi hne k hk
      otherValueStrings := by
        intro pn pv hpn hpv i hi hne
        simpa [OutsideSetSlot, SetOutside, hslot] using
          h.otherValues pn pv hpn hpv i hi hne }

end StoreSetFootprint

namespace StoreSetAdvance

/-- Reconstruct the exact post-store representation from:

* the pre-store representation;
* the one updated target-frame representation;
* byte agreement outside that slot; and
* the explicit footprint-separation certificate for all other objects.

This does not assume `StoreRepr` of the post memory. -/
theorem of_target_repr
    {m m' : Mem} {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat}
    {store store' : Store} {start : Addr} {x : String} {v : Value}
    {bridge : AssignStoreBridge store store' start x v}
    {target : Addr} {slot : Nat}
    (hpre : StoreRepr m N A φf φc store)
    (hfoot : StoreSetFootprint m m' N φf φc store target slot)
    (hsemantic : ∃ (frame : Vsa.While.Frame) (oldValue : Value)
        (beforeVars afterVars : List (String × Value)),
      store.frames[target]? = some frame ∧
      frame.vars = beforeVars ++ (x, oldValue) :: afterVars ∧
      frame.vars.map (replaceBindingValue x v) =
        beforeVars ++ (x, v) :: afterVars ∧
      store' = { store with frames := store.frames.modify target fun current =>
        { current with vars := current.vars.map (replaceBindingValue x v) } })
    (htarget : ∀ (frame : Vsa.While.Frame) (oldValue : Value)
        (beforeVars afterVars : List (String × Value)),
      store.frames[target]? = some frame →
      frame.vars = beforeVars ++ (x, oldValue) :: afterVars →
      frame.vars.map (replaceBindingValue x v) =
        beforeVars ++ (x, v) :: afterVars →
      FrameRepr m' N φf φc (φf target)
        { frame with vars := frame.vars.map (replaceBindingValue x v) }) :
    StoreSetAdvance N A φf φc store store' start x v bridge target m' := by
  obtain ⟨frame, oldValue, beforeVars, afterVars,
    hframe, hsplit, hupdate, hresult⟩ := hsemantic
  subst store'
  obtain ⟨htargetBound, htargetGet⟩ := Array.getElem?_eq_some_iff.mp hframe
  refine
    { target_update := ⟨frame, oldValue, beforeVars, afterVars,
        hframe, hsplit, hupdate, rfl⟩
      frames := ?_
      closures := ?_
      φf_inj := ?_
      φc_inj := ?_
      frames_arena := ?_
      closures_arena := ?_ }
  · intro fa hfa
    have hfaOld : fa < store.frames.size := by simpa using hfa
    rw [Array.getElem_modify]
    by_cases heq : target = fa
    · rw [if_pos heq]
      subst fa
      rw [htargetGet]
      exact htarget frame oldValue beforeVars afterVars hframe hsplit hupdate
    · rw [if_neg heq]
      exact (hfoot.frames fa hfaOld (Ne.symm heq)).survive hfoot.outside
        (hpre.frames fa hfaOld)
  · intro ca hca
    have hcaOld : ca < store.closures.size := by simpa using hca
    exact (hfoot.closures ca hcaOld).survive hfoot.outside
      (hpre.closures ca hcaOld)
  · intro p q hp hq heq
    exact hpre.φf_inj p q (by simpa using hp) (by simpa using hq) heq
  · intro p q hp hq heq
    exact hpre.φc_inj p q (by simpa using hp) (by simpa using hq) heq
  · intro fa hfa
    exact hpre.frames_arena fa (by simpa using hfa)
  · intro ca hca
    exact hpre.closures_arena ca (by simpa using hca)

end StoreSetAdvance

#print axioms FrameOutsideSetSlot.survive
#print axioms frameUnique_of_frameNamesUnique
#print axioms TargetFrameOutsideSetSlot.rebuild
#print axioms ClosureOutsideSetSlot.survive
#print axioms StoreSetAdvance.of_target_repr

end Vsa.Sim
