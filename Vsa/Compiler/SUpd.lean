import Vsa.Compiler.SRel

/-!
# Updates of the store relation

Memory writes outside the frame objects and below-`h` objects keep the store
relation (`StoreRel.transport`); a slot write that binds a name in one frame
matches `Store.define` and `Store.set` (`StoreRel.write_slot`); a fresh frame
of unbound slots matches `Store.allocFrame` (`StoreRel.alloc_frame`).
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem slotOf_some {L : List String} {x : String} {i : Nat} (h : slotOf L x = some i) : L[i]? = some x := by
  induction L generalizing i with
  | nil => simp [slotOf] at h
  | cons y l ih =>
    simp only [slotOf] at h
    split at h
    · next e => cases h; simp [e]
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using ih hj

theorem slotOf_none {L : List String} {x : String} (h : slotOf L x = none) : x ∉ L := by
  induction L with
  | nil => simp
  | cons y l ih =>
    simp only [slotOf] at h
    split at h
    · cases h
    · next e =>
      simp only [Option.map_eq_none_iff] at h
      simp only [List.mem_cons, not_or]
      exact ⟨fun h' => e h'.symm, ih h⟩

theorem slotOf_lt {L : List String} {x : String} {i : Nat} (h : slotOf L x = some i) : i < L.length := by
  have := slotOf_some h
  exact (List.getElem?_eq_some_iff.mp this).1

theorem lookupVar_none_of_not_mem {fr : Frame} {x : String} {H : CloMap} {m : Mem} {h f : Nat}
    {L : List String} {par : Nat} (hf : FrameAt H m h f L par fr) (hx : x ∉ L) : lookupVar fr x = none := by
  cases hl : lookupVar fr x with
  | none => rfl
  | some v => exact absurd (hf.names x (by simp [hl])) hx


theorem FrameAt.transport {H : CloMap} {m m' : Mem} {h h' f : Nat} {L : List String} {par : Nat}
    {fr : Frame} (hf : FrameAt H m h f L par fr) (hag : Agree m m' f (f + frSize L)) (hal : f % 8 = 0)
    (ho : ObjAgree m m' h) (hh : h ≤ h') : FrameAt H m' h' f L par fr where
  parent := by rw [hag f (by omega) (by unfold frSize; omega) hal]; exact hf.parent
  bound i x v hi hx := by
    have hl := (List.getElem?_eq_some_iff.mp hi).1
    rw [hag _ (by omega) (by unfold frSize; omega) (by omega),
      hag _ (by omega) (by unfold frSize; omega) (by omega)]
    exact (hf.bound i x v hi hx).mono ho hh
  unbound i x hi hx := by
    have hl := (List.getElem?_eq_some_iff.mp hi).1
    rw [hag _ (by omega) (by unfold frSize; omega) (by omega)]
    exact hf.unbound i x hi hx
  names := hf.names

theorem CloObj.transport {m m' : Mem} {h h' p : Nat} {name : Option String} {d c : Nat}
    (ho : CloObj m h p name d c) (hag : ObjAgree m m' h) (hh : h ≤ h') : CloObj m' h' p name d c where
  lo := ho.lo
  hi := by have := ho.hi; omega
  al := ho.al
  disp := by rw [hag _ (by have := ho.al; omega) (by have := ho.lo; omega) (by have := ho.hi; omega)]; exact ho.disp
  dispStr := ho.dispStr.mono hag hh
  cat := by rw [hag _ (by have := ho.al; omega) (by have := ho.lo; omega) (by have := ho.hi; omega)]; exact ho.cat
  catStr := ho.catStr.mono hag hh

theorem CloOK.transport {H : CloMap} {s : Store} {m m' : Mem} {h h' : Nat} (hc : CloOK H s m h)
    (hag : ObjAgree m m' h) (hh : h ≤ h') : CloOK H s m' h' where
  len := hc.len
  obj a cd p ha hp := by
    obtain ⟨d, c, ho⟩ := hc.obj a cd p ha hp
    exact ⟨d, c, ho.transport hag hh⟩

/-- Memory that keeps the frame objects below `hF` and the objects below `h`
keeps the store relation, with the object heap grown to `h'`. -/
theorem StoreRel.transport {F : FrMap} {H : CloMap} {s : Store} {m m' : Mem} {hF h h' : Nat}
    (hs : StoreRel F H s m hF h) (hag : Agree m m' frameBase hF) (ho : ObjAgree m m' h) (hh : h ≤ h') :
    StoreRel F H s m' hF h' where
  len := hs.len
  frame a fr f L hfr hF' := by
    obtain ⟨h1, h2, h3, -⟩ := hs.region a f L hF'
    exact (hs.frame a fr f L hfr hF').transport (hag.mono h1 h2) h3 ho hh
  region := hs.region
  nodup := hs.nodup
  disjoint := hs.disjoint
  parents := hs.parents
  clo := hs.clo.transport ho hh
  inj := hs.inj
  top := hs.top

/-! ## Frame updates -/

/-- The frames of `s'` are those of `s` with the same parents. -/
def SameShape (s s' : Store) : Prop :=
  s'.frames.size = s.frames.size ∧
    ∀ (b : Nat) (fr : Frame), s.frames[b]? = some fr → ∃ fr', s'.frames[b]? = some fr' ∧ fr'.parent = fr.parent

theorem ChainL.transport {F : FrMap} {s s' : Store} (hss : SameShape s s') :
    ∀ {a : Addr} {Γ : List (List String)}, ChainL F s a Γ → ChainL F s' a Γ
  | _, _, .top hfr hpar hF => by
    obtain ⟨fr', h1, h2⟩ := hss.2 _ _ hfr
    exact .top h1 (by rw [h2, hpar]) hF
  | _, _, .cons hfr hpar hF hc => by
    obtain ⟨fr', h1, h2⟩ := hss.2 _ _ hfr
    exact .cons h1 (by rw [h2, hpar]) hF (ChainL.transport hss hc)

theorem ParentsLt.transport {s s' : Store} (hp : ParentsLt s) (hss : SameShape s s')
    (hback : ∀ (b : Nat) (fr' : Frame), s'.frames[b]? = some fr' → ∃ fr, s.frames[b]? = some fr ∧
      fr'.parent = fr.parent) : ParentsLt s' := by
  intro a fr' b ha hb
  obtain ⟨fr, h1, h2⟩ := hback a fr' ha
  exact hp a fr b h1 (by rw [← h2, hb])

/-- A frame update that binds `x` to `v` and keeps the parent. -/
structure Binds (fr fr' : Frame) (x : String) (v : Value) : Prop where
  parent : fr'.parent = fr.parent
  look : ∀ y, lookupVar fr' y = if y = x then some v else lookupVar fr y

/-- Rebinding `x` to `v` in a binding list. -/
def rebind (x : String) (v : Value) (p : String × Value) : String × Value := if p.1 == x then (x, v) else p

theorem find?_rebind {l : List (String × Value)} {x y : String} {v : Value} :
    (l.map (rebind x v)).find? (·.1 == y) =
      if y = x ∧ l.any (·.1 == x) then some (x, v) else l.find? (·.1 == y) := by
  induction l with
  | nil => simp
  | cons q l ih =>
    obtain ⟨z, w⟩ := q
    simp only [List.map_cons, List.find?_cons, List.any_cons]
    by_cases hz : z = x
    · subst hz
      have e : rebind z v (z, w) = (z, v) := by simp [rebind]
      rw [e]
      by_cases hy : y = z
      · subst hy; simp
      · have h1 : (z == y) = false := by simpa using Ne.symm hy
        simp only [h1, ih, hy, false_and, if_false]
    · have e : rebind x v (z, w) = (z, w) := by simp [rebind, hz]
      rw [e]
      by_cases hzy : z = y
      · subst hzy; simp [hz]
      · have h1 : (z == y) = false := by simpa using hzy
        have h2 : (z == x) = false := by simpa using hz
        simp only [h1, h2, ih, Bool.false_or]

theorem binds_set {fr : Frame} {x : String} {v : Value} (hx : fr.vars.any (·.1 == x) = true) :
    Binds fr { fr with vars := fr.vars.map (rebind x v) } x v where
  parent := rfl
  look y := by
    simp only [lookupVar, find?_rebind, hx, and_true]
    split <;> simp_all

theorem binds_define {fr : Frame} {x : String} {v : Value} :
    Binds fr { fr with
      vars := (if fr.vars.any (·.1 == x) then fr.vars.map (rebind x v) else fr.vars ++ [(x, v)]) } x v where
  parent := rfl
  look y := by
    split
    · next hx => exact (binds_set hx).look y
    · next hx =>
      simp only [lookupVar, List.find?_append, List.find?_singleton]
      simp only [Bool.not_eq_true, List.any_eq_false, beq_iff_eq] at hx
      by_cases hy : y = x
      · subst hy
        rw [List.find?_eq_none.mpr (fun q hq e => hx q hq (by simpa using e))]
        simp
      · rw [if_neg hy]
        cases hf : fr.vars.find? (·.1 == y) with
        | some q => simp
        | none => simp [Ne.symm hy]

theorem rdW_two {m : Mem} {a b : Nat} {t p : BitVec 64} (ha : a % 8 = 0) (hb : b % 8 = 0) :
    rdW (applyW (applyW m (a, 8, t)) (a + 8, 8, p)) b =
      if b = a + 8 then p else if b = a then t else rdW m b := by
  rw [rdW_upd (by omega) hb, rdW_upd ha hb]

theorem Binds.parAddr_eq {F : FrMap} {fr fr' : Frame} {x : String} {v : Value} (hb : Binds fr fr' x v) :
    parAddr F fr' = parAddr F fr := by unfold Vsa.Compiler.parAddr; rw [hb.parent]

/-- **Slot write.** Writing the representation of `v` into slot `i` of frame `c`,
whose layout gives `x` slot `i`, matches a frame update binding `x` to `v`. -/
theorem StoreRel.write_slot {F : FrMap} {H : CloMap} {s : Store} {m : Mem} {hF h : Nat}
    (hs : StoreRel F H s m hF h) {c : Nat} {fr : Frame} {fc : Nat} {Lc : List String} {x : String}
    {i : Nat} {v : Value} {t p : BitVec 64} (hc : s.frames[c]? = some fr) (hFc : F[c]? = some (fc, Lc))
    (hsl : slotOf Lc x = some i) (hv : VRepr H m h v t p) (g : Frame → Frame) (hg : Binds fr (g fr) x v) :
    StoreRel F H { s with frames := s.frames.modify c g }
      (applyW (applyW m (fc + 8 + 16 * i, 8, t)) (fc + 8 + 16 * i + 8, 8, p)) hF h := by
  have hb : frameBase = 0x80100000 := rfl
  have he : frameEnd = 0x90000000 := rfl
  have hob : objBase = 0x90000000 := rfl
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hs.region c fc Lc hFc
  have hi := slotOf_lt hsl
  have hLi := slotOf_some hsl
  unfold frSize at hc2
  have htop := hs.top
  have hrd : ∀ b, b % 8 = 0 → rdW (applyW (applyW m (fc + 8 + 16 * i, 8, t)) (fc + 8 + 16 * i + 8, 8, p)) b =
      if b = fc + 8 + 16 * i + 8 then p else if b = fc + 8 + 16 * i then t else rdW m b :=
    fun b hb8 => rdW_two (by omega) hb8
  have hout : ∀ lo hi', fc + 8 + 16 * i + 16 ≤ lo ∨ hi' ≤ fc + 8 + 16 * i → Agree m (applyW (applyW m (fc + 8 + 16 * i, 8, t)) (fc + 8 + 16 * i + 8, 8, p)) lo hi' := by
    intro lo hi' hlh b h1 h2 h3
    rw [hrd b h3, if_neg (by omega), if_neg (by omega)]
  have hobj : ObjAgree m (applyW (applyW m (fc + 8 + 16 * i, 8, t)) (fc + 8 + 16 * i + 8, 8, p)) h := fun b h3 h1 h2 => by
    rw [hrd b h3, if_neg (by omega), if_neg (by omega)]
  have hss : SameShape s { s with frames := s.frames.modify c g } := by
    refine ⟨by simp, fun b frb hfb => ?_⟩
    simp only [Array.getElem?_modify]
    split
    · next e => subst e; rw [hc] at hfb; cases hfb; exact ⟨g fr, by rw [hc]; rfl, hg.parent⟩
    · exact ⟨frb, hfb, rfl⟩
  refine ⟨by simp [hs.len], ?_, hs.region, hs.nodup, hs.disjoint, ?_,
    (let hc := hs.clo.transport hobj (Nat.le_refl _); ⟨hc.len, hc.obj⟩),
    hs.inj, hs.top⟩
  · intro b frb fb Lb hfb hFb
    simp only [Array.getElem?_modify] at hfb
    split at hfb
    · next e =>
      subst e
      rw [hc] at hfb; cases hfb
      rw [hFc] at hFb; cases hFb
      have hfa := hs.frame c fr fc Lc hc hFc
      rw [hg.parAddr_eq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hrd fc hc3, if_neg (by omega), if_neg (by omega)]; exact hfa.parent
      · intro j y w hj hy
        have hjl := (List.getElem?_eq_some_iff.mp hj).1
        rw [hg.look y] at hy
        by_cases hyx : y = x
        · subst hyx
          simp only [if_true] at hy; cases hy
          have hji : j = i := by
            have := hs.nodup c fc Lc hFc
            exact (List.Nodup.getElem?_inj hjl this).mp (by rw [hj, hLi])
          subst hji
          rw [hrd _ (by omega), if_neg (by omega), if_pos rfl, hrd _ (by omega),
            if_pos (by omega)]
          exact hv.mono hobj (Nat.le_refl _)
        · rw [if_neg hyx] at hy
          have hji : j ≠ i := fun e => by subst e; rw [hLi] at hj; cases hj; exact hyx rfl
          rw [hrd _ (by omega), if_neg (by omega), if_neg (by omega), hrd _ (by omega),
            if_neg (by omega), if_neg (by omega)]
          exact (hfa.bound j y w hj hy).mono hobj (Nat.le_refl _)
      · intro j y hj hy
        have hjl := (List.getElem?_eq_some_iff.mp hj).1
        rw [hg.look y] at hy
        by_cases hyx : y = x
        · subst hyx; simp at hy
        · rw [if_neg hyx] at hy
          have hji : j ≠ i := fun e => by subst e; rw [hLi] at hj; cases hj; exact hyx rfl
          rw [hrd _ (by omega), if_neg (by omega), if_neg (by omega)]
          exact hfa.unbound j y hj hy
      · intro y hy
        rw [hg.look y] at hy
        by_cases hyx : y = x
        · subst hyx; exact List.mem_of_getElem? hLi
        · rw [if_neg hyx] at hy; exact hfa.names y hy
    · next e =>
      obtain ⟨hb1, hb2, hb3, -⟩ := hs.region b fb Lb hFb
      have hdis : fb + frSize Lb ≤ fc ∨ fc + frSize Lc ≤ fb := by
        rcases Nat.lt_or_gt_of_ne e with h1 | h1
        · exact .inr (hs.disjoint c b fc fb Lc Lb h1 hFc hFb)
        · exact .inl (hs.disjoint b c fb fc Lb Lc h1 hFb hFc)
      unfold frSize at hdis hb2
      exact (hs.frame b frb fb Lb hfb hFb).transport (hout _ _ (by unfold frSize; omega)) hb3 hobj
        (Nat.le_refl _)
  · exact hs.parents.transport hss (fun b frb hfb => by
      simp only [Array.getElem?_modify] at hfb
      split at hfb
      · next e => subst e; rw [hc] at hfb; cases hfb; exact ⟨fr, hc, hg.parent⟩
      · exact ⟨frb, hfb, rfl⟩)

/-! ## Assignment through the chain -/

theorem any_iff_lookup {fr : Frame} {x : String} :
    fr.vars.any (·.1 == x) = (lookupVar fr x).isSome := by
  unfold lookupVar
  cases h : fr.vars.find? (·.1 == x) with
  | none =>
    simp only [Option.map_none, Option.isSome_none]
    rw [List.find?_eq_none] at h
    simpa using fun q hq e => h q hq (by simpa using e)
  | some q =>
    simp only [Option.map_some, Option.isSome_some, List.any_eq_true]
    exact ⟨q, List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- The frame update of an assignment to `x`. -/
def setFrame (x : String) (v : Value) (f : Frame) : Frame := { f with vars := f.vars.map (rebind x v) }

theorem set_step {s : Store} {g : Nat} {a : Addr} {x : String} {v : Value} {fr : Frame}
    (h : s.frames[a]? = some fr) : s.set (g + 1) a x v =
      if (lookupVar fr x).isSome then some { s with frames := s.frames.modify a (setFrame x v) }
      else match fr.parent with
        | some b => s.set g b x v
        | none => none := by
  rw [← any_iff_lookup]
  simp only [Store.set, h, Option.bind_eq_bind, Option.bind_some]
  rfl

theorem set_gas {s : Store} (hp : ParentsLt s) (x : String) (v : Value) :
    ∀ (a g : Nat), a < g → s.set g a x v = s.set (a + 1) a x v := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
  intro g hg
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  cases hfr : s.frames[a]? with
  | none => simp [Store.set, hfr]
  | some fr =>
    rw [set_step hfr, set_step hfr]
    split
    · rfl
    · cases hb : fr.parent with
      | none => rfl
      | some b =>
        have hba := hp a fr b hfr hb
        simp only
        rw [ih b hba g' (by omega), ih b hba a hba]

/-- Memory outside the frame objects below `hF` is unchanged. -/
def OutFrames (m m' : Mem) (hF : Nat) : Prop :=
  ∀ b, b % 8 = 0 → b + 8 ≤ frameBase ∨ hF ≤ b → rdW m' b = rdW m b

theorem OutFrames.refl (m : Mem) (hF : Nat) : OutFrames m m hF := fun _ _ _ => rfl

/-- The outcome of an assignment that found its frame. -/
structure SetPost (F : FrMap) (H : CloMap) (s : Store) (m : Mem) (hF h : Nat) (s' : Store) (m' : Mem) :
    Prop where
  rel : StoreRel F H s' m' hF h
  shape : SameShape s s'
  clo : s'.closures = s.closures
  out : OutFrames m m' hF

theorem setPost_of_slot {F : FrMap} {H : CloMap} {s : Store} {m : Mem} {hF h : Nat}
    (hs : StoreRel F H s m hF h) {c : Nat} {fr : Frame} {fc : Nat} {Lc : List String} {x : String}
    {i : Nat} {v : Value} {t p : BitVec 64} (hc : s.frames[c]? = some fr) (hFc : F[c]? = some (fc, Lc))
    (hsl : slotOf Lc x = some i) (hv : VRepr H m h v t p) (hx : (lookupVar fr x).isSome) :
    SetPost F H s m hF h { s with frames := s.frames.modify c (setFrame x v) }
      (applyW (applyW m (fc + 8 + 16 * i, 8, t)) (fc + 8 + 16 * i + 8, 8, p)) where
  rel := hs.write_slot hc hFc hsl hv _ (binds_set (by rw [any_iff_lookup]; exact hx))
  shape := by
    refine ⟨by simp, fun b frb hfb => ?_⟩
    simp only [Array.getElem?_modify]
    split
    · next e => subst e; rw [hc] at hfb; cases hfb; exact ⟨setFrame x v fr, by rw [hc]; rfl, rfl⟩
    · exact ⟨frb, hfb, rfl⟩
  clo := rfl
  out := fun b hb hout => by
    obtain ⟨h1, h2, h3, -⟩ := hs.region c fc Lc hFc
    have := slotOf_lt hsl
    have := hs.top
    unfold frSize at h2
    rw [rdW_two (by omega) hb, if_neg (by omega), if_neg (by omega)]

/-! ## Growth -/

/-- `F'`/`s'` extend `F`/`s`: every frame stays with its parent, and its object stays. -/
structure Grows (F : FrMap) (s : Store) (F' : FrMap) (s' : Store) : Prop where
  frames : ∀ (b : Nat) (fr : Frame), s.frames[b]? = some fr →
    ∃ fr', s'.frames[b]? = some fr' ∧ fr'.parent = fr.parent
  objs : ∀ (b : Nat) (q : Nat × List String), F[b]? = some q → F'[b]? = some q

theorem Grows.refl (F : FrMap) (s : Store) : Grows F s F s := ⟨fun _ fr h => ⟨fr, h, rfl⟩, fun _ _ h => h⟩

theorem Grows.trans {F F' F'' : FrMap} {s s' s'' : Store} (h1 : Grows F s F' s') (h2 : Grows F' s' F'' s'') :
    Grows F s F'' s'' := by
  refine ⟨fun b fr h => ?_, fun b q h => h2.objs b q (h1.objs b q h)⟩
  obtain ⟨fr1, h1', e1⟩ := h1.frames b fr h
  obtain ⟨fr2, h2', e2⟩ := h2.frames b fr1 h1'
  exact ⟨fr2, h2', e2.trans e1⟩

theorem Grows.of_shape {F : FrMap} {s s' : Store} (h : SameShape s s') : Grows F s F s' := ⟨h.2, fun _ _ h => h⟩

theorem ChainL.grow {F F' : FrMap} {s s' : Store} (hg : Grows F s F' s') :
    ∀ {a : Addr} {Γ : List (List String)}, ChainL F s a Γ → ChainL F' s' a Γ
  | _, _, .top hfr hpar hF => by
    obtain ⟨fr', h1, h2⟩ := hg.frames _ _ hfr
    exact .top h1 (by rw [h2, hpar]) (hg.objs _ _ hF)
  | _, _, .cons hfr hpar hF hc => by
    obtain ⟨fr', h1, h2⟩ := hg.frames _ _ hfr
    exact .cons h1 (by rw [h2, hpar]) (hg.objs _ _ hF) (ChainL.grow hg hc)

theorem getElem?_push_lt {α : Type} {xs : Array α} {x : α} {b : Nat} (h : b < xs.size) :
    (xs.push x)[b]? = xs[b]? := by
  rw [Array.getElem?_push]; simp [Nat.ne_of_lt h]

theorem getElem?_append_lt {α : Type} {xs : List α} {x : α} {b : Nat} (h : b < xs.length) :
    (xs ++ [x])[b]? = xs[b]? := List.getElem?_append_left h

/-- The machine address of a frame's parent, given the parent's address. -/
def parOf (F : FrMap) : Option Addr → Nat
  | some b => (F[b]?.map Prod.fst).getD 0
  | none => 0

theorem parAddr_eq_parOf (F : FrMap) (fr : Frame) : parAddr F fr = parOf F fr.parent := by
  unfold parAddr parOf; cases fr.parent <;> rfl

/-- **Frame allocation.** A fresh frame of unbound slots with layout `L` at `hF`,
whose first word is its parent's address, matches `Store.allocFrame`. -/
theorem StoreRel.alloc_frame {F : FrMap} {H : CloMap} {s : Store} {m : Mem} {hF h : Nat}
    (hs : StoreRel F H s m hF h) {L : List String} {par : Option Addr}
    (hpar : ∀ b, par = some b → b < s.frames.size) (hal : hF % 8 = 0) (hfb : frameBase ≤ hF)
    (hroom : hF + 8 + 16 * L.length ≤ frameEnd) (hnd : L.Nodup) (hl : L.length ≤ 120) :
    StoreRel (F ++ [(hF, L)]) H (s.allocFrame par).1
      (tagsW (applyW m (hF, 8, BitVec.ofNat 64 (parOf F par))) (hF + 8) L.length) (hF + 8 + 16 * L.length) h ∧
    Grows F s (F ++ [(hF, L)]) (s.allocFrame par).1 ∧ (s.allocFrame par).2 = s.frames.size ∧
    (F ++ [(hF, L)])[s.frames.size]? = some (hF, L) ∧ OutFrames m
      (tagsW (applyW m (hF, 8, BitVec.ofNat 64 (parOf F par))) (hF + 8) L.length) (hF + 8 + 16 * L.length) ∧
    Agree m (tagsW (applyW m (hF, 8, BitVec.ofNat 64 (parOf F par))) (hF + 8) L.length) 0 hF := by
  have hb : frameBase = 0x80100000 := rfl
  have he : frameEnd = 0x90000000 := rfl
  have hob : objBase = 0x90000000 := rfl
  have htop := hs.top
  have hlen := hs.len
  have hrd : ∀ b, b % 8 = 0 → rdW (tagsW (applyW m (hF, 8, BitVec.ofNat 64 (parOf F par))) (hF + 8) L.length) b =
      if hF + 8 ≤ b ∧ b < hF + 8 + 16 * L.length ∧ (b - (hF + 8)) % 16 = 0 then 6#64
      else if b = hF then BitVec.ofNat 64 (parOf F par) else rdW m b := by
    intro b hb8
    rw [rdW_tagsW _ _ (by omega) _ _ hb8, rdW_upd hal hb8]
  have hlow : Agree m (tagsW (applyW m (hF, 8, BitVec.ofNat 64 (parOf F par))) (hF + 8) L.length) 0 hF :=
    fun b _ h2 h3 => by rw [hrd b h3, if_neg (by omega), if_neg (by omega)]
  have hobj : ObjAgree m (tagsW (applyW m (hF, 8, BitVec.ofNat 64 (parOf F par))) (hF + 8) L.length) h :=
    fun b h3 h1 h2 => by rw [hrd b h3, if_neg (by omega), if_neg (by omega)]
  have hFlt : ∀ b q, F[b]? = some q → b < F.length := fun b q h => (List.getElem?_eq_some_iff.mp h).1
  have hsz : (s.allocFrame par).1.frames.size = s.frames.size + 1 := by simp [Store.allocFrame]
  have hget : ∀ b, (s.allocFrame par).1.frames[b]? =
      if b = s.frames.size then some ⟨par, []⟩ else if b < s.frames.size then s.frames[b]? else none := by
    intro b
    simp only [Store.allocFrame, Array.getElem?_push]
    split
    · next e => subst e; simp
    · next e =>
      split
      · rfl
      · next e' => exact Array.getElem?_eq_none (by omega)
  have hFget : ∀ b, (F ++ [(hF, L)])[b]? =
      if b = F.length then some (hF, L) else if b < F.length then F[b]? else none := by
    intro b
    split
    · next e => subst e; simp
    · next e =>
      split
      · next e' => exact getElem?_append_lt e'
      · next e' => exact List.getElem?_eq_none (by simp; omega)
  have hparOf : ∀ q : Option Addr, (∀ b, q = some b → b < F.length) → parOf (F ++ [(hF, L)]) q = parOf F q := by
    intro q hq
    cases q with
    | none => rfl
    | some b => simp only [parOf, getElem?_append_lt (hq b rfl)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hs.inj, by omega⟩,
    ⟨fun b fr hfr => ?_, fun b q hq => (getElem?_append_lt (hFlt b q hq)).trans hq⟩, rfl, ?_, ?_, ?_⟩
  · simp [hsz, hlen]
  · intro a fr f L' hfr hF'
    rw [hget] at hfr; rw [hFget] at hF'
    rw [parAddr_eq_parOf]
    by_cases ha : a = s.frames.size
    · subst ha
      rw [if_pos rfl] at hfr; rw [if_pos hlen.symm] at hF'
      cases hfr; cases hF'
      rw [hparOf _ (fun b hb => by rw [hlen]; exact hpar b hb)]
      refine ⟨by rw [hrd hF hal, if_neg (by omega), if_pos rfl], ?_, ?_, ?_⟩
      · intro i x v _ hx; simp [lookupVar] at hx
      · intro i x hi _
        have := (List.getElem?_eq_some_iff.mp hi).1
        rw [hrd _ (by omega), if_pos ⟨by omega, by omega, by omega⟩]; rfl
      · intro x hx; simp [lookupVar] at hx
    · rw [if_neg ha] at hfr; rw [if_neg (by omega)] at hF'
      split at hfr
      · next hlt =>
        rw [if_pos (by omega)] at hF'
        obtain ⟨h1, h2, h3, -⟩ := hs.region a f L' hF'
        have hfa := hs.frame a fr f L' hfr hF'
        rw [parAddr_eq_parOf] at hfa
        rw [hparOf _ (fun b hb => Nat.lt_trans (hs.parents a fr b hfr hb) (by rw [hlen]; exact hlt))]
        exact hfa.transport (hlow.mono (by omega) h2) h3 hobj (Nat.le_refl _)
      · cases hfr
  · intro a f L' hF'
    rw [hFget] at hF'
    split at hF'
    · cases hF'; unfold frSize; exact ⟨hfb, by omega, hal, hl⟩
    · split at hF'
      · obtain ⟨h1, h2, h3, h4⟩ := hs.region a f L' hF'; exact ⟨h1, by omega, h3, h4⟩
      · cases hF'
  · intro a f L' hF'
    rw [hFget] at hF'
    split at hF'
    · cases hF'; exact hnd
    · split at hF'
      · exact hs.nodup a f L' hF'
      · cases hF'
  · intro a b fa fb La Lb hab ha hb'
    rw [hFget] at ha hb'
    split at ha
    · split at hb'
      · omega
      · split at hb'
        · omega
        · cases hb'
    · split at ha
      · split at hb'
        · cases hb'; obtain ⟨-, h2, -, -⟩ := hs.region a fa La ha; exact h2
        · split at hb'
          · exact hs.disjoint a b fa fb La Lb hab ha hb'
          · cases hb'
      · cases ha
  · intro a fr b hfr hb'
    rw [hget] at hfr
    split at hfr
    · next e => cases hfr; have := hpar b hb'; rw [e]; exact this
    · split at hfr
      · have := hs.parents a fr b hfr hb'; omega
      · cases hfr
  · exact (let hc := hs.clo.transport hobj (Nat.le_refl _); ⟨by simp [Store.allocFrame, hc.len], hc.obj⟩)
  · rw [hget]
    have hb := (Array.getElem?_eq_some_iff.mp hfr).1
    rw [if_neg (by omega), if_pos hb]; exact ⟨fr, hfr, rfl⟩
  · rw [hFget, if_pos hlen.symm]
  · intro b hb8 hout
    rw [hrd b hb8, if_neg (by omega), if_neg (by omega)]
  · exact hlow

end Vsa.Compiler
