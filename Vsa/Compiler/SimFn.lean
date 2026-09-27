import Vsa.Compiler.SimAssign

/-!
# Forward simulation: function literals

A function literal allocates its closure object `[frame][code][print][concat]`
at the object heap pointer and jumps over its function's code.
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem FrameAt.grow {H H' : CloMap} {m m' : Mem} {h h' f : Nat} {L : List String} {par : Nat}
    {fr : Frame} (hf : FrameAt H m h f L par fr) (hH : H <+: H') (hag : Agree m m' f (f + frSize L))
    (hal : f % 8 = 0) (ho : ObjAgree m m' h) (hh : h ≤ h') : FrameAt H' m' h' f L par fr := by
  have ht := hf.transport hag hal ho hh
  exact ⟨ht.parent, fun i x v hi hx => (ht.bound i x v hi hx).grow hH (ObjAgree.refl _ _) (Nat.le_refl _),
    ht.unbound, ht.names⟩

theorem getElem?_last {l : List Nat} {x p b : Nat} (h : (l ++ [x])[b]? = some p) (hb : l.length ≤ b) :
    b = l.length ∧ p = x := by
  have hlt := (List.getElem?_eq_some_iff.mp h).1
  simp only [List.length_append, List.length_singleton] at hlt
  have e : b = l.length := by omega
  subst e
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at h
  simp at h
  exact ⟨rfl, h.symm⟩

/-- **Closure allocation.** An object for the new closure at `h`, below `h'`,
matches `Store.allocClosure`. -/
theorem StoreRel.alloc_clo {F : FrMap} {H : CloMap} {s : Store} {m m' : Mem} {hF h h' : Nat}
    (hs : StoreRel F H s m hF h) (hfr : Agree m m' frameBase hF) (hag : ObjAgree m m' h)
    (hh : h + 32 ≤ h') {cd : ClosureData} {d c : Nat} (hobj : CloObj m' h' h cd.name d c) :
    StoreRel F (H ++ [h]) (s.allocClosure cd).1 m' hF h' := by
  have hlen := hs.clo.len
  have hH : H <+: H ++ [h] := List.prefix_append _ _
  refine ⟨hs.len, fun a fr f L hfr' hF' => ?_, hs.region, hs.nodup, hs.disjoint, hs.parents, ⟨?_, ?_⟩, ?_,
    hs.top⟩
  · obtain ⟨h1, h2, h3, -⟩ := hs.region a f L hF'
    exact (hs.frame a fr f L hfr' hF').grow hH (hfr.mono h1 h2) h3 hag (by omega)
  · simp [Store.allocClosure, hlen]
  · intro a cd' p ha hp
    simp only [Store.allocClosure, Array.getElem?_push] at ha
    split at ha
    · next e =>
      cases ha
      subst e
      rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self] at hp
      cases hp
      exact ⟨d, c, hobj⟩
    · rw [List.getElem?_append_left (by rw [hlen]; exact (Array.getElem?_eq_some_iff.mp ha).1)] at hp
      obtain ⟨d', c', ho⟩ := hs.clo.obj a cd' p ha hp
      exact ⟨d', c', ho.transport hag (by omega)⟩
  · intro a b p ha hb
    have hold : ∀ (i q : Nat), H[i]? = some q → q + 32 ≤ h := by
      intro i q hi
      have hlt := (List.getElem?_eq_some_iff.mp hi).1
      rw [hlen] at hlt
      obtain ⟨cd', hcd⟩ : ∃ cd', s.closures[i]? = some cd' := ⟨_, Array.getElem?_eq_getElem hlt⟩
      obtain ⟨_, _, ho⟩ := hs.clo.obj i cd' q hcd hi
      exact ho.hi
    rcases Nat.lt_or_ge a H.length with h1 | h1 <;> rcases Nat.lt_or_ge b H.length with h2 | h2
    · rw [List.getElem?_append_left h1] at ha; rw [List.getElem?_append_left h2] at hb
      exact hs.inj a b p ha hb
    · rw [List.getElem?_append_left h1] at ha
      obtain ⟨-, rfl⟩ := getElem?_last hb h2
      have := hold a _ ha; omega
    · rw [List.getElem?_append_left h2] at hb
      obtain ⟨-, rfl⟩ := getElem?_last ha h1
      have := hold b _ hb; omega
    · have ha' := (List.getElem?_eq_some_iff.mp ha).1
      have hb' := (List.getElem?_eq_some_iff.mp hb).1
      simp at ha' hb'; omega

theorem gexpr_fn (T : List String) (Γ : List (List String)) (k pos : Nat) (name : Option String)
    (params : List String) (body : List Stmt) :
    gexpr T Γ k pos (.fn name params body) =
      (([addi t0 hpO 32] ++ liN t1 objEnd ++ [Br .ge t1 t0 (pos + 12) (pos + 14), J (pos + 13) errPos]) ++
        ([.sd envR hpO] ++ liN t2 (codeBase + 4 * (pos + 58)) ++ [addi t3 hpO 8, .sd t2 t3] ++
        liN t2 (strAddr T (dispName name)) ++ [addi t3 hpO 16, .sd t2 t3] ++
        liN t2 (strAddr T (catName name)) ++ [addi t3 hpO 24, .sd t2 t3] ++ [mvi a0 4, mv a1 hpO, mv hpO t0])) ++
      [J (pos + 57) (pos + 58 + (fnCode T Γ params body (pos + 58)).length)] ++
      fnCode T Γ params body (pos + 58) := by
  show _ = _
  simp only [gexpr, fnCode, List.append_assoc, List.cons_append, List.nil_append]

theorem liN_big {rd n : Nat} (h1 : 2048 ≤ n) (h2 : n < 2 ^ 63) : (li rd (BitVec.ofNat 64 n)).length = 11 :=
  li_length_big (by rw [toInt_ofNat_small n h2]; omega)

/-- Memory after writing a closure object at `h`. -/
def cloW (m : Mem) (h : Nat) (e c d k : BitVec 64) : Mem :=
  applyW (applyW (applyW (applyW m (h, 8, e)) (h + 8, 8, c)) (h + 16, 8, d)) (h + 24, 8, k)

theorem rdW_cloW {m : Mem} {h : Nat} {e c d k : BitVec 64} (hal : h % 8 = 0) {b : Nat} (hb : b % 8 = 0) :
    rdW (cloW m h e c d k) b = if b = h + 24 then k else if b = h + 16 then d else if b = h + 8 then c
      else if b = h then e else rdW m b := by
  unfold cloW
  rw [rdW_upd (by omega) hb, rdW_upd (by omega) hb, rdW_upd (by omega) hb, rdW_upd hal hb]

theorem cloW_out {m : Mem} {h : Nat} {e c d k : BitVec 64} (hal : h % 8 = 0) {lo hi : Nat}
    (hout : hi ≤ h ∨ h + 32 ≤ lo) : Agree m (cloW m h e c d k) lo hi := fun b h1 h2 h3 => by
  rw [rdW_cloW hal h3, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem cloW_obj {m : Mem} {h : Nat} {e c d k : BitVec 64} (hal : h % 8 = 0) : ObjAgree m (cloW m h e c d k) h :=
  fun b h3 _ h2 => by rw [rdW_cloW hal h3, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem SameShape.allocClosure (s : Store) (cd : ClosureData) : SameShape s (s.allocClosure cd).1 :=
  ⟨rfl, fun _ fr h => ⟨fr, h, rfl⟩⟩

/-- The view after allocating a closure object at `V.h`. -/
def View.withClo (V : View) : View := { V with H := V.H ++ [V.h], h := V.h + 32 }

theorem CloCode.alloc {code : List Ins} {T : List String} {V : View} {s : Store} {m m' : Mem}
    (hc : CloCode code T V s m) (hok : CloOK V.H s m V.h) (hag : ObjAgree m m' V.h) {cd : ClosureData} {q : Nat}
    {Γc : List (List String)} (h1 : rdW m' V.h = BitVec.ofNat 64 (V.fa cd.env)) (h2 : rdW m' (V.h + 8) = pcOf q)
    (h3 : ChainL V.F s cd.env Γc) (h4 : Seg code q (fnCode T Γc cd.params cd.body q))
    (h5 : PosOK (q + (fnCode T Γc cd.params cd.body q).length)) (h6 : WfFn T Γc cd.params cd.body) :
    CloCode code T V.withClo (s.allocClosure cd).1 m' := by
  have hlen := hok.len
  have hsh := SameShape.allocClosure s cd
  intro a cd' p ha hp
  simp only [Store.allocClosure, Array.getElem?_push] at ha
  split at ha
  · next e =>
    cases ha; subst e
    simp only [View.withClo] at hp
    rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self] at hp
    cases hp
    exact ⟨q, Γc, h1, h2, h3.transport hsh, h4, h5, h6⟩
  · simp only [View.withClo] at hp
    rw [List.getElem?_append_left (by rw [hlen]; exact (Array.getElem?_eq_some_iff.mp ha).1)] at hp
    obtain ⟨q', Γ', g1, g2, g3, g4, g5, g6⟩ := hc.transport hok hag a cd' p ha hp
    exact ⟨q', Γ', g1, g2, g3.transport hsh, g4, g5, g6⟩

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem sFn {st : St} {d : Nat} {env : Addr} {name : Option String} {params : List String}
    {body : List Stmt} {store' : Store} {a : Addr}
    (halloc : st.store.allocClosure ⟨env, name, params, body⟩ = (store', a)) :
    ESpec code T st d env (.fn name params body) ⟨store', st.out⟩ (.closure a) closureBytes := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp
  obtain ⟨hl1, hl2, hd, hc, hwfn⟩ := hwf
  rw [gexpr_fn] at hseg hP ⊢
  obtain ⟨s1, s3⟩ := hseg.append
  obtain ⟨s1, s2⟩ := s1.append
  obtain ⟨s1, s1b⟩ := s1.append
  have hsd := hm.img.strs _ hd
  have hsc := hm.img.strs _ hc
  have hob : objBase = 0x90000000 := rfl
  have hoe : objEnd = 0xE0000000 := rfl
  have hcb : codeBase = 0x80004800 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hp := hm.img.ptr
  have := hsd.lo; have := hsd.hi; have := hsc.lo; have := hsc.hi; have := hp.lo; have := hp.hi; have := hp.al
  have hl0 : ∀ rd, (liN rd objEnd).length = 11 := fun rd => liN_big (by decide) (by decide)
  have hl1 : ∀ rd, (liN rd (codeBase + 4 * (pos + 58))).length = 11 := fun rd =>
    liN_big (by omega) (by unfold PosOK at hP; simp at hP; omega)
  have hl2 : ∀ rd, (liN rd (strAddr T (dispName name))).length = 11 := fun rd => liN_big (by omega) (by omega)
  have hl3 : ∀ rd, (liN rd (strAddr T (catName name))).length = 11 := fun rd => liN_big (by omega) (by omega)
  simp only [List.length_append, List.length_cons, List.length_nil, hl0, hl1, hl2, hl3] at hP ⊢
  have hpc : PosOK (pos + 58) := posOK_le hP (by omega)
  have k8 := has_mem hm.ho (by decide); have e8 := srcVal_of_has hm.ho
  have k9 := has_mem hm.henv (by decide); have e9 := srcVal_of_has hm.henv
  simp only [hpO, envR] at k8 e8 k9 e9
  obtain ⟨pc0, L, m, o⟩ := A
  simp only at hA; subst hA
  apply run_whole hR.fits s1
  wp_simp [liN, k8, e8, k9, e9, liN_big (n := codeBase + 4 * (pos + 58)) (by unfold PosOK at hpc; omega)
    (by unfold PosOK at hpc; omega), liN_big (n := strAddr T (dispName name)) (by omega) (by omega),
    liN_big (n := strAddr T (catName name)) (by omega) (by omega)]
  have hn0 : (BitVec.ofNat 64 V.h).toNat = V.h := toNat_ofNat_lt (by omega)
  have hn8 : (BitVec.ofNat 64 (V.h + 8)).toNat = V.h + 8 := toNat_ofNat_lt (by omega)
  have hn16 : (BitVec.ofNat 64 (V.h + 16)).toNat = V.h + 16 := toNat_ofNat_lt (by omega)
  have hn24 : (BitVec.ofNat 64 (V.h + 24)).toNat = V.h + 24 := toNat_ofNat_lt (by omega)
  split
  · next hroom =>
    simp only [List.length_append, List.length_cons, List.length_nil, hl0] at s1b
    have t0' : V.h ≠ tohostAddr := by omega
    have t8 : V.h + 8 ≠ tohostAddr := by omega
    have t16 : V.h + 16 ≠ tohostAddr := by omega
    have t24 : V.h + 24 ≠ tohostAddr := by omega
    have o0 : StOK V.h := by unfold StOK; omega
    have o8 : StOK (V.h + 8) := by unfold StOK; omega
    have o16 : StOK (V.h + 16) := by unfold StOK; omega
    have o24 : StOK (V.h + 24) := by unfold StOK; omega
    apply run_whole hR.fits s1b
    wp_simp [liN, k8, e8, k9, e9, hn0, hn8, hn16, hn24, t0', t8, t16, t24, o0, o8, o16, o24, liN_big (n := codeBase + 4 * (pos + 58))
      (by unfold PosOK at hpc; omega) (by unfold PosOK at hpc; omega),
      liN_big (n := strAddr T (dispName name)) (by omega) (by omega),
      liN_big (n := strAddr T (catName name)) (by omega) (by omega)]
    simp only [List.length_append, List.length_cons, List.length_nil, hl0, hl1, hl2, hl3] at s2 s3
    apply run_jumps hR.fits (s2.cast (pos' := pos + 14 + 43) (by omega))
    wp_simp []
    have hst : store' = (st.store.allocClosure ⟨env, name, params, body⟩).1 := by rw [halloc]
    have ha : a = V.H.length := by
      have : a = (st.store.allocClosure ⟨env, name, params, body⟩).2 := by rw [halloc]
      rw [this, hm.rel.clo.len]; rfl
    subst hst ha
    have hmem : applyW (applyW (applyW (applyW m (V.h, 8, BitVec.ofNat 64 (V.fa env)))
        (V.h + 8, 8, BitVec.ofNat 64 (codeBase + 4 * (pos + 58))))
        (V.h + 16, 8, BitVec.ofNat 64 (strAddr T (dispName name))))
        (V.h + 24, 8, BitVec.ofNat 64 (strAddr T (catName name))) =
      cloW m V.h (BitVec.ofNat 64 (V.fa env)) (pcOf (pos + 58)) (BitVec.ofNat 64 (strAddr T (dispName name)))
        (BitVec.ofNat 64 (strAddr T (catName name))) := rfl
    rw [hmem]
    have hobj := cloW_obj (m := m) (e := BitVec.ofNat 64 (V.fa env)) (c := pcOf (pos + 58))
      (d := BitVec.ofNat 64 (strAddr T (dispName name))) (k := BitVec.ofNat 64 (strAddr T (catName name))) hp.al
    have hrd := fun b (hb : b % 8 = 0) => rdW_cloW (m := m) (e := BitVec.ofNat 64 (V.fa env))
      (c := pcOf (pos + 58)) (d := BitVec.ofNat 64 (strAddr T (dispName name)))
      (k := BitVec.ofNat 64 (strAddr T (catName name))) (b := b) hp.al hb
    have hlow : Agree m (cloW m V.h (BitVec.ofNat 64 (V.fa env)) (pcOf (pos + 58))
        (BitVec.ofNat 64 (strAddr T (dispName name))) (BitVec.ofNat 64 (strAddr T (catName name))))
        frameBase V.hF := cloW_out hp.al (.inl (by have := hm.rel.top; have hfe : frameEnd = 0x90000000 := rfl; omega))
    have hcobj : CloObj (cloW m V.h (BitVec.ofNat 64 (V.fa env)) (pcOf (pos + 58))
        (BitVec.ofNat 64 (strAddr T (dispName name))) (BitVec.ofNat 64 (strAddr T (catName name))))
        (V.h + 32) V.h name (strAddr T (dispName name)) (strAddr T (catName name)) :=
      ⟨hp.lo, Nat.le_refl _, hp.al, by rw [hrd _ (by omega), if_neg (by omega), if_pos rfl],
        hsd.mono hobj (by omega), by rw [hrd _ (by omega), if_pos rfl], hsc.mono hobj (by omega)⟩
    refine reach_here (.inr ⟨?_, V.withClo, ?_⟩)
    · show pcOf _ = pcOf _; congr 1 <;> omega
    have hwh : V.withClo.h = V.h + 32 := rfl
    exact {
      ms := {
        rel := hm.rel.alloc_clo hlow hobj (Nat.le_refl _) hcobj
        img := hm.img.transport hobj (by omega) ⟨by omega, hroom, by omega⟩
        clo := hm.clo.alloc hm.rel.clo hobj (by rw [hrd _ hp.al, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_pos rfl]) (by rw [hrd _ (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl])
          hm.chn (s3.cast (by omega))
          (show PosOK (pos + 58 + (fnCode T Γ params body (pos + 58)).length) from posOK_le hP (by omega)) hwfn
        chn := hm.chn.transport (SameShape.allocClosure _ _)
        out := hm.out
        ho := by reg_simp [] <;> rfl
        hf := by reg_simp []; exact hm.hf
        henv := by reg_simp []; exact hm.henv
        hsp := by reg_simp []; exact hm.hsp
        hdep := by reg_simp []; exact hm.hdep
        stk := hm.stk
        hfal := hm.hfal }
      val := ⟨4, BitVec.ofNat 64 V.h, by reg_simp [], by reg_simp [], rfl, by
        simp only [View.withClo, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rw [toNat_ofNat_lt (by omega)]; rfl⟩
      grow := ⟨Grows.of_shape (SameShape.allocClosure _ _), List.prefix_append _ _, Nat.le_refl _,
        by simp [View.withClo]⟩
      within := ⟨by simp [View.withClo], by simp only [View.withClo, closureBytes]; omega⟩
      stack := ⟨cloW_out hp.al (.inr (by have := hm.stk.bounds.1; have hl : stackLo = objEnd := rfl; omega)),
        cloW_out hp.al (.inr (by have := hm.stk.bounds.1; have hl : stackLo = objEnd := rfl; omega))⟩
      obj := hobj }
  · next hroom =>
    exact reach_here (.inl ⟨rfl, fun hr => hroom (by have := hr.2; unfold closureBytes at this; omega)⟩)

end

end Vsa.Compiler
