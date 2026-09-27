import Vsa.Compiler.SRel

/-!
# Variable reads and assignments

`walk_read`: from the frame of `a` in `t0`, the read walk of `x` over the chain
of layouts of `a` loads the value `Store.lookup` finds, or reaches the error
exit when it finds none. `walk_write` is the same for assignments and
`Store.set`.
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

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

/-- Registers a walk may change. -/
def walkClob : List Nat := [t0, t1, t2, t3, a0, a1]

theorem frame_bounds {F : FrMap} {H : CloMap} {s : Store} {m : Mem} {hF h : Nat}
    (hs : StoreRel F H s m hF h) {a f : Nat} {L : List String} (hF' : F[a]? = some (f, L)) :
    frameBase ≤ f ∧ f + 8 + 16 * L.length ≤ frameEnd ∧ f % 8 = 0 ∧ L.length ≤ 120 := by
  obtain ⟨h1, h2, h3, h4⟩ := hs.region a f L hF'
  have := hs.top
  unfold frSize at h2
  exact ⟨h1, by omega, h3, h4⟩

theorem tagOf_ne6 (v : Value) : tagOf v ≠ 6 := by cases v <;> simp only [tagOf] <;> decide

theorem VRepr.tag_ne6 {H : CloMap} {m : Mem} {h : Nat} {v : Value} {t p : BitVec 64}
    (hv : VRepr H m h v t p) : t ≠ 6 := by rw [hv.tag]; exact tagOf_ne6 v

/-- Run code ending in jumps. -/
theorem run_jumps {code : List Ins} {P : AM → Prop} (hfit : Fits code) {pos : Nat} {is : List Ins}
    (hseg : Seg code pos is) {L : GRegs} {m : Mem} {o : Array String}
    (h : WP code P pos is (fun _ _ _ => False) L m o) : Reaches code ⟨pcOf pos, L, m, o⟩ P :=
  WP_sound hfit _ _ _ L m o hseg (fun _ _ _ h => h.elim) h

theorem ChainL.head {F : FrMap} {s : Store} {a : Addr} {L : List String} {g : List (List String)}
    (h : ChainL F s a (L :: g)) : ∃ f, F[a]? = some (f, L) := by
  cases h with
  | top _ _ hF => exact ⟨_, hF⟩
  | cons _ _ hF _ => exact ⟨_, hF⟩

section
variable {code : List Ins} (hfit : Fits code)
include hfit

/-- **One frame of a read.** With the frame `f` of `fr` in `t0`, `readHere`
loads `x` and jumps to `fin` when `fr` binds it, and otherwise falls through
with `t0` unchanged. -/
theorem read_here {H : CloMap} {m : Mem} {h f : Nat} {l : List String} {par : Nat} {fr : Frame}
    (hfa : FrameAt H m h f l par fr) (hfb : frameBase ≤ f) (hfe : f + 8 + 16 * l.length ≤ frameEnd)
    (hl : l.length ≤ 120) (x : String) (fin : Nat) (hfin : PosOK fin) {pos : Nat} {L : GRegs} {o : Array String}
    (hseg : Seg code pos (readHere x l pos fin)) (hP : PosOK (pos + (readHere x l pos fin).length))
    (h5 : Has L t0 (BitVec.ofNat 64 f)) :
    Reaches code ⟨pcOf pos, L, m, o⟩ (fun B => B.mem = m ∧ B.out = o ∧ Keep walkClob L B.regs ∧
      match lookupVar fr x with
      | some v => B.pc = pcOf fin ∧ InA H m h B.regs v
      | none => B.pc = pcOf (pos + (readHere x l pos fin).length) ∧ Has B.regs t0 (BitVec.ofNat 64 f)) := by
  have hb : frameBase = 0x80100000 := rfl
  have he : frameEnd = 0x90000000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have k5 := has_mem h5 (by decide); have e5 := srcVal_of_has h5
  simp only [t0] at k5 e5
  cases hsl : slotOf l x with
  | none =>
    have hn := lookupVar_none_of_not_mem hfa (slotOf_none hsl)
    refine reach_here ⟨rfl, rfl, Keep.refl _ _, ?_⟩
    simp only [hn, readHere, hsl, List.length_nil, Nat.add_zero]
    exact ⟨by simp, h5⟩
  | some i =>
    have hi := slotOf_lt hsl
    have hLi := slotOf_some hsl
    simp only [readHere, hsl, List.length_cons, List.length_nil] at hseg hP ⊢
    have hfn : (BitVec.ofNat 64 (f + (8 + 16 * i))).toNat = f + (8 + 16 * i) :=
      toNat_ofNat_lt (by omega)
    have hfn' : (BitVec.ofNat 64 (f + (8 + 16 * i) + 8)).toNat = f + (8 + 16 * i) + 8 :=
      toNat_ofNat_lt (by omega)
    apply run_jumps hfit hseg
    wp_simp [k5, e5, hfn, hfn']
    have e1 : f + (8 + 16 * i) = f + 8 + 16 * i := by omega
    have e2 : f + 8 + 16 * i + 8 = f + 16 + 16 * i := by omega
    rw [e1, e2]
    refine ⟨by unfold LdOK; omega, ?_⟩
    split
    · next h6 =>
      have hn : lookupVar fr x = none := by
        cases hl : lookupVar fr x with
        | none => rfl
        | some v => exact absurd h6 (hfa.bound i x v hLi hl).tag_ne6
      refine reach_here ⟨rfl, rfl, ?_, ?_⟩
      · reg_simp [walkClob]
        exact Keep.refl _ _
      · simp only [hn]
        exact ⟨by simp, by reg_simp []; exact h5⟩
    · next h6 =>
      cases hl : lookupVar fr x with
      | none => exact absurd (hfa.unbound i x hLi hl) h6
      | some v =>
        refine ⟨by unfold LdOK; omega, reach_here ⟨rfl, rfl, ?_, ?_⟩⟩
        · reg_simp [walkClob]
          exact Keep.refl _ _
        · refine ⟨rfl, _, _, ?_, ?_, hfa.bound i x v hLi hl⟩ <;> reg_simp []

/-- **Variable read walk.** -/
theorem walk_read {F : FrMap} {H : CloMap} {s : Store} {m : Mem} {hF h : Nat} (hs : StoreRel F H s m hF h)
    (x : String) (fin : Nat) (hfin : PosOK fin) :
    ∀ {a : Addr} {Γ : List (List String)}, ChainL F s a Γ → ∀ (pos f : Nat) (L : GRegs)
      (o : Array String), F[a]? = some (f, Γ.headD []) →
      Seg code pos (walkCode (fun l p => readHere x l p fin) pos Γ) → Has L t0 (BitVec.ofNat 64 f) →
      Reaches code ⟨pcOf pos, L, m, o⟩ (fun B => B.mem = m ∧ B.out = o ∧ Keep walkClob L B.regs ∧
        match s.lookup (a + 1) a x with
        | some v => B.pc = pcOf fin ∧ InA H m h B.regs v
        | none => B.pc = pcOf errPos) := by
  intro a Γ hc
  induction hc with
  | @top a fr f0 Lf hfr hpar hF0 =>
    intro pos f L o hFa hseg h5
    simp only [List.headD_cons] at hFa
    have hff : f0 = f := by rw [hF0] at hFa; cases hFa; rfl
    subst hff
    have hfa := hs.frame a fr f0 Lf hfr hF0
    obtain ⟨hf1, hf2, -, hf4⟩ := frame_bounds hs hF0
    rw [lookup_step hfr]
    simp only [walkCode] at hseg
    have hP := seg_end_posOK hfit hseg (by simp)
    simp only [List.length_append, List.length_cons, List.length_nil] at hP
    obtain ⟨s1, s2⟩ := hseg.append
    refine ex_bind (read_here hfit hfa hf1 hf2 hf4 x fin hfin s1 (by omega) h5) ?_
    rintro B ⟨hm, ho, hk, hB⟩
    obtain ⟨pc, L', m', o'⟩ := B
    simp only at hm ho hk hB; subst hm ho
    cases hl : lookupVar fr x with
    | some v => simp only [hl] at hB ⊢; exact reach_here ⟨rfl, rfl, hk, hB⟩
    | none =>
      simp only [hl, hpar] at hB ⊢
      rw [hB.1]
      apply run_jumps hfit s2
      wp_simp []
      exact reach_here ⟨rfl, rfl, hk, rfl⟩
  | @cons a b fr f0 Lf L' g hfr hpar hF0 hcb ih =>
    intro pos f L o hFa hseg h5
    have hb : frameBase = 0x80100000 := rfl
    have he : frameEnd = 0x90000000 := rfl
    have ht : tohostAddr = 0x8001ad00 := rfl
    simp only [List.headD_cons] at hFa
    have hff : f0 = f := by rw [hF0] at hFa; cases hFa; rfl
    subst hff
    have hfa := hs.frame a fr f0 Lf hfr hF0
    obtain ⟨hf1, hf2, -, hf4⟩ := frame_bounds hs hF0
    obtain ⟨fb, hFb⟩ := hcb.head
    obtain ⟨hb1, hb2, -, -⟩ := frame_bounds hs hFb
    have hba : b < a := hs.parents a fr b hfr hpar
    have hpa : parAddr F fr = fb := by simp only [parAddr, hpar, hFb, Option.map_some, Option.getD_some]
    have hrd : rdW m f0 = BitVec.ofNat 64 fb := by rw [hfa.parent, hpa]
    rw [lookup_step hfr]
    simp only [walkCode] at hseg
    obtain ⟨s12, s3⟩ := hseg.append
    obtain ⟨s1, s2⟩ := s12.append
    rw [List.length_append, List.length_singleton, ← Nat.add_assoc] at s3
    have hP := seg_end_posOK hfit s2 (by simp)
    simp only [List.length_cons, List.length_nil] at hP
    refine ex_bind (read_here hfit hfa hf1 hf2 hf4 x fin hfin s1 (by unfold PosOK at hP ⊢; omega) h5) ?_
    rintro B ⟨hm, ho, hk, hB⟩
    obtain ⟨pc, L1, m', o'⟩ := B
    simp only at hm ho hk hB; subst hm ho
    cases hl : lookupVar fr x with
    | some v => simp only [hl] at hB ⊢; exact reach_here ⟨rfl, rfl, hk, hB⟩
    | none =>
      simp only [hl, hpar] at hB ⊢
      rw [hB.1, lookup_gas hs.parents x b a hba]
      have ha := has_mem hB.2 (by decide); have ea := srcVal_of_has hB.2
      simp only [t0] at ha ea
      have hfn : (BitVec.ofNat 64 f0).toNat = f0 := toNat_ofNat_lt (by omega)
      refine WP_sound hfit _ _ (fun L2 m2 o2 => Reaches code ⟨pcOf (pos + (readHere x Lf pos fin).length + 1),
        L2, m2, o2⟩ _) L1 _ _ s2 (fun L2 m2 o2 h => by simpa using h) ?_
      wp_simp [ha, ea, hfn, hrd]
      refine ⟨by unfold LdOK; omega, ?_⟩
      refine reaches_mono (ih _ fb (gset L1 5 (BitVec.ofNat 64 fb)) _ (by simpa using hFb) s3
        (by reg_simp [])) ?_
      rintro B ⟨hm, ho, hk', hB'⟩
      exact ⟨hm, ho, hk.trans ((Keep.gset (Keep.refl _ L1) (by decide : 5 ∈ walkClob)).trans hk'), hB'⟩

end

end Vsa.Compiler
