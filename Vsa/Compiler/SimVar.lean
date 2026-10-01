import Vsa.Compiler.SUpd
import Vsa.Compiler.R6Reg

namespace Vsa.Compiler

open Vsa.Sim Vsa.While LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

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

theorem read_here {H : CloMap} {m : Mem} {h f : Nat} {l : List String} {par : Nat} {fr : Frame}
    (hfa : FrameAt H m h f l par fr) (hfb : frameBase ≤ f) (hfe : f + 8 + 16 * l.length ≤ frameEnd)
    (hl : l.length ≤ 120) (x : String) (fin : Nat) (hfin : PosOK fin) {pos : Nat} {L : GRegs} {o : Array String}
    (hseg : Seg code pos (readHere x l pos fin)) (hP : PosOK (pos + (readHere x l pos fin).length))
    (h5 : Has L t0 (BitVec.ofNat 64 f)) :
    Reaches code ⟨pcOf pos, L, m, o⟩ (fun B => B.mem = m ∧ B.out = o ∧ Keep walkClob L B.regs ∧
      match lookupVar fr x with
      | some v => B.pc = pcOf fin ∧ InA H m h B.regs v
      | none => B.pc = pcOf (pos + (readHere x l pos fin).length) ∧ Has B.regs t0 (BitVec.ofNat 64 f)) := by
  obtain ⟨hb, he, ht⟩ := frame_consts
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
    wp_simp [h5.wp, hfn, hfn']
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
    cases hF0.symm.trans hFa
    obtain ⟨hf1, hf2, -, hf4⟩ := frame_bounds hs hF0
    rw [lookup_step hfr]
    simp only [walkCode] at hseg
    obtain ⟨⟨s1, p1⟩, s2, -⟩ := segP_app.mp ⟨hseg, seg_end_posOK hfit hseg (by simp)⟩
    refine ex_bind (read_here hfit (hs.frame a fr f0 Lf hfr hF0) hf1 hf2 hf4 x fin hfin s1 p1 h5) ?_
    rintro ⟨pc, L', m', o'⟩ ⟨rfl, rfl, hk, hB⟩
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
    obtain ⟨hb, he, ht⟩ := frame_consts
    cases hF0.symm.trans hFa
    have hfa := hs.frame a fr f0 Lf hfr hF0
    obtain ⟨hf1, hf2, -, hf4⟩ := frame_bounds hs hF0
    obtain ⟨fb, hFb⟩ := hcb.head
    obtain ⟨hb1, hb2, -, -⟩ := frame_bounds hs hFb
    have hrd : rdW m f0 = BitVec.ofNat 64 fb := by
      rw [hfa.parent]; simp only [parAddr, hpar, hFb, Option.map_some, Option.getD_some]
    rw [lookup_step hfr]
    simp only [walkCode, List.append_assoc] at hseg
    have h := And.intro hseg (seg_end_posOK hfit hseg (by simp))
    simp only [↓segP_app, List.length_cons, List.length_nil, Nat.zero_add] at h
    obtain ⟨⟨s1, p1⟩, ⟨s2, -⟩, s3, -⟩ := h
    refine ex_bind (read_here hfit hfa hf1 hf2 hf4 x fin hfin s1 p1 h5) ?_
    rintro ⟨pc, L1, m', o'⟩ ⟨rfl, rfl, hk, hB⟩
    cases hl : lookupVar fr x with
    | some v => simp only [hl] at hB ⊢; exact reach_here ⟨rfl, rfl, hk, hB⟩
    | none =>
      simp only [hl, hpar] at hB ⊢
      rw [hB.1, lookup_gas hs.parents x b a (hs.parents a fr b hfr hpar)]
      refine WP_sound hfit _ _ (fun L2 m2 o2 => Reaches code ⟨pcOf (pos + (readHere x Lf pos fin).length + 1),
        L2, m2, o2⟩ _) L1 _ _ s2 (fun L2 m2 o2 h => by simpa using h) ?_
      wp_simp [hB.2.wp, toNat_ofNat_lt, hrd]
      refine ⟨by unfold LdOK; omega, reaches_mono (ih _ fb _ _ (by simpa using hFb) s3
        (Has.set_self _ _ (by decide) (by decide))) ?_⟩
      rintro B ⟨hm, ho, hk', hB'⟩
      exact ⟨hm, ho, hk.trans ((Keep.gset (Keep.refl _ L1) (by decide : 5 ∈ walkClob)).trans hk'), hB'⟩

def writeClob : List Nat := [t0, t1, t2, t3]

theorem write_here {H : CloMap} {m : Mem} {h f : Nat} {l : List String} {par : Nat} {fr : Frame}
    (hfa : FrameAt H m h f l par fr) (hfb : frameBase ≤ f) (hfe : f + 8 + 16 * l.length ≤ frameEnd)
    (hl : l.length ≤ 120) (hal : f % 8 = 0) (x : String) (fin : Nat) (hfin : PosOK fin) {pos : Nat}
    {L : GRegs} {o : Array String} {t p : BitVec 64}
    (hseg : Seg code pos (writeHere x l pos fin)) (hP : PosOK (pos + (writeHere x l pos fin).length))
    (h5 : Has L t0 (BitVec.ofNat 64 f)) (h10 : Has L a0 t) (h11 : Has L a1 p) :
    Reaches code ⟨pcOf pos, L, m, o⟩ (fun B => B.out = o ∧ Keep writeClob L B.regs ∧
      match lookupVar fr x with
      | some _ => ∃ i, slotOf l x = some i ∧ B.pc = pcOf fin ∧
          B.mem = applyW (applyW m (f + 8 + 16 * i, 8, t)) (f + 8 + 16 * i + 8, 8, p)
      | none => B.pc = pcOf (pos + (writeHere x l pos fin).length) ∧ B.mem = m ∧
          Has B.regs t0 (BitVec.ofNat 64 f)) := by
  obtain ⟨hb, he, ht⟩ := frame_consts
  cases hsl : slotOf l x with
  | none =>
    have hn := lookupVar_none_of_not_mem hfa (slotOf_none hsl)
    refine reach_here ⟨rfl, Keep.refl _ _, ?_⟩
    simp only [hn, writeHere, hsl, List.length_nil, Nat.add_zero]
    exact ⟨by simp, by simp, h5⟩
  | some i =>
    have hi := slotOf_lt hsl
    have hLi := slotOf_some hsl
    simp only [writeHere, hsl, List.length_cons, List.length_nil] at hseg hP ⊢
    have hfn : (BitVec.ofNat 64 (f + (8 + 16 * i))).toNat = f + (8 + 16 * i) :=
      toNat_ofNat_lt (by omega)
    have hfn' : (BitVec.ofNat 64 (f + (8 + 16 * i) + 8)).toNat = f + (8 + 16 * i) + 8 :=
      toNat_ofNat_lt (by omega)
    apply run_jumps hfit hseg
    wp_simp [h5.wp, h10.wp, h11.wp, hfn, hfn']
    have e1 : f + (8 + 16 * i) = f + 8 + 16 * i := by omega
    rw [e1]
    refine ⟨by unfold LdOK; omega, ?_⟩
    split
    · next h6 =>
      have hn : lookupVar fr x = none := by
        cases hl : lookupVar fr x with
        | none => rfl
        | some v => exact absurd h6 (hfa.bound i x v hLi hl).tag_ne6
      refine reach_here ⟨rfl, ?_, ?_⟩
      · reg_simp [writeClob]
        exact Keep.refl _ _
      · simp only [hn]
        exact ⟨by simp, by simp, by reg_simp []; exact h5⟩
    · next h6 =>
      cases hl : lookupVar fr x with
      | none => exact absurd (hfa.unbound i x hLi hl) h6
      | some v =>
        rw [if_neg (by omega), if_neg (by omega)]
        refine ⟨by unfold StOK; omega, by unfold StOK; omega, reach_here ⟨rfl, ?_, i, rfl, rfl, rfl⟩⟩
        reg_simp [writeClob]
        exact Keep.refl _ _

theorem walk_write {F : FrMap} {H : CloMap} {s : Store} {m : Mem} {hF h : Nat} (hs : StoreRel F H s m hF h)
    (x : String) (fin : Nat) (hfin : PosOK fin) {v : Value} {t p : BitVec 64} (hv : VRepr H m h v t p) :
    ∀ {a : Addr} {Γ : List (List String)}, ChainL F s a Γ → ∀ (pos f : Nat) (L : GRegs)
      (o : Array String), F[a]? = some (f, Γ.headD []) →
      Seg code pos (walkCode (fun l p => writeHere x l p fin) pos Γ) → Has L t0 (BitVec.ofNat 64 f) →
      Has L a0 t → Has L a1 p →
      Reaches code ⟨pcOf pos, L, m, o⟩ (fun B => B.out = o ∧ Keep writeClob L B.regs ∧
        match s.set (a + 1) a x v with
        | some s' => B.pc = pcOf fin ∧ SetPost F H s m hF h s' B.mem
        | none => B.pc = pcOf errPos ∧ B.mem = m) := by
  intro a Γ hc
  induction hc with
  | @top a fr f0 Lf hfr hpar hF0 =>
    intro pos f L o hFa hseg h5 h10 h11
    simp only [List.headD_cons] at hFa
    have hff : f0 = f := by rw [hF0] at hFa; cases hFa; rfl
    subst hff
    have hfa := hs.frame a fr f0 Lf hfr hF0
    obtain ⟨hf1, hf2, hf3, hf4⟩ := frame_bounds hs hF0
    rw [set_step hfr]
    simp only [walkCode] at hseg
    obtain ⟨⟨s1, p1⟩, s2, -⟩ := segP_app.mp ⟨hseg, seg_end_posOK hfit hseg (by simp)⟩
    refine ex_bind (write_here hfit hfa hf1 hf2 hf4 hf3 x fin hfin s1 p1 h5 h10 h11) ?_
    rintro B ⟨ho, hk, hB⟩
    obtain ⟨pc, L', m', o'⟩ := B
    simp only at ho hk hB; subst ho
    cases hl : lookupVar fr x with
    | some w =>
      simp only [hl] at hB ⊢
      obtain ⟨i, hsl, hpc, hm⟩ := hB
      subst hm
      exact reach_here ⟨rfl, hk, by simp only [Option.isSome_some, if_true]; exact
        ⟨hpc, setPost_of_slot hs hfr hF0 hsl hv (by simp [hl])⟩⟩
    | none =>
      simp only [hl, hpar] at hB ⊢
      obtain ⟨hpc, hm, -⟩ := hB
      subst hm
      rw [hpc]
      apply run_jumps hfit s2
      wp_simp []
      exact reach_here ⟨rfl, hk, by simp⟩
  | @cons a b fr f0 Lf L' g hfr hpar hF0 hcb ih =>
    intro pos f L o hFa hseg h5 h10 h11
    obtain ⟨hb, he, ht⟩ := frame_consts
    simp only [List.headD_cons] at hFa
    have hff : f0 = f := by rw [hF0] at hFa; cases hFa; rfl
    subst hff
    have hfa := hs.frame a fr f0 Lf hfr hF0
    obtain ⟨hf1, hf2, hf3, hf4⟩ := frame_bounds hs hF0
    obtain ⟨fb, hFb⟩ := hcb.head
    obtain ⟨hb1, hb2, -, -⟩ := frame_bounds hs hFb
    have hba : b < a := hs.parents a fr b hfr hpar
    have hpa : parAddr F fr = fb := by simp only [parAddr, hpar, hFb, Option.map_some, Option.getD_some]
    have hrd : rdW m f0 = BitVec.ofNat 64 fb := by rw [hfa.parent, hpa]
    rw [set_step hfr]
    simp only [walkCode, List.append_assoc] at hseg
    have h := And.intro hseg (seg_end_posOK hfit hseg (by simp))
    simp only [↓segP_app, List.length_cons, List.length_nil, Nat.zero_add] at h
    obtain ⟨⟨s1, p1⟩, ⟨s2, -⟩, s3, -⟩ := h
    refine ex_bind (write_here hfit hfa hf1 hf2 hf4 hf3 x fin hfin s1 p1 h5 h10 h11) ?_
    rintro B ⟨ho, hk, hB⟩
    obtain ⟨pc, L1, m', o'⟩ := B
    simp only at ho hk hB; subst ho
    cases hl : lookupVar fr x with
    | some w =>
      simp only [hl] at hB ⊢
      obtain ⟨i, hsl, hpc, hm⟩ := hB
      subst hm
      exact reach_here ⟨rfl, hk, by simp only [Option.isSome_some, if_true]; exact
        ⟨hpc, setPost_of_slot hs hfr hF0 hsl hv (by simp [hl])⟩⟩
    | none =>
      simp only [hl, hpar] at hB ⊢
      obtain ⟨hpc, hm, h5'⟩ := hB
      subst hm
      rw [hpc, set_gas hs.parents x v b a hba]
      have hfn : (BitVec.ofNat 64 f0).toNat = f0 := toNat_ofNat_lt (by omega)
      refine WP_sound hfit _ _ (fun L2 m2 o2 => Reaches code ⟨pcOf (pos + (writeHere x Lf pos fin).length + 1),
        L2, m2, o2⟩ _) L1 _ _ s2 (fun L2 m2 o2 h => by simpa using h) ?_
      wp_simp [h5'.wp, hfn, hrd]
      refine ⟨by unfold LdOK; omega, ?_⟩
      refine reaches_mono (ih _ fb (gset L1 5 (BitVec.ofNat 64 fb)) _ (by simpa using hFb) s3
        (by reg_simp []) (by reg_simp []; exact hk.has (by decide) h10)
        (by reg_simp []; exact hk.has (by decide) h11)) ?_
      rintro B ⟨ho, hk', hB'⟩
      exact ⟨ho, hk.trans ((Keep.gset (Keep.refl _ L1) (by decide : 5 ∈ writeClob)).trans hk'), hB'⟩

end

end Vsa.Compiler
