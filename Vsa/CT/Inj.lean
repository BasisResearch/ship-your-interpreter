import Vsa.CT.Typing

namespace Vsa.CT

open Vsa.While

theorem app_inj {α : Type} {a b c d : List α} (h : a.length = c.length) (e : a ++ b = c ++ d) :
    a = c ∧ b = d := List.append_inj e h

theorem two_inj {α : Type} {a c : List α} {b d : List α} {Q P : Prop}
    (h1 : a.length = c.length ∧ (a = c → Q)) (h2 : b.length = d.length ∧ (b = d → P)) :
    (a ++ b).length = (c ++ d).length ∧ (a ++ b = c ++ d → Q ∧ P) := by
  refine ⟨by simp [h1.1, h2.1], fun e => ?_⟩
  obtain ⟨e1, e2⟩ := app_inj h1.1 e
  exact ⟨h1.2 e1, h2.2 e2⟩

mutual

theorem EL.inj : ∀ (l1 l2 : EL), l1.skel = l2.skel →
    l1.outs.length = l2.outs.length ∧ (l1.outs = l2.outs → l1 = l2)
  | .leaf, l2, h => by cases l2 <;> simp_all [EL.skel, EL.outs]
  | .asg a, l2, h => by
    cases l2 <;> simp [EL.skel] at h
    obtain ⟨h1, h2⟩ := EL.inj a _ h
    exact ⟨by simpa [EL.outs] using h1, fun e => by simp only [EL.outs] at e; rw [h2 e]⟩
  | .bin a b d, l2, h => by
    cases l2 <;> simp [EL.skel] at h
    obtain ⟨ha, hb, rfl⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (EL.inj a _ ha) (EL.inj b _ hb)
    exact ⟨by simpa [EL.outs] using h1, fun e => by
      simp only [EL.outs] at e; obtain ⟨rfl, rfl⟩ := h2 e; rfl⟩
  | .orT a, l2, h => by
    cases l2 <;> simp [EL.skel] at h
    obtain ⟨h1, h2⟩ := EL.inj a _ h
    exact ⟨by simpa [EL.outs] using h1, fun e => by simp only [EL.outs] at e; rw [h2 e]⟩
  | .orF a b, l2, h => by
    cases l2 <;> simp [EL.skel] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (EL.inj a _ ha) (EL.inj b _ hb)
    exact ⟨by simpa [EL.outs] using h1, fun e => by
      simp only [EL.outs] at e; obtain ⟨rfl, rfl⟩ := h2 e; rfl⟩
  | .andF a, l2, h => by
    cases l2 <;> simp [EL.skel] at h
    obtain ⟨h1, h2⟩ := EL.inj a _ h
    exact ⟨by simpa [EL.outs] using h1, fun e => by simp only [EL.outs] at e; rw [h2 e]⟩
  | .andT a b, l2, h => by
    cases l2 <;> simp [EL.skel] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (EL.inj a _ ha) (EL.inj b _ hb)
    exact ⟨by simpa [EL.outs] using h1, fun e => by
      simp only [EL.outs] at e; obtain ⟨rfl, rfl⟩ := h2 e; rfl⟩
  | .un a, l2, h => by
    cases l2 <;> simp [EL.skel] at h
    obtain ⟨h1, h2⟩ := EL.inj a _ h
    exact ⟨by simpa [EL.outs] using h1, fun e => by simp only [EL.outs] at e; rw [h2 e]⟩
  | .call f as c, l2, h => by
    cases l2 <;> simp [EL.skel] at h
    obtain ⟨hf, ha, hc⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (two_inj (EL.inj f _ hf) (Es.inj as _ ha)) (CL.inj c _ hc)
    exact ⟨by simpa [EL.outs, List.append_assoc] using h1, fun e => by
      simp only [EL.outs] at e; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2 e; rfl⟩
  | .fn, l2, h => by cases l2 <;> simp_all [EL.skel, EL.outs]

theorem Es.inj : ∀ (l1 l2 : List EL), skelEs l1 = skelEs l2 →
    (outsEs l1).length = (outsEs l2).length ∧ (outsEs l1 = outsEs l2 → l1 = l2)
  | [], l2, h => by cases l2 <;> simp_all [skelEs, outsEs]
  | a :: as, l2, h => by
    cases l2 <;> simp [skelEs] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (EL.inj a _ ha) (Es.inj as _ hb)
    exact ⟨by simpa [outsEs] using h1, fun e => by
      simp only [outsEs] at e; obtain ⟨rfl, rfl⟩ := h2 e; rfl⟩

theorem CL.inj : ∀ (l1 l2 : CL), l1.skel = l2.skel →
    l1.outs.length = l2.outs.length ∧ (l1.outs = l2.outs → l1 = l2)
  | .clo b, l2, h => by
    cases l2 <;> simp [CL.skel] at h
    obtain ⟨h1, h2⟩ := Ss.inj b _ h
    exact ⟨by simpa [CL.outs] using h1, fun e => by simp only [CL.outs] at e; rw [h2 e]⟩
  | .print vs, l2, h => by cases l2 <;> simp_all [CL.skel, CL.outs]
  | .println vs, l2, h => by cases l2 <;> simp_all [CL.skel, CL.outs]
  | .assert, l2, h => by cases l2 <;> simp_all [CL.skel, CL.outs]

theorem SL.inj : ∀ (l1 l2 : SL), l1.skel = l2.skel →
    l1.outs.length = l2.outs.length ∧ (l1.outs = l2.outs → l1 = l2)
  | .expr a, l2, h => by
    cases l2 <;> simp [SL.skel] at h
    obtain ⟨h1, h2⟩ := EL.inj a _ h
    exact ⟨by simpa [SL.outs] using h1, fun e => by simp only [SL.outs] at e; rw [h2 e]⟩
  | .varInit a, l2, h => by
    cases l2 <;> simp [SL.skel] at h
    obtain ⟨h1, h2⟩ := EL.inj a _ h
    exact ⟨by simpa [SL.outs] using h1, fun e => by simp only [SL.outs] at e; rw [h2 e]⟩
  | .varNull, l2, h => by cases l2 <;> simp_all [SL.skel, SL.outs]
  | .block ss, l2, h => by
    cases l2 <;> simp [SL.skel] at h
    obtain ⟨h1, h2⟩ := Ss.inj ss _ h
    exact ⟨by simpa [SL.outs] using h1, fun e => by simp only [SL.outs] at e; rw [h2 e]⟩
  | .ifT c s, l2, h => by
    cases l2 <;> simp [SL.skel] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (EL.inj c _ ha) (SL.inj s _ hb)
    exact ⟨by simpa [SL.outs] using h1, fun e => by
      simp only [SL.outs] at e; obtain ⟨rfl, rfl⟩ := h2 e; rfl⟩
  | .ifF c s, l2, h => by
    cases l2 <;> simp [SL.skel] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (EL.inj c _ ha) (SL.inj s _ hb)
    exact ⟨by simpa [SL.outs] using h1, fun e => by
      simp only [SL.outs] at e; obtain ⟨rfl, rfl⟩ := h2 e; rfl⟩
  | .ifN c, l2, h => by
    cases l2 <;> simp [SL.skel] at h
    obtain ⟨h1, h2⟩ := EL.inj c _ h
    exact ⟨by simpa [SL.outs] using h1, fun e => by simp only [SL.outs] at e; rw [h2 e]⟩
  | .whileF c, l2, h => by
    cases l2 <;> simp [SL.skel] at h
    obtain ⟨h1, h2⟩ := EL.inj c _ h
    exact ⟨by simpa [SL.outs] using h1, fun e => by simp only [SL.outs] at e; rw [h2 e]⟩
  | .whileBrk c s, l2, h => by
    cases l2 <;> simp [SL.skel] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (EL.inj c _ ha) (SL.inj s _ hb)
    exact ⟨by simpa [SL.outs] using h1, fun e => by
      simp only [SL.outs] at e; obtain ⟨rfl, rfl⟩ := h2 e; rfl⟩
  | .whileRet c s, l2, h => by
    cases l2 <;> simp [SL.skel] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (EL.inj c _ ha) (SL.inj s _ hb)
    exact ⟨by simpa [SL.outs] using h1, fun e => by
      simp only [SL.outs] at e; obtain ⟨rfl, rfl⟩ := h2 e; rfl⟩
  | .whileLoop c s r, l2, h => by
    cases l2 <;> simp [SL.skel] at h
    obtain ⟨ha, hb, hr⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (two_inj (EL.inj c _ ha) (SL.inj s _ hb)) (SL.inj r _ hr)
    exact ⟨by simpa [SL.outs, List.append_assoc] using h1, fun e => by
      simp only [SL.outs] at e; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2 e; rfl⟩
  | .forS i lp, l2, h => by
    cases l2 <;> simp [SL.skel] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (OS.inj i _ ha) (FL.inj lp _ hb)
    exact ⟨by simpa [SL.outs] using h1, fun e => by
      simp only [SL.outs] at e; obtain ⟨rfl, rfl⟩ := h2 e; rfl⟩
  | .ret a, l2, h => by
    cases l2 <;> simp [SL.skel] at h
    obtain ⟨h1, h2⟩ := EL.inj a _ h
    exact ⟨by simpa [SL.outs] using h1, fun e => by simp only [SL.outs] at e; rw [h2 e]⟩
  | .retNull, l2, h => by cases l2 <;> simp_all [SL.skel, SL.outs]
  | .brk, l2, h => by cases l2 <;> simp_all [SL.skel, SL.outs]
  | .cont, l2, h => by cases l2 <;> simp_all [SL.skel, SL.outs]

theorem Ss.inj : ∀ (l1 l2 : List SL), skelSs l1 = skelSs l2 →
    (outsSs l1).length = (outsSs l2).length ∧ (outsSs l1 = outsSs l2 → l1 = l2)
  | [], l2, h => by cases l2 <;> simp_all [skelSs, outsSs]
  | a :: as, l2, h => by
    cases l2 <;> simp [skelSs] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (SL.inj a _ ha) (Ss.inj as _ hb)
    exact ⟨by simpa [outsSs] using h1, fun e => by
      simp only [outsSs] at e; obtain ⟨rfl, rfl⟩ := h2 e; rfl⟩

theorem OS.inj : ∀ (l1 l2 : Option SL), skelOS l1 = skelOS l2 →
    (outsOS l1).length = (outsOS l2).length ∧ (outsOS l1 = outsOS l2 → l1 = l2)
  | none, l2, h => by cases l2 <;> simp_all [skelOS, outsOS]
  | some a, l2, h => by
    cases l2 <;> simp [skelOS] at h
    obtain ⟨h1, h2⟩ := SL.inj a _ h
    exact ⟨by simpa [outsOS] using h1, fun e => by simp only [outsOS] at e; rw [h2 e]⟩

theorem OE.inj : ∀ (l1 l2 : Option EL), skelOE l1 = skelOE l2 →
    (outsOE l1).length = (outsOE l2).length ∧ (outsOE l1 = outsOE l2 → l1 = l2)
  | none, l2, h => by cases l2 <;> simp_all [skelOE, outsOE]
  | some a, l2, h => by
    cases l2 <;> simp [skelOE] at h
    obtain ⟨h1, h2⟩ := EL.inj a _ h
    exact ⟨by simpa [outsOE] using h1, fun e => by simp only [outsOE] at e; rw [h2 e]⟩

theorem FL.inj : ∀ (l1 l2 : FL), l1.skel = l2.skel →
    l1.outs.length = l2.outs.length ∧ (l1.outs = l2.outs → l1 = l2)
  | .condF c, l2, h => by
    cases l2 <;> simp [FL.skel] at h
    obtain ⟨h1, h2⟩ := EL.inj c _ h
    exact ⟨by simpa [FL.outs] using h1, fun e => by simp only [FL.outs] at e; rw [h2 e]⟩
  | .bodyBrk c b, l2, h => by
    cases l2 <;> simp [FL.skel] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (OE.inj c _ ha) (SL.inj b _ hb)
    exact ⟨by simpa [FL.outs] using h1, fun e => by
      simp only [FL.outs] at e; obtain ⟨rfl, rfl⟩ := h2 e; rfl⟩
  | .bodyRet c b, l2, h => by
    cases l2 <;> simp [FL.skel] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (OE.inj c _ ha) (SL.inj b _ hb)
    exact ⟨by simpa [FL.outs] using h1, fun e => by
      simp only [FL.outs] at e; obtain ⟨rfl, rfl⟩ := h2 e; rfl⟩
  | .loop c b s r, l2, h => by
    cases l2 <;> simp [FL.skel] at h
    obtain ⟨hc, hb, hs, hr⟩ := h
    obtain ⟨h1, h2⟩ := two_inj (two_inj (two_inj (OE.inj c _ hc) (SL.inj b _ hb)) (OE.inj s _ hs))
      (FL.inj r _ hr)
    exact ⟨by simpa [FL.outs, List.append_assoc] using h1, fun e => by
      simp only [FL.outs] at e; obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h2 e; rfl⟩

end

theorem skel_outs_inj {l1 l2 : List SL} (h1 : skelSs l1 = skelSs l2) (h2 : outsSs l1 = outsSs l2) :
    l1 = l2 := (Ss.inj l1 l2 h1).2 h2

end Vsa.CT
