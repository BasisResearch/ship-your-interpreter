import VsaIris.WhileLogic.WP

namespace Vsa.While.Logic

open Iris OFE CMRA BI Vsa.While

def globalFrame : Frame :=
  ⟨none, [("print", .native .print), ("println", .native .println),
    ("assert", .native .assert)]⟩

def initOwn : vProp := iprop(0 ↦f globalFrame ∗ outIs "")

theorem abs_initSt : abs initSt = singF 0 globalFrame • singO "" := by
  refine Prod.ext (funext fun a => ?_) (Prod.ext (funext fun c => ?_) rfl)
  · rcases a with _ | a
    · rfl
    · show (initSt.store.frames[a + 1]?).map Excl.excl = _
      simp [initSt, singF, singO]; rfl
  · show (initSt.store.closures[c]?).map Excl.excl = _
    simp [initSt, singF, singO]; rfl

def PostOut (Q : String → Prop) : Status → vProp :=
  fun st => iprop(⌜st = .normal⌝ ∧ ∃ o, ⌜Q o⌝ ∧ outIs o)

theorem adequacy {p : Program} {Φ : Status → vProp} (h : initOwn ⊢ wpSeq 0 0 p Φ) :
    ∃ st' status, ExecSeq initSt 0 0 p st' status ∧
      (Φ status).holds 0 ⟨abs st', abs_validN st' 0⟩ := by
  have hinit : initOwn.holds 0 ⟨abs initSt, abs_validN _ 0⟩ := by
    refine sep_holds.mpr ⟨singF 0 globalFrame, singO "", abs_initSt, ownM_self _ _ _,
      ownM_self _ _ _⟩
  obtain ⟨σ', st, r', hex, _, _, hrep, hΦ⟩ :=
    h 0 _ hinit initSt UCMRA.unit initSt_wf (by decide) unit_right_id.symm
  have : abs σ' = r' := hrep.trans unit_right_id
  subst this
  exact ⟨σ', st, hex, hΦ⟩

theorem adequacy_bigStep {p : Program} {Q : String → Prop}
    (h : initOwn ⊢ wpSeq 0 0 p (PostOut Q)) : ∃ out, BigStep p out ∧ Q out := by
  obtain ⟨σ', st, hex, hpost⟩ := adequacy h
  obtain ⟨hst, _, ⟨o, rfl⟩, hQ, hown⟩ := hpost
  obtain ⟨z, hz⟩ := ownM_holds.mp hown
  have hz : abs σ' = singO o • z := hz
  have hout := (rep_out hz (singO_out o)).1
  subst hst
  exact ⟨o, ⟨σ', hex, hout⟩, hQ⟩

end Vsa.While.Logic
