import VsaIris.WhileLogic.WP

/-!
# Adequacy of the WHILE program logic

A program proved in the logic from the initial resources `initOwn` (the
global frame with the three natives bound, and the empty console) has a
big-step behaviour, and its output satisfies the postcondition
(`adequacy`, `adequacy_bigStep`). `Machine.lean` composes this with
`endToEnd_refinement`.
-/

namespace Vsa.While.Logic

open Iris OFE CMRA BI Vsa.While

/-- The global frame of `initSt`: no parent, the three natives bound. -/
def globalFrame : Frame :=
  ⟨none, [("print", .native .print), ("println", .native .println),
    ("assert", .native .assert)]⟩

/-- The initial resources: the global frame (address `0`) and the empty
console. -/
def initOwn : vProp := iprop(0 ↦f globalFrame ∗ outIs "")

theorem abs_initSt : abs initSt = singF 0 globalFrame • singO "" := by
  refine Prod.ext (funext fun a => ?_) (Prod.ext (funext fun c => ?_) rfl)
  · rcases a with _ | a
    · rfl
    · show (initSt.store.frames[a + 1]?).map Excl.excl = _
      simp [initSt, singF, singO]; rfl
  · show (initSt.store.closures[c]?).map Excl.excl = _
    simp [initSt, singF, singO]; rfl

/-- The postcondition "finished normally, console satisfies `Q`". -/
def PostOut (Q : String → Prop) : Status → vProp :=
  fun st => iprop(⌜st = .normal⌝ ∧ ∃ o, ⌜Q o⌝ ∧ outIs o)

/-- **Adequacy (big-step).** A proof from `initOwn` of a program's weakest
precondition yields a big-step execution whose final state satisfies the
postcondition. -/
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

/-- **Adequacy (output).** A proved triple `{initOwn} p {PostOut Q}` gives a
big-step behaviour of `p` whose output satisfies `Q`. -/
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
