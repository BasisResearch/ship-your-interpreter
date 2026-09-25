import VsaIris.Vsa.Newlib
import VsaIris.Interp.Arm

/-!
# A newlib call's registers as one register file (lane N3)

The newlib specs (`Newlib.lean`) hand their callee the argument registers
(`argsAt`) and the call frame's `sp`, saved registers and temporaries
(`callFrame`). A symbolic run owns them as one register file (`regFile`,
every GPR but `gp`/`tp`). `regFile_of_call` assembles it (the arguments at
their values, the saved registers at `cs`, `sp = s`, the rest at whatever
values they held); `call_of_regFile` takes a returning run's register file
back apart (`sp` and the saved registers as it keeps them, the arguments and
temporaries clobbered).
-/

namespace VsaIris.Newlib

open Iris Iris.BI Iris.Std Iris.ProofMode
open VsaIris VsaIris.Interp

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem clobbered_fn (rs : List Nat) (hnd : rs.Nodup) :
    clobbered (GF := GF) rs ⊢ ∃ f : Nat → BitVec 64, sepL rs (fun r => r ↦ᵣ f r) :=
  sepL_exists_fn (fun r v => iprop(r ↦ᵣ v)) rs hnd

/-- The register file a call starts from. -/
def callRegs (s : BitVec 64) (cs ft fa : Nat → BitVec 64) (x : Nat) : BitVec 64 :=
  if x = 2 then s else if x ∈ calleeSaved then cs x else if x ∈ tmpRegs then ft x else fa x

theorem fRegs_perm : fRegs.Perm (2 :: calleeSaved ++ tmpRegs ++ argRegs) := by decide

theorem regFile_split (rv : Nat → BitVec 64) :
    regFile (GF := GF) rv ⊣⊢ iprop((2 : Nat) ↦ᵣ rv 2 ∗ sepL calleeSaved (fun r => r ↦ᵣ rv r) ∗
      sepL tmpRegs (fun r => r ↦ᵣ rv r) ∗ sepL argRegs (fun r => r ↦ᵣ rv r)) := by
  unfold regFile
  refine (VsaIris.Inst.sepL_perm _ fRegs_perm).trans ?_
  rw [List.cons_append, List.cons_append, sepL_cons]
  refine sep_congr_right ?_
  refine (sepL_append _ _ _).trans ?_
  refine (sep_congr_left (sepL_append _ _ _)).trans ?_
  exact sep_assoc

/-- **The call's registers as one register file.** -/
theorem regFile_of_call (s : BitVec 64) (cs ft fa : Nat → BitVec 64) :
    iprop((2 : Nat) ↦ᵣ s ∗ sepL calleeSaved (fun r => r ↦ᵣ cs r) ∗ sepL tmpRegs (fun r => r ↦ᵣ ft r) ∗
      sepL argRegs (fun r => r ↦ᵣ fa r)) ⊢@{IProp GF} regFile (callRegs s cs ft fa) := by
  refine .trans ?_ (regFile_split _).2
  have h2 : callRegs s cs ft fa 2 = s := by simp [callRegs]
  have hs : sepL (GF := GF) calleeSaved (fun r => r ↦ᵣ cs r) =
      sepL calleeSaved (fun r => r ↦ᵣ callRegs s cs ft fa r) :=
    sepL_congr fun x hx => by
      have : x ≠ 2 := fun e => by subst e; revert hx; decide
      simp [callRegs, this, hx]
  have ht : sepL (GF := GF) tmpRegs (fun r => r ↦ᵣ ft r) =
      sepL tmpRegs (fun r => r ↦ᵣ callRegs s cs ft fa r) :=
    sepL_congr fun x hx => by
      have h1 : x ≠ 2 := fun e => by subst e; revert hx; decide
      have h2 : x ∉ calleeSaved := by simp [tmpRegs, calleeSaved] at hx ⊢; omega
      simp [callRegs, h1, h2, hx]
  have ha : sepL (GF := GF) argRegs (fun r => r ↦ᵣ fa r) =
      sepL argRegs (fun r => r ↦ᵣ callRegs s cs ft fa r) :=
    sepL_congr fun x hx => by
      have h1 : x ≠ 2 := fun e => by subst e; revert hx; decide
      have h2 : x ∉ calleeSaved := by simp [argRegs, calleeSaved] at hx ⊢; omega
      have h3 : x ∉ tmpRegs := by simp [argRegs, tmpRegs] at hx ⊢; omega
      simp [callRegs, h1, h2, h3]
  rw [h2, hs, ht, ha]

/-- Four arguments (`fwrite`'s), the other argument registers at some
values. -/
theorem argsAt4_fn (v0 v1 v2 v3 : BitVec 64) :
    argsAt (GF := GF) [v0, v1, v2, v3] ⊢ ∃ fa : Nat → BitVec 64,
      sepL argRegs (fun r => r ↦ᵣ fa r) ∗ ⌜fa 10 = v0 ∧ fa 11 = v1 ∧ fa 12 = v2 ∧ fa 13 = v3⌝ := by
  unfold argsAt
  simp only [List.zipIdx, List.zipIdx_cons, List.zipIdx_nil, sepL_cons, sepL_nil, List.length_cons,
    List.length_nil]
  iintro ⟨⟨H0, H1, H2, H3, -⟩, Hc⟩
  ihave ⟨%f, Hc⟩ := clobbered_fn (argRegs.drop 4) (by decide) $$ Hc
  iexists (fun x => if x = 10 then v0 else if x = 11 then v1 else if x = 12 then v2 else
    if x = 13 then v3 else f x)
  simp only [argRegs, List.drop, sepL_cons, sepL_nil]
  isplitl
  · simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
    iframe H0 H1 H2 H3 Hc
  · ipureintro; simp

end

end VsaIris.Newlib
