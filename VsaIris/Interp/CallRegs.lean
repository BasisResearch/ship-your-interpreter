import VsaIris.Interp.NewlibCall

/-!
# Calling a function from a run, by its register list (lane H2)

A callee's spec names some registers: its arguments at values, the registers
it clobbers, the callee-saved ones it hands back. A symbolic run's state
(`ms`) holds one register valuation (`regFile R`). `regFile_cut` cuts it
into the callee's list `L` and the rest `K` (a permutation of `fRegs`, one
`decide` at the call site); `ms_callRegs` makes the call, keeps `K` at the
run's values and puts `L` back at whatever the callee left.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.MemRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The body's registers cut into `L` and the rest `K`. -/
theorem regFile_cut {L K : List Nat} (hp : fRegs.Perm (L ++ K)) (R : Nat → BitVec 64) :
    regFile (GF := GF) R ⊣⊢ iprop(sepL L (fun x => x ↦ᵣ R x) ∗ sepL K (fun x => x ↦ᵣ R x)) := by
  unfold regFile
  exact (sepL_perm _ hp).trans (sepL_append _ _ _)

/-- And back, with `L` at new values. -/
theorem regFile_uncut {L K : List Nat} (hp : fRegs.Perm (L ++ K)) (R f : Nat → BitVec 64) :
    iprop(sepL (GF := GF) L (fun x => x ↦ᵣ f x) ∗ sepL K (fun x => x ↦ᵣ R x)) ⊢
      regFile (fun x => if x ∈ L then f x else R x) := by
  have hnd : (L ++ K).Nodup := hp.nodup_iff.1 (by decide)
  obtain ⟨-, -, hdis⟩ := List.nodup_append.1 hnd
  refine .trans ?_ (regFile_cut hp _).2
  have eL : sepL (GF := GF) L (fun x => x ↦ᵣ (if x ∈ L then f x else R x)) =
      sepL L (fun x => x ↦ᵣ f x) := sepL_congr fun x hx => by simp [hx]
  have eK : sepL (GF := GF) K (fun x => x ↦ᵣ (if x ∈ L then f x else R x)) =
      sepL K (fun x => x ↦ᵣ R x) := sepL_congr fun x hx => by
    have : x ∉ L := fun h => hdis x h x hx rfl
    simp [this]
  rw [eL, eK]

variable {live : Nat → Prop}

/-- **A call from a run by the callee's register list** (`jal entry` at `i`):
`L` goes to the callee at the run's values with `X`; it returns `L` at some
values `f` with `Y f`; the run continues at `i + 4` with the rest kept. -/
theorem ms_callRegs (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalExec (vsaModel live) i code entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    {L K : List Nat} (hp : fRegs.Perm (L ++ K)) {P Q : BitVec 64 → IProp GF} {X : IProp GF}
    {Y : (Nat → BitVec 64) → IProp GF} {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem}
    (hP : iprop(sepL L (fun x => x ↦ᵣ R x) ∗ X) ⊢ P (BitVec.ofNat 64 (i + 4)))
    (hQ : Q (BitVec.ofNat 64 (i + 4)) ⊢ ∃ f : Nat → BitVec 64, sepL L (fun x => x ↦ᵣ f x) ∗ Y f) :
    fnSpecW Wp entry P Q ∗ codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗ X ∗
      (∀ f : Nat → BitVec 64, Y f -∗
        ms (BitVec.ofNat 64 (i + 4))
          (upd (fun x => if x ∈ L then f x else R x) 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  unfold ms
  iintro ⟨#Hspec, #Hcode, ⟨Hpc, Hra, Hregs, HS⟩, HX, Hk⟩
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave ⟨HL, HK⟩ := (regFile_cut hp R).1 $$ Hregs
  iapply wp_callW Wp hexec
  iframe Hi Hspec Hpc Hra
  isplitl [HL HX]
  · iapply hP
    iframe HL HX
  iintro Hpc Hra HQ
  ihave ⟨%f, HL, HY⟩ := hQ $$ HQ
  ihave Hregs := regFile_uncut hp R f $$ [HL HK]
  · iframe HL HK
  iapply Hk $$ %f HY
  rw [regFile_upd_ra]
  simp only [upd_same]
  iframe Hpc Hra Hregs HS

end

end VsaIris.Interp
