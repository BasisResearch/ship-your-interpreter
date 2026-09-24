import VsaIris.Vsa.StrlenSpec
import VsaIris.Vsa.BinImg

/-!
# Read-only bytes of a local run, owned instead; `strlen` on an owned buffer

H3's `strlen_specW` reads the string through persistent points-to (the
string's bytes are in the run's read-only `text`). A caller that owns the
string (a stack buffer, a fresh heap block: `stringify`, the concat rule)
must not give the bytes up. `LocalRun.promote` moves read-only cells of a
local run into its owned set: a segment never writes outside its owned set,
so the promoted bytes come back unchanged. `strlen_specOwnedW` is H3's run,
promoted.
-/

namespace VsaIris

variable {M : MachineModel}

/-- **Promoting read-only cells to owned ones.** The run holds with the
cells `t2` owned instead of read-only, and hands them back unchanged. -/
theorem LocalRun.promote {ro : List (Nat × BitVec 64)} {t1 t2 : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hd : ∀ p ∈ t2, ¬ S p.1) :
    ∀ n rv mv, LocalRun M ro (t1 ++ t2) rs S Q n rv mv → (∀ p ∈ t2, mv p.1 = p.2) →
      LocalRun M ro t1 rs (fun a => S a ∨ ∃ p ∈ t2, p.1 = a)
        (fun rv mv => Q rv mv ∧ ∀ p ∈ t2, mv p.1 = p.2) n rv mv
  | 0, _, _, h, ht => ⟨h, ht⟩
  | n + 1, rv, mv, h, ht => by
    rcases h with hQ | ⟨k, hseg⟩
    · exact .inl ⟨hQ, ht⟩
    · refine .inr ⟨k, fun σ hok hro hr hm => ?_⟩
      have hro' : ROHolds M σ ro (t1 ++ t2) := ⟨hro.1, fun p hp => by
        rcases List.mem_append.1 hp with h1 | h2
        · exact hro.2 p h1
        · rw [hm p.1 (.inr ⟨p, h2, rfl⟩)]; exact ht p h2⟩
      obtain ⟨σ', hreach, hok', hregs, hmem, hout, hK⟩ :=
        hseg σ hok hro' hr (fun a ha => hm a (.inl ha))
      refine ⟨σ', hreach, hok', hregs, fun a ha => hmem a (fun h => ha (.inl h)), hout, ?_⟩
      exact LocalRun.promote hd n _ _ hK (fun p hp => by
        rw [hmem p.1 (hd p hp), hm p.1 (.inr ⟨p, hp, rfl⟩)]; exact ht p hp)

end VsaIris

namespace VsaIris.Inst.Strlen

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.Sim Vsa.MemRepr VsaIris.Newlib

section Spec

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The string's bytes and the slack: `[P, P + len + 8)`. -/
def ownedStr (p len : Nat) (a : Nat) : Prop := p ≤ a ∧ a < p + len + 8

theorem ownedStr_iff (p len : Nat) (bv : Nat → BitVec 8) (a : Nat) :
    (slackSet p len a ∨ ∃ q ∈ strText p len bv, q.1 = a) ↔ ownedStr p len a := by
  unfold slackSet ownedStr strText
  constructor
  · rintro (h | ⟨q, hq, rfl⟩)
    · omega
    · simp only [List.mem_map, List.mem_range] at hq
      obtain ⟨k, hk, rfl⟩ := hq
      simp only; omega
  · intro h
    by_cases h' : a < p + len + 1
    · right
      refine ⟨(a, bv a), ?_, rfl⟩
      simp only [List.mem_map, List.mem_range]
      exact ⟨a - p, by omega, by rw [show p + (a - p) = a by omega]⟩
    · left; omega

/-- **`strlen(p)` on an owned string**, for either WP: H3's run with the
string's bytes owned and handed back unchanged, with the slack. -/
theorem strlen_specOwnedW {Φ : Nat × String → IProp GF} (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) {P r : BitVec 64} {len : Nat}
    {bv : Nat → BitVec 8} (ctx : Ctx live P r len bv) (v11 v12 v13 v14 v15 : BitVec 64) :
    instrAt codeBase strlenCode ∗
      VsaIris.PC ↦ᵣ 0x80006cf0#64 ∗ (1 : Nat) ↦ᵣ r ∗ (10 : Nat) ↦ᵣ P ∗ (11 : Nat) ↦ᵣ v11 ∗
      (12 : Nat) ↦ᵣ v12 ∗ (13 : Nat) ↦ᵣ v13 ∗ (14 : Nat) ↦ᵣ v14 ∗ (15 : Nat) ↦ᵣ v15 ∗
      ownSet (ownedStr P.toNat len) (fun a => a ↦ₘ bv a) ∗
      (VsaIris.PC ↦ᵣ r -∗ (1 : Nat) ↦ᵣ r -∗ (10 : Nat) ↦ᵣ BitVec.ofNat 64 len -∗
        clobbered [11, 12, 13, 14, 15] -∗
        ownSet (ownedStr P.toNat len) (fun a => a ↦ₘ bv a) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  have hd : ∀ q ∈ strText P.toNat len bv, ¬ slackSet P.toNat len q.1 := by
    intro q hq
    unfold strText at hq; unfold slackSet
    simp only [List.mem_map, List.mem_range] at hq
    obtain ⟨k, hk, rfl⟩ := hq
    simp only; omega
  have hrun := LocalRun.promote hd (len + 28) (entryRegs P r v11 v12 v13 v14 v15) bv
    (strlenRun ctx (fun _ _ => rfl) ⟨rfl, rfl, rfl⟩) (fun q hq => by
      unfold strText at hq
      simp only [List.mem_map, List.mem_range] at hq
      obtain ⟨k, _, rfl⟩ := hq; rfl)
  iintro ⟨#Hcode, Hpc, Hra, Ha0, H11, H12, H13, H14, H15, HS, Hk⟩
  iapply wp_localRunW Wp (ro := []) (text := codeText codeBase strlenCode)
    (rs := strlenRs) _ _ _ hrun
  isplitl []
  · unfold roOwn
    simp only [sepL_nil]
    isplitr
    · iempintro
    rw [← instrAt_text]
    iexact Hcode
  isplitl [Hpc Hra Ha0 H11 H12 H13 H14 H15]
  · rw [entryRegs_sepL]
    iframe Hpc Hra Ha0 H11 H12 H13 H14 H15
  isplitl [HS]
  · iapply ownSet_iff _ (fun a => (ownedStr_iff P.toNat len bv a).symm) $$ HS
  unfold runKontW
  iintro %rv' %mv' %⟨hQ, hT⟩ Hregs HS'
  ihave ⟨Hpc, Hra, Ha0, H11, H12, H13, H14, H15⟩ := postRegs_split rv' $$ Hregs
  ihave Hpc := reg_cast hQ.1 $$ Hpc
  ihave Hra := reg_cast hQ.2.1 $$ Hra
  ihave Ha0 := reg_cast hQ.2.2.1 $$ Ha0
  ihave HC := clobbered_five (GF := GF) (rv' 11) (rv' 12) (rv' 13) (rv' 14) (rv' 15)
    $$ [H11 H12 H13 H14 H15]
  · iframe H11 H12 H13 H14 H15
  ihave HS2 := ownSet_congr (S := fun a => slackSet P.toNat len a ∨
      ∃ q ∈ strText P.toNat len bv, q.1 = a) (f := fun a => iprop(a ↦ₘ mv' a))
    (g := fun a => iprop(a ↦ₘ bv a)) (fun a ha => by
      rcases ha with h | ⟨q, hq, rfl⟩
      · rw [hQ.2.2.2 a h]
      · rw [hT q hq]
        unfold strText at hq
        simp only [List.mem_map, List.mem_range] at hq
        obtain ⟨k, _, rfl⟩ := hq; rfl) $$ HS'
  ihave HS3 := ownSet_iff _ (fun a => ownedStr_iff P.toNat len bv a) $$ HS2
  iapply Hk $$ Hpc Hra Ha0 HC HS3

/-- `strlen`'s code is the image's. -/
theorem strlenCode_text : TextAt codeBase strlenCode := by decide +kernel

/-- **`strlen` on an owned buffer as a function spec**, for a call from a
run: the string's window `[P, P + len + 8)` owned (the string, its NUL, the
word loop's over-read), handed back unchanged, the length in `a0`. `live`
must hold the code (`CodeLive`) and the window. -/
theorem strlenOwned_fn (live : Nat → Prop) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {P : BitVec 64} {len : Nat} {bv : Nat → BitVec 8}
    (hreg : ReadRegions P len) (hstr : StrBytes P.toNat len bv)
    (hlv : ∀ k, k < len + 8 → live (P.toNat + k)) :
    binImg (GF := GF) ⊢ fnSpecW Wp 0x80006cf0#64
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ (10 : Nat) ↦ᵣ P ∗ clobbered [11, 12, 13, 14, 15] ∗
        ownSet (ownedStr P.toNat len) (fun a => a ↦ₘ bv a)))
      (fun _ => iprop((10 : Nat) ↦ᵣ BitVec.ofNat 64 len ∗ clobbered [11, 12, 13, 14, 15] ∗
        ownSet (ownedStr P.toNat len) (fun a => a ↦ₘ bv a))) := by
  have hcodeL : ∀ q ∈ strlenMR P.toNat len bv, live q.1 := by
    intro q hq
    unfold strlenMR memFoot at hq
    simp only [List.map_append, List.mem_append, List.mem_map] at hq
    rcases hq with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · unfold codeText at ht
      simp only [List.mem_map] at ht
      obtain ⟨z, hz, rfl⟩ := ht
      exact hcl _ (strlenCode_text z hz).1
    · unfold regionText at ht
      simp only [List.mem_map, List.mem_range] at ht
      obtain ⟨k, hk, rfl⟩ := ht
      exact hlv k hk
  iintro #Himg
  ihave #Hcode := instrAt_of_binImg strlenCode_text $$ Himg
  unfold fnSpecW
  imodintro
  iintro %r %Φ Hpc Hra ⟨%hal, Ha0, Hcl, HS⟩ Hk
  have ctx : Ctx live P r len bv := ⟨hreg, hstr, hal, hcodeL⟩
  ihave ⟨%f, Hcl⟩ := clobbered_fn [11, 12, 13, 14, 15] (by decide) $$ Hcl
  simp only [sepL_cons, sepL_nil]
  icases Hcl with ⟨H11, H12, H13, H14, H15, -⟩
  unfold VsaIris.ra
  iapply strlen_specOwnedW live Wp ctx (f 11) (f 12) (f 13) (f 14) (f 15)
  iframe Hcode Hpc Hra Ha0 H11 H12 H13 H14 H15 HS
  iintro Hpc Hra Ha0 Hcl HS
  iapply Hk $$ Hpc Hra
  iframe Ha0 Hcl HS

end Spec

end VsaIris.Inst.Strlen
