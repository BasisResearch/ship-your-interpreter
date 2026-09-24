import VsaIris.Interp.ErrArm
import VsaIris.Interp.SpecEnv

/-!
# `value_equal` from an `eval_expr` run (lane E2)

The `==`/`!=` arms (`0x800036e4`, `0x80003734`) copy both operands into two
frame slots (`sp + 64`, `sp + 32`) and call `value_equal(&l, &r)` (H2's
`valueEqualSpec`), which also reads the store (closures by address) and
borrows 16 bytes of stack for `strcmp`. `ms_callValueEqual` is that call from
a run: the two slots are carved out of the run's owned bytes as the values
(their meaning is `valOf` of the stored words), the store comes out of the
world (`world_store`), and all of it is handed back.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The prologue's spills survive a memory that agrees on them. -/
theorem EvalSaved.agree {M M' : Mem} {s ret v8 v9 v18 v19 : BitVec 64}
    (h : EvalSaved M s ret v8 v9 v18 v19)
    (hag : ∀ k, s.toNat - 1088 + 1048 ≤ k → k < s.toNat - 1088 + 1088 → imgM M' k = imgM M k) :
    EvalSaved M' s ret v8 v9 v18 v19 :=
  ⟨(ldv_agree fun j hj => hag _ (by omega) (by omega)).trans h.ra,
   (ldv_agree fun j hj => hag _ (by omega) (by omega)).trans h.s0,
   (ldv_agree fun j hj => hag _ (by omega) (by omega)).trans h.s1,
   (ldv_agree fun j hj => hag _ (by omega) (by omega)).trans h.s2,
   (ldv_agree fun j hj => hag _ (by omega) (by omega)).trans h.s3⟩

/-- A value slot of a run's owned bytes, out as the value (its words are those
`valOf` speaks of), with the rest of the run. -/
theorem ms_carveWords (N : NativeAddrs) {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop}
    {Mt : Mem} {p w0 w1 w2 : BitVec 64} {v : Value} (hS : ∀ k, InExt (p.toNat, 24) k → S k)
    (h0 : ldv .ld Mt p.toNat = w0) (h8 : ldv .ld Mt (p.toNat + 8) = w1)
    (h16 : ldv .ld Mt (p.toNat + 16) = w2) :
    ms (GF := GF) pc R S Mt ∗ □ valOf N v w0 w1 w2 ⊢
      ms pc R (fun k => S k ∧ ¬ InExt (p.toNat, 24) k) Mt ∗ valAt N p.toNat v := by
  rw [ldv_ld_imgW] at h0 h8 h16
  have e : valOf (GF := GF) N v w0 w1 w2 = valImg N (imgM Mt) p.toNat v := by
    unfold valImg; rw [h0, h8, h16]
  rw [e]
  iintro ⟨Hms, #Hv⟩
  iapply ms_carveVal N (a := p.toNat) (b := p.toNat) (img := imgM Mt) hS rfl rfl rfl $$ [Hms Hv]
  iframe Hms Hv

/-- **`value_equal` from a run** (`jal` at `i`) on the two operand copies the
run stored at `pa` and `pb` (disjoint slots of its owned bytes), with `sp = sp`
and 16 bytes of stack below it. -/
theorem ms_callValueEqual (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs}
    (hve : ⊢ ∀ pa pb s a b st B, valueEqualSpec (vsaModel live) N Wp pa pb s a b st B)
    {i : Nat} {code : List (BitVec 8)} (hexec : JalExec (vsaModel live) i code valueEqualPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {pa pb sp : BitVec 64} {a b : Value}
    {wa0 wa1 wa2 wb0 wb1 wb2 : BitVec 64} {st : Store} {B : List (Nat × Nat)}
    (hSa : ∀ k, InExt (pa.toNat, 24) k → S k) (hSb : ∀ k, InExt (pb.toNat, 24) k → S k)
    (hab : ∀ k, InExt (pa.toNat, 24) k → ¬ InExt (pb.toNat, 24) k)
    (hga : SlotGeom pa) (hgb : SlotGeom pb) (hni : NativeInj N)
    (ha0 : ldv .ld Mt pa.toNat = wa0) (ha8 : ldv .ld Mt (pa.toNat + 8) = wa1)
    (ha16 : ldv .ld Mt (pa.toNat + 16) = wa2)
    (hb0 : ldv .ld Mt pb.toNat = wb0) (hb8 : ldv .ld Mt (pb.toNat + 8) = wb1)
    (hb16 : ldv .ld Mt (pb.toNat + 16) = wb2) :
    ⌜R 10 = pa ∧ R 11 = pb ∧ R 2 = sp⌝ ∗ codeRes ∗ □ valOf N a wa0 wa1 wa2 ∗
      □ valOf N b wb0 wb1 wb2 ∗ ms (BitVec.ofNat 64 i) R S Mt ∗ storeRepr N st B ∗
      stackAt sp 16 ∗ strcmpSpecV (vsaModel live) Wp ∗
      (∀ (R' : Nat → BitVec 64) (M' : Mem), ⌜∀ x ∈ fRegs, x ∉ callerSaved → R' x = R x⌝ -∗
        ⌜R' 10 = if Value.equal a b then 1#64 else 0#64⌝ -∗
        ⌜∀ k, S k → ¬ InExt (pa.toNat, 24) k → ¬ InExt (pb.toNat, 24) k → imgM M' k = imgM Mt k⌝ -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S M' -∗
        storeRepr N st B -∗ stackAt sp 16 -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨%⟨h10, h11, h2⟩, #Hcode, #Hva, #Hvb, Hms, Hst, Hsk, #Hcmp, Hk⟩
  ihave ⟨Hms, HA⟩ := ms_carveWords N hSa ha0 ha8 ha16 $$ [Hms Hva]
  · iframe Hms Hva
  ihave ⟨Hms, HB⟩ := ms_carveWords N (S := fun k => S k ∧ ¬ InExt (pa.toNat, 24) k)
    (fun k hk => ⟨hSb k hk, fun h => hab k h hk⟩) hb0 hb8 hb16 $$ [Hms Hvb]
  · iframe Hms Hvb
  ihave Hspec := hve $$ %pa %pb %sp %a %b %st %B
  unfold valueEqualSpec
  iapply ms_callHelper Wp hexec hcode hal
  iframe Hspec Hcode Hms
  isplitl []
  · ipureintro; exact ⟨h10, h11, h2⟩
  isplitl [HA HB Hst Hsk]
  · iframe HA HB Hst Hsk Hcmp; ipureintro; exact ⟨hga, hgb, hni⟩
  iintro %R' %hkeep ⟨HA, HB, Hst, Hsk, %hr⟩ Hms
  ihave ⟨%M1, Hms, %hM1⟩ := ms_uncarveVal N (S := fun k => S k ∧ ¬ InExt (pa.toNat, 24) k)
    (fun k hk => ⟨hSb k hk, fun h => hab k h hk⟩) $$ [Hms HB]
  · iframe Hms HB
  have hiff : ∀ k, ((S k ∧ ¬ InExt (pa.toNat, 24) k) ∧ ¬ InExt (pb.toNat, 24) k ∨
      InExt (pb.toNat, 24) k) ↔ (S k ∧ ¬ InExt (pa.toNat, 24) k) := fun k => by
    constructor
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact ⟨hSb k h, fun h' => hab k h' h⟩
    · intro h; by_cases h' : InExt (pb.toNat, 24) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
  ihave ⟨%M2, Hms, %hM2⟩ := ms_uncarveVal N hSa $$ [Hms HA]
  · iframe Hms HA
  iapply Hk $$ %R' %M2 %hkeep %hr
    %(fun k hk ha hb => (hM2 k hk ha).trans (hM1 k ⟨hk, ha⟩ hb)) Hms Hst Hsk

end

end VsaIris.Interp
