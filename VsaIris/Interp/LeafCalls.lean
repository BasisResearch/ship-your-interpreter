import VsaIris.Interp.LeafArm
import VsaIris.Interp.CallMalloc

/-!
# Result slots and `env_*` calls from an `eval_expr` run (lane E1)

The `var`, `assign` and `fn` arms store their result into `sret`
themselves (no helper writes it), so their runs own the result slot beside
the frame: `ms_intro_sret` joins `slot24 sret` into the machine state's
owned bytes, `ms_exit_sret`/`ms_exit_sretAny` split it off again, as a
represented value or at any contents (an abort hands the slot back).
`env_get` writes its `out` slot inside the frame: `ms_carveSlot` lends it,
`ms_joinSlot`/`ms_unslot` take it back (found value or not).

`ms_callEnv3` calls a helper whose spec is in `env_get`/`env_set`'s register
form (arguments `a0`-`a2` at the run's values, `sp`, the argument
registers clobbered, `s0`-`s6` saved, a result in `a0`), by `ms_callRegs`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.MemRepr Vsa.While Vsa.RuntimeRepr

section Slots

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- An arm's owned bytes: its frame `[f, f + 1088)` and the result slot. -/
abbrev frS (f a : Nat) : Nat → Prop := fun b => InExt (f, 1088) b ∨ InExt (a, 24) b

/-- **Entering an arm that writes `sret`**: the frame bytes and the result
slot become the machine state's owned bytes, at some tracking memory; they
are disjoint. -/
theorem ms_intro_sret {pc r : BitVec 64} {R : Nat → BitVec 64} {f a : Nat} :
    PC ↦ᵣ pc ∗ ra ↦ᵣ r ∗ regFile R ∗ ownSet (InExt (f, 1088)) byteAny ∗ slot24 a ⊢@{IProp GF}
      ∃ Mt, ms pc (upd R 1 r) (frS f a) Mt ∗ ⌜∀ b, InExt (f, 1088) b → ¬ InExt (a, 24) b⌝ := by
  unfold slot24 blockOwn
  iintro ⟨Hpc, Hra, Hregs, HF, HA⟩
  ihave ⟨%g1, HF⟩ := ownSet_fn _ $$ HF
  ihave ⟨%M1, HF⟩ := ownSet_mem _ g1 $$ HF
  ihave ⟨%g2, HA⟩ := ownSet_fn _ $$ HA
  ihave ⟨%M2, HA⟩ := ownSet_mem _ g2 $$ HA
  ihave ⟨%M, HS, %⟨-, -, hd⟩⟩ := ownSet_join_tracked _ _ M1 M2 $$ [HF HA]
  · iframe HF HA
  iexists M
  unfold ms
  rw [regFile_upd_ra]
  simp only [upd_same]
  iframe Hpc Hra Hregs HS
  ipureintro; exact hd

/-- Two ranges disjoint pointwise are disjoint as intervals. -/
theorem inExt_disj {a n c k : Nat} (hn : 0 < n) (hk : 0 < k)
    (h : ∀ b, InExt (a, n) b → ¬ InExt (c, k) b) : a + n ≤ c ∨ c + k ≤ a := by
  apply Classical.byContradiction; intro hc
  simp only [not_or, Nat.not_le] at hc
  exact h (max a c) (by simp only [InExt]; omega) (by simp only [InExt]; omega)

omit I in
/-- **Leaving it, the slot at any contents** (an abort hands the slot back). -/
theorem ms_exit_sretAny {pc : BitVec 64} {R : Nat → BitVec 64} {f a : Nat} {Mt : Mem}
    (hd : ∀ b, InExt (f, 1088) b → ¬ InExt (a, 24) b) :
    ms pc R (frS f a) Mt ⊢@{IProp GF}
      PC ↦ᵣ pc ∗ ra ↦ᵣ R 1 ∗ regFile R ∗ ownSet (InExt (f, 1088)) byteAny ∗ slot24 a := by
  iintro Hms
  ihave ⟨Hms, HA⟩ := ms_split hd $$ Hms
  ihave ⟨Hpc, Hra, Hregs, HF⟩ := ms_exit $$ Hms
  iframe Hpc Hra Hregs HF
  unfold slot24 blockOwn
  iapply ownSet_forget $$ HA

/-- **Leaving it with the result**: the slot's bytes at the end memory
represent `v`. -/
theorem ms_exit_sret (N : NativeAddrs) {pc : BitVec 64} {R : Nat → BitVec 64} {f a : Nat}
    {Mt : Mem} {v : Value} (hd : ∀ b, InExt (f, 1088) b → ¬ InExt (a, 24) b) :
    ms pc R (frS f a) Mt ∗ valImg N (imgM Mt) a v ⊢@{IProp GF}
      PC ↦ᵣ pc ∗ ra ↦ᵣ R 1 ∗ regFile R ∗ ownSet (InExt (f, 1088)) byteAny ∗ valAt N a v := by
  iintro ⟨Hms, Hv⟩
  ihave ⟨Hms, HA⟩ := ms_split hd $$ Hms
  ihave ⟨Hpc, Hra, Hregs, HF⟩ := ms_exit $$ Hms
  iframe Hpc Hra Hregs HF
  iapply valAt_of_img N $$ [Hv HA]
  iframe Hv HA

/-- Lend a 24-byte slot of the owned bytes (a callee's `out` argument). -/
theorem ms_carveSlot {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {a : Nat}
    (h : ∀ b, InExt (a, 24) b → S b) :
    ms pc R S Mt ⊢@{IProp GF} ms pc R (fun b => S b ∧ ¬ InExt (a, 24) b) Mt ∗ slot24 a := by
  unfold ms
  iintro ⟨Hpc, Hra, Hregs, HS⟩
  ihave ⟨HS, Hsl⟩ := ownSet_carve_slot h $$ HS
  iframe Hpc Hra Hregs HS Hsl

/-- Take it back holding a represented value: the tracking memory gets the
slot's three words, whose meaning is `valOf`. -/
theorem ms_joinSlot (N : NativeAddrs) {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop}
    {Mt : Mem} {a : Nat} {v : Value} (h : ∀ b, InExt (a, 24) b → S b) :
    ms pc R (fun b => S b ∧ ¬ InExt (a, 24) b) Mt ∗ valAt N a v ⊢@{IProp GF}
      ∃ w0 w1 w2, □ valOf N v w0 w1 w2 ∗ ms pc R S (slotWrite Mt a w0 w1 w2) := by
  unfold ms
  iintro ⟨⟨Hpc, Hra, Hregs, HS⟩, Hv⟩
  ihave ⟨%w0, %w1, %w2, #Hw, HS⟩ := ownSet_join_slot h $$ [HS Hv]
  · iframe HS Hv
  iexists w0, w1, w2
  iframe Hw Hpc Hra Hregs HS

/-- Take it back at any contents. -/
theorem ms_unslot {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {a : Nat}
    (h : ∀ b, InExt (a, 24) b → S b) :
    ms pc R (fun b => S b ∧ ¬ InExt (a, 24) b) Mt ∗ slot24 a ⊢@{IProp GF} ∃ Mt', ms pc R S Mt' := by
  unfold ms
  iintro ⟨⟨Hpc, Hra, Hregs, HS⟩, Hsl⟩
  ihave HS := ownSet_unslot h $$ [HS Hsl]
  · iframe HS Hsl
  ihave ⟨%g, HS⟩ := ownSet_fn _ $$ HS
  ihave ⟨%M, HS⟩ := ownSet_mem _ g $$ HS
  iexists M
  iframe Hpc Hra Hregs HS

/-- **Joining the result slot later** (an arm that calls a child first): the
frame's machine state takes the slot in, at a tracking memory agreeing on the
frame. -/
theorem ms_join_sret {pc : BitVec 64} {R : Nat → BitVec 64} {f a : Nat} {Mt : Mem} :
    ms pc R (InExt (f, 1088)) Mt ∗ slot24 a ⊢@{IProp GF}
      ∃ M', ms pc R (frS f a) M' ∗ ⌜(∀ b, InExt (f, 1088) b → imgM M' b = imgM Mt b) ∧
        ∀ b, InExt (f, 1088) b → ¬ InExt (a, 24) b⌝ := by
  unfold slot24 blockOwn
  iintro ⟨Hms, HA⟩
  ihave ⟨%g, HA⟩ := ownSet_fn _ $$ HA
  ihave ⟨%M2, HA⟩ := ownSet_mem _ g $$ HA
  ihave ⟨%M, Hms, %⟨h1, -, hd⟩⟩ := ms_join $$ [Hms HA]
  · iframe Hms HA
  iexists M
  iframe Hms
  ipureintro; exact ⟨h1, hd⟩

end Slots

/-- A doubleword load through memories agreeing on its bytes. -/
theorem ldv_ld_agree {M M' : Mem} {a : Nat} (h : ∀ i, i < 8 → imgM M' (a + i) = imgM M (a + i)) :
    ldv .ld M' a = ldv .ld M a := by
  show ldvf .ld (imgM M') a = ldvf .ld (imgM M) a
  simp only [ldvf, Vsa.Sim.widthOfM, bytesAt8]
  have h0 := h 0 (by omega); simp only [Nat.add_zero] at h0
  rw [h0, h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega)]

section Env

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
variable {live : Nat → Prop}

/-- The registers an `env_get`/`env_set` call takes. -/
abbrev env3L : List Nat := 10 :: 11 :: 12 :: 2 :: (argClob ++ getSaved)

/-- **A call in `env_get`'s register form from a run** (`jal entry` at `i`):
`a0`-`a2` and `sp` at the run's values, the argument registers clobbered,
`s0`-`s6` saved, and `X`; the run continues at `i + 4` with the callee-saved
registers and `sp` kept, the result in `a0`, and `Y` of it. -/
theorem ms_callEnv3 (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalExec (vsaModel live) i code entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {φ : Prop} (hφ : φ) {X : IProp GF} {Y : BitVec 64 → IProp GF}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} :
    fnSpecW Wp entry
      (fun r => iprop(⌜r.toNat % 4 = 0 ∧ φ⌝ ∗ (10 : Nat) ↦ᵣ R 10 ∗ (11 : Nat) ↦ᵣ R 11 ∗
        (12 : Nat) ↦ᵣ R 12 ∗ sp ↦ᵣ R 2 ∗ clobbered argClob ∗
        savedOwn (getSaved.map fun k => (k, R k)) ∗ X))
      (fun _ => iprop(∃ res : BitVec 64, (10 : Nat) ↦ᵣ res ∗ sp ↦ᵣ R 2 ∗ clobbered retClob ∗
        savedOwn (getSaved.map fun k => (k, R k)) ∗ Y res)) ∗
    codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗ X ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ callerSaved → R' x = R x⌝ -∗ Y (R' 10) -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hspec, #Hcode, Hms, HX, Hk⟩
  iapply (ms_callRegs Wp hexec hcode (L := env3L) (K := [23, 24, 25, 26, 27]) (by decide)
    (P := fun r => iprop(⌜r.toNat % 4 = 0 ∧ φ⌝ ∗ (10 : Nat) ↦ᵣ R 10 ∗ (11 : Nat) ↦ᵣ R 11 ∗
        (12 : Nat) ↦ᵣ R 12 ∗ sp ↦ᵣ R 2 ∗ clobbered argClob ∗
        savedOwn (getSaved.map fun k => (k, R k)) ∗ X))
    (Q := fun _ => iprop(∃ res : BitVec 64, (10 : Nat) ↦ᵣ res ∗ sp ↦ᵣ R 2 ∗ clobbered retClob ∗
        savedOwn (getSaved.map fun k => (k, R k)) ∗ Y res))
    (X := X) (Y := fun f => iprop(⌜f 2 = R 2 ∧ ∀ k ∈ getSaved, f k = R k⌝ ∗ Y (f 10)))
    (R := R) (S := S) (Mt := Mt) ?hP ?hQ)
  case hP =>
    simp only [env3L, sepL_cons]
    iintro ⟨⟨H10, H11, H12, H2, Hcs⟩, HX⟩
    ihave ⟨Hcl, Hsv⟩ := (sepL_append _ _ _).1 $$ Hcs
    unfold savedOwn VsaIris.sp
    iframe H10 H11 H12 H2 HX
    isplitl []
    · ipureintro; exact ⟨hi4, hφ⟩
    isplitl [Hcl]
    · iapply clobbered_of_fn argClob R $$ Hcl
    · rw [VsaIris.sepL_map]; iexact Hsv
  case hQ =>
    unfold savedOwn VsaIris.sp
    iintro ⟨%q, H10, H2, Hcl, Hsv, HY⟩
    ihave ⟨%g, Hcl⟩ := clobbered_fn retClob (by decide) $$ Hcl
    iexists (fun y => if y = 10 then q else if y = 2 then R 2 else if y ∈ getSaved then R y else g y)
    simp only [env3L, sepL_cons]
    rw [VsaIris.sepL_map] at *
    have eCl : sepL (GF := GF) argClob (fun y => y ↦ᵣ (if y = 10 then q else if y = 2 then R 2
        else if y ∈ getSaved then R y else g y)) = sepL argClob (fun y => y ↦ᵣ g y) :=
      sepL_congr fun y hy => by
        obtain ⟨h10, h2, hs⟩ := (show ∀ y ∈ argClob, y ≠ 10 ∧ y ≠ 2 ∧ y ∉ getSaved by decide) y hy
        simp [h10, h2, hs]
    have eSv : sepL (GF := GF) getSaved (fun y => y ↦ᵣ (if y = 10 then q else if y = 2 then R 2
        else if y ∈ getSaved then R y else g y)) = sepL getSaved (fun y => y ↦ᵣ R y) :=
      sepL_congr fun y hy => by
        obtain ⟨h10, h2⟩ := (show ∀ y ∈ getSaved, y ≠ 10 ∧ y ≠ 2 by decide) y hy
        simp [h10, h2, hy]
    simp only [retClob, sepL_cons] at *
    icases Hcl with ⟨H11, H12, Hcl⟩
    simp only [ite_true, show (2 : Nat) ≠ 10 from by decide, show (11 : Nat) ≠ 10 from by decide,
      show (12 : Nat) ≠ 10 from by decide, show (11 : Nat) ≠ 2 from by decide,
      show (12 : Nat) ≠ 2 from by decide, show (11 : Nat) ∉ getSaved from by decide,
      show (12 : Nat) ∉ getSaved from by decide, ite_false]
    isplitl [H10 H11 H12 H2 Hcl Hsv]
    · iframe H10 H11 H12 H2
      iapply (sepL_append _ _ _).2
      rw [eCl, eSv]
      iframe Hcl Hsv
    iframe HY
    ipureintro
    refine ⟨trivial, fun k hk => ?_⟩
    obtain ⟨h10, h2⟩ := (show ∀ y ∈ getSaved, y ≠ 10 ∧ y ≠ 2 by decide) k hk
    simp [h10, h2, hk]
  iframe Hspec Hcode Hms HX
  iintro %f ⟨%⟨hf2, hfs⟩, HY⟩ Hms
  have hkeep : ∀ x ∈ fRegs, x ∉ callerSaved →
      (fun x => if x ∈ env3L then f x else R x) x = R x := by
    intro x hx hc
    by_cases hL : x ∈ env3L
    · simp only [hL, ite_true]
      by_cases h2 : x = 2
      · subst h2; exact hf2
      · have hs : x ∈ getSaved :=
          (show ∀ y ∈ env3L, y ∉ callerSaved → y ≠ 2 → y ∈ getSaved by decide) x hL hc h2
        exact hfs x hs
    · simp [hL]
  have e10 : (fun x => if x ∈ env3L then f x else R x) 10 = f 10 := by
    simp only [show (10 : Nat) ∈ env3L from by decide, ite_true]
  rw [← e10]
  iapply Hk $$ %(fun x => if x ∈ env3L then f x else R x) %hkeep HY Hms

end Env

/-! ## Loads through a child's result slot -/

theorem slotWrite_ld0 (Mt : Mem) (a : Nat) (w0 w1 w2 : BitVec 64) :
    ldv .ld (slotWrite Mt a w0 w1 w2) a = w0 := by
  unfold slotWrite
  rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]

theorem slotWrite_ld8 (Mt : Mem) (a : Nat) (w0 w1 w2 : BitVec 64) :
    ldv .ld (slotWrite Mt a w0 w1 w2) (a + 8) = w1 := by
  unfold slotWrite
  rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]

theorem slotWrite_ld16 (Mt : Mem) (a : Nat) (w0 w1 w2 : BitVec 64) :
    ldv .ld (slotWrite Mt a w0 w1 w2) (a + 16) = w2 := by
  unfold slotWrite
  rw [ldv_store_hit]

theorem slotWrite_ld_miss (Mt : Mem) {a c : Nat} (w0 w1 w2 : BitVec 64) (h : c + 8 ≤ a ∨ a + 24 ≤ c) :
    ldv .ld (slotWrite Mt a w0 w1 w2) c = ldv .ld Mt c := by
  unfold slotWrite
  rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]

/-- A word's low half is its first four bytes (a `sw` into a value slot's tag). -/
theorem imgW_low4 (img : Nat → BitVec 8) (a : Nat) :
    (imgW img a).toNat % 2 ^ 32 = imgLE img a 4 := by
  rw [imgW_toNat]
  simp only [imgLE]
  have h0 := (img a).isLt; have h1 := (img (a + 1)).isLt; have h2 := (img (a + 1 + 1)).isLt
  have h3 := (img (a + 1 + 1 + 1)).isLt
  omega

end VsaIris.Interp
