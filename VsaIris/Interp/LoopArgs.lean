import VsaIris.Interp.LoopKit

/-!
# The call arguments loop (lane E6), both modes

INTERP_DESIGN.md §4.3; statements in `SpecLoop.lean` (`evalArgsT_body`,
`evalArgsP_body`). `eval_expr`'s call arm fills `args[32]` (`sp+240`):

```
800031dc ld a2,16(s0); … ld a2,0(a2)        args[i]'s node
800031fc sd a5,24(sp); … sd a6,16(sp); sd a3,8(sp); sd a4,0(sp)
80003220 jal eval_expr                       (slot sp+64)
80003224 … sd the three words to a4-768 = sp+240+24i; addi a6,a6,1
80003250 bne a6,a5 → 800031dc                (else 80003254)
```
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- The bytes of a call node and its argument array a run reads. -/
abbrev argsView (a arr argc : Nat) : List Nat := accAddrs (a + 16) 8 ++ accAddrs arr (8 * argc)

#ix_seg ArgsLoop_runA {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s arr pA : BitVec 64} {idx argc : Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 24 ≤ 0x100000000)
    (hx3 : aX.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (ha1 : 0x80000000 ≤ arr.toNat) (ha2 : arr.toNat + 8 * argc ≤ 0x100000000)
    (ha3 : arr.toNat + 8 * argc ≤ tohostAddr ∨ tohostAddr + 16 ≤ arr.toNat)
    (hidx : idx < argc) (hc : argc ≤ 32)
    (h8 : R 8 = aX) (h16 : R 16 = BitVec.ofNat 64 idx) (h2 : R 2 = s + 18446744073709550528#64)
    (harr : ldv .ld m (aX + 16#64).toNat = arr)
    (hel : ldv .ld m (arr + BitVec.ofNat 64 idx <<< 3).toNat = pA) :
    IW live m (argsView aX.toNat arr.toNat argc) (InExt (s.toNat - 1088, 1088)) Q 0x800031dc#64 R Mt
  by ix_run hlive using [h8, h16, h2, harr, hel, hsf] at 0x80003220

#ix_seg ArgsLoop_runB {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s slotA : BitVec 64} {q : Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709550528#64)
    (hA : ldv .ld Mt (s.toNat - 1088) = slotA)
    (hq0 : (slotA + LeanRV64DExecutable.Functions.sign_extend 3328#12).toNat = q)
    (hq8 : (slotA + LeanRV64DExecutable.Functions.sign_extend 3336#12).toNat = q + 8)
    (hq16 : (slotA + LeanRV64DExecutable.Functions.sign_extend 3344#12).toNat = q + 16)
    (hq1 : s.toNat - 1088 + 240 ≤ q) (hq2 : q + 24 ≤ s.toNat - 1088 + 1008) (hq3 : q % 8 = 0) :
    IW live m [] (InExt (s.toNat - 1088, 1088)) Q 0x80003224#64 R Mt
  by ix_run hlive using [h2, hA, hsf, hq0, hq8, hq16] at 0x800031dc 0x80003254

/-- An element of a represented expression array. -/
theorem exprArray_get {m : Mem} {P : Nat → Prop} :
    ∀ {a n : Nat} {es : List Expr}, ExprArrayReprWithin m P a n es →
      ∀ j (h : j < es.length), ∃ p, read64 m (a + 8 * j) = some p ∧ ExprReprWithin m P p es[j]
  | _, _, _, .nil, j, h => absurd h (by simp)
  | _, _, _, .cons hp _ hs hrest, 0, _ => ⟨_, by simpa using hp, hs⟩
  | a, _, _, .cons _ _ _ hrest, j + 1, h => by
    obtain ⟨p, hp, hs⟩ := exprArray_get hrest j (by simpa using h)
    exact ⟨p, by rw [show a + 8 * (j + 1) = a + 8 + 8 * j by omega]; exact hp, hs⟩

theorem exprArray_length {m : Mem} {P : Nat → Prop} :
    ∀ {a n : Nat} {es : List Expr}, ExprArrayReprWithin m P a n es → es.length = n
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ _ _ hrest => by simp [exprArray_length hrest]

/-- Every byte of a represented expression array's pointers is in the view
and present. -/
theorem exprArray_covers {m : Mem} {P : Nat → Prop} :
    ∀ {a n : Nat} {es : List Expr}, ExprArrayReprWithin m P a n es →
      ∀ k, k < 8 * n → P (a + k) ∧ (m[a + k]?).isSome
  | _, _, _, .nil, k, h => absurd h (by omega)
  | a, _, _, .cons hp cp _ hrest, k, h => by
    by_cases hk : k < 8
    · exact ⟨cp k hk, isSome_of_readLE hp hk⟩
    · have := exprArray_covers hrest (k - 8) (by omega)
      rwa [show a + 8 + (k - 8) = a + k by omega] at this

/-- What a call node's argument array gives the runs. -/
structure ArgsNode (m : Mem) (P : Nat → Prop) (aX arr : BitVec 64) (all : List Expr) : Prop where
  arrw : ldv .ld m (aX + 16#64).toNat = arr
  lo : 0x80000000 ≤ aX.toNat
  hi : aX.toNat + 24 ≤ 0x100000000
  off : aX.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat
  alo : 0x80000000 ≤ arr.toNat
  ahi : arr.toNat + 8 * all.length ≤ 0x100000000
  aoff : arr.toNat + 8 * all.length ≤ tohostAddr ∨ tohostAddr + 16 ≤ arr.toNat
  repr : ExprArrayReprWithin m P arr.toNat all.length all
  view : ∀ a ∈ argsView aX.toNat arr.toNat all.length, P a ∧ (m[a]?).isSome

/-- A call node's argument array facts, from its representation (a nonempty
argument list: the loop is entered only then). -/
theorem argsNode_of_repr {m : Mem} {P : Nat → Prop} {aX : BitVec 64} {f : Expr} {all : List Expr}
    (h : ExprReprWithin m P aX.toNat (.call f all)) (hg : ∀ k, P k → ReadOK k) (hne : all ≠ []) :
    ∃ arr : Nat, ArgsNode m P aX (BitVec.ofNat 64 arr) all ∧ arr < 2 ^ 64 := by
  cases h with
  | @call _ fp arr argc _ _ h9 c9 hf cf hrf ha ca hc cc hsmall hes =>
    have hlen := exprArray_length hes
    subst hlen
    have hpos : 0 < all.length := by
      cases all with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    have hcov := exprArray_covers hes
    have g0 := hg _ (c9 0 (by omega)); have g3 := hg _ (c9 3 (by omega))
    have g8 := hg _ (cf 0 (by omega)); have g16 := hg _ (ca 0 (by omega))
    have g23 := hg _ (ca 7 (by omega)); have g24 := hg _ (cc 0 (by omega))
    have g27 := hg _ (cc 3 (by omega)); have g15 := hg _ (cf 7 (by omega))
    have ga0 := hg _ (hcov 0 (by omega)).1
    have gaN := hg _ (hcov (8 * all.length - 1) (by omega)).1
    have hat : (BitVec.ofNat 64 arr).toNat = arr := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (readLE_lt ha)]
    have e16 : (aX + 16#64).toNat = aX.toNat + 16 := by
      have := g27.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine ⟨arr, ⟨?_, g0.lo, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, readLE_lt ha⟩
    · rw [e16]; exact ldv_ld_read64 ha
    · have := g23.hi; simp only [Nat.add_zero] at *; omega
    · have h0 := g0.off; have h3 := g3.off; have h8' := g8.off; have h15 := g15.off
      have h16 := g16.off; have h23 := g23.off
      simp only [Nat.add_zero] at *; omega
    · rw [hat]; simp only [Nat.add_zero] at ga0; exact ga0.lo
    · rw [hat]; have := gaN.hi; omega
    · rw [hat]
      refine Classical.byContradiction fun hc' => ?_
      have hin : ReadOK (max arr tohostAddr) := by
        have := hcov (max arr tohostAddr - arr) (by omega)
        rw [show arr + (max arr tohostAddr - arr) = max arr tohostAddr by omega] at this
        exact hg _ this.1
      have := hin.off; omega
    · rw [hat]; exact hes
    · intro a ha'
      simp only [List.mem_append, mem_accAddrs_iff] at ha'
      rcases ha' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + 16 + j := ⟨a - (aX.toNat + 16), by omega⟩
        exact ⟨ca j (by omega), isSome_of_readLE ha (by omega)⟩
      · rw [hat] at h1 h2
        obtain ⟨j, rfl⟩ : ∃ j, a = arr + j := ⟨a - arr, by omega⟩
        exact hcov j (by omega)

section Vals

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- The argument values read the same through images that agree on their
words. -/
theorem argVals_congr (N : NativeAddrs) {img img' : Nat → BitVec 8} (base : Nat) :
    ∀ (i : Nat) (vs : List Value),
      (∀ j, j < 24 * vs.length → img (base + 24 * i + j) = img' (base + 24 * i + j)) →
      argVals (GF := GF) N img base i vs ⊢ argVals N img' base i vs
  | _, [], _ => .rfl
  | i, v :: vs, h => by
    unfold argVals
    have e : ∀ o, o < 3 → imgW img (base + 24 * i + 8 * o) = imgW img' (base + 24 * i + 8 * o) :=
      fun o ho => imgW_agree fun j hj => by
        have := h (8 * o + j) (by simp at *; omega)
        rwa [show base + 24 * i + (8 * o + j) = base + 24 * i + 8 * o + j by omega] at this
    have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at e0 e1
    rw [show 8 * 2 = 16 from rfl] at e2
    unfold valImg
    rw [e0, e1, e2]
    iintro ⟨#Hv, #Hr⟩
    isplitl []
    · iexact Hv
    · iapply argVals_congr N base (i + 1) vs (fun j hj => by
        have := h (24 + j) (by simp at *; omega)
        rwa [show base + 24 * i + (24 + j) = base + 24 * (i + 1) + j by omega] at this) $$ Hr

/-- One more argument value at the end. -/
theorem argVals_snoc (N : NativeAddrs) (img : Nat → BitVec 8) (base : Nat) (v : Value) :
    ∀ (i : Nat) (pre : List Value),
      argVals (GF := GF) N img base i pre ∗ valImg N img (base + 24 * (i + pre.length)) v ⊢
        argVals N img base i (pre ++ [v])
  | i, [] => by
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    unfold argVals argVals
    iintro ⟨-, #Hv⟩
    isplitl []
    · iexact Hv
    · iempintro
  | i, w :: pre => by
    simp only [List.cons_append, List.length_cons]
    unfold argVals
    iintro ⟨⟨#Hw, #Hr⟩, #Hv⟩
    isplitl []
    · iexact Hw
    · iapply argVals_snoc N img base v (i + 1) pre
      iframe Hr
      rw [show i + 1 + pre.length = i + (pre.length + 1) by omega]
      iexact Hv

end Vals

/-- A slot of `eval_expr`'s frame at offset `o` below the lowered `sp`. -/
theorem evalSlot {s : BitVec 64} (h : EvalFrameG s) {o : Nat} (ho : o + 24 ≤ 1088)
    (ho8 : o % 8 = 0) :
    (s + 18446744073709550528#64 + BitVec.ofNat 64 o).toNat = s.toNat - 1088 + o ∧
      SlotGeom (s + 18446744073709550528#64 + BitVec.ofNat 64 o) := by
  have h1 := h.sf; have h2 := h.lo; have h3 := h.hi; have h4 := h.al
  have e : (s + 18446744073709550528#64 + BitVec.ofNat 64 o).toNat = s.toNat - 1088 + o := by
    rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨e, ⟨?_, ?_, ?_⟩⟩
  · rw [e]; omega
  · rw [e]; unfold Vsa.Sim.tohostAddr; omega
  · rw [e]; omega

/-- A frame address of `eval_expr` as a plain sum (`ix_fwd using [evalSP_off' hfg]`). -/
theorem evalSP_off' {s : BitVec 64} (h : EvalFrameG s) (c : Nat) (hc : c < 4096) :
    (s + 18446744073709550528#64 + BitVec.ofNat 64 c).toNat = s.toNat - 1088 + c := by
  have h1 := h.sf; have h2 := h.lo; have h3 := h.hi
  rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem sext32_ofNat_eq {a : Nat} (h : a < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a)) = BitVec.ofNat 64 a :=
  BitVec.eq_of_toInt_eq (by rw [sext32_ofNat_toInt h, ofNat_toInt_small h])


theorem times24 {idx : Nat} (hi : idx < 32) :
    (BitVec.ofNat 64 idx <<< 1 + BitVec.ofNat 64 idx) <<< 3 = BitVec.ofNat 64 (24 * idx) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have e : (2:Nat) ^ 64 = 18446744073709551616 := rfl
  rw [e]; omega

theorem args_slot_addr {s : BitVec 64} (h : EvalFrameG s) {idx : Nat} (hi : idx < 32) (c : Nat)
    (hc1 : 18446744073709550848 ≤ c) (hc2 : c < 2 ^ 64) :
    ((BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 idx)) <<< 1 +
        BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 idx))) <<< 3 + 976#64 +
      (s + 18446744073709550528#64 + 32#64) + BitVec.ofNat 64 c).toNat =
      s.toNat - 1088 + 1008 + 24 * idx + c - 2 ^ 64 := by
  rw [sext32_ofNat_eq (by omega), times24 hi]
  have h1 := h.sf; have h2 := h.lo; have h3 := h.hi
  have hs32 := evalSP_off' h 32 (by omega)
  have hA : (BitVec.ofNat 64 (24 * idx) + 976#64 + (s + 18446744073709550528#64 + 32#64)).toNat =
      s.toNat - 1088 + 1008 + 24 * idx := by
    have e1 : (BitVec.ofNat 64 (24 * idx) + 976#64).toNat = 24 * idx + 976 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := 24 * idx) (by omega), Nat.mod_eq_of_lt (a := 976) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, e1, show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from rfl, hs32,
      Nat.mod_eq_of_lt (by omega)]
    omega
  rw [BitVec.toNat_add, hA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc2]
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- What the argument loop's staging leaves in the frame for the copy after
the call: the count, the index and the frame pointer spilled, and the
address of `args[idx]` (`a4 - 768`). -/
structure ArgsSpill (Mt : Mem) (s aE : BitVec 64) (idx argc : Nat) : Prop where
  cnt : ldv .ld Mt (s + 18446744073709550528#64 + 24#64).toNat = BitVec.ofNat 64 argc
  ix : ldv .ld Mt (s + 18446744073709550528#64 + 16#64).toNat = BitVec.ofNat 64 idx
  env : ldv .ld Mt (s + 18446744073709550528#64 + 8#64).toNat = aE
  a0 : (ldv .ld Mt (s + 18446744073709550528#64).toNat + 18446744073709550848#64).toNat =
    argsBase s + 24 * idx
  a8 : (ldv .ld Mt (s + 18446744073709550528#64).toNat + 18446744073709550856#64).toNat =
    argsBase s + 24 * idx + 8
  a16 : (ldv .ld Mt (s + 18446744073709550528#64).toNat + 18446744073709550864#64).toNat =
    argsBase s + 24 * idx + 16

/-! ## The runs' glue, for either WP -/

section Glue

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {inp : Nat}

/-- **Run A**: from the loop head, stage argument `idx` (`all[idx]`) for its
`jal eval_expr` (`0x80003220`, slot `sp+64`), spilling the loop's registers. -/
theorem argsStage (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {f : Expr} {all : List Expr} {idx : Nat}
    {aX aE s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hh : ArgsHead R s aX (BitVec.ofNat 64 inp) aE idx all.length) (hfg : EvalFrameG s)
    (hidx : idx < all.length) (hlen : all.length ≤ 32) :
    ms 0x800031dc#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗ codeRes ∗ □ astEG aX.toNat (.call f all) ∗
      (∀ (R1 : Nat → BitVec 64) (Mt1 : Mem) (aA : BitVec 64),
        ⌜EvalRegs R1 (s + 18446744073709550528#64 + 64#64) (BitVec.ofNat 64 inp) aA aE
            (s + 18446744073709550528#64) ∧ KeepRegs calleeSaved R R1 ∧
          ArgsSpill Mt1 s aE idx all.length ∧
          Untouched (InExt (s.toNat - 1088, 1088)) (argsW s) Mt Mt1 ∧
          ∀ a, argsBase s ≤ a → imgM Mt1 a = imgM Mt a⌝ -∗
        □ astEG aA.toNat all[idx] -∗ ms 0x80003220#64 R1 (InExt (s.toNat - 1088, 1088)) Mt1 -∗
        Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, Hk⟩
  ihave ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩ := astEG_elim _ _ $$ Hast
  obtain ⟨arr, hn, harr⟩ := argsNode_of_repr hrepr hgeo (List.ne_nil_of_length_pos (by omega))
  obtain ⟨p, hp, hsp⟩ := exprArray_get hn.repr idx hidx
  have hpl : p < 2 ^ 64 := readLE_lt hp
  have hel : ldv .ld m (BitVec.ofNat 64 arr + BitVec.ofNat 64 idx <<< 3).toNat = BitVec.ofNat 64 p := by
    rw [arr_elem_addr hn.ahi hidx]; exact ldv_ld_read64 hp
  have hoff := evalSP_off' hfg
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(roOn P m ∗ (∀ (R1 : Nat → BitVec 64) (Mt1 : Mem) (aA : BitVec 64),
        ⌜EvalRegs R1 (s + 18446744073709550528#64 + 64#64) (BitVec.ofNat 64 inp) aA aE
            (s + 18446744073709550528#64) ∧ KeepRegs calleeSaved R R1 ∧
          ArgsSpill Mt1 s aE idx all.length ∧
          Untouched (InExt (s.toNat - 1088, 1088)) (argsW s) Mt Mt1 ∧
          ∀ a, argsBase s ≤ a → imgM Mt1 a = imgM Mt a⌝ -∗
        □ astEG aA.toNat all[idx] -∗ ms 0x80003220#64 R1 (InExt (s.toNat - 1088, 1088)) Mt1 -∗
        Wp.W Φ)))
  rotate_left
  · iframe Hdv Hms Hro; iexact Hk
  intro F'
  refine ArgsLoop_runA (pA := BitVec.ofNat 64 p) hlive hfg.sf hfg.lo hfg.hi hfg.al hn.lo hn.hi hn.off
    hn.alo hn.ahi hn.aoff hidx hlen hh.s0 hh.a6 hh.sp hn.arrw hel ?_
  intros
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  unfold F'
  iintro ⟨⟨#Hro, Hk⟩, Hms⟩
  have hsp1 : ArgsSpill Mt1 s aE idx all.length := by
    subst hMt1
    have hlen32 : idx < 32 := by omega
    constructor
    · ix_fwd using [hoff]; exact hh.a5
    · ix_fwd using [hoff]
    · ix_fwd using [hoff]; exact hh.a3
    all_goals (ix_fwd using [hoff, hfg.sf]; rw [args_slot_addr hfg hlen32 _ (by decide) (by decide)]; unfold argsBase; omega)
  have hregs : EvalRegs R1 (s + 18446744073709550528#64 + 64#64) (BitVec.ofNat 64 inp)
      (BitVec.ofNat 64 p) aE (s + 18446744073709550528#64) := by
    subst hR1; exact ⟨by ix_reg, by ix_reg; exact hh.s2, by ix_reg, by ix_reg; exact hh.a3, by ix_reg; exact hh.sp⟩
  have hk1 : KeepRegs calleeSaved R R1 := by subst hR1; keep_upd
  have hut : Untouched (InExt (s.toNat - 1088, 1088)) (argsW s) Mt Mt1 := by
    subst hMt1
    have hW : ∀ c, c + 8 ≤ 32 → ∀ a, (s + 18446744073709550528#64 + BitVec.ofNat 64 c).toNat ≤ a →
        a < (s + 18446744073709550528#64 + BitVec.ofNat 64 c).toNat + 8 → argsW s a := by
      intro c hc a h1 h2; rw [hoff c (by omega)] at h1 h2; left; simp only [InExt]; omega
    refine Untouched.trans (Untouched.trans (Untouched.trans
      (Untouched.store' _ _ (hW 24 (by omega))) (Untouched.store' _ _ (hW 16 (by omega))))
      (Untouched.store' _ _ (hW 8 (by omega)))) (Untouched.store' _ _ ?_)
    intro a h1 h2; left; simp only [InExt]; omega
  have hlo : ∀ a, argsBase s ≤ a → imgM Mt1 a = imgM Mt a := by
    intro a ha
    subst hMt1
    unfold argsBase at ha
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by rw [hoff 8 (by omega)]; omega),
      imgM_store_miss _ _ (by rw [hoff 16 (by omega)]; omega),
      imgM_store_miss _ _ (by rw [hoff 24 (by omega)]; omega)]
  iapply Hk $$ %R1 %Mt1 %(BitVec.ofNat 64 p) %⟨hregs, hk1, hsp1, hut, hlo⟩ [] Hms
  imodintro; rw [ofNat_toNat_lt hpl]; iapply astEG_of_view hsp hgeo $$ Hro

end Glue

/-- What one argument's copy leaves: the loop's registers reloaded (the
count, the frame pointer, the next index), the callee-saved ones kept, the
argument's three words in `args[idx]`, and the frame otherwise as before the
argument was staged (`Mt0`), outside the written words and on the earlier
arguments. -/
structure ArgsCopied (R R' : Nat → BitVec 64) (Mt0 Mt' : Mem) (s aE : BitVec 64) (idx argc : Nat)
    (w0 w1 w2 : BitVec 64) : Prop where
  keep : KeepRegs calleeSaved R R'
  a5 : R' 15 = BitVec.ofNat 64 argc
  a3 : R' 13 = aE
  a6 : R' 16 = BitVec.ofNat 64 (idx + 1)
  w0 : imgW (imgM Mt') (argsBase s + 24 * idx) = w0
  w1 : imgW (imgM Mt') (argsBase s + 24 * idx + 8) = w1
  w2 : imgW (imgM Mt') (argsBase s + 24 * idx + 16) = w2
  untouched : Untouched (InExt (s.toNat - 1088, 1088)) (argsW s) Mt0 Mt'
  earlier : ∀ a, argsBase s ≤ a → a < argsBase s + 24 * idx → imgM Mt' a = imgM Mt0 a

theorem sign_extend_3328 : LeanRV64DExecutable.Functions.sign_extend (m := 64) 3328#12 =
    18446744073709550848#64 := by decide
theorem sign_extend_3336 : LeanRV64DExecutable.Functions.sign_extend (m := 64) 3336#12 =
    18446744073709550856#64 := by decide
theorem sign_extend_3344 : LeanRV64DExecutable.Functions.sign_extend (m := 64) 3344#12 =
    18446744073709550864#64 := by decide

/-- The three words of a slot just stored, read back. -/
theorem imgW_three (M : Mem) (q : Nat) (a b c : BitVec 64) :
    imgW (imgM (writeLog (writeLog (writeLog M [(q, 8, a)]) [(q + 8, 8, b)]) [(q + 16, 8, c)])) q = a ∧
    imgW (imgM (writeLog (writeLog (writeLog M [(q, 8, a)]) [(q + 8, 8, b)]) [(q + 16, 8, c)]))
      (q + 8) = b ∧
    imgW (imgM (writeLog (writeLog (writeLog M [(q, 8, a)]) [(q + 8, 8, b)]) [(q + 16, 8, c)]))
      (q + 16) = c := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold imgW
  · rw [imgLE_store_miss _ _ (by omega), imgLE_store_miss _ _ (by omega), imgLE_imgM_store]
    simp
  · rw [imgLE_store_miss _ _ (by omega), imgLE_imgM_store]
    simp
  · rw [imgLE_imgM_store]
    simp

/-- Off a slot's three stores, the image is unchanged. -/
theorem imgM_three_out {M : Mem} {q x : Nat} (a b c : BitVec 64) (h : x < q ∨ q + 24 ≤ x) :
    imgM (writeLog (writeLog (writeLog M [(q, 8, a)]) [(q + 8, 8, b)]) [(q + 16, 8, c)]) x =
      imgM M x := by
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]

section Copy

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
variable {live : Nat → Prop}

/-- **Run B**: after argument `idx` returned into `sp+64` (its three words),
the copy into `args[idx]`, the index step and the count test: back to the
head while arguments remain, out to `0x80003254` after the last. -/
theorem argsCopy (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {w0 w1 w2 aE s : BitVec 64} {idx argc : Nat}
    {R : Nat → BitVec 64} {Mt0 Mt : Mem} (hfg : EvalFrameG s)
    (hsp : R 2 = s + 18446744073709550528#64) (hsp1 : ArgsSpill Mt s aE idx argc)
    (hut : Untouched (InExt (s.toNat - 1088, 1088)) (argsW s) Mt0 Mt)
    (hpre : ∀ a, argsBase s ≤ a → a < argsBase s + 24 * idx → imgM Mt a = imgM Mt0 a)
    (hidx : idx < argc) (hc : argc ≤ 32) :
    ms (BitVec.ofNat 64 (0x80003220 + 4)) R (InExt (s.toNat - 1088, 1088))
        (slotWrite Mt (s + 18446744073709550528#64 + 64#64).toNat w0 w1 w2) ∗ codeRes ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem), ⌜idx + 1 ≠ argc⌝ -∗
          ⌜ArgsCopied R R' Mt0 Mt' s aE idx argc w0 w1 w2⌝ -∗
          ms 0x800031dc#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗ Wp.W Φ) ∧
        (∀ (R' : Nat → BitVec 64) (Mt' : Mem), ⌜idx + 1 = argc⌝ -∗
          ⌜ArgsCopied R R' Mt0 Mt' s aE idx argc w0 w1 w2⌝ -∗
          ms 0x80003254#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗ Wp.W Φ))
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, Hk⟩
  have hoff := evalSP_off' hfg
  have hq := hsp1.a0
  have e64 : (s + 18446744073709550528#64 + 64#64).toNat = s.toNat - 1088 + 64 := hoff 64 (by omega)
  have hsl : ldv .ld (slotWrite Mt (s + 18446744073709550528#64 + 64#64).toNat w0 w1 w2)
      (s.toNat - 1088) = ldv .ld Mt (s + 18446744073709550528#64).toNat := by
    rw [hfg.sf]; ix_fwd using [hoff]
  have hw0 : ldv .ld (slotWrite Mt (s + 18446744073709550528#64 + 64#64).toNat w0 w1 w2)
      (s + 18446744073709550528#64 + 64#64).toNat = w0 := by ix_fwd using [hoff]
  have hw1 : ldv .ld (slotWrite Mt (s + 18446744073709550528#64 + 64#64).toNat w0 w1 w2)
      (s + 18446744073709550528#64 + 72#64).toNat = w1 := by ix_fwd using [hoff]
  have hw2 : ldv .ld (slotWrite Mt (s + 18446744073709550528#64 + 64#64).toNat w0 w1 w2)
      (s + 18446744073709550528#64 + 80#64).toNat = w2 := by ix_fwd using [hoff]
  have hb := hfg.lo; have hb2 := hfg.hi; have hb3 := hfg.al
  have hcnt : ldv .ld Mt (s.toNat - 1088 + 24) = BitVec.ofNat 64 argc := by
    have := hsp1.cnt; simp (disch := decide) only [hoff] at this; exact this
  have hix : ldv .ld Mt (s.toNat - 1088 + 16) = BitVec.ofNat 64 idx := by
    have := hsp1.ix; simp (disch := decide) only [hoff] at this; exact this
  have henv : ldv .ld Mt (s.toNat - 1088 + 8) = aE := by
    have := hsp1.env; simp (disch := decide) only [hoff] at this; exact this
  have hq0 : (ldv .ld Mt (s + 18446744073709550528#64).toNat +
      LeanRV64DExecutable.Functions.sign_extend 3328#12).toNat = argsBase s + 24 * idx := by
    rw [sign_extend_3328]; exact hsp1.a0
  have hq8 : (ldv .ld Mt (s + 18446744073709550528#64).toNat +
      LeanRV64DExecutable.Functions.sign_extend 3336#12).toNat = argsBase s + 24 * idx + 8 := by
    rw [sign_extend_3336]; exact hsp1.a8
  have hq16 : (ldv .ld Mt (s + 18446744073709550528#64).toNat +
      LeanRV64DExecutable.Functions.sign_extend 3344#12).toNat = argsBase s + 24 * idx + 16 := by
    rw [sign_extend_3344]; exact hsp1.a16
  ihave #Hdv := roOwn_code (m := Mt) $$ Hcode
  iapply wp_swpF Wp (F := iprop((∀ (R' : Nat → BitVec 64) (Mt' : Mem), ⌜idx + 1 ≠ argc⌝ -∗
          ⌜ArgsCopied R R' Mt0 Mt' s aE idx argc w0 w1 w2⌝ -∗
          ms 0x800031dc#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗ Wp.W Φ) ∧
        (∀ (R' : Nat → BitVec 64) (Mt' : Mem), ⌜idx + 1 = argc⌝ -∗
          ⌜ArgsCopied R R' Mt0 Mt' s aE idx argc w0 w1 w2⌝ -∗
          ms 0x80003254#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗ Wp.W Φ)))
  rotate_left
  · iframe Hdv Hms; iexact Hk
  intro F'
  refine ArgsLoop_runB (q := argsBase s + 24 * idx) hlive hfg.sf hfg.lo hfg.hi hfg.al hsp hsl
    (by rw [sign_extend_3328]; exact hsp1.a0) (by rw [sign_extend_3336]; exact hsp1.a8)
    (by rw [sign_extend_3344]; exact hsp1.a16) (by unfold argsBase; omega) (by unfold argsBase; omega)
    (by unfold argsBase; omega) ?_ ?_
  all_goals
    intro hcnd
    intros
    apply swp_closeRM
    intro R3 Mt3 hR3 hMt3
    have h15 : R3 15 = BitVec.ofNat 64 argc := by
      rw [hR3]; ix_reg; ix_fwd using [hoff]; rw [hcnt]
    have h16 : R3 16 = BitVec.ofNat 64 (idx + 1) := by
      rw [hR3]; ix_reg; ix_fwd using [hoff]; rw [hix, idx_succ]
    have hcp : ArgsCopied R R3 Mt0 Mt3 s aE idx argc w0 w1 w2 := by
      refine ⟨?_, h15, ?_, h16, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hR3]; keep_upd
      · rw [hR3]; ix_reg; ix_fwd using [hoff]; rw [henv]
      all_goals (subst hMt3)
      · rw [(imgW_three _ _ _ _ _).1, hw0]
      · rw [(imgW_three _ _ _ _ _).2.1, hw1]
      · rw [(imgW_three _ _ _ _ _).2.2, hw2]
      · refine hut.trans (Untouched.trans
          (M2 := slotWrite Mt (s + 18446744073709550528#64 + 64#64).toNat w0 w1 w2) ?_ ?_)
        · intro a _ hw
          refine imgM_slotWrite_out w0 w1 w2 fun hin => hw (.inr (.inl ?_))
          rw [e64] at hin; exact hin
        · intro a _ hw
          refine imgM_three_out _ _ _ ?_
          refine Classical.byContradiction fun hc' => hw (.inr (.inr ?_))
          simp only [InExt, argsBase] at hc' ⊢; omega
      · intro a h1 h2
        rw [imgM_three_out _ _ _ (.inl h2), imgM_slotWrite_out w0 w1 w2 (by
          rw [e64]; simp only [InExt, argsBase] at h1 ⊢; omega)]
        exact hpre a h1 h2
    unfold F'
    iintro ⟨Hk, Hms⟩
    first
    | (ihave Hk := and_elim_l $$ Hk
       iapply Hk $$ %R3 %Mt3 %(?_) %hcp Hms)
    | (ihave Hk := and_elim_r $$ Hk
       iapply Hk $$ %R3 %Mt3 %(?_) %hcp Hms)
  · rw [← hR3, h16, h15] at hcnd; intro e; exact hcnd (by rw [e])
  · rw [← hR3, h16, h15, Decidable.not_not] at hcnd
    have := congrArg BitVec.toNat hcnd
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this

end Copy

/-! ## Both modes -/

section Modes

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- The next head's registers and the argument values after one copy. -/
theorem ArgsCopied.head {R R' : Nat → BitVec 64} {Mt0 Mt' : Mem} {s aX aE : BitVec 64}
    {idx argc : Nat} {w0 w1 w2 : BitVec 64} {Rh : Nat → BitVec 64}
    (hc : ArgsCopied R R' Mt0 Mt' s aE idx argc w0 w1 w2) (hk : KeepRegs calleeSaved Rh R)
    (hh : ArgsHead Rh s aX (BitVec.ofNat 64 inp) aE idx argc) :
    ArgsHead R' s aX (BitVec.ofNat 64 inp) aE (idx + 1) argc ∧ KeepRegs argsKeep Rh R' := by
  have hk' := KeepRegs.trans hk hc.keep
  refine ⟨⟨(hk' 2 (by decide)).trans hh.sp, (hk' 8 (by decide)).trans hh.s0,
    (hk' 18 (by decide)).trans hh.s2, hc.a3, hc.a6, hc.a5⟩, ?_⟩
  intro x hx
  simp only [argsKeep, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | hx
  · exact hc.a5.trans hh.a5.symm
  · exact hk' x (by simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false]; exact hx)

omit I in
/-- The argument values after one copy: the earlier ones unchanged, the new
one in `args[idx]`. -/
theorem argVals_step [InterpGS GF] {R R' : Nat → BitVec 64} {Mt0 Mt' : Mem} {s aE : BitVec 64}
    {idx argc : Nat} {w0 w1 w2 : BitVec 64} (N : NativeAddrs) {pre : List Value} {v : Value}
    (hc : ArgsCopied R R' Mt0 Mt' s aE idx argc w0 w1 w2) (hpre : pre.length = idx) :
    argVals (GF := GF) N (imgM Mt0) (argsBase s) 0 pre ∗ □ valOf N v w0 w1 w2 ⊢
      argVals N (imgM Mt') (argsBase s) 0 (pre ++ [v]) := by
  iintro ⟨#Ha, #Hv⟩
  iapply argVals_snoc N (imgM Mt') (argsBase s) v 0 pre
  isplitl []
  · iapply argVals_congr N (argsBase s) 0 pre (fun j hj => by
      rw [hc.earlier _ (by omega) (by rw [← hpre]; omega)]) $$ Ha
  · unfold valImg
    rw [show argsBase s + 24 * (0 + pre.length) = argsBase s + 24 * idx by rw [hpre]; omega,
      hc.w0, hc.w1, hc.w2]
    iexact Hv

/-- `EvalArgsCost.cons`, total mode: argument `idx` through its derivation
`De`, its copy, then the rest (the tail's motive `hr`, over its derivation
`D2`). -/
theorem evalArgsT_cons (hlive : ∀ p ∈ interpText, live p.1)
    {st : St} {d env : Nat} {e : Expr} {es : List Expr} {st1 st2 : St} {v : Value}
    {vs : List Value} {ne nes : Nat}
    (De : EvalECost st d env e st1 v ne) (D2 : EvalArgsCost st1 d env es st2 vs nes)
    (he : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st1 v ne De)
    (hr : evalArgsT_body (GF := GF) live N L Room inp st1 d env es st2 vs nes) :
    evalArgsT_body (GF := GF) live N L Room inp st d env (e :: es) st2 (v :: vs) (ne + nes) := by
  intro Φ k idx f all pre aX aE s R Mt m' _ hdrop hpre hlen hh hfg hsg hall
  obtain ⟨hl, hat, hrest⟩ := drop_cons_facts hdrop
  subst hat
  obtain ⟨hneed, hbb⟩ := hall _ (List.getElem_mem hl)
  have hsl := evalSlot hfg (o := 64) (by omega) rfl
  rw [show k + (ne + nes) = k + nes + ne by omega]
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, #Hargs, Hw, Hk⟩
  iapply argsStage (twpW _) hlive hh hfg hl hlen
  iframe Hms Hcode Hast
  iintro %R1 %Mt1 %aA %⟨hregs, hk1, hsp1, hut1, hlo1⟩ #Hae Hms
  ihave He := he
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80003220)
    (jalx_80003220 live (fun p hp => hlive _ (interp_code_80003220 p hp)))
    interp_code_80003220 (by decide) De (k := k + nes) (hsg.narrow hneed) hneed hsg.le hsl.2 hbb
  iframe He Hcode Hae Hfr Hms Hst Hw
  isplitl []
  · ipureintro
    refine ⟨hregs, fun b hb => ?_⟩
    rw [hsl.1] at hb; simp only [InExt] at hb ⊢; have := hfg.lo; omega
  iintro %R2 %w0 %w1 %w2 %hk2 #Hv Hms Hst Hw
  have hk2' := hk2.calleeSaved_upd (x := 1) (by decide) (BitVec.ofNat 64 (0x80003220 + 4))
  iapply argsCopy (twpW _) (R := upd R2 1 (BitVec.ofNat 64 (0x80003220 + 4))) (Mt0 := Mt) hlive hfg
    (by ix_reg; rw [keep_reg hk2 (by decide)]; exact hregs.sp) hsp1 hut1
    (fun a h1 _ => hlo1 a h1) hl hlen
  iframe Hms Hcode
  have hkR : KeepRegs calleeSaved R (upd R2 1 (BitVec.ofNat 64 (0x80003220 + 4))) :=
    KeepRegs.trans hk1 hk2'
  isplit
  · iintro %R3 %Mt3 %hne %hcp Hms
    obtain ⟨hh3, hk3⟩ := hcp.head hkR hh
    cases es with
    | nil =>
      exfalso
      have := List.drop_eq_nil_iff.mp hrest.symm
      omega
    | cons e2 es2 =>
      iapply hr Φ k (idx + 1) f all (pre ++ [v]) aX aE s R3 Mt3 m' (List.cons_ne_nil _ _) hrest
        (by simp [hpre]) hlen hh3 hfg hsg hall
      iframe Hms Hcode Hast Hfr Hst Hw
      isplitl []
      · iapply argVals_step N hcp hpre
        iframe Hargs Hv
      iintro %R4 %Mt4 %⟨hk4, h16, hut4⟩ Hms Hvals Hst Hw
      rw [List.append_assoc, List.singleton_append] at *
      iapply Hk $$ %R4 %Mt4 %⟨KeepRegs.trans hk3 hk4, h16, hcp.untouched.trans hut4⟩ Hms Hvals Hst Hw
  · iintro %R3 %Mt3 %heq %hcp Hms
    obtain ⟨_, hk3⟩ := hcp.head hkR hh
    have hes : es = [] := by rw [hrest]; exact List.drop_eq_nil_of_le (by omega)
    subst hes
    cases D2
    iapply Hk $$ %R3 %Mt3 %⟨hk3, by rw [hcp.a6, heq], hcp.untouched⟩ Hms [] Hst Hw
    iapply argVals_step N hcp hpre
    iframe Hargs Hv

/-- **The argument loop, partial mode** (`evalArgsP_body`), for every
argument list: each argument through the Löb hypothesis (`ms_callEvalP`,
whose abort rebuilds `eval_expr`'s frame), by structure on the list. -/
theorem evalArgsP_all (hlive : ∀ p ∈ interpText, live p.1) (Core : IProp GF) (d env : Nat) :
    ∀ es, evalArgsP_body (GF := GF) live N L Room inp Core d env es
  | [] => evalArgsP_nil live N L Room inp Core d env
  | e :: es => by
    intro Φ st idx f all pre aX aE s sret0 R Mt m' n0 Out _ hdrop hpre hlen hh hfg hsg hn0 hall hOut
    obtain ⟨hl, hat, hrest⟩ := drop_cons_facts hdrop
    subst hat
    obtain ⟨hneed, hbb⟩ := hall _ (List.getElem_mem hl)
    have hsl := evalSlot hfg (o := 64) (by omega) rfl
    have hsp' := hsg.le
    have hsf := hfg.sf
    have hslo := hfg.lo
    iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, #Hargs, Hw, HOut, #HE, HK⟩
    iapply argsStage (wpW _) hlive hh hfg hl hlen
    iframe Hms Hcode Hast
    iintro %R1 %Mt1 %aA %⟨hregs, hk1, hsp1, hut1, hlo1⟩ #Hae Hms
    ihave He := evalSpecsP_at (N := N) (L := L) (Room := Room) (inp := inp) Core st d env all[idx] $$ HE
    iapply ms_callEvalP (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80003220)
      (Kret := iprop(∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (vs : List Value),
        ⌜EvalArgs st d env (all[idx] :: es) st' vs⌝ -∗
        ⌜KeepRegs argsKeep R R' ∧ R' 16 = BitVec.ofNat 64 all.length ∧
          Untouched (InExt (s.toNat - 1088, 1088)) (argsW s) Mt Mt'⌝ -∗
        ms 0x80003254#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗
        argVals N (imgM Mt') (argsBase s) 0 (pre ++ vs) -∗
        stackScratch (s + 18446744073709550528#64) m' -∗
        world N L Room inp .uncounted st' d -∗ Out -∗ (wpW (vsaModel live)).W Φ))
      (jalx_80003220 live (fun p hp => hlive _ (interp_code_80003220 p hp)))
      interp_code_80003220 (by decide) hOut (hsg.narrow hneed) hneed hsg.le hn0 (by omega)
      hsl.2 hbb
    iframe He Hcode Hae Hfr Hms Hst Hw HOut HK
    isplitl []
    · ipureintro
      refine ⟨hregs, fun b hb => ?_⟩
      rw [hsl.1] at hb; simp only [InExt] at hb ⊢; have := hfg.lo; omega
    iintro %R2 %w0 %w1 %w2 %st1 %v %hE %hk2 #Hv Hms Hst Hw HOut HK
    have hk2' := hk2.calleeSaved_upd (x := 1) (by decide) (BitVec.ofNat 64 (0x80003220 + 4))
    have hkR : KeepRegs calleeSaved R (upd R2 1 (BitVec.ofNat 64 (0x80003220 + 4))) :=
      KeepRegs.trans hk1 hk2'
    iapply argsCopy (wpW _) (R := upd R2 1 (BitVec.ofNat 64 (0x80003220 + 4))) (Mt0 := Mt) hlive hfg
      (by ix_reg; rw [keep_reg hk2 (by decide)]; exact hregs.sp) hsp1 hut1
      (fun a h1 _ => hlo1 a h1) hl hlen
    iframe Hms Hcode
    isplit
    · iintro %R3 %Mt3 %hne %hcp Hms
      obtain ⟨hh3, hk3⟩ := hcp.head hkR hh
      cases es with
      | nil =>
        exfalso
        have := List.drop_eq_nil_iff.mp hrest.symm
        omega
      | cons e2 es2 =>
        iapply evalArgsP_all hlive Core d env (e2 :: es2) Φ st1 (idx + 1) f all (pre ++ [v]) aX aE s
          sret0 R3 Mt3 m' n0 Out (List.cons_ne_nil _ _) hrest (by simp [hpre]) hlen hh3 hfg hsg hn0
          hall hOut
        iframe Hms Hcode Hast Hfr Hst Hw HOut HE
        isplitl []
        · iapply argVals_step N hcp hpre
          iframe Hargs Hv
        isplit
        · iintro %R4 %Mt4 %st4 %vs %hA %⟨hk4, h16, hut4⟩ Hms Hvals Hst Hw HOut
          ihave HK := and_elim_l $$ HK
          rw [List.append_assoc, List.singleton_append]
          iapply HK $$ %R4 %Mt4 %st4 %(v :: vs) %(EvalArgs.cons _ _ _ _ _ _ _ _ _ hE hA)
            %⟨KeepRegs.trans hk3 hk4, h16, hcp.untouched.trans hut4⟩ Hms Hvals Hst Hw HOut
        · iapply and_elim_r $$ HK
    · iintro %R3 %Mt3 %heq %hcp Hms
      obtain ⟨_, hk3⟩ := hcp.head hkR hh
      have hes : es = [] := by rw [hrest]; exact List.drop_eq_nil_of_le (by omega)
      subst hes
      ihave HK := and_elim_l $$ HK
      iapply HK $$ %R3 %Mt3 %st1 %([v] : List Value) %(EvalArgs.cons _ _ _ _ _ _ _ _ _ hE (EvalArgs.nil _ _ _))
        %⟨hk3, by rw [hcp.a6, heq], hcp.untouched⟩ Hms [] Hst Hw HOut
      iapply argVals_step N hcp hpre
      iframe Hargs Hv

end Modes


end VsaIris.Interp
