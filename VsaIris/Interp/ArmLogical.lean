import VsaIris.Interp.NewlibCall

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

theorem logNode_of_repr {m : Mem} {P : Nat → Prop} {aX : BitVec 64} {op : LogOp} {l r : Expr}
    (h : ExprReprWithin m P aX.toNat (.logical op l r)) (hg : ∀ k, P k → ReadOK k) :
    ∃ aL aR : Nat, BinNode m P aX 7 (logOpTok op) (BitVec.ofNat 64 aL) (BitVec.ofNat 64 aR) ∧
      ExprReprWithin m P aL l ∧ ExprReprWithin m P aR r ∧ aL < 2 ^ 64 ∧ aR < 2 ^ 64 := by
  cases h with
  | logical h6 c6 hop cop hl cl hrl hr cr hrr =>
    rename_i aL aR
    have g0 := hg _ (c6 0 (by omega)); have g3 := hg _ (c6 3 (by omega))
    have g8 := hg _ (cop 0 (by omega)); have g16 := hg _ (cl 0 (by omega))
    have g31 := hg _ (cr 7 (by omega))
    have e8 : (aX + 8#64).toNat = aX.toNat + 8 := by
      have := g31.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e16 : (aX + 16#64).toNat = aX.toNat + 16 := by
      have := g31.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e24 : (aX + 24#64).toNat = aX.toNat + 24 := by
      have := g31.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have htok : logOpTok op < 2 ^ 31 := by cases op <;> decide
    refine ⟨aL, aR, ⟨?_, ?_, ?_, ?_, ?_, g0.lo, ?_, ?_, ?_⟩, hrl, hrr, readLE_lt hl, readLE_lt hr⟩
    · exact ldv_lw_read32 h6 (by decide)
    · exact ldv_lwu_read32 h6
    · rw [e8]; exact ldv_lw_read32 hop htok
    · rw [e16]; exact ldv_ld_read64 hl
    · rw [e24]; exact ldv_ld_read64 hr
    · have := g31.hi; simp only [Nat.add_zero] at *; omega
    · have h0 := g0.off; have h3 := g3.off; have h8' := g8.off; have h16 := g16.off
      have h31 := g31.off
      simp only [Nat.add_zero] at *; omega
    · intro a ha
      simp only [List.mem_append, mem_accAddrs_iff] at ha
      rcases ha with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
      · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + j := ⟨a - aX.toNat, by omega⟩
        exact ⟨c6 j (by omega), isSome_of_readLE h6 (by omega)⟩
      · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + 8 + j := ⟨a - (aX.toNat + 8), by omega⟩
        exact ⟨cop j (by omega), isSome_of_readLE hop (by omega)⟩
      · by_cases hj : a < aX.toNat + 24
        · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + 16 + j := ⟨a - (aX.toNat + 16), by omega⟩
          exact ⟨cl j (by omega), isSome_of_readLE hl (by omega)⟩
        · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + 24 + j := ⟨a - (aX.toNat + 24), by omega⟩
          exact ⟨cr j (by omega), isSome_of_readLE hr (by omega)⟩

abbrev unView (a : Nat) : List Nat := accAddrs a 4 ++ accAddrs (a + 8) 4 ++ accAddrs (a + 16) 8

structure UnNode (m : Mem) (P : Nat → Prop) (aX : BitVec 64) (tok : Nat) (aC : BitVec 64) : Prop where
  kind : ldv .lw m aX.toNat = 8#64
  kindu : ldv .lwu m aX.toNat = 8#64
  op : ldv .lw m (aX + 8#64).toNat = BitVec.ofNat 64 tok
  child : ldv .ld m (aX + 16#64).toNat = aC
  lo : 0x80000000 ≤ aX.toNat
  hi : aX.toNat + 24 ≤ 0x100000000
  off : aX.toNat + 24 ≤ Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 16 ≤ aX.toNat
  view : ∀ a ∈ unView aX.toNat, P a ∧ (m[a]?).isSome

theorem unNode_of_repr {m : Mem} {P : Nat → Prop} {aX : BitVec 64} {op : UnOp} {e : Expr}
    (h : ExprReprWithin m P aX.toNat (.unary op e)) (hg : ∀ k, P k → ReadOK k) :
    ∃ aC : Nat, UnNode m P aX (unOpTok op) (BitVec.ofNat 64 aC) ∧ ExprReprWithin m P aC e ∧
      aC < 2 ^ 64 := by
  cases h with
  | unary h8 c8 hop cop hc cc hrc =>
    rename_i aC
    have g0 := hg _ (c8 0 (by omega)); have g3 := hg _ (c8 3 (by omega))
    have g8 := hg _ (cop 0 (by omega))
    have g23 := hg _ (cc 7 (by omega))
    have e8 : (aX + 8#64).toNat = aX.toNat + 8 := by
      have := g23.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e16 : (aX + 16#64).toNat = aX.toNat + 16 := by
      have := g23.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have htok : unOpTok op < 2 ^ 31 := by cases op <;> decide
    refine ⟨aC, ⟨?_, ?_, ?_, ?_, g0.lo, ?_, ?_, ?_⟩, hrc, readLE_lt hc⟩
    · exact ldv_lw_read32 h8 (by decide)
    · exact ldv_lwu_read32 h8
    · rw [e8]; exact ldv_lw_read32 hop htok
    · rw [e16]; exact ldv_ld_read64 hc
    · have := g23.hi; simp only [Nat.add_zero] at *; omega
    · have h0 := g0.off; have h3 := g3.off; have h8' := g8.off
      have h23 := g23.off
      simp only [Nat.add_zero] at *; omega
    · intro a ha
      simp only [List.mem_append, mem_accAddrs_iff] at ha
      rcases ha with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
      · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + j := ⟨a - aX.toNat, by omega⟩
        exact ⟨c8 j (by omega), isSome_of_readLE h8 (by omega)⟩
      · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + 8 + j := ⟨a - (aX.toNat + 8), by omega⟩
        exact ⟨cop j (by omega), isSome_of_readLE hop (by omega)⟩
      · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + 16 + j := ⟨a - (aX.toNat + 16), by omega⟩
        exact ⟨cc j (by omega), isSome_of_readLE hc (by omega)⟩

structure EvalSaved3 (Mt : Mem) (s ret v8 v9 v18 : BitVec 64) : Prop where
  ra : ldv .ld Mt (s.toNat - 1088 + 1080) = ret
  s0 : ldv .ld Mt (s.toNat - 1088 + 1072) = v8
  s1 : ldv .ld Mt (s.toNat - 1088 + 1064) = v9
  s2 : ldv .ld Mt (s.toNat - 1088 + 1056) = v18

theorem EvalSaved3.store {Mt : Mem} {s ret v8 v9 v18 : BitVec 64}
    (h : EvalSaved3 Mt s ret v8 v9 v18) {a w : Nat} (v : BitVec 64)
    (ha : a + w ≤ s.toNat - 1088 + 1056) :
    EvalSaved3 (writeLog Mt [(a, w, v)]) s ret v8 v9 v18 :=
  ⟨by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.ra,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s0,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s1,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s2⟩

theorem ldv_ld_congr {M M' : Mem} {a : Nat} (h : ∀ j, j < 8 → imgM M' (a + j) = imgM M (a + j)) :
    ldv .ld M' a = ldv .ld M a := by
  unfold ldv bytesAt
  congr 1
  apply List.map_congr_left
  intro j hj
  exact h j (List.mem_range.1 hj)

theorem EvalSaved3.agree {Mt Mt' : Mem} {s ret v8 v9 v18 : BitVec 64}
    (h : EvalSaved3 Mt s ret v8 v9 v18)
    (hm : ∀ a, s.toNat - 1088 + 1056 ≤ a → a < s.toNat - 1088 + 1088 → imgM Mt' a = imgM Mt a) :
    EvalSaved3 Mt' s ret v8 v9 v18 :=
  ⟨by rw [ldv_ld_congr fun j hj => hm _ (by omega) (by omega)]; exact h.ra,
   by rw [ldv_ld_congr fun j hj => hm _ (by omega) (by omega)]; exact h.s0,
   by rw [ldv_ld_congr fun j hj => hm _ (by omega) (by omega)]; exact h.s1,
   by rw [ldv_ld_congr fun j hj => hm _ (by omega) (by omega)]; exact h.s2⟩

syntax "ix_saved3 " term " using " term : tactic
macro_rules
  | `(tactic| ix_saved3 $h using $hoff) => `(tactic| (
      (try unfold slotWrite);
      repeat refine EvalSaved3.store ?_ _ (by first | omega | (rw [($hoff:term)] <;> first | omega | decide));
      exact $h))

syntax "ix_fwdF " term : tactic
macro_rules
  | `(tactic| ix_fwdF $hoff) => `(tactic| (
      (try simp only [slotWrite]);
      (try simp (disch := decide) only [($hoff:term)]);
      (try simp only [Nat.add_assoc, Nat.reduceAdd]);
      simp (disch := first | omega | sx_addr) only [ldv_ld_hit_eq, ldv_ld_miss, ldv_lw_miss,
        ldv_lw_store8]))

section Truthy

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

omit I in

theorem ms_congrSet {pc : BitVec 64} {R : Nat → BitVec 64} {S T : Nat → Prop} {M : Mem}
    (h : ∀ k, S k ↔ T k) : ms (GF := GF) pc R S M ⊢ ms pc R T M := by
  unfold ms
  iintro ⟨Hpc, Hra, Hregs, HS⟩
  iframe Hpc Hra Hregs
  iapply ownSet_iff _ h $$ HS

theorem ms_callValRef (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64} {clob : List Nat}
    {Res : (Nat → BitVec 64) → Prop}
    (hexec : JalExec (vsaModel live) i code entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {p w0 w1 w2 : BitVec 64} {v : Value}
    {a0 a8 a16 : Nat} (ha : p.toNat = a0 ∧ a8 = a0 + 8 ∧ a16 = a0 + 16)
    (hS : ∀ k, InExt (p.toNat, 24) k → S k) (hg : SlotGeom p)
    (h0 : ldv .ld Mt a0 = w0) (h8 : ldv .ld Mt a8 = w1) (h16 : ldv .ld Mt a16 = w2) :
    ⌜R 10 = p⌝ ∗
      helperSpec (vsaModel live) Wp entry clob (fun rv => rv 10 = p)
        iprop(valAt N p.toNat v ∗ ⌜SlotGeom p⌝)
        (fun rv' => iprop(valAt N p.toNat v ∗ ⌜Res rv'⌝)) ∗
      codeRes ∗ □ valOf N v w0 w1 w2 ∗ ms (BitVec.ofNat 64 i) R S Mt ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜(∀ x ∈ fRegs, x ∉ clob → R' x = R x) ∧ Res R' ∧
          ∀ k, S k → ¬ InExt (p.toNat, 24) k → imgM Mt' k = imgM Mt k⌝ -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt' -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  obtain ⟨e0, rfl, rfl⟩ := ha
  subst e0
  have hsl : ∀ k, S k ↔ ((S k ∧ ¬ InExt (p.toNat, 24) k) ∨ InExt (p.toNat, 24) k) := fun k => by
    constructor
    · intro h; by_cases h' : InExt (p.toNat, 24) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hS k h
  iintro ⟨%h10, Hspec, #Hcode, #Hv, Hms, Hk⟩
  ihave Hms := ms_congrSet hsl $$ Hms
  ihave ⟨Hms, Hslot⟩ := ms_split (fun k h1 h2 => h1.2 h2) $$ Hms
  ihave Hval := valAt_of_img N (a := p.toNat) (v := v) (mv := imgM Mt) $$ [Hslot]
  · iframe Hslot
    unfold valImg
    rw [← ldv_ld_imgW, ← ldv_ld_imgW, ← ldv_ld_imgW, h0, h8, h16]
    iexact Hv
  iapply ms_callHelper Wp hexec hcode hal
  iframe Hspec Hcode Hms %h10 Hval %hg
  iintro %R' %hkeep ⟨Hval, %hres⟩ Hms
  ihave ⟨%Ms, HsS, -⟩ := valAt_tracked N _ _ $$ Hval
  ihave ⟨%M', Hms, %⟨hM1, -, -⟩⟩ := ms_join $$ [$]
  ihave Hms := ms_congrSet (fun k => (hsl k).symm) $$ Hms
  iapply Hk $$ %R' %M' %⟨hkeep, hres, fun k hk hn => hM1 k ⟨hk, hn⟩⟩ Hms

theorem ms_callTruthy (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code valueTruthyPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {p w0 w1 w2 : BitVec 64} {v : Value}
    {a0 a8 a16 : Nat} (ha : p.toNat = a0 ∧ a8 = a0 + 8 ∧ a16 = a0 + 16)
    (hS : ∀ k, InExt (p.toNat, 24) k → S k) (hg : SlotGeom p)
    (h0 : ldv .ld Mt a0 = w0) (h8 : ldv .ld Mt a8 = w1) (h16 : ldv .ld Mt a16 = w2) :
    ⌜R 10 = p⌝ ∗ valueTruthySpec (vsaModel live) N Wp p v ∗ codeRes ∗ □ valOf N v w0 w1 w2 ∗
      ms (BitVec.ofNat 64 i) R S Mt ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜(∀ x ∈ fRegs, x ∉ [10, 14, 15] → R' x = R x) ∧
          R' 10 = (if v.truthy then 1#64 else 0#64) ∧
          ∀ k, S k → ¬ InExt (p.toNat, 24) k → imgM Mt' k = imgM Mt k⌝ -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt' -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  unfold valueTruthySpec
  exact ms_callValRef Wp (Res := fun rv' => rv' 10 = if v.truthy then 1#64 else 0#64)
    hexec hcode hal ha hS hg h0 h8 h16

end Truthy

theorem upd_eta {R : Nat → BitVec 64} {k : Nat} {v : BitVec 64} (h : R k = v) : upd R k v = R := by
  funext r; by_cases hr : r = k
  · subst hr; rw [upd_same, h]
  · rw [upd_other _ _ hr]

theorem iw_regFact {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {pc : BitVec 64} {R : Nat → BitVec 64}
    {Mt : Mem} {k : Nat} {v : BitVec 64} (h : R k = v) (hk : IW live Dt DA S Q pc (upd R k v) Mt) :
    IW live Dt DA S Q pc R Mt := by
  rwa [upd_eta h] at hk

theorem boolBit_ne (t : Bool) : ((if t then 1#64 else 0#64) != 0#64) = t := by
  cases t <;> decide

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

abbrev seqzV (x : BitVec 64) : BitVec 64 := zero_extend (m := 64) (bool_to_bit (zopz0zI_u x 1#64))

theorem seqzBit_ne (t : Bool) : (seqzV (if t then 1#64 else 0#64) != 0#64) = !t := by
  cases t <;> decide

theorem toInt_neg_wrap (x : BitVec 64) : (-x).toInt = wrap64 (-x.toInt) := by
  unfold wrap64; rw [BitVec.toInt_neg, BitVec.toInt_ofInt]

end VsaIris.Interp
