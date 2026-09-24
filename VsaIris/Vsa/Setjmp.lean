import VsaIris.Interp.Abort
import Vsa.Sim.EnvNewSpec

/-!
# `setjmp` (H5)

`setjmp(jb)` (`0x80006ffc`) stores `ra`, `s0`–`s11` and `sp` into the first
14 words of the `jmp_buf` and returns 0. Its spec returns the written image
with those words named: what `interp_run`'s proof records (`TopLanding`) and
`longjmp` reads back (`landingRegs`).

```
80006ffc: sd ra,0(a0); sd s0,8(a0); … sd s11,96(a0); sd sp,104(a0)
80007034: li a0,0
80007038: ret
```
-/

namespace VsaIris.Newlib.Setjmp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Sim VsaIris.Inst VsaIris.Interp VsaIris.Newlib.Sites VsaIris.Newlib.Exit
  VsaIris.Newlib.MainErr

/-! ## Reading back a log of 8-byte stores -/

theorem read64_writeLog_out (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    ∀ log : List WEntry, (∀ e ∈ log, e.2.1 = 8 ∧ (a + 8 ≤ e.1 ∨ e.1 + 8 ≤ a)) →
      Vsa.MemRepr.read64 (writeLog m log) a = Vsa.MemRepr.read64 m a
  | [], _ => rfl
  | e :: log, h => by
    obtain ⟨a', w, d⟩ := e
    obtain ⟨hw, hd⟩ := h (a', w, d) List.mem_cons_self
    simp only at hw hd
    subst hw
    show Vsa.MemRepr.read64 (writeLog (applyW m (a', 8, d)) log) a = _
    rw [read64_writeLog_out (applyW m (a', 8, d)) a log (fun e he => h e (.tail _ he))]
    exact read64_writeMap8_disjoint m a a' _ hd

/-- A pairwise-disjoint log of 8-byte stores reads back each stored word. -/
theorem read64_writeLog_sd (m : Std.ExtHashMap Nat (BitVec 8)) :
    ∀ log : List WEntry, (∀ e ∈ log, e.2.1 = 8) →
      log.Pairwise (fun e f => e.1 + 8 ≤ f.1 ∨ f.1 + 8 ≤ e.1) →
      ∀ a v, (a, 8, v) ∈ log → Vsa.MemRepr.read64 (writeLog m log) a = some v.toNat
  | [], _, _, _, _, h => nomatch h
  | e :: log, hw, hp, a, v, hin => by
    obtain ⟨a', w, d⟩ := e
    have hw' : w = 8 := hw (a', w, d) List.mem_cons_self
    subst hw'
    show Vsa.MemRepr.read64 (writeLog (applyW m (a', 8, d)) log) a = _
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hin with he | hin
    · cases he
      rw [read64_writeLog_out _ a log (fun f hf => ⟨hw f (.tail _ hf), hp.1 f hf⟩)]
      show Vsa.MemRepr.read64 (writeMap8 m a (sdData_val v)) a = _
      rw [read64_writeMap8, sdData_toNat]
    · exact read64_writeLog_sd _ log (fun f hf => hw f (.tail _ hf)) hp.2 a v hin

/-! ## The segment -/

#derive_case setjmpSeg chain
  [(0x80006ffc#64, 0x00153023#32),
   (0x80007000#64, 0x00853423#32),
   (0x80007004#64, 0x00953823#32),
   (0x80007008#64, 0x01253c23#32),
   (0x8000700c#64, 0x03353023#32),
   (0x80007010#64, 0x03453423#32),
   (0x80007014#64, 0x03553823#32),
   (0x80007018#64, 0x03653c23#32),
   (0x8000701c#64, 0x05753023#32),
   (0x80007020#64, 0x05853423#32),
   (0x80007024#64, 0x05953823#32),
   (0x80007028#64, 0x05a53c23#32),
   (0x8000702c#64, 0x07b53023#32),
   (0x80007030#64, 0x06253423#32),
   (0x80007034#64, 0x00000513#32)] terminator ⟨0x80007038#64, 0x00008067#32, 0x67#8, 0x80#8,
      0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

abbrev sjL (jbp r s : BitVec 64) (cs : Nat → BitVec 64) : GRegs :=
  [(10, jbp), (1, r), (8, cs 8), (9, cs 9), (18, cs 18), (19, cs 19), (20, cs 20), (21, cs 21), (22, cs 22), (23, cs 23), (24, cs 24), (25, cs 25), (26, cs 26), (27, cs 27), (2, s)]

/-- The `jmp_buf` at `jbp`: 8-aligned in RAM above the HTIF words. -/
structure JbAt (jbp : BitVec 64) : Prop where
  lo : Vsa.Sim.tohostAddr + 16 ≤ jbp.toNat
  hi : jbp.toNat + 112 ≤ 0x100000000
  align : jbp.toNat % 8 = 0

theorem jb_off8 (jbp : BitVec 64) (hg : JbAt jbp) (off : Nat) (imm : BitVec 12)
    (himm : (sign_extend (m := 64) imm : BitVec 64).toNat = off) (hoff : off < 112) :
    ∀ x : BitVec 64, x = jbp + sign_extend (m := 64) imm → x.toNat = jbp.toNat + off := by
  intro x hx
  have h2 := hg.hi
  rw [hx, addr_off _ _ off himm (by omega)]

theorem sj_facts {m : Std.ExtHashMap Nat (BitVec 8)} {jbp r s : BitVec 64} {cs : Nat → BitVec 64}
    (hcode : setjmpCodeLoaded m) (hg : JbAt jbp) (hr : r.toNat % 4 = 0) :
    ChainFacts m m (sjL jbp r s cs) [] setjmpSeg := by
  have h1 := hg.lo; have h2 := hg.hi; have h3 := hg.align
  unfold tohostAddr at h1
  unfold setjmpSeg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.setjmpCode_at_"
  · exact sdFact (ea := jbp.toNat + 0) rfl (jb_off8 jbp hg 0 (0x000#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := jbp.toNat + 8) rfl (jb_off8 jbp hg 8 (0x008#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := jbp.toNat + 16) rfl (jb_off8 jbp hg 16 (0x010#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := jbp.toNat + 24) rfl (jb_off8 jbp hg 24 (0x018#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := jbp.toNat + 32) rfl (jb_off8 jbp hg 32 (0x020#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := jbp.toNat + 40) rfl (jb_off8 jbp hg 40 (0x028#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := jbp.toNat + 48) rfl (jb_off8 jbp hg 48 (0x030#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := jbp.toNat + 56) rfl (jb_off8 jbp hg 56 (0x038#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := jbp.toNat + 64) rfl (jb_off8 jbp hg 64 (0x040#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := jbp.toNat + 72) rfl (jb_off8 jbp hg 72 (0x048#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := jbp.toNat + 80) rfl (jb_off8 jbp hg 80 (0x050#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := jbp.toNat + 88) rfl (jb_off8 jbp hg 88 (0x058#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := jbp.toNat + 96) rfl (jb_off8 jbp hg 96 (0x060#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := jbp.toNat + 104) rfl (jb_off8 jbp hg 104 (0x068#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · have e : ∀ x : BitVec 64, x = r →
        (BitVec.update (x + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
      intro x hx; rw [hx, ret_tgt r hr]; exact hr
    exact e _ rfl

theorem sj_log (jbp r s : BitVec 64) (cs : Nat → BitVec 64) :
    (segOut setjmpSeg (sjL jbp r s cs) []).log =
      [((jbp + sign_extend (m := 64) (0x000#12)).toNat, 8, r),
       ((jbp + sign_extend (m := 64) (0x008#12)).toNat, 8, cs 8),
       ((jbp + sign_extend (m := 64) (0x010#12)).toNat, 8, cs 9),
       ((jbp + sign_extend (m := 64) (0x018#12)).toNat, 8, cs 18),
       ((jbp + sign_extend (m := 64) (0x020#12)).toNat, 8, cs 19),
       ((jbp + sign_extend (m := 64) (0x028#12)).toNat, 8, cs 20),
       ((jbp + sign_extend (m := 64) (0x030#12)).toNat, 8, cs 21),
       ((jbp + sign_extend (m := 64) (0x038#12)).toNat, 8, cs 22),
       ((jbp + sign_extend (m := 64) (0x040#12)).toNat, 8, cs 23),
       ((jbp + sign_extend (m := 64) (0x048#12)).toNat, 8, cs 24),
       ((jbp + sign_extend (m := 64) (0x050#12)).toNat, 8, cs 25),
       ((jbp + sign_extend (m := 64) (0x058#12)).toNat, 8, cs 26),
       ((jbp + sign_extend (m := 64) (0x060#12)).toNat, 8, cs 27),
       ((jbp + sign_extend (m := 64) (0x068#12)).toNat, 8, s)] := rfl

theorem sj_pc (jbp r s : BitVec 64) (cs : Nat → BitVec 64) (hr : r.toNat % 4 = 0) :
    evalBlocksPC 0x80006ffc#64 (SegEvalState.init (sjL jbp r s cs) []) setjmpSeg = r := by
  have e : ∀ x : BitVec 64, x = r →
      BitVec.update (x + sign_extend (m := 64) (0x000#12)) 0 0#1 = r := by
    intro x hx; rw [hx, ret_tgt r hr]
  exact e _ rfl

theorem sj_fin10 (jbp r s : BitVec 64) (cs : Nat → BitVec 64) :
    finReg setjmpSeg (sjL jbp r s cs) [] 10 = 0#64 := by
  show 0#64 + sign_extend (m := 64) (0x000#12) = _; decide

/-- The word `setjmp` stores in slot `k`. -/
def sjVal (r s : BitVec 64) (cs : Nat → BitVec 64) (k : Nat) : BitVec 64 :=
  [r, cs 8, cs 9, cs 18, cs 19, cs 20, cs 21, cs 22, cs 23, cs 24, cs 25, cs 26, cs 27, s].getD k 0

/-- The words `setjmp` leaves in the `jmp_buf`: `ra`, `s0`–`s11`, `sp`. -/
structure SetjmpImg (jbp r s : BitVec 64) (cs : Nat → BitVec 64) (img : Nat → BitVec 8) :
    Prop where
  words : ∀ k, k < 14 → imgW img (jbp.toNat + 8 * k) = sjVal r s cs k

theorem sj_read (jbp r s : BitVec 64) (cs : Nat → BitVec 64) (hg : JbAt jbp)
    (m : Std.ExtHashMap Nat (BitVec 8)) :
    ∀ k, k < 14 → Vsa.MemRepr.read64 (writeLog m (segOut setjmpSeg (sjL jbp r s cs) []).log)
      (jbp.toNat + 8 * k) = some (sjVal r s cs k).toNat := by
  have h2 := hg.hi
  have e0 : (jbp + sign_extend (m := 64) (0x000#12)).toNat = jbp.toNat + 0 :=
    addr_off _ _ 0 (by decide) (by omega)
  have e1 : (jbp + sign_extend (m := 64) (0x008#12)).toNat = jbp.toNat + 8 :=
    addr_off _ _ 8 (by decide) (by omega)
  have e2 : (jbp + sign_extend (m := 64) (0x010#12)).toNat = jbp.toNat + 16 :=
    addr_off _ _ 16 (by decide) (by omega)
  have e3 : (jbp + sign_extend (m := 64) (0x018#12)).toNat = jbp.toNat + 24 :=
    addr_off _ _ 24 (by decide) (by omega)
  have e4 : (jbp + sign_extend (m := 64) (0x020#12)).toNat = jbp.toNat + 32 :=
    addr_off _ _ 32 (by decide) (by omega)
  have e5 : (jbp + sign_extend (m := 64) (0x028#12)).toNat = jbp.toNat + 40 :=
    addr_off _ _ 40 (by decide) (by omega)
  have e6 : (jbp + sign_extend (m := 64) (0x030#12)).toNat = jbp.toNat + 48 :=
    addr_off _ _ 48 (by decide) (by omega)
  have e7 : (jbp + sign_extend (m := 64) (0x038#12)).toNat = jbp.toNat + 56 :=
    addr_off _ _ 56 (by decide) (by omega)
  have e8 : (jbp + sign_extend (m := 64) (0x040#12)).toNat = jbp.toNat + 64 :=
    addr_off _ _ 64 (by decide) (by omega)
  have e9 : (jbp + sign_extend (m := 64) (0x048#12)).toNat = jbp.toNat + 72 :=
    addr_off _ _ 72 (by decide) (by omega)
  have e10 : (jbp + sign_extend (m := 64) (0x050#12)).toNat = jbp.toNat + 80 :=
    addr_off _ _ 80 (by decide) (by omega)
  have e11 : (jbp + sign_extend (m := 64) (0x058#12)).toNat = jbp.toNat + 88 :=
    addr_off _ _ 88 (by decide) (by omega)
  have e12 : (jbp + sign_extend (m := 64) (0x060#12)).toNat = jbp.toNat + 96 :=
    addr_off _ _ 96 (by decide) (by omega)
  have e13 : (jbp + sign_extend (m := 64) (0x068#12)).toNat = jbp.toNat + 104 :=
    addr_off _ _ 104 (by decide) (by omega)
  intro k hk
  rw [sj_log, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13]
  apply read64_writeLog_sd
  · intro e he; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, _root_.or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    repeat' apply And.intro
    all_goals first
      | exact Or.inl (by omega)
      | exact Or.inr (by omega)
      | exact fun _ h => h.elim
  · have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
        k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 := by omega
    rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [sjVal]

theorem sj_img (jbp r s : BitVec 64) (cs : Nat → BitVec 64) (hg : JbAt jbp)
    (W : List (Nat × BitVec 8)) :
    SetjmpImg jbp r s cs (fun a => newByte setjmpSeg (sjL jbp r s cs) [] W a) where
  words k hk := by
    apply BitVec.eq_of_toNat_eq
    exact imgW_read64 (sj_read jbp r s cs hg (wbase W) k hk)

theorem sj_logN (jbp r s : BitVec 64) (cs : Nat → BitVec 64) (hg : JbAt jbp) :
    (segOut setjmpSeg (sjL jbp r s cs) []).log =
      [(jbp.toNat + 0, 8, r),
       (jbp.toNat + 8, 8, cs 8),
       (jbp.toNat + 16, 8, cs 9),
       (jbp.toNat + 24, 8, cs 18),
       (jbp.toNat + 32, 8, cs 19),
       (jbp.toNat + 40, 8, cs 20),
       (jbp.toNat + 48, 8, cs 21),
       (jbp.toNat + 56, 8, cs 22),
       (jbp.toNat + 64, 8, cs 23),
       (jbp.toNat + 72, 8, cs 24),
       (jbp.toNat + 80, 8, cs 25),
       (jbp.toNat + 88, 8, cs 26),
       (jbp.toNat + 96, 8, cs 27),
       (jbp.toNat + 104, 8, s)] := by
  have h2 := hg.hi
  have e0 : (jbp + sign_extend (m := 64) (0x000#12)).toNat = jbp.toNat + 0 :=
    addr_off _ _ 0 (by decide) (by omega)
  have e1 : (jbp + sign_extend (m := 64) (0x008#12)).toNat = jbp.toNat + 8 :=
    addr_off _ _ 8 (by decide) (by omega)
  have e2 : (jbp + sign_extend (m := 64) (0x010#12)).toNat = jbp.toNat + 16 :=
    addr_off _ _ 16 (by decide) (by omega)
  have e3 : (jbp + sign_extend (m := 64) (0x018#12)).toNat = jbp.toNat + 24 :=
    addr_off _ _ 24 (by decide) (by omega)
  have e4 : (jbp + sign_extend (m := 64) (0x020#12)).toNat = jbp.toNat + 32 :=
    addr_off _ _ 32 (by decide) (by omega)
  have e5 : (jbp + sign_extend (m := 64) (0x028#12)).toNat = jbp.toNat + 40 :=
    addr_off _ _ 40 (by decide) (by omega)
  have e6 : (jbp + sign_extend (m := 64) (0x030#12)).toNat = jbp.toNat + 48 :=
    addr_off _ _ 48 (by decide) (by omega)
  have e7 : (jbp + sign_extend (m := 64) (0x038#12)).toNat = jbp.toNat + 56 :=
    addr_off _ _ 56 (by decide) (by omega)
  have e8 : (jbp + sign_extend (m := 64) (0x040#12)).toNat = jbp.toNat + 64 :=
    addr_off _ _ 64 (by decide) (by omega)
  have e9 : (jbp + sign_extend (m := 64) (0x048#12)).toNat = jbp.toNat + 72 :=
    addr_off _ _ 72 (by decide) (by omega)
  have e10 : (jbp + sign_extend (m := 64) (0x050#12)).toNat = jbp.toNat + 80 :=
    addr_off _ _ 80 (by decide) (by omega)
  have e11 : (jbp + sign_extend (m := 64) (0x058#12)).toNat = jbp.toNat + 88 :=
    addr_off _ _ 88 (by decide) (by omega)
  have e12 : (jbp + sign_extend (m := 64) (0x060#12)).toNat = jbp.toNat + 96 :=
    addr_off _ _ 96 (by decide) (by omega)
  have e13 : (jbp + sign_extend (m := 64) (0x068#12)).toNat = jbp.toNat + 104 :=
    addr_off _ _ 104 (by decide) (by omega)
  rw [sj_log, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13]

/-! ## The rule -/

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem sepL_calleeSaved_all (f : Nat → BitVec 64) :
    sepL (GF := GF) calleeSaved (fun q => q ↦ᵣ f q) ⊣⊢
      (8 : Nat) ↦ᵣ f 8 ∗ (9 : Nat) ↦ᵣ f 9 ∗ (18 : Nat) ↦ᵣ f 18 ∗ (19 : Nat) ↦ᵣ f 19 ∗
      (20 : Nat) ↦ᵣ f 20 ∗ (21 : Nat) ↦ᵣ f 21 ∗ (22 : Nat) ↦ᵣ f 22 ∗ (23 : Nat) ↦ᵣ f 23 ∗
      (24 : Nat) ↦ᵣ f 24 ∗ (25 : Nat) ↦ᵣ f 25 ∗ (26 : Nat) ↦ᵣ f 26 ∗ (27 : Nat) ↦ᵣ f 27 ∗ emp := by
  show sepL [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] _ ⊣⊢ _
  simp only [sepL_cons, sepL_nil]
  exact .rfl

/-- **`setjmp(jb)`**, for either WP: it fills the first 14 words of the
`jmp_buf` with `ra` (the return address), `s0`–`s11` and `sp`, and returns
0. -/
theorem setjmp_spec (live : Nat → Prop) (hlive : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) (jbp s : BitVec 64) (cs : Nat → BitVec 64)
    (img0 : Nat → BitVec 8) (hg : JbAt jbp) :
    ⊢ fnSpecW Wp 0x80006ffc#64
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ (10 : Nat) ↦ᵣ jbp ∗ sp ↦ᵣ s ∗
        sepL calleeSaved (fun q => q ↦ᵣ cs q) ∗ ownImg (InExt (jbp.toNat, 112)) img0 ∗ binImg))
      (fun r => iprop((10 : Nat) ↦ᵣ 0#64 ∗ sp ↦ᵣ s ∗ sepL calleeSaved (fun q => q ↦ᵣ cs q) ∗
        (∃ img, ownImg (InExt (jbp.toNat, 112)) img ∗ ⌜SetjmpImg jbp r s cs img⌝))) := by
  have h2 := hg.hi
  have hcodeL := setjmpCode_text.live hlive
  unfold fnSpecW
  iintro !>
  iintro %r %Φ Hpc Hra ⟨%hr, Ha0, Hsp, Hsaved, HJ, #Himg⟩ Hk
  ihave #Hcode := instrAt_of_binImg setjmpCode_text $$ Himg
  ihave ⟨H8, H9, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, -⟩ :=
    (sepL_calleeSaved_all cs).1 $$ Hsaved
  ihave HJ := (ownImg_range_w _ _ _).1 $$ HJ
  unfold VsaIris.sp VsaIris.ra
  iapply wp_segW live Wp setjmpSeg (sjL jbp r s cs) [] 0x80006ffc#64
    (codeFoot setjmpCodeBase setjmpCode) (imgW8 jbp.toNat 112 img0) 15 (by decide)
    (by change ChainOK _ [10, 1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 2] _; decide)
    (by change KeysOK [10, 1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 2]; decide)
    (by change ∀ k ∈ wrChain setjmpSeg, k ∈ [10, 1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 2]
        decide)
    (fun a ha => by
      rw [sj_logN jbp r s cs hg]
      have : ¬ (jbp.toNat ≤ a ∧ a < jbp.toNat + 112) := fun h => by
        refine ha (a, img0 a) (List.mem_map.mpr ⟨a, ?_, rfl⟩) rfl
        rw [List.mem_range']; exact ⟨a - jbp.toNat, by omega, by omega⟩
      simp only [OutL]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega)
    (fun c hok ⟨_, hMR, _, _⟩ => sj_facts (setjmpCodeLoaded_of (code_present hok _ hMR hcodeL))
      hg hr)
  have f1 : finReg setjmpSeg (sjL jbp r s cs) [] 1 = r := rfl
  have f8 : finReg setjmpSeg (sjL jbp r s cs) [] 8 = cs 8 := rfl
  have f9 : finReg setjmpSeg (sjL jbp r s cs) [] 9 = cs 9 := rfl
  have f18 : finReg setjmpSeg (sjL jbp r s cs) [] 18 = cs 18 := rfl
  have f19 : finReg setjmpSeg (sjL jbp r s cs) [] 19 = cs 19 := rfl
  have f20 : finReg setjmpSeg (sjL jbp r s cs) [] 20 = cs 20 := rfl
  have f21 : finReg setjmpSeg (sjL jbp r s cs) [] 21 = cs 21 := rfl
  have f22 : finReg setjmpSeg (sjL jbp r s cs) [] 22 = cs 22 := rfl
  have f23 : finReg setjmpSeg (sjL jbp r s cs) [] 23 = cs 23 := rfl
  have f24 : finReg setjmpSeg (sjL jbp r s cs) [] 24 = cs 24 := rfl
  have f25 : finReg setjmpSeg (sjL jbp r s cs) [] 25 = cs 25 := rfl
  have f26 : finReg setjmpSeg (sjL jbp r s cs) [] 26 = cs 26 := rfl
  have f27 : finReg setjmpSeg (sjL jbp r s cs) [] 27 = cs 27 := rfl
  have f2 : finReg setjmpSeg (sjL jbp r s cs) [] 2 = s := rfl
  simp only [sjL] at f1 f8 f9 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f2
  simp only [sjL, sepL_cons, sepL_nil, sj_pc jbp r s cs hr, sj_fin10, f1, f8, f9, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f2]
  rw [← instrAt_eq]
  iframe Hpc Ha0 Hra H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hsp HJ Hcode
  iintro Hpc ⟨Ha0, Hra, H8, H9, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, Hsp, -⟩ HJ -
  iapply Hk $$ Hpc Hra
  iframe Ha0 Hsp
  isplitl [H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27]
  · iapply (sepL_calleeSaved_all cs).2
    iframe H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27
  iexists (fun a => newByte setjmpSeg (sjL jbp r s cs) [] (imgW8 jbp.toNat 112 img0) a)
  isplitl [HJ]
  · iapply (ownImg_range_w _ _ _).2
    rw [show sepL (imgW8 jbp.toNat 112 (fun a => newByte setjmpSeg (sjL jbp r s cs) []
        (imgW8 jbp.toNat 112 img0) a)) (fun p => p.1 ↦ₘ p.2) =
      sepL (imgW8 jbp.toNat 112 img0) (fun p => p.1 ↦ₘ newByte setjmpSeg (sjL jbp r s cs) []
        (imgW8 jbp.toNat 112 img0) p.1) by
      unfold imgW8; rw [VsaIris.sepL_map, VsaIris.sepL_map]]
    iexact HJ
  ipureintro
  exact sj_img jbp r s cs hg _

end Wp

end VsaIris.Newlib.Setjmp
