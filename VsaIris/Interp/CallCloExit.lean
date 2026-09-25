import VsaIris.Interp.CallCloBody
import VsaIris.Interp.LeafCalls

/-!
# The closure call's exits (lane E4)

For either WP, at the depth `d + 1` the body ran at:

* `cloExitN` (`0x80003954`, a normal end, or an empty body):
  `--in->call_depth` (the world back at `d`), `value_null(sret)`, the spills
  reloaded, the shared epilogue.
* `cloExitR` (`0x8000337c`, status `3`): `--in->call_depth`, the result slot
  `sp+144` copied to `sret`, the epilogue.

`ms_joinSlot144`: the lent result slot back into the frame.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr

section Exits

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The lent result slot back into the frame, at a tracking memory agreeing
with the run's on the rest. -/
theorem ms_joinSlot144 {pc : BitVec 64} {R : Nat → BitVec 64} {s : BitVec 64} {Mt : Mem}
    (hfg : EvalFrameG s) :
    ms (GF := GF) pc R (closureS s) Mt ∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat ⊢
      ∃ M, ms pc R (InExt (s.toNat - 1088, 1088)) M ∗ ⌜∀ b, closureS s b → imgM M b = imgM Mt b⌝ := by
  have h144 := evalSP_off' hfg 144 (by decide)
  unfold slot24 blockOwn
  iintro ⟨Hms, HA⟩
  ihave ⟨%g, HA⟩ := ownSet_fn _ $$ HA
  ihave ⟨%M2, HA⟩ := ownSet_mem _ g $$ HA
  ihave ⟨%M, Hms, %⟨h1, -, -⟩⟩ := ms_join $$ [Hms HA]
  · iframe Hms HA
  iexists M
  isplitl
  · iapply ms_iff (fun k => by
      simp only [closureS, InExt]; rw [h144]
      constructor
      · rintro (⟨h, _⟩ | h) <;> omega
      · intro h; by_cases h' : s.toNat - 1088 + 144 ≤ k ∧ k < s.toNat - 1088 + 144 + 24
        · exact .inr h'
        · exact .inl ⟨h, h'⟩) $$ Hms
  · ipureintro; exact h1

/-- **A normal end** (`0x80003954`), for either WP: the depth word back to
`d`, `value_null(sret)`, the spills reloaded, the epilogue; the caller gets its
callee-saved registers, its stack, `null` at `sret`, the world at depth `d`. -/
theorem cloExitN (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {ρ : Regime} {st : St} {d : Nat}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N Wp p)
    {s sret ret : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem} {n : Nat}
    (hfg : EvalFrameG s) (hsg : StackGeom s n) (hn : 1088 ≤ n) (hal : ret.toNat % 4 = 0)
    (hsp : rv 2 = s) (hinpG : RtErr.InpGeom (BitVec.ofNat 64 inp)) (hinpL : inp < 2 ^ 64)
    (hinpA : inp % 8 = 0) (hslg : SlotGeom sret)
    (hat : CloAt R Mt s (BitVec.ofNat 64 inp) sret ret rv) :
    codeRes ∗ ms 0x80003954#64 R (closureS s) Mt ∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat ∗
      slot24 sret.toNat ∗ world N L Room inp ρ st (d + 1) ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗
      (∀ rv' : Nat → BitVec 64, ⌜KeepRegs calleeSaved rv rv'⌝ -∗ regFile rv' -∗
        stackScratch s n -∗ valAt N sret.toNat .null -∗ world N L Room inp ρ st d -∗
        PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  have hsf := hfg.sf; have hs := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  have hinpN : (BitVec.ofNat 64 inp).toNat = inp := Nat.mod_eq_of_lt hinpL
  have hi8 : (BitVec.ofNat 64 inp + 8#64).toNat = inp + 8 := by
    have := hinpG.hi; rw [hinpN] at this
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hwd := world_depth (GF := GF) N L Room inp ρ st (d + 1)
  rw [show inp + interpDepthOff = inp + 8 from rfl] at hwd
  iintro ⟨#Hcode, Hms, Hsl, Hsr, Hw, Hst, Hk⟩
  ihave ⟨%M1, Hms, %hM1⟩ := ms_joinSlot144 hfg $$ [Hms Hsl]
  · iframe Hms Hsl
  ihave ⟨%dimg, Hd, %⟨hdv, hdle⟩, Hcl⟩ := hwd $$ Hw
  ihave ⟨%Md, Hd, %hMd⟩ := ownSet_trackedAt _ dimg $$ Hd
  ihave ⟨%M3, Hms, %⟨hM3f, hM3d, hdisj⟩⟩ := ms_join $$ [Hms Hd]
  · iframe Hms Hd
  have hi3 : inp + 8 + 4 ≤ s.toNat - 1088 ∨ s.toNat ≤ inp + 8 := by
    refine Classical.byContradiction fun hc => ?_
    exact hdisj (max (s.toNat - 1088) (inp + 8)) (by simp only [InExt]; omega)
      (by simp only [InExt]; omega)
  have hdep3 : imgLE (imgM M3) (inp + 8) 4 = d + 1 := by
    rw [imgLE_congr (img' := dimg) (fun i hi => (hM3d _ (by simp [InExt]; omega)).trans
      (hMd _ (by simp [InExt]; omega))), hdv]
  have hdl : ldv .lw M3 (BitVec.ofNat 64 inp + 8#64).toNat = BitVec.ofNat 64 (d + 1) := by
    rw [hi8]; exact ldvf_lw_imgLE hdep3 (by unfold maxCallDepth at hdle; omega)
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ []) (F := iprop(codeRes ∗ slot24 sret.toNat ∗
      (∀ (d' : Nat) (img' : Nat → BitVec 8), ownImg (InExt (inp + 8, 4)) img' -∗
          ⌜imgLE img' (inp + 8) 4 = d' ∧ d' ≤ maxCallDepth⌝ -∗ world N L Room inp ρ st d') ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗
      (∀ rv' : Nat → BitVec 64, ⌜KeepRegs calleeSaved rv rv'⌝ -∗ regFile rv' -∗
        stackScratch s n -∗ valAt N sret.toNat .null -∗ world N L Room inp ρ st d -∗
        PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ Wp.W Φ)))
  rotate_left
  · rw [hro]; iframe Hcode Hsr Hcl Hst Hk
    iapply ms_iff (T := fun b => InExt (s.toNat - 1088, 1088) b ∨
      InExt ((BitVec.ofNat 64 inp).toNat + 8, 4) b) (fun k => by rw [hinpN]) $$ Hms
  intro F'
  refine CloX_runN (m := ∅) (dep := d + 1) hlive hsf hs hs2 hs3 hinpG.lo hinpG.hi
    (by rw [hinpN]; omega) (by rw [hinpN]; exact hinpA) hat.s2 hat.sp hdl ?_
  apply swp_closeRM
  intro R4 Mt4 hR4 hMt4
  unfold F'
  iintro ⟨⟨#Hcode, Hsr, Hcl, Hst, Hk⟩, Hms⟩
  -- the depth word back to the world, at `d`
  ihave ⟨Hms, Hd⟩ := ms_split (S := InExt (s.toNat - 1088, 1088)) (T := InExt (inp + 8, 4))
    (fun a h1 h2 => by simp only [InExt] at h1 h2; omega) $$
    [Hms]
  · iapply ms_iff (T := fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (inp + 8, 4) b)
      (fun k => by rw [hinpN]) $$ Hms
  have hdep4 : imgLE (imgM Mt4) (inp + 8) 4 = d := by
    have hv : (BitVec.signExtend 64 (BitVec.extractLsb 31 0
        (BitVec.ofNat 64 (d + 1) + 18446744073709551615#64))).toNat % 2 ^ 32 = d := by
      have e : BitVec.ofNat 64 (d + 1) + 18446744073709551615#64 = BitVec.ofNat 64 d := by
        rw [← idx_succ, BitVec.add_assoc, show (1#64 + 18446744073709551615#64 : BitVec 64) = 0#64 by
          decide, BitVec.add_zero]
      rw [e, sext32_toNat_small (by unfold maxCallDepth at hdle; omega)]
      exact Nat.mod_eq_of_lt (by unfold maxCallDepth at hdle; omega)
    rw [hMt4, hi8, imgLE_store4_hit, hv]
  ihave Hw := Hcl $$ %d %(imgM Mt4) Hd %⟨hdep4, by omega⟩
  -- `value_null(sret)`
  have h10 : R4 10 = sret := by rw [hR4]; ix_reg; exact hat.s1
  ihave Hvn := hvn $$ %sret
  unfold valueNullSpec
  iapply ms_callHelper Wp (i := 0x80003964)
    (jalx_80003964 live (fun p hp => hlive _ (interp_code_80003964 p hp))) interp_code_80003964
    (by decide) (Pre := iprop(slot24 sret.toNat ∗ ⌜SlotGeom sret⌝))
  iframe Hvn Hcode Hms
  isplitl []
  · ipureintro; exact h10
  isplitl [Hsr]
  · iframe Hsr; ipureintro; exact hslg
  iintro %R5 %hk5 Hval Hms
  -- the spills reloaded, the epilogue
  have hoff := evalSP_off' hfg
  have hfr : ∀ k, closureS s k → imgM Mt4 k = imgM Mt k := fun k hk => by
    simp only [closureS, InExt] at hk
    rw [hMt4, imgM_store_miss _ _ (by rw [hi8]; omega), hM3f k (by simp only [InExt]; omega),
      hM1 k (by simp only [closureS, InExt]; omega)]
  have hsv : CloSpills Mt4 s ret rv := hat.spills.agree fun k h1 h2 _ _ =>
    hfr k (by simp only [closureS, InExt]; omega)
  have hk5' : ∀ x ∈ fRegs, x ≠ 1 → upd R5 1 (BitVec.ofNat 64 (0x80003964 + 4)) x = R4 x :=
    fun x hx h1 => by simp only [upd_apply, h1, ite_false]; exact hk5 x hx (by simp)
  have h2' : upd R5 1 (BitVec.ofNat 64 (0x80003964 + 4)) 2 = s + 18446744073709550528#64 := by
    rw [hk5' 2 (by decide) (by decide), hR4]; ix_reg; exact hat.sp
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ []) (F := iprop(
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗ valAt N sret.toNat .null ∗
      world N L Room inp ρ st d ∗
      (∀ rv' : Nat → BitVec 64, ⌜KeepRegs calleeSaved rv rv'⌝ -∗ regFile rv' -∗
        stackScratch s n -∗ valAt N sret.toNat .null -∗ world N L Room inp ρ st d -∗
        PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ Wp.W Φ)))
  rotate_left
  · rw [hro]; iframe Hcode Hms Hst Hval Hw; iexact Hk
  intro F'
  refine CloX_runE (m := ∅) (ret := ret) (v8 := rv 8) (v9 := rv 9) (v18 := rv 18) (v19 := rv 19)
    (v21 := rv 21) (v23 := rv 23) hlive hsf hs hs2 hs3 hal h2' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hoff 1080 (by decide)]; exact hsv.saved.ra
  · rw [hoff 1072 (by decide)]; exact hsv.saved.s0
  · rw [hoff 1064 (by decide)]; exact hsv.saved.s1
  · rw [hoff 1056 (by decide)]; exact hsv.saved.s2
  · rw [hoff 1048 (by decide)]; exact hsv.s3
  · rw [hoff 1032 (by decide)]; exact hsv.s5
  · rw [hoff 1016 (by decide)]; exact hsv.s7
  apply swp_closeF
  unfold F'
  iintro ⟨⟨Hst, Hval, Hw, Hk⟩, Hms⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave Hst := evalFrame_join hsg.le hn $$ [Hst HS]
  · iframe Hst HS
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  iapply Hk $$ %_ %?_ Hregs Hst Hval Hw Hpc Hra
  keep_split
  · ix_reg; exact (evalSP_restore s).trans hsp.symm
  all_goals ix_reg
  all_goals
    rw [hk5 _ (by decide) (by simp), hR4]
    ix_reg
    exact hat.keep _ (by decide)

/-- **A `return`** (`0x8000337c`, status `3`), for either WP: the depth word
back to `d`, the result slot `sp+144` copied to `sret`, the spills reloaded,
the epilogue; the caller gets its callee-saved registers, its stack, the value
at `sret`, the world at depth `d`. -/
theorem cloExitR (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {ρ : Regime} {st : St} {d : Nat} {v : Value}
    {s sret ret : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem} {n : Nat}
    (hfg : EvalFrameG s) (hsg : StackGeom s n) (hn : 1088 ≤ n) (hal : ret.toNat % 4 = 0)
    (hsp : rv 2 = s) (hinpG : RtErr.InpGeom (BitVec.ofNat 64 inp)) (hinpL : inp < 2 ^ 64)
    (hinpA : inp % 8 = 0) (hslg : SlotGeom sret)
    (hat : CloAt R Mt s (BitVec.ofNat 64 inp) sret ret rv) (h10 : R 10 = 3#64) :
    codeRes ∗ ms 0x8000337c#64 R (closureS s) Mt ∗
      valAt N (s + 18446744073709550528#64 + 144#64).toNat v ∗
      slot24 sret.toNat ∗ world N L Room inp ρ st (d + 1) ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗
      (∀ rv' : Nat → BitVec 64, ⌜KeepRegs calleeSaved rv rv'⌝ -∗ regFile rv' -∗
        stackScratch s n -∗ valAt N sret.toNat v -∗ world N L Room inp ρ st d -∗
        PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  have hsf := hfg.sf; have hs := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  have hoff := evalSP_off' hfg
  have h144 := hoff 144 (by decide)
  have hinpN : (BitVec.ofNat 64 inp).toNat = inp := Nat.mod_eq_of_lt hinpL
  have hi8 : (BitVec.ofNat 64 inp + 8#64).toNat = inp + 8 := by
    have := hinpG.hi; rw [hinpN] at this
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hwd := world_depth (GF := GF) N L Room inp ρ st (d + 1)
  rw [show inp + interpDepthOff = inp + 8 from rfl] at hwd
  iintro ⟨#Hcode, Hms, Hv, Hsr, Hw, Hst, Hk⟩
  -- the result slot back into the frame
  ihave Hv := (show valAt (GF := GF) N (s + 18446744073709550528#64 + 144#64).toNat v ⊢
    valAt N (s.toNat - 1088 + 144) v by rw [h144]) $$ Hv
  ihave ⟨%w0, %w1, %w2, #Hw3, Hms⟩ := ms_joinSlot N (S := InExt (s.toNat - 1088, 1088))
    (a := s.toNat - 1088 + 144) (fun b hb => by simp only [InExt] at hb ⊢; omega) $$ [Hms Hv]
  · iframe Hms Hv
  -- the depth word
  ihave ⟨%dimg, Hd, %⟨hdv, hdle⟩, Hcl⟩ := hwd $$ Hw
  ihave ⟨%Md, Hd, %hMd⟩ := ownSet_trackedAt _ dimg $$ Hd
  ihave ⟨%M3, Hms, %⟨hM3f, hM3d, hdisj⟩⟩ := ms_join $$ [Hms Hd]
  · iframe Hms Hd
  have hi3 : inp + 8 + 4 ≤ s.toNat - 1088 ∨ s.toNat ≤ inp + 8 := by
    refine Classical.byContradiction fun hc => ?_
    exact hdisj (max (s.toNat - 1088) (inp + 8)) (by simp only [InExt]; omega)
      (by simp only [InExt]; omega)
  have hdep3 : imgLE (imgM M3) (inp + 8) 4 = d + 1 := by
    rw [imgLE_congr (img' := dimg) (fun i hi => (hM3d _ (by simp [InExt]; omega)).trans
      (hMd _ (by simp [InExt]; omega))), hdv]
  have hdl : ldv .lw M3 (BitVec.ofNat 64 inp + 8#64).toNat = BitVec.ofNat 64 (d + 1) := by
    rw [hi8]; exact ldvf_lw_imgLE hdep3 (by unfold maxCallDepth at hdle; omega)
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ []) (F := iprop(codeRes ∗ □ valOf N v w0 w1 w2 ∗
      slot24 sret.toNat ∗
      (∀ (d' : Nat) (img' : Nat → BitVec 8), ownImg (InExt (inp + 8, 4)) img' -∗
          ⌜imgLE img' (inp + 8) 4 = d' ∧ d' ≤ maxCallDepth⌝ -∗ world N L Room inp ρ st d') ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗
      (∀ rv' : Nat → BitVec 64, ⌜KeepRegs calleeSaved rv rv'⌝ -∗ regFile rv' -∗
        stackScratch s n -∗ valAt N sret.toNat v -∗ world N L Room inp ρ st d -∗
        PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ Wp.W Φ)))
  rotate_left
  · rw [hro]; iframe Hcode Hw3 Hsr Hcl Hst Hk
    iapply ms_iff (T := fun b => InExt (s.toNat - 1088, 1088) b ∨
      InExt ((BitVec.ofNat 64 inp).toNat + 8, 4) b) (fun k => by rw [hinpN]) $$ Hms
  intro F'
  refine CloX_runX (m := ∅) (dep := d + 1) hlive hsf hs hs2 hs3 hinpG.lo hinpG.hi
    (by rw [hinpN]; omega) (by rw [hinpN]; exact hinpA) hat.s2 hat.sp hdl ?_ ?_ ?_
  · intro hc
    exfalso
    rw [h10] at hc
    exact absurd hc (by decide)
  · intro _ hne
    exfalso
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hne
    exact hne h10
  intro _ _
  apply swp_closeRM
  intro R4 Mt4 hR4 hMt4
  unfold F'
  iintro ⟨⟨#Hcode, #Hw3, Hsr, Hcl, Hst, Hk⟩, Hms⟩
  -- the depth word back to the world, at `d`
  ihave ⟨Hms, Hd⟩ := ms_split (S := InExt (s.toNat - 1088, 1088)) (T := InExt (inp + 8, 4))
    (fun a h1 h2 => by simp only [InExt] at h1 h2; omega) $$ [Hms]
  · iapply ms_iff (T := fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (inp + 8, 4) b)
      (fun k => by rw [hinpN]) $$ Hms
  have hdep4 : imgLE (imgM Mt4) (inp + 8) 4 = d := by
    have hv : (BitVec.signExtend 64 (BitVec.extractLsb 31 0
        (BitVec.ofNat 64 (d + 1) + 18446744073709551615#64))).toNat % 2 ^ 32 = d := by
      have e : BitVec.ofNat 64 (d + 1) + 18446744073709551615#64 = BitVec.ofNat 64 d := by
        rw [← idx_succ, BitVec.add_assoc, show (1#64 + 18446744073709551615#64 : BitVec 64) = 0#64 by
          decide, BitVec.add_zero]
      rw [e, sext32_toNat_small (by unfold maxCallDepth at hdle; omega)]
      exact Nat.mod_eq_of_lt (by unfold maxCallDepth at hdle; omega)
    rw [hMt4, hi8, imgLE_store4_hit, hv]
  ihave Hw := Hcl $$ %d %(imgM Mt4) Hd %⟨hdep4, by omega⟩
  -- `sret` joined for the copy
  ihave ⟨%M5, Hms, %⟨hM5, hd5⟩⟩ := ms_join_sret $$ [Hms Hsr]
  · iframe Hms Hsr
  have hr4 : sret.toNat + 24 ≤ s.toNat - 1088 ∨ s.toNat ≤ sret.toNat := by
    refine Classical.byContradiction fun hc => ?_
    exact hd5 (max (s.toNat - 1088) sret.toNat) (by simp only [InExt]; omega)
      (by simp only [InExt]; have := hslg.hi; omega)
  have hfr : ∀ k, InExt (s.toNat - 1088, 1088) k → imgM M5 k = imgM
      (slotWrite Mt (s.toNat - 1088 + 144) w0 w1 w2) k := fun k hk => by
    rw [hM5 k hk, hMt4, imgM_store_miss _ _ (by simp only [InExt] at hk; rw [hi8]; omega),
      hM3f k (by simp only [InExt] at hk ⊢; omega)]
  have hsv : CloSpills M5 s ret rv := hat.spills.agree fun k h1 h2 _ _ => by
    rw [hfr k (by simp only [InExt]; omega), imgM_slotWrite_out w0 w1 w2 (by simp only [InExt]; omega)]
  have hwv : ∀ o, o < 3 → ldv .ld M5 (s.toNat - 1088 + 144 + 8 * o) =
      ldv .ld (slotWrite Mt (s.toNat - 1088 + 144) w0 w1 w2) (s.toNat - 1088 + 144 + 8 * o) :=
    fun o ho => ldv_agree fun i hi => hfr _ (by simp only [InExt]; omega)
  have h2' : R4 2 = s + 18446744073709550528#64 := by rw [hR4]; ix_reg; exact hat.sp
  have h9' : R4 9 = sret := by rw [hR4]; ix_reg; exact hat.s1
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ []) (F := iprop(□ valOf N v w0 w1 w2 ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗ world N L Room inp ρ st d ∗
      (∀ rv' : Nat → BitVec 64, ⌜KeepRegs calleeSaved rv rv'⌝ -∗ regFile rv' -∗
        stackScratch s n -∗ valAt N sret.toNat v -∗ world N L Room inp ρ st d -∗
        PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ Wp.W Φ)))
  rotate_left
  · rw [hro]; iframe Hcode Hms Hw3 Hst Hw; iexact Hk
  intro F'
  refine CloX_runC (m := ∅) (ret := ret) (v8 := rv 8) (v9 := rv 9) (v18 := rv 18) (v19 := rv 19)
    (v21 := rv 21) (v23 := rv 23) hlive hsf hs hs2 hs3 hslg.al (by have := hslg.lo; omega) hslg.hi hr4
    hal h9' h2' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hoff 1080 (by decide)]; exact hsv.saved.ra
  · rw [hoff 1072 (by decide)]; exact hsv.saved.s0
  · rw [hoff 1064 (by decide)]; exact hsv.saved.s1
  · rw [hoff 1056 (by decide)]; exact hsv.saved.s2
  · rw [hoff 1048 (by decide)]; exact hsv.s3
  · rw [hoff 1032 (by decide)]; exact hsv.s5
  · rw [hoff 1016 (by decide)]; exact hsv.s7
  apply swp_closeF
  unfold F'
  iintro ⟨⟨#Hw3, Hst, Hw, Hk⟩, Hms⟩
  have e8 : (sret + 8#64).toNat = sret.toNat + 8 := by
    have := hslg.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e16 : (sret + 16#64).toNat = sret.toNat + 16 := by
    have := hslg.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hc0 : ldv .ld M5 (s + 18446744073709550528#64 + 144#64).toNat = w0 := by
    rw [h144, show s.toNat - 1088 + 144 = s.toNat - 1088 + 144 + 8 * 0 by rfl, hwv 0 (by omega)]
    exact slotWrite_ld0 _ _ _ _ _
  have hc1 : ldv .ld M5 (s + 18446744073709550528#64 + 152#64).toNat = w1 := by
    rw [hoff 152 (by decide), show s.toNat - 1088 + 152 = s.toNat - 1088 + 144 + 8 * 1 by omega,
      hwv 1 (by omega)]
    exact slotWrite_ld8 _ _ _ _ _
  have hc2 : ldv .ld M5 (s + 18446744073709550528#64 + 160#64).toNat = w2 := by
    rw [hoff 160 (by decide), show s.toNat - 1088 + 160 = s.toNat - 1088 + 144 + 8 * 2 by omega,
      hwv 2 (by omega)]
    exact slotWrite_ld16 _ _ _ _ _
  rw [e8, e16, hc0, hc1, hc2]
  obtain ⟨g0, g1, g2⟩ := imgW_three M5 sret.toNat w0 w1 w2
  ihave Hv := (show valOf (GF := GF) N v w0 w1 w2 ⊢ valImg N (imgM (writeLog (writeLog (writeLog M5
      [(sret.toNat, 8, w0)]) [(sret.toNat + 8, 8, w1)]) [(sret.toNat + 16, 8, w2)])) sret.toNat v by
    unfold valImg; rw [g0, g1, g2]) $$ Hw3
  ihave ⟨Hpc, Hra, Hregs, HS, Hval⟩ := ms_exit_sret N hd5 $$ [Hms Hv]
  · iframe Hms Hv
  ihave Hst := evalFrame_join hsg.le hn $$ [Hst HS]
  · iframe Hst HS
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  iapply Hk $$ %_ %?_ Hregs Hst Hval Hw Hpc Hra
  keep_split
  · ix_reg; exact (evalSP_restore s).trans hsp.symm
  all_goals ix_reg
  all_goals
    rw [hR4]
    ix_reg
    exact hat.keep _ (by decide)

end Exits

end VsaIris.Interp
