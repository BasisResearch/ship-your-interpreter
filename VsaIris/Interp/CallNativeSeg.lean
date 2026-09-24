import VsaIris.Interp.CallNativeOut
import VsaIris.Interp.SpecErr

/-!
# The native path as two segment lemmas (lane E4)

Every native call (`print`, `println`, `assert`) runs the same code around its
`jalr a6`: `callNativeMarshal` (the kind dispatch `0x80003254` to the `jalr`
at `0x800039f4`: the callee copied to `sp+120`, the line, the arguments
marshalled, the argument array carved out of the frame as `valsAt`; end state
`NatAt`) and `callNativeEpi` (after the native, `0x800039f8`: the array back
into the frame, `s7` restored, the shared epilogue, the arm's exit
continuation `CallExitK`). Both for either WP.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.RuntimeRepr

/-- The state at the native's `jalr a6` (`0x800039f4`): the arguments
`(sret, in, argc, args, line)`, `a6` the native's entry, `s7` the line, the
other callee-saved registers as at the dispatch, and the frame's saved words
unchanged. -/
structure NatAt (R1 : Nat → BitVec 64) (Mt1 Mt : Mem) (s sret inp entry line : BitVec 64)
    (argc : Nat) (R : Nat → BitVec 64) : Prop where
  a6 : R1 16 = entry
  a0 : R1 10 = sret
  a1 : R1 11 = inp
  a2 : R1 12 = BitVec.ofNat 64 argc
  a3 : R1 13 = s + 18446744073709550528#64 + 240#64
  a4 : R1 14 = line
  sp : R1 2 = s + 18446744073709550528#64
  keep : ∀ x ∈ [8, 9, 18, 19, 20, 21, 22, 24, 25, 26, 27], R1 x = R x
  mem : ∀ o, 1008 ≤ o → o + 8 ≤ 1088 → ldv .ld Mt1 (s.toNat - 1088 + o) = ldv .ld Mt (s.toNat - 1088 + o)

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The error context (E2's `errCtx`: the binary's image, the `jmp_buf` with
its aligned `ra` word) out of the world (persistent). -/
theorem world_errCtx (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (ρ : Regime)
    (st : St) (d : Nat) :
    world (GF := GF) N L Room inp ρ st d ⊢ world N L Room inp ρ st d ∗ errCtx inp := by
  unfold world worldE interpCtxE
  iintro ⟨%H, %B, Hh, Hs, Hc, Hio, ⟨Hcore, %jb, #Hjb, %hjb⟩, %hB, #Hb⟩
  isplitl [Hh Hs Hc Hio Hcore]
  · iexists H, B
    iframe Hh Hs Hc Hio Hcore Hb
    isplitl []
    · iexists jb; iframe Hjb; ipureintro; exact hjb
    · ipureintro; exact hB
  · unfold errCtx
    iframe Hb
    iexists jb
    iframe Hjb
    ipureintro
    unfold jbWord; simpa using hjb

/-- The frame without the argument array. -/
abbrev natS (s : BitVec 64) (argc : Nat) : Nat → Prop :=
  fun k => InExt (s.toNat - 1088, 1088) k ∧ ¬ InExt (argsBase s, 24 * argc) k

/-- **To the native's `jalr`**, for either WP. -/
theorem callNativeMarshal (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs} {inp : Nat} {vs : List Value} {nf : NativeFn}
    {entry : BitVec 64} {fe : Expr} {args : List Expr} {s aX sret ret w0 w1 w2 : BitVec 64}
    {rv R : Nat → BitVec 64} {Mt : Mem} {n : Nat}
    (hentry : N.addr nf = entry.toNat) (hlen : vs.length ≤ 32) (hsg : StackGeom s n) (hn : 1088 ≤ n)
    (hcall : CallAt R Mt s aX sret (BitVec.ofNat 64 inp) ret rv w0 w1 w2 vs.length) :
    codeRes ∗ □ astEG aX.toNat (.call fe args) ∗ □ valOf N (.native nf) w0 w1 w2 ∗
      argVals N (imgM Mt) (argsBase s) 0 vs ∗ ms 0x80003254#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗
      (∀ (R1 : Nat → BitVec 64) (Mt1 : Mem) (line : BitVec 64),
        ⌜NatAt R1 Mt1 Mt s sret (BitVec.ofNat 64 inp) entry line vs.length R⌝ -∗
        ms 0x800039f4#64 R1 (natS s vs.length) Mt1 -∗ valsAt N (argsBase s) vs -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hcode, #Hast, #Hv, #Hav, Hms, Hk⟩
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨aF, hnd, -, -⟩ := callNode_of_repr hrepr hgeo
  unfold valOf
  icases Hv with ⟨%⟨hk5, hw2⟩, -⟩
  have hw2' : w2 = entry := BitVec.eq_of_toNat_eq (hw2.trans hentry)
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hs' : 0x87800000 + 1088 ≤ s.toNat := by omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have hoff := evalSP_off (s := s) hsf (by omega)
  ihave #Hdv := roOwn_data hnd.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(argVals N (imgM Mt) (argsBase s) 0 vs ∗
      (∀ (R1 : Nat → BitVec 64) (Mt1 : Mem) (line : BitVec 64),
        ⌜NatAt R1 Mt1 Mt s sret (BitVec.ofNat 64 inp) entry line vs.length R⌝ -∗
        ms 0x800039f4#64 R1 (natS s vs.length) Mt1 -∗ valsAt N (argsBase s) vs -∗ Wp.W Φ)))
  rotate_left
  · iframe Hdv Hms Hav; iexact Hk
  intro F'
  refine CallN_run1 (w0 := w0) (w1 := w1) (w2 := w2) hlive hsf hs' hs2 hs3 hnd.lo hnd.hi hnd.off
    hcall.s0 hcall.sp ?_ ?_ ?_ ?_ ?_
  · rw [hoff 96 (by decide)]; exact hcall.w0
  · rw [hoff 104 (by decide)]; exact hcall.w1
  · rw [hoff 112 (by decide)]; exact hcall.w2
  · rw [hoff 96 (by decide)]; exact ldv_lw_of_ld hcall.w0 hk5 (by decide)
  intro vl _
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  unfold F'
  iintro ⟨⟨#Hav, Hk⟩, Hms⟩
  have hreg : ∀ a, InExt (argsBase s, 24 * vs.length) a → InExt (s.toNat - 1088, 1088) a := by
    intro a ha; simp only [InExt, argsBase] at ha ⊢; omega
  have hmiss : ∀ a, (a < s.toNat - 1088 + 120 ∨ s.toNat - 1088 + 144 ≤ a) → imgM Mt1 a = imgM Mt a := by
    intro a ha
    subst hMt1
    rw [imgM_store_miss _ _ (by rw [hoff 136 (by decide)]; omega),
      imgM_store_miss _ _ (by rw [hoff 128 (by decide)]; omega),
      imgM_store_miss _ _ (by rw [hoff 120 (by decide)]; omega)]
  have hag : ∀ a, InExt (argsBase s + 24 * 0, 24 * vs.length) a → imgM Mt a = imgM Mt1 a := by
    intro a ha
    simp only [InExt, argsBase, Nat.mul_zero, Nat.add_zero] at ha
    exact (hmiss a (by omega)).symm
  ihave #Hav1 := argVals_agree N (argsBase s) vs 0 hag $$ Hav
  ihave ⟨Hms, Hvals⟩ := ms_carveVals N hreg $$ [Hms Hav1]
  · iframe Hms Hav1
  have hnat : NatAt R1 Mt1 Mt s sret (BitVec.ofNat 64 inp) entry vl vs.length R := by
    subst hR1
    refine ⟨by ix_reg; exact hw2', by ix_reg; exact hcall.s1, by ix_reg; exact hcall.s2,
      by ix_reg; exact hcall.a5, by ix_reg, by ix_reg, by ix_reg; exact hcall.sp, ?_, fun o h1 h2 => ?_⟩
    · intro x hx
      have hx' : x = 8 ∨ x = 9 ∨ x = 18 ∨ x = 19 ∨ x = 20 ∨ x = 21 ∨ x = 22 ∨ x = 24 ∨ x = 25 ∨
          x = 26 ∨ x = 27 := by simpa using hx
      rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
    · exact ldv_eqOn .ld (fun j hj => hmiss _ (by simp only [widthOfM] at hj; omega))
  iapply Hk $$ %R1 %Mt1 %vl %hnat Hms Hvals


/-- **After the native** (`0x800039f8`), for either WP: the argument array
back into the frame, `s7` restored, the shared epilogue; the continuation gets
the callee-saved registers kept, the stack back, `PC`/`ra` at the return. -/
theorem callNativeEpi (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs} {inp : Nat} {vs : List Value}
    {entry line : BitVec 64} {s aX sret ret w0 w1 w2 : BitVec 64}
    {rv R R1 R2 : Nat → BitVec 64} {Mt Mt1 : Mem} {n : Nat}
    (hsg : StackGeom s n) (hn : 1088 ≤ n) (hal : ret.toNat % 4 = 0) (hsp : rv 2 = s)
    (hlen : vs.length ≤ 32)
    (hcall : CallAt R Mt s aX sret (BitVec.ofNat 64 inp) ret rv w0 w1 w2 vs.length)
    (hnat : NatAt R1 Mt1 Mt s sret (BitVec.ofNat 64 inp) entry line vs.length R)
    (hkeep : ∀ x ∈ fRegs, x ∉ callerSaved → R2 x = R1 x) :
    codeRes ∗ ms 0x800039f8#64 (upd R2 1 (BitVec.ofNat 64 (0x800039f4 + 4))) (natS s vs.length) Mt1 ∗
      valsAt N (argsBase s) vs ∗ stackScratch (s + 18446744073709550528#64) (n - 1088) ∗
      (∀ rv' : Nat → BitVec 64, ⌜KeepRegs calleeSaved rv rv'⌝ -∗ regFile rv' -∗
        stackScratch s n -∗ PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hs' : 0x87800000 + 1088 ≤ s.toNat := by omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hreg : ∀ a, InExt (argsBase s, 24 * vs.length) a → InExt (s.toNat - 1088, 1088) a := by
    intro a ha; simp only [InExt, argsBase] at ha ⊢; omega
  iintro ⟨#Hcode, Hms, Hvals, Hst, Hk⟩
  ihave ⟨%Mt3, Hms, %hag3⟩ := ms_uncarveVals N hreg $$ [Hms Hvals]
  · iframe Hms Hvals
  have hfr : ∀ o, 1008 ≤ o → o + 8 ≤ 1088 →
      ldv .ld Mt3 (s.toNat - 1088 + o) = ldv .ld Mt (s.toNat - 1088 + o) := by
    intro o h1 h2
    rw [← hnat.mem o h1 h2]
    exact ldv_eqOn .ld (fun j hj => hag3 _ (by simp only [InExt, widthOfM] at *; omega)
      (by simp only [InExt, argsBase, widthOfM] at *; omega))
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have h2' : upd R2 1 (BitVec.ofNat 64 (0x800039f4 + 4)) 2 = s + 18446744073709550528#64 := by
    ix_reg; rw [hkeep 2 (by decide) (by decide)]; exact hnat.sp
  have hks : ∀ x ∈ [19, 20, 21, 22, 24, 25, 26, 27], R2 x = rv x := fun x hx => by
    rw [hkeep x ((by decide : ∀ y ∈ [19, 20, 21, 22, 24, 25, 26, 27], y ∈ fRegs) x hx)
      ((by decide : ∀ y ∈ [19, 20, 21, 22, 24, 25, 26, 27], y ∉ callerSaved) x hx),
      hnat.keep x ((by decide : ∀ y ∈ [19, 20, 21, 22, 24, 25, 26, 27],
        y ∈ [8, 9, 18, 19, 20, 21, 22, 24, 25, 26, 27]) x hx),
      hcall.keep x ((by decide : ∀ y ∈ [19, 20, 21, 22, 24, 25, 26, 27],
        y ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27]) x hx)]
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ []) (F := iprop(
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗
      (∀ rv' : Nat → BitVec 64, ⌜KeepRegs calleeSaved rv rv'⌝ -∗ regFile rv' -∗
        stackScratch s n -∗ PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ Wp.W Φ)))
  rotate_left
  · rw [hro]; iframe Hcode Hms Hst; iexact Hk
  intro F'
  refine CallN_run2 (m := ∅) (DA := []) (ret := ret) (v8 := rv 8) (v9 := rv 9) (v18 := rv 18)
    (v23 := rv 23) hlive hsf hs' hs2 hs3 hal h2' ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hoff 1080 (by decide), hfr 1080 (by omega) (by omega)]; exact hcall.ra
  · rw [hoff 1072 (by decide), hfr 1072 (by omega) (by omega)]; exact hcall.sv8
  · rw [hoff 1064 (by decide), hfr 1064 (by omega) (by omega)]; exact hcall.sv9
  · rw [hoff 1056 (by decide), hfr 1056 (by omega) (by omega)]; exact hcall.sv18
  · rw [hoff 1016 (by decide), hfr 1016 (by omega) (by omega)]; exact hcall.sv23
  apply swp_closeF
  unfold F'
  iintro ⟨⟨Hst, Hk⟩, Hms⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave Hst := evalFrame_join hsg.le hn $$ [Hst HS]
  · iframe Hst HS
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  iapply Hk $$ %_ %?_ Hregs Hst Hpc Hra
  keep_split
  · ix_reg; exact (evalSP_restore s).trans hsp.symm
  all_goals ix_reg
  all_goals exact hks _ (by decide)


/-- The frame without the argument array and the values: the whole frame. -/
theorem natS_join (N : NativeAddrs) {s : BitVec 64} {vs : List Value} {M : Mem}
    (hlen : vs.length ≤ 32) (hs : 1088 ≤ s.toNat) :
    ownSet (GF := GF) (natS s vs.length) (fun a => a ↦ₘ imgM M a) ∗ valsAt N (argsBase s) vs ⊢
      ownSet (InExt (s.toNat - 1088, 1088)) byteAny := by
  iintro ⟨HS, Hv⟩
  unfold valsAt
  ihave Hb := blockOwn_of_valsAt N (argsBase s) vs 0 $$ Hv
  simp only [Nat.mul_zero, Nat.add_zero]
  unfold blockOwn
  ihave HS := ownSet_forget _ _ $$ HS
  ihave H := ownSet_join _ _ _ (fun a (h1 : natS s vs.length a) h2 => h1.2 h2) $$ [HS Hb]
  · iframe HS Hb
  iapply ownSet_iff _ (fun a => ⟨fun h => h.elim (·.1) (fun h => by
    simp only [InExt, argsBase] at h ⊢; omega), fun h => by
    by_cases h' : InExt (argsBase s, 24 * vs.length) a
    · exact .inr h'
    · exact .inl ⟨h, h'⟩⟩) $$ H

/-- **`assert` from the kind dispatch**, for either WP and regime: the
native's return (`AssertOk vs`, the result `null`) or its abort (`¬ AssertOk
vs`, H5's core at the native's region, the arm's whole stack back). -/
theorem callNativeAssert (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {ρ : Regime} {st2 : St} {d : Nat} {vs : List Value} {fe : Expr} {args : List Expr}
    {s aX sret ret w0 w1 w2 : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem} {n : Nat}
    (hna : ∀ sret inp args s line vs ρ st d jb,
      ⊢ nativeAssertSpec (vsaModel live) N Wp L Room sret inp args s line vs ρ st d jb)
    (hN : N.addr .assert = 0x80002df4) (hinp : RtErr.InpGeom (BitVec.ofNat 64 inp))
    (hinpLt : inp < 2 ^ 64) (hlen : vs.length ≤ 32) (hsg : StackGeom s n)
    (hroom : nativeAssertNeed + 1088 ≤ n) (hslg : SlotGeom sret) (hal : ret.toNat % 4 = 0)
    (hsp : rv 2 = s)
    (hcall : CallAt R Mt s aX sret (BitVec.ofNat 64 inp) ret rv w0 w1 w2 vs.length) :
    codeRes ∗ □ astEG aX.toNat (.call fe args) ∗ □ valOf N (.native .assert) w0 w1 w2 ∗
      argVals N (imgM Mt) (argsBase s) 0 vs ∗ ms 0x80003254#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗ world N L Room inp ρ st2 d ∗
      slot24 sret.toNat ∗
      ((∀ rv' : Nat → BitVec 64, ⌜AssertOk vs⌝ -∗ ⌜KeepRegs calleeSaved rv rv'⌝ -∗ regFile rv' -∗
          stackScratch s n -∗ valAt N sret.toNat .null -∗ world N L Room inp ρ st2 d -∗
          PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ Wp.W Φ) ∧
       (⌜¬ AssertOk vs⌝ -∗ abortCore N L Room inp (s + 18446744073709550528#64) nativeAssertNeed -∗
          stackScratch s n -∗ slot24 sret.toNat -∗ Wp.W Φ))
    ⊢ Wp.W Φ := by
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hn : 1088 ≤ n := by unfold nativeAssertNeed at hroom; omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hms' : n - 1088 ≤ (s + 18446744073709550528#64).toNat := by rw [hsf]; omega
  have hinpN : (BitVec.ofNat 64 inp).toNat = inp := Nat.mod_eq_of_lt hinpLt
  have hna' : nativeAssertNeed ≤ n - 1088 := Nat.le_sub_of_add_le hroom
  iintro ⟨#Hcode, #Hast, #Hv, #Hav, Hms, Hst, Hw, Hslot, Hk⟩
  ihave ⟨Hw, #HE⟩ := world_errCtx N L Room inp ρ st2 d $$ Hw
  unfold errCtx
  icases HE with ⟨#Himg, %jb, #Hjb, %hjb⟩
  have hent : N.addr .assert = nativeAssertPC.toNat := by rw [hN]; rfl
  iapply callNativeMarshal hlive Wp (N := N) (nf := .assert) (entry := nativeAssertPC) hent hlen hsg hn
    hcall
  iframe Hcode Hast Hv Hav Hms
  iintro %R1 %Mt1 %line %hnat Hms Hvals
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow (m := nativeAssertNeed) hms' hna' $$ Hst
  have hbase : (s + 18446744073709550528#64 + 240#64).toNat = argsBase s := by rw [hoff 240 (by decide)]
  have hspec := hna sret (BitVec.ofNat 64 inp) (s + 18446744073709550528#64 + 240#64)
    (s + 18446744073709550528#64) line vs ρ st2 d jb
  unfold nativeAssertSpec at hspec
  rw [hinpN, hbase] at hspec
  have hP : ∀ r : BitVec 64, r = BitVec.ofNat 64 (0x800039f4 + 4) →
      iprop(regFile R1 ∗ codeRes ∗ iprop(slot24 sret.toNat ∗ valsAt N (argsBase s) vs ∗ binImg ∗
        jmpRO inp jb ∗ world N L Room inp ρ st2 d ∗
        stackAt (s + 18446744073709550528#64) nativeAssertNeed)) ⊢@{IProp GF}
      iprop(⌜r.toNat % 4 = 0⌝ ∗ regFile R1 ∗
        ⌜R1 10 = sret ∧ R1 11 = BitVec.ofNat 64 inp ∧ R1 12 = BitVec.ofNat 64 vs.length ∧
          R1 13 = s + 18446744073709550528#64 + 240#64 ∧ R1 14 = line ∧
          R1 2 = s + 18446744073709550528#64⌝ ∗ codeRes ∗ slot24 sret.toNat ∗
        ⌜SlotGeom sret ∧ ArgsGeom (s + 18446744073709550528#64 + 240#64) vs.length ∧
          vs.length < 2 ^ 31 ∧ Newlib.RtErr.InpGeom (BitVec.ofNat 64 inp) ∧
          (jbWord inp jb 0).toNat % 4 = 0⌝ ∗
        valsAt N (argsBase s) vs ∗ binImg ∗ jmpRO inp jb ∗ world N L Room inp ρ st2 d ∗
        stackAt (s + 18446744073709550528#64) nativeAssertNeed) := by
    intro r hr; subst hr
    iintro ⟨Hregs, #Hc, Hsl, Hvs, #Hb, #Hj, Hw, Hst⟩
    iframe Hregs Hc Hsl Hvs Hb Hj Hw Hst
    ipureintro
    refine ⟨by decide, ⟨hnat.a0, hnat.a1, hnat.a2, hnat.a3, hnat.a4, hnat.sp⟩, hslg, ⟨?_, ?_, ?_⟩,
      by omega, hinp, hjb⟩
    · rw [hbase]; simp only [argsBase]; omega
    · rw [hbase]; simp only [argsBase]; unfold tohostAddr; omega
    · rw [hbase]; simp only [argsBase]; omega
  iapply ms_callAbortR Wp (i := 0x800039f4)
    (jalrx_800039f4 live (fun p hp => hlive _ (interp_code_800039f4 p hp)) nativeAssertPC (by decide))
    interp_code_800039f4 (R := R1) (S := natS s vs.length) (Mt := Mt1) hnat.a6
    (P := fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ regFile R1 ∗
        ⌜R1 10 = sret ∧ R1 11 = BitVec.ofNat 64 inp ∧ R1 12 = BitVec.ofNat 64 vs.length ∧
          R1 13 = s + 18446744073709550528#64 + 240#64 ∧ R1 14 = line ∧
          R1 2 = s + 18446744073709550528#64⌝ ∗ codeRes ∗ slot24 sret.toNat ∗
        ⌜SlotGeom sret ∧ ArgsGeom (s + 18446744073709550528#64 + 240#64) vs.length ∧
          vs.length < 2 ^ 31 ∧ Newlib.RtErr.InpGeom (BitVec.ofNat 64 inp) ∧
          (jbWord inp jb 0).toNat % 4 = 0⌝ ∗
        valsAt N (argsBase s) vs ∗ binImg ∗ jmpRO inp jb ∗ world N L Room inp ρ st2 d ∗
        stackAt (s + 18446744073709550528#64) nativeAssertNeed))
    (Q := fun _ => iprop(∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = R1 x⌝ ∗
        ⌜∃ v m, (vs = [v] ∨ vs = [v, m]) ∧ v.truthy = true⌝ ∗ valAt N sret.toNat .null ∗
        valsAt N (argsBase s) vs ∗ world N L Room inp ρ st2 d ∗
        stackAt (s + 18446744073709550528#64) nativeAssertNeed))
    (A := iprop(⌜¬ AssertOk vs⌝ ∗ abortRes N L Room inp (s + 18446744073709550528#64) nativeAssertNeed ∗
        slot24 sret.toNat ∗ valsAt N (argsBase s) vs))
    (Pre := iprop(slot24 sret.toNat ∗ valsAt N (argsBase s) vs ∗ binImg ∗
      jmpRO inp jb ∗ world N L Room inp ρ st2 d ∗
      stackAt (s + 18446744073709550528#64) nativeAssertNeed))
    (Post := fun R' => iprop(⌜∀ x ∈ fRegs, x ∉ callerSaved → R' x = R1 x⌝ ∗ ⌜AssertOk vs⌝ ∗
      valAt N sret.toNat .null ∗ valsAt N (argsBase s) vs ∗ world N L Room inp ρ st2 d ∗
      stackAt (s + 18446744073709550528#64) nativeAssertNeed))
    (hP _ rfl)
    (by
      iintro ⟨%R', Hregs, %hk, %hok, Hnull, Hvs, Hw, Hst⟩
      iexists R'
      iframe Hregs Hnull Hvs Hw Hst
      ipureintro; exact ⟨hk, hok⟩)
  ihave Hsp0 := hspec
  ihave Hsp := Hsp0 $$ %R1
  iframe Hsp Hcode Hms Hslot Hvals Himg Hjb Hw
  isplitl [Hst]
  · unfold stackAt; iframe Hst; ipureintro; exact (stackGeom_evalSP hsg hn hsf).narrow hna'
  isplit
  · -- the native returned: `AssertOk vs`, the epilogue
    iintro %R2 ⟨%hk2, %hok, Hnull, Hvals, Hw, ⟨Hst, -⟩⟩ Hms
    ihave Hst := stackScratch_widen (m := nativeAssertNeed) hms' hna' $$ [Hslack Hst]
    · iframe Hslack Hst
    iapply callNativeEpi hlive Wp hsg hn hal hsp hlen hcall hnat hk2
    iframe Hcode Hms Hvals Hst
    iintro %rv' %hkeep Hregs Hst Hpc Hra
    ihave Hk := and_elim_l $$ Hk
    iapply Hk $$ %rv' %hok %hkeep Hregs Hst Hnull Hw Hpc Hra
  · -- it aborted: the arm's stack rebuilt around H5's core
    iintro ⟨%hno, Hab, Hslot, Hvals⟩ HS
    unfold abortRes abortAt
    icases Hab with ⟨Hcore, Hst⟩
    ihave Hst := stackScratch_widen (m := nativeAssertNeed) hms' hna' $$ [Hslack Hst]
    · iframe Hslack Hst
    ihave HF := natS_join N (s := s) (M := Mt1) hlen (by omega) $$ [HS Hvals]
    · iframe HS Hvals
    ihave Hst := evalFrame_join hsg.le hn $$ [Hst HF]
    · iframe Hst HF
    ihave Hk := and_elim_r $$ Hk
    iapply Hk $$ %hno Hcore Hst Hslot

end

end VsaIris.Interp
