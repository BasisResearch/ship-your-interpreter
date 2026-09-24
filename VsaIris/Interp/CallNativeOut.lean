import VsaIris.Interp.CallPrefix
import VsaIris.Interp.CallNative

/-!
# The call arm's printing natives (lane E4)

`callNativeOut`: from the kind dispatch `0x80003254` (`CallAt`, reached by
the prefix) on a callee `.native f` whose entry is a printing native
(`native_print`, `native_println`; `natOutSpec`), for either WP and either
regime: marshal `f(sret, in, argc, args, line)` (run N1), the `jalr a6`
(`ms_callHelperR`) against the native's spec with the argument array carved
out of the frame (`ms_carveVals`), the console through the world
(`world_out`), then the epilogue (run N2) into the arm's exit continuation.
The store is unchanged and the console grows by the native's text.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.RuntimeRepr

section Lemmas

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- The arguments' meaning depends on their words only. -/
theorem argVals_agree (N : NativeAddrs) {f g : Nat → BitVec 8} (base : Nat) :
    ∀ (vs : List Value) (i : Nat), (∀ a, InExt (base + 24 * i, 24 * vs.length) a → f a = g a) →
      argVals (GF := GF) N f base i vs ⊢ argVals N g base i vs
  | [], _, _ => by unfold argVals; exact .rfl
  | v :: vs, i, h => by
    unfold argVals
    rw [valImg_agreeOn (g := g) (fun k hk => h k (by simp only [InExt, List.length_cons] at hk ⊢; omega))]
    iintro ⟨#Hv, #Hvs⟩
    iframe Hv
    iapply argVals_agree N base vs (i + 1)
      (fun a ha => h a (by simp only [InExt, List.length_cons] at ha ⊢; omega)) $$ Hvs

/-- A signed word load of a word whose low half is a small kind. -/
theorem ldv_lw_of_ld {Mt : Mem} {a : Nat} {w : BitVec 64} {k : Nat} (h : ldv .ld Mt a = w)
    (hk : w.toNat % 2 ^ 32 = k) (hk31 : k < 2 ^ 31) : ldv .lw Mt a = BitVec.ofNat 64 k := by
  rw [ldv_ld_imgW] at h
  exact ldv_lw_kind (by rw [h]; exact hk) hk31

/-- `ms_callHelperR` at a printing native's spec (its pins, precondition
and postcondition spelled out). -/
theorem ms_callNatOut {live : Nat → Prop} (N : NativeAddrs) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalrExec (vsaModel live) i code 16 entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) {need : Nat} {sret args sp : BitVec 64}
    {vs : List Value} {st : Store} {o o' : String} {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem}
    (h16 : R 16 = entry)
    (hpins : R 10 = sret ∧ R 12 = BitVec.ofNat 64 vs.length ∧ R 13 = args ∧ R 2 = sp) :
    natOutSpec (vsaModel live) N Wp entry need sret args sp vs st o o' ∗ codeRes ∗
      ms (BitVec.ofNat 64 i) R S Mt ∗
      iprop(slot24 sret.toNat ∗ ⌜SlotGeom sret ∧ ArgsGeom args vs.length ∧ vs.length < 2 ^ 31⌝ ∗
        valsAt N args.toNat vs ∗ dispResL st vs ∗ Newlib.binImg ∗ Stdio.stdioOwn ∗ consoleOwn o ∗
        stackAt sp need) ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ callerSaved → R' x = R x⌝ -∗
        iprop(valAt N sret.toNat .null ∗ valsAt N args.toNat vs ∗ Stdio.stdioOwn ∗
          consoleOwn o' ∗ stackAt sp need) -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hsp, Hcode, Hms, Hpre, Hk⟩
  unfold natOutSpec
  iapply ms_callHelperR Wp hexec hcode hal h16
  iframe Hsp Hcode Hms Hpre Hk
  ipureintro; exact hpins

/-- The argument loop yields one value per argument. -/
theorem evalArgsCost_length : ∀ {st d env es st' vs n},
    EvalArgsCost st d env es st' vs n → vs.length = es.length
  | _, _, _, _, _, _, _, .nil .. => rfl
  | _, _, _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ _ _ _ h => by
    simp [evalArgsCost_length h]

/-- The partial argument loop yields one value per argument. -/
theorem evalArgs_length : ∀ {st d env es st' vs},
    EvalArgs st d env es st' vs → vs.length = es.length
  | _, _, _, _, _, _, .nil .. => rfl
  | _, _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ _ h => by
    simp [evalArgs_length h]


end Lemmas


section Defs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- The call arm's exit continuation, for either WP: at the return address,
with the callee-saved registers kept, the stack back, the result in the slot
and the world advanced. -/
def CallExitK (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (rv : Nat → BitVec 64) (s : BitVec 64) (n : Nat) (sret : BitVec 64) (v : Value) (ρ : Regime)
    (st' : St) (d : Nat) (ret : BitVec 64) : IProp GF :=
  iprop(∀ rv' : Nat → BitVec 64, ⌜KeepRegs calleeSaved rv rv'⌝ -∗ regFile rv' -∗
    stackScratch s n -∗ valAt N sret.toNat v -∗ world N L Room inp ρ st' d -∗
    PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ Wp.W Φ)

/-- A printing native's spec at every argument (persistent). -/
def NatOutSpecs (live : Nat → Prop) (N : NativeAddrs) (Wp : MachWP (GF := GF) (vsaModel live))
    (entry : BitVec 64) (need : Nat) (out : Store → List Value → String → String) : IProp GF :=
  iprop(□ ∀ (a b c : BitVec 64) (vs : List Value) (st : Store) (o : String),
    natOutSpec (vsaModel live) N Wp entry need a b c vs st o (out st vs o))

instance (live : Nat → Prop) (N : NativeAddrs) (Wp : MachWP (GF := GF) (vsaModel live))
    (entry : BitVec 64) (need : Nat) (out : Store → List Value → String → String) :
    Persistent (NatOutSpecs live N Wp entry need out) := by
  unfold NatOutSpecs; infer_instance

/-- A printing native's spec at every argument, from its proof at each. -/
theorem natOutSpecs_of {live : Nat → Prop} (N : NativeAddrs) (Wp : MachWP (GF := GF) (vsaModel live))
    {entry : BitVec 64} {need : Nat} {out : Store → List Value → String → String}
    (h : ∀ a b c vs st o, ⊢ natOutSpec (vsaModel live) N Wp entry need a b c vs st o (out st vs o)) :
    ⊢ NatOutSpecs live N Wp entry need out := by
  unfold NatOutSpecs
  iintro !> %a %b %c %vs %st %o
  iapply h

end Defs

#ix_piece callNativeOut_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {ρ : Regime} {st2 : St} {d : Nat} {vs : List Value} {nf : NativeFn}
    {entry : BitVec 64} {need : Nat} {out : Store → List Value → String → String}
    {fe : Expr} {args : List Expr} {s aX sret ret w0 w1 w2 : BitVec 64} {rv R : Nat → BitVec 64}
    {Mt : Mem} {n : Nat}
    (hentry : N.addr nf = entry.toNat) (hent4 : entry.toNat % 4 = 0) (hlen : vs.length ≤ 32)
    (hsg : StackGeom s n) (hn : 1088 ≤ n) (hneed : need + 1088 ≤ n) (hslg : SlotGeom sret)
    (hal : ret.toNat % 4 = 0) (hd : DispSupply (GF := GF) N) (hsp : rv 2 = s)
    (hcall : CallAt R Mt s aX sret (BitVec.ofNat 64 inp) ret rv w0 w1 w2 vs.length) :
    NatOutSpecs live N Wp entry need out ∗ codeRes ∗ □ astEG aX.toNat (.call fe args) ∗
      □ valOf N (.native nf) w0 w1 w2 ∗ argVals N (imgM Mt) (argsBase s) 0 vs ∗
      ms 0x80003254#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗ world N L Room inp ρ st2 d ∗
      slot24 sret.toNat ∗
      CallExitK live N L Room inp Wp Φ rv s n sret .null ρ ⟨st2.store, out st2.store vs st2.out⟩ d ret
    ⊢ Wp.W Φ by
  iintro ⟨#Hspec, #Hcode, #Hast, #Hv, #Hav, Hms, Hst, Hw, Hslot, Hk⟩
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
  have hx1 := hnd.lo; have hx2 := hnd.hi; have hx3 := hnd.off
  ihave #Hdv := roOwn_data hnd.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(NatOutSpecs live N Wp entry need out ∗ codeRes ∗ roOn P m ∗
      argVals N (imgM Mt) (argsBase s) 0 vs ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗ world N L Room inp ρ st2 d ∗
      slot24 sret.toNat ∗
      CallExitK live N L Room inp Wp Φ rv s n sret .null ρ ⟨st2.store, out st2.store vs st2.out⟩ d ret))
  rotate_left
  · iframe Hdv Hms Hspec Hcode Hro Hav Hst Hw Hslot; iexact Hk
  intro F'
  refine CallN_run1 (w0 := w0) (w1 := w1) (w2 := w2) hlive hsf hs' hs2 hs3 hx1 hx2 hx3 hcall.s0
    hcall.sp ?_ ?_ ?_ ?_ ?_
  · rw [hoff 96 (by decide)]; exact hcall.w0
  · rw [hoff 104 (by decide)]; exact hcall.w1
  · rw [hoff 112 (by decide)]; exact hcall.w2
  · rw [hoff 96 (by decide)]; exact ldv_lw_of_ld hcall.w0 hk5 (by decide)
  intro vl _
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  unfold F'
  iintro ⟨⟨#Hspec, #Hcode, #Hro, #Hav, Hst, Hw, Hslot, Hk⟩, Hms⟩

#ix_piece callNativeOut_p2 from callNativeOut_p1 by
  -- the argument array out of the frame, the world opened, the native
  have hbase : (s + 18446744073709550528#64 + 240#64).toNat = argsBase s := by
    rw [hoff 240 (by decide)]
  have hreg : ∀ a, InExt (argsBase s, 24 * vs.length) a → InExt (s.toNat - 1088, 1088) a := by
    intro a ha; simp only [InExt, argsBase] at ha ⊢; omega
  have hag : ∀ a, InExt (argsBase s + 24 * 0, 24 * vs.length) a → imgM Mt a = imgM Mt1 a := by
    intro a ha
    simp only [InExt, argsBase, Nat.mul_zero, Nat.add_zero] at ha
    subst hMt1
    rw [imgM_store_miss _ _ (by rw [hoff 136 (by decide)]; omega),
      imgM_store_miss _ _ (by rw [hoff 128 (by decide)]; omega),
      imgM_store_miss _ _ (by rw [hoff 120 (by decide)]; omega)]
  ihave #Hav1 := argVals_agree N (argsBase s) vs 0 hag $$ Hav
  ihave ⟨Hms, Hvals⟩ := ms_carveVals N hreg $$ [Hms Hav1]
  · iframe Hms Hav1
  ihave ⟨Hcon, Hio, #Hbin, %B, Hstore, Hclose⟩ := world_out N L Room inp ρ st2 d $$ Hw
  ihave ⟨Hstore, #Hdisp⟩ := dispResL_of_argVals N hd st2.store B (imgM Mt1) (argsBase s) vs 0 $$
    [Hstore Hav1]
  · iframe Hstore Hav1
  have hms' : n - 1088 ≤ (s + 18446744073709550528#64).toNat := by rw [hsf]; omega
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow (m := need) hms' (by omega) $$ Hst
  unfold NatOutSpecs
  ihave #Hsp := Hspec $$ %sret %(s + 18446744073709550528#64 + 240#64)
    %(s + 18446744073709550528#64) %vs %st2.store %st2.out
  iapply ms_callNatOut N Wp (i := 0x800039f4)
    (jalrx_800039f4 live (fun p hp => hlive _ (interp_code_800039f4 p hp)) entry hent4)
    interp_code_800039f4 (by decide) (need := need) (sret := sret)
    (args := s + 18446744073709550528#64 + 240#64) (sp := s + 18446744073709550528#64) (vs := vs)
    (st := st2.store) (o := st2.out) (o' := out st2.store vs st2.out)
    (R := R1) (by subst hR1; ix_reg; exact hw2')
    (by subst hR1; exact ⟨by ix_reg; exact hcall.s1, by ix_reg; exact hcall.a5, by ix_reg,
      by ix_reg; exact hcall.sp⟩)
  iframe Hsp Hcode Hms
  isplitl [Hslot Hvals Hcon Hio Hst]
  · iframe Hslot Hcon Hio Hbin Hdisp
    isplitl []
    · ipureintro
      refine ⟨hslg, ⟨?_, ?_, ?_⟩, by omega⟩
      · rw [hbase]; simp only [argsBase]; omega
      · rw [hbase]; simp only [argsBase]; unfold tohostAddr; omega
      · rw [hbase]; simp only [argsBase]; omega
    rw [hbase]
    iframe Hvals
    unfold stackAt
    iframe Hst
    ipureintro
    exact (stackGeom_evalSP hsg hn hsf).narrow (by omega)
  iintro %R2 %hkeep2 ⟨Hnull, Hvals, Hio, Hcon, Hst, %hsg2⟩ Hms

#ix_piece callNativeOut_p3 from callNativeOut_p2 by
  -- the world closed, the array back into the frame, the epilogue
  ihave Hw := Hclose $$ %(out st2.store vs st2.out) Hcon Hio Hstore
  rw [hbase]
  ihave ⟨%Mt3, Hms, %hag3⟩ := ms_uncarveVals N hreg $$ [Hms Hvals]
  · iframe Hms Hvals
  ihave Hst := stackScratch_widen (m := need) hms' (by omega) $$ [Hslack Hst]
  · iframe Hslack Hst
  have hfr : ∀ o, (1008 ≤ o ∧ o + 8 ≤ 1088) →
      ldv .ld Mt3 (s.toNat - 1088 + o) = ldv .ld Mt (s.toNat - 1088 + o) := by
    intro o ho
    rw [ldv_eqOn .ld (Mt' := Mt1) (fun j hj => hag3 _ (by simp only [InExt, widthOfM] at *; omega)
      (by simp only [InExt, argsBase, widthOfM] at *; omega))]
    subst hMt1
    rw [ldv_eqOn .ld (Mt' := Mt) (fun j hj => by
      simp only [widthOfM] at hj
      rw [imgM_store_miss _ _ (by rw [hoff 136 (by decide)]; omega),
        imgM_store_miss _ _ (by rw [hoff 128 (by decide)]; omega),
        imgM_store_miss _ _ (by rw [hoff 120 (by decide)]; omega)])]
  have hkR : ∀ x ∈ fRegs, x ∉ callerSaved → R2 x = R1 x := hkeep2
  ihave #Hdv := roOwn_data (DA := []) (fun a h => by simp at h) $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(stackScratch (s + 18446744073709550528#64) (n - 1088) ∗
      valAt N sret.toNat .null ∗ world N L Room inp ρ ⟨st2.store, out st2.store vs st2.out⟩ d ∗
      CallExitK live N L Room inp Wp Φ rv s n sret .null ρ ⟨st2.store, out st2.store vs st2.out⟩ d ret))
  rotate_left
  · iframe Hdv Hms Hst Hnull Hw Hk
  intro F'
  have h2' : upd R2 1 (BitVec.ofNat 64 (0x800039f4 + 4)) 2 = s + 18446744073709550528#64 := by
    ix_reg; rw [hkR 2 (by decide) (by decide)]; subst hR1; ix_reg; exact hcall.sp
  refine CallN_run2 (ret := ret) (v8 := rv 8) (v9 := rv 9) (v18 := rv 18) (v23 := rv 23) hlive hsf
    hs' hs2 hs3 hal h2' ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hoff 1080 (by decide), hfr 1080 (by omega)]; exact hcall.ra
  · rw [hoff 1072 (by decide), hfr 1072 (by omega)]; exact hcall.sv8
  · rw [hoff 1064 (by decide), hfr 1064 (by omega)]; exact hcall.sv9
  · rw [hoff 1056 (by decide), hfr 1056 (by omega)]; exact hcall.sv18
  · rw [hoff 1016 (by decide), hfr 1016 (by omega)]; exact hcall.sv23
  apply swp_closeF
  unfold F'
  iintro ⟨⟨Hst, Hnull, Hw, Hk⟩, Hms⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave Hst := evalFrame_join hsg.le hn $$ [Hst HS]
  · iframe Hst HS
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  unfold CallExitK
  iapply Hk $$ %_ %?_ Hregs Hst Hnull Hw Hpc Hra
  keep_split
  · ix_reg; exact (evalSP_restore s).trans hsp.symm
  all_goals ix_reg
  all_goals (rw [hkR _ (by decide) (by decide)]; subst hR1; ix_reg; exact hcall.keep _ (by decide))

#ix_chain callNativeOut := [callNativeOut_p1, callNativeOut_p2, callNativeOut_p3]

end VsaIris.Interp
