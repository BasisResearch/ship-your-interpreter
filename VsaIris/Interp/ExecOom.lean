import VsaIris.Interp.ExecEnv
import VsaIris.Interp.SpecErr
import VsaIris.Vsa.OomSites

/-!
# Allocating helpers from an exec arm, partial mode (lane E5)

In the uncounted regime `env_new` and `env_define` may run out of memory: their
specs' abort branch parks at the helper's out-of-memory block (`oomAt`, H1),
which H5's `wp_oomBlock` runs to `exit(1)`'s entry (`OomSites.oom80002a38`,
`oom80002bd0`), ending in `abortRes` over the arm's lowered stack. The call
steps: `ms_callRegsAbort` (`ms_callRegs` for a `fnSpecAbort`), `oom_regs` (the
registers a parked helper and the arm hold, as `wp_oomBlock` takes them),
`ms_callEnvNewP`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.VsaHeap
open Vsa.MemRepr Vsa.While Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs}

omit I in
/-- **A call from a run to a function that may abort**, by the callee's
register list: the return branch is `ms_callRegs`'s; on abort the run's other
registers `K` and its owned bytes join the callee's abort resource. -/
theorem ms_callRegsAbort (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalExec (vsaModel live) i code entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    {L K : List Nat} (hp : fRegs.Perm (L ++ K)) {P Q : BitVec 64 → IProp GF} {A X : IProp GF}
    {Y : (Nat → BitVec 64) → IProp GF} {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem}
    (hP : iprop(sepL L (fun x => x ↦ᵣ R x) ∗ X) ⊢ P (BitVec.ofNat 64 (i + 4)))
    (hQ : Q (BitVec.ofNat 64 (i + 4)) ⊢ ∃ f : Nat → BitVec 64, sepL L (fun x => x ↦ᵣ f x) ∗ Y f) :
    fnSpecAbort Wp entry P Q A ∗ codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗ X ∗
      ((∀ f : Nat → BitVec 64, Y f -∗
        ms (BitVec.ofNat 64 (i + 4))
          (upd (fun x => if x ∈ L then f x else R x) 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ) ∧
       (A -∗ sepL K (fun x => x ↦ᵣ R x) -∗ ownSet S byteAny -∗ Wp.W Φ))
    ⊢ Wp.W Φ := by
  unfold ms
  iintro ⟨#Hspec, #Hcode, ⟨Hpc, Hra, Hregs, HS⟩, HX, Hk⟩
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave ⟨HL, HK⟩ := (regFile_cut hp R).1 $$ Hregs
  iapply wp_callAbort Wp hexec
  iframe Hi Hspec Hpc Hra
  isplitl [HL HX]
  · iapply hP
    iframe HL HX
  isplit
  · iintro Hpc Hra HQ
    ihave ⟨%f, HL, HY⟩ := hQ $$ HQ
    ihave Hregs := regFile_uncut hp R f $$ [HL HK]
    · iframe HL HK
    ihave Hk := and_elim_l $$ Hk
    iapply Hk $$ %f HY
    rw [regFile_upd_ra]
    simp only [upd_same]
    iframe Hpc Hra Hregs HS
  · iintro HA
    ihave Hk := and_elim_r $$ Hk
    iapply Hk $$ HA HK
    iapply ownSet_forget $$ HS

/-- The registers a parked allocating helper holds (`env_new`'s and
`env_define`'s `oomAt` list). -/
abbrev envOomRegs : List Nat := VsaIris.ra :: 10 :: retClob ++ newSaved

omit I in
/-- **The registers at an out-of-memory block**: a parked helper's and the
arm's `s7`-`s11`, as `wp_oomBlock` takes them. -/
theorem oom_regs (R : Nat → BitVec 64) :
    clobbered (GF := GF) envOomRegs ∗ sepL [23, 24, 25, 26, 27] (fun x => x ↦ᵣ R x) ⊢
      ∃ (r : BitVec 64) (cs : Nat → BitVec 64), ra ↦ᵣ r ∗ clobbered Newlib.argRegs ∗
        clobbered Newlib.tmpRegs ∗ sepL Newlib.calleeSaved (fun q => q ↦ᵣ cs q) := by
  iintro ⟨Hc, HK⟩
  ihave ⟨%f, Hc⟩ := clobbered_fn envOomRegs (by decide) $$ Hc
  let g : Nat → BitVec 64 := fun x => if x ∈ [23, 24, 25, 26, 27] then R x else f x
  have eC : sepL (GF := GF) envOomRegs (fun x => x ↦ᵣ f x) = sepL envOomRegs (fun x => x ↦ᵣ g x) :=
    sepL_congr fun x hx => by
      have : x ∉ [23, 24, 25, 26, 27] := (show ∀ y ∈ envOomRegs, y ∉ [23, 24, 25, 26, 27] by decide) x hx
      simp only [g, this, ite_false]
  have eK : sepL (GF := GF) [23, 24, 25, 26, 27] (fun x => x ↦ᵣ R x) =
      sepL [23, 24, 25, 26, 27] (fun x => x ↦ᵣ g x) := sepL_congr fun x hx => by
        simp only [g, hx, ite_true]
  rw [eC] at *
  rw [eK] at *
  ihave H := (sepL_append _ _ _).2 $$ [Hc HK]
  · iframe Hc HK
  have hp : (envOomRegs ++ [23, 24, 25, 26, 27]).Perm
      (1 :: (Newlib.argRegs ++ (Newlib.tmpRegs ++ Newlib.calleeSaved))) := by decide
  ihave H := (sepL_perm _ hp).1 $$ H
  rw [sepL_cons]
  ihave ⟨Hra, H⟩ := H
  ihave ⟨Ha, H⟩ := (sepL_append _ _ _).1 $$ H
  ihave ⟨Ht, Hs⟩ := (sepL_append _ _ _).1 $$ H
  iexists g 1, g
  unfold VsaIris.ra
  iframe Hra Hs
  isplitl [Ha]
  · iapply clobbered_of_fn _ g $$ Ha
  · iapply clobbered_of_fn _ g $$ Ht

/-- **`env_new(env)` from a run, uncounted regime** (partial mode): the
return branch is `ms_callEnvNewW`'s; out of memory, the helper's block runs to
`exit(1)`'s entry (`wp_oomBlock` at `oom80002a38`) over the arm's lowered stack
`[R 2 - n, R 2)`, which the abort branch receives as `abortRes`. -/
theorem ms_callEnvNewP (HN : Newlib.NewlibHoles) (hcl : Newlib.CodeLive live) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code envNewPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) {inp : Nat} {st : St} {d env : Nat}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {n : Nat}
    (hsp : EnvSp (R 2) envNewNeed) (hn : envNewNeed ≤ n) (hn2 : n ≤ (R 2).toNat)
    (hlo : Vsa.Sim.tohostAddr + 16 ≤ (R 2).toNat - n) (hfit : (R 2).toNat - n + Newlib.fwriteNeed + 16 ≤ (R 2).toNat)
    (hhi : (R 2).toNat ≤ 0x88000000) :
    envNewSpec (wpW (vsaModel live)) N ∗ codeRes ∗ Newlib.binImg ∗ ms (BitVec.ofNat 64 i) R S Mt ∗
      stackScratch (R 2) n ∗ □ frameAt env (R 10).toNat ∗
      world N vsaLayoutP vsaRoomB inp .uncounted st d ∗
      ((∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ (10 :: retClob) → R' x = R x⌝ -∗
          stackScratch (R 2) n -∗
          world N vsaLayoutP vsaRoomB inp .uncounted ⟨(st.store.allocFrame (some env)).1, st.out⟩ d -∗
          frameAt st.store.frames.size (R' 10).toNat -∗
          ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortRes N vsaLayoutP vsaRoomB inp (R 2) n ∗ ownSet S byteAny -∗ (wpW (vsaModel live)).W Φ))
    ⊢ (wpW (vsaModel live)).W Φ := by
  unfold envNewSpec
  iintro ⟨#Hen, #Hcode, #Himg, Hms, Hst, #Hfr, Hw, Hk⟩
  ihave #Hgp := codeRes_gp $$ Hcode
  ihave ⟨Hh, Hc, Hio, Hi⟩ := (world_heapStore N inp .uncounted st d).1 $$ Hw
  ihave ⟨%H, %B, Hhr, Hs, %hB⟩ := (show heapStore (GF := GF) N .uncounted st.store ⊢
    ∃ H B, heapRes vsaLayoutP vsaRoomB .uncounted H ∗ storeRepr N st.store B ∗ ⌜∀ b ∈ B, b ∈ H⌝
    by unfold heapStore; exact .rfl) $$ Hh
  ihave ⟨⟨Hs, -⟩, %hne⟩ := keep_pure (storeRepr_frameAt_ne (N := N) (s := st.store) (B := B)
    (fa := env) (e := (R 10).toNat)) $$ [Hs]
  · iframe Hs Hfr
  ihave ⟨Hsl, Hst⟩ := stackScratch_narrow (s := R 2) hn2 hn $$ Hst
  ihave #Hspec := Hen $$ %.uncounted %st.store %(some env) %(R 10) %(R 2)
    %(newSaved.map fun k => (k, R k)) %(by simp [newSaved])
  iapply (ms_callRegsAbort (wpW _) hexec hcode (L := envNewL) (K := [23, 24, 25, 26, 27])
    (by decide)
    (P := fun r => iprop(⌜r.toNat % 4 = 0 ∧ EnvSp (R 2) envNewNeed⌝ ∗ (10 : Nat) ↦ᵣ R 10 ∗
      sp ↦ᵣ R 2 ∗ gp ↦ᵣ□ gpV ∗ clobbered retClob ∗ savedOwn (newSaved.map fun k => (k, R k)) ∗
      stackScratch (R 2) envNewNeed ∗ parentAt (some env) (R 10).toNat ∗
      heapStore N (Regime.uncounted.plus envBytes) st.store))
    (Q := fun _ => iprop(∃ e : BitVec 64, (10 : Nat) ↦ᵣ e ∗ sp ↦ᵣ R 2 ∗ clobbered retClob ∗
      savedOwn (newSaved.map fun k => (k, R k)) ∗ stackScratch (R 2) envNewNeed ∗
      heapStore N .uncounted (st.store.allocFrame (some env)).1 ∗
      frameAt st.store.frames.size e.toNat))
    (X := iprop(gp ↦ᵣ□ Newlib.gpV ∗ stackScratch (R 2) envNewNeed ∗
      parentAt (some env) (R 10).toNat ∗ heapStore N .uncounted st.store))
    (Y := fun f => iprop(⌜f 2 = R 2 ∧ ∀ k ∈ newSaved, f k = R k⌝ ∗
      stackScratch (R 2) envNewNeed ∗ heapStore N .uncounted (st.store.allocFrame (some env)).1 ∗
      frameAt st.store.frames.size (f 10).toNat))
    (R := R) (S := S) (Mt := Mt) ?hP ?hQ)
  case hP =>
    simp only [envNewL, sepL_cons]
    iintro ⟨⟨H10, H2, Hcs⟩, #Hgp', Hst, #Hpar', Hh⟩
    ihave ⟨Hcl, Hsv⟩ := (sepL_append _ _ _).1 $$ Hcs
    unfold VsaIris.sp savedOwn
    rw [show Newlib.gpV = MallocFast.gpV from rfl, Regime.plus_uncounted]
    iframe H10 H2 Hgp' Hst Hpar' Hh
    isplitl []
    · ipureintro; exact ⟨hi4, hsp⟩
    isplitl [Hcl]
    · iapply clobbered_of_fn retClob R $$ Hcl
    · rw [VsaIris.sepL_map]; iexact Hsv
  case hQ =>
    unfold VsaIris.sp savedOwn
    iintro ⟨%q, H10, H2, Hcl, Hsv, Hst, Hh, #Hfr⟩
    ihave ⟨%g, Hcl⟩ := clobbered_fn retClob (by decide) $$ Hcl
    iexists (fun y => if y = 10 then q else if y = 2 then R 2 else if y ∈ newSaved then R y else g y)
    simp only [envNewL, sepL_cons]
    rw [VsaIris.sepL_map] at *
    have eCl : sepL (GF := GF) retClob (fun y => y ↦ᵣ (if y = 10 then q else if y = 2 then R 2
        else if y ∈ newSaved then R y else g y)) = sepL retClob (fun y => y ↦ᵣ g y) :=
      sepL_congr fun y hy => by
        obtain ⟨h10, h2, hs⟩ := (show ∀ y ∈ retClob, y ≠ 10 ∧ y ≠ 2 ∧ y ∉ newSaved by decide) y hy
        simp [h10, h2, hs]
    have eSv : sepL (GF := GF) newSaved (fun y => y ↦ᵣ (if y = 10 then q else if y = 2 then R 2
        else if y ∈ newSaved then R y else g y)) = sepL newSaved (fun y => y ↦ᵣ R y) :=
      sepL_congr fun y hy => by
        obtain ⟨h10, h2⟩ := (show ∀ y ∈ newSaved, y ≠ 10 ∧ y ≠ 2 by decide) y hy
        simp [h10, h2, hy]
    simp only [ite_true, show (2 : Nat) ≠ 10 from by decide, ite_false]
    isplitl [H10 H2 Hcl Hsv]
    · iframe H10 H2
      iapply (sepL_append _ _ _).2
      rw [eCl, eSv]
      iframe Hcl Hsv
    iframe Hst Hh Hfr
    ipureintro
    refine ⟨trivial, fun k hk => ?_⟩
    obtain ⟨h10, h2⟩ := (show ∀ y ∈ newSaved, y ≠ 10 ∧ y ≠ 2 by decide) k hk
    simp [h10, h2, hk]
  iframe Hspec Hcode Hms Hgp Hst
  isplitl [Hhr Hs]
  · isplitl []
    · simp only [parentAt]; iframe Hfr; ipureintro; exact hne
    unfold heapStore; iexists H, B; iframe Hhr Hs; ipureintro; exact hB
  isplit
  · -- the return branch
    iintro %f ⟨%⟨hf2, hfs⟩, Hst, Hh, #Hnew⟩ Hms
    ihave Hk := and_elim_l $$ Hk
    have hkeep : ∀ x ∈ fRegs, x ∉ (10 :: retClob) →
        (fun x => if x ∈ envNewL then f x else R x) x = R x := by
      intro x hx hc
      by_cases hL : x ∈ envNewL
      · simp only [hL, ite_true]
        by_cases h2 : x = 2
        · subst h2; exact hf2
        · have hs : x ∈ newSaved :=
            (show ∀ y ∈ envNewL, y ∉ (10 :: retClob) → y ≠ 2 → y ∈ newSaved by decide) x hL hc h2
          exact hfs x hs
      · simp [hL]
    have e10 : (fun x => if x ∈ envNewL then f x else R x) 10 = f 10 := by
      simp only [show (10 : Nat) ∈ envNewL from by decide, ite_true]
    rw [← e10] at *
    ihave Hst := stackScratch_widen hn2 hn $$ [Hsl Hst]
    · iframe Hsl Hst
    iapply Hk $$ %(fun x => if x ∈ envNewL then f x else R x) %hkeep Hst [Hh Hc Hio Hi] Hnew Hms
    iapply (world_heapStore N inp _ _ d).2
    iframe Hh Hc Hio Hi
  · -- out of memory
    iintro ⟨-, HA⟩ HK HS
    unfold oomAt
    icases HA with ⟨Hpc, Hsp, Hcl, Hst, -⟩
    ihave ⟨%r, %cs, Hra, Hargs, Htmp, Hcs⟩ := oom_regs R $$ [Hcl HK]
    · iframe Hcl HK
    ihave Hst := stackScratch_widen hn2 hn $$ [Hsl Hst]
    · iframe Hsl Hst
    ihave Hk := and_elim_r $$ Hk
    have e16 : (R 2 - 16#64).toNat = (R 2).toNat - 16 := toNat_sub_frame (by
      simp only [BitVec.toNat_ofNat]; have := hsp.lo; unfold htifLo envNewNeed at this; omega)
    iapply Newlib.Oom.wp_oomBlock HN live hcl (wpW _) N vsaLayoutP vsaRoomB inp
      Newlib.OomSites.oom80002a38 Newlib.OomSites.oom80002a38_ok (R 2) (R 2 - 16#64) r n
      ⟨hn2, hlo, by rw [e16]; omega, by rw [e16]; show (R 2).toNat - 16 + 0 ≤ (R 2).toNat; omega,
        hhi, by rw [e16]; have := hsp.align; omega⟩ cs st.out
    rw [show BitVec.ofNat 64 Newlib.OomSites.oom80002a38.head = 0x80002a38#64 from rfl]
    iframe Hpc Hra Hsp Hargs Htmp Hcs Hgp Himg Hst Hio Hc
    iintro HA
    iapply Hk
    iframe HA HS

end

end VsaIris.Interp
