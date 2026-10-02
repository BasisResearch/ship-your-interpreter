import VsaIris.Interp.EnvRun
import VsaIris.Interp.SpecEnv
import Vsa.Sim.HelperCall

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

abbrev gprs : List Nat := eRegs.tail

theorem eRegs_eq : eRegs = VsaIris.PC :: gprs := rfl

theorem pc_not_gprs : VsaIris.PC ∉ gprs := by decide

section Regs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

def regsOf (rs : List Nat) (R : Nat → BitVec 64) : IProp GF := sepL rs (fun r => r ↦ᵣ R r)

theorem regsOf_congr {rs : List Nat} {R R' : Nat → BitVec 64} (h : ∀ r ∈ rs, R r = R' r) :
    regsOf (GF := GF) rs R = regsOf rs R' := by
  unfold regsOf
  exact sepL_congr fun r hr => by rw [h r hr]

@[simp] theorem regsOf_nil (R : Nat → BitVec 64) : regsOf (GF := GF) [] R = iprop(emp) := rfl

theorem regsOf_cons (r : Nat) (rs : List Nat) (R : Nat → BitVec 64) :
    regsOf (GF := GF) (r :: rs) R = iprop(r ↦ᵣ R r ∗ regsOf rs R) := rfl

theorem regsOf_merge_eq (rs ks : List Nat) (R R' : Nat → BitVec 64) :
    regsOf (GF := GF) (rs.filter (fun r => decide (r ∈ ks)))
        (fun r => if r ∈ ks then R' r else R r) =
      regsOf (rs.filter (fun r => decide (r ∈ ks))) R' ∧
    regsOf (GF := GF) (rs.filter (fun r => !decide (r ∈ ks)))
        (fun r => if r ∈ ks then R' r else R r) =
      regsOf (rs.filter (fun r => !decide (r ∈ ks))) R := by
  refine ⟨regsOf_congr fun r hr => ?_, regsOf_congr fun r hr => ?_⟩
  · have : r ∈ ks := by simpa using (List.mem_filter.1 hr).2
    simp [this]
  · have : r ∉ ks := by simpa using (List.mem_filter.1 hr).2
    simp [this]

theorem regsOf_extract (rs ks : List Nat) (hnd : rs.Nodup) (hks : ks.Nodup)
    (hsub : ∀ k ∈ ks, k ∈ rs) (R : Nat → BitVec 64) :
    regsOf (GF := GF) rs R ⊢ regsOf ks R ∗
      ∀ R' : Nat → BitVec 64, regsOf ks R' -∗ regsOf rs (fun r => if r ∈ ks then R' r else R r) := by
  have hperm : (rs.filter (fun r => decide (r ∈ ks))).Perm ks :=
    (List.perm_ext_iff_of_nodup (hnd.filter _) hks).2 fun k => by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨hsub k h, h⟩⟩
  unfold regsOf
  iintro H
  ihave ⟨Hin, Hout⟩ := (sepL_filter rs (fun r => decide (r ∈ ks)) _).1 $$ H
  ihave Hin := (sepL_perm _ hperm).1 $$ Hin
  iframe Hin
  iintro %R' HR'
  iapply (sepL_filter rs (fun r => decide (r ∈ ks)) _).2
  have hm := regsOf_merge_eq (GF := GF) rs ks R R'
  unfold regsOf at hm
  rw [hm.1, hm.2]
  iframe Hout
  iapply (sepL_perm _ hperm).2 $$ HR'

theorem regsOf_of_clobbered (clob : List Nat) (hnd : clob.Nodup) :
    clobbered (GF := GF) clob ⊢ ∃ f : Nat → BitVec 64, regsOf clob f :=
  clobbered_fn clob hnd

theorem clobbered_of_regsOf (clob : List Nat) (f : Nat → BitVec 64) :
    regsOf (GF := GF) clob f ⊢ clobbered clob :=
  clobbered_of_fn clob f

theorem regsOf_entry (rs : List Nat) (fixed : List (Nat × BitVec 64)) (clob : List Nat)
    (hperm : (fixed.map Prod.fst ++ clob).Perm rs) (hnd : rs.Nodup) :
    savedOwn (GF := GF) fixed ∗ clobbered clob ⊢
      ∃ R : Nat → BitVec 64, ⌜∀ p ∈ fixed, R p.1 = p.2⌝ ∗ regsOf rs R := by
  obtain ⟨hfx, hcl, hdj⟩ := List.nodup_append.1 (hperm.nodup_iff.2 hnd)
  iintro ⟨Hf, Hc⟩
  ihave Hf := savedOwn_fn fixed hfx $$ Hf
  ihave ⟨%f, Hc⟩ := clobbered_fn clob hcl $$ Hc
  classical
  obtain ⟨R, hR⟩ : ∃ R : Nat → BitVec 64,
      R = fun k => if k ∈ fixed.map Prod.fst then pairVal fixed k else f k := ⟨_, rfl⟩
  have e1 : sepL (GF := GF) (fixed.map Prod.fst) (fun r => r ↦ᵣ R r) =
      sepL (fixed.map Prod.fst) (fun k => k ↦ᵣ pairVal fixed k) :=
    sepL_congr fun k hk => by rw [hR]; simp only [hk, ite_true]
  have e2 : sepL (GF := GF) clob (fun r => r ↦ᵣ R r) = sepL clob (fun k => k ↦ᵣ f k) :=
    sepL_congr fun k hk => by
      have : k ∉ fixed.map Prod.fst := fun h => hdj k h k hk rfl
      rw [hR]; simp only [this, ite_false]
  iexists R
  isplitr
  · ipureintro
    intro p hp
    simp only [hR, List.mem_map_of_mem hp, ite_true]
    exact pairVal_of_mem fixed hfx p hp
  unfold regsOf
  iapply (sepL_perm _ hperm).1
  iapply (sepL_append _ _ _).2
  rw [e1, e2]
  iframe Hf Hc

theorem regsOf_exit (rs : List Nat) (fixed : List (Nat × BitVec 64)) (clob : List Nat)
    (hperm : (fixed.map Prod.fst ++ clob).Perm rs) (R : Nat → BitVec 64)
    (hR : ∀ p ∈ fixed, R p.1 = p.2) :
    regsOf (GF := GF) rs R ⊢ savedOwn fixed ∗ clobbered clob := by
  unfold regsOf
  iintro H
  ihave H := (sepL_perm _ hperm).2 $$ H
  ihave ⟨Hf, Hc⟩ := (sepL_append _ _ _).1 $$ H
  isplitl [Hf]
  · iapply savedOwn_back fixed R hR $$ Hf
  · iapply clobbered_of_fn clob R $$ Hc

end Regs

def memOf (img : Nat → BitVec 8) : List Nat → Mem
  | [] => ∅
  | a :: l => (memOf img l).insert a (img a)

theorem imgM_memOf (img : Nat → BitVec 8) :
    ∀ (l : List Nat) (a : Nat), a ∈ l → imgM (memOf img l) a = img a
  | [], _, h => absurd h (by simp)
  | b :: l, a, h => by
    unfold memOf imgM
    rw [Std.ExtHashMap.getElem?_insert]
    by_cases hab : b = a
    · subst hab; simp
    · simp only [beq_iff_eq, hab, ite_false]
      exact imgM_memOf img l a (by simpa [Ne.symm hab] using h)

theorem memOf_get (img : Nat → BitVec 8) :
    ∀ (l : List Nat) (a : Nat), a ∈ l → (memOf img l)[a]? = some (img a)
  | [], _, h => absurd h (by simp)
  | b :: l, a, h => by
    unfold memOf
    rw [Std.ExtHashMap.getElem?_insert]
    by_cases hab : b = a
    · subst hab; simp
    · simp only [beq_iff_eq, hab, ite_false]
      exact memOf_get img l a (by simpa [Ne.symm hab] using h)

theorem bytesAt_wordOf (f : Nat → BitVec 8) (a : Nat) : bytesAt f a 8 = wordOf f a := by
  simp [bytesAt, wordOf, List.range_succ]

theorem ldv_ld_img (Mt : Mem) (a : Nat) : ldv .ld Mt a = imgW (imgM Mt) a := by
  have hm : ∀ k, k < 8 → (memOf (imgM Mt) (List.range' a 8))[a + k]? = some (imgM Mt (a + k)) :=
    fun k hk => memOf_get _ _ _ (List.mem_range'.2 ⟨k, hk, by omega⟩)
  have hr : read64 (memOf (imgM Mt) (List.range' a 8)) a = some (imgW (imgM Mt) a).toNat := by
    rw [imgW_toNat]; exact readLE_of_img hm
  show bytesVal .ld (bytesAt (imgM Mt) a 8) = _
  rw [bytesAt_wordOf]
  exact wordOf_value hm hr

theorem ldv_lw_img (Mt : Mem) (a k : Nat) (hk : k < 2 ^ 31) (h : imgLE (imgM Mt) a 4 = k) :
    ldv .lw Mt a = BitVec.ofNat 64 k := by
  show bytesVal .lw (bytesAt (imgM Mt) a 4) = _
  simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, bytesVal, List.getD_cons_zero, List.getD_cons_succ,
    Nat.add_zero]
  refine Vsa.Sim.sext32_of_lt _ _ _ _ k hk ?_
  rw [← h]
  simp [imgLE, Nat.add_assoc]

section Tracked

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem ownSet_tracked (S : Nat → Prop) (img : Nat → BitVec 8) :
    ownSet (GF := GF) S (fun a => a ↦ₘ img a) ⊢
      ∃ Mt : Mem, ⌜∀ a, S a → imgM Mt a = img a⌝ ∗ ownSet S (fun a => a ↦ₘ imgM Mt a) := by
  unfold ownSet
  iintro ⟨%l, %⟨hnd, hmem⟩, Hl⟩
  iexists memOf img l
  have hag : ∀ a, S a → imgM (memOf img l) a = img a :=
    fun a ha => imgM_memOf img l a ((hmem a).2 ha)
  isplitr
  · ipureintro; exact hag
  iexists l
  isplitr
  · ipureintro; exact ⟨hnd, hmem⟩
  rw [sepL_congr (Ψ := fun a => a ↦ₘ imgM (memOf img l) a)
    (fun a ha => by rw [hag a ((hmem a).1 ha)])]
  iexact Hl

end Tracked

section Span

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {live : Nat → Prop}

theorem wp_ew (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {pc : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem} (h : EW live S Q pc R Mt) :
    textOwn (GF := GF) envText ∗ gp ↦ᵣ□ gpV ∗ VsaIris.PC ↦ᵣ pc ∗ regsOf gprs R ∗
      ownSet S (fun a => a ↦ₘ imgM Mt a) ∗
      (∀ rv mv, ⌜Q rv mv⌝ -∗ VsaIris.PC ↦ᵣ rv VsaIris.PC -∗ regsOf gprs rv -∗
        ownSet S (fun a => a ↦ₘ mv a) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  obtain ⟨n, hn⟩ := h
  let rv : Nat → BitVec 64 := fun r => if r = VsaIris.PC then pc else R r
  have hrun := hn rv (imgM Mt) ⟨by simp [rv], fun r _ hr => by simp [rv, hr], fun _ _ => rfl⟩
  iintro ⟨#Ht, #Hgp, Hpc, HR, HS, Hk⟩
  iapply wp_localRunW Wp n rv (imgM Mt) hrun
  have hro : roOwn (GF := GF) roR envText = iprop((gp ↦ᵣ□ gpV ∗ emp) ∗ textOwn envText) := rfl
  have hregs : sepL (GF := GF) eRegs (fun r => r ↦ᵣ rv r) =
      iprop(VsaIris.PC ↦ᵣ pc ∗ regsOf gprs R) := by
    rw [eRegs_eq, sepL_cons]
    unfold regsOf
    rw [sepL_congr (Ψ := fun r => r ↦ᵣ R r) (fun r hr => by
      simp [rv, show r ≠ VsaIris.PC from fun e => pc_not_gprs (e ▸ hr)])]
    simp [rv]
  rw [hro, hregs]
  iframe Ht Hgp HS Hpc HR
  iintro %rv' %mv' %hQ Hrs HS
  rw [eRegs_eq, sepL_cons]
  icases Hrs with ⟨Hpc, Hrs⟩
  iapply Hk $$ %rv' %mv' %hQ Hpc [Hrs] HS
  unfold regsOf; iexact Hrs

def Span (live : Nat → Prop) (S : Nat → Prop) (pc : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem)
    (F : BitVec 64 → (Nat → BitVec 64) → Mem → Prop) : Prop :=
  ∀ Q, (∀ pc' R' Mt', F pc' R' Mt' → EW live S Q pc' R' Mt') → EW live S Q pc R Mt

theorem Span.trans {live : Nat → Prop} {S : Nat → Prop} {pc : BitVec 64} {R : Nat → BitVec 64}
    {Mt : Mem} {F F' : BitVec 64 → (Nat → BitVec 64) → Mem → Prop}
    (h : Span live S pc R Mt F) (k : ∀ pc' R' Mt', F pc' R' Mt' → Span live S pc' R' Mt' F') :
    Span live S pc R Mt F' :=
  fun Q hk => h Q fun pc' R' Mt' hF => k pc' R' Mt' hF Q hk

theorem Span.mono {live : Nat → Prop} {S : Nat → Prop} {pc : BitVec 64} {R : Nat → BitVec 64}
    {Mt : Mem} {F F' : BitVec 64 → (Nat → BitVec 64) → Mem → Prop}
    (h : Span live S pc R Mt F) (k : ∀ pc' R' Mt', F pc' R' Mt' → F' pc' R' Mt') :
    Span live S pc R Mt F' :=
  fun Q hk => h Q fun pc' R' Mt' hF => hk pc' R' Mt' (k pc' R' Mt' hF)

theorem wp_span (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {S : Nat → Prop} {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    {F : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} (h : Span live S pc R Mt F) :
    textOwn (GF := GF) envText ∗ gp ↦ᵣ□ gpV ∗ VsaIris.PC ↦ᵣ pc ∗ regsOf gprs R ∗
      ownSet S (fun a => a ↦ₘ imgM Mt a) ∗
      (∀ pc' R' Mt', ⌜F pc' R' Mt'⌝ -∗ VsaIris.PC ↦ᵣ pc' -∗ regsOf gprs R' -∗
        ownSet S (fun a => a ↦ₘ imgM Mt' a) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  let Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop := fun rv mv =>
    ∃ R' Mt', F (rv VsaIris.PC) R' Mt' ∧ (∀ r ∈ gprs, rv r = R' r) ∧ ∀ a, S a → mv a = imgM Mt' a
  have hQ := h Q fun pc' R' Mt' hF => swp_done fun rv mv hm =>
    ⟨R', Mt', hm.pc ▸ hF, fun r hr => hm.regs r (List.mem_of_mem_tail hr)
      (fun e => pc_not_gprs (e ▸ hr)), hm.img⟩
  iintro ⟨#Ht, #Hgp, Hpc, HR, HS, Hk⟩
  iapply wp_ew Wp hQ
  iframe Ht Hgp Hpc HR HS
  iintro %rv %mv %⟨R', Mt', hF, hR, hM⟩ Hpc HR HS
  rw [regsOf_congr (R' := R') hR]
  ihave HS := ownSet_congr (Ψ := fun a => a ↦ₘ imgM Mt' a) (fun a ha => by rw [hM a ha]) $$ HS
  iapply Hk $$ %(rv VsaIris.PC) %R' %Mt' %hF Hpc HR HS

end Span

end VsaIris.Interp
