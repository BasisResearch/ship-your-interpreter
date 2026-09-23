import VsaIris.Interp.EnvRun
import VsaIris.Interp.SpecEnv
import Vsa.Sim.HelperCall

/-!
# `env_*` spans at the Iris level

An `env_*` helper is a chain of spans and calls. A span is call-free code
between two call sites (or the entry and a `ret`); it is proved first-order,
as `EW live S Q pc R Mt` (`SWP` over `envText`, driven by the generated step
table and `sx_run`), and entered at the Iris level by ONE rule, `wp_ew`. The
calls are taken at the Iris level against the callees' specs (`wp_callW`),
with the register file split around them by `regsOf_extract`.

* `regsOf rs R`: the registers `rs` at the values `R`.
* `wp_ew`: a span from the PC, the general-purpose registers `gprs` and an
  owned byte set at a tracking memory's image.
* `regsOf_extract`: take the registers a call touches out of the file, and put
  back any values for them.
* `ownSet_tracked`: any owned image is the image of some tracking memory.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

/-- The general-purpose registers an `env_*` span owns (`eRegs` without `PC`). -/
abbrev gprs : List Nat := eRegs.tail

theorem eRegs_eq : eRegs = VsaIris.PC :: gprs := rfl

theorem eRegs_nodup : eRegs.Nodup := by decide

theorem pc_not_gprs : VsaIris.PC ∉ gprs := by decide

section Regs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The registers `rs` at the values `R`. -/
def regsOf (rs : List Nat) (R : Nat → BitVec 64) : IProp GF := sepL rs (fun r => r ↦ᵣ R r)

theorem regsOf_congr {rs : List Nat} {R R' : Nat → BitVec 64} (h : ∀ r ∈ rs, R r = R' r) :
    regsOf (GF := GF) rs R = regsOf rs R' := by
  unfold regsOf
  exact sepL_congr fun r hr => by rw [h r hr]

@[simp] theorem regsOf_nil (R : Nat → BitVec 64) : regsOf (GF := GF) [] R = iprop(emp) := rfl

theorem regsOf_cons (r : Nat) (rs : List Nat) (R : Nat → BitVec 64) :
    regsOf (GF := GF) (r :: rs) R = iprop(r ↦ᵣ R r ∗ regsOf rs R) := rfl

/-- The registers of an `if`-merged file are the two files' on their parts. -/
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

/-- **The registers a call touches, out of the file.** `ks` (distinct, inside
`rs`) come out at their current values; any new values for them go back. -/
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

/-- The clobbered registers as a file at some values. -/
theorem regsOf_of_clobbered (clob : List Nat) (hnd : clob.Nodup) :
    clobbered (GF := GF) clob ⊢ ∃ f : Nat → BitVec 64, regsOf clob f :=
  clobbered_fn clob hnd

theorem clobbered_of_regsOf (clob : List Nat) (f : Nat → BitVec 64) :
    regsOf (GF := GF) clob f ⊢ clobbered clob :=
  clobbered_of_fn clob f

/-- **The register file from an ABI entry**: registers at known values
(`fixed`: the arguments, `ra`, `sp`, the callee-saved ones) and clobbered ones
make up `rs` at some file `R` agreeing with `fixed`. -/
theorem regsOf_entry (rs : List Nat) (fixed : List (Nat × BitVec 64)) (clob : List Nat)
    (hperm : (fixed.map Prod.fst ++ clob).Perm rs) (hnd : rs.Nodup) :
    savedOwn (GF := GF) fixed ∗ clobbered clob ⊢
      ∃ R : Nat → BitVec 64, ⌜∀ p ∈ fixed, R p.1 = p.2⌝ ∗ regsOf rs R := by
  have hnd' : (fixed.map Prod.fst ++ clob).Nodup := hperm.nodup_iff.2 hnd
  have hfx : (fixed.map Prod.fst).Nodup := (List.nodup_append.1 hnd').1
  have hcl : clob.Nodup := (List.nodup_append.1 hnd').2.1
  have hdj := (List.nodup_append.1 hnd').2.2
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
    have hm : p.1 ∈ fixed.map Prod.fst := List.mem_map_of_mem hp
    simp only [hR, hm, ite_true]
    exact pairVal_of_mem fixed hfx p hp
  unfold regsOf
  iapply (sepL_perm _ hperm).1
  iapply (sepL_append _ _ _).2
  rw [e1, e2]
  iframe Hf Hc

/-- **The register file at an ABI return**: registers at known values and
the clobbered rest. -/
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

/-! ## Tracking memories -/

/-- A memory holding `img` at the listed addresses. -/
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

/-! ## Load values as image reads

The step table names a load's value `ldv k Mt a`; frames and values are
stated over images (`imgLE`/`imgW`). -/

theorem bytesAt_wordOf (f : Nat → BitVec 8) (a : Nat) : bytesAt f a 8 = wordOf f a := by
  simp [bytesAt, wordOf, List.range_succ]

/-- A doubleword load reads the image's word. -/
theorem ldv_ld_img (Mt : Mem) (a : Nat) : ldv .ld Mt a = imgW (imgM Mt) a := by
  have hm : ∀ k, k < 8 → (memOf (imgM Mt) (List.range' a 8))[a + k]? = some (imgM Mt (a + k)) :=
    fun k hk => memOf_get _ _ _ (List.mem_range'.2 ⟨k, hk, by omega⟩)
  have hr : read64 (memOf (imgM Mt) (List.range' a 8)) a = some (imgW (imgM Mt) a).toNat := by
    rw [imgW_toNat]; exact readLE_of_img hm
  show bytesVal .ld (bytesAt (imgM Mt) a 8) = _
  rw [bytesAt_wordOf]
  exact wordOf_value hm hr

/-- A word load of a small nonnegative count. -/
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

/-- **Any owned image is a tracking memory's image** on the owned set. -/
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

/-! ## The span rule -/

section Span

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {live : Nat → Prop}

/-- **One `env_*` span, at the Iris level.** From the PC at `pc`, the
general-purpose registers at `R`, and the owned bytes `S` at the tracking
memory's image, a span proved first-order (`EW`) runs to its end condition
`Q`; the continuation gets the final values. Everything else the caller owns
is framed by the continuation. -/
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

/-- A span proved first-order with its exits described by `F`: whatever the
rest of the run `Q` is, it holds from `pc` once it holds from every exit
`F` admits. `sx_run` proves these (its reached goals are closed by `hk`). -/
def Span (live : Nat → Prop) (S : Nat → Prop) (pc : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem)
    (F : BitVec 64 → (Nat → BitVec 64) → Mem → Prop) : Prop :=
  ∀ Q, (∀ pc' R' Mt', F pc' R' Mt' → EW live S Q pc' R' Mt') → EW live S Q pc R Mt

/-- Spans compose: continue every exit of the first with a span. -/
theorem Span.trans {live : Nat → Prop} {S : Nat → Prop} {pc : BitVec 64} {R : Nat → BitVec 64}
    {Mt : Mem} {F F' : BitVec 64 → (Nat → BitVec 64) → Mem → Prop}
    (h : Span live S pc R Mt F) (k : ∀ pc' R' Mt', F pc' R' Mt' → Span live S pc' R' Mt' F') :
    Span live S pc R Mt F' :=
  fun Q hk => h Q fun pc' R' Mt' hF => k pc' R' Mt' hF Q hk

/-- A span with no instructions. -/
theorem Span.refl {live : Nat → Prop} {S : Nat → Prop} {pc : BitVec 64} {R : Nat → BitVec 64}
    {Mt : Mem} {F : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} (h : F pc R Mt) :
    Span live S pc R Mt F :=
  fun _ hk => hk pc R Mt h

/-- **A span at the Iris level**, exits described by `F`. The continuation
gets the exit PC, the registers and the tracking memory at the exit, and
`F`'s facts about them. -/
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
