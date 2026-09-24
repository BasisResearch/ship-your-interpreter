import VsaIris.Interp.EnvDefineSpans
import VsaIris.Interp.EnvDefineCalls
import VsaIris.Interp.DefineCost
import VsaIris.Stack
import VsaIris.Interp.ProofEnvSet

/-!
# `env_define`'s arms, at the Iris level

The constants of one call (`DefCall`), what its entry guarantees
(`DefCall.OK`), and the additive pair of continuations it ends in (`defK`:
the return, or the out-of-memory abort). The two sinks every path reaches:
`def_ret` (the epilogue, then the return) and `def_oom` (the out-of-memory
arm `0x80002bd0`, parked for the abort).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

/-- The constants of one `env_define` call: entry `sp`, return address, the
name and value pointers, the name and value, the callee-saved words, and the
value slot's bytes at the entry. -/
structure DefCall where
  s : BitVec 64
  r : BitVec 64
  pn : BitVec 64
  vp : BitVec 64
  x : String
  v : Value
  saved : List (Nat × BitVec 64)
  so : Nat → BitVec 8

/-- What the entry guarantees about a call's constants. -/
structure DefCall.OK (C : DefCall) : Prop where
  sp : EnvSp C.s envDefineNeed
  slot : SlotWin C.vp.toNat
  ra : C.r.toNat % 4 = 0
  saved : C.saved.map Prod.fst = defineSaved
  sep : C.vp.toNat + 24 ≤ C.s.toNat - envDefineNeed ∨ C.s.toNat ≤ C.vp.toNat

theorem DefCall.OK.s64 {C : DefCall} (h : C.OK) : htifLo + 16 + 64 ≤ C.s.toNat := by
  have := h.sp.lo; unfold envDefineNeed at this; omega

theorem DefCall.OK.sepStk {C : DefCall} (h : C.OK) :
    C.vp.toNat + 24 ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ C.vp.toNat := by
  have := h.sep; unfold envDefineNeed at this; omega

section Sinks

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- The registers the abort hands over clobbered: all but `sp`. -/
abbrev oomRegs : List Nat := VsaIris.ra :: 10 :: retClob ++ defineSaved

/-- **The pair of continuations** an `env_define` path ends in, with the
final regime `ρ` and store `st'`. -/
def defK (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (C : DefCall) (ρ : Regime) (st' : Store) : IProp GF :=
  iprop((VsaIris.PC ↦ᵣ C.r -∗ VsaIris.ra ↦ᵣ C.r -∗
      (VsaIris.sp ↦ᵣ C.s ∗ clobbered (10 :: retClob) ∗ savedOwn C.saved ∗
        stackScratch C.s envDefineNeed ∗ valAt N C.vp.toNat C.v ∗ heapStore N ρ st') -∗ Wp.W Φ) ∧
    ((⌜ρ = .uncounted⌝ ∗ oomAt 0x80002bd0#64 (C.s - 64#64) C.s envDefineNeed oomRegs ∗
      valAt N C.vp.toNat C.v) -∗ Wp.W Φ))

omit I in
theorem toNat_s64 {C : DefCall} (hC : C.OK) : (C.s - 64#64).toNat = C.s.toNat - 64 :=
  toNat_sub_frame (by have := hC.s64; simp; omega)

omit I in
/-- The entry stack as the 64-byte frame and the callees' scratch below it. -/
theorem def_stack_split {C : DefCall} (hC : C.OK) :
    stackScratch (GF := GF) C.s envDefineNeed ⊢
      stackScratch (C.s - 64#64) allocHeadroom ∗ blockOwn (C.s.toNat - 64) 64 := by
  iintro H
  ihave ⟨H1, H2⟩ := stackScratch_frame (s := C.s) (f := 64#64) (n := envDefineNeed)
    (by have := hC.sp.lo; unfold envDefineNeed allocHeadroom at *; omega)
    (by unfold envDefineNeed allocHeadroom; decide) $$ H
  rw [show envDefineNeed - (64#64 : BitVec 64).toNat = allocHeadroom from rfl, toNat_s64 hC,
    show (64#64 : BitVec 64).toNat = 64 from rfl]
  iframe H1 H2

omit I in
/-- The inverse of `def_stack_split`. -/
theorem def_stack_join {C : DefCall} (hC : C.OK) :
    stackScratch (GF := GF) (C.s - 64#64) allocHeadroom ∗ blockOwn (C.s.toNat - 64) 64 ⊢
      stackScratch C.s envDefineNeed := by
  iintro ⟨H1, H2⟩
  iapply stackScratch_unframe (s := C.s) (f := 64#64) (n := envDefineNeed)
    (by have := hC.sp.lo; unfold envDefineNeed allocHeadroom at *; omega)
    (by unfold envDefineNeed allocHeadroom; decide)
  rw [show envDefineNeed - (64#64 : BitVec 64).toNat = allocHeadroom from rfl, toNat_s64 hC,
    show (64#64 : BitVec 64).toNat = 64 from rfl]
  iframe H1 H2

/-- The slot's bytes and the entry meaning give back `valAt`. -/
theorem def_valAt (N : NativeAddrs) {C : DefCall} {Mt : Mem}
    (hslot : ∀ a, C.vp.toNat ≤ a → a < C.vp.toNat + 24 → imgM Mt a = C.so a) :
    ownSet (GF := GF) (InExt (C.vp.toNat, 24)) (fun a => a ↦ₘ imgM Mt a) ∗
      valImg N C.so C.vp.toNat C.v ⊢ valAt N C.vp.toNat C.v := by
  iintro ⟨Hout, #Hv⟩
  unfold valAt
  iexists (imgM Mt)
  iframe Hout
  rw [valImg_agree N C.v fun o ho => hslot _ (by omega) (by omega)]
  iexact Hv

/-- **The return**: the epilogue `0x80002aec` from the frame, then the return
continuation. -/
theorem def_ret (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hl : ∀ p ∈ envText, live p.1) (N : NativeAddrs) {C : DefCall} (hC : C.OK) {ρ : Regime}
    {st' : Store} {R : Nat → BitVec 64} {Mt : Mem}
    (hstk : DefStack C.s.toNat C.r (pairVal C.saved) R Mt)
    (hslot : ∀ a, C.vp.toNat ≤ a → a < C.vp.toNat + 24 → imgM Mt a = C.so a) :
    textOwn envText ∗ gp ↦ᵣ□ gpV ∗ valImg N C.so C.vp.toNat C.v ∗
      VsaIris.PC ↦ᵣ 0x80002aec#64 ∗ regsOf gprs R ∗
      ownSet (baseS C.s.toNat C.vp.toNat) (fun a => a ↦ₘ imgM Mt a) ∗
      stackScratch (C.s - 64#64) allocHeadroom ∗ heapStore N ρ st' ∗ defK Wp Φ N C ρ st'
    ⊢ Wp.W Φ := by
  iintro ⟨#Ht, #Hgp, #Hv, Hpc, HR, HB, Hscr, Hhs, HK⟩
  have hs := hC.s64
  iapply wp_span Wp (def_epi hl (S := baseS C.s.toNat C.vp.toNat) hs hC.sp.hi hC.ra hstk
    (fun a h1 h2 => .inl ⟨h1, h2⟩))
  iframe Ht Hgp Hpc HR HB
  iintro %pc1 %R1 %Mt1 %⟨rfl, rfl, hret⟩ Hpc HR HB
  have hperm : (([(VsaIris.ra, C.r), (VsaIris.sp, C.s)] ++ C.saved).map Prod.fst ++
      (10 :: retClob)).Perm gprs := by
    simp only [List.map_append, List.map_cons, List.map_nil, hC.saved]; decide
  have hfix : ∀ p ∈ [(VsaIris.ra, C.r), (VsaIris.sp, C.s)] ++ C.saved, R1 p.1 = p.2 := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hret.ra
      · show R1 2 = C.s
        rw [hret.sp]; exact BitVec.eq_of_toNat_eq (by simp)
    · rw [hret.saved p.1 (by rw [← hC.saved]; exact List.mem_map_of_mem hp),
        pairVal_of_mem C.saved (by rw [hC.saved]; decide) p hp]
  ihave ⟨Hfix, Hcl⟩ := regsOf_exit gprs _ (10 :: retClob) hperm R1 hfix $$ HR
  unfold savedOwn
  ihave ⟨H2, Hsv⟩ := (sepL_append _ _ _).1 $$ Hfix
  simp only [sepL_cons, sepL_nil]
  icases H2 with ⟨Hra, Hsp, -⟩
  ihave ⟨Hstk, Hout⟩ := scan_exit_bytes (Mt := Mt1) (by omega) hC.sepStk $$ HB
  unfold defK
  ihave Kret := and_elim_l $$ HK
  iapply Kret $$ Hpc Hra
  unfold savedOwn
  iframe Hsp Hcl Hsv Hhs
  isplitl [Hscr Hstk]
  · iapply def_stack_join hC; iframe Hscr Hstk
  iapply def_valAt N hslot; iframe Hout Hv

/-- **The out-of-memory arm** `0x80002bd0`: parked for the abort, uncounted. -/
theorem def_oom (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (N : NativeAddrs) {C : DefCall} (hC : C.OK) {ρ : Regime} {st' : Store}
    {R : Nat → BitVec 64} {Mt : Mem} {H : List (Nat × Nat)} (hρ : ρ = .uncounted)
    (h2 : (R 2).toNat = C.s.toNat - 64)
    (hslot : ∀ a, C.vp.toNat ≤ a → a < C.vp.toNat + 24 → imgM Mt a = C.so a) :
    valImg N C.so C.vp.toNat C.v ∗ VsaIris.PC ↦ᵣ 0x80002bd0#64 ∗ regsOf gprs R ∗
      ownSet (baseS C.s.toNat C.vp.toNat) (fun a => a ↦ₘ imgM Mt a) ∗
      stackScratch (C.s - 64#64) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB .uncounted H ∗ defK Wp Φ N C ρ st'
    ⊢ Wp.W Φ := by
  iintro ⟨#Hv, Hpc, HR, HB, Hscr, Hh, HK⟩
  have hs := hC.s64
  have hperm : ([(VsaIris.sp, C.s - 64#64)].map Prod.fst ++ oomRegs).Perm gprs := by
    simp only [List.map_cons, List.map_nil]; decide
  ihave ⟨Hsp, Hcl⟩ := regsOf_exit gprs _ _ hperm R (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    show R 2 = C.s - 64#64
    apply BitVec.eq_of_toNat_eq; rw [h2, toNat_s64 hC]) $$ HR
  unfold savedOwn
  simp only [sepL_cons, sepL_nil]
  icases Hsp with ⟨Hsp, -⟩
  ihave ⟨Hstk, Hout⟩ := scan_exit_bytes (Mt := Mt) (by omega) hC.sepStk $$ HB
  unfold defK
  ihave Kab := and_elim_r $$ HK
  iapply Kab
  isplitl []
  · ipureintro; exact hρ
  isplitl [Hpc Hsp Hcl Hscr Hstk Hh]
  · unfold oomAt
    iframe Hpc Hsp Hcl
    isplitl [Hscr Hstk]
    · iapply def_stack_join hC; iframe Hscr Hstk
    iexists H; iexact Hh
  iapply def_valAt N hslot; iframe Hout Hv

end Sinks

end VsaIris.Interp
