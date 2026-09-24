import VsaIris.Interp.ProofNativePrint

/-!
# `native_println` (lane H2)

`native_println(sret, in, argc, args, line)` calls `native_print` with its
own frame's 24-byte slot as the result, prints `'\n'` with `fputc`, and
returns `null` (`value_null`) in the caller's slot. Four runs, three calls:
`native_print` by `nativePrint_spec`, `fputc` by `IrisHoles.out`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib VsaIris.Stdio
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- The bytes `native_println`'s runs own: its frame above the slot (the two
saved words and a pad word). -/
abbrev nplF (s : BitVec 64) (k : Nat) : Prop := InExt (s.toNat - 24, 24) k

/-- And newlib's two words. -/
abbrev nplS (s : BitVec 64) (k : Nat) : Prop := nplF s k ∨ ioW k

macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; simp only [mem_accAddrs_iff, nplS, nplF, ioW, VsaIris.InExt] at *; sx_addr))

/-! ## The runs -/

/- The prologue: to `jal native_print`. -/
#ix_seg npl_pro {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {rv : Nat → BitVec 64}
    {s r : BitVec 64} (h2 : rv 2 = s)
    (hs1 : 0x87800000 + 48 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0) :
    IW live ∅ [] (nplF s) Q nativePrintlnPC (upd rv 1 r) M
  by
    have hsf : (s + 18446744073709551568#64).toNat = s.toNat - 48 := by
      rw [BitVec.toNat_add]; simp; omega
    unfold nativePrintlnPC
    ix_run hlive using [h2, hsf] at 0x80002f90

/- After `native_print`: `stdout`, to `jal fputc`. -/
#ix_seg npl_mid {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64}
    (hio1 : ldv .ld M 0x8001b970 = 0x8001b538#64) (hio2 : ldv .ld M 0x8001b548 = 0x8001bb20#64) :
    IW live ∅ [] (nplS s) Q 0x80002f94#64 R M
  by
    ix_run hlive using [hio1, hio2] at 0x80002fa0

/- After `fputc`: to `jal value_null`. -/
#ix_seg npl_null {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} :
    IW live ∅ [] (nplF s) Q 0x80002fa4#64 R M
  by
    ix_run hlive at 0x80002fa8

/- The epilogue, after `value_null`. -/
#ix_seg npl_epi {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s r v8 : BitVec 64}
    (h2 : R 2 = s + 18446744073709551568#64)
    (hs1 : 0x87800000 + 48 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : r.toNat % 4 = 0)
    (hra : ldv .ld M (s + 18446744073709551568#64 + 40#64).toNat = r)
    (hs0 : ldv .ld M (s + 18446744073709551568#64 + 32#64).toNat = v8) :
    IW live ∅ [] (nplF s) Q 0x80002fac#64 R M
  by
    ix_run hlive using [h2, hra, hs0, hal]

/-! ## The Iris glue -/

section Glue

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

omit I in
/-- `native_println`'s frame out of the stack below `s`: `native_print`'s
stack, its result slot, the rest. -/
theorem nplFrame_split {s : BitVec 64} (hs : 48 + nativePrintNeed ≤ s.toNat) :
    stackScratch (GF := GF) s nativePrintlnNeed ⊢
      stackScratch (s + 18446744073709551568#64) nativePrintNeed ∗
        slot24 (s + 18446744073709551568#64).toNat ∗ ownSet (InExt (s.toNat - 24, 24)) byteAny := by
  have h := stackScratch_frame (GF := GF) (s := s) (f := 48#64) (n := nativePrintlnNeed)
    (by unfold nativePrintlnNeed; omega) (by unfold nativePrintlnNeed; simp)
  have hsm : s - 48#64 = s + 18446744073709551568#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have e : (s + 18446744073709551568#64).toNat = s.toNat - 48 := by
    rw [BitVec.toNat_add]; simp; omega
  rw [hsm, show (48#64 : BitVec 64).toNat = 48 from rfl,
    show nativePrintlnNeed - 48 = nativePrintNeed by unfold nativePrintlnNeed; omega] at h
  refine h.trans ?_
  iintro ⟨Hst, Hb⟩
  ihave ⟨H1, H2⟩ := blockOwn_split _ 48 24 (s.toNat - 24) 24 (by omega) (by rw [e]; omega) rfl $$ Hb
  unfold slot24
  iframe Hst H1
  unfold blockOwn
  iexact H2

omit I in
/-- And back. -/
theorem nplFrame_join {s : BitVec 64} (hs : 48 + nativePrintNeed ≤ s.toNat) :
    stackScratch (GF := GF) (s + 18446744073709551568#64) nativePrintNeed ∗
        slot24 (s + 18446744073709551568#64).toNat ∗ ownSet (InExt (s.toNat - 24, 24)) byteAny ⊢
      stackScratch s nativePrintlnNeed := by
  have h := stackScratch_unframe (GF := GF) (s := s) (f := 48#64) (n := nativePrintlnNeed)
    (by unfold nativePrintlnNeed; omega) (by unfold nativePrintlnNeed; simp)
  have hsm : s - 48#64 = s + 18446744073709551568#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have e : (s + 18446744073709551568#64).toNat = s.toNat - 48 := by
    rw [BitVec.toNat_add]; simp; omega
  rw [hsm, show (48#64 : BitVec 64).toNat = 48 from rfl,
    show nativePrintlnNeed - 48 = nativePrintNeed by unfold nativePrintlnNeed; omega] at h
  refine .trans ?_ h
  iintro ⟨Hst, H1, H2⟩
  iframe Hst
  unfold slot24
  iapply blockOwn_join _ 24 (s.toNat - 24) 24 48 (by rw [e]; omega) rfl
  iframe H1
  unfold blockOwn
  iexact H2

/-- `native_println`'s return continuation (its `helperSpec` post). -/
abbrev NplK (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (sret args s r : BitVec 64) (vs : List Value) (st : Store) (o : String) (rv : Nat → BitVec 64) :
    IProp GF :=
  iprop(PC ↦ᵣ r -∗ ra ↦ᵣ r -∗
    (∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = rv x⌝ ∗
      (valAt N sret.toNat .null ∗ valsAt N args.toNat vs ∗ stdioOwn ∗
        consoleOwn (o ++ printArgs st vs ++ "\n") ∗ stackAt s nativePrintlnNeed)) -∗ Wp.W Φ)

/-- What `native_println` carries across its calls. -/
def FnplR (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (sret args s r : BitVec 64) (vs : List Value) (st : Store) (o : String) (rv : Nat → BitVec 64) :
    IProp GF :=
  iprop(slot24 sret.toNat ∗ valAt N (s + 18446744073709551568#64).toNat .null ∗
    valsAt N args.toNat vs ∗ stackScratch (s + 18446744073709551568#64) nativePrintNeed ∗
    NplK Wp Φ N sret args s r vs st o rv)

/-- The shared pure facts of a `native_println` run. -/
structure NplCtx (live : Nat → Prop) (sret s r : BitVec 64) (rv : Nat → BitVec 64) : Prop where
  hlive : ∀ p ∈ interpText, live p.1
  hal : r.toNat % 4 = 0
  h10 : rv 10 = sret
  h2 : rv 2 = s
  hs1 : 0x87800000 + nativePrintlnNeed ≤ s.toNat
  hs2 : s.toNat ≤ 0x88000000
  hs3 : s.toNat % 16 = 0
  hg : SlotGeom sret

/-- **After `native_print`**: `fputc('\n')`, `value_null`, the epilogue, the
return. -/
theorem npl_rest (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {sret args s r : BitVec 64} {vs : List Value} {st : Store} {o : String}
    {rv : Nat → BitVec 64} (c : NplCtx live sret s r rv) (hcl : CodeLive live) (H : OutHoles)
    {R : Nat → BitVec 64} {M : Mem}
    (hR8 : R 8 = sret) (hR2 : R 2 = s + 18446744073709551568#64)
    (hkeep : ∀ x ∈ fRegs, x ∉ callerSaved → x ≠ 2 → x ≠ 8 → R x = rv x)
    (hra : ldv .ld M (s + 18446744073709551568#64 + 40#64).toNat = r)
    (hs0 : ldv .ld M (s + 18446744073709551568#64 + 32#64).toNat = rv 8) :
    codeRes ∗ binImg ∗ ms 0x80002f94#64 R (nplF s) M ∗ slot24 sret.toNat ∗
      valAt N (s + 18446744073709551568#64).toNat .null ∗ valsAt N args.toNat vs ∗ stdioOwn ∗
      consoleOwn (o ++ printArgs st vs) ∗ stackScratch (s + 18446744073709551568#64) nativePrintNeed ∗
      NplK Wp Φ N sret args s r vs st o rv ⊢ Wp.W Φ := by
  iintro ⟨#Hcode, #Himg, Hms, Hsl, Hnull, Hvs, Hstd, Hcon, Hst, Hk⟩
  have hs1 := c.hs1; have hs2 := c.hs2; have hs3 := c.hs3
  unfold nativePrintlnNeed nativePrintNeed printNeed fprintfNeed at hs1
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have e48 : (s + 18446744073709551568#64).toNat = s.toNat - 48 := by
    rw [BitVec.toNat_add]; simp; omega
  -- `stdout`, to `jal fputc`
  ihave ⟨%img, %M1, %hok, Hms, Hio, %⟨hM1, hio, hd⟩⟩ := ms_ioOpen $$ [Hms Hstd]
  · iframe Hms Hstd
  have hio1 : ldv .ld M1 0x8001b970 = 0x8001b538#64 := by
    rw [ldv_ld_imgW]; unfold imgW
    rw [imgLE_congr (img' := img) (fun j hj => hio _ (by simp [ioW, InExt]; omega))]
    exact hok.impure
  have hio2 : ldv .ld M1 0x8001b548 = 0x8001bb20#64 := by
    rw [ldv_ld_imgW]; unfold imgW
    rw [imgLE_congr (img' := img) (fun j hj => hio _ (by simp [ioW, InExt]; omega))]
    exact StdioOK.stdout hok
  iapply wp_swpF Wp (S := nplS s) (R := R) (Mt := M1) (pc := 0x80002f94#64)
    (F := iprop(ownSet (fun k => stdioFoot k ∧ ¬ ioW k) (fun k => k ↦ₘ img k) ∗ codeRes ∗ binImg ∗
      consoleOwn (o ++ printArgs st vs) ∗ FnplR Wp Φ N sret args s r vs st o rv))
  rotate_left
  · rw [hro]; unfold FnplR; iframe Hcode Himg Hio Hcon Hsl Hnull Hvs Hst Hk Hms
  intro F'
  refine npl_mid c.hlive hio1 hio2 ?_
  apply swp_closeF
  dsimp only [F']
  iintro ⟨⟨Hio, #Hcode, #Himg, Hcon, Hrest⟩, Hms⟩
  ihave ⟨Hms, Hstd⟩ := ms_ioClose hok hd $$ [Hms Hio]
  · iframe Hms Hio
    ipureintro; exact hio
  -- `fputc('\n', stdout)`
  have hsg : StackGeom (s + 18446744073709551568#64) nativePrintNeed :=
    ⟨by rw [e48]; unfold nativePrintNeed printNeed fprintfNeed; omega,
      by rw [e48]; unfold Vsa.Sim.LayoutInstance.stackSL nativePrintNeed printNeed fprintfNeed; simp; omega,
      by rw [e48]; unfold Vsa.Sim.LayoutInstance.stackSL; simp; omega, by rw [e48]; omega⟩
  iapply ms_callOut Wp (i := 0x80002fa0)
    (jalx_80002fa0 live (fun p hp => c.hlive _ (interp_code_80002fa0 p hp))) interp_code_80002fa0
    (R := upd (upd (upd R 15 2147595576#64) 10 10#64) 11 2147597088#64)
    (S := nplF s) (Mt := M1) (n := nativePrintNeed)
    (fun cs => H.fputc live Wp (10#8) (s + 18446744073709551568#64) cs (o ++ printArgs st vs) hcl
      (spIn_of_stackGeom hsg (by decide)))
    (by simp) (fun j hj => by
      simp only [List.length_cons, List.length_nil] at hj
      rcases j with _ | _ | j
      · ix_reg; rfl
      · ix_reg; rfl
      · omega)
    (by ix_reg; exact hR2) (by rw [e48]; unfold nativePrintNeed printNeed fprintfNeed; omega)
    (by decide)
  unfold FnplR
  icases Hrest with ⟨Hsl, Hnull, Hvs, Hst, Hk⟩
  iframe Hcode Hms Hstd Hcon Hst Himg
  iintro %R4 %hk4 Hstd Hcon Hms Hst
  rw [show toString (Char.ofNat (10#8 : BitVec 8).toNat) = "\n" by decide]
  have k4 := fun x (hx : x ∈ fRegs) (hc : x ∉ callerSaved) => hk4 x hx hc
  -- to `jal value_null`
  iapply wp_swpF Wp (S := nplF s) (R := upd R4 1 (BitVec.ofNat 64 (0x80002fa0 + 4))) (Mt := M1)
    (pc := 0x80002fa4#64) (F := iprop(codeRes ∗ stdioOwn ∗ consoleOwn (o ++ printArgs st vs ++ "\n") ∗
      FnplR Wp Φ N sret args s r vs st o rv))
  rotate_left
  · rw [hro]; unfold FnplR; iframe Hcode Hstd Hcon Hsl Hnull Hvs Hst Hk Hms
  intro F'
  refine npl_null c.hlive ?_
  apply swp_closeF
  dsimp only [F']
  unfold FnplR
  iintro ⟨⟨#Hcode, Hstd, Hcon, Hsl, Hnull, Hvs, Hst, Hk⟩, Hms⟩
  -- `value_null(sret)`
  ihave #Hvn := valueNull_spec c.hlive Wp N sret
  unfold valueNullSpec
  iapply ms_callHelper Wp (i := 0x80002fa8)
    (jalx_80002fa8 live (fun p hp => c.hlive _ (interp_code_80002fa8 p hp))) interp_code_80002fa8
    (by decide) (clob := []) (pins := fun rv => rv 10 = sret)
    (Pre := iprop(slot24 sret.toNat ∗ ⌜SlotGeom sret⌝)) (Post := fun _ => valAt N sret.toNat .null)
    (R := upd (upd R4 1 (BitVec.ofNat 64 (0x80002fa0 + 4))) 10
      (upd R4 1 (BitVec.ofNat 64 (0x80002fa0 + 4)) 8))
  isplitl []
  · ipureintro; ix_reg; rw [k4 8 (by decide) (by decide)]; exact hR8
  isplitl []
  · iexact Hvn
  iframe Hcode Hms
  isplitl [Hsl]
  · iframe Hsl; ipureintro; exact c.hg
  iintro %R5 %hk5 Hnull2 Hms
  have k5 : ∀ x ∈ fRegs, R5 x = upd (upd R4 1 (BitVec.ofNat 64 (0x80002fa0 + 4))) 10
      (upd R4 1 (BitVec.ofNat 64 (0x80002fa0 + 4)) 8) x := fun x hx => hk5 x hx (by simp)
  -- the epilogue
  iapply wp_swpF Wp (S := nplF s) (pc := 0x80002fac#64) (R := upd R5 1 (BitVec.ofNat 64 (0x80002fa8 + 4)))
    (Mt := M1)
    (F := iprop(codeRes ∗ valAt N (s + 18446744073709551568#64).toNat .null ∗ valAt N sret.toNat .null ∗
      valsAt N args.toNat vs ∗ stdioOwn ∗ consoleOwn (o ++ printArgs st vs ++ "\n") ∗
      stackScratch (s + 18446744073709551568#64) nativePrintNeed ∗ NplK Wp Φ N sret args s r vs st o rv))
  rotate_left
  · rw [hro]; iframe Hcode Hnull Hnull2 Hvs Hstd Hcon Hst Hk Hms
  intro F'
  have sw : ∀ o, 24 ≤ o → o + 8 ≤ 48 →
      ldv .ld M1 (s + 18446744073709551568#64 + BitVec.ofNat 64 o).toNat =
        ldv .ld M (s + 18446744073709551568#64 + BitVec.ofNat 64 o).toNat := fun o h1 h2 => by
    have e : (s + 18446744073709551568#64 + BitVec.ofNat 64 o).toNat = s.toNat - 48 + o := by
      rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
    rw [e]
    exact ldv_agree fun j hj => hM1 _ (by simp only [nplF, InExt]; omega)
  have hra1 : ldv .ld M1 (s + 18446744073709551568#64 + 40#64).toNat = r := by
    rw [sw 40 (by omega) (by omega)]; exact hra
  have hs01 : ldv .ld M1 (s + 18446744073709551568#64 + 32#64).toNat = rv 8 := by
    rw [sw 32 (by omega) (by omega)]; exact hs0
  refine npl_epi c.hlive (by ix_reg; rw [k5 2 (by decide)]; ix_reg; rw [k4 2 (by decide) (by decide)]; exact hR2)
    (by omega) hs2 hs3 c.hal hra1 hs01 ?_
  apply swp_closeF
  dsimp only [F']
  iintro ⟨⟨-, Hnull, Hnull2, Hvs, Hstd, Hcon, Hst, Hk⟩, Hms⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave Hslot := valAt_slot $$ Hnull
  ihave Hst := nplFrame_join (s := s) (by unfold nativePrintNeed printNeed fprintfNeed; omega)
    $$ [Hst Hslot HS]
  · iframe Hst Hslot HS
  ihave Hra := ptsto_eq (show _ = r by ix_reg) $$ Hra
  iapply Hk $$ Hpc Hra
  iexists _
  iframe Hregs Hnull2 Hvs Hstd Hcon
  isplitr
  · ipureintro
    intro x hx hc
    have h1 : x ≠ 1 := fun e => by subst e; revert hx; decide
    have h10 : x ≠ 10 := fun e => by subst e; exact hc (by decide)
    have h11 : x ≠ 11 := fun e => by subst e; exact hc (by decide)
    have h15 : x ≠ 15 := fun e => by subst e; exact hc (by decide)
    by_cases h2 : x = 2
    · subst h2; ix_reg
      rw [BitVec.add_assoc, show (18446744073709551568#64 : BitVec 64) + 48#64 = 0#64 by decide,
        BitVec.add_zero, c.h2]
    · by_cases h8 : x = 8
      · subst h8; ix_reg
      · simp only [upd, h1, h10, h2, h8, ite_false]
        rw [k5 x hx]
        simp only [upd, h1, h10, ite_false]
        rw [k4 x hx hc]
        simp only [upd, h10, h11, h15, ite_false]
        exact hkeep x hx hc h2 h8
  · unfold stackAt
    iframe Hst
    ipureintro
    exact ⟨by unfold nativePrintlnNeed nativePrintNeed printNeed fprintfNeed; omega,
      by unfold Vsa.Sim.LayoutInstance.stackSL; simp
         unfold nativePrintlnNeed nativePrintNeed printNeed fprintfNeed; omega,
      by unfold Vsa.Sim.LayoutInstance.stackSL; simp; omega, hs3⟩

/-- `native_print`'s stack and result slot, from `native_println`'s stack. -/
theorem npl_geom {s : BitVec 64} (h : StackGeom s nativePrintlnNeed) :
    StackGeom (s + 18446744073709551568#64) nativePrintNeed ∧ SlotGeom (s + 18446744073709551568#64) := by
  have hs1 := h.le; have hs2 := h.lo; have hs3 := h.hi; have hs4 := h.al
  simp only [Vsa.Sim.LayoutInstance.stackSL] at hs2 hs3
  unfold nativePrintlnNeed nativePrintNeed printNeed fprintfNeed at hs1 hs2
  have e48 : (s + 18446744073709551568#64).toNat = s.toNat - 48 := by
    rw [BitVec.toNat_add]; simp; omega
  have a1 : nativePrintNeed ≤ s.toNat - 48 := by unfold nativePrintNeed printNeed fprintfNeed; omega
  have a2 : 0x87800000 ≤ s.toNat - 48 - nativePrintNeed := by
    unfold nativePrintNeed printNeed fprintfNeed; rw [Nat.sub_sub]; exact hs2
  have a3 : s.toNat - 48 ≤ 0x88000000 := by omega
  have a4 : (s.toNat - 48) % 16 = 0 := by omega
  have a5 : (s.toNat - 48) % 8 = 0 := by omega
  have a6 : 0x8001ad00 + 16 ≤ s.toNat - 48 := by omega
  have a7 : s.toNat - 48 + 24 ≤ 0x100000000 := by omega
  rw [← e48] at a1 a2 a3 a4 a5 a6 a7
  exact ⟨⟨a1, a2, a3, a4⟩, ⟨a5, a6, a7⟩⟩

/-- **`native_println`**, given `IrisHoles.out`, for either WP. -/
theorem nativePrintln_spec (hlive : ∀ q ∈ interpText, live q.1) (hcl : CodeLive live)
    (H : OutHoles) (Wp : MachWP (GF := GF) (vsaModel live)) (N : NativeAddrs)
    (sret args s : BitVec 64) (vs : List Value) (st : Store) (o : String) :
    ⊢ nativePrintlnSpec (vsaModel live) N Wp sret args s vs st o := by
  unfold nativePrintlnSpec helperSpec fnSpecW
  iintro %rv !> %r %Φ Hpc Hra ⟨%hal, Hregs, %⟨h10, h12, h13, h2⟩, #Hcode, Hsl, %⟨hg, ha, hn⟩, Hvs,
    #Hd, #Himg, Hstd, Hcon, ⟨Hst, %hsg⟩⟩ Hk
  have hs1 := hsg.le; have hs2 := hsg.lo; have hs3 := hsg.hi; have hs4 := hsg.al
  simp only [Vsa.Sim.LayoutInstance.stackSL] at hs2 hs3
  unfold nativePrintlnNeed nativePrintNeed printNeed fprintfNeed at hs1 hs2
  have c : NplCtx live sret s r rv :=
    ⟨hlive, hal, h10, h2, by unfold nativePrintlnNeed nativePrintNeed printNeed fprintfNeed; omega,
      by omega, hs4, hg⟩
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have e48 : (s + 18446744073709551568#64).toNat = s.toNat - 48 := by
    rw [BitVec.toNat_add]; simp; omega
  ihave ⟨Hst, Hslot, HF⟩ := nplFrame_split (s := s)
    (by unfold nativePrintNeed printNeed fprintfNeed; omega) $$ Hst
  ihave ⟨%M, Hms⟩ := ms_intro $$ [Hpc Hra Hregs HF]
  · iframe Hpc Hra Hregs HF
  -- the prologue
  iapply wp_swpF Wp (S := nplF s) (R := upd rv 1 r) (Mt := M) (pc := nativePrintlnPC)
    (F := iprop(codeRes ∗ dispResL st vs ∗ binImg ∗ slot24 sret.toNat ∗ slot24 (s + 18446744073709551568#64).toNat ∗
      valsAt N args.toNat vs ∗ stdioOwn ∗ consoleOwn o ∗
      stackScratch (s + 18446744073709551568#64) nativePrintNeed ∗ NplK Wp Φ N sret args s r vs st o rv))
  rotate_left
  · rw [hro]; iframe Hcode Hd Himg Hsl Hslot Hvs Hstd Hcon Hst Hk Hms
  intro F'
  refine npl_pro hlive h2 (by omega) (by omega) hs4 ?_
  apply swp_closeF
  dsimp only [F']
  iintro ⟨⟨#Hcode, #Hd, #Himg, Hsl, Hslot, Hvs, Hstd, Hcon, Hst, Hk⟩, Hms⟩
  -- `native_print(sp, …)`
  obtain ⟨hsg', hgs⟩ := npl_geom hsg
  ihave #Hnp := nativePrint_spec hlive hcl H Wp N (s + 18446744073709551568#64) args
    (s + 18446744073709551568#64) vs st o
  unfold nativePrintSpec
  iapply ms_callHelper Wp (i := 0x80002f90)
    (jalx_80002f90 live (fun p hp => hlive _ (interp_code_80002f90 p hp))) interp_code_80002f90
    (by decide)
    (R := upd (upd (upd (upd rv 1 r) 2 (s + 18446744073709551568#64)) 8 (rv 10)) 10
      (s + 18446744073709551568#64)) (clob := callerSaved)
    (pins := fun rv => rv 10 = s + 18446744073709551568#64 ∧ rv 12 = BitVec.ofNat 64 vs.length ∧
      rv 13 = args ∧ rv 2 = s + 18446744073709551568#64)
    (Pre := iprop(slot24 (s + 18446744073709551568#64).toNat ∗
      ⌜SlotGeom (s + 18446744073709551568#64) ∧ ArgsGeom args vs.length ∧ vs.length < 2 ^ 31⌝ ∗
      valsAt N args.toNat vs ∗ dispResL st vs ∗ binImg ∗ stdioOwn ∗ consoleOwn o ∗
      stackAt (s + 18446744073709551568#64) nativePrintNeed))
    (Post := fun _ => iprop(valAt N (s + 18446744073709551568#64).toNat .null ∗ valsAt N args.toNat vs ∗
      stdioOwn ∗ consoleOwn (o ++ printArgs st vs) ∗ stackAt (s + 18446744073709551568#64) nativePrintNeed))
  isplitl []
  · ipureintro
    refine ⟨by ix_reg, ?_, ?_, by ix_reg⟩
    · ix_reg; exact h12
    · ix_reg; exact h13
  isplitl []
  · iexact Hnp
  iframe Hcode Hms
  isplitl [Hslot Hvs Hstd Hcon Hst]
  · unfold stackAt
    iframe Hslot Hvs Hstd Hcon Hst Hd Himg
    isplitl []
    · ipureintro; exact ⟨hgs, ha, hn⟩
    · ipureintro; exact hsg'
  iintro %R' %hk' ⟨Hnull, Hvs, Hstd, Hcon, Hst, -⟩ Hms
  iapply npl_rest Wp c hcl H ?h8 ?h2 ?hkeep (R := upd R' 1 (BitVec.ofNat 64 (0x80002f90 + 4))) (M := writeLog (writeLog M
      [((s + 18446744073709551568#64 + 32#64).toNat, 8, rv 8)])
      [((s + 18446744073709551568#64 + 40#64).toNat, 8, r)]) ?hra ?hs0
  case h8 => ix_reg; rw [hk' 8 (by decide) (by decide)]; ix_reg; exact h10
  case h2 => ix_reg; rw [hk' 2 (by decide) (by decide)]; ix_reg
  case hkeep =>
    intro x hx hc hx2 hx8
    have hx1 : x ≠ 1 := fun e => by subst e; revert hx; decide
    have hx10 : x ≠ 10 := fun e => by subst e; exact hc (by decide)
    simp only [upd, hx1, ite_false]
    rw [hk' x hx hc]
    simp only [upd, hx1, hx2, hx8, hx10, ite_false]
  case hra =>
    rw [ldv_store_hit]
  case hs0 =>
    have e32 : (s + 18446744073709551568#64 + 32#64).toNat = s.toNat - 48 + 32 := by
      rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
    have e40 : (s + 18446744073709551568#64 + 40#64).toNat = s.toNat - 48 + 40 := by
      rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
    rw [e32, e40, ldv_store_miss _ _ _ (by simp only [widthOfM]; omega), ldv_store_hit]
  iframe Hcode Himg Hms Hsl Hnull Hvs Hstd Hcon Hst Hk

end Glue

end VsaIris.Interp
