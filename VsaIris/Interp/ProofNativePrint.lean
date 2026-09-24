import VsaIris.Interp.ProofValuePrint
import VsaIris.Vsa.StdioRead

/-!
# `native_print` and `native_println` (lane H2)

`native_print(sret, in, argc, args, line)` copies each argument into its
frame, prints it with `value_print`, prints `' '` between arguments with
`fputc`, and returns `null` (`value_null`). The loop is a Lean induction over
the arguments left, each iteration two runs and two calls.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib VsaIris.Stdio
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- `_impure_data._stdout` holds `&__sf[1]`. -/
theorem StdioOK.stdout {img : Nat → BitVec 8} (h : StdioOK img) :
    imgW img (consoleReent + 16) = BitVec.ofNat 64 consoleStdout :=
  StdioOK.word h.facts.1.stdout (dataList_range (by decide) (by decide))

/-- The two words of newlib's data `native_print` reads: `_impure_ptr` and
`_impure_data._stdout`. -/
abbrev ioW (k : Nat) : Prop := InExt (0x8001b970, 8) k ∨ InExt (0x8001b548, 8) k

/-- The bytes `native_print` owns across its calls: its frame and the
arguments. -/
abbrev npF (s args : BitVec 64) (n : Nat) (k : Nat) : Prop :=
  InExt (s.toNat - 80, 80) k ∨ InExt (args.toNat, 24 * n) k

/-- A run's bytes: those and the two words of newlib's data. -/
abbrev npS (s args : BitVec 64) (n : Nat) (k : Nat) : Prop := npF s args n k ∨ ioW k

macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; simp only [mem_accAddrs_iff, npS, npF, ioW, VsaIris.InExt] at *; sx_addr))

section Vals

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- The meanings of `n` consecutive values in an image, persistent. -/
def valsImg (N : NativeAddrs) (f : Nat → BitVec 8) : Nat → List Value → IProp GF
  | _, [] => iprop(emp)
  | a, v :: vs => iprop(valImg N f a v ∗ valsImg N f (a + 24) vs)

instance (N : NativeAddrs) (f : Nat → BitVec 8) (a : Nat) (vs : List Value) :
    Persistent (valsImg (GF := GF) N f a vs) := by
  induction vs generalizing a with
  | nil => unfold valsImg; infer_instance
  | cons v vs ih => unfold valsImg; infer_instance

theorem valsImg_cons (N : NativeAddrs) (f : Nat → BitVec 8) (a : Nat) (v : Value) (vs : List Value) :
    valsImg (GF := GF) N f a (v :: vs) = iprop(valImg N f a v ∗ valsImg N f (a + 24) vs) := rfl

theorem valsAt_cons (N : NativeAddrs) (a : Nat) (v : Value) (vs : List Value) :
    valsAt (GF := GF) N a (v :: vs) ⊣⊢ iprop(valAt N a v ∗ valsAt N (a + 24) vs) := by
  unfold valsAt
  rw [List.zipIdx_cons, sepL_cons, List.zipIdx_succ, sepL_map]
  refine sep_congr (by simp) ?_
  exact .of_eq (sepL_congr fun p _ => by
    rcases p with ⟨x, i⟩
    simp only
    congr 1
    omega)

theorem valsImg_agree (N : NativeAddrs) {f g : Nat → BitVec 8} :
    ∀ (vs : List Value) (a : Nat), (∀ k, InExt (a, 24 * vs.length) k → f k = g k) →
      valsImg (GF := GF) N f a vs ⊢ valsImg N g a vs
  | [], _, _ => .rfl
  | v :: vs, a, h => by
    have e := valImg_agree (GF := GF) (N := N) (v := v) (g := g) (a := a)
      (fun k hk => h k (by simp only [InExt, List.length_cons] at hk ⊢; omega))
    have ih := valsImg_agree N vs (a + 24)
      (fun k hk => h k (by simp only [InExt, List.length_cons] at hk ⊢; omega))
    show iprop(valImg N f a v ∗ valsImg N f (a + 24) vs) ⊢ iprop(valImg N g a v ∗ valsImg N g (a + 24) vs)
    rw [e]
    exact sep_mono .rfl ih

omit I in
theorem ownSet_inExt_nil (a : Nat) (Φ : Nat → IProp GF) : ⊢ ownSet (InExt (a, 0)) Φ := by
  unfold ownSet
  iexists []
  isplitr
  · ipureintro; exact ⟨List.nodup_nil, fun k => by simp [InExt]⟩
  · simp only [sepL_nil]; iempintro

/-- **Values at one tracking memory**: their bytes and their meanings. -/
theorem valsAt_tracked (N : NativeAddrs) :
    ∀ (vs : List Value) (a : Nat), valsAt (GF := GF) N a vs ⊢
      ∃ M : Mem, ownSet (InExt (a, 24 * vs.length)) (fun k => k ↦ₘ imgM M k) ∗
        valsImg N (imgM M) a vs
  | [], a => by
    iintro -
    iexists ∅
    isplitl
    · iapply ownSet_inExt_nil
    · show ⊢ iprop(emp); iempintro
  | v :: vs, a => by
    simp only [valsImg_cons]
    iintro H
    ihave ⟨H1, H2⟩ := (valsAt_cons N a v vs).1 $$ H
    ihave ⟨%M1, HA, #Hv⟩ := valAt_tracked N a v $$ H1
    ihave ⟨%M2, HB, #Hvs⟩ := valsAt_tracked N vs (a + 24) $$ H2
    ihave ⟨%M, H, %⟨hA, hB, _⟩⟩ := ownSet_join_tracked _ _ M1 M2 $$ [HA HB]
    · iframe HA HB
    have e := valImg_agree (GF := GF) (N := N) (v := v) (a := a) (fun k hk => (hA k hk).symm)
    ihave #Hvs' := valsImg_agree N vs (a + 24) (fun k hk => (hB k hk).symm) $$ Hvs
    iexists M
    isplitl
    · iapply ownSet_iff _ (fun k => ⟨fun hk => by simp only [InExt, List.length_cons] at hk ⊢; omega,
        fun hk => by simp only [InExt, List.length_cons] at hk ⊢; omega⟩) $$ H
    rw [← e]
    iframe Hv Hvs'

/-- And back. -/
theorem valsAt_of_tracked (N : NativeAddrs) (M : Mem) :
    ∀ (vs : List Value) (a : Nat),
      ownSet (GF := GF) (InExt (a, 24 * vs.length)) (fun k => k ↦ₘ imgM M k) ∗
        valsImg N (imgM M) a vs ⊢ valsAt N a vs
  | [], a => by
    iintro -
    unfold valsAt; simp only [List.zipIdx_nil, sepL_nil]; iempintro
  | v :: vs, a => by
    refine .trans ?_ (valsAt_cons N a v vs).2
    show iprop(ownSet (InExt (a, 24 * (vs.length + 1))) (fun k => k ↦ₘ imgM M k) ∗
      (valImg N (imgM M) a v ∗ valsImg N (imgM M) (a + 24) vs)) ⊢ _
    iintro ⟨H, #H1, #H2⟩
    ihave ⟨HA, HB⟩ := ownSet_split _ (InExt (a, 24)) _ $$ H
    isplitl [HA]
    · iapply valAt_of_img
      iframe H1
      iapply ownSet_iff _ (fun k => ⟨fun hk => hk.2,
        fun hk => ⟨by simp only [InExt] at hk ⊢; omega, hk⟩⟩) $$ HA
    · iapply valsAt_of_tracked N M vs (a + 24)
      iframe H2
      iapply ownSet_iff _ (fun k => ⟨fun hk => by simp only [InExt] at hk ⊢; omega,
        fun hk => ⟨by simp only [InExt] at hk ⊢; omega, by simp only [InExt] at hk ⊢; omega⟩⟩) $$ HB

/-- One value's meaning out of the list's. -/
theorem valsImg_get (N : NativeAddrs) (f : Nat → BitVec 8) :
    ∀ (vs : List Value) (a i : Nat) (h : i < vs.length),
      valsImg (GF := GF) N f a vs ⊢ valImg N f (a + 24 * i) vs[i]
  | v :: vs, a, 0, _ => by
    show iprop(valImg N f a v ∗ valsImg N f (a + 24) vs) ⊢ _
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
    iintro ⟨H, -⟩; iexact H
  | v :: vs, a, i + 1, h => by
    show iprop(valImg N f a v ∗ valsImg N f (a + 24) vs) ⊢ _
    iintro ⟨-, H⟩
    have := valsImg_get N f vs (a + 24) i (by simp at h; omega)
    rw [show a + 24 * (i + 1) = a + 24 + 24 * i by omega, List.getElem_cons_succ]
    iapply this $$ H

/-- `ioW` is inside newlib's data. -/
theorem ioW_stdio {k : Nat} (h : ioW k) : stdioFoot k := by
  simp only [ioW, InExt] at h; unfold stdioFoot InRange; omega

omit I in
/-- **Open the two words of newlib's data into a run's owned bytes.** -/
theorem ms_ioOpen {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop} {M : Mem} :
    ms (GF := GF) pc R S M ∗ stdioOwn ⊢
      ∃ (img : Nat → BitVec 8) (M' : Mem), ⌜StdioOK img⌝ ∗
        ms pc R (fun k => S k ∨ ioW k) M' ∗
        ownSet (fun k => stdioFoot k ∧ ¬ ioW k) (fun k => k ↦ₘ img k) ∗
        ⌜(∀ k, S k → imgM M' k = imgM M k) ∧ (∀ k, ioW k → imgM M' k = img k) ∧
          ∀ k, S k → ¬ ioW k⌝ := by
  iintro ⟨Hms, Hio⟩
  ihave ⟨%img, %hok, H1, H2⟩ := stdioAt_open StdioOK ioW $$ Hio
  ihave H1 := ownSet_iff _ (fun k => ⟨fun h => h.2, fun h => ⟨ioW_stdio h, h⟩⟩) $$ H1
  ihave ⟨%Mi, H1, %hMi⟩ := ownSet_trackedAt _ img $$ H1
  ihave ⟨%M', Hms, %⟨h1, h2, h3⟩⟩ := ms_join $$ [Hms H1]
  · iframe Hms H1
  iexists img, M'
  iframe Hms H2
  ipureintro
  exact ⟨hok, h1, fun k hk => (h2 k hk).trans (hMi k hk), h3⟩

omit I in
/-- **Close them again**, unchanged by the run. -/
theorem ms_ioClose {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop} {M : Mem}
    {img : Nat → BitVec 8} (hok : StdioOK img) (hd : ∀ k, S k → ¬ ioW k)
    (hio : ∀ k, ioW k → imgM M k = img k) :
    ms (GF := GF) pc R (fun k => S k ∨ ioW k) M ∗
        ownSet (fun k => stdioFoot k ∧ ¬ ioW k) (fun k => k ↦ₘ img k) ⊢
      ms pc R S M ∗ stdioOwn := by
  iintro ⟨Hms, H2⟩
  ihave ⟨Hms, H1⟩ := ms_split hd $$ Hms
  iframe Hms
  iapply stdioAt_close StdioOK ioW img hok
  iframe H2
  ihave H1 := ownSet_congr (Ψ := fun k => iprop(k ↦ₘ img k)) (fun k hk => by rw [hio k hk]) $$ H1
  iapply ownSet_iff _ (fun k => ⟨fun h => ⟨ioW_stdio h, h⟩, fun h => h.2⟩) $$ H1

end Vals

/-! ## The runs (`#ix_seg`: each run a lemma ending at its computed state) -/

/- The prologue, one or more arguments: to the loop head. -/
#ix_seg np_pro {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {rv : Nat → BitVec 64}
    {s args sret r : BitVec 64} {n : Nat}
    (h10 : rv 10 = sret) (h12 : rv 12 = BitVec.ofNat 64 n) (h13 : rv 13 = args) (h2 : rv 2 = s)
    (hs1 : 0x87800000 + 80 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hn : 0 < n) (hn2 : n < 2 ^ 31) :
    IW live ∅ [] (npF s args n) Q nativePrintPC (upd rv 1 r) M
  by
    have hsf : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
      rw [BitVec.toNat_add]; simp; omega
    have hnI : (BitVec.ofNat 64 n).toInt = (n : Int) := by
      rw [BitVec.toInt_eq_toNat_cond]; simp; omega
    have h0I : (0#64 : BitVec 64).toInt = 0 := by decide
    unfold nativePrintPC
    ix_run hlive using [h10, h12, h13, h2, hsf, hnI, h0I] at 0x80002f1c
    all_goals first
      | (intro hc; exfalso
         simp only [upd_apply, Nat.reduceEqDiff, ite_false, h12, hnI, h0I] at hc; omega)
      | (intro _; ix_run hlive using [h10, h12, h13, h2, hsf] at 0x80002f1c)

/- The prologue, no arguments: to `jal value_null`. -/
#ix_seg np_pro0 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {rv : Nat → BitVec 64}
    {s args sret r : BitVec 64} {n : Nat}
    (h10 : rv 10 = sret) (h12 : rv 12 = BitVec.ofNat 64 n) (h13 : rv 13 = args) (h2 : rv 2 = s)
    (hs1 : 0x87800000 + 80 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hn : n = 0) :
    IW live ∅ [] (npF s args n) Q nativePrintPC (upd rv 1 r) M
  by
    subst hn
    have hsf : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
      rw [BitVec.toNat_add]; simp; omega
    unfold nativePrintPC
    ix_run hlive using [h10, h12, h13, h2, hsf] at 0x80002f64

/- The loop body: copy argument `i`, `jal value_print`. -/
#ix_seg np_body {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s args : BitVec 64} {n i : Nat} {w0 w1 w2 : BitVec 64}
    (h8 : R 8 = args + BitVec.ofNat 64 (24 * i)) (h9 : R 9 = BitVec.ofNat 64 i)
    (h18 : R 18 = 0x8001b970#64) (h2 : R 2 = s + 18446744073709551536#64)
    (hs1 : 0x87800000 + 80 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (ha1 : args.toNat % 8 = 0) (ha2 : tohostAddr + 16 ≤ args.toNat)
    (ha3 : args.toNat + 24 * n ≤ 0x100000000) (hi : i < n)
    (ea : (args + BitVec.ofNat 64 (24 * i)).toNat = args.toNat + 24 * i)
    (hw0 : ldv .ld M (args.toNat + 24 * i) = w0)
    (hw1 : ldv .ld M (args + BitVec.ofNat 64 (24 * i) + 8#64).toNat = w1)
    (hw2 : ldv .ld M (args + BitVec.ofNat 64 (24 * i) + 16#64).toNat = w2)
    (hio1 : ldv .ld M 0x8001b970 = 0x8001b538#64) (hio2 : ldv .ld M 0x8001b548 = 0x8001bb20#64) :
    IW live ∅ [] (npS s args n) Q 0x80002f1c#64 R M
  by
    have hsf : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
      rw [BitVec.toNat_add]; simp; omega
    ix_run hlive using [h8, h9, h18, h2, hsf, ea, hw0, hw1, hw2, hio1, hio2] at 0x80002f44

/- After `value_print`, more arguments: `jal fputc` with `' '`. -/
#ix_seg np_more {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s args : BitVec 64} {n i : Nat}
    (h8 : R 8 = args + BitVec.ofNat 64 (24 * i)) (h9 : R 9 = BitVec.ofNat 64 (i + 1))
    (h18 : R 18 = 0x8001b970#64) (h19 : R 19 = BitVec.ofNat 64 n)
    (hne : BitVec.ofNat 64 n ≠ BitVec.ofNat 64 (i + 1))
    (hio1 : ldv .ld M 0x8001b970 = 0x8001b538#64) (hio2 : ldv .ld M 0x8001b548 = 0x8001bb20#64) :
    IW live ∅ [] (npS s args n) Q 0x80002f48#64 R M
  by
    ix_run hlive using [h8, h9, h18, h19, hio1, hio2] at 0x80002f18
    all_goals first
      | (intro hc; exfalso; apply hc; ix_reg; rw [h19, h9]; exact hne)
      | (intro _; ix_run hlive using [h8, h9, h18, h19, hio1, hio2] at 0x80002f18)

/- After the last `value_print`: restore `s0`-`s3`, `jal value_null`. -/
#ix_seg np_last {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s args : BitVec 64} {n : Nat} {v8 v9 v18 v19 : BitVec 64}
    (h9 : R 9 = BitVec.ofNat 64 n) (h19 : R 19 = BitVec.ofNat 64 n)
    (h2 : R 2 = s + 18446744073709551536#64)
    (hs1 : 0x87800000 + 80 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hl8 : ldv .ld M (s + 18446744073709551536#64 + 64#64).toNat = v8)
    (hl9 : ldv .ld M (s + 18446744073709551536#64 + 56#64).toNat = v9)
    (hl18 : ldv .ld M (s + 18446744073709551536#64 + 48#64).toNat = v18)
    (hl19 : ldv .ld M (s + 18446744073709551536#64 + 40#64).toNat = v19) :
    IW live ∅ [] (npS s args n) Q 0x80002f48#64 R M
  by
    ix_run hlive using [h9, h19, h2, hl8, hl9, hl18, hl19] at 0x80002f64
    all_goals first
      | (intro hc; exfalso; apply hc; ix_reg; rw [h19, h9]; done)
      | (intro _; ix_run hlive using [h9, h19, h2, hl8, hl9, hl18, hl19] at 0x80002f64)

/- The epilogue, after `value_null`. -/
#ix_seg np_epi {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R : Nat → BitVec 64}
    {s args r v20 : BitVec 64} {n : Nat}
    (h2 : R 2 = s + 18446744073709551536#64)
    (hs1 : 0x87800000 + 80 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : r.toNat % 4 = 0)
    (hra : ldv .ld M (s + 18446744073709551536#64 + 72#64).toNat = r)
    (hs4 : ldv .ld M (s + 18446744073709551536#64 + 32#64).toNat = v20) :
    IW live ∅ [] (npF s args n) Q 0x80002f68#64 R M
  by
    ix_run hlive using [h2, hra, hs4, hal]

end VsaIris.Interp
