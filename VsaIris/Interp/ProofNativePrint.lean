import VsaIris.Interp.ProofValuePrint
import VsaIris.Interp.ProofValueCons
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
    have e := valImg_agreeOn (GF := GF) (N := N) (v := v) (g := g) (a := a)
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
    have e := valImg_agreeOn (GF := GF) (N := N) (v := v) (a := a) (fun k hk => (hA k hk).symm)
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
    {img : Nat → BitVec 8} (hok : StdioOK img) (hd : ∀ k, S k → ¬ ioW k) :
    ms (GF := GF) pc R (fun k => S k ∨ ioW k) M ∗
        ownSet (fun k => stdioFoot k ∧ ¬ ioW k) (fun k => k ↦ₘ img k) ∗
        ⌜∀ k, ioW k → imgM M k = img k⌝ ⊢
      ms pc R S M ∗ stdioOwn := by
  iintro ⟨Hms, H2, %hio⟩
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
    ix_run1 hlive using [h10, h12, h13, h2, hsf, hnI, h0I] at 0x80002f1c
    all_goals first
      | (intro hc; exfalso
         simp only [upd_apply, Nat.reduceEqDiff, ite_false, h12, hnI, h0I] at hc; omega)
      | (intro _; ix_run1 hlive using [h10, h12, h13, h2, hsf] at 0x80002f1c)

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
    ix_run1 hlive using [h10, h12, h13, h2, hsf] at 0x80002f64

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
    ix_run1 hlive using [h8, h9, h18, h2, hsf, ea, hw0, hw1, hw2, hio1, hio2] at 0x80002f44

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
    ix_run1 hlive using [h8, h9, h18, h19, hio1, hio2] at 0x80002f18
    all_goals first
      | (intro hc; exfalso; apply hc; ix_reg; rw [h19, h9]; exact hne)
      | (intro _; ix_run1 hlive using [h8, h9, h18, h19, hio1, hio2] at 0x80002f18)

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
    IW live ∅ [] (npF s args n) Q 0x80002f48#64 R M
  by
    ix_run1 hlive using [h9, h19, h2, hl8, hl9, hl18, hl19] at 0x80002f64
    all_goals first
      | (intro hc; exfalso; apply hc; ix_reg; rw [h19, h9]; done)
      | (intro _; ix_run1 hlive using [h9, h19, h2, hl8, hl9, hl18, hl19] at 0x80002f64)

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
    ix_run1 hlive using [h2, hra, hs4, hal]

/-! ## What the loop prints -/

/-- What `native_print` has printed at the head of iteration `i`: the first
`i` arguments and, after the first, the separator. -/
def npOut (st : Store) (vs : List Value) (i : Nat) : String :=
  if i = 0 then "" else printArgs st (vs.take i) ++ " "

theorem intercalate_snoc (a : String) (l : List String) (x : String) :
    String.intercalate " " (a :: (l ++ [x])) = String.intercalate " " (a :: l) ++ " " ++ x := by
  induction l generalizing a with
  | nil => simp [String.intercalate_cons_cons, String.intercalate_singleton]
  | cons b l ih =>
    rw [List.cons_append, String.intercalate_cons_cons, ih, String.intercalate_cons_cons]
    simp [String.append_assoc]

theorem npOut_step (st : Store) (vs : List Value) (i : Nat) (h : i < vs.length) :
    npOut st vs i ++ (vs[i]).display st = printArgs st (vs.take (i + 1)) := by
  unfold npOut printArgs
  rw [List.take_succ_eq_append_getElem h, List.map_append]
  by_cases h0 : i = 0
  · subst h0; simp
  · simp only [h0, ite_false, List.map_cons, List.map_nil]
    obtain ⟨a, l, hal⟩ : ∃ a l, List.map (Value.display st) (List.take i vs) = a :: l := by
      cases e : List.map (Value.display st) (List.take i vs) with
      | nil =>
        have := congrArg List.length e
        rw [List.length_map, List.length_take, List.length_nil] at this
        have hm : min i vs.length = i := Nat.min_eq_left (by omega)
        omega
      | cons a l => exact ⟨a, l, rfl⟩
    rw [hal, List.cons_append, intercalate_snoc]

theorem npOut_succ (st : Store) (vs : List Value) (i : Nat) (h : i < vs.length) :
    npOut st vs i ++ (vs[i]).display st ++ " " = npOut st vs (i + 1) := by
  rw [npOut_step st vs i h]; unfold npOut; simp

theorem npOut_last (st : Store) (vs : List Value) (i : Nat) (h : i + 1 = vs.length) :
    npOut st vs i ++ (vs[i]'(by omega)).display st = printArgs st vs := by
  rw [npOut_step st vs i (by omega), h, List.take_length]

/-! ## Words through stores -/

theorem imgW_store_hit (Mt : Mem) (a : Nat) (w : BitVec 64) :
    imgW (imgM (writeLog Mt [(a, 8, w)])) a = w := by
  unfold imgW; rw [imgLE_imgM_store]; simp

theorem imgW_store_miss (Mt : Mem) {a b wd : Nat} (v : BitVec 64) (h : a + 8 ≤ b ∨ b + wd ≤ a) :
    imgW (imgM (writeLog Mt [(b, wd, v)])) a = imgW (imgM Mt) a := by
  unfold imgW; rw [imgLE_store_miss _ _ h]

theorem ldv_agree {M M' : Mem} {a : Nat} (h : ∀ j, j < 8 → imgM M (a + j) = imgM M' (a + j)) :
    ldv .ld M a = ldv .ld M' a := by
  rw [ldv_ld_imgW, ldv_ld_imgW, imgW_agree h]

/-- `addiw s1,s1,1` on a small count. -/
theorem sx32_succ (i : Nat) (h : i + 1 < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 i + 1#64)) = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 64 i + 1#64).toNat = i + 1 := by simp; omega
  have he : (BitVec.extractLsb 31 0 (BitVec.ofNat 64 i + 1#64)).toNat = i + 1 := by
    rw [BitVec.extractLsb_toNat, h1]; simp; omega
  have hm : (BitVec.extractLsb 31 0 (BitVec.ofNat 64 i + 1#64)).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, he]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth, he]
  simp

/-! ## The Iris glue -/

section Glue

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- `native_print`'s return continuation (its `helperSpec` post). -/
abbrev NpK (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (sret args s r : BitVec 64) (vs : List Value) (st : Store) (o : String) (rv : Nat → BitVec 64) :
    IProp GF :=
  iprop(PC ↦ᵣ r -∗ ra ↦ᵣ r -∗
    (∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = rv x⌝ ∗
      (valAt N sret.toNat .null ∗ valsAt N args.toNat vs ∗ stdioOwn ∗
        consoleOwn (o ++ printArgs st vs) ∗ stackAt s nativePrintNeed)) -∗ Wp.W Φ)

/-- The frame of the epilogue run. -/
def FnpE (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (sret args s r : BitVec 64) (vs : List Value) (st : Store) (o : String) (rv : Nat → BitVec 64)
    (Margs : Mem) : IProp GF :=
  iprop(valsImg N (imgM Margs) args.toNat vs ∗ valAt N sret.toNat .null ∗ stdioOwn ∗
    consoleOwn (o ++ printArgs st vs) ∗ stackScratch (s - 80#64) printNeed ∗
    NpK Wp Φ N sret args s r vs st o rv)

/-- The shared pure facts of a `native_print` run. -/
structure NpCtx (live : Nat → Prop) (sret args s r : BitVec 64) (n : Nat) (rv : Nat → BitVec 64) :
    Prop where
  hlive : ∀ p ∈ interpText, live p.1
  hal : r.toNat % 4 = 0
  h10 : rv 10 = sret
  h12 : rv 12 = BitVec.ofNat 64 n
  h13 : rv 13 = args
  h2 : rv 2 = s
  hs1 : 0x87800000 + nativePrintNeed ≤ s.toNat
  hs2 : s.toNat ≤ 0x88000000
  hs3 : s.toNat % 16 = 0
  hs4 : s.toNat ≤ Vsa.Sim.LayoutInstance.spEntry - Vsa.Sim.LayoutInstance.interpRunFrame
  hg : SlotGeom sret
  ha : ArgsGeom args n
  hn : n < 2 ^ 31
  hdfa : ∀ k, InExt (s.toNat - 80, 80) k → ¬ InExt (args.toNat, 24 * n) k

/-- The pure state of the loop: `s0 = args + 24 i8`, `s1 = i9`, the other
saved registers, the frame's saved words, the arguments' bytes. -/
structure NpFacts (sret args s r : BitVec 64) (n i8 i9 : Nat) (rv R : Nat → BitVec 64)
    (M Margs : Mem) : Prop where
  h8 : R 8 = args + BitVec.ofNat 64 (24 * i8)
  h9 : R 9 = BitVec.ofNat 64 i9
  h18 : R 18 = 0x8001b970#64
  h19 : R 19 = BitVec.ofNat 64 n
  h20 : R 20 = sret
  h2 : R 2 = s + 18446744073709551536#64
  hk : ∀ x ∈ fRegs, x ∉ callerSaved → x ∉ [2, 8, 9, 18, 19, 20] → R x = rv x
  sra : ldv .ld M (s + 18446744073709551536#64 + 72#64).toNat = r
  ss0 : ldv .ld M (s + 18446744073709551536#64 + 64#64).toNat = rv 8
  ss1 : ldv .ld M (s + 18446744073709551536#64 + 56#64).toNat = rv 9
  ss2 : ldv .ld M (s + 18446744073709551536#64 + 48#64).toNat = rv 18
  ss3 : ldv .ld M (s + 18446744073709551536#64 + 40#64).toNat = rv 19
  ss4 : ldv .ld M (s + 18446744073709551536#64 + 32#64).toNat = rv 20
  hargs : ∀ k, InExt (args.toNat, 24 * n) k → imgM M k = imgM Margs k

/-- The rest a `native_print` loop carries. -/
def NpRest (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (sret args s r : BitVec 64) (vs : List Value) (st : Store) (o : String) (rv : Nat → BitVec 64)
    (Margs : Mem) : IProp GF :=
  iprop(codeRes ∗ slot24 sret.toNat ∗ valsImg N (imgM Margs) args.toNat vs ∗ dispResL st vs ∗
    binImg ∗ stackScratch (s - 80#64) printNeed ∗ NpK Wp Φ N sret args s r vs st o rv)

omit I in
omit I in
/-- A newlib stdout spec is a function spec. -/
theorem outSpec_fn {live : Nat → Prop} {Wp : MachWP (GF := GF) (vsaModel live)} {entry : BitVec 64}
    {args : List (BitVec 64)} {Rr : IProp GF} {s : BitVec 64} {need : Nat} {cs : Nat → BitVec 64}
    {o frag : String} :
    outSpec live Wp entry args Rr s need cs o frag ⊢
      fnSpecW Wp entry (fun _ => iprop(argsAt args ∗ Rr ∗ stdioOwn ∗ consoleOwn o ∗
          callFrame s need Newlib.calleeSaved cs))
        (fun _ => iprop(clobbered argRegs ∗ stdioOwn ∗ consoleOwn (o ++ frag) ∗
          callFrame s need Newlib.calleeSaved cs)) := .rfl

omit I in
/-- **A newlib stdout call from a run** (`jal`), against an `IrisHoles.out`
statement at the run's callee-saved registers. -/
theorem ms_callOut (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalExec (vsaModel live) i code entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    {args : List (BitVec 64)} {Rr : IProp GF} {s : BitVec 64} {need n : Nat} {R : Nat → BitVec 64}
    {S : Nat → Prop} {Mt : Mem} {o frag : String}
    (hspec : ∀ cs, ⊢ outSpec live Wp entry args Rr s need cs o frag)
    (hlen : args.length ≤ 8) (hvs : ∀ i (h : i < args.length), R (10 + i) = args[i])
    (hs : R 2 = s) (hn : n ≤ s.toNat) (hneed : need ≤ n) :
    codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗ Rr ∗ stdioOwn ∗ consoleOwn o ∗ stackScratch s n ∗ binImg ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ callerSaved → R' x = R x⌝ -∗ stdioOwn -∗
        consoleOwn (o ++ frag) -∗ ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗
        stackScratch s n -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hcode, Hms, HR, Hstd, Hcon, Hst, #Himg, Hk⟩
  ihave #Hsp0 := hspec R
  ihave #Hsp := outSpec_fn $$ Hsp0
  ihave #Hgp := codeRes_gp $$ Hcode
  iapply ms_callNewlib Wp hexec hcode
    (P := fun _ => iprop(argsAt args ∗ Rr ∗ stdioOwn ∗ consoleOwn o ∗
      callFrame s need Newlib.calleeSaved R))
    (Q := fun _ => iprop(clobbered argRegs ∗ stdioOwn ∗ consoleOwn (o ++ frag) ∗
      callFrame s need Newlib.calleeSaved R))
    (X := iprop(Rr ∗ stdioOwn ∗ consoleOwn o))
    (Y := iprop(stdioOwn ∗ consoleOwn (o ++ frag))) hlen hvs hs hn hneed
    (fun r => by iintro ⟨Ha, ⟨Hx, Hs, Hc⟩, Hf⟩; iframe Ha Hx Hs Hc Hf)
    (fun r => by iintro ⟨Ha, Hs, Hc, Hf⟩; iframe Ha Hs Hc Hf)
  iframe Hsp Hcode Hms Hst Hgp Himg HR Hstd Hcon
  iintro %R' %hk ⟨Hstd, Hcon⟩ Hms Hst
  iapply Hk $$ %R' %hk Hstd Hcon Hms Hst

/-- The frame of `native_print` as a stack region below `s`. -/
theorem npFrame_join {s : BitVec 64} (hs : 80 + printNeed ≤ s.toNat) :
    stackScratch (GF := GF) (s - 80#64) printNeed ∗
      ownSet (InExt (s.toNat - 80, 80)) byteAny ⊢ stackScratch s nativePrintNeed := by
  have h := stackScratch_unframe (GF := GF) (s := s) (f := 80#64) (n := nativePrintNeed)
    (by unfold nativePrintNeed; omega) (by unfold nativePrintNeed; simp)
  have e : (s - 80#64).toNat = s.toNat - 80 := toNat_sub_frame (by simp; omega)
  rw [e, show (80#64 : BitVec 64).toNat = 80 from rfl,
    show nativePrintNeed - 80 = printNeed by unfold nativePrintNeed; omega] at h
  unfold blockOwn at h
  exact h

/-- And the frame out of the stack below `s`. -/
theorem npFrame_split {s : BitVec 64} (hs : 80 + printNeed ≤ s.toNat) :
    stackScratch (GF := GF) s nativePrintNeed ⊢
      stackScratch (s - 80#64) printNeed ∗ ownSet (InExt (s.toNat - 80, 80)) byteAny := by
  have h := stackScratch_frame (GF := GF) (s := s) (f := 80#64) (n := nativePrintNeed)
    (by unfold nativePrintNeed; omega) (by unfold nativePrintNeed; simp)
  have e : (s - 80#64).toNat = s.toNat - 80 := toNat_sub_frame (by simp; omega)
  rw [e, show (80#64 : BitVec 64).toNat = 80 from rfl,
    show nativePrintNeed - 80 = printNeed by unfold nativePrintNeed; omega] at h
  unfold blockOwn at h
  exact h

/-- **`native_print`'s tail**: `value_null`, the epilogue, the return. -/
theorem np_tail (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {sret args s r : BitVec 64} {n : Nat} {vs : List Value} {st : Store}
    {o : String} {rv : Nat → BitVec 64} {Margs : Mem} (c : NpCtx live sret args s r n rv)
    (hvn : ⊢ valueNullSpec (vsaModel live) N Wp sret) (hlen : vs.length = n)
    {R : Nat → BitVec 64} {M : Mem}
    (hR10 : R 10 = sret) (hR20 : R 20 = sret) (hR2 : R 2 = s + 18446744073709551536#64)
    (hkeep : ∀ x ∈ fRegs, x ∉ callerSaved → x ≠ 2 → x ≠ 20 → R x = rv x)
    (hra : ldv .ld M (s + 18446744073709551536#64 + 72#64).toNat = r)
    (hs4 : ldv .ld M (s + 18446744073709551536#64 + 32#64).toNat = rv 20)
    (hargs : ∀ k, InExt (args.toNat, 24 * n) k → imgM M k = imgM Margs k)
    (hdfa : ∀ k, InExt (s.toNat - 80, 80) k → ¬ InExt (args.toNat, 24 * n) k) :
    codeRes ∗ ms 0x80002f64#64 R (npF s args n) M ∗ slot24 sret.toNat ∗
      valsImg N (imgM Margs) args.toNat vs ∗ stdioOwn ∗ consoleOwn (o ++ printArgs st vs) ∗
      stackScratch (s - 80#64) printNeed ∗ NpK Wp Φ N sret args s r vs st o rv ⊢ Wp.W Φ := by
  iintro ⟨#Hcode, Hms, Hsl, #Hv, Hstd, Hcon, Hst, Hk⟩
  ihave #Hvn := hvn
  unfold valueNullSpec
  iapply ms_callHelper Wp (i := 0x80002f64)
    (jalx_80002f64 live (fun p hp => c.hlive _ (interp_code_80002f64 p hp))) interp_code_80002f64
    (by decide) (clob := []) (pins := fun rv => rv 10 = sret)
    (Pre := iprop(slot24 sret.toNat ∗ ⌜SlotGeom sret⌝)) (Post := fun _ => valAt N sret.toNat .null)
  isplitl []
  · ipureintro; exact hR10
  isplitl []
  · iexact Hvn
  iframe Hcode Hms
  isplitl [Hsl]
  · iframe Hsl; ipureintro; exact c.hg
  iintro %R' %hk' Hnull Hms
  have hR' : ∀ x ∈ fRegs, R' x = R x := fun x hx => hk' x hx (by simp)
  iapply wp_swpF Wp (S := npF s args n) (F := FnpE Wp Φ N sret args s r vs st o rv Margs)
  rotate_left
  · have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
      unfold codeRes; simp [dataOf]
    rw [hro]
    unfold FnpE
    iframe Hcode Hv Hnull Hstd Hcon Hst Hk Hms
  intro F'
  have hs1 := c.hs1; have hs2 := c.hs2; have hs3 := c.hs3
  unfold nativePrintNeed printNeed fprintfNeed at hs1
  refine np_epi c.hlive (by ix_reg; rw [hR' 2 (by decide), hR2]) (by omega) hs2 hs3 c.hal hra hs4 ?_
  intros; apply swp_closeF
  dsimp only [F']
  unfold FnpE
  iintro ⟨⟨#Hv, Hnull, Hstd, Hcon, Hst, Hk⟩, Hms⟩
  unfold ms
  icases Hms with ⟨Hpc, Hra, Hregs, HS⟩
  ihave ⟨HF, HA⟩ := ownSet_split_tracked _ _ M hdfa $$ HS
  ihave HF := ownSet_forget _ _ $$ HF
  ihave Hst := npFrame_join (s := s) (by unfold printNeed fprintfNeed; omega) $$ [Hst HF]
  · iframe Hst HF
  subst hlen
  ihave #Hv' := valsImg_agree N vs args.toNat (fun k hk => (hargs k hk).symm) $$ Hv
  ihave Hvs := valsAt_of_tracked N M vs args.toNat $$ [HA Hv']
  · iframe HA Hv'
  ihave Hra := ptsto_eq (show _ = r by ix_reg) $$ Hra
  iapply Hk $$ Hpc Hra
  iexists _
  iframe Hregs Hnull Hvs Hstd Hcon
  isplitr
  · ipureintro
    intro x hx hc
    have h1 : x ≠ 1 := fun e => by subst e; revert hx; decide
    have h10 : x ≠ 10 := fun e => by subst e; exact hc (by decide)
    by_cases h2 : x = 2
    · subst h2; ix_reg
      rw [BitVec.add_assoc, show (18446744073709551536#64 : BitVec 64) + 80#64 = 0#64 by decide,
        BitVec.add_zero, c.h2]
    · by_cases h20 : x = 20
      · subst h20; ix_reg
      · simp only [upd, h1, h10, h2, h20, ite_false]
        rw [hR' x hx]; exact hkeep x hx hc h2 h20
  · unfold stackAt
    iframe Hst
    ipureintro
    exact ⟨by unfold nativePrintNeed printNeed fprintfNeed; omega,
      by unfold Vsa.Sim.LayoutInstance.stackSL; simp; unfold nativePrintNeed printNeed fprintfNeed; omega,
      by unfold Vsa.Sim.LayoutInstance.stackSL; simp; omega, hs3, c.hs4⟩

/-- The frame of the loop-body run. -/
def FnpA (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (sret args s r : BitVec 64) (vs : List Value) (st : Store) (o o' : String) (rv : Nat → BitVec 64)
    (Margs : Mem) (img : Nat → BitVec 8) : IProp GF :=
  iprop(NpRest Wp Φ N sret args s r vs st o rv Margs ∗ consoleOwn o' ∗
    ownSet (fun k => stdioFoot k ∧ ¬ ioW k) (fun k => k ↦ₘ img k))

/-- **An iteration's first half**: the loop head, the copy of argument `i`,
`value_print`. -/
theorem np_A (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {sret args s r : BitVec 64} {n : Nat} {vs : List Value} {st : Store}
    {o : String} {rv : Nat → BitVec 64} {Margs : Mem} (c : NpCtx live sret args s r n rv)
    (hvp : ∀ v o', ⊢ valuePrintSpec (vsaModel live) N Wp (s - 80#64) (s - 80#64) v st o')
    (hlen : vs.length = n) {i : Nat} (hi : i < n) {R : Nat → BitVec 64} {M : Mem}
    (f : NpFacts sret args s r n i i rv R M Margs)
    (hB : ∀ R' M', NpFacts sret args s r n i (i + 1) rv R' M' Margs →
      NpRest Wp Φ N sret args s r vs st o rv Margs ∗ ms 0x80002f48#64 R' (npF s args n) M' ∗ stdioOwn ∗
        consoleOwn (o ++ npOut st vs i ++ (vs[i]'(by omega)).display st) ⊢ Wp.W Φ) :
    NpRest Wp Φ N sret args s r vs st o rv Margs ∗ ms 0x80002f1c#64 R (npF s args n) M ∗ stdioOwn ∗
      consoleOwn (o ++ npOut st vs i) ⊢ Wp.W Φ := by
  iintro ⟨Hrest, Hms, Hstd, Hcon⟩
  ihave ⟨%img, %M1, %hok, Hms, Hio, %⟨hM1, hio, hd⟩⟩ := ms_ioOpen $$ [Hms Hstd]
  · iframe Hms Hstd
  have hs1 := c.hs1; have hs2 := c.hs2; have hs3 := c.hs3
  unfold nativePrintNeed printNeed fprintfNeed at hs1
  have ha1 := c.ha.al; have ha2 := c.ha.lo; have ha3 := c.ha.hi
  have ea : (args + BitVec.ofNat 64 (24 * i)).toNat = args.toNat + 24 * i := by
    rw [BitVec.toNat_add]; simp; omega
  have hA : ∀ k, InExt (args.toNat, 24 * n) k → imgM M1 k = imgM Margs k := fun k hk =>
    (hM1 k (.inr hk)).trans (f.hargs k hk)
  have hw : ∀ o, o ≤ 16 → imgW (imgM M1) (args.toNat + 24 * i + o) =
      imgW (imgM Margs) (args.toNat + 24 * i + o) := fun o ho =>
    imgW_agree (fun j hj => hA _ (by simp [InExt]; omega))
  have hw0 : ldv .ld M1 (args.toNat + 24 * i) = imgW (imgM Margs) (args.toNat + 24 * i) := by
    rw [ldv_ld_imgW]; simpa using hw 0 (by omega)
  have hw1 : ldv .ld M1 (args + BitVec.ofNat 64 (24 * i) + 8#64).toNat =
      imgW (imgM Margs) (args.toNat + 24 * i + 8) := by
    rw [ldv_ld_imgW, show (args + BitVec.ofNat 64 (24 * i) + 8#64).toNat = args.toNat + 24 * i + 8 by
      rw [BitVec.toNat_add, ea]; simp; omega]
    exact hw 8 (by omega)
  have hw2 : ldv .ld M1 (args + BitVec.ofNat 64 (24 * i) + 16#64).toNat =
      imgW (imgM Margs) (args.toNat + 24 * i + 16) := by
    rw [ldv_ld_imgW, show (args + BitVec.ofNat 64 (24 * i) + 16#64).toNat = args.toNat + 24 * i + 16 by
      rw [BitVec.toNat_add, ea]; simp; omega]
    exact hw 16 (by omega)
  have hio1 : ldv .ld M1 0x8001b970 = 0x8001b538#64 := by
    rw [ldv_ld_imgW]; unfold imgW
    rw [imgLE_congr (img' := img) (fun j hj => hio _ (by simp [ioW, InExt]; omega))]
    exact hok.impure
  have hio2 : ldv .ld M1 0x8001b548 = 0x8001bb20#64 := by
    rw [ldv_ld_imgW]; unfold imgW
    rw [imgLE_congr (img' := img) (fun j hj => hio _ (by simp [ioW, InExt]; omega))]
    exact StdioOK.stdout hok
  iapply wp_swpF Wp (S := npS s args n) (R := R) (Mt := M1) (pc := 0x80002f1c#64)
    (F := FnpA Wp Φ N sret args s r vs st o (o ++ npOut st vs i) rv Margs img)
  rotate_left
  · have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
      unfold codeRes; simp [dataOf]
    unfold NpRest
    icases Hrest with ⟨#Hcode, Hsl, #Hv, #Hd, #Himg, Hst, Hk⟩
    rw [hro]
    unfold FnpA NpRest
    iframe Hcode Hsl Hv Hd Himg Hst Hk Hcon Hio Hms
  intro F'
  refine np_body c.hlive f.h8 f.h9 f.h18 f.h2 (by omega) hs2 hs3 ha1 ha2 ha3 hi ea hw0 hw1 hw2 hio1
    hio2 ?_
  intros; apply swp_closeF
  dsimp only [F']
  unfold FnpA
  iintro ⟨⟨Hrest, Hcon, Hio⟩, Hms⟩
  have hsm : s - 80#64 = s + 18446744073709551536#64 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  have hsf : (s + 18446744073709551536#64).toNat = s.toNat - 80 := by
    rw [BitVec.toNat_add]; simp; omega
  have e8 : (s + 18446744073709551536#64 + 8#64).toNat = s.toNat - 80 + 8 := by
    rw [BitVec.toNat_add, hsf]; simp; omega
  have e16 : (s + 18446744073709551536#64 + 16#64).toNat = s.toNat - 80 + 16 := by
    rw [BitVec.toNat_add, hsf]; simp; omega
  rw [e8, e16]
  ihave ⟨Hms, Hstd⟩ := ms_ioClose hok hd $$ [Hms Hio]
  · iframe Hms Hio
    ipureintro
    intro k hk
    simp only [ioW, InExt] at hk
    simp (disch := omega) only [imgM_store_miss]
    exact hio k (by simp only [ioW, InExt]; omega)
  -- the copy slot out of the frame
  have hsl : ∀ k, npF s args n k ↔
      ((npF s args n k ∧ ¬ InExt (s.toNat - 80, 24) k) ∨ InExt (s.toNat - 80, 24) k) := fun k => by
    constructor
    · intro h; by_cases h' : InExt (s.toNat - 80, 24) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · left; simp only [InExt] at h ⊢; omega
  ihave Hms := ms_iff hsl $$ Hms
  ihave ⟨Hms, Hslot⟩ := ms_split (fun k h1 h2 => h1.2 h2) $$ Hms
  -- its three words are argument `i`'s
  have hv0 : imgW (imgM (writeLog (writeLog (writeLog M1 [(s.toNat - 80, 8,
      imgW (imgM Margs) (args.toNat + 24 * i))]) [(s.toNat - 80 + 8, 8,
      imgW (imgM Margs) (args.toNat + 24 * i + 8))]) [(s.toNat - 80 + 16, 8,
      imgW (imgM Margs) (args.toNat + 24 * i + 16))])) (s.toNat - 80) =
      imgW (imgM Margs) (args.toNat + 24 * i) := by
    rw [imgW_store_miss _ _ (by omega), imgW_store_miss _ _ (by omega), imgW_store_hit]
  have hv8 : imgW (imgM (writeLog (writeLog (writeLog M1 [(s.toNat - 80, 8,
      imgW (imgM Margs) (args.toNat + 24 * i))]) [(s.toNat - 80 + 8, 8,
      imgW (imgM Margs) (args.toNat + 24 * i + 8))]) [(s.toNat - 80 + 16, 8,
      imgW (imgM Margs) (args.toNat + 24 * i + 16))])) (s.toNat - 80 + 8) =
      imgW (imgM Margs) (args.toNat + 24 * i + 8) := by
    rw [imgW_store_miss _ _ (by omega), imgW_store_hit]
  have hv16 : imgW (imgM (writeLog (writeLog (writeLog M1 [(s.toNat - 80, 8,
      imgW (imgM Margs) (args.toNat + 24 * i))]) [(s.toNat - 80 + 8, 8,
      imgW (imgM Margs) (args.toNat + 24 * i + 8))]) [(s.toNat - 80 + 16, 8,
      imgW (imgM Margs) (args.toNat + 24 * i + 16))])) (s.toNat - 80 + 16) =
      imgW (imgM Margs) (args.toNat + 24 * i + 16) := by
    rw [imgW_store_hit]
  unfold NpRest
  icases Hrest with ⟨#Hcode, Hsl, #Hv, #Hd, #Himg, Hst, Hk⟩
  ihave #Hvi := valsImg_get N (imgM Margs) vs args.toNat i (by omega) $$ Hv
  rw [← valImg_words (GF := GF) hv0 hv8 hv16] at *
  have hst80 : (s - 80#64).toNat = s.toNat - 80 := by rw [hsm, hsf]
  ihave Hval := valAt_of_img N $$ [Hvi Hslot]
  · iframe Hvi Hslot
  ihave #Hdi := (show dispResL (GF := GF) st vs ⊢ dispRes st (vs[i]'(by omega)) from by
    unfold dispResL
    exact sepL_elem_persist (dispRes st) (List.getElem_mem (show i < vs.length by omega))) $$ Hd
  ihave #Hvp := hvp (vs[i]'(by omega)) (o ++ npOut st vs i)
  unfold valuePrintSpec
  have hsg80 : StackGeom (s - 80#64) printNeed := ⟨by rw [hst80]; unfold printNeed fprintfNeed; omega,
    by rw [hst80]; unfold Vsa.Sim.LayoutInstance.stackSL printNeed fprintfNeed; simp; omega,
    by rw [hst80]; unfold Vsa.Sim.LayoutInstance.stackSL; simp; omega,
    by rw [hst80]; omega, by rw [hst80]; have := c.hs4; omega⟩
  have hslg : SlotGeom (s - 80#64) := ⟨by rw [hst80]; omega,
    by rw [hst80]; unfold Vsa.Sim.tohostAddr; omega, by rw [hst80]; omega⟩
  iapply ms_callHelper Wp (i := 0x80002f44)
    (jalx_80002f44 live (fun p hp => c.hlive _ (interp_code_80002f44 p hp))) interp_code_80002f44
    (by decide) (clob := callerSaved)
    (pins := fun rv => rv 10 = s - 80#64 ∧ rv 11 = stdoutFile ∧ rv 2 = s - 80#64)
    (Pre := iprop(valAt N (s - 80#64).toNat (vs[i]'(by omega)) ∗ ⌜SlotGeom (s - 80#64)⌝ ∗
      dispRes st (vs[i]'(by omega)) ∗ binImg ∗ stdioOwn ∗ consoleOwn (o ++ npOut st vs i) ∗
      stackAt (s - 80#64) printNeed))
    (Post := fun _ => iprop(valAt N (s - 80#64).toNat (vs[i]'(by omega)) ∗ stdioOwn ∗
      consoleOwn (o ++ npOut st vs i ++ (vs[i]'(by omega)).display st) ∗
      stackAt (s - 80#64) printNeed))
  iframe Hvp Hcode Hms
  isplitl []
  · ipureintro; refine ⟨?_, ?_, ?_⟩
    · ix_reg; exact hsm.symm
    · ix_reg; rfl
    · ix_reg; rw [f.h2, hsm]
  isplitl [Hval Hstd Hcon Hst]
  · rw [hst80]
    iframe Hval Hdi Himg Hstd Hcon
    unfold stackAt
    iframe Hst
    ipureintro; exact ⟨hslg, hsg80⟩
  iintro %R2 %hk2 ⟨Hval, Hstd, Hcon, ⟨Hst, -⟩⟩ Hms
  rw [hst80]
  ihave ⟨%Ms, HsS, #Hw⟩ := valAt_tracked N _ _ $$ Hval
  ihave ⟨%M3, Hms, %⟨h3a, h3b, _⟩⟩ := ms_join $$ [Hms HsS]
  · iframe Hms HsS
  ihave Hms := ms_iff (fun k => (hsl k).symm) $$ Hms
  -- the frame's saved words and the arguments' bytes survive
  have hsv : ∀ o, 24 ≤ o → o + 8 ≤ 80 →
      ldv .ld M3 (s.toNat - 80 + o) = ldv .ld M (s.toNat - 80 + o) := fun o h1 h2 =>
    ldv_agree fun j hj => by
      rw [h3a _ ⟨.inl (by simp only [InExt]; omega), by simp only [InExt]; omega⟩]
      simp (disch := omega) only [imgM_store_miss]
      exact hM1 _ (.inl (by simp only [InExt]; omega))
  have hsvo : ∀ o, 24 ≤ o → o + 8 ≤ 80 →
      (s + 18446744073709551536#64 + BitVec.ofNat 64 o).toNat = s.toNat - 80 + o := fun o h1 h2 => by
    rw [BitVec.toNat_add, hsf]; simp; omega
  have hA3 : ∀ k, InExt (args.toNat, 24 * n) k → imgM M3 k = imgM Margs k := fun k hk => by
    have hnf : ¬ InExt (s.toNat - 80, 80) k := fun h => c.hdfa k h hk
    rw [h3a _ ⟨.inr hk, fun h => hnf (by simp only [InExt] at h ⊢; omega)⟩]
    simp (disch := (simp only [InExt] at hnf; omega)) only [imgM_store_miss]
    exact hA k hk
  iapply hB (upd R2 1 (BitVec.ofNat 64 (0x80002f44 + 4))) M3 ?_
  rotate_left
  · unfold NpRest
    iframe Hcode Hsl Hv Hd Himg Hst Hk Hms Hstd Hcon
  have k2 := fun x (hx : x ∈ fRegs) (hc : x ∉ callerSaved) => hk2 x hx hc
  have sw : ∀ o, 24 ≤ o → o + 8 ≤ 80 →
      ldv .ld M3 (s + 18446744073709551536#64 + BitVec.ofNat 64 o).toNat =
        ldv .ld M (s + 18446744073709551536#64 + BitVec.ofNat 64 o).toNat := fun o h1 h2 => by
    rw [hsvo o h1 h2]; exact hsv o h1 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hA3⟩
  · ix_reg; rw [k2 8 (by decide) (by decide)]; ix_reg; exact f.h8
  · ix_reg; rw [k2 9 (by decide) (by decide)]; ix_reg
    exact sx32_succ i (by have := c.hn; omega)
  · ix_reg; rw [k2 18 (by decide) (by decide)]; ix_reg; exact f.h18
  · ix_reg; rw [k2 19 (by decide) (by decide)]; ix_reg; exact f.h19
  · ix_reg; rw [k2 20 (by decide) (by decide)]; ix_reg; exact f.h20
  · ix_reg; rw [k2 2 (by decide) (by decide)]; ix_reg; exact f.h2
  · intro x hx hc hn
    have hx1 : x ≠ 1 := fun e => by subst e; revert hx; decide
    have e9 : x ≠ 9 := fun e => hn (by simp [e])
    have e10 : x ≠ 10 := fun e => hc (by simp [e])
    have e11 : x ≠ 11 := fun e => hc (by simp [e])
    have e13 : x ≠ 13 := fun e => hc (by simp [e])
    have e14 : x ≠ 14 := fun e => hc (by simp [e])
    have e15 : x ≠ 15 := fun e => hc (by simp [e])
    simp only [upd, hx1, ite_false]
    rw [k2 x hx hc]
    simp only [upd, e9, e10, e11, e13, e14, e15, ite_false]
    exact f.hk x hx hc hn
  · rw [sw 72 (by omega) (by omega)]; exact f.sra
  · rw [sw 64 (by omega) (by omega)]; exact f.ss0
  · rw [sw 56 (by omega) (by omega)]; exact f.ss1
  · rw [sw 48 (by omega) (by omega)]; exact f.ss2
  · rw [sw 40 (by omega) (by omega)]; exact f.ss3
  · rw [sw 32 (by omega) (by omega)]; exact f.ss4

/-- The frame of the `fputc` run. -/
def FnpB (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (sret args s r : BitVec 64) (vs : List Value) (st : Store) (o o' : String) (rv : Nat → BitVec 64)
    (Margs : Mem) (img : Nat → BitVec 8) : IProp GF :=
  FnpA Wp Φ N sret args s r vs st o o' rv Margs img

/-- The `fputc(' ')` call, at `0x80002f18`, back to the loop head. -/
theorem np_fputc (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {sret args s r : BitVec 64} {n : Nat} {vs : List Value} {st : Store}
    {o o' : String} {rv : Nat → BitVec 64} {Margs : Mem} (c : NpCtx live sret args s r n rv)
    (hcl : CodeLive live) (H : OutHoles) {i : Nat}
    {R : Nat → BitVec 64} {M : Mem} (f : NpFacts sret args s r n (i + 1) (i + 1) rv R M Margs)
    (ha0 : R 10 = 32#64) (ha1 : R 11 = stdoutFile)
    (hA : ∀ R' M', NpFacts sret args s r n (i + 1) (i + 1) rv R' M' Margs →
      NpRest Wp Φ N sret args s r vs st o rv Margs ∗ ms 0x80002f1c#64 R' (npF s args n) M' ∗
        stdioOwn ∗ consoleOwn (o' ++ " ") ⊢ Wp.W Φ) :
    NpRest Wp Φ N sret args s r vs st o rv Margs ∗ ms 0x80002f18#64 R (npF s args n) M ∗ stdioOwn ∗
      consoleOwn o' ⊢ Wp.W Φ := by
  iintro ⟨Hrest, Hms, Hstd, Hcon⟩
  have hs1 := c.hs1; have hs2 := c.hs2; have hs3 := c.hs3
  unfold nativePrintNeed printNeed fprintfNeed at hs1
  have hsm : s - 80#64 = s + 18446744073709551536#64 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  have hst80 : (s - 80#64).toNat = s.toNat - 80 := by
    rw [hsm, BitVec.toNat_add]; simp; omega
  have hsg : StackGeom (s - 80#64) printNeed := ⟨by rw [hst80]; unfold printNeed fprintfNeed; omega,
    by rw [hst80]; unfold Vsa.Sim.LayoutInstance.stackSL printNeed fprintfNeed; simp; omega,
    by rw [hst80]; unfold Vsa.Sim.LayoutInstance.stackSL; simp; omega, by rw [hst80]; omega,
    by rw [hst80]; have := c.hs4; omega⟩
  unfold NpRest
  icases Hrest with ⟨#Hcode, Hsl, #Hv, #Hd, #Himg, Hst, Hk⟩
  iapply ms_callOut Wp (i := 0x80002f18)
    (jalx_80002f18 live (fun p hp => c.hlive _ (interp_code_80002f18 p hp))) interp_code_80002f18
    (R := R) (S := npF s args n) (Mt := M) (n := printNeed)
    (fun cs => H.fputc live Wp (32#8) (s - 80#64) cs o' hcl (spIn_of_stackGeom hsg (by decide)))
    (by simp) (fun j hj => by
      simp only [List.length_cons, List.length_nil] at hj
      rcases j with _ | _ | j
      · rw [ha0]; rfl
      · rw [ha1]; rfl
      · omega)
    (by rw [f.h2, hsm]) (by rw [hst80]; unfold printNeed fprintfNeed; omega) (by decide)
  iframe Hcode Hms Hstd Hcon Hst Himg
  iintro %R4 %hk4 Hstd Hcon Hms Hst
  rw [show toString (Char.ofNat (32#8 : BitVec 8).toNat) = " " by decide]
  have k4 := fun x (hx : x ∈ fRegs) (hc : x ∉ callerSaved) => hk4 x hx hc
  iapply hA (upd R4 1 (BitVec.ofNat 64 (0x80002f18 + 4))) M ?_
  rotate_left
  · unfold NpRest
    iframe Hcode Hsl Hv Hd Himg Hst Hk Hms Hstd Hcon
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, f.sra, f.ss0, f.ss1, f.ss2, f.ss3, f.ss4, f.hargs⟩
  · ix_reg; rw [k4 8 (by decide) (by decide)]; exact f.h8
  · ix_reg; rw [k4 9 (by decide) (by decide)]; exact f.h9
  · ix_reg; rw [k4 18 (by decide) (by decide)]; exact f.h18
  · ix_reg; rw [k4 19 (by decide) (by decide)]; exact f.h19
  · ix_reg; rw [k4 20 (by decide) (by decide)]; exact f.h20
  · ix_reg; rw [k4 2 (by decide) (by decide)]; exact f.h2
  · intro x hx hc hn
    have hx1 : x ≠ 1 := fun e => by subst e; revert hx; decide
    simp only [upd, hx1, ite_false]
    rw [k4 x hx hc]; exact f.hk x hx hc hn

/-- **An iteration's second half, more arguments**: `fputc(' ')`, back to the
loop head. -/
theorem np_B_more (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {sret args s r : BitVec 64} {n : Nat} {vs : List Value} {st : Store}
    {o : String} {rv : Nat → BitVec 64} {Margs : Mem} (c : NpCtx live sret args s r n rv)
    (hcl : CodeLive live) (H : OutHoles) (hlen : vs.length = n) {i : Nat} (hi : i + 1 < n)
    {R : Nat → BitVec 64} {M : Mem} (f : NpFacts sret args s r n i (i + 1) rv R M Margs)
    (hA : ∀ R' M', NpFacts sret args s r n (i + 1) (i + 1) rv R' M' Margs →
      NpRest Wp Φ N sret args s r vs st o rv Margs ∗ ms 0x80002f1c#64 R' (npF s args n) M' ∗
        stdioOwn ∗ consoleOwn (o ++ npOut st vs (i + 1)) ⊢ Wp.W Φ) :
    NpRest Wp Φ N sret args s r vs st o rv Margs ∗ ms 0x80002f48#64 R (npF s args n) M ∗ stdioOwn ∗
      consoleOwn (o ++ npOut st vs i ++ (vs[i]'(by omega)).display st) ⊢ Wp.W Φ := by
  iintro ⟨Hrest, Hms, Hstd, Hcon⟩
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
  have hne : BitVec.ofNat 64 n ≠ BitVec.ofNat 64 (i + 1) := fun h => by
    have h1 := congrArg BitVec.toNat h; have := c.hn
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h1
    omega
  iapply wp_swpF Wp (S := npS s args n) (R := R) (Mt := M1) (pc := 0x80002f48#64)
    (F := FnpB Wp Φ N sret args s r vs st o (o ++ npOut st vs i ++ (vs[i]'(by omega)).display st)
      rv Margs img)
  rotate_left
  · have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
      unfold codeRes; simp [dataOf]
    unfold NpRest
    icases Hrest with ⟨#Hcode, Hsl, #Hv, #Hd, #Himg, Hst, Hk⟩
    rw [hro]
    unfold FnpB FnpA NpRest
    iframe Hcode Hsl Hv Hd Himg Hst Hk Hcon Hio Hms
  intro F'
  refine np_more c.hlive f.h8 f.h9 f.h18 f.h19 hne hio1 hio2 ?_
  intros; apply swp_closeF
  dsimp only [F']
  unfold FnpB FnpA
  iintro ⟨⟨Hrest, Hcon, Hio⟩, Hms⟩
  ihave ⟨Hms, Hstd⟩ := ms_ioClose hok hd $$ [Hms Hio]
  · iframe Hms Hio
    ipureintro; exact hio
  have ha1 := c.ha.al; have ha2 := c.ha.lo; have ha3 := c.ha.hi
  have h8 : args + BitVec.ofNat 64 (24 * i) + 24#64 = args + BitVec.ofNat 64 (24 * (i + 1)) := by
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq; simp; omega
  iapply (np_fputc Wp c hcl H (N := N) (vs := vs) (st := st) (o := o) (Margs := Margs) (Φ := Φ)
    (o' := o ++ npOut st vs i ++ (vs[i]'(by omega)).display st) (i := i) (M := M1)
    (R := upd (upd (upd (upd R 10 32#64) 15 2147595576#64) 8 (args + BitVec.ofNat 64 (24 * i) + 24#64)) 11
      2147597088#64) ?f ?ha0 ?ha1 ?hA)
  case ha0 => ix_reg
  case ha1 => ix_reg; rfl
  case hA =>
    intro R' M' f'
    rw [show o ++ npOut st vs i ++ (vs[i]'(by omega)).display st ++ " " = o ++ npOut st vs (i + 1) by
      rw [String.append_assoc, String.append_assoc, ← npOut_succ st vs i (by omega),
        String.append_assoc]]
    exact hA R' M' f'
  case f =>
    have sw : ∀ o, 24 ≤ o → o + 8 ≤ 80 →
        ldv .ld M1 (s + 18446744073709551536#64 + BitVec.ofNat 64 o).toNat =
          ldv .ld M (s + 18446744073709551536#64 + BitVec.ofNat 64 o).toNat := fun o h1 h2 => by
      have hs1 := c.hs1
      unfold nativePrintNeed printNeed fprintfNeed at hs1
      have e : (s + 18446744073709551536#64 + BitVec.ofNat 64 o).toNat = s.toNat - 80 + o := by
        rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
      rw [e]
      exact ldv_agree fun j hj => hM1 _ (.inl (by simp only [InExt]; omega))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => (hM1 k (.inr hk)).trans
      (f.hargs k hk)⟩
    · ix_reg; exact h8
    · ix_reg; exact f.h9
    · ix_reg; exact f.h18
    · ix_reg; exact f.h19
    · ix_reg; exact f.h20
    · ix_reg; exact f.h2
    · intro x hx hc hn
      have e10 : x ≠ 10 := fun e => hc (by simp [e])
      have e11 : x ≠ 11 := fun e => hc (by simp [e])
      have e15 : x ≠ 15 := fun e => hc (by simp [e])
      have e8 : x ≠ 8 := fun e => hn (by simp [e])
      simp only [upd, e10, e11, e15, e8, ite_false]
      exact f.hk x hx hc hn
    · rw [sw 72 (by omega) (by omega)]; exact f.sra
    · rw [sw 64 (by omega) (by omega)]; exact f.ss0
    · rw [sw 56 (by omega) (by omega)]; exact f.ss1
    · rw [sw 48 (by omega) (by omega)]; exact f.ss2
    · rw [sw 40 (by omega) (by omega)]; exact f.ss3
    · rw [sw 32 (by omega) (by omega)]; exact f.ss4
  iframe Hrest Hms Hstd Hcon

/-- **An iteration's second half, last argument**: restore `s0`-`s3`, then the
tail. -/
theorem np_B_last (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {sret args s r : BitVec 64} {n : Nat} {vs : List Value} {st : Store}
    {o : String} {rv : Nat → BitVec 64} {Margs : Mem} (c : NpCtx live sret args s r n rv)
    (hvn : ⊢ valueNullSpec (vsaModel live) N Wp sret) (hlen : vs.length = n) {i : Nat}
    (hi : i + 1 = n) {R : Nat → BitVec 64} {M : Mem}
    (f : NpFacts sret args s r n i (i + 1) rv R M Margs) :
    NpRest Wp Φ N sret args s r vs st o rv Margs ∗ ms 0x80002f48#64 R (npF s args n) M ∗ stdioOwn ∗
      consoleOwn (o ++ npOut st vs i ++ (vs[i]'(by omega)).display st) ⊢ Wp.W Φ := by
  iintro ⟨Hrest, Hms, Hstd, Hcon⟩
  have hs1 := c.hs1; have hs2 := c.hs2; have hs3 := c.hs3
  unfold nativePrintNeed printNeed fprintfNeed at hs1
  unfold NpRest
  icases Hrest with ⟨#Hcode, Hsl, #Hv, #Hd, #Himg, Hst, Hk⟩
  rw [String.append_assoc, npOut_last st vs i (by omega)]
  iapply wp_swpF Wp (S := npF s args n) (R := R) (Mt := M) (pc := 0x80002f48#64)
    (F := iprop(slot24 sret.toNat ∗ valsImg N (imgM Margs) args.toNat vs ∗ stdioOwn ∗
      consoleOwn (o ++ printArgs st vs) ∗ stackScratch (s - 80#64) printNeed ∗
      NpK Wp Φ N sret args s r vs st o rv ∗ codeRes))
  rotate_left
  · have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
      unfold codeRes; simp [dataOf]
    rw [hro]
    iframe Hcode Hsl Hv Hstd Hcon Hst Hk Hms
  intro F'
  refine np_last c.hlive (f.h9.trans (by rw [hi])) f.h19 f.h2 (by omega) hs2 hs3 f.ss0 f.ss1 f.ss2
    f.ss3 ?_
  intros; apply swp_closeF
  dsimp only [F']
  iintro ⟨⟨Hsl, #Hv, Hstd, Hcon, Hst, Hk, #Hcode⟩, Hms⟩
  iapply np_tail Wp c hvn hlen
    (R := upd (upd (upd (upd (upd (upd R 10 32#64) 8 (rv 8)) 9 (rv 9)) 18 (rv 18)) 19 (rv 19)) 10 (R 20))
    (M := M) ?h10 ?h20 ?h2 ?hkeep f.sra f.ss4 f.hargs c.hdfa
  case h10 => simp only [upd]; simp; exact f.h20
  case h20 => simp only [upd]; simp; exact f.h20
  case h2 => simp only [upd]; simp; exact f.h2
  case hkeep =>
    intro x hx hc h2 h20
    have e10 : x ≠ 10 := fun e => hc (by simp [callerSaved, e])
    simp only [upd]
    by_cases h8 : x = 8
    · simp [h8]
    by_cases h9 : x = 9
    · simp [h9]
    by_cases h18 : x = 18
    · simp [h18]
    by_cases h19 : x = 19
    · simp [h19]
    simp only [e10, h8, h9, h18, h19, if_false]
    exact f.hk x hx hc (by simp [h2, h8, h9, h18, h19, h20])
  iframe Hcode Hms Hsl Hv Hstd Hcon Hst Hk

/-- **The loop**, from the head with argument `i` next, by induction on the
arguments left. -/
theorem np_loop (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {sret args s r : BitVec 64} {n : Nat} {vs : List Value} {st : Store}
    {o : String} {rv : Nat → BitVec 64} {Margs : Mem} (c : NpCtx live sret args s r n rv)
    (hcl : CodeLive live) (H : OutHoles)
    (hvp : ∀ v o', ⊢ valuePrintSpec (vsaModel live) N Wp (s - 80#64) (s - 80#64) v st o')
    (hvn : ⊢ valueNullSpec (vsaModel live) N Wp sret) (hlen : vs.length = n) :
    ∀ k i, i + k + 1 = n → ∀ R M, NpFacts sret args s r n i i rv R M Margs →
      NpRest Wp Φ N sret args s r vs st o rv Margs ∗ ms 0x80002f1c#64 R (npF s args n) M ∗
        stdioOwn ∗ consoleOwn (o ++ npOut st vs i) ⊢ Wp.W Φ := by
  intro k
  induction k with
  | zero =>
    intro i hk R M f
    exact np_A Wp c hvp hlen (by omega) f fun R' M' f' =>
      np_B_last Wp c hvn hlen (by omega) f'
  | succ k ih =>
    intro i hk R M f
    exact np_A Wp c hvp hlen (by omega) f fun R' M' f' =>
      np_B_more Wp c hcl H hlen (by omega) f' fun R'' M'' f'' => ih (i + 1) (by omega) R'' M'' f''

/-- **`native_print`**, given `IrisHoles.out`, for either WP. -/
theorem nativePrint_spec (hlive : ∀ q ∈ interpText, live q.1) (hcl : CodeLive live) (H : OutHoles)
    (Wp : MachWP (GF := GF) (vsaModel live)) (N : NativeAddrs) (sret args s : BitVec 64)
    (vs : List Value) (st : Store) (o : String) :
    ⊢ nativePrintSpec (vsaModel live) N Wp sret args s vs st o := by
  unfold nativePrintSpec helperSpec fnSpecW
  iintro %rv !> %r %Φ Hpc Hra ⟨%hal, Hregs, %⟨h10, h12, h13, h2⟩, #Hcode, Hsl, %⟨hg, ha, hn⟩, Hvs,
    #Hd, #Himg, Hstd, Hcon, ⟨Hst, %hsg⟩⟩ Hk
  have hs1 := hsg.le; have hs2 := hsg.lo; have hs3 := hsg.hi; have hs4 := hsg.al
  simp only [Vsa.Sim.LayoutInstance.stackSL] at hs2 hs3
  unfold nativePrintNeed printNeed fprintfNeed at hs1 hs2
  ihave ⟨%Margs, HA, #Hv⟩ := valsAt_tracked N vs args.toNat $$ Hvs
  ihave ⟨Hst, HF⟩ := npFrame_split (s := s) (by unfold printNeed fprintfNeed; omega) $$ Hst
  ihave ⟨%f, HF⟩ := ownSet_fn _ $$ HF
  ihave ⟨%Mf, HF⟩ := ownSet_mem _ f $$ HF
  ihave ⟨%M, HM, %⟨-, hMa, hdfa⟩⟩ := ownSet_join_tracked _ _ Mf Margs $$ [HF HA]
  · iframe HF HA
  have c : NpCtx live sret args s r vs.length rv :=
    ⟨hlive, hal, h10, h12, h13, h2, by unfold nativePrintNeed printNeed fprintfNeed; omega, by omega,
      hs4, hsg.top, hg, ha, hn, hdfa⟩
  have hms : ms (GF := GF) nativePrintPC (upd rv 1 r) (npF s args vs.length) M =
      iprop(PC ↦ᵣ nativePrintPC ∗ ra ↦ᵣ r ∗ regFile rv ∗
        ownSet (fun a => InExt (s.toNat - 80, 80) a ∨ InExt (args.toNat, 24 * vs.length) a)
          (fun a => a ↦ₘ imgM M a)) := by
    unfold ms; rw [regFile_upd_ra]; simp only [upd_same]
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hoff : ∀ k, k < 80 → (s + 18446744073709551536#64 + BitVec.ofNat 64 k).toNat = s.toNat - 80 + k := by
    intro k hk; rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  by_cases h0 : vs.length = 0
  · have e : o ++ printArgs st vs = o := by
      rw [List.length_eq_zero_iff.1 h0]; simp [printArgs]
    ihave Hcon := (show consoleOwn (GF := GF) o ⊢ consoleOwn (o ++ printArgs st vs) by rw [e]) $$ Hcon
    iapply wp_swpF Wp (S := npF s args vs.length) (R := upd rv 1 r) (Mt := M) (pc := nativePrintPC)
      (F := iprop(slot24 sret.toNat ∗ valsImg N (imgM Margs) args.toNat vs ∗ stdioOwn ∗
        consoleOwn (o ++ printArgs st vs) ∗ stackScratch (s - 80#64) printNeed ∗
        NpK Wp Φ N sret args s r vs st o rv ∗ codeRes))
    rotate_left
    · rw [hro, hms]
      iframe Hcode Hsl Hv Hstd Hcon Hst Hk Hpc Hra Hregs HM
    intro F'
    refine np_pro0 hlive h10 h12 h13 h2 (by omega) (by omega) hs4 h0 ?_ ?_
    rotate_left
    · intro _ _ hc; exfalso; apply hc; simp [upd, h12, h0]
    rw [show npF s args 0 = npF s args vs.length by rw [h0]]
    intros
    ix_run1 hlive using [h10, h2] at 0x80002f64
    intros; apply swp_closeF
    dsimp only [F']
    iintro ⟨⟨Hsl, #Hv, Hstd, Hcon, Hst, Hk, #Hcode⟩, Hms⟩
    iapply np_tail Wp c (valueNull_spec hlive Wp N sret) rfl (Margs := Margs)
      (R := upd (upd (upd (upd rv 1 r) 2 (s + 18446744073709551536#64)) 20 sret) 10 sret)
      (M := writeLog (writeLog M [((s + 18446744073709551536#64 + 32#64).toNat, 8, rv 20)])
        [((s + 18446744073709551536#64 + 72#64).toNat, 8, r)]) ?h10 ?h20 ?h2 ?hkeep ?hra ?hs4 ?hargs hdfa
    case h10 => simp [upd, h10]
    case h20 => simp [upd]
    case h2 => simp [upd]
    case hkeep =>
      intro x hx hc hx2 hx20
      have hx1 : x ≠ 1 := fun e => by subst e; revert hx; decide
      have hx10 : x ≠ 10 := fun e => hc (by simp [callerSaved, e])
      simp [upd, hx1, hx2, hx20, hx10]
    case hra =>
      rw [hoff 72 (by omega), hoff 32 (by omega), ldv_store_hit]
    case hs4 =>
      rw [hoff 72 (by omega), hoff 32 (by omega), ldv_store_miss _ _ _ (by simp only [widthOfM]; omega),
        ldv_store_hit]
    case hargs =>
      intro k hk
      have hk' := hdfa k
      simp only [InExt] at hk hk'
      rw [hoff 72 (by omega), hoff 32 (by omega)]
      simp (disch := omega) only [imgM_store_miss]
      exact hMa k hk
    iframe Hcode Hms Hsl Hv Hstd Hcon Hst Hk
  · iapply wp_swpF Wp (S := npF s args vs.length) (R := upd rv 1 r) (Mt := M) (pc := nativePrintPC)
      (F := iprop(NpRest Wp Φ N sret args s r vs st o rv Margs ∗ stdioOwn ∗ consoleOwn o))
    rotate_left
    · rw [hro, hms]
      unfold NpRest
      iframe Hcode Hsl Hv Hd Himg Hstd Hcon Hst Hk Hpc Hra Hregs HM
    intro F'
    refine np_pro hlive h10 h12 h13 h2 (by omega) (by omega) hs4 (by omega) hn ?_
    intros; apply swp_closeF
    dsimp only [F']
    iintro ⟨⟨Hrest, Hstd, Hcon⟩, Hms⟩
    have hvp : ∀ v o', ⊢ valuePrintSpec (vsaModel live) N Wp (s - 80#64) (s - 80#64) v st o' :=
      fun v o' => valuePrint_spec hlive hcl H Wp N _ _ v st o'
    ihave Hcon := (show consoleOwn (GF := GF) o ⊢ consoleOwn (o ++ npOut st vs 0) by
      simp [npOut]) $$ Hcon
    iapply (np_loop Wp c hcl H hvp (Margs := Margs) (st := st) (o := o) (valueNull_spec hlive Wp N sret) rfl (vs.length - 1) 0 (by omega)
      (upd (upd (upd (upd (upd (upd (upd rv 1 r) 2 (s + 18446744073709551536#64)) 20 sret) 8 args)
        19 (BitVec.ofNat 64 vs.length)) 9 0#64) 18 2147596656#64)
      (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog M
        [((s + 18446744073709551536#64 + 32#64).toNat, 8, rv 20)])
        [((s + 18446744073709551536#64 + 72#64).toNat, 8, r)])
        [((s + 18446744073709551536#64 + 64#64).toNat, 8, rv 8)])
        [((s + 18446744073709551536#64 + 56#64).toNat, 8, rv 9)])
        [((s + 18446744073709551536#64 + 48#64).toNat, 8, rv 18)])
        [((s + 18446744073709551536#64 + 40#64).toNat, 8, rv 19)]) ?f)
    case f =>
      refine ⟨by simp [upd], by simp [upd], by simp [upd], by simp [upd], by simp [upd, h10],
        by simp [upd], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx hc hx'
        have hx1 : x ≠ 1 := fun e => by subst e; revert hx; decide
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
        obtain ⟨hx2, hx8, hx9, hx18, hx19, hx20⟩ := hx'
        simp [upd, hx1, hx2, hx8, hx9, hx18, hx19, hx20]
      all_goals first
        | (intro k hk
           have hk' := hdfa k
           simp only [InExt] at hk hk'
           simp only [hoff 72 (by omega), hoff 64 (by omega), hoff 56 (by omega), hoff 48 (by omega),
             hoff 40 (by omega), hoff 32 (by omega)]
           simp (disch := omega) only [imgM_store_miss]
           exact hMa k hk)
        | (simp only [hoff 72 (by omega), hoff 64 (by omega), hoff 56 (by omega), hoff 48 (by omega),
             hoff 40 (by omega), hoff 32 (by omega)]
           simp (disch := (simp only [widthOfM]; omega)) only [ldv_store_miss, ldv_store_hit])
    iframe Hrest Hms Hstd Hcon

end Glue

end VsaIris.Interp
