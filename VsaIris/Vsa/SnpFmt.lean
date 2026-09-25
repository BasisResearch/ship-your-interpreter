import VsaIris.Vsa.SnpSnprintf
import VsaIris.Vsa.Newlib

/-!
# `_svfprintf_r` on any `%s`/`%d` format (lane N2)

`fmtRen g bytes args` is what `_svfprintf_r` prints for the format `bytes`
(`Newlib.parseFmt`: literal bytes, `%s`, `%d`) over the view image `g` and the
`va_list` words `args`: a `%s` argument's C string (`cstrOf`), a `%d`
argument's low word as a signed decimal. `svf_fmt` runs the loop from any
loop head to `_svfprintf_r`'s return by induction on the format, one
`svf_iterS`/`svf_iterD` per conversion and `svf_iterEnd` at the NUL.
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.Interp VsaIris.MallocFast VsaIris.Newlib

/-- A `ld`'s low word, sign-extended, is the `lw` at the same address. -/
theorem lw_of_ld (M : Mem) (a : Nat) : ldv .lw M a = sx32 (ldv .ld M a) := by
  have h8 := toNat_append8 (imgM M) a
  have h4 := toNat_append4 (imgM M) a
  have hs := imgLE_split (imgM M) a 4 4
  have hl := imgLE_lt (imgM M) (a + 4) 4
  simp only [ldv, bytesVal, bytesAt, widthOfM, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, sx32,
    Nat.add_zero]
  simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, h8, h4, show (8 : Nat) = 4 + 4 from rfl, hs]
  have hl4 := imgLE_lt (imgM M) a 4
  simp only [show (256 : Nat) ^ 4 = 2 ^ 32 by decide] at hl4 ⊢
  omega

/-! ## The rendering -/

/-- The C string at `a` in `g`, within `fuel` bytes. -/
def cstrOf (g : Nat → BitVec 8) (a : Nat) : Nat → List (BitVec 8)
  | 0 => []
  | f + 1 => if g a = 0#8 then [] else g a :: cstrOf g (a + 1) f

theorem cstrOf_eq (g : Nat → BitVec 8) : ∀ (len a f : Nat), (∀ i, i < len → g (a + i) ≠ 0#8) →
    g (a + len) = 0#8 → len < f → cstrOf g a f = pieceBytes g a len
  | 0, a, f + 1, _, hz, _ => by simp [cstrOf, pieceBytes, show g a = 0#8 from hz]
  | len + 1, a, f + 1, hnz, hz, hf => by
    have h0 : g a ≠ 0#8 := by simpa using hnz 0 (by omega)
    rw [cstrOf, if_neg h0, cstrOf_eq g len (a + 1) f (fun i hi => by
      rw [show a + 1 + i = a + (i + 1) by omega]; exact hnz _ (by omega))
      (by rw [show a + 1 + len = a + (len + 1) by omega]; exact hz) (by omega)]
    simp only [pieceBytes, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, Nat.succ_eq_add_one]
    congr 1; omega
  | _, _, 0, _, _, hf => absurd hf (by omega)

/-- `_svfprintf_r`'s output for a `%s`/`%d` format over the view image `g`
and the argument words. -/
def fmtRen (g : Nat → BitVec 8) : List (BitVec 8) → List (BitVec 64) → List (BitVec 8)
  | [], _ => []
  | b :: rest, args =>
    if b = 0x25#8 then
      match rest with
      | [] => []
      | c :: r =>
        (if c = 0x73#8 then cstrOf g (args.headD 0).toNat (2 ^ 32)
          else strBytes (Vsa.While.intToString (sx32 (args.headD 0)).toInt)) ++ fmtRen g r args.tail
    else b :: fmtRen g rest args

theorem fmtRen_cons (g : Nat → BitVec 8) (args : List (BitVec 64)) {b : BitVec 8}
    (rest : List (BitVec 8)) (h : b ≠ 0x25#8) : fmtRen g (b :: rest) args = b :: fmtRen g rest args := by
  rw [fmtRen.eq_def]; dsimp only; rw [if_neg h]

theorem fmtRen_lit (g : Nat → BitVec 8) (args : List (BitVec 64)) :
    ∀ (lit x : List (BitVec 8)), (∀ b ∈ lit, b ≠ 0x25#8) → fmtRen g (lit ++ x) args = lit ++ fmtRen g x args
  | [], _, _ => rfl
  | b :: l, x, h => by
    rw [List.cons_append, fmtRen_cons g args _ (h b List.mem_cons_self),
      fmtRen_lit g args l x fun c hc => h c (List.mem_cons_of_mem _ hc), List.cons_append]

theorem fmtRen_lit_all (g : Nat → BitVec 8) (args : List (BitVec 64)) (lit : List (BitVec 8))
    (h : ∀ b ∈ lit, b ≠ 0x25#8) : fmtRen g lit args = lit := by
  have := fmtRen_lit g args lit [] h
  simpa [fmtRen] using this

theorem fmtRen_conv (g : Nat → BitVec 8) (c : BitVec 8) (r : List (BitVec 8)) (a : BitVec 64)
    (args : List (BitVec 64)) :
    fmtRen g (0x25#8 :: c :: r) (a :: args) =
      (if c = 0x73#8 then cstrOf g a.toNat (2 ^ 32)
        else strBytes (Vsa.While.intToString (sx32 a).toInt)) ++ fmtRen g r args := by
  simp [fmtRen]

theorem parseFmt_lit : ∀ (lit x : List (BitVec 8)), (∀ b ∈ lit, b ≠ 0x25#8) →
    parseFmt (lit ++ x) = parseFmt x
  | [], _, _ => rfl
  | b :: l, x, h => by
    have e : parseFmt (b :: (l ++ x)) = parseFmt (l ++ x) := by
      rw [parseFmt.eq_def]; dsimp only; rw [if_neg (h b List.mem_cons_self)]
    rw [List.cons_append, e]
    exact parseFmt_lit l x fun c hc => h c (List.mem_cons_of_mem _ hc)

/-- A format is a literal run, or a literal run then `'%'`. -/
theorem fmt_split : ∀ (bs : List (BitVec 8)), (∀ b ∈ bs, b ≠ 0x25#8) ∨
    ∃ lit x, bs = lit ++ 0x25#8 :: x ∧ ∀ b ∈ lit, b ≠ 0x25#8
  | [] => .inl (by simp)
  | b :: bs => by
    by_cases hb : b = 0x25#8
    · exact .inr ⟨[], bs, by simp [hb], by simp⟩
    · rcases fmt_split bs with h | ⟨lit, x, rfl, hl⟩
      · refine .inl fun c hc => ?_
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hb
        · exact h c hc
      · refine .inr ⟨b :: lit, x, rfl, fun c hc => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hb
        · exact hl c hc

/-! ## The loop's inputs -/

/-- The format's remaining bytes `bs` at `q` in the view, then the NUL. -/
structure FmtAt (Dt : Mem) (DA : List Nat) (q : Nat) (bs : List (BitVec 8)) : Prop where
  bytes : ∀ i (h : i < bs.length), imgM Dt (q + i) = bs[i] ∧ bs[i] ≠ 0#8
  nul : imgM Dt (q + bs.length) = 0#8
  geom : FmtGeom DA q bs.length

theorem FmtAt.drop {Dt : Mem} {DA : List Nat} {q : Nat} {l1 l2 : List (BitVec 8)}
    (F : FmtAt Dt DA q (l1 ++ l2)) : FmtAt Dt DA (q + l1.length) l2 where
  bytes i h := by
    have := F.bytes (l1.length + i) (by simp; omega)
    rw [List.getElem_append_right (by omega)] at this
    simpa [Nat.add_assoc] using this
  nul := by have := F.nul; simpa [Nat.add_assoc] using this
  geom := by
    have G := F.geom
    simp only [List.length_append] at G
    exact ⟨fun b h1 h2 => G.dom b (by omega) (by omega), by have := G.lo; omega,
      by have := G.hi; omega, by have := G.htif; omega⟩

theorem FmtGeom.mono {DA : List Nat} {q k k' : Nat} (G : FmtGeom DA q k) (h : k' ≤ k) :
    FmtGeom DA q k' :=
  ⟨fun b h1 h2 => G.dom b h1 (by omega), G.lo, by have := G.hi; omega, by have := G.htif; omega⟩

/-- A literal run's bytes are its pieces. -/
theorem FmtAt.lit {Dt : Mem} {DA : List Nat} {q : Nat} {lit x : List (BitVec 8)}
    (F : FmtAt Dt DA q (lit ++ x)) (hl : ∀ b ∈ lit, b ≠ 0x25#8) :
    pieceBytes (imgM Dt) q lit.length = lit ∧
      ∀ i, i < lit.length → imgM Dt (q + i) ≠ 0#8 ∧ imgM Dt (q + i) ≠ 37#8 := by
  have hb : ∀ i (h : i < lit.length), imgM Dt (q + i) = lit[i] ∧ lit[i] ≠ 0#8 := fun i h => by
    have := F.bytes i (by simp; omega)
    rwa [List.getElem_append_left h] at this
  refine ⟨List.ext_getElem (by simp) fun i h1 h2 => ?_, fun i hi => ?_⟩
  · simp only [pieceBytes, List.getElem_map, List.getElem_range]
    exact (hb i h2).1
  · rw [(hb i hi).1]
    exact ⟨(hb i hi).2, hl _ (List.getElem_mem hi)⟩

/-- The `va_list`'s words from `ap`. -/
def ArgsAt (Mt0 : Mem) (ap : Nat) (args : List (BitVec 64)) : Prop :=
  ∀ i (h : i < args.length), ldv .ld Mt0 (BitVec.ofNat 64 (ap + 8 * i)).toNat = args[i]

theorem ArgsAt.tail {Mt0 : Mem} {ap : Nat} {a : BitVec 64} {args : List (BitVec 64)}
    (h : ArgsAt Mt0 ap (a :: args)) : ArgsAt Mt0 (ap + 8) args := fun i hi => by
  have := h (i + 1) (by simp; omega)
  simpa [show ap + 8 * (i + 1) = ap + 8 + 8 * i by omega] using this

/-- Every `%s` argument is a C string of the view. -/
def StrArgs (Dt : Mem) (DA : List Nat) (cs : List Conv) (args : List (BitVec 64)) : Prop :=
  ∀ i (h : i < cs.length) (h' : i < args.length), cs[i] = .str → ∃ len, DStr Dt DA (args[i]).toNat len

theorem StrArgs.tail {Dt : Mem} {DA : List Nat} {c : Conv} {cs : List Conv} {a : BitVec 64}
    {args : List (BitVec 64)} (h : StrArgs Dt DA (c :: cs) (a :: args)) : StrArgs Dt DA cs args :=
  fun i h1 h2 hc => h (i + 1) (by simp; omega) (by simp; omega) (by simpa using hc)

/-! ## The loop -/

/-- **`_svfprintf_r`'s loop on a `%s`/`%d` format** (`0x80007720` → the
return): the remaining format `bs` at `q`, the remaining `va_list` words at
`ap`, the stream `tot` printed so far. -/
theorem svf_fmt {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} (SG : SnpGeom s dst n) (DO : DataOff Dt DA s dst n)
    (hmb : ldv .ld Mt0 0x8001b880 = 0x80012268#64) (hmx : ldv .lbu Mt0 0x8001b8f8 = 1#64)
    (hal : (R0 1).toNat % 4 = 0) :
    ∀ (m : Nat) (bs : List (BitVec 8)) (q ap : Nat) (args : List (BitVec 64)) (cs : List Conv)
      (tot : List (BitVec 8)) (R : Nat → BitVec 64) (Mt : Mem), bs.length ≤ m →
      FmtAt Dt DA q bs → parseFmt bs = some cs → cs.length ≤ args.length →
      ArgsAt Mt0 ap args → s - 40 ≤ ap → ap + 8 * args.length ≤ s → StrArgs Dt DA cs args →
      (tot ++ fmtRen (imgM Dt) bs args).length + 21 < 2 ^ 31 →
      SvfAt s dst n R0 Mt0 q ap (BitVec.ofNat 64 tot.length) tot R Mt →
      SvfRetK live Dt DA Q s dst n R0 Mt0 (BitVec.ofNat 64 (tot ++ fmtRen (imgM Dt) bs args).length)
        (tot ++ fmtRen (imgM Dt) bs args) →
      NW live Dt DA (snpS s dst n) Q 0x80007720#64 R Mt := by
  intro m
  induction m with
  | zero =>
    intro bs q ap args cs tot R Mt hm F _ _ _ _ _ _ hlen A hret
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    refine svf_iterEnd hlive R Mt SG DO hmb hmx A 0 F.geom (fun i hi => absurd hi (by omega))
      (by simpa using F.nul) (by simp [fmtRen] at hlen; omega) hal ?_
    simpa [fmtRen, pieceBytes_zero] using hret
  | succ m IH =>
    intro bs q ap args cs tot R Mt hm F hp hcs HA hap1 hap2 HS hlen A hret
    rcases fmt_split bs with hl | ⟨lit, x, rfl, hl⟩
    · -- no conversion left: the literal run and the NUL
      have hr := fmtRen_lit_all (imgM Dt) args bs hl
      obtain ⟨hpb, hb⟩ := (show FmtAt Dt DA q (bs ++ []) by simpa using F).lit hl
      rw [hr] at hlen hret
      refine svf_iterEnd hlive R Mt SG DO hmb hmx A bs.length F.geom (fun i hi => hb i hi)
        F.nul (by simp at hlen; omega) hal ?_
      rw [hpb]; simpa using hret
    · obtain ⟨hpb, hb⟩ := F.lit hl
      rw [parseFmt_lit lit _ hl] at hp
      have Fx := F.drop
      rcases x with _ | ⟨c, r⟩
      · simp [parseFmt] at hp
      simp only [parseFmt, ite_true] at hp
      have hk := Fx.bytes 0 (by simp)
      have hk1 := Fx.bytes 1 (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at hk hk1
      have Fr : FmtAt Dt DA (q + lit.length + 2) r := by
        have := (show FmtAt Dt DA (q + lit.length) ([0x25#8, c] ++ r) by simpa using Fx).drop
        simpa [Nat.add_assoc] using this
      have hG : FmtGeom DA q (lit.length + 1) := F.geom.mono (by simp)
      have hrl : r.length ≤ m := by simp at hm; omega
      rw [fmtRen_lit _ _ _ _ hl] at hlen hret
      by_cases hs' : c = 0x73#8
      · subst hs'
        simp only [ite_true] at hp
        obtain ⟨cs', hp', rfl⟩ : ∃ cs', parseFmt r = some cs' ∧ cs = .str :: cs' := by
          cases h : parseFmt r <;> simp_all
        rcases args with _ | ⟨a, args⟩
        · simp at hcs
        obtain ⟨len, hstr⟩ := HS 0 (by simp) (by simp) rfl
        have hcs' : cstrOf (imgM Dt) a.toNat (2 ^ 32) = pieceBytes (imgM Dt) a.toNat len :=
          cstrOf_eq _ len a.toNat _ hstr.nz hstr.nul (by have := hstr.hi; omega)
        rw [fmtRen_conv, if_pos rfl, hcs'] at hlen hret
        have hv : ldv .ld Mt0 (BitVec.ofNat 64 ap).toNat = BitVec.ofNat 64 a.toNat := by
          have := HA 0 (by simp); simpa using this
        refine svf_iterS hlive R Mt SG DO hmb hmx A lit.length hG hb hk.1 hk1.1 a.toNat len hv hap1
          (by simp at hap2; omega) hstr (by simp at hlen; omega) fun R' Mt' A' => ?_
        rw [hpb] at A'
        refine IH r (q + lit.length + 2) (ap + 8) args cs' (tot ++ lit ++ pieceBytes (imgM Dt) a.toNat len)
          R' Mt' hrl Fr hp' (by simp at hcs; omega) HA.tail (by omega) (by simp at hap2; omega) HS.tail
          (by simp at hlen ⊢; omega) (by simpa [Nat.add_assoc] using A') ?_
        simpa [List.append_assoc] using hret
      · have hd' : c = 0x64#8 := by
          if h : c = 0x64#8 then exact h else simp [hs', h] at hp
        subst hd'
        simp only [show (0x64#8 : BitVec 8) ≠ 0x73#8 by decide, ite_false, ite_true] at hp
        obtain ⟨cs', hp', rfl⟩ : ∃ cs', parseFmt r = some cs' ∧ cs = .int :: cs' := by
          cases h : parseFmt r <;> simp_all
        rcases args with _ | ⟨a, args⟩
        · simp at hcs
        rw [fmtRen_conv, if_neg (by decide)] at hlen hret
        have hv : ldv .lw Mt0 (BitVec.ofNat 64 ap).toNat = sx32 a := by
          rw [lw_of_ld]; have := HA 0 (by simp); simp only [Nat.mul_zero, Nat.add_zero] at this; rw [this]; rfl
        refine svf_iterD hlive R Mt SG DO hmb hmx A lit.length hG hb hk.1 hk1.1 (sx32 a) hv hap1
          (by simp at hap2; omega) (by simp at hlen; omega) fun R' Mt' A' => ?_
        rw [hpb] at A'
        refine IH r (q + lit.length + 2) (ap + 8) args cs'
          (tot ++ lit ++ strBytes (Vsa.While.intToString (sx32 a).toInt))
          R' Mt' hrl Fr hp' (by simp at hcs; omega) HA.tail (by omega) (by simp at hap2; omega)
          (fun i h1 h2 hc => HS (i + 1) (by simp; omega) (by simp; omega) (by simpa using hc))
          (by simp at hlen ⊢; omega) (by simpa [Nat.add_assoc] using A') ?_
        simpa [List.append_assoc] using hret


/-- **A `%s`/`%d` format's whole loop**: from the loop head with nothing
printed to `_svfprintf_r`'s return with the rendering `fmtRen`. -/
theorem loop_fmt {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (SG : SnpGeom s dst n) (DO : DataOff Dt DA s dst n)
    (hmb : ldv .ld Mt0 0x8001b880 = 0x80012268#64) (hmx : ldv .lbu Mt0 0x8001b8f8 = 1#64)
    (hal : (R0 1).toNat % 4 = 0) (p ap : Nat) (bs : List (BitVec 8)) (cs : List Conv)
    (args : List (BitVec 64)) (F : FmtAt Dt DA p bs) (hp : parseFmt bs = some cs)
    (hcs : cs.length ≤ args.length) (HA : ArgsAt Mt0 ap args) (hap1 : s - 40 ≤ ap)
    (hap2 : ap + 8 * args.length ≤ s) (HS : StrArgs Dt DA cs args)
    (hlen : (fmtRen (imgM Dt) bs args).length + 21 < 2 ^ 31) :
    SvfLoopRun live Dt DA Q s dst n R0 Mt0 p ap (fmtRen (imgM Dt) bs args) := by
  intro R Mt A hret
  exact svf_fmt hlive SG DO hmb hmx hal bs.length bs p ap args cs [] R Mt (Nat.le_refl _) F hp hcs HA
    hap1 hap2 HS (by simpa using hlen) (by simpa using A) (by simpa using hret)

/-- The rendering is at most the format plus `B` per conversion, for `%s`
strings of at most `B` bytes. -/
theorem fmtRen_length_le (g : Nat → BitVec 8) (B : Nat) (hB : 20 ≤ B) :
    ∀ (m : Nat) (bs : List (BitVec 8)) (cs : List Conv) (args : List (BitVec 64)), bs.length ≤ m →
      parseFmt bs = some cs → cs.length ≤ args.length →
      (∀ i (h : i < cs.length) (h' : i < args.length), cs[i] = .str →
        (cstrOf g (args[i]).toNat (2 ^ 32)).length ≤ B) →
      (fmtRen g bs args).length ≤ bs.length + cs.length * B := by
  intro m
  induction m with
  | zero =>
    intro bs cs args hm hp _ _
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    simp [fmtRen]
  | succ m IH =>
    intro bs cs args hm hp hcs hS
    rcases fmt_split bs with hl | ⟨lit, x, rfl, hl⟩
    · rw [fmtRen_lit_all g args bs hl]; omega
    · rw [parseFmt_lit lit _ hl] at hp
      rw [fmtRen_lit g args lit _ hl]
      rcases x with _ | ⟨c, r⟩
      · simp [parseFmt] at hp
      simp only [parseFmt, ite_true] at hp
      rcases args with _ | ⟨a, args⟩
      · have : cs ≠ [] := by
          intro h; subst h
          by_cases hs : c = 0x73#8 <;> simp_all <;> (by_cases hd : c = 0x64#8 <;> simp_all)
        cases cs with
        | nil => exact absurd rfl this
        | cons _ _ => simp at hcs
      rw [fmtRen_conv]
      have hrl : r.length ≤ m := by simp at hm; omega
      by_cases hs : c = 0x73#8
      · subst hs
        simp only [ite_true] at hp
        obtain ⟨cs', hp', rfl⟩ : ∃ cs', parseFmt r = some cs' ∧ cs = .str :: cs' := by
          cases h : parseFmt r <;> simp_all
        have h1 := hS 0 (by simp) (by simp) rfl
        have h2 := IH r cs' args hrl hp' (by simp at hcs; omega)
          (fun i h h' hc => hS (i + 1) (by simp; omega) (by simp; omega) (by simpa using hc))
        simp only [ite_true, List.length_append, List.length_cons] at h1 h2 ⊢
        simp only [List.getElem_cons_zero] at h1
        rw [Nat.succ_mul]
        omega
      · obtain ⟨cs', hp', rfl⟩ : ∃ cs', parseFmt r = some cs' ∧ cs = .int :: cs' := by
          if hd : c = 0x64#8 then
            subst hd; simp only [show (0x64#8 : BitVec 8) ≠ 0x73#8 by decide, ite_false, ite_true] at hp
            cases h : parseFmt r <;> simp_all
          else simp [hs, hd] at hp
        have h1 := intToString_length_le (sx32 a)
        have h2 := IH r cs' args hrl hp' (by simp at hcs; omega)
          (fun i h h' hc => hS (i + 1) (by simp; omega) (by simp; omega) (by simpa using hc))
        simp only [hs, ite_false, List.length_append, List.length_cons] at h2 ⊢
        rw [Nat.succ_mul]
        omega

end VsaIris.Sym
