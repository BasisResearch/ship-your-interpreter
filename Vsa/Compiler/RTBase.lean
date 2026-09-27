import Vsa.Compiler.RTCode
import Vsa.Compiler.PrintInt

/-!
# Proof support for the runtime

Register frames (`Keep`), aligned doubleword memory (`rdW_upd`), string objects
(`StrW`), the `wp_simp` normal form for `WP` goals, and entry points into a
routine's code at an interior label (`Seg.drop`).
-/

namespace Vsa.Compiler

open Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-! ## Segments -/

theorem Seg.drop {code : List Ins} {pos : Nat} {c : List Ins} (h : Seg code pos c) (k : Nat) :
    Seg code (pos + k) (c.drop k) := by
  intro j hj
  simp only [List.length_drop] at hj
  rw [Nat.add_assoc, h (k + j) (by omega)]
  simp

/-- Run a routine's code from its interior label `k`. -/
theorem run_at {code : List Ins} {P : AM → Prop} (hfit : Fits code) {b : Nat} {c : List Ins}
    (hseg : Seg code b c) (k : Nat) {L : GRegs} {m : Mem} {o : Array String}
    (h : WP code P (b + k) (c.drop k) (fun _ _ _ => False) L m o) :
    Reaches code ⟨pcOf (b + k), L, m, o⟩ P :=
  WP_sound hfit _ _ _ L m o (hseg.drop k) (fun _ _ _ h => h.elim) h

/-- `run_at` with the label written as an absolute index. -/
theorem run_at' {code : List Ins} {P : AM → Prop} (hfit : Fits code) {b : Nat} {c : List Ins}
    (hseg : Seg code b c) (k j : Nat) (hj : b + k = j) {L : GRegs} {m : Mem} {o : Array String}
    (h : WP code P j (c.drop k) (fun _ _ _ => False) L m o) :
    Reaches code ⟨pcOf j, L, m, o⟩ P := by
  subst hj; exact run_at hfit hseg k h

theorem sext_zero12 : (sign_extend (0 : BitVec 12) : BitVec 64) = 0 := by decide

theorem zero_add64 (x : BitVec 64) : 0#64 + x = x := by simp

theorem zero_add64' (x : BitVec 64) : (0 : BitVec 64) + x = x := by simp

theorem toNat_ofNat6 (k : Nat) : (BitVec.ofNat 6 k).toNat = k % 64 := by simp

theorem natCast_lit (n : Nat) : ((no_index (OfNat.ofNat n : Nat)) : Int) = (OfNat.ofNat n : Int) := rfl

theorem add_zero64 (x : BitVec 64) : x + (0 : BitVec 64) = x := by simp

theorem ofNat_add_lit (a k : Nat) (hk : k < 2 ^ 63) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 k = BitVec.ofNat 64 (a + k) := BitVec.ofNat_add_ofNat ..

theorem shl_ofNat (n k : Nat) : (BitVec.ofNat 64 n) <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod]

theorem ofNat_add_neg (a k : Nat) (hk : 2 ^ 63 ≤ k ∧ k < 2 ^ 64) (ha : 2 ^ 64 - k ≤ a) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 k = BitVec.ofNat 64 (a - (2 ^ 64 - k)) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem sext_lo (n : Nat) (h : n < 2048) :
    (sign_extend (BitVec.ofNat 12 n) : BitVec 64) = BitVec.ofNat 64 n := by
  have := sext12_ofInt (n : Int) (by omega) (by omega)
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast] at this; exact this

theorem sext_hi (n : Nat) (h1 : 2048 ≤ n) (h2 : n < 4096) :
    (sign_extend (BitVec.ofNat 12 n) : BitVec 64) = BitVec.ofNat 64 (n + (2 ^ 64 - 4096)) := by
  have e : BitVec.ofNat 12 n = BitVec.ofInt 12 ((n : Int) - 4096) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega
  rw [e, sext12_ofInt _ (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega

theorem toInt_ofNat_small (n : Nat) (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega

theorem toInt_ofNat_big (n : Nat) (h1 : 2 ^ 63 ≤ n) (h2 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toInt = (n : Int) - 2 ^ 64 := by
  rw [BitVec.toInt_eq_toNat_bmod]; simp [Int.bmod]; omega

/-- Run the `n` instructions at label `k` of a routine, then continue with `K`. -/
theorem run_block {code : List Ins} {P : AM → Prop} (hfit : Fits code) {b : Nat} {c : List Ins}
    (hseg : Seg code b c) (k n j : Nat) (hj : b + k = j)
    {KP : GRegs → Mem → Array String → Prop}
    (hK : ∀ L m o, KP L m o → Reaches code ⟨pcOf (j + n), L, m, o⟩ P)
    (hn : n ≤ (c.drop k).length)
    {L : GRegs} {m : Mem} {o : Array String}
    (h : WP code P j ((c.drop k).take n) KP L m o) :
    Reaches code ⟨pcOf j, L, m, o⟩ P := by
  subst hj
  have hs : Seg code (b + k) ((c.drop k).take n) := by
    have := (hseg.drop k)
    intro i hi
    simp only [List.length_take] at hi
    rw [this i (by omega)]
    simp [List.getElem?_take, show i < n by omega]
  have hlen : ((c.drop k).take n).length = n := by
    rw [List.length_take]; exact Nat.min_eq_left hn
  exact WP_sound hfit _ _ _ L m o hs (fun L' m' o' h' => by rw [hlen]; exact hK L' m' o' h') h

theorem reach_here {code : List Ins} {A : AM} {Q : AM → Prop} (h : Q A) : Reaches code A Q :=
  ⟨A, Star.refl _ _, h⟩

theorem reaches_mono {code : List Ins} {A : AM} {P Q : AM → Prop} (h : Reaches code A P)
    (hPQ : ∀ B, P B → Q B) : Reaches code A Q := by
  obtain ⟨B, s, hp⟩ := h; exact ⟨B, s, hPQ B hp⟩

/-- The console text of an output array. -/
def ostr (o : Array String) : String := String.join o.toList

theorem ostr_push (o : Array String) (s : String) : ostr (o.push s) = ostr o ++ s := by
  simp [ostr, String.join_append]

theorem toString_char (c : Char) : toString c = String.ofList [c] :=
  String.toList_inj.mp (by rw [String.toList_ofList]; exact String.toList_singleton c)

/-! ## Register frames -/

/-- `L'` agrees with `L` outside the registers `S`. -/
def Keep (S : List Nat) (L L' : GRegs) : Prop := ∀ r, r ∉ S → lookupG r L' = lookupG r L

theorem Keep.refl (S : List Nat) (L : GRegs) : Keep S L L := fun _ _ => rfl

theorem Keep.trans {S : List Nat} {L L' L'' : GRegs} (h1 : Keep S L L') (h2 : Keep S L' L'') :
    Keep S L L'' := fun r hr => (h2 r hr).trans (h1 r hr)

theorem Keep.mono {S S' : List Nat} {L L' : GRegs} (h : Keep S L L') (hs : ∀ r ∈ S, r ∈ S') :
    Keep S' L L' := fun r hr => h r (fun h' => hr (hs r h'))

theorem Keep.gset {S : List Nat} {L L' : GRegs} {rd : Nat} {v : BitVec 64} (h : Keep S L L')
    (hrd : rd ∈ S) : Keep S L (gset L' rd v) := fun r hr => by
  rw [lookupG_set, if_neg (fun e => hr (by rw [e]; exact hrd))]; exact h r hr

theorem Keep.lib {S : List Nat} {L L' : GRegs} {v : BitVec 64} (h : Keep S L L')
    (hs : ∀ r ∈ clobbered, r ∈ S) : Keep S L ((10, v) :: eraseAll clobbered L') := fun r hr => by
  have h10 : r ≠ 10 := fun e => hr (hs r (by subst e; simp [clobbered]))
  simp only [lookupG, if_neg (Ne.symm h10)]
  rw [lookupG_eraseAll, if_neg (fun h' => hr (hs r h'))]
  exact h r hr

theorem Keep.has {S : List Nat} {L L' : GRegs} (h : Keep S L L') {r : Nat} {v : BitVec 64}
    (hr : r ∉ S) (hv : Has L r v) : Has L' r v := by
  obtain ⟨h31, (⟨rfl, rfl⟩ | ⟨hne, hl⟩)⟩ := hv
  · exact Has.zero _
  · exact ⟨h31, .inr ⟨hne, by rw [h r hr, hl]⟩⟩

theorem has_gset {L : GRegs} {rd n : Nat} {v w : BitVec 64} (h : 1 ≤ rd ∧ rd ≤ 31) :
    Has (gset L rd v) n w ↔ if n = rd then v = w else Has L n w := by
  split
  · next e => subst e; exact ⟨fun h' => by
      have := (Has.set_self L v h.1 h.2).src.2; rw [← this]; exact h'.src.2, fun e' => e' ▸ Has.set_self L v h.1 h.2⟩
  · next e =>
    constructor
    · intro h'
      obtain ⟨h31, (⟨rfl, rfl⟩ | ⟨hne, hl⟩)⟩ := h'
      · exact Has.zero _
      · exact ⟨h31, .inr ⟨hne, by rw [lookupG_set, if_neg e] at hl; exact hl⟩⟩
    · intro h'; exact h'.set_other e

theorem keep_gset {S : List Nat} {L L' : GRegs} {rd : Nat} {v : BitVec 64} (h : rd ∈ S) :
    Keep S L (gset L' rd v) ↔ Keep S L L' := by
  constructor
  · intro hk r hr
    have := hk r hr
    rw [lookupG_set, if_neg (fun e => hr (by rw [e]; exact h))] at this
    exact this
  · intro hk; exact hk.gset h

theorem libc_length (pos tgt : Nat) : (libc pos tgt).length = 3 := rfl

theorem libRes_mulE (x y : BitVec 64) : libRes mulPC x y = some (x * y) := by simp [libRes]

theorem libRes_divE (x y : BitVec 64) (h : y.toInt ≠ 0) :
    libRes divPC x y = some (BitVec.ofInt 64 (x.toInt.tdiv y.toInt)) := by
  simp [libRes, show divPC ≠ mulPC by decide, h]

theorem libRes_modE (x y : BitVec 64) (h : y.toInt ≠ 0) :
    libRes modPC x y = some (BitVec.ofInt 64 (x.toInt.tmod y.toInt)) := by
  simp [libRes, show modPC ≠ mulPC by decide, show modPC ≠ divPC by decide, h]

theorem keysG_lib (L : GRegs) (r : BitVec 64) (n : Nat) :
    n ∈ keysG ((10, r) :: eraseAll clobbered L) ↔ n = 10 ∨ (n ∉ clobbered ∧ n ∈ keysG L) := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := mem_keysG_lookup h
    simp only [lookupG] at hv
    by_cases h10 : n = 10
    · exact .inl h10
    · rw [if_neg (Ne.symm h10), lookupG_eraseAll] at hv
      split at hv
      · cases hv
      · next hc => exact .inr ⟨hc, mem_keysG_of_lookup hv⟩
  · rintro (h | ⟨hc, h⟩)
    · subst h; simp [keysG]
    · obtain ⟨v, hv⟩ := mem_keysG_lookup h
      exact mem_keysG_of_lookup (v := v) (by
        by_cases h10 : n = 10
        · subst h10; simp [clobbered] at hc
        · simp only [lookupG, if_neg (Ne.symm h10)]; rw [lookupG_eraseAll, if_neg hc, hv])

theorem keysG_lib' (L : GRegs) (r : BitVec 64) (n : Nat) (hn : n ∉ clobbered) :
    n ∈ keysG ((10, r) :: eraseAll clobbered L) ↔ n ∈ keysG L := by
  rw [keysG_lib]; constructor
  · rintro (h | ⟨-, h⟩)
    · subst h; simp [clobbered] at hn
    · exact h
  · intro h; exact .inr ⟨hn, h⟩

theorem keysG_lib10 (L : GRegs) (r : BitVec 64) : 10 ∈ keysG ((10, r) :: eraseAll clobbered L) :=
  (keysG_lib L r 10).mpr (.inl rfl)

theorem srcVal_lib (L : GRegs) (r : BitVec 64) (n : Nat) (hn : n ∉ clobbered) :
    srcVal n ((10, r) :: eraseAll clobbered L) = srcVal n L := by
  have h10 : n ≠ 10 := fun e => hn (by subst e; simp [clobbered])
  cases n with
  | zero => rfl
  | succ k =>
    simp only [srcVal, lookupG, if_neg (Ne.symm h10)]
    rw [lookupG_eraseAll, if_neg hn]

theorem srcVal_lib10 (L : GRegs) (r : BitVec 64) : srcVal 10 ((10, r) :: eraseAll clobbered L) = r := by
  simp [srcVal, lookupG]

theorem has_lib {L : GRegs} {r w : BitVec 64} {n : Nat} (hn : n ∉ clobbered) :
    Has ((10, r) :: eraseAll clobbered L) n w ↔ Has L n w := by
  have h10 : n ≠ 10 := fun e => hn (by subst e; simp [clobbered])
  simp only [Has, lookupG, if_neg (Ne.symm h10), lookupG_eraseAll, if_neg hn]

theorem has_lib10 {L : GRegs} {r w : BitVec 64} :
    Has ((10, r) :: eraseAll clobbered L) 10 w ↔ r = w := by
  simp [Has, lookupG]

theorem keep_lib {S : List Nat} {L0 L : GRegs} {r : BitVec 64} (hs : ∀ n ∈ clobbered, n ∈ S) :
    Keep S L0 ((10, r) :: eraseAll clobbered L) ↔ Keep S L0 L := by
  constructor
  · intro hk n hn
    have := hk n hn
    have hc : n ∉ clobbered := fun h => hn (hs n h)
    have h10 : n ≠ 10 := fun e => hc (by subst e; simp [clobbered])
    simp only [lookupG, if_neg (Ne.symm h10), lookupG_eraseAll, if_neg hc] at this
    exact this
  · intro hk; exact hk.lib hs

theorem has_mem {L : GRegs} {n : Nat} {v : BitVec 64} (h : Has L n v) (hn : n ≠ 0) :
    n ∈ keysG L := by
  obtain ⟨-, (⟨rfl, -⟩ | ⟨-, hl⟩)⟩ := h
  · exact absurd rfl hn
  · exact mem_keysG_of_lookup hl

/-! ## Aligned doublewords -/

theorem rdW_upd {m : Mem} {a b : Nat} {v : BitVec 64} (ha : a % 8 = 0) (hb : b % 8 = 0) :
    rdW (applyW m (a, 8, v)) b = if b = a then v else rdW m b := by
  split
  · next h => subst h; exact rdW_write m b v
  · next h => exact rdW_write_other m b a v (by omega)

/-- `m'` agrees with `m` on the aligned words of `[lo, hi)`. -/
def Agree (m m' : Mem) (lo hi : Nat) : Prop :=
  ∀ a, lo ≤ a → a + 8 ≤ hi → a % 8 = 0 → rdW m' a = rdW m a

theorem Agree.refl (m : Mem) (lo hi : Nat) : Agree m m lo hi := fun _ _ _ _ => rfl

theorem Agree.trans {m m' m'' : Mem} {lo hi : Nat} (h1 : Agree m m' lo hi) (h2 : Agree m' m'' lo hi) :
    Agree m m'' lo hi := fun a h h' h'' => (h2 a h h' h'').trans (h1 a h h' h'')

theorem Agree.mono {m m' : Mem} {lo hi lo' hi' : Nat} (h : Agree m m' lo hi) (h1 : lo ≤ lo')
    (h2 : hi' ≤ hi) : Agree m m' lo' hi' := fun a ha hb hc => h a (by omega) (by omega) hc

theorem Agree.upd_out {m : Mem} {lo hi a : Nat} {v : BitVec 64} (ha : a % 8 = 0)
    (hout : a + 8 ≤ lo ∨ hi ≤ a) : Agree m (applyW m (a, 8, v)) lo hi := fun b h1 h2 h3 => by
  rw [rdW_upd ha h3, if_neg (by omega)]

/-- Memory after copying the first `k` words from `s` to `d`. -/
def copyW (m : Mem) (s d : Nat) : Nat → Mem
  | 0 => m
  | k + 1 => applyW (copyW m s d k) (d + 8 * k, 8, rdW m (s + 8 * k))

theorem rdW_copyW (m : Mem) (s d : Nat) (hd : d % 8 = 0) : ∀ (k a : Nat), a % 8 = 0 →
    rdW (copyW m s d k) a = if d ≤ a ∧ a < d + 8 * k then rdW m (s + (a - d)) else rdW m a
  | 0, a, _ => by rw [if_neg (by omega)]; rfl
  | k + 1, a, ha => by
    simp only [copyW]
    rw [rdW_upd (by omega) ha, rdW_copyW m s d hd k a ha]
    by_cases h1 : a = d + 8 * k
    · subst h1; simp only [if_true]
      rw [if_pos (by omega)]; congr 1; omega
    · rw [if_neg h1]
      by_cases h2 : d ≤ a ∧ a < d + 8 * k
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem toNat_ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat]; omega

theorem ofNat_ne_zero {x : Nat} (h0 : 0 < x) (h : x < 2 ^ 64) : BitVec.ofNat 64 x ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [toNat_ofNat_lt h] at this
  simp at this; omega

/-- Three-way lexicographic comparison of character lists. -/
def cmpL : List Char → List Char → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a.toNat < b.toNat then -1 else if b.toNat < a.toNat then 1 else cmpL as bs

theorem take_succ_eq {xs ys : List Char} {i : Nat} (h : xs.take i = ys.take i) (hx : i < xs.length)
    (hy : i < ys.length) (he : xs[i] = ys[i]) : xs.take (i + 1) = ys.take (i + 1) := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hy,
    h, he]

theorem cmpL_cons (a b : Char) (as bs : List Char) : cmpL (a :: as) (b :: bs) =
    if a.toNat < b.toNat then -1 else if b.toNat < a.toNat then 1 else cmpL as bs := rfl

theorem cmpL_drop : ∀ (i : Nat) (xs ys : List Char), xs.take i = ys.take i → i ≤ xs.length →
    i ≤ ys.length → cmpL (xs.drop i) (ys.drop i) = cmpL xs ys
  | 0, _, _, _, _, _ => rfl
  | i + 1, x :: xs, y :: ys, h, h1, h2 => by
    simp only [List.take_succ_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [List.drop_succ_cons]
    rw [cmpL_drop i xs ys h (by simp at h1; omega) (by simp at h2; omega)]
    simp [cmpL]
  | i + 1, [], _, _, h1, _ => by simp at h1
  | i + 1, _ :: _, [], _, _, h2 => by simp at h2

/-- Memory after writing tag `6` into the first `k` slots of a frame whose slots start at `a`. -/
def tagsW (m : Mem) (a : Nat) : Nat → Mem
  | 0 => m
  | k + 1 => applyW (tagsW m a k) (a + 16 * k, 8, 6#64)

theorem rdW_tagsW (m : Mem) (a : Nat) (ha : a % 8 = 0) : ∀ (k b : Nat), b % 8 = 0 →
    rdW (tagsW m a k) b =
      if a ≤ b ∧ b < a + 16 * k ∧ (b - a) % 16 = 0 then 6#64 else rdW m b
  | 0, b, _ => by rw [if_neg (by omega)]; rfl
  | k + 1, b, hb => by
    simp only [tagsW]
    rw [rdW_upd (by omega) hb, rdW_tagsW m a ha k b hb]
    by_cases h1 : b = a + 16 * k
    · subst h1; rw [if_pos rfl, if_pos (by omega)]
    · rw [if_neg h1]
      by_cases h2 : a ≤ b ∧ b < a + 16 * k ∧ (b - a) % 16 = 0
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

/-! ## String objects -/

/-- The string object at `p` holds the characters `cs`. -/
structure StrW (m : Mem) (p : Nat) (cs : List Char) : Prop where
  lo : tohostAddr + 16 ≤ p
  hi : p + 8 + 8 * cs.length ≤ 2 ^ 32
  al : p % 8 = 0
  len : rdW m p = BitVec.ofNat 64 cs.length
  chars : ∀ i (h : i < cs.length), rdW m (p + 8 + 8 * i) = BitVec.ofNat 64 cs[i].toNat
  small : ∀ c ∈ cs, c.toNat < 256

theorem StrW.transport {m m' : Mem} {p : Nat} {cs : List Char} (h : StrW m p cs)
    (hag : Agree m m' p (p + 8 + 8 * cs.length)) : StrW m' p cs where
  lo := h.lo
  hi := h.hi
  al := h.al
  len := by rw [hag p (Nat.le_refl _) (by omega) h.al]; exact h.len
  chars i hi := by
    rw [hag (p + 8 + 8 * i) (by omega) (by omega) (by have := h.al; omega)]; exact h.chars i hi
  small := h.small

/-! ## Loops -/

theorem loop_run {code : List Ins} {I : Nat → AM → Prop} {Q : AM → Prop}
    (step : ∀ n A, I (n + 1) A → Reaches code A (I n)) (base : ∀ A, I 0 A → Reaches code A Q) :
    ∀ n A, I n A → Reaches code A Q
  | 0, A, h => base A h
  | n + 1, A, h => ex_bind (step n A h) (fun B hB => loop_run step base n B hB)

/-- A loop that may also leave early. -/
theorem loop_run' {code : List Ins} {I : Nat → AM → Prop} {Q : AM → Prop}
    (step : ∀ n A, I (n + 1) A → Reaches code A (fun B => I n B ∨ Q B))
    (base : ∀ A, I 0 A → Reaches code A Q) :
    ∀ n A, I n A → Reaches code A Q
  | 0, A, h => base A h
  | n + 1, A, h => ex_bind (step n A h) (fun B hB => hB.elim (loop_run' step base n B) (reach_here))

/-! ## Normal form of `WP` goals -/

/-- Compute a `WP` goal: unfold the instructions, evaluate register reads and
writes, branch and jump targets, and discharge decidable side conditions. -/
syntax "wp_simp" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| wp_simp) => `(tactic| wp_simp [])
  | `(tactic| wp_simp [$xs,*]) => `(tactic|
      simp (disch := first | decide | omega) only [WP, List.drop, List.take, List.drop_zero, List.drop_append,
        List.drop_eq_nil_of_le, List.length_append, List.length_cons, List.length_nil, putcR, liN,
        List.cons_append, List.nil_append,
        srcVal_gset, keysG_gset, srcVal_zero, sext_ofInt12, brT_bOff_of, BrOK_bOff_of, jT_jOff_of,
        JOK_jOff_of, guard_eq, guard_ne, guard_lt, guard_ge, SrcOK, reduceIte, Nat.reduceEqDiff,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceMul, Nat.reducePow,
        ofNat_add_lit, ofNat_add_neg, shl_ofNat, true_and, and_true,
        true_or, or_true, false_or, or_false, decide_eq_true_eq, BitVec.zero_add, BitVec.add_zero,
        sext_zero12, zero_add64, zero_add64', add_zero64, natCast_lit, BitVec.toInt_zero, toNat_ofNat6, Nat.reduceMod, BitVec.reduceToNat,
        List.take_append, List.take_of_length_le, WP_libc_iff, libc_length, libRes_mulE, libRes_divE, libRes_modE,
        keysG_lib', keysG_lib10, srcVal_lib, srcVal_lib10, sext_lo, sext_hi, BitVec.reduceOfInt, BitVec.reduceAdd, toInt_ofNat_small, toInt_ofNat_big,
        WP_li_iff, li_length_small, li_length_big, List.append_assoc, Nat.add_sub_cancel,
        tohostW_toNat, putcWord_low,
        Br, J, Call, mvi, addi, ret, mv, a0, a1, a2, a3, a4, a5, a6, a7, t0, t1, t2, t3, t4, t5,
        t6, s2, s3, s4, s5, s6, s9, s10, s11, ra, spR, hpO, envR, hpF, depR, $xs,*])

/-- Discharge register-file goals (`Has`, `Keep`) through chains of writes. -/
syntax "reg_simp" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| reg_simp) => `(tactic| reg_simp [])
  | `(tactic| reg_simp [$xs,*]) => `(tactic|
      simp (disch := decide) only [has_gset, keep_gset, has_lib, has_lib10, keep_lib, reduceIte,
        Nat.reduceEqDiff,
        a0, a1, a2, a3, a4, a5, a6, a7, t0, t1, t2, t3, t4, t5, t6, s2, s3, s4, s5, s6, s9, s10,
        s11, ra, spR, hpO, envR, hpF, depR, $xs,*])

/-- Close an equation between `BitVec.ofNat 64` words by arithmetic on the naturals. -/
macro "bv_eq" : tactic => `(tactic| first
  | with_reducible rfl
  | (apply congrArg (BitVec.ofNat 64); omega)
  | (rw [ofNat_add_lit _ _ (by decide)]; apply congrArg (BitVec.ofNat 64); omega)
  | (rw [ofNat_add_neg _ _ (by decide) (by omega)]; apply congrArg (BitVec.ofNat 64); omega))

/-- Lengths of routine code with constants. -/
macro "len_ok" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (disch := decide) [liN, li_length_big, li_length_small, putcR, libc, List.length_append, $xs,*])

end Vsa.Compiler
