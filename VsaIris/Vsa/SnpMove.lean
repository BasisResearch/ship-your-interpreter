import VsaIris.Vsa.SnpCtx
import VsaIris.Interp.Arm

/-!
# `memmove` in a `snprintf` run

`__ssputs_r` copies every output piece with `memmove(dst, src, len)`: the
format's literal runs and the `%s` arguments (data-view bytes), the sign and
digit buffers (owned stack bytes). The source bytes are read through
`swp_havocP` (`ntP_<pc>`), so one lemma covers both kinds: `ReadB` says a byte
reads `b` in every image consistent with the data view and the owned bytes.
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.MallocFast

/-- `a` reads `b`: a data-view byte, or an owned byte at the tracking memory. -/
def ReadB (Dt : Mem) (DA : List Nat) (S : Nat → Prop) (Mt : Mem) (a : Nat) (b : BitVec 8) : Prop :=
  (a ∈ DA ∧ imgM Dt a = b) ∨ (S a ∧ imgM Mt a = b)

theorem ReadB.img {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {Mt : Mem} {a : Nat} {b : BitVec 8}
    (h : ReadB Dt DA S Mt a b) {f : Nat → BitVec 8} (hD : ∀ p ∈ dataOf Dt DA, f p.1 = p.2)
    (hS : ∀ a, S a → f a = imgM Mt a) : f a = b := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h2]; exact hD (a, imgM Dt a) (List.mem_map_of_mem (f := fun a => (a, imgM Dt a)) h1)
  · rw [← h2]; exact hS a h1

theorem ReadB.transport {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {Mt Mt' : Mem} {a : Nat}
    {b : BitVec 8} (h : ReadB Dt DA S Mt a b) (hM : imgM Mt' a = imgM Mt a) : ReadB Dt DA S Mt' a b := by
  rcases h with h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr ⟨h1, hM.trans h2⟩

/-- The window `[lo, hi)` reads the image `g`. -/
def ReadWin (Dt : Mem) (DA : List Nat) (S : Nat → Prop) (Mt : Mem) (lo hi : Nat)
    (g : Nat → BitVec 8) : Prop :=
  ∀ a, lo ≤ a → a < hi → ReadB Dt DA S Mt a (g a)

theorem ReadWin.transport {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {Mt Mt' : Mem} {lo hi : Nat}
    {g : Nat → BitVec 8} (h : ReadWin Dt DA S Mt lo hi g)
    (hM : ∀ a, lo ≤ a → a < hi → imgM Mt' a = imgM Mt a) : ReadWin Dt DA S Mt' lo hi g :=
  fun a h1 h2 => (h a h1 h2).transport (hM a h1 h2)

/-- **A load inside a readable window** reads the window's image, whatever
consistent image the run's state has. -/
theorem ldvf_readWin {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {Mt : Mem} {lo hi : Nat}
    {g : Nat → BitVec 8} (h : ReadWin Dt DA S Mt lo hi g) {f : Nat → BitVec 8}
    (hD : ∀ p ∈ dataOf Dt DA, f p.1 = p.2) (hS : ∀ a, S a → f a = imgM Mt a) (k : MKind)
    {a : Nat} (h1 : lo ≤ a) (h2 : a + widthOfM k ≤ hi) : ldvf k f a = ldvf k g a := by
  unfold ldvf bytesAt
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have := List.mem_range.mp hj
  exact (h (a + j) (by omega) (by omega)).img hD hS

/-- A partly known load (`ntP_<pc>`'s continuation) inside a readable
window `h`: the value is the window's, after moving the window across the
run's stores (all outside it). -/
macro "snp_ld " h:term : tactic =>
  `(tactic| (rintro ⟨f, hfD, hfS, hv⟩; subst hv; rw [ldvf_readWin (ReadWin.transport $h (fun a h1 h2 => by
      first | rfl | (simp (disch := sx_addr) only [imgM_store_miss]))) hfD hfS _ (by sx_addr) (by simp only [widthOfM]; sx_addr)]; clear hfD hfS f))

/-- A byte load's value from any consistent image. -/
theorem ldvf_lbu_readB {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {Mt : Mem} {a : Nat}
    {b : BitVec 8} (h : ReadB Dt DA S Mt a b) {f : Nat → BitVec 8}
    (hD : ∀ p ∈ dataOf Dt DA, f p.1 = p.2) (hS : ∀ a, S a → f a = imgM Mt a) :
    ldvf .lbu f a = BitVec.zeroExtend 64 b := by
  simp only [ldvf, bytesVal, bytesAt, widthOfM, List.range_one, List.map_cons, List.map_nil,
    List.getD_cons_zero, Nat.add_zero]
  rw [h.img hD hS]
  rfl


/-- A byte store of a zero-extended byte reads back the byte. -/
theorem sbData_zext (b : BitVec 8) : sbData (BitVec.zeroExtend 64 b) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [sbData, Sail.BitVec.extractLsb]
  simp
  omega

theorem imgM_sb_zext (Mt : Mem) (a : Nat) (b : BitVec 8) :
    imgM (writeLog Mt [(a, 1, BitVec.zeroExtend 64 b)]) a = b := by
  have h := pin1_of_writeLog Mt [] [] a (BitVec.zeroExtend 64 b) trivial
  simp only [List.nil_append] at h
  unfold imgM
  rw [h, Option.getD_some, sbData_zext]

theorem imgLE_shift {f g : Nat → BitVec 8} :
    ∀ n a b, (∀ i, i < n → f (a + i) = g (b + i)) → VsaIris.Interp.imgLE f a n = VsaIris.Interp.imgLE g b n
  | 0, _, _, _ => rfl
  | n + 1, a, b, h => by
    simp only [VsaIris.Interp.imgLE]
    rw [show f a = g b by simpa using h 0 (by omega),
      imgLE_shift n (a + 1) (b + 1) (fun i hi => by
        have := h (i + 1) (by omega); rwa [show a + (i + 1) = a + 1 + i by omega,
          show b + (i + 1) = b + 1 + i by omega] at this)]

/-- A doubleword store of a loaded word reads back the loaded bytes. -/
theorem imgM_sd_ldvf (Mt : Mem) (A B j : Nat) (g : Nat → BitVec 8) (hj : j < 8) :
    imgM (writeLog Mt [(A, 8, ldvf .ld g B)]) (A + j) = g (B + j) := by
  have e : ldvf .ld g B = VsaIris.Interp.imgW (fun x => g (x - A + B)) A := by
    rw [VsaIris.Interp.ldvf_ld_imgLE (k := VsaIris.Interp.imgLE g B 8) rfl]
    unfold VsaIris.Interp.imgW
    congr 1
    exact imgLE_shift 8 B A (fun i _ => by
      show g (B + i) = g (A + i - A + B); congr 1; omega)
  rw [e, VsaIris.Interp.imgM_store_img hj]
  show g (A + j - A + B) = g (B + j); congr 1; omega

/-- The first `c` bytes of a copy of `g`'s bytes from `src` to `d` are in
place in `Mt`, and every byte outside `[d, d + c)` is as in `Mt0`. -/
structure Copied (Mt Mt0 : Mem) (d src c : Nat) (g : Nat → BitVec 8) : Prop where
  done : ∀ i, i < c → imgM Mt (d + i) = g (src + i)
  rest : ∀ a, a < d ∨ d + c ≤ a → imgM Mt a = imgM Mt0 a

theorem Copied.zero (Mt : Mem) (d src : Nat) (g : Nat → BitVec 8) : Copied Mt Mt d src 0 g :=
  ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩

/-- A copied doubleword extends a copy by eight bytes. -/
theorem Copied.sd {Mt Mt0 : Mem} {d src c : Nat} {g : Nat → BitVec 8} (h : Copied Mt Mt0 d src c g)
    {A B : Nat} (hA : A = d + c) (hB : B = src + c) :
    Copied (writeLog Mt [(A, 8, ldvf .ld g B)]) Mt0 d src (c + 8) g where
  done i hi := by
    by_cases hic : c ≤ i
    · have := imgM_sd_ldvf Mt A B (i - c) g (by omega)
      rwa [show A + (i - c) = d + i by omega, show B + (i - c) = src + i by omega] at this
    · rw [imgM_store_miss _ _ (by omega)]; exact h.done i (by omega)
  rest a ha := by rw [imgM_store_miss _ _ (by omega)]; exact h.rest a (by omega)

/-- A copied byte extends a copy by one byte. -/
theorem Copied.sb {Mt Mt0 : Mem} {d src c : Nat} {g : Nat → BitVec 8} (h : Copied Mt Mt0 d src c g)
    {A : Nat} (hA : A = d + c) :
    Copied (writeLog Mt [(A, 1, BitVec.zeroExtend 64 (g (src + c)))]) Mt0 d src (c + 1) g where
  done i hi := by
    by_cases hic : i = c
    · subst hic hA; exact imgM_sb_zext Mt _ _
    · rw [imgM_store_miss _ _ (by omega)]; exact h.done i (by omega)
  rest a ha := by rw [imgM_store_miss _ _ (by omega)]; exact h.rest a (by omega)

/-- Registers `memmove`'s byte loop keeps: all but `a1`, `a3`, `a4`, `a5`. -/
abbrev MMKeep (R R0 : Nat → BitVec 64) : Prop :=
  ∀ z, z ≠ 11 → z ≠ 13 → z ≠ 14 → z ≠ 15 → R z = R0 z

theorem toNat_ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  simp only [BitVec.toNat_ofNat]; omega

theorem ofNat_add_one {x : Nat} (h : x + 1 < 2 ^ 64) :
    BitVec.ofNat 64 x + 1#64 = BitVec.ofNat 64 (x + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem ofNat_ne_of_lt {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) :
    BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun e => h (by
  have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega)

theorem addr_m1 {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 64) :
    (BitVec.ofNat 64 x + 18446744073709551615#64).toNat = x - 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]
  rw [show (18446744073709551615#64 : BitVec 64).toNat = 2 ^ 64 - 1 from rfl]
  rw [show x + (2 ^ 64 - 1) = (x - 1) + 2 ^ 64 by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- **`memmove`'s byte loop** (`0x80006a0c`): `k` bytes left, `j` done. At the
`ret` the destination holds the source bytes `sb`, and nothing else changed. -/
theorem mm_byteLoop {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem}
    {DA : List Nat} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (d src len : Nat) (sb : Nat → BitVec 8) (R0 : Nat → BitVec 64) (Mt0 : Mem)
    (hd1 : 0x8001ad10 ≤ d) (hdd1 : dst ≤ d) (hdd2 : d + len ≤ dst + n)
    (hdn : dst + n ≤ 0x100000000)
    (hs1 : 0x80000000 ≤ src) (hs2 : src + len ≤ 0x100000000)
    (hs3 : src + len ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ src)
    (hdisj : src + len ≤ d ∨ d + len ≤ src)
    (hsrc : ∀ i, i < len → ReadB Dt DA (snpS s dst n) Mt0 (src + i) (sb i))
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', MMKeep R' R0 → (∀ i, i < len → imgM Mt' (d + i) = sb i) →
      (∀ a, a < d ∨ d + len ≤ a → imgM Mt' a = imgM Mt0 a) →
      NW live Dt DA (snpS s dst n) Q (R0 1) R' Mt') :
    ∀ k j (R : Nat → BitVec 64) (Mt : Mem), j + k = len → 0 < k →
      R 15 = BitVec.ofNat 64 (d + j) → R 11 = BitVec.ofNat 64 (src + j) →
      R 13 = BitVec.ofNat 64 (d + len) → MMKeep R R0 →
      (∀ i, i < j → imgM Mt (d + i) = sb i) → (∀ a, a < d ∨ d + j ≤ a → imgM Mt a = imgM Mt0 a) →
      NW live Dt DA (snpS s dst n) Q 0x80006a0c#64 R Mt := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; omega
  | succ k ih =>
    intro j R Mt hjk _ h15 h11 h13 hkp hin hout
    have hR1 : R 1 = R0 1 := hkp 1 (by decide) (by decide) (by decide) (by decide)
    have hb : ReadB Dt DA (snpS s dst n) Mt (src + j) (sb j) :=
      (hsrc j (by omega)).transport (hout _ (by omega))
    refine ntP_80006a0c hlive ?_ ?_
    · rw [h11]; sx_addr
    rintro v ⟨f, hfD, hfS, rfl⟩
    have e11 : (R 11 + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)).toNat = src + j := by
      rw [h11]
      simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
        BitVec.reduceSignExtend, BitVec.add_zero, BitVec.toNat_ofNat]; omega
    rw [e11, ldvf_lbu_readB hb hfD hfS]
    nx_run hlive using [h15, h11, h13] at 0x80006a0c 0x80006a20
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *)
    all_goals rename_i hc
    all_goals rw [ofNat_add_one (by omega), ofNat_add_one (by omega),
      addr_m1 (by omega) (by omega), Nat.add_sub_cancel] at *
    case succ.refine_2.hk.hT =>
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · exact absurd (by rw [h13, show d + j + 1 = d + len by omega]) hc
        · exact h0
      refine ih (j + 1) _ _ (by omega) hk0 ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [Nat.add_assoc]
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [Nat.add_assoc]
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h13
      · intro z h11' h13' h14 h15'
        simp only [upd_apply, h11', h14, h15', ite_false]; exact hkp z h11' h13' h14 h15'
      · intro i hi
        by_cases hij : i = j
        · subst hij; exact imgM_sb_zext Mt (d + i) (sb i)
        · rw [imgM_store_miss _ _ (by omega)]; exact hin i (by omega)
      · intro a ha
        rw [imgM_store_miss _ _ (by omega)]; exact hout a (by omega)
    case succ.refine_2.hk.hF =>
      have hlen : j + 1 = len := by
        apply Classical.byContradiction; intro hne
        exact hc (by rw [h13]; exact ofNat_ne_of_lt (by omega) (by omega) (by omega))
      refine nt_80006a20 hlive ?_ ?_
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hR1]; exact hal
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hR1]
        refine hk _ _ ?_ ?_ ?_
        · intro z h11' h13' h14 h15'
          simp only [upd_apply, h11', h14, h15', ite_false]; exact hkp z h11' h13' h14 h15'
        · intro i hi
          by_cases hij : i = j
          · subst hij; exact imgM_sb_zext Mt (d + i) (sb i)
          · rw [imgM_store_miss _ _ (by omega)]; exact hin i (by omega)
        · intro a ha
          rw [imgM_store_miss _ _ (by omega)]; exact hout a (by omega)

/-- Registers `memmove`'s word loops keep: all but `a1`, `a3`, `a4`, `a7`, `t1`. -/
abbrev MWKeep (R R0 : Nat → BitVec 64) : Prop :=
  ∀ z, z ≠ 11 → z ≠ 13 → z ≠ 14 → z ≠ 17 → z ≠ 6 → R z = R0 z

theorem ofNat_add_ofNat (x y : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The geometry of a `memmove(d, src, len)` inside a `snprintf` run: the
destination is in the owned window above the HTIF words, the source in RAM
off them, the two disjoint. -/
structure MoveGeom (s dst n d src len : Nat) : Prop where
  d_lo : 0x8001ad10 ≤ d
  d_in : dst ≤ d ∧ d + len ≤ dst + n
  dst_hi : dst + n ≤ 0x100000000
  s_lo : 0x80000000 ≤ src
  s_hi : src + len ≤ 0x100000000
  s_htif : src + len ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ src
  disj : src + len ≤ d ∨ d + len ≤ src

/-- Replace a run's tracking memory by any memory with a property it has
(keeps the terms of a long run small). -/
theorem nw_gen {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {pc : BitVec 64} {R : Nat → BitVec 64}
    {M : Mem} (P : Mem → Prop) (hP : P M) (h : ∀ M', P M' → NW live Dt DA S Q pc R M') :
    NW live Dt DA S Q pc R M := h M hP

/-- A word copy's store: rebase the memory onto `Copied` one word longer, with
the source window moved along. -/
macro "snp_sd " hcp:ident ", " hw:ident " => " hcp':ident ", " hw':ident : tactic =>
  `(tactic| (refine nw_gen (fun M => Copied M _ _ _ _ _ ∧ ReadWin _ _ _ M _ _ _) (And.intro (Copied.sd $hcp (by sx_addr) (by sx_addr)) (ReadWin.transport $hw (fun a h1 h2 => (by simp (disch := sx_addr) only [imgM_store_miss])))) ?_; clear $hcp $hw; rintro _ ⟨$hcp', $hw'⟩))

/-- Register facts at a word loop's exits: lookups through the updates, and
`ofNat` sums as `Nat` sums. -/
macro "mm_regs" : tactic =>
  `(tactic| first
    | (intro z hz1 hz2 hz3 hz4 hz5; simp only [upd_apply, hz1, hz2, hz3, hz4, hz5, ite_false])
    | (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; done)
    | (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, ofNat_add_ofNat] <;>
       (congr 1 <;> omega)))

/-- **One iteration of `memmove`'s 32-byte loop** (`0x80006a48`): four
doubleword copies, then the back edge (`hkL`) or the fall-through (`hkX`). -/
theorem mm32_step {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem}
    {DA : List Nat} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (d src len L c : Nat) (g : Nat → BitVec 8) (R : Nat → BitVec 64) (Mt Mt0 : Mem)
    (G : MoveGeom s dst n d src len) (hd8 : d % 8 = 0) (hL : L ≤ len) (hc : c + 32 ≤ L)
    (hc8 : c % 8 = 0)
    (hw : ReadWin Dt DA (snpS s dst n) Mt src (src + len) g) (hcp : Copied Mt Mt0 d src c g)
    (h11 : R 11 = BitVec.ofNat 64 (src + c)) (h14 : R 14 = BitVec.ofNat 64 (d + c))
    (h16 : R 16 = BitVec.ofNat 64 (d + L))
    (hkL : c + 32 < L → ∀ R' Mt', R' 11 = BitVec.ofNat 64 (src + (c + 32)) →
      R' 14 = BitVec.ofNat 64 (d + (c + 32)) → R' 16 = R 16 → MWKeep R' R →
      Copied Mt' Mt0 d src (c + 32) g → ReadWin Dt DA (snpS s dst n) Mt' src (src + len) g →
      NW live Dt DA (snpS s dst n) Q 0x80006a48#64 R' Mt')
    (hkX : c + 32 = L → ∀ R' Mt', R' 11 = BitVec.ofNat 64 (src + (c + 32)) →
      R' 14 = BitVec.ofNat 64 (d + (c + 32)) → R' 16 = R 16 → MWKeep R' R →
      Copied Mt' Mt0 d src (c + 32) g → NW live Dt DA (snpS s dst n) Q 0x80006a74#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80006a48#64 R Mt := by
  obtain ⟨hd1, ⟨hdd1, hdd2⟩, hdn, hs1, hs2, hs3, hdisj⟩ := G
  nx_run hlive using [h11, h14, h16]
  snp_ld hw
  nx_run hlive using [h11, h14, h16] at 0x80006a58
  snp_sd hcp, hw => hcp1, hw1
  nx_run hlive using [h11, h14, h16]
  snp_ld hw1
  nx_run hlive using [h11, h14, h16] at 0x80006a60
  snp_sd hcp1, hw1 => hcp2, hw2
  nx_run hlive using [h11, h14, h16]
  snp_ld hw2
  nx_run hlive using [h11, h14, h16] at 0x80006a68
  snp_sd hcp2, hw2 => hcp3, hw3
  nx_run hlive using [h11, h14, h16]
  snp_ld hw3
  nx_run hlive using [h11, h14, h16] at 0x80006a70
  snp_sd hcp3, hw3 => hcp4, hw4
  nx_run hlive using [h11, h14, h16] at 0x80006a48 0x80006a74
  all_goals rename_i hb
  all_goals (rw [show c + 8 + 8 + 8 + 8 = c + 32 by omega] at hcp4)
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hb ⊢)
  all_goals (rw [ofNat_add_ofNat, h16] at hb)
  · refine hkL (Nat.lt_of_le_of_ne hc (fun e => hb (by rw [show d + c + 32 = d + L by omega])))
      _ _ ?_ ?_ ?_ ?_ hcp4 hw4
    all_goals mm_regs
  · refine hkX (by
      apply Classical.byContradiction; intro hne
      exact hb (ofNat_ne_of_lt (by omega) (by omega) (by omega))) _ _ ?_ ?_ ?_ ?_ hcp4
    all_goals mm_regs

theorem MWKeep.trans {R R' R'' : Nat → BitVec 64} (h : MWKeep R' R) (h' : MWKeep R'' R') :
    MWKeep R'' R := fun z a b c d e => (h' z a b c d e).trans (h z a b c d e)

/-- **`memmove`'s 32-byte loop** (`0x80006a48`), `m` blocks left: it copies
`[c, L)` and falls through at `0x80006a74`. -/
theorem mm_loop32 {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem}
    {DA : List Nat} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (d src len L : Nat) (g : Nat → BitVec 8) (R0 : Nat → BitVec 64) (Mt0 : Mem)
    (G : MoveGeom s dst n d src len) (hd8 : d % 8 = 0) (hL : L ≤ len) (hL32 : L % 32 = 0)
    (hk : ∀ R' Mt', MWKeep R' R0 → R' 11 = BitVec.ofNat 64 (src + L) →
      R' 14 = BitVec.ofNat 64 (d + L) → Copied Mt' Mt0 d src L g →
      NW live Dt DA (snpS s dst n) Q 0x80006a74#64 R' Mt') :
    ∀ m c (R : Nat → BitVec 64) (Mt : Mem), c + 32 * m = L → 0 < m →
      R 11 = BitVec.ofNat 64 (src + c) → R 14 = BitVec.ofNat 64 (d + c) →
      R 16 = BitVec.ofNat 64 (d + L) → MWKeep R R0 → Copied Mt Mt0 d src c g →
      ReadWin Dt DA (snpS s dst n) Mt src (src + len) g →
      NW live Dt DA (snpS s dst n) Q 0x80006a48#64 R Mt := by
  intro m
  induction m with
  | zero => intro _ _ _ _ h; omega
  | succ m ih =>
    intro c R Mt hcm _ h11 h14 h16 hkp hcp hw
    refine mm32_step hlive d src len L c g R Mt Mt0 G hd8 hL (by omega) (by omega) hw hcp h11 h14 h16
      ?_ ?_
    · intro hlt R' Mt' h11' h14' h16' hkp' hcp' hw'
      exact ih (c + 32) R' Mt' (by omega) (by omega) h11' h14' (h16'.trans h16) (hkp.trans hkp')
        hcp' hw'
    · intro heq R' Mt' h11' h14' _ hkp' hcp'
      rw [heq] at h11' h14' hcp'
      exact hk R' Mt' (hkp.trans hkp') h11' h14' hcp'

theorem ofNat_sub_ofNat (x y : Nat) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y = BitVec.ofNat 64 (x + (2 ^ 64 - y)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- **One iteration of `memmove`'s 8-byte loop** (`0x80006aac`): `a6 = d - src`,
the loop ends when `a1` reaches `src + E`. -/
theorem mm8_step {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem}
    {DA : List Nat} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (d src len E c : Nat) (g : Nat → BitVec 8) (R : Nat → BitVec 64) (Mt Mt0 : Mem)
    (G : MoveGeom s dst n d src len) (hd8 : d % 8 = 0) (hE : E ≤ len) (hc : c + 8 ≤ E)
    (hc8 : c % 8 = 0)
    (hw : ReadWin Dt DA (snpS s dst n) Mt src (src + len) g) (hcp : Copied Mt Mt0 d src c g)
    (h11 : R 11 = BitVec.ofNat 64 (src + c)) (h14 : R 14 = BitVec.ofNat 64 (src + E))
    (h16 : R 16 = BitVec.ofNat 64 (d + (2 ^ 64 - src)))
    (hkL : c + 8 < E → ∀ R' Mt', R' 11 = BitVec.ofNat 64 (src + (c + 8)) →
      R' 14 = R 14 → R' 16 = R 16 → MWKeep R' R →
      Copied Mt' Mt0 d src (c + 8) g → ReadWin Dt DA (snpS s dst n) Mt' src (src + len) g →
      NW live Dt DA (snpS s dst n) Q 0x80006aac#64 R' Mt')
    (hkX : c + 8 = E → ∀ R' Mt', R' 11 = BitVec.ofNat 64 (src + (c + 8)) →
      R' 14 = R 14 → R' 16 = R 16 → MWKeep R' R →
      Copied Mt' Mt0 d src (c + 8) g → NW live Dt DA (snpS s dst n) Q 0x80006ac0#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80006aac#64 R Mt := by
  obtain ⟨hd1, ⟨hdd1, hdd2⟩, hdn, hs1, hs2, hs3, hdisj⟩ := G
  nx_run hlive using [h11, h14, h16]
  snp_ld hw
  nx_run hlive using [h11, h14, h16] at 0x80006abc
  snp_sd hcp, hw => hcp1, hw1
  nx_run hlive using [h11, h14, h16] at 0x80006aac 0x80006ac0
  all_goals rename_i hb
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hb ⊢)
  all_goals (rw [ofNat_add_ofNat] at hb; try rw [h14] at hb)
  · refine hkL (Nat.lt_of_le_of_ne hc (fun e => hb (by rw [show src + c + 8 = src + E by omega])))
      _ _ ?_ ?_ ?_ ?_ hcp1 hw1
    all_goals mm_regs
  · refine hkX (by
      apply Classical.byContradiction; intro hne
      exact hb (ofNat_ne_of_lt (by omega) (by omega) (by omega))) _ _ ?_ ?_ ?_ ?_ hcp1
    all_goals mm_regs

/-- Registers `memmove` keeps: all but `a1`–`a7`, `t1`, `t3`. -/
abbrev MMFrame (R R0 : Nat → BitVec 64) : Prop :=
  ∀ z, z ≠ 11 → z ≠ 12 → z ≠ 13 → z ≠ 14 → z ≠ 15 → z ≠ 16 → z ≠ 17 → z ≠ 6 → z ≠ 28 →
    R z = R0 z

theorem MMFrame.of_mm {R R0 : Nat → BitVec 64} (h : MMKeep R R0) : MMFrame R R0 :=
  fun z a _ b c d _ _ _ _ => h z a b c d

theorem MMFrame.of_mw {R R0 : Nat → BitVec 64} (h : MWKeep R R0) : MMFrame R R0 :=
  fun z a _ b c _ _ e f _ => h z a b c e f

theorem MMFrame.trans {R R' R'' : Nat → BitVec 64} (h : MMFrame R' R) (h' : MMFrame R'' R') :
    MMFrame R'' R := fun z a b c d e f g i j => (h' z a b c d e f g i j).trans (h z a b c d e f g i j)

/-- **`memmove`'s byte tail** (`0x800069fc`): `k` bytes left after `c` copied,
`a5 = d + c`, `a1 = src + c`, `a2 = k`. At the `ret` the copy is complete. -/
theorem mm_tail {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem}
    {DA : List Nat} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (d src len c k : Nat) (g : Nat → BitVec 8) (R R0 : Nat → BitVec 64) (Mt Mt0 : Mem)
    (G : MoveGeom s dst n d src len) (hck : c + k = len)
    (hw : ReadWin Dt DA (snpS s dst n) Mt src (src + len) g) (hcp : Copied Mt Mt0 d src c g)
    (h12 : R 12 = BitVec.ofNat 64 k) (h15 : R 15 = BitVec.ofNat 64 (d + c))
    (h11 : R 11 = BitVec.ofNat 64 (src + c)) (hkp : MMFrame R R0)
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', MMFrame R' R0 → Copied Mt' Mt0 d src len g →
      NW live Dt DA (snpS s dst n) Q (R0 1) R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x800069fc#64 R Mt := by
  obtain ⟨hd1, ⟨hdd1, hdd2⟩, hdn, hs1, hs2, hs3, hdisj⟩ := G
  have hR1 : R 1 = R0 1 := hkp 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  nx_run hlive using [h12, h15, h11] at 0x80006a0c 0x80006ae0
  all_goals (rename_i hb; try simp only [upd_apply, Nat.reduceEqDiff, ite_false] at hb; try rw [h12] at hb)
  · -- k = 0: `ret`
    have hk64 : k < 2 ^ 64 := by omega
    have hk0 : k = 0 := by
      have := congrArg BitVec.toNat hb; simp at this; omega
    subst hk0
    rw [Nat.add_zero] at hck
    subst hck
    refine nt_80006ae0 hlive ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [hR1]; exact hal
    · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [hR1]
      refine hk _ Mt (hkp.trans fun z _ _ h13 _ _ _ _ _ _ => ?_) hcp
      simp only [upd_apply, h13, ite_false]
  · -- the byte loop from `j = c`
    have hk64 : k < 2 ^ 64 := by omega
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact (hb (by rw [h12, h])).elim
      · exact h
    refine mm_byteLoop hlive d src len (fun i => g (src + i)) R Mt0 hd1 hdd1 hdd2 hdn hs1 hs2 hs3
      hdisj (fun i hi => (hw (src + i) (by omega) (by omega)).transport
        (hcp.rest _ (by omega)).symm) (by rw [hR1]; exact hal)
      (fun R' Mt' hk' hd hr => by rw [hR1]; exact hk R' Mt' (hkp.trans (MMFrame.of_mm hk')) ⟨hd, hr⟩)
      k c _ Mt hck hk0 ?_ ?_ ?_ ?_ hcp.done hcp.rest
    · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h15
    · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h11
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, ofNat_add_ofNat]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]; omega
    · intro z h11' h13 h14 h15'
      simp only [upd_apply, h13, ite_false]

end VsaIris.Sym
