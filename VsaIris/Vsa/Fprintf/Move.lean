import VsaIris.Vsa.Fprintf.Tac
import VsaIris.Interp.Arm

/-!
# `memmove` in a stdout run (lane N5)

`__sfvwrite_r` copies each output piece into `__sbprintf`'s stack buffer with
`memmove(d, src, len)`: the format's literal runs and the `%s` argument
(data-view bytes), the digit and sign buffers (owned stack bytes). The
destination lies above every source (the buffer is in `__sbprintf`'s frame,
the digits in the inner `_vfprintf_r`'s, below it), so only the forward
paths run: the byte loop (`len ≤ 31` or a misaligned pair), and the 32-byte,
8-byte and byte loops for aligned pairs.

The source bytes are read through `swp_havocP` (`itP_<pc>`): `ReadB` says a
byte reads `b` in every image consistent with the data view and the owned
bytes, so one lemma covers both kinds. The invariant `Copied` (bytes copied so
far, everything else as at the entry) is N2's (`SnpMove.lean`, over N2's
`snprintf` table), here over the shared stdio table.

`Cover P lo hi` (a range all of whose bytes satisfy `P`: owned, or in the
data view) is the run's coverage fact; `nf_cover` closes a byte-set side
condition from one.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open scoped VsaIris.Sym.Stdout

/-! ## Coverage facts -/

/-- Every byte of `[lo, hi)` satisfies `P`. -/
def Cover (P : Nat → Prop) (lo hi : Nat) : Prop := ∀ b, lo ≤ b → b < hi → P b

theorem Cover.mem {P : Nat → Prop} {lo hi b : Nat} (h : Cover P lo hi) (h1 : lo ≤ b) (h2 : b < hi) :
    P b := h b h1 h2

open Lean Elab Tactic Meta in
/-- Close `P b` (the body of a byte-set side condition, `lo ≤ b < hi` in
context) from some `Cover P lo' hi'` hypothesis and `omega`. -/
elab "nf_cover" : tactic => do
  let g ← getMainGoal
  let lctx ← g.withContext getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← g.withContext (instantiateMVars d.type)
    unless ty.getAppFn.isConstOf ``Cover do continue
    let saved ← saveState
    try
      let gs ← evalTacticAt (← `(tactic| (refine Cover.mem $(mkIdent d.userName) ?_ ?_ <;> omega))) g
      if gs.isEmpty then
        replaceMainGoal []
        return
      saved.restore
    catch _ => saved.restore
  throwError "nf_cover: no Cover fact covers the access"

/-- An access-range hypothesis as `Nat` arithmetic modulo `2^64` (`omega`
reads it). -/
macro "fp_hb " h:ident : tactic => `(tactic| simp only [mem_accAddrs_iff,
  LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend,
  BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow] at $h:ident)

/-- Byte-set side conditions (`∀ b ∈ accAddrs a w, P b`) from a `Cover` fact. -/
macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; fp_hb hb; nf_cover))

/-! ## Reads and copies -/

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

/-- A partly known load (`itP_<pc>`'s continuation) inside a readable
window `h`: the value is the window's, after moving the window across the
run's stores (all outside it). -/
macro "fp_ld " h:term : tactic =>
  `(tactic| (rintro ⟨f, hfD, hfS, hv⟩; subst hv; rw [ldvf_readWin (ReadWin.transport $h (fun a h1 h2 => by
      first | rfl | (simp (disch := nx_addr) only [imgM_store_miss]))) hfD hfS _ (by nx_addr) (by simp only [widthOfM]; nx_addr)]; clear hfD hfS f))

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
    ∀ n a b, (∀ i, i < n → f (a + i) = g (b + i)) → imgLE f a n = imgLE g b n
  | 0, _, _, _ => rfl
  | n + 1, a, b, h => by
    simp only [imgLE]
    rw [show f a = g b by simpa using h 0 (by omega),
      imgLE_shift n (a + 1) (b + 1) (fun i hi => by
        have := h (i + 1) (by omega); rwa [show a + (i + 1) = a + 1 + i by omega,
          show b + (i + 1) = b + 1 + i by omega] at this)]

/-- A doubleword store of a loaded word reads back the loaded bytes. -/
theorem imgM_sd_ldvf (Mt : Mem) (A B j : Nat) (g : Nat → BitVec 8) (hj : j < 8) :
    imgM (writeLog Mt [(A, 8, ldvf .ld g B)]) (A + j) = g (B + j) := by
  have e : ldvf .ld g B = imgW (fun x => g (x - A + B)) A := by
    rw [ldvf_ld_imgLE (k := imgLE g B 8) rfl]
    unfold imgW
    congr 1
    exact imgLE_shift 8 B A (fun i _ => by
      show g (B + i) = g (A + i - A + B); congr 1; omega)
  rw [e, imgM_store_img hj]
  show g (A + j - A + B) = g (B + j); congr 1; omega

/-- The first `c` bytes of a copy of `g`'s bytes from `src` to `d` are in
place in `Mt`, and every byte outside `[d, d + c)` is as in `Mt0`. -/
structure Copied (Mt Mt0 : Mem) (d src c : Nat) (g : Nat → BitVec 8) : Prop where
  done : ∀ i, i < c → imgM Mt (d + i) = g (src + i)
  rest : ∀ a, a < d ∨ d + c ≤ a → imgM Mt a = imgM Mt0 a

theorem Copied.zero (Mt : Mem) (d src : Nat) (g : Nat → BitVec 8) : Copied Mt Mt d src 0 g :=
  ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩

theorem Copied.sd {Mt Mt0 : Mem} {d src c : Nat} {g : Nat → BitVec 8} (h : Copied Mt Mt0 d src c g)
    {A B : Nat} (hA : A = d + c) (hB : B = src + c) :
    Copied (writeLog Mt [(A, 8, ldvf .ld g B)]) Mt0 d src (c + 8) g where
  done i hi := by
    by_cases hic : c ≤ i
    · have := imgM_sd_ldvf Mt A B (i - c) g (by omega)
      rwa [show A + (i - c) = d + i by omega, show B + (i - c) = src + i by omega] at this
    · rw [imgM_store_miss _ _ (by omega)]; exact h.done i (by omega)
  rest a ha := by rw [imgM_store_miss _ _ (by omega)]; exact h.rest a (by omega)

theorem Copied.sb {Mt Mt0 : Mem} {d src c : Nat} {g : Nat → BitVec 8} (h : Copied Mt Mt0 d src c g)
    {A : Nat} (hA : A = d + c) :
    Copied (writeLog Mt [(A, 1, BitVec.zeroExtend 64 (g (src + c)))]) Mt0 d src (c + 1) g where
  done i hi := by
    by_cases hic : i = c
    · subst hic hA; exact imgM_sb_zext Mt _ _
    · rw [imgM_store_miss _ _ (by omega)]; exact h.done i (by omega)
  rest a ha := by rw [imgM_store_miss _ _ (by omega)]; exact h.rest a (by omega)

/-! ## Arithmetic -/

theorem ofNat_add_one {x : Nat} (h : x + 1 < 2 ^ 64) :
    BitVec.ofNat 64 x + 1#64 = BitVec.ofNat 64 (x + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem ofNat_ne_of_lt {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) :
    BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun e => h (by
  have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega)

theorem ofNat_add_ofNat (x y : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem ofNat_sub_ofNat (x y : Nat) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y = BitVec.ofNat 64 (x + (2 ^ 64 - y)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-! ## The loops -/

/-- The geometry of a `memmove(d, src, len)`: the destination owned and
above the HTIF words, the source in RAM off them, the two disjoint. -/
structure MoveGeom (S : Nat → Prop) (d src len : Nat) : Prop where
  d_lo : 0x8001ad10 ≤ d
  d_hi : d + len ≤ 0x100000000
  d_own : Cover S d (d + len)
  s_lo : 0x80000000 ≤ src
  s_hi : src + len ≤ 0x100000000
  s_htif : src + len ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ src
  disj : src + len ≤ d ∨ d + len ≤ src

/-- Registers `memmove` changes: `a1`–`a7`, `t1`, `t3`. -/
abbrev MMFrame (R R0 : Nat → BitVec 64) : Prop :=
  ∀ z, z ≠ 11 → z ≠ 12 → z ≠ 13 → z ≠ 14 → z ≠ 15 → z ≠ 16 → z ≠ 17 → z ≠ 6 → z ≠ 28 →
    R z = R0 z

theorem MMFrame.trans {R R' R'' : Nat → BitVec 64} (h : MMFrame R' R) (h' : MMFrame R'' R') :
    MMFrame R'' R := fun z a b c d e f g i j => (h' z a b c d e f g i j).trans (h z a b c d e f g i j)

theorem MMFrame.trans' {R R' R'' : Nat → BitVec 64} (h : MMFrame R' R) (h' : MMFrame R'' R') :
    MMFrame R'' R := h.trans h'

theorem MMFrame.refl (R : Nat → BitVec 64) : MMFrame R R := fun _ _ _ _ _ _ _ _ _ _ => rfl

/-- Registers a loop keeps: all but `a`, `b`, `c`. -/
def Keep3 (R' R : Nat → BitVec 64) (a b c : Nat) : Prop := ∀ z, z ≠ a → z ≠ b → z ≠ c → R' z = R z

theorem Keep3.trans {R R' R'' : Nat → BitVec 64} {a b c : Nat} (h : Keep3 R' R a b c)
    (h' : Keep3 R'' R' a b c) : Keep3 R'' R a b c := fun z x y w => (h' z x y w).trans (h z x y w)

/-- `Keep3` of one register update outside the frame. -/
macro "k3_frame" : tactic =>
  `(tactic| (intro z ha hb hc; simp only [upd_apply, ha, hb, hc, ite_false]))

/-- `MMFrame` of one register update outside the frame. -/
macro "mm_frame" : tactic =>
  `(tactic| (intro z h11 h12 h13 h14 h15 h16 h17 h6 h28; simp only [upd_apply, h11, h12, h13, h14, h15, h16, h17, h6, h28, ite_false]))

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- **`memmove`'s byte loop** (`0x80006a0c`): `k` bytes left, `j` done. At the
`ret` the destination holds the window's bytes, nothing else changed. -/
theorem mm_byteLoop (hlive : ∀ p ∈ stdioText, live p.1) (d src len : Nat) (g : Nat → BitVec 8)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (G : MoveGeom S d src len)
    (hw : ReadWin Dt DA S Mt0 src (src + len) g) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', MMFrame R' R0 → Copied Mt' Mt0 d src len g → NW live Dt DA S Q (R0 1) R' Mt') :
    ∀ k j (R : Nat → BitVec 64) (Mt : Mem), j + k = len → 0 < k →
      R 15 = BitVec.ofNat 64 (d + j) → R 11 = BitVec.ofNat 64 (src + j) →
      R 13 = BitVec.ofNat 64 (d + len) → MMFrame R R0 → Copied Mt Mt0 d src j g →
      NW live Dt DA S Q 0x80006a0c#64 R Mt := by
  obtain ⟨hd1, hd2, hdS, hs1, hs2, hs3, hdisj⟩ := G
  intro k
  induction k with
  | zero => intro _ _ _ _ h; omega
  | succ k ih =>
    intro j R Mt hjk _ h15 h11 h13 hkp hcp
    have hR1 : R 1 = R0 1 := hkp 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    have hb : ReadB Dt DA S Mt (src + j) (g (src + j)) :=
      (hw (src + j) (by omega) (by omega)).transport (hcp.rest _ (by omega))
    have e11 : (R 11 + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12)).toNat = src + j := by
      rw [h11]
      simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
        BitVec.reduceSignExtend, BitVec.add_zero, BitVec.toNat_ofNat]; omega
    have ex : ∀ x : Nat, x + 1 < 2 ^ 64 →
        BitVec.ofNat 64 x + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x001#12) =
          BitVec.ofNat 64 (x + 1) := fun x hx => by
      rw [show LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x001#12) = 1#64 by decide]
      exact ofNat_add_one hx
    have eA : (BitVec.ofNat 64 (d + j + 1) +
        LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xfff#12)).toNat = d + j := by
      rw [show LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xfff#12) =
        BitVec.ofNat 64 (2 ^ 64 - 1) by decide, ofNat_add_ofNat, BitVec.toNat_ofNat]
      omega
    refine itP_80006a0c hlive (by rw [e11]; unfold LdOK tohostAddr; omega) fun v hv => ?_
    obtain ⟨f, hfD, hfS, rfl⟩ := hv
    rw [e11, ldvf_lbu_readB hb hfD hfS]
    refine it_80006a10 hlive (it_80006a14 hlive (it_80006a18 hlive ?_ ?_ (it_80006a1c hlive ?_ ?_)))
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h15, h11, h13,
      ex (d + j) (by omega), ex (src + j) (by omega), eA]
    · unfold StOKb tohostAddr; omega
    · intro b hb; rw [mem_accAddrs_iff] at hb; exact hdS b (by omega) (by omega)
    · intro hc
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · exact absurd (by rw [show d + j + 1 = d + len by omega]) hc
        · exact h0
      refine ih (j + 1) _ _ (by omega) hk0 ?_ ?_ ?_ ?_ ?_
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [Nat.add_assoc]
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h11, ex (src + j) (by omega)]
        rw [Nat.add_assoc]
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h13
      · refine hkp.trans' ?_; mm_frame
      · rw [show d + j + 1 = d + (j + 1) by omega] at *
        exact hcp.sb rfl
    · intro hc
      have hlen : j + 1 = len := by
        apply Classical.byContradiction; intro hne
        exact hc (ofNat_ne_of_lt (by omega) (by omega) (by omega))
      refine it_80006a20 hlive ?_ ?_
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hR1]; exact hal
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hR1]
        refine hk _ _ ?_ ?_
        · refine hkp.trans' ?_; mm_frame
        · rw [← hlen]; exact hcp.sb rfl

/-- An effective address below a register: `x + sext imm = x - k`. -/
theorem ea_sub {x k : Nat} {imm : BitVec 12}
    (himm : LeanRV64DExecutable.Functions.sign_extend (m := 64) imm = BitVec.ofNat 64 (2 ^ 64 - k))
    (hk : k ≤ x) (hk0 : 0 < k) (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x + LeanRV64DExecutable.Functions.sign_extend (m := 64) imm).toNat = x - k := by
  rw [himm, ofNat_add_ofNat, BitVec.toNat_ofNat]; omega

theorem ea_add {x k : Nat} {imm : BitVec 12}
    (himm : LeanRV64DExecutable.Functions.sign_extend (m := 64) imm = BitVec.ofNat 64 k)
    (hx : x + k < 2 ^ 64) :
    (BitVec.ofNat 64 x + LeanRV64DExecutable.Functions.sign_extend (m := 64) imm).toNat = x + k := by
  rw [himm, ofNat_add_ofNat, BitVec.toNat_ofNat]; omega

theorem ofNat_add_sx {x k : Nat} {imm : BitVec 12}
    (himm : LeanRV64DExecutable.Functions.sign_extend (m := 64) imm = BitVec.ofNat 64 k) :
    BitVec.ofNat 64 x + LeanRV64DExecutable.Functions.sign_extend (m := 64) imm = BitVec.ofNat 64 (x + k) := by
  rw [himm, ofNat_add_ofNat]

/-- A word load of the copy's source, then its store to the destination: the
window moves across the store (outside it), the copy grows by eight bytes. -/
theorem Copied.sd_win {Mt Mt0 : Mem} {d src c len : Nat} {g : Nat → BitVec 8}
    (h : Copied Mt Mt0 d src c g) (hw : ReadWin Dt DA S Mt src (src + len) g)
    (hdisj : src + len ≤ d ∨ d + len ≤ src) (hc : c + 8 ≤ len) :
    Copied (writeLog Mt [(d + c, 8, ldvf .ld g (src + c))]) Mt0 d src (c + 8) g ∧
      ReadWin Dt DA S (writeLog Mt [(d + c, 8, ldvf .ld g (src + c))]) src (src + len) g :=
  ⟨h.sd rfl rfl, hw.transport fun a h1 h2 => imgM_store_miss _ _ (by omega)⟩

/-- **One iteration of `memmove`'s 32-byte loop** (`0x80006a48`): four
doubleword copies, then the back edge or the fall-through at `0x80006a74`. -/
theorem mm32_step (hlive : ∀ p ∈ stdioText, live p.1) (d src len L c : Nat)
    (g : Nat → BitVec 8) (R : Nat → BitVec 64) (Mt Mt0 : Mem) (G : MoveGeom S d src len)
    (hd8 : d % 8 = 0) (hL : L ≤ len) (hc : c + 32 ≤ L) (hc8 : c % 8 = 0)
    (hw : ReadWin Dt DA S Mt src (src + len) g) (hcp : Copied Mt Mt0 d src c g)
    (h11 : R 11 = BitVec.ofNat 64 (src + c)) (h14 : R 14 = BitVec.ofNat 64 (d + c))
    (h16 : R 16 = BitVec.ofNat 64 (d + L))
    (hkL : c + 32 < L → ∀ R' Mt', R' 11 = BitVec.ofNat 64 (src + (c + 32)) →
      R' 14 = BitVec.ofNat 64 (d + (c + 32)) → R' 16 = R 16 → Keep3 R' R 11 13 14 →
      Copied Mt' Mt0 d src (c + 32) g → ReadWin Dt DA S Mt' src (src + len) g →
      NW live Dt DA S Q 0x80006a48#64 R' Mt')
    (hkX : c + 32 = L → ∀ R' Mt', R' 11 = BitVec.ofNat 64 (src + (c + 32)) →
      R' 14 = BitVec.ofNat 64 (d + (c + 32)) → Keep3 R' R 11 13 14 →
      Copied Mt' Mt0 d src (c + 32) g → NW live Dt DA S Q 0x80006a74#64 R' Mt') :
    NW live Dt DA S Q 0x80006a48#64 R Mt := by
  obtain ⟨hd1, hd2, hdS, hs1, hs2, hs3, hdisj⟩ := G
  have s0 : LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x000#12) = BitVec.ofNat 64 0 := by decide
  have s32 : LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x020#12) = BitVec.ofNat 64 32 := by decide
  have m32 : LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xfe0#12) = BitVec.ofNat 64 (2 ^ 64 - 32) := by decide
  have m24 : LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xfe8#12) = BitVec.ofNat 64 (2 ^ 64 - 24) := by decide
  have m16 : LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xff0#12) = BitVec.ofNat 64 (2 ^ 64 - 16) := by decide
  have m8 : LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (2 ^ 64 - 8) := by decide
  have eS : ∀ x k, x + k < 2 ^ 64 → (BitVec.ofNat 64 x + BitVec.ofNat 64 k) = BitVec.ofNat 64 (x + k) :=
    fun x k _ => ofNat_add_ofNat x k
  -- the four source loads and destination stores, as `Nat` addresses
  have a0 : (BitVec.ofNat 64 (src + c) + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x000#12)).toNat
      = src + c := by rw [ea_add s0 (by omega), Nat.add_zero]
  have eB : BitVec.ofNat 64 (src + c) + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x020#12) =
      BitVec.ofNat 64 (src + c + 32) := ofNat_add_sx s32
  have eA : BitVec.ofNat 64 (d + c) + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x020#12) =
      BitVec.ofNat 64 (d + c + 32) := ofNat_add_sx s32
  have d32 : ∀ x, 32 ≤ x → x < 2 ^ 64 → (BitVec.ofNat 64 x + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xfe0#12)).toNat = x - 32 :=
    fun x h1 h2 => ea_sub m32 h1 (by decide) h2
  have d24 : ∀ x, 24 ≤ x → x < 2 ^ 64 → (BitVec.ofNat 64 x + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xfe8#12)).toNat = x - 24 :=
    fun x h1 h2 => ea_sub m24 h1 (by decide) h2
  have d16 : ∀ x, 16 ≤ x → x < 2 ^ 64 → (BitVec.ofNat 64 x + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xff0#12)).toNat = x - 16 :=
    fun x h1 h2 => ea_sub m16 h1 (by decide) h2
  have d8 : ∀ x, 8 ≤ x → x < 2 ^ 64 → (BitVec.ofNat 64 x + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xff8#12)).toNat = x - 8 :=
    fun x h1 h2 => ea_sub m8 h1 (by decide) h2
  have ldw : ∀ (M : Mem) (c' : Nat), c' + 8 ≤ len → ReadWin Dt DA S M src (src + len) g →
      ∀ f : Nat → BitVec 8, (∀ p ∈ dataOf Dt DA, f p.1 = p.2) → (∀ a, S a → f a = imgM M a) →
      ldvf .ld f (src + c') = ldvf .ld g (src + c') :=
    fun M c' hc' hw' f hD hS => ldvf_readWin hw' hD hS .ld (by omega) (by simp only [widthOfM]; omega)
  have hsd : ∀ c', c' % 8 = 0 → c' + 8 ≤ len → StOK (d + c') 8 ∧ ∀ b ∈ accAddrs (d + c') 8, S b :=
    fun c' h8 hc' => ⟨by unfold StOK tohostAddr; omega, fun b hb => by
      rw [mem_accAddrs_iff] at hb; exact hdS b (by omega) (by omega)⟩
  refine itP_80006a48 hlive (by rw [h11, a0]; unfold LdOK tohostAddr; omega) fun v hv => ?_
  obtain ⟨f, hfD, hfS, rfl⟩ := hv
  rw [h11, a0, ldw Mt c (by omega) hw f hfD hfS]
  refine it_80006a4c hlive (it_80006a50 hlive ?_)
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h11, h14, eB, eA]
  refine it_80006a54 hlive ?_ ?_ ?_
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, d32 (d + c + 32) (by omega) (by omega),
    Nat.add_sub_cancel]
  · exact (hsd c hc8 (by omega)).1
  · exact (hsd c hc8 (by omega)).2
  obtain ⟨hcp1, hw1⟩ := hcp.sd_win hw hdisj (by omega)
  refine itP_80006a58 hlive ?_ fun v hv => ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, d24 (src + c + 32) (by omega) (by omega)]
    unfold LdOK tohostAddr; omega
  obtain ⟨f, hfD, hfS, rfl⟩ := hv
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, d24 (src + c + 32) (by omega) (by omega),
    show src + c + 32 - 24 = src + (c + 8) by omega, ldw _ (c + 8) (by omega) hw1 f hfD hfS]
  refine it_80006a5c hlive ?_ ?_ ?_
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, d24 (d + c + 32) (by omega) (by omega),
    show d + c + 32 - 24 = d + (c + 8) by omega]
  · exact (hsd (c + 8) (by omega) (by omega)).1
  · exact (hsd (c + 8) (by omega) (by omega)).2
  obtain ⟨hcp2, hw2⟩ := hcp1.sd_win hw1 hdisj (by omega)
  refine itP_80006a60 hlive ?_ fun v hv => ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, d16 (src + c + 32) (by omega) (by omega)]
    unfold LdOK tohostAddr; omega
  obtain ⟨f, hfD, hfS, rfl⟩ := hv
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, d16 (src + c + 32) (by omega) (by omega),
    show src + c + 32 - 16 = src + (c + 8 + 8) by omega, ldw _ (c + 8 + 8) (by omega) hw2 f hfD hfS]
  refine it_80006a64 hlive ?_ ?_ ?_
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, d16 (d + c + 32) (by omega) (by omega),
    show d + c + 32 - 16 = d + (c + 8 + 8) by omega]
  · exact (hsd (c + 8 + 8) (by omega) (by omega)).1
  · exact (hsd (c + 8 + 8) (by omega) (by omega)).2
  obtain ⟨hcp3, hw3⟩ := hcp2.sd_win hw2 hdisj (by omega)
  refine itP_80006a68 hlive ?_ fun v hv => ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, d8 (src + c + 32) (by omega) (by omega)]
    unfold LdOK tohostAddr; omega
  obtain ⟨f, hfD, hfS, rfl⟩ := hv
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, d8 (src + c + 32) (by omega) (by omega),
    show src + c + 32 - 8 = src + (c + 8 + 8 + 8) by omega, ldw _ (c + 8 + 8 + 8) (by omega) hw3 f hfD hfS]
  refine it_80006a6c hlive ?_ ?_ ?_
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, d8 (d + c + 32) (by omega) (by omega),
    show d + c + 32 - 8 = d + (c + 8 + 8 + 8) by omega]
  · exact (hsd (c + 8 + 8 + 8) (by omega) (by omega)).1
  · exact (hsd (c + 8 + 8 + 8) (by omega) (by omega)).2
  obtain ⟨hcp4, hw4⟩ := hcp3.sd_win hw3 hdisj (by omega)
  rw [show c + 8 + 8 + 8 + 8 = c + 32 by omega] at hcp4
  refine it_80006a70 hlive (fun hb => ?_) (fun hb => ?_)
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h16] at hb
  · refine hkL (Nat.lt_of_le_of_ne hc (fun e => hb (by rw [show d + c + 32 = d + L by omega])))
      _ _ ?_ ?_ ?_ ?_ hcp4 hw4
    all_goals first
      | (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [← Nat.add_assoc]; done)
      | (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; done)
      | k3_frame
  · refine hkX (by
      apply Classical.byContradiction; intro hne
      exact hb (ofNat_ne_of_lt (by omega) (by omega) (by omega))) _ _ ?_ ?_ ?_ hcp4
    all_goals first
      | (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [← Nat.add_assoc]; done)
      | k3_frame

/-- **`memmove`'s 32-byte loop** (`0x80006a48`), `m` blocks left: it copies
`[c, L)` and falls through at `0x80006a74`. -/
theorem mm_loop32 (hlive : ∀ p ∈ stdioText, live p.1) (d src len L : Nat) (g : Nat → BitVec 8)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (G : MoveGeom S d src len) (hd8 : d % 8 = 0) (hL : L ≤ len)
    (hk : ∀ R' Mt', Keep3 R' R0 11 13 14 → R' 11 = BitVec.ofNat 64 (src + L) →
      R' 14 = BitVec.ofNat 64 (d + L) → Copied Mt' Mt0 d src L g →
      NW live Dt DA S Q 0x80006a74#64 R' Mt') :
    ∀ m c (R : Nat → BitVec 64) (Mt : Mem), c + 32 * m = L → 0 < m → c % 8 = 0 →
      R 11 = BitVec.ofNat 64 (src + c) → R 14 = BitVec.ofNat 64 (d + c) →
      R 16 = BitVec.ofNat 64 (d + L) → Keep3 R R0 11 13 14 → Copied Mt Mt0 d src c g →
      ReadWin Dt DA S Mt src (src + len) g →
      NW live Dt DA S Q 0x80006a48#64 R Mt := by
  intro m
  induction m with
  | zero => intro _ _ _ _ h; omega
  | succ m ih =>
    intro c R Mt hcm _ hc8 h11 h14 h16 hkp hcp hw
    refine mm32_step hlive d src len L c g R Mt Mt0 G hd8 hL (by omega) hc8 hw hcp h11 h14 h16
      ?_ ?_
    · intro hlt R' Mt' h11' h14' h16' hkp' hcp' hw'
      exact ih (c + 32) R' Mt' (by omega) (by omega) (by omega) h11' h14' (h16'.trans h16)
        (hkp.trans hkp') hcp' hw'
    · intro heq R' Mt' h11' h14' hkp' hcp'
      rw [heq] at h11' h14' hcp'
      exact hk R' Mt' (hkp.trans hkp') h11' h14' hcp'

/-- **`memmove`'s byte tail** (`0x800069fc`): `k` bytes left after `c`
copied, `a5 = d + c`, `a1 = src + c`, `a2 = k`. At the `ret` the copy is
complete. -/
theorem mm_tail (hlive : ∀ p ∈ stdioText, live p.1) (d src len c k : Nat) (g : Nat → BitVec 8)
    (R R0 : Nat → BitVec 64) (Mt Mt0 : Mem) (G : MoveGeom S d src len) (hck : c + k = len)
    (hw : ReadWin Dt DA S Mt0 src (src + len) g) (hcp : Copied Mt Mt0 d src c g)
    (h12 : R 12 = BitVec.ofNat 64 k) (h15 : R 15 = BitVec.ofNat 64 (d + c))
    (h11 : R 11 = BitVec.ofNat 64 (src + c)) (hkp : MMFrame R R0) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', MMFrame R' R0 → Copied Mt' Mt0 d src len g → NW live Dt DA S Q (R0 1) R' Mt') :
    NW live Dt DA S Q 0x800069fc#64 R Mt := by
  have G' := G
  obtain ⟨hd1, hd2, hdS, hs1, hs2, hs3, hdisj⟩ := G'
  have hR1 : R 1 = R0 1 := hkp 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  refine it_800069fc hlive (it_80006a00 hlive (fun hb => ?_) (fun hb => ?_))
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12] at hb
  · have hk0 : k = 0 := by
      have := congrArg BitVec.toNat hb; simp only [BitVec.toNat_ofNat] at this; omega
    subst hk0
    rw [Nat.add_zero] at hck
    subst hck
    refine it_80006ae0 hlive ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hR1]; exact hal
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hR1]
      exact hk _ Mt (hkp.trans (by mm_frame)) hcp
  · have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact (hb (by rw [h])).elim
      · exact h
    refine it_80006a04 hlive (it_80006a08 hlive ?_)
    refine mm_byteLoop hlive d src len g R0 Mt0 G hw hal hk k c _ Mt hck hk0 ?_ ?_ ?_ ?_ hcp
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h15
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h11
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12, h15, BitVec.add_assoc]
      rw [show LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xfff#12) +
          LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x001#12) = 0#64 by decide,
        BitVec.add_zero, ofNat_add_ofNat, ← hck, Nat.add_assoc]
    · refine hkp.trans' ?_; mm_frame

/-- **`memmove`'s 8-byte loop** (`0x80006aac`), `m` words left: `a6 = d - src`,
the loop ends when `a1` reaches `src + E`. -/
theorem mm_loop8 (hlive : ∀ p ∈ stdioText, live p.1) (d src len E : Nat) (g : Nat → BitVec 8)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (G : MoveGeom S d src len) (hd8 : d % 8 = 0) (hE : E ≤ len)
    (hk : ∀ R' Mt', Keep3 R' R0 6 11 17 → R' 11 = BitVec.ofNat 64 (src + E) → Copied Mt' Mt0 d src E g →
      NW live Dt DA S Q 0x80006ac0#64 R' Mt') :
    ∀ m c (R : Nat → BitVec 64) (Mt : Mem), c + 8 * m = E → 0 < m → c % 8 = 0 →
      R 11 = BitVec.ofNat 64 (src + c) → R 14 = BitVec.ofNat 64 (src + E) →
      R 16 = BitVec.ofNat 64 (d + (2 ^ 64 - src)) → Keep3 R R0 6 11 17 → Copied Mt Mt0 d src c g →
      ReadWin Dt DA S Mt src (src + len) g →
      NW live Dt DA S Q 0x80006aac#64 R Mt := by
  have G' := G
  obtain ⟨hd1, hd2, hdS, hs1, hs2, hs3, hdisj⟩ := G'
  have s0 : LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x000#12) = BitVec.ofNat 64 0 := by decide
  have s8 : LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 8 := by decide
  intro m
  induction m with
  | zero => intro _ _ _ _ h; omega
  | succ m ih =>
    intro c R Mt hcm _ hc8 h11 h14 h16 hkp hcp hw
    have a0 : (BitVec.ofNat 64 (src + c) + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x000#12)).toNat
        = src + c := by rw [ea_add s0 (by omega), Nat.add_zero]
    have e7 : BitVec.ofNat 64 (src + c) + BitVec.ofNat 64 (d + (2 ^ 64 - src)) = BitVec.ofNat 64 (d + c) := by
      rw [ofNat_add_ofNat]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
    have a7 : (BitVec.ofNat 64 (d + c) + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x000#12)).toNat
        = d + c := by rw [ea_add s0 (by omega), Nat.add_zero]
    refine itP_80006aac hlive (by rw [h11, a0]; unfold LdOK tohostAddr; omega) fun v hv => ?_
    obtain ⟨f, hfD, hfS, rfl⟩ := hv
    rw [h11, a0, ldvf_readWin hw hfD hfS .ld (by omega) (by simp only [widthOfM]; omega)]
    refine it_80006ab0 hlive (it_80006ab4 hlive (it_80006ab8 hlive ?_ ?_ ?_))
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h11, h16, e7, a7]
    · unfold StOK tohostAddr; omega
    · intro b hb; rw [mem_accAddrs_iff] at hb; exact hdS b (by omega) (by omega)
    obtain ⟨hcp1, hw1⟩ := hcp.sd_win hw hdisj (by omega)
    refine it_80006abc hlive (fun hb => ?_) (fun hb => ?_)
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h14, ofNat_add_sx s8] at hb
    · have hm : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · exact absurd (by rw [show src + c + 8 = src + E by omega]) hb
        · exact h0
      refine ih (c + 8) _ _ (by omega) hm (by omega) ?_ ?_ ?_ ?_ hcp1 hw1
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h11, ofNat_add_sx s8]
        rw [Nat.add_assoc]
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h14
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h16
      · refine hkp.trans ?_; k3_frame
    · have hE8 : c + 8 = E := by
        apply Classical.byContradiction; intro hne
        exact hb (ofNat_ne_of_lt (by omega) (by omega) (by omega))
      refine hk _ _ (hkp.trans (by k3_frame)) ?_ (hE8 ▸ hcp1)
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h11, ofNat_add_sx s8]
      rw [Nat.add_assoc, hE8]

/-! ## Mask arithmetic -/

section Masks

open Sail LeanRV64DExecutable.Functions

theorem and_low5 (n c : Nat) (hc : c < 32) : n &&& c = (n % 32) &&& c := by
  have h1 : (n &&& c) % 2 ^ 5 = (n % 2 ^ 5) &&& (c % 2 ^ 5) := Nat.and_mod_two_pow ..
  rw [Nat.mod_eq_of_lt (show c < 2 ^ 5 by omega),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right (show c < 2 ^ 5 by omega))] at h1
  simpa using h1

theorem mask_ofNat {n c : Nat} (hn : n < 2 ^ 64) (hc : c < 32) {imm : BitVec 12}
    (himm : sign_extend (m := 64) imm = BitVec.ofNat 64 c) :
    BitVec.ofNat 64 n &&& sign_extend (m := 64) imm = BitVec.ofNat 64 ((n % 32) &&& c) := by
  rw [himm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
  rw [and_low5 n c hc, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right (show c < 2 ^ 64 by omega))]

theorem and24 (r : Nat) (h : r < 32) : r &&& 24 = r / 8 * 8 := by revert r; decide
theorem and31 (r : Nat) (h : r < 32) : r &&& 31 = r := by revert r; decide
theorem and7 (r : Nat) (h : r < 32) : r &&& 7 = r % 8 := by revert r; decide

theorem srl5_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    shift_bits_right (BitVec.ofNat 64 n) (Sail.BitVec.extractLsb (0x05#6) 5 0) = BitVec.ofNat 64 (n / 32) := by
  simp only [shift_bits_right, Sail.BitVec.extractLsb, BitVec.reduceExtractLsb, BitVec.ushiftRight_eq',
    BitVec.reduceToNat]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

theorem sll5_ofNat {n : Nat} (hn : n * 32 < 2 ^ 64) :
    shift_bits_left (BitVec.ofNat 64 n) (Sail.BitVec.extractLsb (0x05#6) 5 0) = BitVec.ofNat 64 (n * 32) := by
  simp only [shift_bits_left, Sail.BitVec.extractLsb, BitVec.reduceExtractLsb, BitVec.shiftLeft_eq',
    BitVec.reduceToNat]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem or_and7_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b) &&& sign_extend (m := 64) (0x007#12) = 0#64 ↔
      a % 8 = 0 ∧ b % 8 = 0 := by
  rw [show sign_extend (m := 64) (0x007#12) = BitVec.ofNat 64 7 by decide]
  have key : (a ||| b) &&& 7 = a % 8 ||| b % 8 := by
    rw [show (7 : Nat) = 2 ^ 3 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.or_mod_two_pow]
  have e : ((BitVec.ofNat 64 a ||| BitVec.ofNat 64 b) &&& BitVec.ofNat 64 7).toNat = a % 8 ||| b % 8 := by
    simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb, Nat.reducePow, Nat.reduceMod]
    exact key
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [e] at this
    have h2 := Nat.or_eq_zero_iff.mp (by simpa using this)
    omega
  · intro ⟨h1, h2⟩
    apply BitVec.eq_of_toNat_eq
    rw [e, h1, h2]; rfl

/-- `(r - 8) & ~7` for `8 ≤ r < 32`. -/
theorem sub8_mask (r : Nat) (h2 : r < 32) (h1 : 8 ≤ r) :
    (BitVec.ofNat 64 r + sign_extend (m := 64) (0xff8#12)) &&& sign_extend (m := 64) (0xff8#12) =
      BitVec.ofNat 64 ((r - 8) / 8 * 8) := by
  revert r; decide

end Masks

/-! ## The whole call -/

section Run

open Sail LeanRV64DExecutable.Functions

/-- Register lookups through an `upd` chain. -/
syntax "rsimp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| rsimp $[$loc]?) =>
    `(tactic| simp (config := {failIfUnchanged := false}) only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] $[$loc]?)

/-- After the 32-byte loop (`0x80006a74`): the 8-byte loop when a word is
left, then the byte tail. -/
theorem mm_after32 (hlive : ∀ p ∈ stdioText, live p.1) (d src len : Nat) (g : Nat → BitVec 8)
    (R R0 : Nat → BitVec 64) (Mt Mt0 : Mem) (G : MoveGeom S d src len) (hd8 : d % 8 = 0)
    (hs8 : src % 8 = 0) (h32 : 32 ≤ len) (hw : ReadWin Dt DA S Mt0 src (src + len) g)
    (hcp : Copied Mt Mt0 d src (len / 32 * 32) g)
    (h10 : R 10 = BitVec.ofNat 64 d) (h12 : R 12 = BitVec.ofNat 64 len)
    (h15 : R 15 = BitVec.ofNat 64 (len / 32 - 1)) (h17 : R 17 = BitVec.ofNat 64 src)
    (hkp : MMFrame R R0) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', MMFrame R' R0 → Copied Mt' Mt0 d src len g → NW live Dt DA S Q (R0 1) R' Mt') :
    NW live Dt DA S Q 0x80006a74#64 R Mt := by
  have G' := G
  obtain ⟨hd1, hd2, hdS, hs1, hs2, hs3, hdisj⟩ := G'
  have hm : 1 ≤ len / 32 := by omega
  have e32 : sign_extend (m := 64) (0x020#12) = BitVec.ofNat 64 32 := by decide
  have e0 : sign_extend (m := 64) (0x000#12) = BitVec.ofNat 64 0 := by decide
  have e24 : sign_extend (m := 64) (0x018#12) = BitVec.ofNat 64 24 := by decide
  have e31 : sign_extend (m := 64) (0x01f#12) = BitVec.ofNat 64 31 := by decide
  have e7 : sign_extend (m := 64) (0x007#12) = BitVec.ofNat 64 7 := by decide
  have e8 : sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 8 := by decide
  have e40 : sign_extend (m := 64) (0x028#12) = BitVec.ofNat 64 40 := by decide
  have hL : (len / 32 - 1) * 32 + 32 = len / 32 * 32 := by
    rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel (by omega)]
  have hr : len % 32 < 32 := Nat.mod_lt _ (by omega)
  refine it_80006a74 hlive (it_80006a78 hlive (it_80006a7c hlive (it_80006a80 hlive
    (it_80006a84 hlive (it_80006a88 hlive (it_80006a8c hlive (it_80006a90 hlive
    (it_80006a94 hlive (fun hb => ?_) (fun hb => ?_)))))))))
  all_goals rsimp at hb
  all_goals simp only [h12, mask_ofNat (n := len) (by omega) (by omega) e24, and24 _ hr] at hb
  · -- no word left: the byte tail from `len / 32 * 32`
    have hw0 : len % 32 / 8 * 8 = 0 := by
      have := congrArg BitVec.toNat hb; simp only [BitVec.toNat_ofNat] at this; omega
    refine it_80006ae4 hlive (it_80006ae8 hlive ?_)
    refine mm_tail hlive d src len (len / 32 * 32) (len % 32) g _ R0 Mt Mt0 G (by omega) hw hcp
      ?_ ?_ ?_ ?_ hal hk
    · rsimp; rw [h12, mask_ofNat (n := len) (by omega) (by omega) e31, and31 _ hr, ofNat_add_sx e0]; rfl
    · rsimp
      rw [h15, sll5_ofNat (by omega), h10, ofNat_add_ofNat, ofNat_add_sx e32, Nat.add_assoc, hL]
    · rsimp
      rw [h15, sll5_ofNat (by omega), h17, ofNat_add_ofNat, ofNat_add_sx e32,
        show (len / 32 - 1) * 32 + src + 32 = src + len / 32 * 32 by omega]
    · refine hkp.trans' ?_; mm_frame
  · -- the 8-byte loop over `[L, E)`, then the byte tail
    have hw8 : 8 ≤ len % 32 := by
      apply Classical.byContradiction; intro hlt
      exact hb (by rw [show len % 32 / 8 * 8 = 0 by omega])
    refine it_80006a98 hlive (it_80006a9c hlive (it_80006aa0 hlive (it_80006aa4 hlive
      (it_80006aa8 hlive ?_))))
    have eT : ∀ R' : Nat → BitVec 64, R' 12 = BitVec.ofNat 64 len →
        ((R' 12 &&& sign_extend (m := 64) (0x01f#12)) + sign_extend (m := 64) (0xff8#12)) &&&
          sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 ((len % 32 - 8) / 8 * 8) := by
      intro R' h; rw [h, mask_ofNat (n := len) (by omega) (by omega) e31, and31 _ hr, sub8_mask _ hr hw8]
    refine mm_loop8 hlive d src len (len / 32 * 32 + len % 32 / 8 * 8) g _ Mt0 G hd8 (by omega)
      ?_ (len % 32 / 8) (len / 32 * 32) _ Mt (by omega) (by omega) (by omega) ?_ ?_ ?_ (fun _ _ _ _ => rfl)
      hcp (hw.transport fun a h1 h2 => hcp.rest a (by omega))
    · intro R' Mt' hk3 h11' hcp'
      refine it_80006ac0 hlive (it_80006ac4 hlive (it_80006ac8 hlive (it_80006acc hlive
        (it_80006ad0 hlive ?_))))
      have k13 := hk3 13 (by decide) (by decide) (by decide)
      have k28 := hk3 28 (by decide) (by decide) (by decide)
      have k15 := hk3 15 (by decide) (by decide) (by decide)
      have k12 := hk3 12 (by decide) (by decide) (by decide)
      rsimp at k13 k28 k15 k12
      refine mm_tail hlive d src len (len / 32 * 32 + len % 32 / 8 * 8) (len % 8) g _ R0 Mt' Mt0 G
        (by omega) hw hcp' ?_ ?_ ?_ ?_ hal hk
      · rsimp; rw [k12, h12, mask_ofNat (n := len) (by omega) (by omega) e7, and7 _ hr, Nat.mod_mod_of_dvd _ (by decide)]
      · rsimp
        rw [k13, eT _ h12, k15, h15, sll5_ofNat (by omega), h10, ofNat_add_ofNat,
          ofNat_add_sx e32, ofNat_add_sx e8, ofNat_add_ofNat]
        congr 1; omega
      · rsimp
        rw [k13, eT _ h12, k28, h15, sll5_ofNat (by omega), h17, ofNat_add_ofNat,
          ofNat_add_sx e32, ofNat_add_sx e0, ofNat_add_sx e8, ofNat_add_ofNat]
        congr 1; omega
      · intro z a1 a2 a3 a4 a5 a6 a7 a8 a9
        rsimp; simp only [a1, a2, a3, a4, a5, a6, a7, a8, a9, ite_false]
        rw [hk3 z a8 a1 a7]; rsimp; simp only [a1, a2, a3, a4, a5, a6, a7, a8, a9, ite_false]
        exact hkp z a1 a2 a3 a4 a5 a6 a7 a8 a9
    · rsimp
      rw [h15, sll5_ofNat (by omega), h17, ofNat_add_ofNat, ofNat_add_sx e32,
        show (len / 32 - 1) * 32 + src + 32 = src + len / 32 * 32 by omega]
    · rsimp
      rw [eT _ h12, h15, sll5_ofNat (by omega), h17, ofNat_add_ofNat, ofNat_add_ofNat, ofNat_add_sx e40]
      congr 1; omega
    · rsimp; rw [h10, h17, ofNat_sub_ofNat _ _ (by omega)]

/-- The forward copy (`0x800069f0`): the byte loop for `len ≤ 31` or a
misaligned pair, otherwise the 32-byte, 8-byte and byte loops. -/
theorem mm_fwd (hlive : ∀ p ∈ stdioText, live p.1) (d src len : Nat) (g : Nat → BitVec 8)
    (R R0 : Nat → BitVec 64) (Mt : Mem) (G : MoveGeom S d src len)
    (hw : ReadWin Dt DA S Mt src (src + len) g)
    (h10 : R 10 = BitVec.ofNat 64 d) (h11 : R 11 = BitVec.ofNat 64 src)
    (h12 : R 12 = BitVec.ofNat 64 len) (hkp : MMFrame R R0) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', MMFrame R' R0 → Copied Mt' Mt d src len g → NW live Dt DA S Q (R0 1) R' Mt') :
    NW live Dt DA S Q 0x800069f0#64 R Mt := by
  have G' := G
  obtain ⟨hd1, hd2, hdS, hs1, hs2, hs3, hdisj⟩ := G'
  have e0 : sign_extend (m := 64) (0x000#12) = BitVec.ofNat 64 0 := by decide
  have e31 : sign_extend (m := 64) (0x01f#12) = BitVec.ofNat 64 31 := by decide
  have e1 : sign_extend (m := 64) (0xfff#12) + sign_extend (m := 64) (0x001#12) = 0#64 := by decide
  refine it_800069f0 hlive (it_800069f4 hlive (fun hc => ?_) (fun hc => ?_))
  all_goals rsimp at hc
  all_goals rw [show (0#64 : BitVec 64) + sign_extend (m := 64) (0x01f#12) = BitVec.ofNat 64 31 by decide,
    h12] at hc
  all_goals simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)] at hc
  · -- `len > 31`
    refine it_80006a24 hlive (it_80006a28 hlive (it_80006a2c hlive (it_80006a30 hlive
      (fun hb => ?_) (fun hb => ?_))))
    all_goals rsimp at hb
    all_goals rw [h10, h11, Ne, or_and7_zero (by omega) (by omega)] at hb
    all_goals try have hb := Classical.not_not.mp hb
    · -- misaligned: the byte loop from the start
      refine it_80006ad4 hlive (it_80006ad8 hlive (it_80006adc hlive (it_80006a04 hlive
        (it_80006a08 hlive ?_))))
      refine mm_byteLoop hlive d src len g R0 Mt G hw hal hk len 0 _ Mt (by omega) (by omega)
        ?_ ?_ ?_ ?_ (Copied.zero Mt d src g)
      · rsimp; rw [h10, ofNat_add_sx e0]
      · rsimp; rw [h11]; rfl
      · rsimp
        rw [h10, h12, BitVec.add_assoc (BitVec.ofNat 64 len), e1, BitVec.add_zero, e0, ofNat_add_ofNat, ofNat_add_ofNat,
          Nat.add_zero]
      · refine hkp.trans' ?_; mm_frame
    · -- aligned: the 32-byte loop over `[0, len / 32 * 32)`
      have hd8 : d % 8 = 0 := hb.1
      refine it_80006a34 hlive (it_80006a38 hlive (it_80006a3c hlive (it_80006a40 hlive
        (it_80006a44 hlive ?_))))
      refine mm_loop32 hlive d src len (len / 32 * 32) g _ Mt G hd8 (Nat.div_mul_le_self _ _) ?_
        (len / 32) 0 _ Mt (by omega) (by omega) (by omega) ?_ ?_ ?_ (fun _ _ _ _ => rfl)
        (Copied.zero Mt d src g) hw
      · intro R' Mt' hk3 _ _ hcp
        have k10 := hk3 10 (by decide) (by decide) (by decide)
        have k12 := hk3 12 (by decide) (by decide) (by decide)
        have k15 := hk3 15 (by decide) (by decide) (by decide)
        have k17 := hk3 17 (by decide) (by decide) (by decide)
        rsimp at k10 k12 k15 k17
        refine mm_after32 hlive d src len g R' R0 Mt' Mt G hd8 hb.2 (by omega) hw hcp
          (by rw [k10, h10]) (by rw [k12, h12]) ?_ (by rw [k17, h11, ofNat_add_sx e0, Nat.add_zero]) ?_ hal hk
        · rw [k15, h12, srl5_ofNat (by omega), show sign_extend (m := 64) (0xfff#12) =
            BitVec.ofNat 64 (2 ^ 64 - 1) by decide, ofNat_add_ofNat]
          apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
        · intro z a1 a2 a3 a4 a5 a6 a7 a8 a9
          rw [hk3 z a1 a3 a4]; rsimp; simp only [a1, a2, a3, a4, a5, a6, a7, a8, a9, ite_false]
          exact hkp z a1 a2 a3 a4 a5 a6 a7 a8 a9
      · rsimp; rw [h11, Nat.add_zero]
      · rsimp; rw [h10, ofNat_add_sx e0, Nat.add_zero]
      · rsimp; rw [h12, srl5_ofNat (by omega), sll5_ofNat (by omega), h10, ofNat_add_ofNat]
  · -- `len ≤ 31`: the byte tail from the start
    refine it_800069f8 hlive ?_
    refine mm_tail hlive d src len 0 len g _ R0 Mt Mt G (by omega) hw (Copied.zero Mt d src g)
      ?_ ?_ ?_ ?_ hal hk
    · rsimp; exact h12
    · rsimp; rw [h10, ofNat_add_sx e0]
    · rsimp; rw [h11]; rfl
    · refine hkp.trans' ?_; mm_frame

/-- **`memmove(d, src, len)`** with disjoint ranges: the destination holds
the window's bytes, nothing else changed, `a0 = d`, back at `ra`. -/
theorem memmove_run (hlive : ∀ p ∈ stdioText, live p.1) (d src len : Nat) (g : Nat → BitVec 8)
    (R : Nat → BitVec 64) (Mt : Mem) (G : MoveGeom S d src len)
    (hw : ReadWin Dt DA S Mt src (src + len) g)
    (h10 : R 10 = BitVec.ofNat 64 d) (h11 : R 11 = BitVec.ofNat 64 src)
    (h12 : R 12 = BitVec.ofNat 64 len) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', MMFrame R' R → Copied Mt' Mt d src len g → NW live Dt DA S Q (R 1) R' Mt') :
    NW live Dt DA S Q 0x800069c4#64 R Mt := by
  have G' := G
  obtain ⟨hd1, hd2, hdS, hs1, hs2, hs3, hdisj⟩ := G'
  refine it_800069c4 hlive (fun hc => ?_) (fun hc => ?_)
  · exact mm_fwd hlive d src len g R R Mt G hw h10 h11 h12 (MMFrame.refl R) hal hk
  · rw [h10, h11, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hc
    refine it_800069c8 hlive (it_800069cc hlive (fun hc2 => ?_) (fun hc2 => ?_))
    · exact mm_fwd hlive d src len g _ R Mt G hw (by rsimp; exact h10) (by rsimp; exact h11)
        (by rsimp; exact h12) (by mm_frame) hal hk
    · exfalso; apply hc2
      rsimp; rw [h10, h11, h12, ofNat_add_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

end Run

end VsaIris.Sym.Fp
