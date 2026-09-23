import VsaIris.Interp.EnvTac
import VsaIris.Interp.EnvSpan

/-!
# `env_get`'s spans, first-order

`env_get` (`0x80002c10`) and `env_set` (`0x80002cdc`) are the same code up to
the hit arm (`env.c:43`, `env.c:56`). Each call-free span is one lemma here,
proved by `sx_run` over the generated step table; the Iris proof
(`ProofEnvGet.lean`) strings them together around the `strcmp` calls.

The spans and their exits:

* `get_entry` `0x80002c10` → `0x80002c40` (the frame head), the prologue.
* `get_head` `0x80002c40` → `0x80002cc4` (empty frame) | `0x80002c60`
  (scan start).
* `get_load` `0x80002c60` → `0x80002c68` (`jal strcmp`), the name load.
* `get_cmp` `0x80002c6c` → `0x80002c60` (next name) | `0x80002cc4` (frame
  exhausted) | return (hit: the value copied into `out`).
* `get_parent` `0x80002cc4` → `0x80002c40` (parent frame) | return (miss).

Between spans the stack frame is described by `GetStack`: `sp = s - 64` and
the seven spilled words, as loads from the tracking memory.
-/

namespace VsaIris.Interp

open VsaIris.Sym VsaIris.MallocFast Vsa.MemRepr Vsa.Sim

/-- The stack frame after `env_get`'s prologue (entry `sp = s`): `sp = s -
64`, and the spilled `ra`, `s0-s5` at `s - 8`, `s - 16`, … `s - 56`. -/
structure GetStack (s : Nat) (r : BitVec 64) (sv : Nat → BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) : Prop where
  sp : (R 2).toNat = s - 64
  ra : ldv .ld Mt (s - 8) = r
  s0 : ldv .ld Mt (s - 16) = sv 8
  s1 : ldv .ld Mt (s - 24) = sv 9
  s2 : ldv .ld Mt (s - 32) = sv 18
  s3 : ldv .ld Mt (s - 40) = sv 19
  s4 : ldv .ld Mt (s - 48) = sv 20
  s5 : ldv .ld Mt (s - 56) = sv 21

/-- A load reads only its window. -/
theorem ldv_congr (k : MKind) {Mt Mt' : Mem} {a : Nat}
    (h : ∀ j, j < widthOfM k → imgM Mt (a + j) = imgM Mt' (a + j)) : ldv k Mt a = ldv k Mt' a := by
  unfold ldv bytesAt
  congr 1
  apply List.map_congr_left
  intro j hj
  exact h j (List.mem_range.1 hj)

/-- `GetStack` reads only the stack frame. -/
theorem GetStack.congr {s : Nat} {r : BitVec 64} {sv : Nat → BitVec 64} {R R' : Nat → BitVec 64}
    {Mt Mt' : Mem} (h : GetStack s r sv R Mt) (h2 : R' 2 = R 2)
    (hm : ∀ a, s - 64 ≤ a → a < s → imgM Mt' a = imgM Mt a) (hs : 64 ≤ s) :
    GetStack s r sv R' Mt' := by
  have c : ∀ o, 8 ≤ o → o ≤ 64 → ldv .ld Mt' (s - o) = ldv .ld Mt (s - o) := fun o h1 h2 =>
    ldv_congr .ld fun j hj => hm _ (by simp [widthOfM] at hj; omega) (by simp [widthOfM] at hj; omega)
  exact ⟨by rw [h2]; exact h.sp, (c 8 (by omega) (by omega)).trans h.ra,
    (c 16 (by omega) (by omega)).trans h.s0, (c 24 (by omega) (by omega)).trans h.s1,
    (c 32 (by omega) (by omega)).trans h.s2, (c 40 (by omega) (by omega)).trans h.s3,
    (c 48 (by omega) (by omega)).trans h.s4, (c 56 (by omega) (by omega)).trans h.s5⟩

/-- The entry's register values: `a0 = env ≠ 0`, the caller's `sp`, `ra` and
callee-saved registers. -/
structure GetEntry (s : Nat) (r : BitVec 64) (sv : Nat → BitVec 64) (R : Nat → BitVec 64) :
    Prop where
  env : R 10 ≠ 0#64
  sp : (R 2).toNat = s
  ra : R 1 = r
  saved : ∀ k ∈ getSaved, R k = sv k

/-- The frame head: the prologue done, `s3` the name, `s4` the frame, `s5`
the output slot. -/
structure GetHead (s : Nat) (r : BitVec 64) (sv : Nat → BitVec 64) (e name out : BitVec 64)
    (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  stack : GetStack s r sv R Mt
  name : R 19 = name
  frame : R 20 = e
  out : R 21 = out

theorem get_entry {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s : Nat} {r : BitVec 64}
    {sv : Nat → BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hlo : htifLo + 16 + 64 ≤ s) (hhi : s ≤ 0x100000000) (hal : s % 16 = 0)
    (h : GetEntry s r sv R) :
    Span live (fun a => s - 64 ≤ a ∧ a < s) 0x80002c10#64 R Mt
      (fun pc' R' Mt' => pc' = 0x80002c40#64 ∧ GetHead s r sv (R 10) (R 11) (R 12) R' Mt') := by
  intro Q hk
  have he := h.env
  have h2 := h.sp
  sx_run hl at 0x80002c40
  refine hk _ _ _ ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals (try sx_norm)
  all_goals (try sx_mem)
  · rw [BitVec.toNat_add, h2]; simp only [BitVec.reduceToNat]; omega
  · exact h.ra
  all_goals exact h.saved _ (by decide)

/-- The bytes a frame span owns: `env_get`'s stack frame, the output slot and
the current frame's blocks. -/
def getS (s out : Nat) (G : FrameGeom) (a : Nat) : Prop :=
  (s - 64 ≤ a ∧ a < s) ∨ (out ≤ a ∧ a < out + 24) ∨ frameS G a

macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; have hb' := of_mem_accAddrs hb; simp only [InExt, frameS, getS, htifLo] at *; sx_addr))

/-- `BitVec.toInt` of a small literal. -/
theorem toInt_ofNat_small {n : Nat} (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show 2 * n < 2 ^ 64 by omega, ite_true]

/-- A frame's count is below `2^31` (the `lw` sign-extends it): the names
array holds `8 * cap` bytes of 32-bit RAM. -/
theorem FrameLayout.count_lt {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : FrameLayout img G n) : n < 2 ^ 31 := by
  have hle := h.count_le
  rcases Nat.eq_zero_or_pos G.cap with h0 | hpos
  · omega
  obtain ⟨h1, h2, -, -⟩ := h.arrays hpos
  have hw := h.win G.nblk (by simp [FrameGeom.blocks, show G.cap ≠ 0 by omega])
  have := hw.lo; have := hw.hi
  omega

/-- The head of a frame's scan, or its end. -/
structure HeadScan (G : FrameGeom) (n : Nat) (R R' : Nat → BitVec 64) : Prop where
  keep : ∀ k, k ≠ 8 → k ≠ 9 → k ≠ 18 → R' k = R k
  idx : R' 8 = 0#64
  cur : R' 9 = BitVec.ofNat 64 G.pn
  cnt : R' 18 = BitVec.ofNat 64 n

theorem get_head {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s out n : Nat}
    {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem}
    (hlay : FrameLayout (imgM Mt) G n) (he : (R 20).toNat = G.e) :
    Span live (getS s out G) 0x80002c40#64 R Mt
      (fun pc' R' Mt' => Mt' = Mt ∧
        ((n = 0 ∧ pc' = 0x80002cc4#64 ∧ ∀ k, k ≠ 18 → R' k = R k) ∨
         (0 < n ∧ pc' = 0x80002c60#64 ∧ HeadScan G n R R'))) := by
  intro Q hk
  have hn := hlay.count_lt
  have hw := hlay.win G.sblk (by simp [FrameGeom.blocks])
  have hsb := hlay.sblk
  have hea := hlay.e_align
  have := hw.lo; have := hw.hi; have := hw.htif
  have hld : ldv .lw Mt (R 20).toNat = BitVec.ofNat 64 n := by
    rw [he]; exact ldv_lw_img Mt _ n hn hlay.count
  have hint : (BitVec.ofNat 64 n).toInt = n := toInt_ofNat_small (by omega)
  sx_run hl at 0x80002cc4 0x80002c60
  · intro hc
    rw [upd_same, hld, hint] at hc
    exact hk _ _ _ ⟨rfl, .inl ⟨by simp at hc; omega, rfl, fun k hk => upd_other _ _ hk⟩⟩
  · intro hc
    rw [upd_same, hld, hint] at hc
    sx_run hl at 0x80002c60
    have h8 : (R 20 + 8#64).toNat = G.e + 8 := by rw [BitVec.toNat_add, he]; simp; omega
    refine hk _ _ _ ⟨rfl, .inr ⟨by simp at hc; omega, rfl, ⟨fun k h8' h9 h18 => ?_, rfl, ?_, ?_⟩⟩⟩
    · simp [upd_apply, h8', h9, h18]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [h8, ldv_ld_img]; unfold imgW; rw [hlay.names]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hld

/-- The pure facts of a frame's arrays the scan reads, at slot `i < n`. -/
theorem FrameLayout.slot {img : Nat → BitVec 8} {G : FrameGeom} {n i : Nat}
    (h : FrameLayout img G n) (hi : i < n) :
    G.cap ≠ 0 ∧ G.nblk.1 = G.pn ∧ G.pn + 8 * i + 8 ≤ G.nblk.1 + G.nblk.2 ∧
      G.vblk.1 = G.pv ∧ G.pv + 24 * i + 24 ≤ G.vblk.1 + G.vblk.2 ∧
      BlockWin G.nblk ∧ BlockWin G.vblk := by
  have hle := h.count_le
  have hpos : 0 < G.cap := by omega
  obtain ⟨h1, h2, h3, h4⟩ := h.arrays hpos
  refine ⟨by omega, h1, by omega, h3, by omega,
    h.win _ (by simp [FrameGeom.blocks, show G.cap ≠ 0 by omega]),
    h.win _ (by simp [FrameGeom.blocks, show G.cap ≠ 0 by omega])⟩

theorem get_load {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s out n i : Nat}
    {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem}
    (hlay : FrameLayout (imgM Mt) G n) (hi : i < n) (h9 : (R 9).toNat = G.pn + 8 * i) :
    Span live (getS s out G) 0x80002c60#64 R Mt
      (fun pc' R' Mt' => Mt' = Mt ∧ pc' = 0x80002c68#64 ∧
        R' 10 = imgW (imgM Mt) (G.pn + 8 * i) ∧ R' 11 = R 19 ∧
        ∀ k, k ≠ 10 → k ≠ 11 → R' k = R k) := by
  intro Q hk
  obtain ⟨hcap, hn1, hn2, -, -, hw, -⟩ := hlay.slot hi
  have := hw.lo; have := hw.hi; have := hw.htif; have := hw.align
  sx_run hl at 0x80002c68
  refine hk _ _ _ ⟨rfl, rfl, ?_, ?_, fun k h10 h11 => ?_⟩
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [h9, ldv_ld_img]
  · simp
  · simp [upd_apply, h10, h11]

/-- The epilogue's loads read back the spilled words. -/
theorem GetStack.restore {s : Nat} {r : BitVec 64} {sv : Nat → BitVec 64} {R : Nat → BitVec 64}
    {Mt : Mem} (h : GetStack s r sv R Mt) (hs : 64 ≤ s) (hs' : s ≤ 0x100000000) :
    ldv .ld Mt (R 2 + 56#64).toNat = r ∧ ldv .ld Mt (R 2 + 48#64).toNat = sv 8 ∧
    ldv .ld Mt (R 2 + 40#64).toNat = sv 9 ∧ ldv .ld Mt (R 2 + 32#64).toNat = sv 18 ∧
    ldv .ld Mt (R 2 + 24#64).toNat = sv 19 ∧ ldv .ld Mt (R 2 + 16#64).toNat = sv 20 ∧
    ldv .ld Mt (R 2 + 8#64).toNat = sv 21 := by
  have hsp := h.sp
  have e : ∀ c : Nat, c < 64 → (R 2 + BitVec.ofNat 64 c).toNat = s - (64 - c) := fun c hc => by
    rw [BitVec.toNat_add, hsp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, e 56 (by omega)]; exact h.ra
  · rw [show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl, e 48 (by omega)]; exact h.s0
  · rw [show (40#64 : BitVec 64) = BitVec.ofNat 64 40 from rfl, e 40 (by omega)]; exact h.s1
  · rw [show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from rfl, e 32 (by omega)]; exact h.s2
  · rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, e 24 (by omega)]; exact h.s3
  · rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, e 16 (by omega)]; exact h.s4
  · rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, e 8 (by omega)]; exact h.s5

/-- The slot offset `env_get`/`env_set` compute for index `i`: `(i<<1 + i)<<3`. -/
theorem slot24_index (i : Nat) :
    (BitVec.ofNat 64 i <<< 1 + BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (24 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- The return of `env_get`/`env_set`: `a0 = res`, the frame popped and the
caller's `ra`, `s0-s5` restored. -/
structure GetRet (s : Nat) (r : BitVec 64) (sv : Nat → BitVec 64) (res : BitVec 64)
    (R' : Nat → BitVec 64) : Prop where
  a0 : R' 10 = res
  ra : R' 1 = r
  sp : R' 2 = BitVec.ofNat 64 s
  saved : ∀ k ∈ getSaved, R' k = sv k

/-- A 24-byte copy from `src` to `dst`: the three words, and nothing else changed. -/
structure CopyOut (dst src : Nat) (Mt Mt' : Mem) : Prop where
  w0 : ldv .ld Mt' dst = ldv .ld Mt src
  w1 : ldv .ld Mt' (dst + 8) = ldv .ld Mt (src + 8)
  w2 : ldv .ld Mt' (dst + 16) = ldv .ld Mt (src + 16)
  frame : ∀ a, (a < dst ∨ dst + 24 ≤ a) → imgM Mt' a = imgM Mt a

/-- The scan's next index. -/
structure CmpNext (i : Nat) (R R' : Nat → BitVec 64) : Prop where
  keep : ∀ k, k ≠ 8 → k ≠ 9 → R' k = R k
  idx : R' 8 = BitVec.ofNat 64 (i + 1)
  cur : R' 9 = R 9 + 8#64

/-- The shared epilogue `0x80002ca0`: restore `ra`, `s0-s5`, pop, return. -/
theorem get_epi {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s out : Nat} {G : FrameGeom}
    {r : BitVec 64}
    {sv : Nat → BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hs : htifLo + 16 + 64 ≤ s) (hs' : s ≤ 0x100000000) (hra : r.toNat % 4 = 0)
    (hstk : GetStack s r sv R Mt) :
    Span live (getS s out G) 0x80002ca0#64 R Mt
      (fun pc' R' Mt' => pc' = r ∧ Mt' = Mt ∧ GetRet s r sv (R 10) R') := by
  intro Q hk
  have hsp := hstk.sp
  obtain ⟨hr1, hr8, hr9, hr18, hr19, hr20, hr21⟩ := hstk.restore (by omega) hs'
  sx_run hl
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hr1]; exact hra
  refine hk _ _ _ ⟨hr1, rfl, ⟨by simp [upd_apply], ?_, ?_, ?_⟩⟩
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr1
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hsp, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · intro k hk
    simp only [getSaved, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact hr8
    · exact hr9
    · exact hr18
    · exact hr19
    · exact hr20
    · exact hr21

end VsaIris.Interp
