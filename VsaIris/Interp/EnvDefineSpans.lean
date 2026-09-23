import VsaIris.Interp.EnvScanCore

/-!
# `env_define`'s spans, first-order

`env_define(env, name, v)` (`0x80002a5c`, `env.c:22`). Registers: `s4` the
frame, `s2` the name, `s5` the value pointer, `s3` the count, `s6` the names
array, `s0` the index, `s1` the names cursor. The spans:

* `def_entry` `0x80002a5c` → `0x80002bf4` (empty frame) | `0x80002ab0` (scan);
* `def_load` `0x80002ab0` → `0x80002ab8` (`jal strcmp`);
* `def_cmp` `0x80002abc` → `0x80002ab0` (next) | `0x80002b14` (miss) | `0x80002ac0` (hit);
* `def_write` `0x80002ac0` → `0x80002aec`, the hit: `vals[i] := *v`;
* `def_epi` `0x80002aec` → return;
* `def_cap` `0x80002b14` → `0x80002b90` (full: grow) | `0x80002b1c` (append);
* `def_empty` `0x80002bf4` → `0x80002b98` (first growth, `cap := 8`) | `0x80002b1c`;
* the growth and append spans around the `realloc`/`strlen`/`malloc`/`memcpy` calls.

The stack frame after the prologue is `DefStack`: `sp = s - 64` and the
eight spilled words `ra`, `s0-s6`.
-/

namespace VsaIris.Interp

open VsaIris.Sym VsaIris.MallocFast Vsa.MemRepr Vsa.Sim

/-- `env_define`'s stack frame after its prologue (entry `sp = s`). -/
structure DefStack (s : Nat) (r : BitVec 64) (sv : Nat → BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) : Prop where
  sp : (R 2).toNat = s - 64
  ra : ldv .ld Mt (s - 8) = r
  s0 : ldv .ld Mt (s - 16) = sv 8
  s1 : ldv .ld Mt (s - 24) = sv 9
  s2 : ldv .ld Mt (s - 32) = sv 18
  s3 : ldv .ld Mt (s - 40) = sv 19
  s4 : ldv .ld Mt (s - 48) = sv 20
  s5 : ldv .ld Mt (s - 56) = sv 21
  s6 : ldv .ld Mt (s - 64) = sv 22

/-- `DefStack` reads only the stack frame and `sp`. -/
theorem DefStack.congr {s : Nat} {r : BitVec 64} {sv : Nat → BitVec 64} {R R' : Nat → BitVec 64}
    {Mt Mt' : Mem} (h : DefStack s r sv R Mt) (h2 : R' 2 = R 2)
    (hm : ∀ a, s - 64 ≤ a → a < s → imgM Mt' a = imgM Mt a) (hs : 64 ≤ s) :
    DefStack s r sv R' Mt' := by
  have c : ∀ o, 8 ≤ o → o ≤ 64 → ldv .ld Mt' (s - o) = ldv .ld Mt (s - o) := fun o h1 h2 =>
    ldv_congr .ld fun j hj => hm _ (by simp [widthOfM] at hj; omega) (by simp [widthOfM] at hj; omega)
  exact ⟨by rw [h2]; exact h.sp, (c 8 (by omega) (by omega)).trans h.ra,
    (c 16 (by omega) (by omega)).trans h.s0, (c 24 (by omega) (by omega)).trans h.s1,
    (c 32 (by omega) (by omega)).trans h.s2, (c 40 (by omega) (by omega)).trans h.s3,
    (c 48 (by omega) (by omega)).trans h.s4, (c 56 (by omega) (by omega)).trans h.s5,
    (c 64 (by omega) (by omega)).trans h.s6⟩

/-- A store into the 64-byte frame at `B` misses every address outside it. -/
theorem imgM_frame_store {Mt : Mem} {B : BitVec 64} {lo c w a : Nat} (v : BitVec 64)
    (hB : B.toNat = lo) (hlo : lo + 64 < 2 ^ 64) (hc : c + w ≤ 64) (ha : a < lo ∨ lo + 64 ≤ a) :
    imgM (writeLog Mt [((B + BitVec.ofNat 64 c).toNat, w, v)]) a = imgM Mt a := by
  apply imgM_store_miss
  rw [BitVec.toNat_add, hB, BitVec.toNat_ofNat]
  have : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
  rw [this, Nat.mod_eq_of_lt (by omega)]; omega

/-- `imgM_frame_store` at offset `0`. -/
theorem imgM_frame_store0 {Mt : Mem} {B : BitVec 64} {lo w a : Nat} (v : BitVec 64)
    (hB : B.toNat = lo) (hw : w ≤ 64) (ha : a < lo ∨ lo + 64 ≤ a) :
    imgM (writeLog Mt [(B.toNat, w, v)]) a = imgM Mt a := by
  apply imgM_store_miss; omega

/-- The prologue `0x80002a5c`: spill `ra`, `s0-s6`, read the count, move the
arguments into `s4`/`s2`/`s5`. -/
theorem def_pro {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s out n : Nat}
    {r : BitVec 64} {sv : Nat → BitVec 64} {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem}
    (hlo : htifLo + 16 + 64 ≤ s) (hhi : s ≤ 0x100000000) (hal : s % 16 = 0)
    (h2 : (R 2).toNat = s) (hra : R 1 = r) (hsv : ∀ k ∈ defineSaved, R k = sv k)
    (hlay : FrameLayout (imgM Mt) G n) (he : (R 10).toNat = G.e)
    (hsep : ∀ a, frameS G a → a < s - 64 ∨ s ≤ a) :
    Span live (getS s out G) 0x80002a5c#64 R Mt
      (fun pc' R' Mt' => pc' = 0x80002a90#64 ∧ DefStack s r sv R' Mt' ∧ R' 20 = R 10 ∧
        R' 18 = R 11 ∧ R' 21 = R 12 ∧ R' 19 = BitVec.ofNat 64 n ∧
        ∀ a, (a < s - 64 ∨ s ≤ a) → imgM Mt' a = imgM Mt a) := by
  intro Q hk
  have hn := hlay.count_lt
  have hw := hlay.win G.sblk (by simp [FrameGeom.blocks])
  have hsb := hlay.sblk
  have := hw.lo; have := hw.hi; have := hw.htif
  have hld : ldv .lw Mt (R 10).toNat = BitVec.ofNat 64 n := by
    rw [he]; exact ldv_lw_img Mt _ n hn hlay.count
  sx_run hl at 0x80002a90
  refine hk _ _ _ ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  all_goals clear hk
  all_goals (try sx_norm)
  all_goals (try sx_mem)
  · rw [BitVec.toNat_add, h2]; simp only [BitVec.reduceToNat]; omega
  · exact hra
  · exact hsv 8 (by decide)
  · exact hsv 9 (by decide)
  · exact hsv 18 (by decide)
  · exact hsv 19 (by decide)
  · exact hsv 20 (by decide)
  · exact hsv 21 (by decide)
  · exact hsv 22 (by decide)
  · have hb : (R 2 + 18446744073709551552#64 + 24#64).toNat = s - 40 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, h2]; simp only [BitVec.reduceToNat]; omega
    have hes := hsep G.e (by unfold frameS InExt; exact .inl ⟨hsb.1, by omega⟩)
    rw [hb, ldv_store_miss _ _ _ (by simp only [widthOfM]; omega), hld]
  · clear hsep hlay hld hw hsb hsv hra he hn
    generalize hB : R 2 + 18446744073709551552#64 = B
    have hBn : B.toNat = s - 64 := by
      rw [← hB, BitVec.toNat_add, h2]; simp only [BitVec.reduceToNat]; omega
    have ha' : a < s - 64 ∨ s - 64 + 64 ≤ a := by omega
    clear hB h2 ha
    simp (disch := first | decide | omega | exact ha') only [imgM_frame_store _ hBn,
      imgM_frame_store0 _ hBn]

end VsaIris.Interp
