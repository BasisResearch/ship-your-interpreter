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
      (fun pc' R' Mt' => pc' = 0x80002a90#64 ∧ DefStack s r sv R' Mt' ∧ R' 10 = R 10 ∧ R' 20 = R 10 ∧
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
  refine hk _ _ _ ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
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

/-- The scan's start in a nonempty frame: `s6 := names`, `s0 := 0`, `s1 := names`. -/
structure DefHead (G : FrameGeom) (R R' : Nat → BitVec 64) : Prop where
  keep : ∀ k, k ≠ 8 → k ≠ 9 → k ≠ 22 → R' k = R k
  idx : R' 8 = 0#64
  cur : R' 9 = BitVec.ofNat 64 G.pn
  arr : R' 22 = BitVec.ofNat 64 G.pn

/-- The count test `0x80002a90`: an empty frame goes to the growth check,
a nonempty one to the scan. -/
theorem def_head {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s out n : Nat}
    {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem}
    (hlay : FrameLayout (imgM Mt) G n) (he : (R 10).toNat = G.e)
    (h19 : R 19 = BitVec.ofNat 64 n) :
    Span live (getS s out G) 0x80002a90#64 R Mt
      (fun pc' R' Mt' => Mt' = Mt ∧
        ((n = 0 ∧ pc' = 0x80002bf4#64 ∧ R' = R) ∨
         (0 < n ∧ pc' = 0x80002ab0#64 ∧ DefHead G R R'))) := by
  intro Q hk
  have hn := hlay.count_lt
  have hw := hlay.win G.sblk (by simp [FrameGeom.blocks])
  have hsb := hlay.sblk
  have hea := hlay.e_align
  have := hw.lo; have := hw.hi; have := hw.htif
  have hint : (BitVec.ofNat 64 n).toInt = n := toInt_ofNat_small (by omega)
  sx_run hl at 0x80002bf4 0x80002ab0
  · intro hc
    rw [h19, hint] at hc
    exact hk _ _ _ ⟨rfl, .inl ⟨by simp at hc; omega, rfl, rfl⟩⟩
  · intro hc
    rw [h19, hint] at hc
    sx_run hl at 0x80002ab0
    have h8 : (R 10 + 8#64).toNat = G.e + 8 := by rw [BitVec.toNat_add, he]; simp; omega
    have hpn : ldv .ld Mt (R 10 + 8#64).toNat = BitVec.ofNat 64 G.pn := by
      rw [h8, ldv_ld_img]; unfold imgW; rw [hlay.names]
    refine hk _ _ _ ⟨rfl, .inr ⟨by simp at hc; omega, rfl,
      ⟨fun k h8' h9 h22 => ?_, by simp [upd_apply], ?_, ?_⟩⟩⟩
    · simp [upd_apply, h8', h9, h22]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hpn
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hpn

/-- The load of name `i` `0x80002ab0`: `a0 := names[i]`, `a1 := name`. -/
theorem def_load {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s out n i : Nat}
    {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem}
    (hlay : FrameLayout (imgM Mt) G n) (hi : i < n) (h9 : (R 9).toNat = G.pn + 8 * i) :
    Span live (getS s out G) 0x80002ab0#64 R Mt
      (fun pc' R' Mt' => Mt' = Mt ∧ pc' = 0x80002ab8#64 ∧
        R' 10 = imgW (imgM Mt) (G.pn + 8 * i) ∧ R' 11 = R 18 ∧
        ∀ k, k ≠ 10 → k ≠ 11 → R' k = R k) := by
  intro Q hk
  obtain ⟨hcap, hn1, hn2, -, -, hw, -⟩ := hlay.slot hi
  have := hw.lo; have := hw.hi; have := hw.htif; have := hw.align
  sx_run hl at 0x80002ab8
  refine hk _ _ _ ⟨rfl, rfl, ?_, ?_, fun k h10 h11 => ?_⟩
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [h9, ldv_ld_img]
  · simp
  · simp [upd_apply, h10, h11]

/-- The compare's branch `0x80002abc`: `bnez a0` to the next name (or the
frame's end), or on to the hit write. -/
theorem def_cmp {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s out n i : Nat}
    {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem} (hi : i < n) (hn : n < 2 ^ 31)
    (h8 : R 8 = BitVec.ofNat 64 i) (h19 : R 19 = BitVec.ofNat 64 n) :
    Span live (getS s out G) 0x80002abc#64 R Mt
      (fun pc' R' Mt' => Mt' = Mt ∧
        ((R 10 ≠ 0#64 ∧ i + 1 < n ∧ pc' = 0x80002ab0#64 ∧ CmpNext i R R') ∨
         (R 10 ≠ 0#64 ∧ i + 1 = n ∧ pc' = 0x80002b14#64 ∧ CmpNext i R R') ∨
         (R 10 = 0#64 ∧ pc' = 0x80002ac0#64 ∧ R' = R))) := by
  intro Q hk
  have hinc : R 8 + 1#64 = BitVec.ofNat 64 (i + 1) := by
    rw [h8]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  have hnext : CmpNext i R (upd (upd R 8 (R 8 + 1#64)) 9 (R 9 + 8#64)) :=
    ⟨fun k h8' h9 => by simp [upd_apply, h8', h9], by simp [upd_apply, hinc], by simp [upd_apply]⟩
  sx_run hl at 0x80002ab0 0x80002b14 0x80002ac0
  · intro hc
    sx_run hl at 0x80002ab0 0x80002b14
    · intro he
      have : i + 1 = n := by
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hinc, h19] at he
        have := congrArg BitVec.toNat he
        simp at this; omega
      exact hk _ _ _ ⟨rfl, .inr (.inl ⟨hc, this, rfl, hnext⟩)⟩
    · intro he
      have : i + 1 ≠ n := fun h => he (by
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hinc, h19, h])
      exact hk _ _ _ ⟨rfl, .inl ⟨hc, by omega, rfl, hnext⟩⟩
  · intro hc
    exact hk _ _ _ ⟨rfl, .inr (.inr ⟨by simpa using hc, rfl, rfl⟩)⟩

/-- The epilogue's loads read back the spilled words. -/
theorem DefStack.restore {s : Nat} {r : BitVec 64} {sv : Nat → BitVec 64} {R : Nat → BitVec 64}
    {Mt : Mem} (h : DefStack s r sv R Mt) (hs : 64 ≤ s) (hs' : s ≤ 0x100000000) :
    ldv .ld Mt (R 2 + 56#64).toNat = r ∧ ldv .ld Mt (R 2 + 48#64).toNat = sv 8 ∧
    ldv .ld Mt (R 2 + 40#64).toNat = sv 9 ∧ ldv .ld Mt (R 2 + 32#64).toNat = sv 18 ∧
    ldv .ld Mt (R 2 + 24#64).toNat = sv 19 ∧ ldv .ld Mt (R 2 + 16#64).toNat = sv 20 ∧
    ldv .ld Mt (R 2 + 8#64).toNat = sv 21 ∧ ldv .ld Mt (R 2).toNat = sv 22 := by
  have hsp := h.sp
  have e : ∀ c : Nat, c < 64 → (R 2 + BitVec.ofNat 64 c).toNat = s - (64 - c) := fun c hc => by
    rw [BitVec.toNat_add, hsp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, e 56 (by omega)]; exact h.ra
  · rw [show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl, e 48 (by omega)]; exact h.s0
  · rw [show (40#64 : BitVec 64) = BitVec.ofNat 64 40 from rfl, e 40 (by omega)]; exact h.s1
  · rw [show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from rfl, e 32 (by omega)]; exact h.s2
  · rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, e 24 (by omega)]; exact h.s3
  · rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, e 16 (by omega)]; exact h.s4
  · rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, e 8 (by omega)]; exact h.s5
  · rw [hsp, show s - 64 = s - 64 from rfl]; exact h.s6

/-- `env_define`'s return: `ra`, `sp` and the callee-saved registers restored. -/
structure DefRet (s : Nat) (r : BitVec 64) (sv : Nat → BitVec 64) (R' : Nat → BitVec 64) : Prop where
  ra : R' 1 = r
  sp : R' 2 = BitVec.ofNat 64 s
  saved : ∀ k ∈ defineSaved, R' k = sv k

/-- The epilogue `0x80002aec`: restore `ra`, `s0-s6`, pop, return. -/
theorem def_epi {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s out : Nat} {G : FrameGeom}
    {r : BitVec 64} {sv : Nat → BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hs : htifLo + 16 + 64 ≤ s) (hs' : s ≤ 0x100000000) (hra : r.toNat % 4 = 0)
    (hstk : DefStack s r sv R Mt) :
    Span live (getS s out G) 0x80002aec#64 R Mt
      (fun pc' R' Mt' => pc' = r ∧ Mt' = Mt ∧ DefRet s r sv R') := by
  intro Q hk
  have hsp := hstk.sp
  obtain ⟨hr1, hr8, hr9, hr18, hr19, hr20, hr21, hr22⟩ := hstk.restore (by omega) hs'
  sx_run hl
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hr1]; exact hra
  refine hk _ _ _ ⟨hr1, rfl, ⟨?_, ?_, ?_⟩⟩
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr1
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hsp, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · intro k hk
    simp only [defineSaved, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact hr8
    · exact hr9
    · exact hr18
    · exact hr19
    · exact hr20
    · exact hr21
    · exact hr22

/-- The hit `0x80002ac0`: `vals[i] := *v` (the same code as `set_write`). -/
theorem def_write {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s out n i : Nat}
    {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem}
    (hlay : FrameLayout (imgM Mt) G n) (hi : i < n)
    (h8 : R 8 = BitVec.ofNat 64 i) (he : (R 20).toNat = G.e) (hout : (R 21).toNat = out)
    (hwo : 0x80000000 ≤ out ∧ out + 24 ≤ 0x100000000 ∧ htifLo + 16 ≤ out ∧ out % 8 = 0) :
    Span live (getS s out G) 0x80002ac0#64 R Mt
      (fun pc' R' Mt' => pc' = 0x80002aec#64 ∧ CopyOut (G.pv + 24 * i) out Mt Mt' ∧
        ∀ k, k ≠ 10 → k ≠ 11 → k ≠ 12 → k ≠ 13 → k ≠ 14 → k ≠ 15 → R' k = R k) := by
  intro Q hk
  obtain ⟨hcap, -, -, hv1, hv2, -, hvw⟩ := hlay.slot hi
  have := hvw.lo; have := hvw.hi; have := hvw.htif; have := hvw.align
  have hw := hlay.win G.sblk (by simp [FrameGeom.blocks])
  have hsb := hlay.sblk
  have := hw.lo; have := hw.hi; have := hw.htif
  have hpv : ldv .ld Mt (R 20 + 16#64).toNat = BitVec.ofNat 64 G.pv := by
    rw [show (R 20 + 16#64).toNat = G.e + 16 by rw [BitVec.toNat_add, he]; simp; omega,
      ldv_ld_img]
    unfold imgW; rw [hlay.vals]
  sx_run hl at 0x80002ae0
  rw [hpv, h8, slot24_index i, ← BitVec.ofNat_add]
  generalize hA : BitVec.ofNat 64 (G.pv + 24 * i) = A
  have hAn : A.toNat = G.pv + 24 * i := by
    rw [← hA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  clear hA
  have hA8 : (A + 8#64).toNat = G.pv + 24 * i + 8 := by rw [BitVec.toNat_add, hAn]; simp; omega
  have hA16 : (A + 16#64).toNat = G.pv + 24 * i + 16 := by rw [BitVec.toNat_add, hAn]; simp; omega
  have hal : (G.pv + 24 * i) % 8 = 0 := by omega
  sx_run hl at 0x80002aec
  have hout8 : (R 21 + 8#64).toNat = out + 8 := by rw [BitVec.toNat_add, hout]; simp; omega
  have hout16 : (R 21 + 16#64).toNat = out + 16 := by rw [BitVec.toNat_add, hout]; simp; omega
  refine hk _ _ _ ⟨rfl, ?_, fun k h10 h11 h12 h13 h14 h15 => by
    simp [upd_apply, h10, h11, h12, h13, h14, h15]⟩
  rw [hout8, hout16, hout, hA8, hA16, hAn]
  refine ⟨?_, ?_, ?_, fun a ha => ?_⟩
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_hit_eq _ _ rfl]
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_hit_eq _ _ rfl]
  · rw [ldv_ld_hit_eq _ _ rfl]
  · rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega)]

/-- A frame's capacity is below `2^29` (the names array is in 32-bit RAM). -/
theorem FrameLayout.cap_lt {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : FrameLayout img G n) : G.cap < 2 ^ 29 := by
  rcases Nat.eq_zero_or_pos G.cap with h0 | hpos
  · omega
  obtain ⟨-, h2, -, -⟩ := h.arrays hpos
  have hw := h.win G.nblk (by simp [FrameGeom.blocks, show G.cap ≠ 0 by omega])
  have := hw.lo; have := hw.hi
  omega

/-- `slliw` of a small word. -/
theorem sext_slliw (c : Nat) (h : c < 2 ^ 29) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 c) <<< 1) =
      BitVec.ofNat 64 (2 * c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega

/-- `slli _, _, 3` of a small word. -/
theorem shl3_small (c : Nat) (h : c < 2 ^ 32) :
    BitVec.ofNat 64 c <<< 3 = BitVec.ofNat 64 (8 * c) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The growth's registers at `0x80002b98`: `a5 = cap'`, `a1 = 8 * cap'`,
`s6` the old names array. -/
structure DefGrow (cap' pn : Nat) (R R' : Nat → BitVec 64) : Prop where
  keep : ∀ k, k ≠ 11 → k ≠ 15 → k ≠ 22 → R' k = R k
  cap : R' 15 = BitVec.ofNat 64 cap'
  names : R' 11 = BitVec.ofNat 64 (8 * cap')
  arr : R' 22 = BitVec.ofNat 64 pn

/-- After a miss `0x80002b14`: a full frame grows to `2 * cap`, otherwise the
binding is appended. -/
theorem def_cap {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s out n : Nat}
    {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem}
    (hlay : FrameLayout (imgM Mt) G n) (he : (R 20).toNat = G.e)
    (h19 : R 19 = BitVec.ofNat 64 n) (h22 : R 22 = BitVec.ofNat 64 G.pn) :
    Span live (getS s out G) 0x80002b14#64 R Mt
      (fun pc' R' Mt' => Mt' = Mt ∧
        ((G.cap = n ∧ pc' = 0x80002b98#64 ∧ DefGrow (2 * G.cap) G.pn R R') ∨
         (G.cap ≠ n ∧ pc' = 0x80002b1c#64 ∧ ∀ k, k ≠ 15 → R' k = R k))) := by
  intro Q hk
  have hn := hlay.count_lt
  have hc := hlay.cap_lt
  have hw := hlay.win G.sblk (by simp [FrameGeom.blocks])
  have hsb := hlay.sblk
  have hea := hlay.e_align
  have := hw.lo; have := hw.hi; have := hw.htif
  have h4 : (R 20 + 4#64).toNat = G.e + 4 := by rw [BitVec.toNat_add, he]; simp; omega
  have hld : ldv .lw Mt (R 20 + 4#64).toNat = BitVec.ofNat 64 G.cap := by
    rw [h4]; exact ldv_lw_img Mt _ G.cap (by omega) hlay.cap
  sx_run hl at 0x80002b98 0x80002b1c
  · intro hc'
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hld, h19] at hc'
    have hcn : G.cap = n := by
      have := congrArg BitVec.toNat hc'
      simp only [BitVec.toNat_ofNat] at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    sx_run hl at 0x80002b98
    refine hk _ _ _ ⟨rfl, .inl ⟨hcn, rfl, ⟨fun k h11 h15 _ => ?_, ?_, ?_, ?_⟩⟩⟩
    · simp [upd_apply, h11, h15]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hld]
      exact sext_slliw _ (by omega)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hld]
      rw [sext_slliw _ (by omega), shl3_small _ (by omega)]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h22
  · intro hc'
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hld, h19] at hc'
    refine hk _ _ _ ⟨rfl, .inr ⟨fun h => hc' (by rw [h]), rfl, fun k h15 => ?_⟩⟩
    simp [upd_apply, h15]

/-- An empty frame `0x80002bf4` (`cap = 0`): the first growth, to 8. -/
theorem def_empty {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s out : Nat}
    {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem}
    (hlay : FrameLayout (imgM Mt) G 0) (he : (R 10).toNat = G.e) (h19 : R 19 = 0#64) :
    Span live (getS s out G) 0x80002bf4#64 R Mt
      (fun pc' R' Mt' => Mt' = Mt ∧ pc' = 0x80002b98#64 ∧ DefGrow 8 G.pn R R') := by
  intro Q hk
  have hc0 : G.cap = 0 := by rw [hlay.cap_canon]; rfl
  have hw := hlay.win G.sblk (by simp [FrameGeom.blocks])
  have hsb := hlay.sblk
  have hea := hlay.e_align
  have := hw.lo; have := hw.hi; have := hw.htif
  have h4 : (R 10 + 4#64).toNat = G.e + 4 := by rw [BitVec.toNat_add, he]; simp; omega
  have hld : ldv .lw Mt (R 10 + 4#64).toNat = 0#64 := by
    rw [h4, ldv_lw_img Mt _ G.cap (by omega) hlay.cap, hc0]
  have h8 : (R 10 + 8#64).toNat = G.e + 8 := by rw [BitVec.toNat_add, he]; simp; omega
  have hpn : ldv .ld Mt (R 10 + 8#64).toNat = BitVec.ofNat 64 G.pn := by
    rw [h8, ldv_ld_img]; unfold imgW; rw [hlay.names]
  sx_run hl at 0x80002b98
  · intro hc
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hld, h19] at hc
    exact absurd rfl hc
  · intro _
    sx_run hl at 0x80002b98
    · intro hc
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hld] at hc
      exact absurd rfl hc
    · intro _
      sx_run hl at 0x80002b98
      refine hk _ _ _ ⟨rfl, rfl, ⟨fun k h11 h15 h22 => ?_, ?_, ?_, ?_⟩⟩
      · simp [upd_apply, h11, h15, h22]
      · simp [upd_apply]
      · simp [upd_apply]
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hpn

end VsaIris.Interp
