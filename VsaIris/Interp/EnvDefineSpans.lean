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
  have hes := hsep G.e (by unfold frameS InExt; exact .inl ⟨hsb.1, by omega⟩)
  clear hsep hlay
  sx_run hl at 0x80002a90
  refine hk _ _ _ ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  all_goals clear hk
  all_goals (try sx_norm)
  · rw [BitVec.toNat_add, h2]; simp only [BitVec.reduceToNat]; omega
  · clear hld hw hsb he hn hes
    simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss]
    exact hra
  · clear hld hw hsb he hn hes
    simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss]
    exact hsv 8 (by decide)
  · clear hld hw hsb he hn hes
    simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss]
    exact hsv 9 (by decide)
  · clear hld hw hsb he hn hes
    simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss]
    exact hsv 18 (by decide)
  · clear hld hw hsb he hn hes
    simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss]
    exact hsv 19 (by decide)
  · clear hld hw hsb he hn hes
    simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss]
    exact hsv 20 (by decide)
  · clear hld hw hsb he hn hes
    simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss]
    exact hsv 21 (by decide)
  · clear hld hw hsb he hn hes
    simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss]
    exact hsv 22 (by decide)
  · have hb : (R 2 + 18446744073709551552#64 + 24#64).toNat = s - 40 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, h2]; simp only [BitVec.reduceToNat]; omega
    first
      | exact hld
      | (rw [hb, ldv_store_miss _ _ _ (by simp only [widthOfM]; omega), hld])
  · clear hld hw hsb hsv hra he hn hes
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
theorem def_epi {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s : Nat} {S : Nat → Prop}
    {r : BitVec 64} {sv : Nat → BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hs : htifLo + 16 + 64 ≤ s) (hs' : s ≤ 0x100000000) (hra : r.toNat % 4 = 0)
    (hstk : DefStack s r sv R Mt) (hS : ∀ a, s - 64 ≤ a → a < s → S a) :
    Span live S 0x80002aec#64 R Mt
      (fun pc' R' Mt' => pc' = r ∧ Mt' = Mt ∧ DefRet s r sv R') := by
  intro Q hk
  have hsp := hstk.sp
  obtain ⟨hr1, hr8, hr9, hr18, hr19, hr20, hr21, hr22⟩ := hstk.restore (by omega) hs'
  sx_run hl
  iterate 8
    · intro b hb; have hb' := of_mem_accAddrs hb; apply hS <;> sx_addr
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

/-- A frame's capacity is below `2^28` (the names array is in the upper half
of 32-bit RAM). -/
theorem FrameLayout.cap_lt {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : FrameLayout img G n) : G.cap < 2 ^ 28 := by
  rcases Nat.eq_zero_or_pos G.cap with h0 | hpos
  · omega
  obtain ⟨-, h2, -, -⟩ := h.arrays_le hpos
  have hw := h.win G.nblk (by simp [FrameGeom.blocks, show G.cap ≠ 0 by omega])
  have := hw.lo; have := hw.hi; have := hw.htif
  unfold htifLo at this
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

/-- `addiw _, _, 1` of a small word. -/
theorem sext_addiw (n : Nat) (h : n + 1 < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 n + 1#64)) =
      BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · simp [BitVec.toNat_add]
    omega
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]
    simp [BitVec.toNat_add]
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

/-- A word store read back through the image. -/
theorem imgLE4_store (Mt : Mem) (a : Nat) (v : BitVec 64) :
    imgLE (imgM (writeLog Mt [(a, 4, v)])) a 4 = v.toNat % 2 ^ 32 := by
  simp only [writeLog, List.foldl, applyW, writeMap4, imgM, imgLE, Std.ExtHashMap.getElem?_insert,
    beq_iff_eq]
  simp [swData, Sail.BitVec.extractLsb, Nat.shiftRight_eq_div_pow]
  omega

/-- The `Env` struct at `e` sits in RAM above the HTIF words, 8-aligned. -/
structure EnvWin (e : Nat) : Prop where
  lo : 0x80000000 ≤ e
  hi : e + 32 ≤ 0x100000000
  htif : htifLo + 16 ≤ e
  align : e % 8 = 0

/-- A frame's struct window. -/
theorem FrameLayout.envWin {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : FrameLayout img G n) : EnvWin G.e := by
  have hw := h.win G.sblk (by simp [FrameGeom.blocks])
  have hsb := h.sblk
  have := hw.lo; have := hw.hi; have := hw.htif
  exact ⟨by omega, by omega, by omega, h.e_align⟩

/-- The growth's first step `0x80002b98`: `cap := cap'`, `a0 := names`; on to
`jal realloc`. -/
theorem def_grow1 {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {S : Nat → Prop}
    {e : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    (hw : EnvWin e) (he : (R 20).toNat = e) (hS : ∀ a, e ≤ a → a < e + 32 → S a) :
    Span live S 0x80002b98#64 R Mt
      (fun pc' R' Mt' => pc' = 0x80002ba0#64 ∧ Mt' = writeLog Mt [(e + 4, 4, R 15)] ∧
        R' 10 = R 22 ∧ ∀ k, k ≠ 10 → R' k = R k) := by
  intro Q hk
  have := hw.lo; have := hw.hi; have := hw.htif; have := hw.align
  have h4 : (R 20 + 4#64).toNat = e + 4 := by rw [BitVec.toNat_add, he]; simp; omega
  sx_run hl at 0x80002ba0
  · intro b hb; have hb' := of_mem_accAddrs hb; apply hS <;> sx_addr
  refine hk _ _ _ ⟨rfl, by rw [h4], by simp [upd_apply], fun k hk => by simp [upd_apply, hk]⟩

/-- The growth's middle `0x80002ba4`: `names := a0`, `a0 := vals`,
`a1 := 24 * cap'`; on to `jal realloc`. -/
theorem def_grow2 {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {S : Nat → Prop}
    {e cap pv : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    (hw : EnvWin e) (he : (R 20).toNat = e) (hS : ∀ a, e ≤ a → a < e + 32 → S a)
    (hc : cap < 2 ^ 29) (hcap : imgLE (imgM Mt) (e + 4) 4 = cap)
    (hpv : imgLE (imgM Mt) (e + 16) 8 = pv) :
    Span live S 0x80002ba4#64 R Mt
      (fun pc' R' Mt' => pc' = 0x80002bbc#64 ∧ Mt' = writeLog Mt [(e + 8, 8, R 10)] ∧
        R' 10 = BitVec.ofNat 64 pv ∧ R' 11 = BitVec.ofNat 64 (24 * cap) ∧
        R' 15 = BitVec.ofNat 64 cap ∧ ∀ k, k ≠ 10 → k ≠ 11 → k ≠ 15 → R' k = R k) := by
  intro Q hk
  have := hw.lo; have := hw.hi; have := hw.htif; have := hw.align
  have h4 : (R 20 + 4#64).toNat = e + 4 := by rw [BitVec.toNat_add, he]; simp; omega
  have h8 : (R 20 + 8#64).toNat = e + 8 := by rw [BitVec.toNat_add, he]; simp; omega
  have h16 : (R 20 + 16#64).toNat = e + 16 := by rw [BitVec.toNat_add, he]; simp; omega
  have hld : ldv .lw Mt (R 20 + 4#64).toNat = BitVec.ofNat 64 cap := by
    rw [h4]; exact ldv_lw_img Mt _ cap (by omega) hcap
  have hlv : ldv .ld Mt (e + 16) = BitVec.ofNat 64 pv := by
    rw [ldv_ld_img]; unfold imgW; rw [hpv]
  sx_run hl at 0x80002bbc
  iterate 3
    · intro b hb; have hb' := of_mem_accAddrs hb; apply hS <;> sx_addr
  have h24 : ((BitVec.ofNat 64 cap <<< 1 + BitVec.ofNat 64 cap) <<< 3) =
      BitVec.ofNat 64 (24 * cap) := slot24_index cap
  refine hk _ _ _ ⟨rfl, by rw [h8], ?_, ?_, ?_, fun k h10 h11 h15 => by
    simp [upd_apply, h10, h11, h15]⟩
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h16]; exact hlv
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hld]; exact h24
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hld]

/-- The growth's end `0x80002bc0`: `vals := a0`; both arrays non-NULL go on
to the append, otherwise to the out-of-memory arm. -/
theorem def_grow3 {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {S : Nat → Prop}
    {e p1 : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    (hw : EnvWin e) (he : (R 20).toNat = e) (hS : ∀ a, e ≤ a → a < e + 32 → S a)
    (hp1 : imgLE (imgM Mt) (e + 8) 8 = p1) :
    Span live S 0x80002bc0#64 R Mt
      (fun pc' R' Mt' => Mt' = writeLog Mt [(e + 16, 8, R 10)] ∧
        (∀ k, k ≠ 15 → R' k = R k) ∧
        ((p1 ≠ 0 ∧ R 10 ≠ 0#64 ∧ pc' = 0x80002b1c#64) ∨
         ((p1 = 0 ∨ R 10 = 0#64) ∧ pc' = 0x80002bd0#64))) := by
  intro Q hk
  have := hw.lo; have := hw.hi; have := hw.htif; have := hw.align
  have h8 : (R 20 + 8#64).toNat = e + 8 := by rw [BitVec.toNat_add, he]; simp; omega
  have h16 : (R 20 + 16#64).toNat = e + 16 := by rw [BitVec.toNat_add, he]; simp; omega
  have hlp : ldv .ld Mt (R 20 + 8#64).toNat = BitVec.ofNat 64 p1 := by
    rw [h8, ldv_ld_img]; unfold imgW; rw [hp1]
  have hp1n : BitVec.ofNat 64 p1 = 0#64 ↔ p1 = 0 := by
    have := imgLE_lt (imgM Mt) (e + 8) 8
    rw [hp1] at this
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp at this; omega
    · intro h; rw [h]
  sx_run hl at 0x80002bd0 0x80002b1c
  iterate 2
    · intro b hb; have hb' := of_mem_accAddrs hb; apply hS <;> sx_addr
  · intro hc
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hlp, hp1n] at hc
    exact hk _ _ _ ⟨by rw [h16], fun k hk => by simp [upd_apply, hk], .inr ⟨.inl hc, rfl⟩⟩
  · intro hc
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hlp, hp1n] at hc
    sx_run hl at 0x80002bd0 0x80002b1c
    · intro ha
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at ha
      exact hk _ _ _ ⟨by rw [h16], fun k hk => by simp [upd_apply, hk], .inl ⟨hc, ha, rfl⟩⟩
    · intro ha
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, Classical.not_not] at ha
      exact hk _ _ _ ⟨by rw [h16], fun k hk => by simp [upd_apply, hk], .inr ⟨.inr ha, rfl⟩⟩

/-- The append's start `0x80002b1c`: `a0 := name`; on to `jal strlen`. -/
theorem def_app1 {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {S : Nat → Prop}
    {R : Nat → BitVec 64} {Mt : Mem} :
    Span live S 0x80002b1c#64 R Mt
      (fun pc' R' Mt' => pc' = 0x80002b20#64 ∧ Mt' = Mt ∧ R' 10 = R 18 ∧
        ∀ k, k ≠ 10 → R' k = R k) := by
  intro Q hk
  sx_run hl at 0x80002b20
  exact hk _ _ _ ⟨rfl, rfl, by simp [upd_apply], fun k hk => by simp [upd_apply, hk]⟩

/-- After `strlen` `0x80002b24`: `s0 := a0 := len + 1`; on to `jal malloc`. -/
theorem def_app2 {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {S : Nat → Prop}
    {R : Nat → BitVec 64} {Mt : Mem} :
    Span live S 0x80002b24#64 R Mt
      (fun pc' R' Mt' => pc' = 0x80002b2c#64 ∧ Mt' = Mt ∧ R' 8 = R 10 + 1#64 ∧
        R' 10 = R 10 + 1#64 ∧ ∀ k, k ≠ 8 → k ≠ 10 → R' k = R k) := by
  intro Q hk
  sx_run hl at 0x80002b2c
  exact hk _ _ _ ⟨rfl, rfl, by simp [upd_apply], by simp [upd_apply],
    fun k h8 h10 => by simp [upd_apply, h8, h10]⟩

/-- After `malloc` `0x80002b30`: `s1 := a0`; NULL goes to the out-of-memory
arm, otherwise `a2 := len + 1`, `a1 := name` and on to `jal memcpy`. -/
theorem def_app3 {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {S : Nat → Prop}
    {R : Nat → BitVec 64} {Mt : Mem} :
    Span live S 0x80002b30#64 R Mt
      (fun pc' R' Mt' => Mt' = Mt ∧ R' 9 = R 10 ∧
        ((R 10 = 0#64 ∧ pc' = 0x80002bd0#64 ∧ ∀ k, k ≠ 9 → R' k = R k) ∨
         (R 10 ≠ 0#64 ∧ pc' = 0x80002b40#64 ∧ R' 12 = R 8 ∧ R' 11 = R 18 ∧
          ∀ k, k ≠ 9 → k ≠ 11 → k ≠ 12 → R' k = R k))) := by
  intro Q hk
  sx_run hl at 0x80002b40 0x80002bd0
  · intro hc
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
    exact hk _ _ _ ⟨rfl, by simp [upd_apply], .inl ⟨hc, rfl, fun k hk => by simp [upd_apply, hk]⟩⟩
  · intro hc
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
    sx_run hl at 0x80002b40
    exact hk _ _ _ ⟨rfl, by simp [upd_apply], .inr ⟨hc, rfl, by simp [upd_apply],
      by simp [upd_apply], fun k h9 h11 h12 => by simp [upd_apply, h9, h11, h12]⟩⟩

/-- `n` bytes at `a` a doubleword access may touch: RAM above the HTIF
words, 8-aligned. -/
structure WordsWin (a n : Nat) : Prop where
  lo : 0x80000000 ≤ a
  hi : a + n ≤ 0x100000000
  htif : htifLo + 16 ≤ a
  align : a % 8 = 0

/-- What the append's stores leave: `names[n] := np`, `vals[n] := *v`,
`count := n + 1`, nothing else. -/
structure AppOut (e n pn pv vp : Nat) (np : BitVec 64) (Mt Mt' : Mem) : Prop where
  name : ldv .ld Mt' (pn + 8 * n) = np
  w0 : ldv .ld Mt' (pv + 24 * n) = ldv .ld Mt vp
  w1 : ldv .ld Mt' (pv + 24 * n + 8) = ldv .ld Mt (vp + 8)
  w2 : ldv .ld Mt' (pv + 24 * n + 16) = ldv .ld Mt (vp + 16)
  cnt : imgLE (imgM Mt') e 4 = n + 1
  frame : ∀ a, ¬ InExt (pn + 8 * n, 8) a → ¬ InExt (pv + 24 * n, 24) a → ¬ InExt (e, 4) a →
    imgM Mt' a = imgM Mt a

/-- The append's stores `0x80002b44`: the new name pointer and value into
slot `n`, the count bumped; on to the epilogue. -/
theorem def_app4 {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {S : Nat → Prop}
    {e n pn pv vp : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    (hw : EnvWin e) (he : (R 20).toNat = e) (hvp : (R 21).toNat = vp)
    (hcnt : imgLE (imgM Mt) e 4 = n) (hn : n + 1 < 2 ^ 31)
    (hpn : imgLE (imgM Mt) (e + 8) 8 = pn) (hpv : imgLE (imgM Mt) (e + 16) 8 = pv)
    (wn : WordsWin (pn + 8 * n) 8) (wv : WordsWin (pv + 24 * n) 24) (wp : WordsWin vp 24)
    (dnv : pn + 8 * n + 8 ≤ pv + 24 * n ∨ pv + 24 * n + 24 ≤ pn + 8 * n)
    (dne : pn + 8 * n + 8 ≤ e ∨ e + 32 ≤ pn + 8 * n)
    (dve : pv + 24 * n + 24 ≤ e ∨ e + 32 ≤ pv + 24 * n)
    (hS : ∀ a, (e ≤ a ∧ a < e + 32) ∨ InExt (pn + 8 * n, 8) a ∨ InExt (pv + 24 * n, 24) a ∨
      InExt (vp, 24) a → S a) :
    Span live S 0x80002b44#64 R Mt
      (fun pc' R' Mt' => pc' = 0x80002aec#64 ∧ AppOut e n pn pv vp (R 9) Mt Mt' ∧
        ∀ k, k ≠ 10 → k ≠ 11 → k ≠ 12 → k ≠ 13 → k ≠ 14 → k ≠ 15 → k ≠ 16 → k ≠ 17 →
          R' k = R k) := by
  intro Q hk
  have := hw.lo; have := hw.hi; have := hw.htif; have := hw.align
  have := wn.lo; have := wn.hi; have := wn.htif; have := wn.align
  have := wv.lo; have := wv.hi; have := wv.htif; have := wv.align
  have := wp.lo; have := wp.hi; have := wp.htif; have := wp.align
  have hS' : ∀ a, e ≤ a → a < e + 32 → S a := fun a h1 h2 => hS a (.inl ⟨h1, h2⟩)
  have h8 : (R 20 + 8#64).toNat = e + 8 := by rw [BitVec.toNat_add, he]; simp; omega
  have h16 : (R 20 + 16#64).toNat = e + 16 := by rw [BitVec.toNat_add, he]; simp; omega
  have hlc : ldv .lw Mt (R 20).toNat = BitVec.ofNat 64 n := by
    rw [he]; exact ldv_lw_img Mt _ n (by omega) hcnt
  have hln : ldv .ld Mt (R 20 + 8#64).toNat = BitVec.ofNat 64 pn := by
    rw [h8, ldv_ld_img]; unfold imgW; rw [hpn]
  have hlv : ldv .ld Mt (R 20 + 16#64).toNat = BitVec.ofNat 64 pv := by
    rw [h16, ldv_ld_img]; unfold imgW; rw [hpv]
  have hSp : ∀ a, vp ≤ a → a < vp + 24 → S a := fun a h1 h2 => hS a (.inr (.inr (.inr ⟨h1, h2⟩)))
  sx_run hl at 0x80002b70
  iterate 6
    · intro b hb; have hb' := of_mem_accAddrs hb
      first | (apply hS' <;> sx_addr) | (apply hSp <;> sx_addr)
  rw [hlc, hln, hlv, shl3_small n (by omega), ← BitVec.ofNat_add, slot24_index n]
  generalize hA : BitVec.ofNat 64 (pn + 8 * n) = A
  have hAn : A.toNat = pn + 8 * n := by
    rw [← hA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  clear hA
  have hSn : ∀ a, pn + 8 * n ≤ a → a < pn + 8 * n + 8 → S a :=
    fun a h1 h2 => hS a (.inr (.inl ⟨h1, h2⟩))
  sx_run hl at 0x80002b7c
  · intro b hb; have hb' := of_mem_accAddrs hb; apply hSn <;> sx_addr
  rw [← BitVec.ofNat_add]
  generalize hB : BitVec.ofNat 64 (pv + 24 * n) = B
  have hBn : B.toNat = pv + 24 * n := by
    rw [← hB, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  clear hB
  have hSv : ∀ a, pv + 24 * n ≤ a → a < pv + 24 * n + 24 → S a :=
    fun a h1 h2 => hS a (.inr (.inr (.inl ⟨h1, h2⟩)))
  sx_run hl at 0x80002aec
  iterate 4
    · intro b hb; have hb' := of_mem_accAddrs hb
      first | (apply hSv <;> sx_addr) | (apply hS' <;> sx_addr)
  have hB8 : (B + 8#64).toNat = pv + 24 * n + 8 := by rw [BitVec.toNat_add, hBn]; simp; omega
  have hB16 : (B + 16#64).toNat = pv + 24 * n + 16 := by rw [BitVec.toNat_add, hBn]; simp; omega
  have hv8 : (R 21 + 8#64).toNat = vp + 8 := by rw [BitVec.toNat_add, hvp]; simp; omega
  have hv16 : (R 21 + 16#64).toNat = vp + 16 := by rw [BitVec.toNat_add, hvp]; simp; omega
  rw [sext_addiw n hn, hAn, hBn, hB8, hB16, hv8, hv16, hvp, he]
  refine hk _ _ _ ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, fun a h1 h2 h3 => ?_⟩, fun k h10 h11 h12 h13 h14 h15
    h16 h17 => by simp [upd_apply, h10, h11, h12, h13, h14, h15, h16, h17]⟩
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
      ldv_ld_miss _ _ (by omega), ldv_ld_hit_eq _ _ rfl]
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
      ldv_ld_hit_eq _ _ rfl]
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_hit_eq _ _ rfl]
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_hit_eq _ _ rfl]
  · rw [imgLE4_store, BitVec.toNat_ofNat]; omega
  · simp only [InExt] at h1 h2 h3
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega)]

end VsaIris.Interp
