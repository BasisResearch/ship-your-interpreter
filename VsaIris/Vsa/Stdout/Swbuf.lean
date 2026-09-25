import VsaIris.Vsa.Stdout.Fflush

/-!
# `__swbuf_r` on `stdout` (lane N1)

`__swbuf_r(reent, c, stdout)` with `_w` exhausted: `stdout` is in write mode
with its one-byte buffer, so it resets `_w` to `_lbfsize = 0`, stores `c` at
`_p = _bf._base`, advances `_p`, and, the buffer now full, flushes it
(`fflush_run`), which prints `c`. It returns `c`. At `_flags = 0x000a` it
first orients `stdout` (`swbufU_chain`); `swbuf_run'` takes either
orientation.
-/

namespace VsaIris.Sym

open scoped VsaIris.Sym.Stdout

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- A byte just stored with `sb`. -/
theorem imgM_sb_hit (M : Mem) (a : Nat) (v : BitVec 64) :
    imgM (writeLog M [(a, 1, v)]) a = BitVec.ofNat 8 (v.toNat % 2 ^ 8) := by
  have h := imgLE_store1_hit M a v
  simp only [imgLE, Nat.mul_zero, Nat.add_zero] at h
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat]; omega

theorem ofNat_zeroExtend8 (c : BitVec 8) :
    BitVec.ofNat 8 ((BitVec.zeroExtend 64 c).toNat % 2 ^ 8) = c := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]
  have := c.isLt; omega

theorem sext32_eq_zero {v : BitVec 32}
    (h : LeanRV64DExecutable.Functions.sign_extend (m := 64) v = 0#64) : v = 0#32 := by
  have := congrArg (BitVec.setWidth 32) h
  simp [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend] at this
  rw [← this]; ext i hi; simp [BitVec.getElem_setWidth, hi, BitVec.getLsbD_signExtend]; omega

/-- A word that loads as `0` has zero bytes. -/
theorem imgLE_zero_of_lw {M : Mem} {a : Nat} (h : ldv .lw M a = 0#64) : imgLE (imgM M) a 4 = 0 := by
  rw [ldv_lw_img] at h
  have e := congrArg BitVec.toNat (sext32_eq_zero h)
  have hl := imgLE_lt (imgM M) a 4
  simp at e
  omega

/-- **`_flags2` through an `ORIENT` block**: the block's `sw 0` to `_flags2`
(`0x8001bbd0`) rewrites the zero word already there (`imgM_store_restore`). -/
theorem imgM_flags2_keep {M M0 : Mem} (h0 : ldv .lw M0 0x8001bbd0 = 0#64)
    (hag : ∀ i, i < 4 → imgM M (0x8001bbd0 + i) = imgM M0 (0x8001bbd0 + i)) {a : Nat}
    (ha : 0x8001bbd0 ≤ a ∧ a < 0x8001bbd0 + 4) :
    imgM (writeLog M [(0x8001bbd0, 4, 0#64)]) a = imgM M a :=
  imgM_store_restore M 0#64 (by decide) (by rw [imgLE_congr hag, imgLE_zero_of_lw h0]; rfl) ha

/-- A kept byte `a` through a run's write log, with the `ORIENT` block's
`_flags2` store (if any) restored from `h0 : ldv .lw Mt 0x8001bbd0 = 0`. -/
syntax "nx_keep_orient " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| nx_keep_orient $h0) => `(tactic| (
      simp (disch := nx_addr) only [imgM_store_miss]
      try (by_cases hf2 : 0x8001bbd0 ≤ a ∧ a < 0x8001bbd0 + 4
           · rw [imgM_flags2_keep $h0 (fun i hi => by simp (disch := nx_addr) only [imgM_store_miss]) hf2]
             simp (disch := nx_addr) only [imgM_store_miss]
           · simp (disch := nx_addr) only [imgM_store_miss])))

set_option hygiene false in
/-- `__swbuf_r` from its entry to `jal _fflush_r`, with `_flags = fl`: from
`0x000a` the run takes the `ORIENT` block (`0x8000f1b4`–`0x8000f1c8`, storing
`_flags = 0x200a` and `_flags2 = 0`) and rejoins at `0x8000f118`. -/
macro "#swbuf_seg " n:ident fl:term : command => `(
  #ix_seg $n {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
      {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
      {R : Nat → BitVec 64} {s sp ra : BitVec 64} {need : Nat} {c : BitVec 8}
      (hs1 : s.toNat - need + 320 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
      (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
      (h1 : R 1 = ra) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = BitVec.zeroExtend 64 c)
      (h12 : R 12 = 0x8001bb20#64) (h2 : R 2 = sp)
      (hsinit : ldv .ld Mt 0x8001b580 = 0x80005d2c#64) (hlbf : ldv .lw Mt 0x8001bb48 = 0#64)
      (hF : ldv .lh Mt 0x8001bb30 = $fl) (hB : ldv .ld Mt 0x8001bb38 = 0x8001bb97#64)
      (hlm : ldv .lw Mt 0x8001bbd0 = 0#64) (hP : ldv .ld Mt 0x8001bb20 = 0x8001bb97#64)
      (hbs : ldv .lw Mt 0x8001bb40 = 1#64) (hlock : ldv .ld Mt 0x8001bbc0 = 0#64)
      (hwr : ldv .ld Mt 0x8001bb60 = 0x8000efd4#64) (hck : ldv .ld Mt 0x8001bb50 = 0x8001bb20#64)
      (hsfd : ldv .lh Mt 0x8001bb32 = 1#64) :
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000f0c8#64 R Mt
    by nx_run hlive using [h1, h10, h11, h12, h2, hsinit, hlbf, hF, hB, hlm, hP, hbs, BitVec.reduceAnd,
      BitVec.reduceOr, BitVec.add_assoc] at 2147544524)

#swbuf_seg swbuf_A 0x200a#64

#swbuf_seg swbufU_A 0x000a#64

set_option hygiene false in
/-- `__swbuf_r` from `jal _fflush_r` (either orientation's run). -/
macro "swbuf_B_tac" : tactic => `(tactic| (
    refine fflush_run (sp := sp + 18446744073709551568#64) (B := 0x8001bb97#64) (bs := [c])
      (ra := 0x8000f1dc#64) hlive ?_ ?_ hs3 hs4 ?_ (by decide) ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun R' hR => ?_)
    all_goals try (simp [tohostAddr]; done)
    all_goals try (nx_norm; done)
    all_goals try nx_addr
    all_goals try ((try nx_norm); nx_mem; (try simp only [hsinit, hF, hlm, hlock, hwr, hck, hsfd, hB, List.length_cons, List.length_nil,
      Nat.reduceAdd, BitVec.reduceOfNat, BitVec.reduceAdd]); (try nx_norm); done)
    · intro i hi; simp only [List.length_cons, List.length_nil] at hi
      obtain rfl : i = 0 := by omega
      nx_addr
    · intro i hi; simp only [List.length_cons, List.length_nil] at hi
      obtain rfl : i = 0 := by omega
      refine .inl ⟨by simp [outS, stdioFoot, InRange, impureW], ?_⟩
      simp only [List.getElem_cons_zero, Nat.add_zero, BitVec.reduceToNat]
      rw [imgM_sb_hit, ofNat_zeroExtend8]))

set_option hygiene false in
/-- `__swbuf_r` from `_fflush_r`'s return. -/
macro "swbuf_C_tac" : tactic => `(tactic| (
    nx_ret hR
    nx_run hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19, h1, BitVec.add_assoc]))

#ix_piece swbuf_B from swbuf_A by
  swbuf_B_tac

#ix_piece swbuf_C from swbuf_B by
  swbuf_C_tac

#nx_chain swbuf_chain := [swbuf_A, swbuf_B, swbuf_C]

#ix_piece swbufU_B from swbufU_A by
  swbuf_B_tac

#ix_piece swbufU_C from swbufU_B by
  swbuf_C_tac

#nx_chain swbufU_chain := [swbufU_A, swbufU_B, swbufU_C]

/-- The memory after `__swbuf_r(reent, c, stdout)` returns. -/
@[nx_mt] abbrev swbufMt (Mt : Mem) (sp ra s0 s1 s2 s3 : BitVec 64) (c : BitVec 8) : Mem :=
  fflushMt (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mt
    [((sp + 18446744073709551600#64).toNat, 8, s0)]) [((sp + 18446744073709551592#64).toNat, 8, s1)])
    [((sp + 18446744073709551608#64).toNat, 8, ra)]) [(2147597100, 4, 0#64)])
    [(2147597088, 8, 2147597208#64)]) [(2147597100, 4, 18446744073709551615#64)])
    [(2147597207, 1, BitVec.zeroExtend 64 c)])
    (sp + 18446744073709551568#64) 2147597207#64 2147545564#64 (BitVec.zeroExtend 64 c &&& 255#64)
    2147595576#64 s2 s3

/-- **`__swbuf_r(reent, c, stdout)`** prints `c` and returns it. -/
theorem swbuf_run {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp ra : BitVec 64} {need : Nat} {c : BitVec 8}
    (hs1 : s.toNat - need + 320 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = BitVec.zeroExtend 64 c)
    (h12 : R 12 = 0x8001bb20#64) (h2 : R 2 = sp)
    (hsinit : ldv .ld Mt 0x8001b580 = 0x80005d2c#64) (hlbf : ldv .lw Mt 0x8001bb48 = 0#64)
    (hF : ldv .lh Mt 0x8001bb30 = 0x200a#64) (hB : ldv .ld Mt 0x8001bb38 = 0x8001bb97#64)
    (hlm : ldv .lw Mt 0x8001bbd0 = 0#64) (hP : ldv .ld Mt 0x8001bb20 = 0x8001bb97#64)
    (hbs : ldv .lw Mt 0x8001bb40 = 1#64) (hlock : ldv .ld Mt 0x8001bbc0 = 0#64)
    (hwr : ldv .ld Mt 0x8001bb60 = 0x8000efd4#64) (hck : ldv .ld Mt 0x8001bb50 = 0x8001bb20#64)
    (hsfd : ldv .lh Mt 0x8001bb32 = 1#64)
    (hk : ∀ R', RetOK R R' (BitVec.zeroExtend 64 c &&& 255#64) → SWPO live (stdioText ++ dataOf Dt DA)
      iRegs (outS s need) Q (t ++ putcs [c]) ra R' (swbufMt Mt sp ra (R 8) (R 9) (R 18) (R 19) c)) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000f0c8#64 R Mt := by
  refine swbuf_chain hlive hs1 hs2 hs3 hs4 hal hra h1 h10 h11 h12 h2 hsinit hlbf hF hB hlm hP hbs hlock
    hwr hck hsfd ?_
  intros
  simp only [nx_mt, BitVec.add_assoc, BitVec.reduceAdd] at hk ⊢
  exact hk _ (retOK_of (by simp [upd_apply]) (by ret_keep))

/-- The bytes a stdout write leaves alone: all but its frames (the `n` bytes
below `sp`), `errno`, `stdout`'s `_p`, `_w` and flags, and its buffer byte. -/
@[nx_mt] def outKeep (sp : BitVec 64) (n : Nat) (a : Nat) : Prop :=
  ¬ (sp.toNat - n ≤ a ∧ a < sp.toNat) ∧ ¬ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) ∧ ¬ (0x8001bb20 ≤ a ∧ a < 0x8001bb28) ∧
    ¬ (0x8001bb2c ≤ a ∧ a < 0x8001bb32) ∧ a ≠ 0x8001bb97

/-- A callee's frame window inside its caller's: the callee's `sp` is `k`
bytes below. -/
theorem outKeep_sub {s : BitVec 64} {k n m a : Nat} (hk : k + n ≤ m) (hs : k ≤ s.toNat)
    (hk64 : k < 2 ^ 64) (h : outKeep s m a) :
    outKeep (s + BitVec.ofNat 64 (2 ^ 64 - k)) n a := by
  have e : (s + BitVec.ofNat 64 (2 ^ 64 - k)).toNat = s.toNat - k := by
    rw [BitVec.toNat_add]; have := s.isLt; simp only [BitVec.toNat_ofNat]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp; omega
    · rw [Nat.mod_eq_of_lt (by omega : 2 ^ 64 - k < 2 ^ 64)]; omega
  simp only [outKeep, e] at h ⊢
  omega

/-- `stdout`'s written fields after a flushed write of `c`. -/
structure OutDone (M : Mem) (c : BitVec 8) : Prop where
  p : ldv .ld M 0x8001bb20 = 0x8001bb97#64
  w : ldv .lw M 0x8001bb2c = 0#64
  flagsU : ldv .lhu M 0x8001bb30 = 0x200a#64
  flagsS : ldv .lh M 0x8001bb30 = 0x200a#64
  buf : imgM M 0x8001bb97 = c

/-- **`__swbuf_r(reent, c, stdout)`**, abstract post: prints `c`, returns it;
the memory keeps `outKeep` and ends with `stdout` idle (`OutDone`). -/
theorem swbuf_run' {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp ra : BitVec 64} {need : Nat} {c : BitVec 8}
    (hs1 : s.toNat - need + 320 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = BitVec.zeroExtend 64 c)
    (h12 : R 12 = 0x8001bb20#64) (h2 : R 2 = sp)
    (hsinit : ldv .ld Mt 0x8001b580 = 0x80005d2c#64) (hlbf : ldv .lw Mt 0x8001bb48 = 0#64)
    {o : Bool} (hF : ldv .lh Mt 0x8001bb30 = consoleFlagsV o)
    (hB : ldv .ld Mt 0x8001bb38 = 0x8001bb97#64)
    (hlm : ldv .lw Mt 0x8001bbd0 = 0#64) (hP : ldv .ld Mt 0x8001bb20 = 0x8001bb97#64)
    (hbs : ldv .lw Mt 0x8001bb40 = 1#64) (hlock : ldv .ld Mt 0x8001bbc0 = 0#64)
    (hwr : ldv .ld Mt 0x8001bb60 = 0x8000efd4#64) (hck : ldv .ld Mt 0x8001bb50 = 0x8001bb20#64)
    (hsfd : ldv .lh Mt 0x8001bb32 = 1#64)
    (hk : ∀ R' M', RetOK R R' (BitVec.zeroExtend 64 c &&& 255#64) → MemKeep Mt M' (outKeep sp 256) →
      OutDone M' c → SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs [c]) ra R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000f0c8#64 R Mt := by
  cases o
  · refine swbufU_chain hlive hs1 hs2 hs3 hs4 hal hra h1 h10 h11 h12 h2 hsinit hlbf hF hB hlm hP hbs
      hlock hwr hck hsfd ?_
    intros
    refine hk _ _ (retOK_of (by simp [upd_apply]) (by ret_keep)) ⟨fun a ha => ?_⟩ ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [outKeep] at ha
      nx_keep_orient hlm
    all_goals try (nx_mem; done)
    all_goals try (nx_mem; nx_norm; done)
    simp (disch := nx_addr) only [imgM_store_miss]
    rw [imgM_sb_hit, ofNat_zeroExtend8]
  refine swbuf_run hlive hs1 hs2 hs3 hs4 hal hra h1 h10 h11 h12 h2 hsinit hlbf hF hB hlm hP hbs hlock
    hwr hck hsfd fun R' hR => hk R' _ hR ⟨fun a ha => ?_⟩ ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [outKeep] at ha
    simp only [nx_mt, BitVec.add_assoc, BitVec.reduceAdd]
    simp (disch := nx_addr) only [imgM_store_miss]
  all_goals simp only [nx_mt, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try (nx_mem; done)
  all_goals try (nx_mem; nx_norm; done)
  simp (disch := nx_addr) only [imgM_store_miss]
  rw [imgM_sb_hit, ofNat_zeroExtend8]

end VsaIris.Sym
