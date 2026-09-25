import VsaIris.Vsa.Fprintf.Flush
import VsaIris.Vsa.SymCompact

/-!
# The memory after a loop-bearing call; `__sbprintf`'s `FILE` (lane N5)

A call whose effect depends on its data (`__sfvwrite_r`'s copy/flush loop)
cannot hand its caller an explicit write log. It hands back the caller's
memory with its footprint regions replaced by some bytes `g` (`fillR`, N3's
`SymCompact.lean`), together with named facts about the new contents. Loads
outside the regions read through to the caller's memory (`nx_mem` below
peels each region with `ldv_*_fillR_miss`), loads inside meet the facts.

`SbFile M f pend` is `__sbprintf`'s stack `FILE` at `f` (buffer at
`f + 184`) holding the pending bytes `pend`: the fields `_vfprintf_r`,
`__sfvwrite_r` and `_fflush_r` load, as load values of `M`.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- Store forwarding through `fillR` regions too (a load off a region reads
the memory below it). -/
macro_rules
  | `(tactic| nx_mem) => `(tactic| simp (disch := nx_addr) only [ldv_store_hit, ldv_ld_hit_eq,
      ldv_ld_miss, ldv_lw_miss, ldv_lw_store8, ldv_lw_hit, ldv_lh_hit, ldv_lhu_hit, ldv_lbu_hit,
      ldv_lh_miss, ldv_lhu_miss, ldv_lbu_miss, ldv_lwu_miss, ldv_ld_fillR_miss, ldv_lw_fillR_miss,
      ldv_lwu_fillR_miss, ldv_lh_fillR_miss, ldv_lhu_fillR_miss, ldv_lbu_fillR_miss])

/-- A load is determined by the bytes it reads. -/
theorem ldv_agree {k : MKind} {M M' : Mem} {a : Nat}
    (h : ∀ j, j < widthOfM k → imgM M' (a + j) = imgM M (a + j)) : ldv k M' a = ldv k M a := by
  unfold ldv bytesAt
  congr 1
  refine List.map_congr_left fun j hj => ?_
  exact h j (List.mem_range.mp hj)

/-- The fixed fields of `__sbprintf`'s stack `FILE` at `f`, and the
boundary data its flushes read: `stdout`'s flags and descriptor (`__swrite`),
`__sinit` done (`_fflush_r`). -/
structure SbFixed (M : Mem) (f : BitVec 64) : Prop where
  flags : ldv .lh M (f + 16#64).toNat = 0x2008#64
  flagsU : ldv .lhu M (f + 16#64).toNat = 0x2008#64
  base : ldv .ld M (f + 24#64).toNat = f + 184#64
  size : ldv .lw M (f + 32#64).toNat = 1024#64
  cookie : ldv .ld M (f + 48#64).toNat = 0x8001bb20#64
  writer : ldv .ld M (f + 64#64).toNat = 0x8000efd4#64
  flags2 : ldv .lw M (f + 176#64).toNat = 0#64
  sfl : ldv .lh M 0x8001bb30 = 0x200a#64
  sfd : ldv .lh M 0x8001bb32 = 1#64
  sinit : ldv .ld M 0x8001b580 = 0x80005d2c#64

/-- **`__sbprintf`'s stack `FILE`** at `f` with `pend` buffered (at most 1023
bytes: a full buffer is flushed at once). -/
structure SbFile (M : Mem) (f : BitVec 64) (pend : List (BitVec 8)) : Prop extends SbFixed M f where
  len : pend.length < 1024
  p : ldv .ld M f.toNat = f + BitVec.ofNat 64 (184 + pend.length)
  w : ldv .lw M (f + 12#64).toNat = BitVec.ofNat 64 (1024 - pend.length)
  buf : ∀ i (h : i < pend.length), imgM M ((f + 184#64).toNat + i) = pend[i]

/-! ## Frames -/

/-- `M'` agrees with `M` outside the bytes `Reg`. -/
def Frame (M' M : Mem) (Reg : Nat → Prop) : Prop := ∀ a, ¬ Reg a → imgM M' a = imgM M a

theorem Frame.refl (M : Mem) (Reg : Nat → Prop) : Frame M M Reg := fun _ _ => rfl

theorem Frame.trans {M M' M'' : Mem} {Reg : Nat → Prop} (h : Frame M' M Reg) (h' : Frame M'' M' Reg) :
    Frame M'' M Reg := fun a ha => (h' a ha).trans (h a ha)

theorem Frame.mono {M M' : Mem} {Reg Reg' : Nat → Prop} (h : Frame M' M Reg) (hR : ∀ a, Reg a → Reg' a) :
    Frame M' M Reg' := fun a ha => h a (fun hr => ha (hR a hr))

/-- A store inside the region. -/
theorem Frame.store (M : Mem) {Reg : Nat → Prop} {a w : Nat} (v : BitVec 64)
    (h : ∀ b, a ≤ b → b < a + w → Reg b) : Frame (writeLog M [(a, w, v)]) M Reg := by
  intro b hb
  refine imgM_store_miss _ _ ?_
  refine Classical.byContradiction fun hc => hb (h b (by omega) (by omega))

/-- A copy inside the region. -/
theorem Frame.copied {M' M : Mem} {d src c : Nat} {g : Nat → BitVec 8} {Reg : Nat → Prop}
    (h : Copied M' M d src c g) (hR : ∀ b, d ≤ b → b < d + c → Reg b) : Frame M' M Reg := by
  intro b hb
  refine h.rest b ?_
  refine Classical.byContradiction fun hc => hb (hR b (by omega) (by omega))

/-- A load outside the region reads through a frame. -/
theorem Frame.ldv {M' M : Mem} {Reg : Nat → Prop} (h : Frame M' M Reg) (k : MKind) {a : Nat}
    (ha : ∀ j, j < widthOfM k → ¬ Reg (a + j)) : ldv k M' a = ldv k M a :=
  ldv_agree fun j hj => h _ (ha j hj)

/-- The bytes `__sfvwrite_r`'s passes change: `_p`, `_w`, the buffer, the
callee stack below `fp`, `stdout`'s flags, `errno`. -/
def SfvReg (f fp : Nat) (a : Nat) : Prop :=
  (f ≤ a ∧ a < f + 8) ∨ (f + 12 ≤ a ∧ a < f + 16) ∨ (f + 184 ≤ a ∧ a < f + 1208) ∨
    (fp - 256 ≤ a ∧ a < fp) ∨ (0x8001bb30 ≤ a ∧ a < 0x8001bb32) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c)

/-- The fixed fields survive a pass (all but `stdout`'s flags lie outside
`SfvReg`; the flags are rewritten with their value). -/
theorem SbFixed.transport {M M' : Mem} {f fp : BitVec 64} (h : SbFixed M f)
    (hF : Frame M' M (SfvReg f.toNat fp.toNat)) (hsfl : ldv .lh M' 0x8001bb30 = 0x200a#64)
    (hf1 : 0x8001c168 ≤ f.toNat) (hf2 : f.toNat + 1208 ≤ fp.toNat - 256 ∨ fp.toNat ≤ f.toNat)
    (hf3 : f.toNat + 1208 < 2 ^ 64) (hfp : 0x80100000 ≤ fp.toNat - 256) :
    SbFixed M' f := by
  have out : ∀ (k : MKind) (n : Nat), 16 ≤ n → n + 8 ≤ 184 →
      ldv k M' (f + BitVec.ofNat 64 n).toNat = ldv k M (f + BitVec.ofNat 64 n).toNat := by
    intro k n h1 h2
    have hw : widthOfM k ≤ 8 := by cases k <;> simp [widthOfM]
    have hn184 : n < 184 := by omega
    have hn : (f + BitVec.ofNat 64 n).toNat = f.toNat + n := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show f.toNat + n < 2 ^ 64 by omega)]
    refine hF.ldv k fun j hj => ?_
    rw [hn]; unfold SfvReg; omega
  have outA : ∀ (k : MKind) (a : Nat), 0x8001b580 ≤ a → a + widthOfM k ≤ 0x8001b588 ∨
      (0x8001bb32 ≤ a ∧ a + widthOfM k ≤ 0x8001bb34) → ldv k M' a = ldv k M a := by
    intro k a h1 h2
    refine hF.ldv k fun j hj => ?_
    unfold SfvReg; omega
  exact ⟨by rw [out .lh 16 (by omega) (by omega)]; exact h.flags,
    by rw [out .lhu 16 (by omega) (by omega)]; exact h.flagsU,
    by rw [out .ld 24 (by omega) (by omega)]; exact h.base,
    by rw [out .lw 32 (by omega) (by omega)]; exact h.size,
    by rw [out .ld 48 (by omega) (by omega)]; exact h.cookie,
    by rw [out .ld 64 (by omega) (by omega)]; exact h.writer,
    by rw [out .lw 176 (by omega) (by omega)]; exact h.flags2,
    hsfl,
    by rw [outA .lh _ (by omega) (.inr ⟨Nat.le_refl _, by simp [widthOfM]⟩)]; exact h.sfd,
    by rw [outA .ld _ (Nat.le_refl _) (.inl (by simp [widthOfM]))]; exact h.sinit⟩

/-- A word load of a small count just stored. -/
theorem ldv_lw_store_ofNat (M : Mem) (a : Nat) {n : Nat} (hn : n < 2 ^ 31) :
    ldv .lw (writeLog M [(a, 4, BitVec.ofNat 64 n)]) a = BitVec.ofNat 64 n := by
  rw [ldv_lw_hit M _ rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend,
    BitVec.toNat_ofNat]
  have hmsb : (BitVec.ofNat 32 (n % 2 ^ 64 % 2 ^ 32)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not, Nat.not_le, BitVec.toNat_ofNat]; omega
  rw [hmsb]
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The bytes a copy of `c` bytes from `src` reads from its window `g`. -/
def copyBytes (g : Nat → BitVec 8) (src c : Nat) : List (BitVec 8) := (List.range c).map fun i => g (src + i)

@[simp] theorem copyBytes_length (g : Nat → BitVec 8) (src c : Nat) : (copyBytes g src c).length = c := by
  simp [copyBytes]

theorem copyBytes_get (g : Nat → BitVec 8) (src c i : Nat) (h : i < (copyBytes g src c).length) :
    (copyBytes g src c)[i] = g (src + i) := by
  simp [copyBytes]

/-- The memory after a copy into the buffer and the `_p`/`_w` stores. -/
abbrev advMt (Mt : Mem) (f : BitVec 64) (k c : Nat) : Mem :=
  writeLog (writeLog Mt [(f.toNat, 8, f + BitVec.ofNat 64 (184 + k + c))])
    [((f + 12#64).toNat, 4, BitVec.ofNat 64 (1024 - k - c))]

/-- **A copy into the buffer**, then `_p`/`_w` advanced: the fixed fields,
the frame (only `SfvReg` changed), the buffered bytes `pend ++ copied`. -/
theorem SbFile.advanceCore {Mt0 Mt : Mem} {f fp : BitVec 64} {pend : List (BitVec 8)} {src c : Nat}
    {g : Nat → BitVec 8} (hF0 : SbFile Mt0 f pend)
    (hcp : Copied Mt Mt0 ((f + 184#64).toNat + pend.length) src c g) (hkc : pend.length + c ≤ 1024)
    (hf1 : 0x8001c168 ≤ f.toNat) (hf2 : f.toNat + 1208 ≤ fp.toNat - 256 ∨ fp.toNat ≤ f.toNat)
    (hf3 : f.toNat + 1208 < 2 ^ 32) (hfp : 0x80100000 ≤ fp.toNat - 256) :
    SbFixed (advMt Mt f pend.length c) f ∧ Frame (advMt Mt f pend.length c) Mt0 (SfvReg f.toNat fp.toNat) ∧
      ∀ i (h : i < (pend ++ copyBytes g src c).length),
        imgM (advMt Mt f pend.length c) ((f + 184#64).toNat + i) = (pend ++ copyBytes g src c)[i] := by
  have hB : (f + 184#64).toNat = f.toNat + 184 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have h12 : (f + 12#64).toNat = f.toNat + 12 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hFr : Frame (advMt Mt f pend.length c) Mt0 (SfvReg f.toNat fp.toNat) :=
    ((Frame.copied hcp fun b h1 h2 => by unfold SfvReg; omega).trans
      (Frame.store _ _ fun b h1 h2 => by unfold SfvReg; omega)).trans
      (Frame.store _ _ fun b h1 h2 => by rw [h12] at h1 h2; unfold SfvReg; omega)
  refine ⟨hF0.toSbFixed.transport hFr ?_ hf1 hf2 (by omega) hfp, hFr, ?_⟩
  · rw [ldv_lh_miss _ _ (by rw [h12]; omega), ldv_lh_miss _ _ (by omega),
      Frame.ldv (Reg := fun a => (f + 184#64).toNat + pend.length ≤ a ∧
        a < (f + 184#64).toNat + pend.length + c)
        (Frame.copied hcp fun b h1 h2 => ⟨h1, h2⟩) .lh (fun j hj => by simp only [widthOfM] at hj; omega)]
    exact hF0.sfl
  · intro i hi
    simp only [List.length_append, copyBytes_length] at hi
    rw [imgM_store_miss _ _ (by rw [h12, hB]; omega), imgM_store_miss _ _ (by rw [hB]; omega)]
    by_cases hik : i < pend.length
    · rw [List.getElem_append_left hik, hcp.rest _ (by omega)]
      exact hF0.buf i hik
    · rw [List.getElem_append_right (by omega), copyBytes_get,
        show (f + 184#64).toNat + i = (f + 184#64).toNat + pend.length + (i - pend.length) by omega]
      exact hcp.done _ (by omega)

/-- **A copy into the buffer** that leaves room: the `FILE` holds
`pend ++ copied`. -/
theorem SbFile.advance {Mt0 Mt : Mem} {f fp : BitVec 64} {pend : List (BitVec 8)} {src c : Nat}
    {g : Nat → BitVec 8} (hF0 : SbFile Mt0 f pend)
    (hcp : Copied Mt Mt0 ((f + 184#64).toNat + pend.length) src c g) (hkc : pend.length + c < 1024)
    (hf1 : 0x8001c168 ≤ f.toNat) (hf2 : f.toNat + 1208 ≤ fp.toNat - 256 ∨ fp.toNat ≤ f.toNat)
    (hf3 : f.toNat + 1208 < 2 ^ 32) (hfp : 0x80100000 ≤ fp.toNat - 256) :
    SbFile (advMt Mt f pend.length c) f (pend ++ copyBytes g src c) ∧
      Frame (advMt Mt f pend.length c) Mt0 (SfvReg f.toNat fp.toNat) := by
  obtain ⟨hx, hFr, hbuf⟩ := hF0.advanceCore hcp (by omega) hf1 hf2 hf3 hfp
  have h12 : (f + 12#64).toNat = f.toNat + 12 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨⟨hx, by simp; omega, ?_, ?_, hbuf⟩, hFr⟩
  · rw [ldv_ld_miss _ _ (by rw [h12]; omega), ldv_store_hit]; simp [Nat.add_assoc]
  · simp only [List.length_append, copyBytes_length]
    rw [ldv_lw_store_ofNat _ _ (by omega), Nat.sub_sub]

/-- The bytes `__swrite(stdout, …)` called with `sp = fp` changes: its
frames below `fp`, `stdout`'s flags, `errno`. -/
def SwReg (fp : Nat) (a : Nat) : Prop :=
  (fp - 256 ≤ a ∧ a < fp) ∨ (0x8001bb30 ≤ a ∧ a < 0x8001bb32) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c)

/-- A frame grows by a store inside the region. -/
theorem Frame.snoc {M M0 : Mem} {Reg : Nat → Prop} {a w : Nat} {v : BitVec 64} (h : Frame M M0 Reg)
    (hr : ∀ b, a ≤ b → b < a + w → Reg b) : Frame (writeLog M [(a, w, v)]) M0 Reg :=
  h.trans (Frame.store M v hr)

/-- Peel a chain of stores inside the region (`SfvReg`), each by `omega` on
its `Nat` address. -/
macro "frame_chain" : tactic => `(tactic| (repeat (refine Frame.snoc ?_ ?_)) <;>
  first | exact Frame.refl _ _ | (intro b h1 h2; simp (config := {failIfUnchanged := false}) (disch := omega) only [BitVec.add_assoc, BitVec.reduceAdd, toNat_add_lit, toNat_add_neg,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod] at h1 h2; (try unfold SfvReg); (try unfold SwReg); omega))

/-- **A flushed buffer**: after `_fflush_r` on the stack `FILE` (called with
`sp = fp`), `_p` is back at the base, `_w` at 1024, nothing buffered, and
only `SfvReg` changed. -/
theorem SbFile.flushed {M2 Mt0 : Mem} {f fp ra s0 s1 s2 s3 : BitVec 64}
    (hF : SbFixed M2 f) (hFr : Frame M2 Mt0 (SfvReg f.toNat fp.toNat))
    (hf1 : 0x8001c168 ≤ f.toNat) (hf2 : fp.toNat ≤ f.toNat) (hf3 : f.toNat + 1208 < 2 ^ 32)
    (hfp : 0x80100000 ≤ fp.toNat - 256) :
    SbFile (fflushFMt M2 fp f (f + 184#64) ra s0 s1 s2 s3) f [] ∧
      Frame (fflushFMt M2 fp f (f + 184#64) ra s0 s1 s2 s3) Mt0 (SfvReg f.toNat fp.toNat) := by
  have hA : Frame (fflushFMt M2 fp f (f + 184#64) ra s0 s1 s2 s3) M2 (SfvReg f.toNat fp.toNat) := by
    unfold fflushFMt sflushFMt swriteMt
    frame_chain
  have hFr' := hFr.trans hA
  have h12 : (f + 12#64).toNat = f.toNat + 12 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨⟨hF.transport hA ?_ hf1 (.inr hf2) (by omega) hfp, by simp, ?_, ?_,
    fun i h => absurd h (by simp)⟩, hFr'⟩
  all_goals unfold fflushFMt sflushFMt swriteMt
  all_goals (simp only [BitVec.add_assoc, BitVec.reduceAdd]; try nx_mem)
  · decide
  · rfl
  · decide

/-- **After `__swrite(stdout, …)`** called with `sp = fp`: the stack `FILE`
is as it was; only its frame, `stdout`'s flags and `errno` changed. -/
theorem SbFile.swrote {Mt : Mem} {f fp ra s0 : BitVec 64} {pend : List (BitVec 8)} (hF : SbFile Mt f pend)
    (hf1 : 0x8001c168 ≤ f.toNat) (hf2 : fp.toNat ≤ f.toNat) (hf3 : f.toNat + 1208 < 2 ^ 32)
    (hfp : 0x80100000 ≤ fp.toNat - 256) :
    SbFile (swriteMt Mt fp ra s0) f pend ∧ Frame (swriteMt Mt fp ra s0) Mt (SfvReg f.toNat fp.toNat) := by
  have hA : Frame (swriteMt Mt fp ra s0) Mt (SwReg fp.toNat) := by
    unfold swriteMt
    frame_chain
  have hA' : Frame (swriteMt Mt fp ra s0) Mt (SfvReg f.toNat fp.toNat) :=
    hA.mono fun a h => by unfold SwReg at h; unfold SfvReg; omega
  have h12 : (f + 12#64).toNat = f.toNat + 12 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨⟨hF.toSbFixed.transport hA' ?_ hf1 (.inr hf2) (by omega) hfp, hF.len, ?_, ?_, fun i h => ?_⟩, hA'⟩
  · unfold swriteMt
    simp (config := {failIfUnchanged := false}) only [BitVec.add_assoc, BitVec.reduceAdd]; nx_mem; decide
  · rw [hA.ldv .ld (fun j hj => by simp only [widthOfM] at hj; unfold SwReg; omega)]; exact hF.p
  · rw [hA.ldv .lw (fun j hj => by simp only [widthOfM] at hj; rw [h12]; unfold SwReg; omega)]; exact hF.w
  · rw [hA _ (by
      have : (f + 184#64).toNat = f.toNat + 184 := by
        rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
      rw [this]; unfold SwReg; have := hF.len; omega)]
    exact hF.buf i h

/-! ## Pieces as windows -/

/-- A piece's bytes as a byte function from its source address. -/
def win (bs : List (BitVec 8)) (src : Nat) (a : Nat) : BitVec 8 := bs.getD (a - src) 0

theorem copyBytes_win (bs : List (BitVec 8)) (src c : Nat) (hc : c ≤ bs.length) :
    copyBytes (win bs src) src c = bs.take c := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [copyBytes_length] at h1
  rw [copyBytes_get, List.getElem_take]
  simp [win, List.getD_eq_getElem?_getD, show i < bs.length by omega]

theorem win_drop (bs : List (BitVec 8)) (src c : Nat) (a : Nat) (h : src + c ≤ a) :
    win (bs.drop c) (src + c) a = win bs src a := by
  simp only [win, List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2; omega

/-- A piece's bytes readable at `M`. -/
def PieceReads (Dt : Mem) (DA : List Nat) (S : Nat → Prop) (M : Mem) (src : Nat) (bs : List (BitVec 8)) :
    Prop := ∀ i (h : i < bs.length), ReadB Dt DA S M (src + i) bs[i]

theorem PieceReads.readWin {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {M : Mem} {src : Nat}
    {bs : List (BitVec 8)} (h : PieceReads Dt DA S M src bs) :
    ReadWin Dt DA S M src (src + bs.length) (win bs src) := by
  intro a h1 h2
  have := h (a - src) (by omega)
  rw [show src + (a - src) = a by omega] at this
  simpa [win, List.getD_eq_getElem?_getD, show a - src < bs.length by omega] using this

theorem PieceReads.drop {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {M : Mem} {src : Nat}
    {bs : List (BitVec 8)} (h : PieceReads Dt DA S M src bs) (c : Nat) :
    PieceReads Dt DA S M (src + c) (bs.drop c) := by
  intro i hi
  simp only [List.length_drop] at hi
  rw [List.getElem_drop, show src + c + i = src + (c + i) by omega]
  exact h (c + i) (by omega)

theorem PieceReads.transport {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {M M' : Mem} {src : Nat}
    {bs : List (BitVec 8)} (h : PieceReads Dt DA S M src bs)
    (hM : ∀ i, i < bs.length → imgM M' (src + i) = imgM M (src + i)) : PieceReads Dt DA S M' src bs :=
  fun i hi => (h i hi).transport (hM i hi)

end VsaIris.Sym.Fp
