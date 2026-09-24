import VsaIris.Vsa.AllocTac
import VsaIris.Vsa.HeapShape

/-!
# `_sbrk_r`

`_sbrk_r(reent, n)` (`0x8000696c`) clears `errno` and calls `_sbrk(n)`
(`0x80000118`), which advances `brk.0` by `n` when the result stays within
`__heap_end` and returns the old break, and otherwise sets the reentrancy
structure's `_errno` (through `__errno`) and returns `-1`. `_sbrk_r` then
copies a nonzero `errno` into `reent`; `_sbrk` never sets it, so that store
does not run.

`sbrk_r_gen` is the whole call as one step of `AW` for any increment word
(`_malloc_trim_r` shrinks the break); `sbrk_r_run` is its nonnegative case. From the entry, both
outcomes continue at the return address with the caller's registers except
`a0` (the result) and the temporaries `a4`/`a5`, and with the memory changed
only on the call's frames, `brk.0` and the two error words (`SbrkW`). Both
`malloc_extend_top` and `_malloc_trim_r` call it.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The bytes a `_sbrk_r` call may write: its and `_sbrk`'s frames (32 bytes
below `sp`), `brk.0`, `errno`, and the reentrancy structure's `_errno`. -/
def SbrkW (sp : Nat) (a : Nat) : Prop :=
  (sp - 32 ≤ a ∧ a < sp) ∨ (brkAddr ≤ a ∧ a < brkAddr + 8) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) ∨
    (0x8001b538 ≤ a ∧ a < 0x8001b53c)

/-- A `_sbrk_r` call: the increment `sb` in `a1`, the break `brkv` in
`brk.0`, a 16-aligned `sp` with 32 bytes below it owned and clear of the
globals, and a word-aligned return address. -/
structure SbrkPre (S : Nat → Prop) (R : Nat → BitVec 64) (Mt : Mem) (brkv sb : Nat) : Prop where
  a1 : (R 11).toNat = sb
  sb_lt : sb < 2 ^ 32
  brk : read64 Mt brkAddr = some brkv
  brk_pos : 0 < brkv
  brk_le : brkv ≤ heapEnd
  sp_lo : Vsa.Sim.tohostAddr + 16 + 32 ≤ (R 2).toNat
  sp_hi : (R 2).toNat ≤ 0x100000000
  sp_al : (R 2).toNat % 16 = 0
  ra_al : (R 1).toNat % 4 = 0
  off1 : (R 2).toNat ≤ 0x8001b538 ∨ 0x8001b53c + 32 ≤ (R 2).toNat
  off2 : (R 2).toNat ≤ 0x8001b960 ∨ 0x8001ba68 + 32 ≤ (R 2).toNat
  own : ∀ a, SbrkW (R 2).toNat a → S a

/-- After a `_sbrk_r` call: the caller's registers other than `a0`, `a4` and
`a5`, the break `brk'` in `brk.0`, and the memory changed only on `SbrkW`. -/
structure SbrkPost (R R' : Nat → BitVec 64) (Mt Mt' : Mem) (brk' : Nat) : Prop where
  regs : ∀ x, x ≠ 10 → x ≠ 14 → x ≠ 15 → R' x = R x
  brk : read64 Mt' brkAddr = some brk'
  agree : ∀ a : Nat, ¬ SbrkW (R 2).toNat a → Mt'[a]? = Mt[a]?
  pres : ∀ a : Nat, (Mt[a]?).isSome → (Mt'[a]?).isSome

theorem SbrkPre.acc {S : Nat → Prop} {R : Nat → BitVec 64} {Mt : Mem} {brkv sb : Nat}
    (P : SbrkPre S R Mt brkv sb) {a w : Nat} (h : ∀ b, a ≤ b → b < a + w → SbrkW (R 2).toNat b) :
    ∀ b ∈ accAddrs a w, S b := by
  intro b hb
  have := of_mem_accAddrs hb
  exact P.own b (h b this.1 this.2)

/-- `SbrkW` bytes are owned: the `sx_side` rule inside a `_sbrk_r` call. -/
macro_rules
  | `(tactic| sx_side) => `(tactic| (refine VsaIris.VsaHeap.SbrkPre.acc ‹VsaIris.VsaHeap.SbrkPre _ _ _ _ _› ?_; intro b hb1 hb2; unfold VsaIris.VsaHeap.SbrkW Vsa.Sim.DlHeap.brkAddr; sx_addr))

/-- The `_impure_ptr` word `__errno` returns: the reentrancy structure. -/
theorem impure_val :
    bytesVal .ld [0x38#8, 0xb5#8, 0x01#8, 0x80#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8] = 0x8001b538#64 := by
  decide

/-- A `_sbrk_r` call with any increment word in `a1`: the break `brkv`
advances (modulo `2 ^ 64`) to `nbrk`. -/
structure SbrkPreG (S : Nat → Prop) (R : Nat → BitVec 64) (Mt : Mem) (brkv nbrk : Nat) : Prop where
  sum : (BitVec.ofNat 64 brkv + R 11).toNat = nbrk
  brk : read64 Mt brkAddr = some brkv
  brk_pos : 0 < brkv
  brk_le : brkv ≤ heapEnd
  sp_lo : Vsa.Sim.tohostAddr + 16 + 32 ≤ (R 2).toNat
  sp_hi : (R 2).toNat ≤ 0x100000000
  sp_al : (R 2).toNat % 16 = 0
  ra_al : (R 1).toNat % 4 = 0
  off1 : (R 2).toNat ≤ 0x8001b538 ∨ 0x8001b53c + 32 ≤ (R 2).toNat
  off2 : (R 2).toNat ≤ 0x8001b960 ∨ 0x8001ba68 + 32 ≤ (R 2).toNat
  own : ∀ a, SbrkW (R 2).toNat a → S a

theorem SbrkPreG.acc {S : Nat → Prop} {R : Nat → BitVec 64} {Mt : Mem} {brkv nbrk : Nat}
    (P : SbrkPreG S R Mt brkv nbrk) {a w : Nat} (h : ∀ b, a ≤ b → b < a + w → SbrkW (R 2).toNat b) :
    ∀ b ∈ accAddrs a w, S b := by
  intro b hb
  have := of_mem_accAddrs hb
  exact P.own b (h b this.1 this.2)

/-- `SbrkW` bytes are owned: the `sx_side` rule inside a general `_sbrk_r` call. -/
macro_rules
  | `(tactic| sx_side) => `(tactic| (refine VsaIris.VsaHeap.SbrkPreG.acc ‹VsaIris.VsaHeap.SbrkPreG _ _ _ _ _› ?_; intro b hb1 hb2; unfold VsaIris.VsaHeap.SbrkW Vsa.Sim.DlHeap.brkAddr; sx_addr))

/-- **`_sbrk_r`** from its entry, for any increment word: when the advanced
break `nbrk` stays within `__heap_end` the break moves there and `a0` is the
old break; otherwise `a0 = -1` and the break is kept. -/
theorem sbrk_r_gen {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ allocText, live p.1) {R : Nat → BitVec 64} {Mt : Mem} {brkv nbrk : Nat}
    (P : SbrkPreG S R Mt brkv nbrk)
    (hok : nbrk ≤ heapEnd → ∀ R' Mt', SbrkPost R R' Mt Mt' nbrk →
      R' 10 = BitVec.ofNat 64 brkv → AW live S Q (R 1) R' Mt')
    (hfail : heapEnd < nbrk → ∀ R' Mt', SbrkPost R R' Mt Mt' brkv →
      R' 10 = 18446744073709551615#64 → AW live S Q (R 1) R' Mt') :
    AW live S Q 0x8000696c#64 R Mt := by
  have hsum := P.sum; have hbrk := P.brk; have hbp := P.brk_pos
  have hbl := P.brk_le; have hlo := P.sp_lo; have hhi := P.sp_hi; have hal := P.sp_al
  have hra := P.ra_al; have ho1 := P.off1; have ho2 := P.off2
  unfold heapEnd at hbl; unfold Vsa.Sim.tohostAddr at hlo
  unfold brkAddr at hbrk
  sx_run [8] hlive at 0x8000011c
  simp (disch := decide) only [ldv_at hbrk]
  refine st_8000011c hlive (fun h => ?_) (fun _ => ?_)
  · exfalso
    simp only [upd_apply, Nat.reduceEqDiff, ite_true] at h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    simp at this; omega
  sx_run [4] hlive at 0x8000012c
  refine st_8000012c hlive (fun hbad => ?_) (fun hok' => ?_)
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hbad
    sx_run [30] hlive at 0x8000016c
    simp only [impure_val] at *
    sx_run [30] hlive
    have hlt : heapEnd < nbrk := by rw [← hsum]; unfold heapEnd; simpa using hbad
    refine hfail hlt _ _ ⟨?_, ?_, ?_, ?_⟩ ?_
    · intro x h10 h14 h15
      by_cases h1 : x = 1
      · subst h1; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      by_cases h2 : x = 2
      · subst h2; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        apply BitVec.eq_of_toNat_eq; sx_addr
      by_cases h8 : x = 8
      · subst h8; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      simp only [upd_apply, h1, h2, h8, h10, h14, h15, ite_false]
    · unfold brkAddr
      rw [read64_store_miss _ _ (by sx_addr), read64_store_miss _ _ (by sx_addr),
        read64_store_miss _ _ (by sx_addr), read64_store_miss _ _ (by sx_addr),
        read64_store_miss _ _ (by sx_addr)]
      exact hbrk
    · intro a ha
      unfold SbrkW brkAddr at ha
      rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
        simp only [OutL, and_true] <;> sx_addr
    · intro a h
      exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
        (writeLog_present _ _ _ (writeLog_present _ _ _ h))))
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hok'
    sx_run [30] hlive
    have hle : nbrk ≤ heapEnd := by rw [← hsum]; unfold heapEnd; simpa using hok'
    refine hok hle _ _ ⟨?_, ?_, ?_, ?_⟩ ?_
    · intro x h10 h14 h15
      by_cases h1 : x = 1
      · subst h1; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      by_cases h2 : x = 2
      · subst h2; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        apply BitVec.eq_of_toNat_eq; sx_addr
      by_cases h8 : x = 8
      · subst h8; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      simp only [upd_apply, h1, h2, h8, h10, h14, h15, ite_false]
    · unfold brkAddr; rw [read64_store_hit]; congr 1
    · intro a ha
      unfold SbrkW brkAddr at ha
      rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;>
        sx_addr
    · intro a h
      exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
        (writeLog_present _ _ _ h)))
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]

/-- **`_sbrk_r`** from its entry: on success (`brkv + sb ≤ __heap_end`) the
break advances and `a0` is the old break; otherwise `a0 = -1` and the break
is kept. -/
theorem sbrk_r_run {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ allocText, live p.1) {R : Nat → BitVec 64} {Mt : Mem} {brkv sb : Nat}
    (P : SbrkPre S R Mt brkv sb)
    (hok : brkv + sb ≤ heapEnd → ∀ R' Mt', SbrkPost R R' Mt Mt' (brkv + sb) →
      R' 10 = BitVec.ofNat 64 brkv → AW live S Q (R 1) R' Mt')
    (hfail : heapEnd < brkv + sb → ∀ R' Mt', SbrkPost R R' Mt Mt' brkv →
      R' 10 = 18446744073709551615#64 → AW live S Q (R 1) R' Mt') :
    AW live S Q 0x8000696c#64 R Mt := by
  have hbl := P.brk_le; have hsb := P.a1; have hsblt := P.sb_lt
  unfold heapEnd at hbl
  refine sbrk_r_gen hlive ⟨?_, P.brk, P.brk_pos, P.brk_le, P.sp_lo, P.sp_hi, P.sp_al, P.ra_al,
    P.off1, P.off2, P.own⟩ hok hfail
  rw [BitVec.toNat_add, hsb, BitVec.toNat_ofNat]; omega

end VsaIris.VsaHeap
