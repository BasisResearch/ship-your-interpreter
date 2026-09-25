import VsaIris.Vsa.Stdout.Steps
import VsaIris.Vsa.SymRunO
import VsaIris.Vsa.SymJalr
import VsaIris.Interp.ITac

/-!
# `_write`: the console loop (lane N1)

`_write(fd, buf, n)` (`0x8000003c`, libgloss HTIF) ignores `fd` and stores
each byte of `buf[0, n)` to `tohost` as a putchar command, then returns `n`:

```
8000003c beqz a2,64        80000050 addi a1,a1,1
80000040 li   a4,257       80000054 or   a5,a5,a4
80000044 add  a3,a1,a2     80000058 auipc a6,0x1b
80000048 slli a4,a4,0x30   8000005c sd   a5,-856(a6)   (tohost: prints)
8000004c lbu  a5,0(a1)     80000060 bne  a1,a3,4c
80000064 mv   a0,a2 ; ret
```

`write_run` is the whole call as a transformer of printing symbolic runs
(`SWPO`): the console grows by the bytes (`putcs`), `a0 = n`, and only
`a0`, `a1`, `a3`–`a6` change. A byte is read either from owned bytes (the
tracking memory: `stdout`'s one-byte buffer, a stack buffer) or from the
persistent data view (a string argument): `ByteSrc`.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- What the console prints for a byte sequence. -/
def putcs (bs : List (BitVec 8)) : String := String.join (bs.map putcStr)

@[simp] theorem putcs_nil : putcs [] = "" := rfl

theorem putcs_cons (b : BitVec 8) (bs : List (BitVec 8)) :
    putcs (b :: bs) = putcStr b ++ putcs bs := by
  simp [putcs, String.join_cons]

theorem putcs_append (xs ys : List (BitVec 8)) : putcs (xs ++ ys) = putcs xs ++ putcs ys := by
  simp [putcs, List.map_append, String.join_append]

/-- Where a loaded byte lives: owned (tracking memory `Mt`) or in the
persistent data view (`Dt` on `DA`). -/
def ByteSrc (S : Nat → Prop) (Mt Dt : Mem) (DA : List Nat) (a : Nat) (b : BitVec 8) : Prop :=
  (S a ∧ imgM Mt a = b) ∨ (a ∈ DA ∧ imgM Dt a = b)

/-- A byte source survives a store off the byte. -/
theorem ByteSrc.store {S : Nat → Prop} {Mt Dt : Mem} {DA : List Nat} {a : Nat} {b : BitVec 8}
    (h : ByteSrc S Mt Dt DA a b) {addr w : Nat} (v : BitVec 64) (hd : a < addr ∨ addr + w ≤ a) :
    ByteSrc S (writeLog Mt [(addr, w, v)]) Dt DA a b := by
  rcases h with ⟨h1, h2⟩ | h
  · exact .inl ⟨h1, by rw [imgM_store_miss _ _ hd, h2]⟩
  · exact .inr h

theorem ldv_lbu (M : Mem) (a : Nat) : ldv .lbu M a = zero_extend (m := 64) (imgM M a) := by
  simp [ldv, bytesAt, bytesVal, widthOfM]

/-- The registers `_write` changes. -/
abbrev writeClob : List Nat := [10, 11, 13, 14, 15, 16]

/-- The state after `_write` returns: `a0 = n`, back at `ra`, and every
register outside `writeClob` (and the PC) unchanged. -/
structure WriteOut (R R' : Nat → BitVec 64) : Prop where
  a0 : R' 10 = R 12
  keep : ∀ x, x ≠ 32 → x ∉ writeClob → R' x = R x

section Loop

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}

/-- The putchar word `_write` builds: `0x0101 << 48 | b`. -/
theorem write_word (b : BitVec 8) :
    zero_extend (m := 64) b ||| shift_bits_left ((0#64) + sign_extend (m := 64) (0x101#12))
      (Sail.BitVec.extractLsb (0x30#6) 5 0) = putcWord b := by
  have e : shift_bits_left ((0#64) + sign_extend (m := 64) (0x101#12))
      (Sail.BitVec.extractLsb (0x30#6) 5 0) = 0x0101000000000000#64 := by decide
  rw [e, BitVec.or_comm]
  rfl

/-- The putchar store `sd a5,-856(a6)` inside a `_write` run. -/
theorem write_putc (hl : ∀ p ∈ stdioText, live p.1) (b : BitVec 8) {t : String}
    {R : Nat → BitVec 64} (h16 : R 16 = 0x8001b058#64) (h15 : R 15 = putcWord b)
    (hk : SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q (t ++ putcStr b) 0x80000060#64 R Mt) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t 0x8000005c#64 R Mt :=
  swp_putc putcSite putcSite_cert b (fun p hp => hl _ (stdio_code_8000005c p hp))
    (fun p hp => List.mem_append_left _ (stdio_code_8000005c p hp))
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl h16 h15 hk

/-- The shifted putchar command `a4` holds in the loop. -/
abbrev writeCmd : BitVec 64 :=
  shift_bits_left ((0#64) + sign_extend (m := 64) (0x101#12)) (Sail.BitVec.extractLsb (0x30#6) 5 0)

theorem toNat_ofNat_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem sx0 : sign_extend (m := 64) (0x000#12) = 0#64 := by decide

theorem ofNat_add_sx0 (a : Nat) : BitVec.ofNat 64 a + sign_extend (m := 64) (0x000#12) = BitVec.ofNat 64 a := by
  rw [show sign_extend (m := 64) (0x000#12) = 0#64 by decide, BitVec.add_zero]

theorem ofNat_add_sx1 (a : Nat) :
    BitVec.ofNat 64 a + sign_extend (m := 64) (0x001#12) = BitVec.ofNat 64 (a + 1) := by
  rw [show sign_extend (m := 64) (0x001#12) = 1#64 by decide]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]

/-- One pass of the `_write` loop body from `lbu` to the `bne`: loads `bs[j]`,
prints it, advances `a1`. -/
theorem write_iter (hl : ∀ p ∈ stdioText, live p.1) (buf : Nat) (bs : List (BitVec 8))
    (hlo : 0x80000000 ≤ buf) (hhi : buf + bs.length ≤ 0x100000000)
    (hht : buf + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ buf)
    (hsrc : ∀ i (h : i < bs.length), ByteSrc S Mt Dt DA (buf + i) bs[i])
    (j : Nat) (hj : j < bs.length) (R : Nat → BitVec 64) (t : String)
    (h11 : R 11 = BitVec.ofNat 64 (buf + j)) (h14 : R 14 = writeCmd)
    (hk : SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q (t ++ putcStr bs[j]) 0x80000060#64
      (upd (upd (upd R 15 (putcWord bs[j])) 11 (BitVec.ofNat 64 (buf + j + 1))) 16 0x8001b058#64) Mt) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t 0x8000004c#64 R Mt := by
  have hlt : buf + j < 2 ^ 64 := by omega
  have ea : ((R 11) + sign_extend (m := 64) (0x000#12)).toNat = buf + j := by
    rw [h11, ofNat_add_sx0, toNat_ofNat_lt hlt]
  have hea : LdOK ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1 := by
    show LdOK _ 1
    rw [ea]; simp only [LdOK]; unfold tohostAddr at *; omega
  have cont : SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t 0x80000050#64
      (upd R 15 (zero_extend (m := 64) bs[j])) Mt := by
    refine it_80000050 hl (it_80000054 hl (it_80000058 hl ?_))
    refine write_putc hl bs[j] (by simp [upd]; decide) ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, reduceIte]
      rw [h14, write_word]
    · refine swp_congr (fun x _ _ => ?_) hk
      simp only [upd_apply]
      by_cases e16 : x = 16
      · subst e16; simp; decide
      by_cases e11 : x = 11
      · subst e11; simp [h11, ofNat_add_sx1]
      by_cases e15 : x = 15
      · subst e15; simp [h14, write_word]
      simp [e16, e11, e15]
  rcases hsrc j hj with ⟨hS, himg⟩ | ⟨hD, himg⟩
  · refine it_8000004c hl hea (fun b hb => ?_) ?_
    · rw [ea] at hb; rw [(of_mem_accAddrs hb) |> fun h => show b = buf + j by omega]; exact hS
    · rw [ea, ldv_lbu, himg]; exact cont
  · refine itD_8000004c hl hea (fun b hb => ?_) ?_
    · rw [ea] at hb; rw [(of_mem_accAddrs hb) |> fun h => show b = buf + j by omega]; exact hD
    · rw [ea, ldv_lbu, himg]; exact cont

theorem putcs_drop (bs : List (BitVec 8)) (j : Nat) (hj : j < bs.length) :
    putcs (bs.drop j) = putcStr bs[j] ++ putcs (bs.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons hj, putcs_cons]

/-- **The `_write` loop** from `lbu` at `0x8000004c` with `bs[j]` next and
`k + 1` bytes left: prints `bs[j, n)` and reaches `mv a0,a2` with `a1` at the
end and only `a1`, `a5`, `a6` changed. -/
theorem write_loop (hl : ∀ p ∈ stdioText, live p.1) (buf : Nat) (bs : List (BitVec 8))
    (hlo : 0x80000000 ≤ buf) (hhi : buf + bs.length ≤ 0x100000000)
    (hht : buf + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ buf)
    (hsrc : ∀ i (h : i < bs.length), ByteSrc S Mt Dt DA (buf + i) bs[i]) :
    ∀ k j (R : Nat → BitVec 64) (t : String), j + k + 1 = bs.length →
      R 11 = BitVec.ofNat 64 (buf + j) → R 13 = BitVec.ofNat 64 (buf + bs.length) →
      R 14 = writeCmd →
      (∀ R' : Nat → BitVec 64, R' 11 = R 13 → R' 16 = 0x8001b058#64 →
        (∀ x, x ≠ 11 → x ≠ 15 → x ≠ 16 → R' x = R x) →
        SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q (t ++ putcs (bs.drop j)) 0x80000064#64 R' Mt) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t 0x8000004c#64 R Mt := by
  intro k
  induction k with
  | zero =>
    intro j R t hjk h11 h13 h14 hk
    have hj : j < bs.length := by omega
    refine write_iter hl buf bs hlo hhi hht hsrc j hj R t h11 h14 (it_80000060 hl ?_ ?_)
    · intro hc; exfalso; apply hc
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [h13]; congr 1; omega
    · intro _
      have e : putcs (bs.drop j) = putcStr bs[j] := by
        rw [putcs_drop bs j hj, show j + 1 = bs.length by omega, List.drop_length, putcs_nil,
          String.append_empty]
      rw [← e]
      refine hk _ ?_ (by simp [upd_apply]) (fun x h1 h2 h3 => by simp [upd_apply, h1, h2, h3])
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [h13]; congr 1; omega
  | succ k ih =>
    intro j R t hjk h11 h13 h14 hk
    have hj : j < bs.length := by omega
    refine write_iter hl buf bs hlo hhi hht hsrc j hj R t h11 h14 (it_80000060 hl ?_ ?_)
    · intro _
      refine ih (j + 1) _ _ (by omega) (by simp [upd_apply, Nat.add_assoc]) (by simp [upd_apply, h13])
        (by simp [upd_apply, h14]) fun R' h11' h16' hkeep => ?_
      rw [String.append_assoc, ← putcs_drop bs j hj]
      refine hk R' (by rw [h11']; simp [upd_apply]) h16' fun x h1 h2 h3 => ?_
      rw [hkeep x h1 h2 h3]; simp [upd_apply, h1, h2, h3]
    · intro hc; exfalso; apply hc
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [h13]
      intro e
      have := congrArg BitVec.toNat e
      rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
      omega

/-- **`_write(fd, buf, n)`** from its entry with `ra = R 1`: prints `bs`
(`n = |bs|` bytes at `buf`), returns `n`, changes only `writeClob`. -/
theorem write_run (hl : ∀ p ∈ stdioText, live p.1) (buf : Nat) (bs : List (BitVec 8))
    (hlo : 0x80000000 ≤ buf) (hhi : buf + bs.length ≤ 0x100000000)
    (hht : buf + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ buf)
    (hsrc : ∀ i (h : i < bs.length), ByteSrc S Mt Dt DA (buf + i) bs[i])
    (R : Nat → BitVec 64) (t : String) (h11 : R 11 = BitVec.ofNat 64 buf)
    (h12 : R 12 = BitVec.ofNat 64 bs.length) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' : Nat → BitVec 64, WriteOut R R' →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q (t ++ putcs bs) (R 1) R' Mt) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t 0x8000003c#64 R Mt := by
  refine it_8000003c hl (fun h0 => ?_) (fun h0 => ?_)
  · -- `n = 0`
    have hn : bs.length = 0 := by
      have := congrArg BitVec.toNat (h12.symm.trans h0)
      rw [toNat_ofNat_lt (by omega)] at this; simpa using this
    have e : bs = [] := List.eq_nil_of_length_eq_zero hn
    subst e
    refine it_80000064 hl (it_80000068 hl (by simpa [upd_apply] using hal) ?_)
    simp only [putcs_nil, String.append_empty] at hk
    refine swp_congr (R' := upd R 10 (R 12 + sign_extend (m := 64) (0x000#12))) (fun x _ _ => rfl) ?_
    rw [show upd R 10 (R 12 + sign_extend (m := 64) (0x000#12)) 1 = R 1 by simp [upd_apply]]
    exact hk _ ⟨by simp [upd_apply, h0]; decide, fun x _ hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [upd_apply, hx.1]⟩
  · have hpos : 0 < bs.length := by
      rcases Nat.eq_zero_or_pos bs.length with h | h
      · exact absurd (by rw [h12, h]) h0
      · exact h
    refine it_80000040 hl (it_80000044 hl (it_80000048 hl ?_))
    refine write_loop hl buf bs hlo hhi hht hsrc (bs.length - 1) 0 _ t (by omega)
      (by simp [upd_apply, h11]) ?_ rfl fun R' h11' h16' hkeep => ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [h11, h12]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]; try omega
    · simp only [List.drop_zero] at hk ⊢
      refine it_80000064 hl (it_80000068 hl ?_ ?_)
      · rw [upd_apply, if_neg (by decide), hkeep 1 (by decide) (by decide) (by decide)]
        simpa [upd_apply] using hal
      · have e1 : upd R' 10 (R' 12 + sign_extend (m := 64) (0x000#12)) 1 = R 1 := by
          rw [upd_apply, if_neg (by decide), hkeep 1 (by decide) (by decide) (by decide)]
          simp [upd_apply]
        rw [e1]
        refine hk _ ⟨?_, fun x hx32 hx => ?_⟩
        · rw [upd_apply, if_pos rfl, hkeep 12 (by decide) (by decide) (by decide)]
          simp [upd_apply, sx0]
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          obtain ⟨h10, h11x, h13, h14, h15, h16⟩ := hx
          rw [upd_apply, if_neg h10, hkeep x h11x h15 h16]
          simp [upd_apply, h13, h14]

/-- `_write`'s end state as an explicit register file: `a0 = n`, the
clobbered `a1`, `a3`–`a6` at some values. -/
abbrev writeRegs (R : Nat → BitVec 64) (v11 v13 v14 v15 v16 : BitVec 64) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd R 10 (R 12)) 11 v11) 13 v13) 14 v14) 15 v15) 16 v16

/-- **`_write`**, with the end state as an explicit register file (the form
`ix_run` continues from). -/
theorem write_run' (hl : ∀ p ∈ stdioText, live p.1) (buf : Nat) (bs : List (BitVec 8))
    (hlo : 0x80000000 ≤ buf) (hhi : buf + bs.length ≤ 0x100000000)
    (hht : buf + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ buf)
    (hsrc : ∀ i (h : i < bs.length), ByteSrc S Mt Dt DA (buf + i) bs[i])
    (R : Nat → BitVec 64) (t : String) (h11 : R 11 = BitVec.ofNat 64 buf)
    (h12 : R 12 = BitVec.ofNat 64 bs.length) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ v11 v13 v14 v15 v16 : BitVec 64,
      SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q (t ++ putcs bs) (R 1)
        (writeRegs R v11 v13 v14 v15 v16) Mt) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t 0x8000003c#64 R Mt := by
  refine write_run hl buf bs hlo hhi hht hsrc R t h11 h12 hal fun R' hw => ?_
  refine swp_congr (fun x _ hx => ?_) (hk (R' 11) (R' 13) (R' 14) (R' 15) (R' 16))
  simp only [upd_apply]
  by_cases e16 : x = 16; · simp [e16]
  by_cases e15 : x = 15; · simp [e15]
  by_cases e14 : x = 14; · simp [e14]
  by_cases e13 : x = 13; · simp [e13]
  by_cases e11 : x = 11; · simp [e11]
  by_cases e10 : x = 10; · simp [e10, hw.a0]
  simp only [e16, e15, e14, e13, e11, e10, ite_false]
  exact (hw.keep x (by simpa [VsaIris.PC] using hx) (by simp [e16, e15, e14, e13, e11, e10])).symm

end Loop

end VsaIris.Sym
