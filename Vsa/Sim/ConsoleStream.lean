import Vsa.MemRepr
import Vsa.Sim.ReprSurvival
import Vsa.Sim.ValueSpec

/-!
# Initialized newlib stdout state

This is the post-CRT state used by the fixed interpreter image. It is not an
ELF-static predicate: CRT initialization changes the reentrancy record and the
`FILE` object before entering `interp_run`.

The pinned fields are exactly those followed by the successful output path:
`fputc -> _putc_r -> __swbuf_r -> _fflush_r -> __sflush_r -> __swrite ->
_write_r -> _write`.
The one-byte backing buffer may contain the most recently printed byte.
-/

open Vsa.MemRepr

namespace Vsa.Sim

def consoleImpurePtrAddr : Nat := 0x8001b970
def consoleReent : Nat := 0x8001b538
def consoleStdout : Nat := 0x8001bb20
def consoleBuf : Nat := 0x8001bb97
def consoleSinit : Nat := 0x80005d2c
def consoleSwrite : Nat := 0x8000efd4

/-- Bytes which newlib may inspect or update while writing stdout. The FILE
object bound is intentionally wider than the fields pinned below. -/
def ConsoleFoot (a : Nat) : Prop :=
  (consoleImpurePtrAddr ≤ a ∧ a < consoleImpurePtrAddr + 8) ∨
  (consoleReent ≤ a ∧ a < consoleReent + 256) ∨
  (consoleStdout ≤ a ∧ a < consoleStdout + 184) ∨
  a = consoleBuf

/-- `stdout`'s `_flags`: `__SWR | __SNBF` (`0x000a`) as `main`'s
`setvbuf(stdout, 0, _IONBF, 0)` leaves it, and `0x200a` once a write has
oriented the stream (`__SORD`, set by `ORIENT` at the head of `_fputs_r`,
`_fwrite_r`, `_vfprintf_r` and `__swbuf_r`; `Vsa.Sim.ConsoleOrient`). -/
@[reducible] def consoleFlags (oriented : Bool) : Nat := if oriented then 0x200a else 0x000a

/-- The high byte of `consoleFlags`. -/
@[reducible] def consoleFlag1 (oriented : Bool) : BitVec 8 := if oriented then 0x20#8 else 0x00#8

/-- Initialized stdout state at interpreter and native-call boundaries, at
orientation `oriented`. The `_w = 0`, one-byte buffer, and `__swrite` callback
force `fputc` down the terminal-write path rather than allowing an arbitrary
buffered `FILE`. `interp_run`'s entry is unoriented (`ConsoleBoot`); the first
write orients it and every later boundary is `ConsoleStream`. -/
structure ConsoleStreamAt (oriented : Bool) (m : Mem) : Prop where
  impure : read64 m consoleImpurePtrAddr = some consoleReent
  stdout : read64 m (consoleReent + 16) = some consoleStdout
  sinit : read64 m (consoleReent + 72) = some consoleSinit
  cursor : read64 m (consoleStdout + 0) = some consoleBuf
  readCount : read32 m (consoleStdout + 8) = some 0
  writeCount : read32 m (consoleStdout + 12) = some 0
  flags : readLE m (consoleStdout + 16) 2 = some (consoleFlags oriented)
  flag0 : m[consoleStdout + 16]? = some 0x0a#8
  flag1 : m[consoleStdout + 17]? = some (consoleFlag1 oriented)
  fd : readLE m (consoleStdout + 18) 2 = some 1
  base : read64 m (consoleStdout + 24) = some consoleBuf
  bufSize : read32 m (consoleStdout + 32) = some 1
  lineBufSize : read32 m (consoleStdout + 40) = some 0
  cookie : read64 m (consoleStdout + 48) = some consoleStdout
  writer : read64 m (consoleStdout + 64) = some consoleSwrite
  lock : read64 m (consoleStdout + 160) = some 0
  lockMode : read32 m (consoleStdout + 176) = some 0
  bufferByte : ∃ b : BitVec 8, m[consoleBuf]? = some b

/-- `stdout` after its first write (`_flags = 0x200a`): the state at every
boundary after a console write, and the one the write paths flush from. -/
abbrev ConsoleStream (m : Mem) : Prop := ConsoleStreamAt true m

/-- `stdout` at `interp_run`'s entry (`_flags = 0x000a`, not yet oriented). -/
abbrev ConsoleBoot (m : Mem) : Prop := ConsoleStreamAt false m

/-- The transient FILE state at the concrete `_fflush_r`/`__sflush_r` call.
`__swbuf_r` has installed the byte and advanced `_p` by one.  Because stdout
is unbuffered, `_w` has wrapped from zero to `-1`; the flush restores the
stable `ConsoleStream` cursor/count pair after `__swrite` emits this byte. -/
structure ConsoleFlushState (m : Mem) (ch : BitVec 8) : Prop where
  impure : read64 m consoleImpurePtrAddr = some consoleReent
  stdout : read64 m (consoleReent + 16) = some consoleStdout
  sinit : read64 m (consoleReent + 72) = some consoleSinit
  cursor : read64 m (consoleStdout + 0) = some (consoleBuf + 1)
  readCount : read32 m (consoleStdout + 8) = some 0
  writeCount : read32 m (consoleStdout + 12) = some 0xffffffff
  flags : readLE m (consoleStdout + 16) 2 = some 0x200a
  flag0 : m[consoleStdout + 16]? = some 0x0a#8
  flag1 : m[consoleStdout + 17]? = some 0x20#8
  fd : readLE m (consoleStdout + 18) 2 = some 1
  base : read64 m (consoleStdout + 24) = some consoleBuf
  bufSize : read32 m (consoleStdout + 32) = some 1
  lineBufSize : read32 m (consoleStdout + 40) = some 0
  cookie : read64 m (consoleStdout + 48) = some consoleStdout
  writer : read64 m (consoleStdout + 64) = some consoleSwrite
  lock : read64 m (consoleStdout + 160) = some 0
  lockMode : read32 m (consoleStdout + 176) = some 0
  bufferByte : m[consoleBuf]? = some ch

def IsConsoleStdout (stream : BitVec 64) : Prop :=
  stream = BitVec.ofNat 64 consoleStdout

/-- A two-byte little-endian field equal to one has the unique byte image
`[1, 0]`.  This is the byte-level fact consumed by the reflected `lh` row. -/
theorem readLE_two_one_bytes {m : Mem} {a : Nat}
    (h : readLE m a 2 = some 1) :
    m[a]? = some 1#8 ∧ m[a + 1]? = some 0#8 := by
  generalize h0 : m[a]? = o0 at h
  cases o0 with
  | none => simp [readLE, h0] at h
  | some b0 =>
      generalize h1 : m[a + 1]? = o1 at h
      cases o1 with
      | none => simp [readLE, h0, h1] at h
      | some b1 =>
          simp [readLE, h0, h1] at h
          have hb0 := b0.isLt
          have hb1 := b1.isLt
          have e0 : b0 = 1#8 := by
            apply BitVec.eq_of_toNat_eq
            change b0.toNat = 1
            omega
          have e1 : b1 = 0#8 := by
            apply BitVec.eq_of_toNat_eq
            change b1.toNat = 0
            omega
          simpa [e0, e1] using And.intro h0 h1

theorem ConsoleStreamAt.of_eq {o : Bool} {m m' : Mem} (h : m = m')
    (hc : ConsoleStreamAt o m) : ConsoleStreamAt o m' := by
  subst m'
  exact hc

/-- Preservation by pointwise agreement on the concrete fields. -/
theorem ConsoleStreamAt.of_agree {o : Bool} {m m' : Mem}
    (h : ∀ a, ConsoleFoot a → m'[a]? = m[a]?)
    (hc : ConsoleStreamAt o m) : ConsoleStreamAt o m' := by
  have hag : AgreeP ConsoleFoot m m' := fun a ha => (h a ha).symm
  refine {
    impure := ?_, stdout := ?_, sinit := ?_, cursor := ?_,
    readCount := ?_, writeCount := ?_, flags := ?_, flag0 := ?_, flag1 := ?_,
    fd := ?_, base := ?_,
    bufSize := ?_, lineBufSize := ?_, cookie := ?_, writer := ?_, lock := ?_,
    lockMode := ?_, bufferByte := ?_ }
  · rw [← read64_agreeP hag (fun k hk => Or.inl ⟨by omega, by omega⟩)]
    exact hc.impure
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact hc.stdout
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact hc.sinit
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.cursor
  · rw [← read32_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.readCount
  · rw [← read32_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.writeCount
  · rw [← readLE_agreeP hag 2 _ (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.flags
  · exact (h _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans hc.flag0
  · exact (h _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans hc.flag1
  · rw [← readLE_agreeP hag 2 _ (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.fd
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.base
  · rw [← read32_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.bufSize
  · rw [← read32_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.lineBufSize
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.cookie
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.writer
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.lock
  · rw [← read32_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.lockMode
  · obtain ⟨b, hb⟩ := hc.bufferByte
    exact ⟨b, (h consoleBuf (Or.inr (Or.inr (Or.inr rfl)))).trans hb⟩

/-- **The first write orients `stdout`.** `ORIENT` (`_fputs_r` `0x80006418`,
`_fwrite_r` `0x800050f0`, `_vfprintf_r` `0x8000a8fc`, `__swbuf_r`
`0x8000f1b4`) stores `_flags | __SORD` with `sh` and `_flags2 & ~__SWID` with
`sw`: on `ConsoleStreamAt o` the first is `0x200a` (low byte unchanged, high
byte `0x20`) and the second rewrites `_flags2 = 0` with `0`. Any memory that
agrees with `m` on the rest of `ConsoleFoot` and holds `0x20` at
`consoleStdout + 17` is the oriented `ConsoleStream`, from either orientation
(so a later `ORIENT`, which the binary skips, would be harmless too). -/
theorem ConsoleStreamAt.orient {o : Bool} {m m' : Mem}
    (h : ∀ a, ConsoleFoot a → a ≠ consoleStdout + 17 → m'[a]? = m[a]?)
    (h17 : m'[consoleStdout + 17]? = some 0x20#8)
    (hc : ConsoleStreamAt o m) : ConsoleStream m' := by
  let P : Nat → Prop := fun a => ConsoleFoot a ∧ a ≠ consoleStdout + 17
  have hag : AgreeP P m m' := fun a ha => (h a ha.1 ha.2).symm
  have hF : ∀ (n a : Nat), (∀ k, k < n → P (a + k)) → readLE m' a n = readLE m a n :=
    fun n a hk => (readLE_agreeP hag n a hk).symm
  have r : ∀ (n a : Nat), ((consoleImpurePtrAddr ≤ a ∧ a + n ≤ consoleImpurePtrAddr + 8) ∨
      (consoleReent ≤ a ∧ a + n ≤ consoleReent + 256) ∨
      (consoleStdout ≤ a ∧ a + n ≤ consoleStdout + 184)) →
      (a + n ≤ consoleStdout + 17 ∨ consoleStdout + 18 ≤ a) →
      readLE m' a n = readLE m a n := by
    intro n a h1 h2
    refine hF n a fun k hk => ⟨?_, by omega⟩
    unfold ConsoleFoot; omega
  have b16 : m'[consoleStdout + 16]? = some 0x0a#8 :=
    (h _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))) (by omega)).trans hc.flag0
  refine {
    impure := ?_, stdout := ?_, sinit := ?_, cursor := ?_,
    readCount := ?_, writeCount := ?_, flags := ?_, flag0 := b16, flag1 := h17,
    fd := ?_, base := ?_, bufSize := ?_, lineBufSize := ?_, cookie := ?_, writer := ?_,
    lock := ?_, lockMode := ?_, bufferByte := ?_ }
  · exact (r 8 _ (Or.inl ⟨by omega, by omega⟩) (by left; decide)).trans hc.impure
  · exact (r 8 _ (Or.inr (Or.inl ⟨by omega, by omega⟩)) (by left; decide)).trans hc.stdout
  · exact (r 8 _ (Or.inr (Or.inl ⟨by omega, by omega⟩)) (by left; decide)).trans hc.sinit
  · exact (r 8 _ (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by left; omega)).trans hc.cursor
  · exact (r 4 _ (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by left; omega)).trans hc.readCount
  · exact (r 4 _ (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by left; omega)).trans hc.writeCount
  · simp [readLE, b16, h17, consoleFlags]
  · exact (r 2 _ (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by right; omega)).trans hc.fd
  · exact (r 8 _ (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by right; omega)).trans hc.base
  · exact (r 4 _ (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by right; omega)).trans hc.bufSize
  · exact (r 4 _ (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by right; omega)).trans hc.lineBufSize
  · exact (r 8 _ (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by right; omega)).trans hc.cookie
  · exact (r 8 _ (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by right; omega)).trans hc.writer
  · exact (r 8 _ (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by right; omega)).trans hc.lock
  · exact (r 4 _ (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by right; omega)).trans hc.lockMode
  · obtain ⟨b, hb⟩ := hc.bufferByte
    exact ⟨b, (h consoleBuf (Or.inr (Or.inr (Or.inr rfl))) (by decide)).trans hb⟩

theorem ConsoleFlushState.of_agree {m m' : Mem} {ch : BitVec 8}
    (h : ∀ a, ConsoleFoot a → m'[a]? = m[a]?)
    (hc : ConsoleFlushState m ch) : ConsoleFlushState m' ch := by
  have hag : AgreeP ConsoleFoot m m' := fun a ha => (h a ha).symm
  refine {
    impure := ?_, stdout := ?_, sinit := ?_, cursor := ?_,
    readCount := ?_, writeCount := ?_, flags := ?_, flag0 := ?_, flag1 := ?_,
    fd := ?_, base := ?_, bufSize := ?_, lineBufSize := ?_, cookie := ?_,
    writer := ?_, lock := ?_, lockMode := ?_, bufferByte := ?_ }
  · rw [← read64_agreeP hag (fun k hk => Or.inl ⟨by omega, by omega⟩)]
    exact hc.impure
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact hc.stdout
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact hc.sinit
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.cursor
  · rw [← read32_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.readCount
  · rw [← read32_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.writeCount
  · rw [← readLE_agreeP hag 2 _ (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.flags
  · exact (h _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans hc.flag0
  · exact (h _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans hc.flag1
  · rw [← readLE_agreeP hag 2 _ (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.fd
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.base
  · rw [← read32_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.bufSize
  · rw [← read32_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.lineBufSize
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.cookie
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.writer
  · rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.lock
  · rw [← read32_agreeP hag (fun k hk => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hc.lockMode
  · exact (h consoleBuf (Or.inr (Or.inr (Or.inr rfl)))).trans hc.bufferByte

/-- Exact FILE updates performed by the successful one-byte `__sflush_r`
prefix: reset `_p` to `_bf._base`, then reset `_w` to zero. -/
def closeConsoleFlush (m : Mem) : Mem :=
  writeMap4
    (writeMap8 m consoleStdout (sdData_val (BitVec.ofNat 64 consoleBuf)))
    (consoleStdout + 12) (swData (0#64))

theorem ConsoleFlushState.close {m : Mem} {ch : BitVec 8}
    (hc : ConsoleFlushState m ch) : ConsoleStream (closeConsoleFlush m) := by
  let P : Nat → Prop := fun a =>
    (a < consoleStdout ∨ consoleStdout + 8 ≤ a) ∧
    (a < consoleStdout + 12 ∨ consoleStdout + 16 ≤ a)
  have hag : AgreeP P m (closeConsoleFlush m) := by
    intro a ha
    unfold closeConsoleFlush
    rw [getElem_writeMap4_disjoint _ _ _ _ ha.2,
      getElem_writeMap8_disjoint _ _ _ _ ha.1]
  have hAway (n a : Nat)
      (h0 : a + n ≤ consoleStdout ∨ consoleStdout + 8 ≤ a)
      (h1 : a + n ≤ consoleStdout + 12 ∨ consoleStdout + 16 ≤ a) :
      ∀ k, k < n → P (a + k) := by
    intro k hk
    exact ⟨by rcases h0 with h | h <;> omega,
      by rcases h1 with h | h <;> omega⟩
  refine {
    impure := ?_, stdout := ?_, sinit := ?_, cursor := ?_,
    readCount := ?_, writeCount := ?_, flags := ?_, flag0 := ?_, flag1 := ?_,
    fd := ?_, base := ?_, bufSize := ?_, lineBufSize := ?_, cookie := ?_,
    writer := ?_, lock := ?_, lockMode := ?_, bufferByte := ?_ }
  · rw [← read64_agreeP hag (hAway 8 consoleImpurePtrAddr
      (by left; decide) (by left; decide))]
    exact hc.impure
  · rw [← read64_agreeP hag (hAway 8 (consoleReent + 16)
      (by left; decide) (by left; decide))]
    exact hc.stdout
  · rw [← read64_agreeP hag (hAway 8 (consoleReent + 72)
      (by left; decide) (by left; decide))]
    exact hc.sinit
  · unfold closeConsoleFlush
    rw [read64_writeMap4_disjoint _ _ _ _ (by omega)]
    simpa [Nat.add_zero, sdData_toNat, consoleBuf] using
      (read64_writeMap8 m consoleStdout
        (sdData_val (BitVec.ofNat 64 consoleBuf)))
  · rw [← read32_agreeP hag (hAway 4 (consoleStdout + 8)
      (by right; omega) (by left; omega))]
    exact hc.readCount
  · unfold closeConsoleFlush
    rw [read32_writeMap4, swData_toNat]
    rfl
  · rw [← readLE_agreeP hag 2 _ (hAway 2 (consoleStdout + 16)
      (by right; omega) (by right; omega))]
    exact hc.flags
  · exact (hag _ (hAway 1 (consoleStdout + 16) (by right; omega)
      (by right; omega) 0 (by omega))).symm.trans hc.flag0
  · exact (hag _ (hAway 1 (consoleStdout + 17) (by right; omega)
      (by right; omega) 0 (by omega))).symm.trans hc.flag1
  · rw [← readLE_agreeP hag 2 _ (hAway 2 (consoleStdout + 18)
      (by right; omega) (by right; omega))]
    exact hc.fd
  · rw [← read64_agreeP hag (hAway 8 (consoleStdout + 24)
      (by right; omega) (by right; omega))]
    exact hc.base
  · rw [← read32_agreeP hag (hAway 4 (consoleStdout + 32)
      (by right; omega) (by right; omega))]
    exact hc.bufSize
  · rw [← read32_agreeP hag (hAway 4 (consoleStdout + 40)
      (by right; omega) (by right; omega))]
    exact hc.lineBufSize
  · rw [← read64_agreeP hag (hAway 8 (consoleStdout + 48)
      (by right; omega) (by right; omega))]
    exact hc.cookie
  · rw [← read64_agreeP hag (hAway 8 (consoleStdout + 64)
      (by right; omega) (by right; omega))]
    exact hc.writer
  · rw [← read64_agreeP hag (hAway 8 (consoleStdout + 160)
      (by right; omega) (by right; omega))]
    exact hc.lock
  · rw [← read32_agreeP hag (hAway 4 (consoleStdout + 176)
      (by right; omega) (by right; omega))]
    exact hc.lockMode
  · exact ⟨ch, (hag consoleBuf
      (hAway 1 consoleBuf (by right; decide) (by right; decide) 0 (by omega))).symm.trans
      hc.bufferByte⟩

end Vsa.Sim
