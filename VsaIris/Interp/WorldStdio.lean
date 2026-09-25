import VsaIris.Vsa.Stdio
import VsaIris.Interp.Bridge
import VsaIris.Vsa.HeapShape

/-!
# newlib's runtime data at the boundary (A0)

`Stdio.StdioOK img` asks that every memory holding `img` on `stdioFoot`
satisfy `ConsoleStream`, `ExitRuntimeData` and the `stderr` pointer. At the
boundary `img` is the total read `memImg m` of the configuration's memory, so
each read fact of `m` moves to any such memory (`readLE_of_img`): a successful
read already proves its bytes present, and nothing else is needed.
`ConsoleStream.of_agree` does not apply: its footprint `ConsoleFoot` covers
the whole reentrancy record, including the allocator's `_errno` word, which is
outside `stdioFoot`.
-/

namespace VsaIris.Interp

open Vsa.MemRepr Vsa.Sim VsaIris.Stdio VsaIris.VsaHeap

set_option autoImplicit false

/-- A successful read moves to any memory holding the image on its bytes
(`readLE_memImg`, then `Repr.readLE_of_img`). -/
theorem readLE_img {P : Nat → Prop} {m m' : Mem} (h : ImgOn P (memImg m) m') (n a : Nat)
    {v : Nat}
    (hr : readLE m a n = some v) (hin : ∀ k, k < n → P (a + k)) : readLE m' a n = some v := by
  rw [← readLE_memImg hr]
  exact readLE_of_img fun i hi => h _ (hin i hi)

theorem byte_of_img {P : Nat → Prop} {m m' : Mem} (h : ImgOn P (memImg m) m') {a : Nat}
    {b : BitVec 8}
    (hb : m[a]? = some b) (hin : P a) : m'[a]? = some b := by
  rw [h a hin, memImg_eq hb]

/-- Every byte of a read below lies in `stdioFoot`: the constants are
concrete, so one `omega` after unfolding. -/
macro "stdio_in" : tactic =>
  `(tactic| (intro k hk; simp only [stdioFoot, Stdio.InRange, consoleImpurePtrAddr, consoleReent,
      consoleStdout, consoleBuf, exitAtexitAddr, exitAtexitLockAddr, exitStdioHandlerAddr,
      exitGlueAddr, exitStdin, exitStderr, stderrPtrAddr] at *; omega))

/-- A locale read's bytes lie in `stdioFoot`. -/
macro "stdio_in_locale" : tactic =>
  `(tactic| (intro k hk; simp only [stdioFoot, Stdio.InRange, localeMbtowcAddr, localeMbMaxAddr,
      localeDecPointAddr] at *; omega))

/-- One byte in `stdioFoot`. -/
macro "stdio_in_one" : tactic =>
  `(tactic| (simp only [stdioFoot, Stdio.InRange, consoleStdout, consoleBuf]; omega))

theorem ExitIdleFile.of_img {m m' : Mem} {file flags descriptor : Nat}
    (h : ImgOn stdioFoot (memImg m) m') (hf : ExitIdleFile m file flags descriptor)
    (hin : ∀ k, k < 184 → stdioFoot (file + k)) : ExitIdleFile m' file flags descriptor where
  flags_read := readLE_img h 2 _ hf.flags_read fun k hk => by
    have := hin (16 + k) (by omega); rwa [← Nat.add_assoc] at this
  descriptor_read := readLE_img h 2 _ hf.descriptor_read fun k hk => by
    have := hin (18 + k) (by omega); rwa [← Nat.add_assoc] at this
  readCount := readLE_img h 4 _ hf.readCount fun k hk => by
    have := hin (8 + k) (by omega); rwa [← Nat.add_assoc] at this
  savedReadCount := readLE_img h 4 _ hf.savedReadCount fun k hk => by
    have := hin (112 + k) (by omega); rwa [← Nat.add_assoc] at this
  cookie := readLE_img h 8 _ hf.cookie fun k hk => by
    have := hin (48 + k) (by omega); rwa [← Nat.add_assoc] at this
  closeCallback := readLE_img h 8 _ hf.closeCallback fun k hk => by
    have := hin (80 + k) (by omega); rwa [← Nat.add_assoc] at this
  ungetcBuffer := readLE_img h 8 _ hf.ungetcBuffer fun k hk => by
    have := hin (88 + k) (by omega); rwa [← Nat.add_assoc] at this
  lineBuffer := readLE_img h 8 _ hf.lineBuffer fun k hk => by
    have := hin (120 + k) (by omega); rwa [← Nat.add_assoc] at this
  lock := readLE_img h 8 _ hf.lock fun k hk => by
    have := hin (160 + k) (by omega); rwa [← Nat.add_assoc] at this
  lockMode := readLE_img h 4 _ hf.lockMode fun k hk => by
    have := hin (176 + k) (by omega); rwa [← Nat.add_assoc] at this

theorem ConsoleStream.of_img {m m' : Mem} (h : ImgOn stdioFoot (memImg m) m')
    (hc : ConsoleStream m) :
    ConsoleStream m' where
  impure := readLE_img h 8 _ hc.impure (by stdio_in)
  stdout := readLE_img h 8 _ hc.stdout (by stdio_in)
  sinit := readLE_img h 8 _ hc.sinit (by stdio_in)
  cursor := readLE_img h 8 _ hc.cursor (by stdio_in)
  readCount := readLE_img h 4 _ hc.readCount (by stdio_in)
  writeCount := readLE_img h 4 _ hc.writeCount (by stdio_in)
  flags := readLE_img h 2 _ hc.flags (by stdio_in)
  flag0 := byte_of_img h hc.flag0 (by stdio_in_one)
  flag1 := byte_of_img h hc.flag1 (by stdio_in_one)
  fd := readLE_img h 2 _ hc.fd (by stdio_in)
  base := readLE_img h 8 _ hc.base (by stdio_in)
  bufSize := readLE_img h 4 _ hc.bufSize (by stdio_in)
  lineBufSize := readLE_img h 4 _ hc.lineBufSize (by stdio_in)
  cookie := readLE_img h 8 _ hc.cookie (by stdio_in)
  writer := readLE_img h 8 _ hc.writer (by stdio_in)
  lock := readLE_img h 8 _ hc.lock (by stdio_in)
  lockMode := readLE_img h 4 _ hc.lockMode (by stdio_in)
  bufferByte := by
    obtain ⟨b, hb⟩ := hc.bufferByte
    exact ⟨b, byte_of_img h hb (by stdio_in_one)⟩

theorem ExitRuntimeData.of_img {m m' : Mem} (h : ImgOn stdioFoot (memImg m) m')
    (he : ExitRuntimeData m) : ExitRuntimeData m' where
  atexit := readLE_img h 8 _ he.atexit (by stdio_in)
  atexitLock := by
    obtain ⟨w, hw⟩ := he.atexitLock
    exact ⟨w, readLE_img h 8 _ hw (by stdio_in)⟩
  stdioHandler := readLE_img h 8 _ he.stdioHandler (by stdio_in)
  glueNext := readLE_img h 8 _ he.glueNext (by stdio_in)
  glueCount := readLE_img h 4 _ he.glueCount (by stdio_in)
  glueFiles := readLE_img h 8 _ he.glueFiles (by stdio_in)
  stdin := ExitIdleFile.of_img h he.stdin (by stdio_in)
  stderr := ExitIdleFile.of_img h he.stderr (by stdio_in)
  stdoutClose := readLE_img h 8 _ he.stdoutClose (by stdio_in)
  stdoutUngetc := readLE_img h 8 _ he.stdoutUngetc (by stdio_in)
  stdoutLine := readLE_img h 8 _ he.stdoutLine (by stdio_in)

theorem LocaleData.of_img {m m' : Mem} (h : ImgOn stdioFoot (memImg m) m')
    (hl : LocaleData m) : LocaleData m' where
  mbtowc := readLE_img h 8 _ hl.mbtowc (by stdio_in_locale)
  mbMax := readLE_img h 1 _ hl.mbMax (by stdio_in_locale)
  decPoint := readLE_img h 8 _ hl.decPoint (by stdio_in_locale)

/-- **newlib's data at the boundary**: the memory's own image satisfies
`StdioOK`. The `stderr` pointer is the one fact the boundary does not state
(INTERP_DESIGN.md Q6); `BootGap.stderr` carries it. -/
theorem stdioOK_of_mem {m : Mem} (hc : ConsoleStream m) (he : ExitRuntimeData m)
    (hs : read64 m stderrPtrAddr = some exitStderr) (hl : LocaleData m) :
    StdioOK (memImg m) := by
  intro m' h
  exact ⟨ConsoleStream.of_img h hc, ExitRuntimeData.of_img h he,
    readLE_img h 8 _ hs (by stdio_in), LocaleData.of_img h hl⟩

end VsaIris.Interp
