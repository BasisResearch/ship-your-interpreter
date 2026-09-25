import VsaIris.Vsa.StdioErr
import VsaIris.Interp.Repr

/-!
# The data after one `stderr` write is `StdioErrOK` (lane N3)

`stdioErrOK_of_write`: if newlib's data started at a `StdioOK` image `img`,
and a run changed only `stderr`'s written fields (`errWritten`: `_p`, `_r`,
`_w`, the flags, `_bf`, `_flags2`) to a written unbuffered stream's
(`_p = _bf._base = stderr + 119`, flags `0x201a`, `_flags2 = 0`), the final
image `img'` satisfies `StdioErrOK`. Every other field `exit`'s close path
reads is `img`'s (`field_keep`).
-/

namespace VsaIris.Stdio

open Vsa.MemRepr Vsa.Sim VsaIris.Interp

/-- The bytes of `stderr`'s `FILE` a first write changes: `_p`, `_r`, `_w`,
the flags (`[0, 18)`), `_bf` (`[24, 36)`), `_flags2` (`[176, 180)`). -/
def errWritten (a : Nat) : Prop :=
  (0x8001bbd8 ≤ a ∧ a < 0x8001bbd8 + 18) ∨ (0x8001bbd8 + 24 ≤ a ∧ a < 0x8001bbd8 + 36) ∨
    (0x8001bbd8 + 176 ≤ a ∧ a < 0x8001bbd8 + 180)

section

variable {img img' : Nat → BitVec 8} {m : Mem}

/-- A field outside the written bytes reads as at the start. -/
theorem field_keep (hm : ∀ a, stdioFoot a → m[a]? = some (img' a))
    (hfr : ∀ a, stdioFoot a → ¬ errWritten a → img' a = img a) {a n v : Nat}
    (h0 : readLE (fillMem img dataList) a n = some v)
    (hin : ∀ k, k < n → stdioFoot (a + k) ∧ ¬ errWritten (a + k)) : readLE m a n = some v := by
  rw [readLE_of_img (img := img') (fun i hi => hm _ (hin i hi).1)]
  congr 1
  rw [← readLE_memImg h0]
  refine imgLE_congr fun i hi => ?_
  rw [hfr _ (hin i hi).1 (hin i hi).2]
  unfold memImg
  rw [fillMem_get img (mem_dataList (hin i hi).1)]
  rfl

/-- A written field reads as the final image says. -/
theorem field_new (hm : ∀ a, stdioFoot a → m[a]? = some (img' a)) {a n v : Nat}
    (hv : imgLE img' a n = v) (hin : ∀ k, k < n → stdioFoot (a + k)) : readLE m a n = some v := by
  rw [readLE_of_img (img := img') (fun i hi => hm _ (hin i hi)), hv]

end

/-- The byte ranges of the fields: in `stdioFoot`, outside the written bytes. -/
macro "field_in" : tactic => `(tactic| (intro k hk; simp only [stdioFoot, InRange, errWritten,
  consoleImpurePtrAddr, consoleReent, consoleStdout, consoleBuf, exitAtexitAddr, exitAtexitLockAddr,
  exitStdioHandlerAddr, exitGlueAddr, exitStdin, exitStderr, stderrPtrAddr] at *; omega))

/-- **After one write to `stderr`**, newlib's data is `StdioErrOK`. -/
theorem stdioErrOK_of_writeAt {o : Bool} {img img' : Nat → BitVec 8} (h : StdioOKAt o img)
    (hfr : ∀ a, stdioFoot a → ¬ errWritten a → img' a = img a)
    (hcur : imgLE img' 0x8001bbd8 8 = 0x8001bc4f) (hfl : imgLE img' 0x8001bbe8 2 = 0x201a)
    (hbase : imgLE img' 0x8001bbf0 8 = 0x8001bc4f) (hlm : imgLE img' 0x8001bc88 4 = 0) :
    StdioErrOKAt o img' := by
  intro m hm
  obtain ⟨hc, he, hs, _, _⟩ := h.facts
  have K := fun {a n v : Nat} (h0 : readLE (fillMem img dataList) a n = some v)
    (hin : ∀ k, k < n → stdioFoot (a + k) ∧ ¬ errWritten (a + k)) => field_keep hm hfr h0 hin
  have B : ∀ a, stdioFoot a → ¬ errWritten a → m[a]? = (fillMem img dataList)[a]? := fun a h1 h2 => by
    rw [hm a h1, hfr a h1 h2, fillMem_get img (mem_dataList h1)]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  -- ConsoleStream
  · exact K hc.impure (by field_in)
  · exact K hc.stdout (by field_in)
  · exact K hc.sinit (by field_in)
  · exact K hc.cursor (by field_in)
  · exact K hc.readCount (by field_in)
  · exact K hc.writeCount (by field_in)
  · exact K hc.flags (by field_in)
  · rw [B _ (by unfold stdioFoot InRange consoleStdout; omega)
      (by unfold errWritten consoleStdout; omega)]; exact hc.flag0
  · rw [B _ (by unfold stdioFoot InRange consoleStdout; omega)
      (by unfold errWritten consoleStdout; omega)]; exact hc.flag1
  · exact K hc.fd (by field_in)
  · exact K hc.base (by field_in)
  · exact K hc.bufSize (by field_in)
  · exact K hc.lineBufSize (by field_in)
  · exact K hc.cookie (by field_in)
  · exact K hc.writer (by field_in)
  · exact K hc.lock (by field_in)
  · exact K hc.lockMode (by field_in)
  · obtain ⟨b, hb⟩ := hc.bufferByte
    exact ⟨b, by rw [B _ (by unfold stdioFoot InRange consoleBuf; omega)
      (by unfold errWritten consoleBuf; omega)]; exact hb⟩
  -- the rest of `CloseCommon`
  · exact K he.atexit (by field_in)
  · exact K he.stdioHandler (by field_in)
  · exact K he.glueNext (by field_in)
  · exact K he.glueCount (by field_in)
  · exact K he.glueFiles (by field_in)
  · exact K he.stdin.flags_read (by field_in)
  · exact K he.stdin.descriptor_read (by field_in)
  · exact K he.stdin.readCount (by field_in)
  · exact K he.stdin.savedReadCount (by field_in)
  · exact K he.stdin.cookie (by field_in)
  · exact K he.stdin.closeCallback (by field_in)
  · exact K he.stdin.ungetcBuffer (by field_in)
  · exact K he.stdin.lineBuffer (by field_in)
  · exact K he.stdin.lock (by field_in)
  · exact K he.stdin.lockMode (by field_in)
  · exact K he.stdoutClose (by field_in)
  · exact K he.stdoutUngetc (by field_in)
  · exact K he.stdoutLine (by field_in)
  -- `stderr`, written
  · exact field_new hm hfl (by field_in)
  · exact K he.stderr.descriptor_read (by field_in)
  · exact field_new hm hcur (by field_in)
  · exact field_new hm hbase (by field_in)
  · exact K he.stderr.cookie (by field_in)
  · exact K he.stderr.closeCallback (by field_in)
  · exact K he.stderr.ungetcBuffer (by field_in)
  · exact K he.stderr.lineBuffer (by field_in)
  · exact K he.stderr.lock (by field_in)
  · exact field_new hm hlm (by field_in)
  -- `_impure_data._stderr`
  · exact K hs (by field_in)

/-- **After one write to `stderr`**, at either `stdout` orientation. -/
theorem stdioErrOK_of_write {img img' : Nat → BitVec 8} (h : StdioOK img)
    (hfr : ∀ a, stdioFoot a → ¬ errWritten a → img' a = img a)
    (hcur : imgLE img' 0x8001bbd8 8 = 0x8001bc4f) (hfl : imgLE img' 0x8001bbe8 2 = 0x201a)
    (hbase : imgLE img' 0x8001bbf0 8 = 0x8001bc4f) (hlm : imgLE img' 0x8001bc88 4 = 0) :
    StdioErrOK img' :=
  let ⟨o, h⟩ := h
  ⟨o, stdioErrOK_of_writeAt h hfr hcur hfl hbase hlm⟩

end VsaIris.Stdio
