/-
io_swbuf_r — mined invariant candidate (invgen.py machine-loop path, S2 seed).
ANALYSIS ONLY — a DESIGN-TIME candidate for the proving agent; Law 4 applies.
Nothing here enters a proof.

WHY "mining-silent" BEFORE: no machine-loop probe was wired for 0x8000f0c8.
This run wired T1-T5 probes (gen_trace --case io_swbuf_r, pc 0x8000f0c8 entry
+ 0x8000f108/0x8000f118/0x8000f170 body), drove a long buffered print
(io_drive2.wl), and mined the per-call byte-put facts.  Reachable: 6 calls.

MINED CONSTANTS (6 calls, body @0x8000f108):
  a1 (c)    = 0xa            (the byte being buffered — '\n' here; per-call)
  a2 (fp)   = 0x8001ba60     (stdout FILE, GLOBAL across calls / T1)
  a4 (_p)   = 0x8001bad7     (buffer cursor, the store address)
  sp        = 0x87fff6b0     (frame constant / T1)

S2 shape: __swbuf_r is a SINGLE-BYTE put (NO loop of its own) — it stores one
byte `c` at the cursor `_p`, advances `_p` by 1, decrements `_w`, and on a full
buffer splices _fflush_r (S1).  The mined facts are the straight-span
byte-store post: `_p' = _p + 1`, byte stored = `c & 0xff`, out grows by that
byte only when unbuffered/flushed.  These are gen_fn folds, not a loop stride;
the candidate states the single-step post as the fuzzable well-formedness.
-/
namespace InvGen_io_swbuf_r

/-- Per-call constants (S2 ghost). -/
structure SwbufG where
  c      : Nat            -- a1, the byte (mined 0xa on the traced call)
  fp     : Nat            -- a2 (mined 0x8001ba60)
  p      : Nat            -- a4 = FILE._p, store cursor (mined 0x8001bad7)
  w      : Nat            -- FILE._w before the put

/-- Single-byte-put post: cursor advanced by 1, byte low 8 bits stored,
write-count decremented (guarded, S2). -/
structure SwbufPostMined (g : SwbufG) (pOut wOut stored : Nat) : Prop where
  padv   : pOut = g.p + 1                      -- T3: _p advances by exactly 1
  wdec   : wOut + 1 = g.w ∨ g.w = 0            -- _w decrement (or already 0)
  byte   : stored = g.c % 256                  -- byte stored = c & 0xff

/-- Candidate: the single-step put post is self-consistent — cursor strictly
advances and the stored byte is a valid byte (< 256). -/
def IoSwbufRInvCandidate : Prop :=
  ∀ (g : SwbufG) (pOut wOut stored : Nat),
    SwbufPostMined g pOut wOut stored →
    (pOut = g.p + 1) ∧ (g.p < pOut) ∧ (stored < 256)

/-- SURVIVES. -/
theorem IoSwbufRInvCandidate_true : IoSwbufRInvCandidate := by
  intro g pOut wOut stored h
  refine ⟨h.padv, ?_, ?_⟩
  · rw [h.padv]; omega
  · rw [h.byte]; omega

end InvGen_io_swbuf_r
