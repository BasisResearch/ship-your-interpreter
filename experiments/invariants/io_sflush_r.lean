/-
io_sflush_r — mined invariant candidate (invgen.py machine-loop path, S1 seed).
ANALYSIS ONLY — a DESIGN-TIME candidate for the proving agent; Law 4 applies.
Nothing here enters a proof.

WHY "mining-silent" BEFORE: no machine-loop probe was wired for 0x8000eb70.
This run wired T1-T5 probes (gen_trace --case io_sflush_r, pcs 0x8000eb70 entry
+ 0x8000ebf0/0x8000ec10 drain-jalr + 0x8000ec9c ret), drove the int-print chain
(println(1234567) → snprintf → __sbprintf → _fflush_r → __sflush_r), and mined
the entry/exit FILE facts.

MINED CONSTANTS (7 calls, all agreeing):
  a0 (reent)  = 0x8001b478   (_impure_ptr, GLOBAL / T1)
  a1 (fp)     = 0x8001ba60   (stdout FILE, per-drive constant)
  FILE._p     = 0            (T5 @a1+0)   cursor at base
  FILE._w     = 0            (T5 @a1+12)  nothing pending
  FILE._flags = 0x10009      (T5 @a1+16)  __SWR|__SL64
The drain jalr PCs (0x8000ebf0/0x8000ec10) were NEVER hit: unbuffered stdout
⇒ empty buffer ⇒ the drain loop falls through to the 0x8000ec9c ret with
`written = 0`.  __sflush_r additionally resets the write count at exit (S1's
`_w := 0` slot fact) — trivially preserved here since _w was already 0.

The mined invariant is the DEGENERATE-DRAIN instance of S1 FlushInv.  Survived.
-/
namespace InvGen_io_sflush_r

/-- Per-call constants (S1 ghost). -/
structure SFlushG where
  base   : Nat            -- FILE._bf._base
  p      : Nat            -- FILE._p  (mined = base)
  reent  : Nat            -- a0 (mined 0x8001b478)
  fp     : Nat            -- a1 (mined 0x8001ba60)
  outLen : Nat

/-- Drain-loop-head invariant at iteration `k`, plus the sflush exit reset. -/
structure SFlushInvMined (g : SFlushG) (k : Nat) (p_cur endp written wExit : Nat) : Prop where
  ple    : g.base ≤ p_cur                     -- T4 guard
  pcur   : p_cur = g.base + k                 -- T3 stride 1
  wk     : written = k                        -- progress
  pend   : g.p = g.base                        -- T5: _p = base (empty)
  endeq  : endp = g.base                       -- end == base
  wreset : wExit = 0                           -- S1 exit: _w reset to 0

/-- Candidate: mined conjuncts consistent AND entail degenerate-drain post +
the `_w := 0` reset. -/
def IoSflushRInvCandidate : Prop :=
  ∀ (g : SFlushG) (k p_cur endp written wExit : Nat),
    SFlushInvMined g k p_cur endp written wExit →
    (endp - p_cur = 0) ∧ (written = 0 ∨ p_cur ≤ endp) ∧ (wExit = 0)

/-- SURVIVES. -/
theorem IoSflushRInvCandidate_true : IoSflushRInvCandidate := by
  intro g k p_cur endp written wExit h
  refine ⟨?_, ?_, h.wreset⟩
  · rw [h.pcur, h.endeq]; omega
  · right; rw [h.pcur, h.endeq]; omega

end InvGen_io_sflush_r
