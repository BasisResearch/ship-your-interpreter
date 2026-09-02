/-
io_fflush_r — mined invariant candidate (invgen.py machine-loop path, S1 seed).
ANALYSIS ONLY — a DESIGN-TIME candidate for the proving agent; Law 4 applies.
Nothing here enters a proof.

WHY THIS WAS "mining-silent" BEFORE: invgen wired no machine-loop probe for
0x8000edcc, so the relational kind-seam path (its only wired path) found no
agreeing bridge and reported silent.  This run wired the T1-T5 machine probes
(scripts/gen_trace.py --case io_fflush_r, pc 0x8000edcc + drain-loop body),
drove the whole print chain (println(1234567) → snprintf → vfprintf →
__sbprintf → _fflush_r), and mined the entry/exit FILE-struct facts.

MINED CONSTANTS (int-print drive, 4 calls, all agreeing / T1):
  a0 (reent)  = 0x8001b478   (_impure_ptr, GLOBAL across every call)
  a1 (fp)     = 0x8001ba60   (the stdout FILE)
  FILE._p     = 0            (T5 window @a1+0)   ← buffer cursor
  FILE._w     = 0            (T5 window @a1+12)  ← nothing pending
  FILE._flags = 0x10009      (T5 window @a1+16)  ← __SWR|__SL64 path
The drain loop (0x8000ebf0/0x8000ec10 jalr _swrite) NEVER ITERATES on this
ELF: stdout is unbuffered (main.c setvbuf _IONBF) so `_p = _bf._base` at flush
time ⇒ `written = 0`, `out` unchanged.  The mined invariant is therefore the
DEGENERATE-DRAIN instance of the S1 FlushInv seed.  A real, survived fact —
not a loop stride, because the loop body is dead on the traced program.

Self-contained (fuzzable hermetically); fields mirror the S1 seed / WInv idiom.
-/
namespace InvGen_io_fflush_r

/-- Per-call constants the miner found fixed within a flush call (S1 ghost). -/
structure FlushG where
  base   : Nat            -- FILE._bf._base  (== _p at entry ⇒ empty)
  p      : Nat            -- FILE._p         (cursor; mined = base)
  reent  : Nat            -- a0  (mined 0x8001b478, GLOBAL)
  fp     : Nat            -- a1  (mined 0x8001ba60)
  outLen : Nat            -- console bytes emitted before this flush

/-- The mined flush-loop-head invariant at iteration `k` (`k` bytes drained).
For the traced program the guard `p < end` is false from the start
(base = end), so the head is entered with k = 0. -/
structure FlushInvMined (g : FlushG) (k : Nat) (p_cur endp written : Nat) : Prop where
  ple    : g.base ≤ p_cur                     -- T4 guard: cursor ≥ base
  pcur   : p_cur = g.base + k                 -- T3 stride 1 (drained-so-far)
  wk     : written = k                        -- progress = bytes drained
  pend   : g.p = g.base                        -- T5 mined: _p = base (empty buf)
  endeq  : endp = g.base                       -- end == base ⇒ nothing to drain

/-- Candidate as a ∀-telescope Prop: the mined conjuncts are mutually
consistent AND entail the degenerate-drain post — zero bytes drained. -/
def IoFflushRInvCandidate : Prop :=
  ∀ (g : FlushG) (k p_cur endp written : Nat),
    FlushInvMined g k p_cur endp written →
    (endp - p_cur = 0) ∧ (endp = g.base) ∧ (g.p = g.base)

/-- The candidate SURVIVES: the degenerate-drain facts follow from the fields. -/
theorem IoFflushRInvCandidate_true : IoFflushRInvCandidate := by
  intro g k p_cur endp written h
  refine ⟨?_, h.endeq, h.pend⟩
  rw [h.pcur, h.endeq]
  omega

end InvGen_io_fflush_r

-- axiom check (design-time; not part of the candidate)
-- #print axioms InvGen_io_fflush_r.IoFflushRInvCandidate_true
