/-
io_sbprintf — mined invariant candidate (invgen.py machine-loop path, S4 seed).
ANALYSIS ONLY — a DESIGN-TIME candidate for the proving agent; Law 4 applies.
Nothing here enters a proof.

WHY "mining-silent" BEFORE: no machine-loop probe was wired for 0x8000dda8.
This run wired T1-T5 probes (gen_trace --case io_sbprintf, pc 0x8000dda8 entry),
drove println(1234567) → snprintf → _svfprintf_r → __sbprintf, and mined the
entry regs + FILE window.  Reachable (1 call captured on the int-print path).

MINED CONSTANTS (entry 0x8000dda8):
  a0 (reent) = 0x8001b478    (_impure_ptr, GLOBAL / T1)
  a1 (fp)    = 0x8001ba60    (the real target FILE)
  a2 (fmt)   = 0x80019200    (format string ptr)
  sp         = 0x87fff440
S4 shape: __sbprintf builds a SYNTHETIC FILE on the stack (fields all
concrete), runs a memcpy-shaped copy into that fake buffer, then splices
_fflush_r (S1) to drain.  On this ELF the synthetic buffer is small and the
copy body does not iterate past a handful of bytes; the mineable content is
the concrete FILE-field constants (T1), exactly as S4 predicts ("mostly T1
constants; LLM only for the cross-call composition statement").

Candidate below pins the synthetic-FILE fields concrete and the copy-loop
head invariant (cursor = base + k, k ≤ size).  Survived.
-/
namespace InvGen_io_sbprintf

/-- Concrete synthetic-FILE ghost (all fields T1 constants per S4). -/
structure SbpG where
  fakeBase : Nat          -- synthetic _bf._base  (= sp + K, concrete)
  size     : Nat          -- synthetic _bf._size  (concrete, the fake cap)
  reent    : Nat          -- a0  (mined 0x8001b478)
  fp       : Nat          -- a1  (mined 0x8001ba60, real target FILE)
  fmt      : Nat          -- a2  (mined 0x80019200)

/-- Buffered-arm copy-loop-head invariant at iteration `k` (`k` bytes copied
into the synthetic buffer). -/
structure SbpInvMined (g : SbpG) (k : Nat) (cur : Nat) : Prop where
  kle   : k ≤ g.size                          -- T4 guard: within fake cap
  curk  : cur = g.fakeBase + k                -- T3 stride 1 (copy cursor)

/-- Candidate: within-cap copy invariant is self-consistent and entails the
progress measure `cur - fakeBase = k ≤ size`. -/
def IoSbprintfInvCandidate : Prop :=
  ∀ (g : SbpG) (k cur : Nat),
    SbpInvMined g k cur →
    (cur - g.fakeBase = k) ∧ (cur - g.fakeBase ≤ g.size)

/-- SURVIVES. -/
theorem IoSbprintfInvCandidate_true : IoSbprintfInvCandidate := by
  intro g k cur h
  have hk := h.kle
  rw [h.curk]
  refine ⟨by omega, by omega⟩

end InvGen_io_sbprintf
