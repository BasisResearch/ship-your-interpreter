/-
io_vfprintf_r — mined invariant candidate (invgen.py machine-loop path, S3 seed).
ANALYSIS ONLY — a DESIGN-TIME candidate for the proving agent; Law 4 applies.
Nothing here enters a proof.

WHY "mining-silent" BEFORE: no machine-loop probe was wired for 0x8000a884.
This run wired T1-T5 probes (gen_trace --case io_vfprintf_r, pc 0x8000a884),
drove println(1234567) → _svfprintf_r → _vfprintf_r, confirming reachability
(1 call captured) and mining the entry frame.

MINED CONSTANTS (entry 0x8000a884):
  a0 (reent) = 0x8001b478    (_impure_ptr, GLOBAL / T1)
  a1 (fp)    = 0x87ffef68    (the on-stack synthetic sprint FILE)
  a2 (fmt)   = 0x80019200    (format string ptr)
  FILE._flags= 0x12008       (T5 @a1+16)  __SWR|__SSTR
  sp         = 0x87ffef50

S3 shape: two fmt loops.
 (1) %lld digit loop = SAME SHAPE as the LANDED `decimalLoop_spec`
     (SnprintfSpec3): cursor decrements from buf+len, val' = val/10,
     digit = val%10 stored at cursor.  Seeded verbatim below (val_k =
     remaining value, k digits emitted).
 (2) %s copy loop = byte-copy = memcpy iterW precedent (MemcpySpec2):
     copied prefix = source prefix, cursor pair advances in lock-step,
     NUL check as guard.
On the int-print drive only the %lld path is exercised (the digit loop is the
landed one); this candidate re-states its head invariant in the hermetic idiom
so the fuzzer can confirm self-consistency independent of the landed proof.
-/
namespace InvGen_io_vfprintf_r

/-- %lld digit-loop ghost (mirrors decimalLoop_spec). -/
structure VfDigG where
  buf   : Nat            -- destination buffer base
  len   : Nat            -- total digits to emit
  val0  : Nat            -- initial magnitude

/-- Digit-loop-head invariant after `k` digits emitted. -/
structure VfDigInvMined (g : VfDigG) (k : Nat) (cursor val_k : Nat) : Prop where
  kle    : k ≤ g.len                          -- T4 guard: digits ≤ len
  curk   : cursor = g.buf + g.len - k         -- T3 stride -1: cursor decrements
  -- val decays by /10 each step: after k steps, val_k = val0 / 10^k.  We keep
  -- the weaker monotone fact the miner can ground (val_k ≤ val0) as the
  -- loop-preserved measure; the exact /10 law is decimalLoop_spec's business.
  valmono : val_k ≤ g.val0                     -- T4 monotone: magnitude shrinks

/-- Candidate: the digit-loop head facts are self-consistent and entail the
progress measure (cursor within [buf, buf+len], magnitude non-increasing). -/
def IoVfprintfRInvCandidate : Prop :=
  ∀ (g : VfDigG) (k cursor val_k : Nat),
    VfDigInvMined g k cursor val_k →
    (g.buf ≤ cursor) ∧ (cursor ≤ g.buf + g.len) ∧ (val_k ≤ g.val0)

/-- SURVIVES. -/
theorem IoVfprintfRInvCandidate_true : IoVfprintfRInvCandidate := by
  intro g k cursor val_k h
  have hk := h.kle
  refine ⟨?_, ?_, h.valmono⟩
  · rw [h.curk]; omega
  · rw [h.curk]; omega

end InvGen_io_vfprintf_r
