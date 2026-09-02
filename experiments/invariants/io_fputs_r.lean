/-
io_fputs_r — mined invariant candidate (invgen.py machine-loop path, S5 seed).
ANALYSIS ONLY — a DESIGN-TIME candidate for the proving agent; Law 4 applies.
Nothing here enters a proof.

WHY "mining-silent" BEFORE: no machine-loop probe was wired for 0x800063b8.
This run wired T1-T5 probes (gen_trace --case io_fputs_r, pc 0x800063b8),
drove the print chain, and confirmed reachability (2 calls) + mined the entry
iov/uio setup regs.

MINED CONSTANTS (entry 0x800063b8):
  a0 (reent) = 0x8001b478    (_impure_ptr, GLOBAL / T1)
  a1 (buf)   = 0x8001c3e0    (source string base; window read back the string
                              bytes 0x4847464544434241 = "ABCDEFGH" — confirms
                              a1 = the payload pointer)
  a2 (fp)    = 0x8001ba60    (the target FILE)

S5 shape: fputs_r is a WRAPPER SHELL — newlib delegates to __sfvwrite_r (whose
unbuffered arm is LANDED as sfvwrite_unbuf_summary).  No loop of its own; the
mineable content is the uio/iov setup post:
  iov.base = buf,  iov.len = strlen(buf),  uio fields at sp-slots (T5 window),
then the sfvwrite_unbuf_summary splice: out' = out0 ++ buf[0, n).
Candidate states the iov-setup well-formedness (base = buf, len ≥ 0, out grows
by exactly the iov span).  Survived.
-/
namespace InvGen_io_fputs_r

/-- iov/uio setup ghost (S5). -/
structure FputsG where
  buf    : Nat            -- a1 (mined 0x8001c3e0)
  n      : Nat            -- strlen(buf), the iov length
  fp     : Nat            -- a2 (mined 0x8001ba60)
  reent  : Nat            -- a0 (mined 0x8001b478)
  outLen : Nat            -- console bytes before this call

/-- Post of the wrapper: one iov spanning [buf, buf+n), then the unbuffered
sfvwrite splice grows out by exactly n bytes. -/
structure FputsPostMined (g : FputsG) (iovBase iovLen outLen' : Nat) : Prop where
  ibase  : iovBase = g.buf                     -- iov.base = buf
  ilen   : iovLen = g.n                        -- iov.len  = strlen(buf)
  outg   : outLen' = g.outLen + g.n            -- out grows by n (unbuf splice)

/-- Candidate: the iov setup is consistent and the out-growth equals the iov
span (the WRGOk-mirror frame post). -/
def IoFputsRInvCandidate : Prop :=
  ∀ (g : FputsG) (iovBase iovLen outLen' : Nat),
    FputsPostMined g iovBase iovLen outLen' →
    (iovBase = g.buf) ∧ (outLen' - g.outLen = iovLen)

/-- SURVIVES. -/
theorem IoFputsRInvCandidate_true : IoFputsRInvCandidate := by
  intro g iovBase iovLen outLen' h
  refine ⟨h.ibase, ?_⟩
  rw [h.outg, h.ilen]; omega

end InvGen_io_fputs_r
