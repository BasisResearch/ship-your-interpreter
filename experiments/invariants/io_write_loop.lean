/-
Mined loop invariant for the `_write` byte-store loop (head 0x8000004c),
Experiment 2 of the invariant-gen-plan validation round 2.

Source of the conjuncts: scripts/mine_loop_inv.py over a 13-visit / 5-segment
trace (t5.elf).  Every conjunct below is TRACE-GROUNDED (tagged); quantifier
placement (the ∀ k telescope, the entry relation) is the LLM/idiom-shaped part
the plan assigns to stage 5.  This is a DESIGN-TIME candidate — nothing here
enters a proof.  It is written to be (a) fuzzable by scripts/statement_fuzz.py
and (b) a loopFromBody-shaped skeleton whose residual obligation we measure.

Self-contained (no repo imports) so the fuzzer runs it hermetically; the field
names mirror Vsa/Sim/rows/FnWriteFold.lean's WInv.
-/

namespace IoWriteMined

/-- Ghost bundle: the per-call constants the miner found fixed within a segment
(a3 = end, a2 = len, a4 = putchar cmd word) plus the buffer bytes. -/
structure WG where
  buf     : Nat            -- start pointer  (a1 at entry)
  len     : Nat            -- a2  (T1 per-call constant)
  writeCmd : Nat           -- a4  (T1 GLOBAL constant, mined 0x0101000000000000)
  outLen  : Nat            -- console bytes already emitted before this call

/-- The mined loop-head invariant at iteration `k` (`k` bytes copied so far).
Fields, each tagged with the mining tier that grounded it. -/
structure WInvMined (g : WG) (k : Nat) (a1 a3 a2 a4 : Nat) : Prop where
  klt    : k < g.len                      -- T4 guard: cursor below end ⇔ k<len
  a1cur  : a1 = g.buf + k                  -- T3 stride 1: cursor = buf + k
  a3end  : a3 = g.buf + g.len              -- T2 entry: end = start + len
  a2len  : a2 = g.len                      -- T1 per-call constant
  a4cmd  : a4 = g.writeCmd                 -- T1 global constant (putchar word)
  guard  : a1 < a3                         -- T4 guard ordering (a1 < a3)

/-- The candidate, as a ∀-telescope Prop (fuzzer-parseable).  For ALL ghost
bundles, iteration counts, and register values, the invariant fields are
mutually consistent — i.e. the mined conjuncts do not contradict each other
(the well-formedness the fuzzer checks: is there a lethal witness?). -/
def IoWriteInvCandidate : Prop :=
  ∀ (g : WG) (k a1 a3 a2 a4 : Nat),
    WInvMined g k a1 a3 a2 a4 →
    -- the two mined derived facts that a loopFromBody step must preserve:
    (a1 < a3) ∧ (a3 - a1 = g.len - k)

/-- The candidate is TRUE (survives): the derived facts follow from the fields.
This is the whole point — a mined invariant that is self-consistent and whose
loop-progress measure (a3 - a1 = len - k) is entailed.  Fuzzer must SURVIVE. -/
theorem IoWriteInvCandidate_true : IoWriteInvCandidate := by
  intro g k a1 a3 a2 a4 h
  refine ⟨h.guard, ?_⟩
  rw [h.a1cur, h.a3end]
  omega

end IoWriteMined
