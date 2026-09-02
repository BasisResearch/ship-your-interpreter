-- crux_relations.lean — mined hCallClosure depth/budget invariant candidates
-- (invgen depth-descent extension, ANALYSIS ONLY — DRAFTs for the proving agent;
-- Law 4 applies).  cluster env-seam  target TermResidualsCore.hCallClosure.
--
-- Constants mined from /tmp/rl-trace/cruxDepth_trace.jsonl (clo_depth.wl, closure
-- calls at depth 0..4).  Frame constants match Vsa/While/StackNeed.lean:
--   evalFrame 1088, execFrame 176, perCallBudget 6144, maxCallDepth 1000.
namespace InvGen_cruxRelations

def evalFrame : Nat := 1088          -- StackNeed.evalFrame
def execFrame : Nat := 176           -- StackNeed.execFrame
def perCallBudget : Nat := 6144      -- StackNeed.perCallBudget
def maxCallDepth : Nat := 1000       -- crux a_3 bound

-- ── R1/R2: per-closure-call frame consumption ─────────────────────────────
-- Mined per-descent sp deltas on the pure recursion ladder = 1264 constant
-- (= evalFrame + execFrame).  On nested-closure descents = 2352 (= 2*evalFrame
-- + execFrame).  BOTH must fit one call level's perCallBudget.

/-- One closure call's frame consumption (eval arm frame + body prologue frames)
    fits the uniform per-call budget.  This is the StackNeed.perCallBudget
    soundness obligation, grounded on the mined maxima. -/
structure PerCallBudgetOK (delta : Nat) : Prop where
  fits    : delta ≤ perCallBudget
  atleast : evalFrame ≤ delta            -- every call commits ≥ one eval frame

def minedRecurDelta : Nat := 1264        -- evalFrame + execFrame (clean ladder)
def minedNestDelta  : Nat := 2352        -- 2*evalFrame + execFrame (compose/apply)
def minedRecur : Prop := PerCallBudgetOK minedRecurDelta
def minedNest  : Prop := PerCallBudgetOK minedNestDelta
-- mutant: a call consuming MORE than the budget (an unsound perCallBudget).
def budgetMutant : Prop := PerCallBudgetOK (perCallBudget + 8)

-- ── R4: the depth ladder is NOT a constant (falsity #13 form) ─────────────
-- Demand at depth d = d * perLevel + base; a constant budget C is refuted the
-- moment the demand at a reachable depth exceeds C.  The mined per-level slope
-- (least squares) ≈ 1208; the clean recursion per-level = 1264.  We use 1264.

/-- The recursion-sound budget is a LADDER: the whole call chain at depth d
    demands d closure-call frames, bounded by the maxCallDepth * perCallBudget
    linker-stack reservation.  The constant-budget form (a fixed `budget` field
    independent of d) is REFUTED — the mutant asserts a constant covers all d. -/
structure DepthLadderOK (perLevel base : Nat) : Prop where
  /-- one call level of the ladder costs ≤ perCallBudget (ladder step sound). -/
  step  : perLevel ≤ perCallBudget
  /-- the whole ladder to maxCallDepth fits the reserved stack window
      (maxCallDepth * perCallBudget ≤ 8 MiB linker stack; here checked as the
      ladder-vs-reservation inequality). -/
  total : maxCallDepth * perLevel + base ≤ maxCallDepth * perCallBudget

def minedPerLevel : Nat := 1264
def minedBase : Nat := 1175              -- least-squares intercept (rounded)
def minedLadder : Prop := DepthLadderOK minedPerLevel minedBase
-- mutant (the OLD unsound shape): a constant "budget" that a depth-1 demand
-- (2208) already exceeds — modeled as claiming the whole ladder fits a per-level
-- cost of ZERO (constant budget, no growth), which fails `total`'s growth need.
def constMutant : Prop := DepthLadderOK 0 (maxCallDepth * perCallBudget + 8)

-- ── R6: one env_new (fresh frame) per closure call ────────────────────────
/-- Each closure call allocates exactly one fresh frame (env_new).  Mined:
    env_new calls == depth events (14 == 14).  The frame-count grows by one per
    call level — the φ-growth the crux's `PhiExtends φf φf' frames.size` states. -/
structure FrameGrowthOK (envNewCalls depthEvents : Nat) : Prop where
  oneperCall : envNewCalls = depthEvents

def minedFrameGrowth : Prop := FrameGrowthOK 14 14
def frameMutant : Prop := FrameGrowthOK 13 14

end InvGen_cruxRelations
