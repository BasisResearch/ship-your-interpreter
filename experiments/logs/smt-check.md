
## smt_check.py run

- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615}

## smt_check.py run


## smt_check.py run

- `SmtAcc.BinArmMemExt` → **ENCODE-GAP** (unencodable atom; hyps=['(forall ((m_def (Array Int Bool)) (m_val (Array Int (_ BitVec 8)))) (forall ((a Int)) (=> (not (and (<= SL_lo a) (< a sp_n))) (and (= (select m_def a) (select m0_def a)) (= (select m_val a) (select m0_val a))))))'] concl=None)

## smt_check.py run

- `SmtAcc.BinArmMemExt` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplay.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, SL_lo=0, sp=#xffffffffffffffff)}

## smt_check.py run

- `SmtAcc.BinArmMemExt` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplay.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, SL_lo=0, sp=#xffffffffffffffff)}

## smt_check.py run

- `SmtAcc.BinArmMemExt` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplay.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, SL_lo=0, sp=#xffffffffffffffff)}

## smt_check.py run

- `SmtAcc.BinArmMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=18446744073709551615, SL_lo=0, sp=#xffffffffffffffff)}

## smt_check.py run

- `SmtAcc.McallMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0}

## smt_check.py run

- `SmtAcc.McallPresence` → **ENCODE-GAP** (unencodable atom; hyps=[] concl=None)

## smt_check.py run

- `SmtAcc.McallPresence` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=1022335223146396966, SL_lo=0, sp=#x0e3010780902bd26)}

## smt_check.py run

- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT**

## smt_check.py run

- `IoWriteMined.IoWriteInvCandidate` → **ENCODE-GAP** (unencodable atom; hyps=[None] concl=None)

## smt_check.py run

- `IoWriteMined.IoWriteInvCandidate` → **ENCODE-GAP** (unencodable atom; hyps=[None] concl=None)

## smt_check.py run

- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT**

## smt_check.py run

- `IoWriteMined.IoWriteInvCandidate` → **ENCODE-GAP** (unencodable atom; hyps=[None] concl=(and (< a1 a3) (= (ite (>= a3 a1) (- a3 a1) 0) (ite (>= g_len k) (- g_len k) 0))))

## smt_check.py run

- `IoWriteMined.IoWriteInvCandidate` → **VALID-IN-FRAGMENT**

## smt_check.py run

- `SmtAcc.CurMemExt` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat)

## smt_check.py run

- `SmtAcc.AmdHeadroom` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat)

## smt_check.py run

- `SmtAcc.BudgetLadderOk` → **NON-VACUOUS** — witness {consumed=2752, d=2, perLevel=295, budget=6258, base=2162}

## smt_check.py run

- `SmtAcc.OpaqueMix` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['GoodState']; not auto-replayed | model {SL_hi=0, op_GoodState_SL=false), sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615}

## smt_check.py run


## smt_check.py acceptance run

- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615}
- `SmtAcc.McallMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0}
- `SmtAcc.McallPresence` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=16715942433050673624, SL_lo=0, sp=#xe7faf513f7dd41d8)}
- `SmtAcc.BinArmMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=18446744073709551615, SL_lo=0, sp=#xffffffffffffffff)}
- `IoWriteMined.IoWriteInvCandidate` → **ENCODE-FAIL** (def body not found)
- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT**
- `SmtAcc.CurMemExt` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat)
- `SmtAcc.AmdHeadroom` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat)

### Acceptance verdicts
- a_headroom: REFUTED-REPLAYED
- b_memext: REFUTED-REPLAYED
- b_presence: REFUTED-REPLAYED
- c_binarm: REFUTED-REPLAYED
- d_io_write_loop.lean: ENCODE-FAIL
- d_budget: VALID-IN-FRAGMENT
- e_memext: VALID-IN-FRAGMENT
- e_headroom: VALID-IN-FRAGMENT
- REFUTED-REPLAYED count (need ≥2): 4

**Acceptance → FAIL** (replayed 4/4, need ≥2)

## smt_check.py run


## smt_check.py acceptance run

- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615}
- `SmtAcc.McallMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0}
- `SmtAcc.McallPresence` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=16715942433050673624, SL_lo=0, sp=#xe7faf513f7dd41d8)}
- `SmtAcc.BinArmMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=18446744073709551615, SL_lo=0, sp=#xffffffffffffffff)}
- `IoWriteMined.IoWriteInvCandidate` → **VALID-IN-FRAGMENT**
- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT**
- `SmtAcc.CurMemExt` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat)
- `SmtAcc.AmdHeadroom` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat)

### Acceptance verdicts
- a_headroom: REFUTED-REPLAYED
- b_memext: REFUTED-REPLAYED
- b_presence: REFUTED-REPLAYED
- c_binarm: REFUTED-REPLAYED
- d_io_write_loop.lean: VALID-IN-FRAGMENT
- d_budget: VALID-IN-FRAGMENT
- e_memext: VALID-IN-FRAGMENT
- e_headroom: VALID-IN-FRAGMENT
- REFUTED-REPLAYED count (need ≥2): 4

**Acceptance → PASS** (replayed 4/4, need ≥2)

## smt_check.py run


## smt_check.py acceptance run

- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615}
- `SmtAcc.McallMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0}
- `SmtAcc.McallPresence` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=16715942433050673624, SL_lo=0, sp=#xe7faf513f7dd41d8)}
- `SmtAcc.BinArmMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=18446744073709551615, SL_lo=0, sp=#xffffffffffffffff)}
- `IoWriteMined.IoWriteInvCandidate` → **VALID-IN-FRAGMENT**
- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT**
- `SmtAcc.CurMemExt` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat)
- `SmtAcc.AmdHeadroom` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat)

### Acceptance verdicts
- a_headroom: REFUTED-REPLAYED
- b_memext: REFUTED-REPLAYED
- b_presence: REFUTED-REPLAYED
- c_binarm: REFUTED-REPLAYED
- d_io_write_loop.lean: VALID-IN-FRAGMENT
- d_budget: VALID-IN-FRAGMENT
- e_memext: VALID-IN-FRAGMENT
- e_headroom: VALID-IN-FRAGMENT
- REFUTED-REPLAYED count (need ≥2): 4

**Acceptance → PASS** (replayed 4/4, need ≥2)

## smt_check.py run


## smt_check.py acceptance run

- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615}
- `SmtAcc.McallMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0}
- `SmtAcc.McallPresence` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=16715942433050673624, SL_lo=0, sp=#xe7faf513f7dd41d8)}
- `SmtAcc.BinArmMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=18446744073709551615, SL_lo=0, sp=#xffffffffffffffff)}
- `IoWriteMined.IoWriteInvCandidate` → **VALID-IN-FRAGMENT**
- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT**
- `SmtAcc.CurMemExt` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat)
- `SmtAcc.AmdHeadroom` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat)

### Acceptance verdicts
- a_headroom: REFUTED-REPLAYED
- b_memext: REFUTED-REPLAYED
- b_presence: REFUTED-REPLAYED
- c_binarm: REFUTED-REPLAYED
- d_io_write_loop.lean: VALID-IN-FRAGMENT
- d_budget: VALID-IN-FRAGMENT
- e_memext: VALID-IN-FRAGMENT
- e_headroom: VALID-IN-FRAGMENT
- REFUTED-REPLAYED count (need ≥2): 4

**Acceptance → PASS** (replayed 4/4, need ≥2)

## smt_check.py run

- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615}

## smt_check.py run

- `SmtAcc.AmdHeadroom` → **VALID-IN-FRAGMENT**

## smt_check.py run

- `SmtAcc.BudgetLadderOk` → **NON-VACUOUS** — witness {consumed=2752, d=2, perLevel=295, budget=6258, base=2162}

## smt_check.py run

- `SmtAcc.CurMemExt` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat)

## smt_check.py run


## smt_check.py run

- `NovelResidC` → **ENCODE-GAP** (unencodable atom; hyps=[None] concl=None)

## smt_check.py run


## smt_check.py run


## smt_check.py acceptance run

- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615}
- `SmtAcc.McallMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0}
- `SmtAcc.McallPresence` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=16715942433050673624, SL_lo=0, sp=#xe7faf513f7dd41d8)}
- `SmtAcc.BinArmMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=18446744073709551615, SL_lo=0, sp=#xffffffffffffffff)}
- `IoWriteMined.IoWriteInvCandidate` → **VALID-IN-FRAGMENT**
- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT**
- `SmtAcc.CurMemExt` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat)
- `SmtAcc.AmdHeadroom` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat)

### Acceptance verdicts
- a_headroom: REFUTED-REPLAYED
- b_memext: REFUTED-REPLAYED
- b_presence: REFUTED-REPLAYED
- c_binarm: REFUTED-REPLAYED
- d_io_write_loop.lean: VALID-IN-FRAGMENT
- d_budget: VALID-IN-FRAGMENT
- e_memext: VALID-IN-FRAGMENT
- e_headroom: VALID-IN-FRAGMENT
- REFUTED-REPLAYED count (need ≥2): 4

**Acceptance → PASS** (replayed 4/4, need ≥2)

## smt_check.py run

  (encoder: lean)
- `NovelResidA` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplay.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {base=#x75346575757572ba), base_n=8445486756382732986} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidA` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplay.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {base=#x75346575757572ba), base_n=8445486756382732986} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidB` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidC` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplay.refuted' depends on axioms: [propext, Classical.choice, Quot.sound] | model {m0_val=(lambda ((x!1 Int))} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidA` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {base=#x75346575757572ba), base_n=8445486756382732986} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidC` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidA` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {base=#x75346575757572ba), base_n=8445486756382732986} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidA` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {base=#x75346575757572ba), base_n=8445486756382732986} [enc:lean]

## smt_check.py run


## smt_check.py acceptance run

  (encoder: lean)
- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615} [enc:lean]
  (encoder: lean)
- `SmtAcc.McallMemExt` → **NOT-REFUTED / UNKNOWN** ((error "line 15 column 98: Sorts (_ BitVec 8) and Int are incompatible")) [enc:lean]
  (encoder: lean)
- `SmtAcc.McallPresence` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=136, sp=#x0000000000000088), SL_lo=0} [enc:lean]
  (encoder: lean)
- `SmtAcc.BinArmMemExt` → **NOT-REFUTED / UNKNOWN** ((error "line 15 column 98: Sorts (_ BitVec 8) and Int are incompatible")) [enc:lean]
  (encoder: lean)
- `IoWriteMined.IoWriteInvCandidate` → **REFUTABLE** (negation SAT — not valid) [enc:lean]
  (encoder: lean)
- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT** [enc:lean]
  (encoder: lean)
- `SmtAcc.CurMemExt` → **NOT-REFUTED / UNKNOWN** ((error "line 15 column 98: Sorts (_ BitVec 8) and Int are incompatible")) [enc:lean]
  (encoder: lean)
- `SmtAcc.AmdHeadroom` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

### Acceptance verdicts
- a_headroom: REFUTED-REPLAYED
- b_memext: UNKNOWN
- b_presence: REFUTED-REPLAYED
- c_binarm: UNKNOWN
- d_io_write_loop.lean: REFUTABLE
- d_budget: VALID-IN-FRAGMENT
- e_memext: UNKNOWN
- e_headroom: VALID-IN-FRAGMENT
- REFUTED-REPLAYED count (need ≥2): 2

**Acceptance → FAIL** (replayed 2/4, need ≥2)

## smt_check.py run


## smt_check.py acceptance run

  (encoder: lean)
- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615} [enc:lean]
  (encoder: lean)
- `SmtAcc.McallMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=15152151881707510024, sp=#xd24741db5bf15908), SL_lo=0} [enc:lean]
  (encoder: lean)
- `SmtAcc.McallPresence` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=136, sp=#x0000000000000088), SL_lo=0} [enc:lean]
  (encoder: lean)
- `SmtAcc.BinArmMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=15152151881707510024, sp=#xd24741db5bf15908), SL_lo=0} [enc:lean]
  (encoder: python)
- `IoWriteMined.IoWriteInvCandidate` → **VALID-IN-FRAGMENT** [enc:python]
  (encoder: python)
- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT** [enc:python]
  (encoder: lean)
- `SmtAcc.CurMemExt` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `SmtAcc.AmdHeadroom` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

### Acceptance verdicts
- a_headroom: REFUTED-REPLAYED
- b_memext: REFUTED-REPLAYED
- b_presence: REFUTED-REPLAYED
- c_binarm: REFUTED-REPLAYED
- d_io_write_loop.lean: VALID-IN-FRAGMENT
- d_budget: VALID-IN-FRAGMENT
- e_memext: VALID-IN-FRAGMENT
- e_headroom: VALID-IN-FRAGMENT
- REFUTED-REPLAYED count (need ≥2): 4

**Acceptance → PASS** (replayed 4/4, need ≥2)

## smt_check.py run

  (encoder: lean)
- `NovelResidA` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {base=#x75346575757572ba), base_n=8445486756382732986} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidB` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidC` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC0` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC2` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC3` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC4` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC5` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC6` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {mq_val=(_ as-array k!35))} [enc:lean]
  (encoder: lean)
- `GateC7` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC8` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {m0_val=(lambda ((x!1 Int)), mq_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC9` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC0` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC2` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC3` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC4` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC5` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC6` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {mq_val=(_ as-array k!35))} [enc:lean]
  (encoder: lean)
- `GateC7` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC8` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {m0_val=(lambda ((x!1 Int)), mq_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC9` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC3` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC4` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC5` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC6` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {mq_val=(_ as-array k!35))} [enc:lean]
  (encoder: lean)
- `GateC7` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int)), mq_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC9` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC3` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC4` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC5` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC6` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC7` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC9` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC3` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC4` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC5` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC6` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC7` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC9` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC0` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {mq_def=(_ as-array k!40)), m0_val=(lambda ((x!1 Int)), m0_def=(_ as-array k!41)), mq_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC3` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC4` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC5` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC6` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC7` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC9` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC3` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC4` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC5` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC6` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC7` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC9` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GG` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC3` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC4` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC5` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC6` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC7` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC9` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC3` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC4` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC5` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC6` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {mq_val=(_ as-array k!35))} [enc:lean]
  (encoder: lean)
- `GateC7` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int)), mq_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC9` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC3` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC4` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC5` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC6` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC7` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC9` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {mq_def=(_ as-array k!40)), m0_val=(lambda ((x!1 Int)), m0_def=(_ as-array k!41)), mq_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC3` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC4` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC5` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC6` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC7` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC9` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]

## smt_check.py run


## smt_check.py acceptance run

  (encoder: lean)
- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615} [enc:lean]
  (encoder: lean)
- `SmtAcc.McallMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=15152151881707510024, sp=#xd24741db5bf15908), SL_lo=0} [enc:lean]
  (encoder: lean)
- `SmtAcc.McallPresence` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=136, sp=#x0000000000000088), SL_lo=0} [enc:lean]
  (encoder: lean)
- `SmtAcc.BinArmMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=15152151881707510024, sp=#xd24741db5bf15908), SL_lo=0} [enc:lean]
  (encoder: python)
- `IoWriteMined.IoWriteInvCandidate` → **VALID-IN-FRAGMENT** [enc:python]
  (encoder: python)
- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT** [enc:python]
  (encoder: lean)
- `SmtAcc.CurMemExt` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `SmtAcc.AmdHeadroom` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

### Acceptance verdicts
- a_headroom: REFUTED-REPLAYED
- b_memext: REFUTED-REPLAYED
- b_presence: REFUTED-REPLAYED
- c_binarm: REFUTED-REPLAYED
- d_io_write_loop.lean: VALID-IN-FRAGMENT
- d_budget: VALID-IN-FRAGMENT
- e_memext: VALID-IN-FRAGMENT
- e_headroom: VALID-IN-FRAGMENT
- REFUTED-REPLAYED count (need ≥2): 4

**Acceptance → PASS** (replayed 4/4, need ≥2)

## smt_check.py run

  (encoder: lean)
- `NovelResidA` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {base=#x75346575757572ba), base_n=8445486756382732986} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidB` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidC` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {m0_val=(lambda ((x!1 Int))} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidC` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {m0_val=(lambda ((x!1 Int))} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidC` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidA` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {base=#x75346575757572ba), base_n=8445486756382732986} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidB` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidC` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
  (encoder: lean)
  (encoder: lean)
  (encoder: lean)
  (encoder: lean)
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
  (encoder: lean)
  (encoder: lean)
  (encoder: lean)
  (encoder: lean)
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC3` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC4` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC5` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC6` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC7` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC9` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC3` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC4` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC5` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC6` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {mq_val=(_ as-array k!35))} [enc:lean]
  (encoder: lean)
- `GateC7` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int)), mq_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC9` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC3` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC4` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC5` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC6` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC7` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC9` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {mq_def=(_ as-array k!40)), m0_val=(lambda ((x!1 Int)), m0_def=(_ as-array k!41)), mq_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC3` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC4` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC5` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC6` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC7` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC9` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]

## smt_check.py run


## smt_check.py acceptance run

  (encoder: lean)
- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615} [enc:lean]
  (encoder: lean)
- `SmtAcc.McallMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=15152151881707510024, sp=#xd24741db5bf15908), SL_lo=0} [enc:lean]
  (encoder: lean)
- `SmtAcc.McallPresence` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=136, sp=#x0000000000000088), SL_lo=0} [enc:lean]
  (encoder: lean)
- `SmtAcc.BinArmMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=15152151881707510024, sp=#xd24741db5bf15908), SL_lo=0} [enc:lean]
  (encoder: python)
- `IoWriteMined.IoWriteInvCandidate` → **VALID-IN-FRAGMENT** [enc:python]
  (encoder: python)
- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT** [enc:python]
  (encoder: lean)
- `SmtAcc.CurMemExt` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `SmtAcc.AmdHeadroom` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

### Acceptance verdicts
- a_headroom: REFUTED-REPLAYED
- b_memext: REFUTED-REPLAYED
- b_presence: REFUTED-REPLAYED
- c_binarm: REFUTED-REPLAYED
- d_io_write_loop.lean: VALID-IN-FRAGMENT
- d_budget: VALID-IN-FRAGMENT
- e_memext: VALID-IN-FRAGMENT
- e_headroom: VALID-IN-FRAGMENT
- REFUTED-REPLAYED count (need ≥2): 4

**Acceptance → PASS** (replayed 4/4, need ≥2)

## smt_check.py run


## smt_check.py acceptance run

  (encoder: lean)
- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615} [enc:lean]
  (encoder: lean)
- `SmtAcc.McallMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=15152151881707510024, sp=#xd24741db5bf15908), SL_lo=0} [enc:lean]
  (encoder: lean)
- `SmtAcc.McallPresence` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=136, sp=#x0000000000000088), SL_lo=0} [enc:lean]
  (encoder: lean)
- `SmtAcc.BinArmMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=15152151881707510024, sp=#xd24741db5bf15908), SL_lo=0} [enc:lean]
  (encoder: python)
- `IoWriteMined.IoWriteInvCandidate` → **VALID-IN-FRAGMENT** [enc:python]
  (encoder: python)
- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT** [enc:python]
  (encoder: lean)
- `SmtAcc.CurMemExt` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `SmtAcc.AmdHeadroom` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

### Acceptance verdicts
- a_headroom: REFUTED-REPLAYED
- b_memext: REFUTED-REPLAYED
- b_presence: REFUTED-REPLAYED
- c_binarm: REFUTED-REPLAYED
- d_io_write_loop.lean: VALID-IN-FRAGMENT
- d_budget: VALID-IN-FRAGMENT
- e_memext: VALID-IN-FRAGMENT
- e_headroom: VALID-IN-FRAGMENT
- REFUTED-REPLAYED count (need ≥2): 4

**Acceptance → PASS** (replayed 4/4, need ≥2)

## smt_check.py run

  (encoder: lean)
- `NovelResidA` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {base=#x75346575757572ba), base_n=8445486756382732986} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidB` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `NovelResidC` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC0` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC1` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC2` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int)), mq_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC3` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC4` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC5` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {m0_def=(_ as-array k!38)), m0_val=(_ as-array k!39))} [enc:lean]
  (encoder: lean)
- `GateC6` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int)), mq_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC7` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `GateC8` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {} [enc:lean]
  (encoder: lean)
- `GateC9` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]
  (encoder: lean)
- `GateC10` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {m0_val=(lambda ((x!1 Int))} [enc:lean]
  (encoder: lean)
- `GateC11` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `FbTest` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `FreshTriWin` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {m0_val=(lambda ((x!1 Int)), mq_val=(lambda ((x!1 Int))} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `FreshTriWinT` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `FreshValDemand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptA.AcceptNegPre` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.AcceptMcallPre` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.AcceptMemExtPre` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_hi=0, sp=#xffeffffffff7fffb), op_True=false), SL_lo=0, sp_n=18442240474081656827} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptA.CegisCand` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_lo=0, SL_hi=0, sp=#xffffffffffffffff), sp_n=18446744073709551615, op_True=false)} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_hi=0, op_True=false), sp=#xffeffffffff7fffb), SL_lo=0, sp_n=18442240474081656827} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptA.CegisCand` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptA.CegisCand` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_lo=0, SL_hi=0, sp=#xffffffffffffffff), sp_n=18446744073709551615, op_True=false)} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_hi=0, op_True=false), sp=#xffeffffffff7fffb), SL_lo=0, sp_n=18442240474081656827} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_lo=0, SL_hi=0, sp=#xffffffffffffffff), sp_n=18446744073709551615, op_True=false)} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_hi=0, op_True=false), sp=#xffeffffffff7fffb), SL_lo=0, sp_n=18442240474081656827} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptA.CegisCand` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_lo=0, SL_hi=0, sp=#xffffffffffffffff), sp_n=18446744073709551615, op_True=false)} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_hi=0, op_True=false), sp=#xffeffffffff7fffb), SL_lo=0, sp_n=18442240474081656827} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run


## smt_check.py acceptance run

  (encoder: lean)
- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615} [enc:lean]
  (encoder: lean)
- `SmtAcc.McallMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=15152151881707510024, sp=#xd24741db5bf15908), SL_lo=0} [enc:lean]
  (encoder: lean)
- `SmtAcc.McallPresence` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=136, sp=#x0000000000000088), SL_lo=0} [enc:lean]
  (encoder: lean)
- `SmtAcc.BinArmMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=15152151881707510024, sp=#xd24741db5bf15908), SL_lo=0} [enc:lean]
  (encoder: python)
- `IoWriteMined.IoWriteInvCandidate` → **VALID-IN-FRAGMENT** [enc:python]
  (encoder: python)
- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT** [enc:python]
  (encoder: lean)
- `SmtAcc.CurMemExt` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `SmtAcc.AmdHeadroom` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

### Acceptance verdicts
- a_headroom: REFUTED-REPLAYED
- b_memext: REFUTED-REPLAYED
- b_presence: REFUTED-REPLAYED
- c_binarm: REFUTED-REPLAYED
- d_io_write_loop.lean: VALID-IN-FRAGMENT
- d_budget: VALID-IN-FRAGMENT
- e_memext: VALID-IN-FRAGMENT
- e_headroom: VALID-IN-FRAGMENT
- REFUTED-REPLAYED count (need ≥2): 4

**Acceptance → PASS** (replayed 4/4, need ≥2)

## smt_check.py run

  (dump path unavailable for CegisLive.CegisCand: dump-encode-gap — falling back to Python encoder)
- `CegisLive.CegisCand` → **ENCODE-GAP** (unencodable atom; hyps=['(and (<= (+ SL_lo 3264) sp_n) (<= sp_n SL_hi) (= (mod sp_n 16) 0))'] concl=None)

## smt_check.py run

  (encoder: lean)
- `CegisAcceptA.CegisCand` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_lo=0, SL_hi=0, sp=#xffffffffffffffff), sp_n=18446744073709551615, op_True=false)} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_hi=0, op_True=false), sp=#xffeffffffff7fffb), SL_lo=0, sp_n=18442240474081656827} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptA.CegisCand` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_lo=0, SL_hi=0, sp=#xffffffffffffffff), sp_n=18446744073709551615, op_True=false)} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_hi=0, op_True=false), sp=#xffeffffffff7fffb), SL_lo=0, sp_n=18442240474081656827} [enc:lean]

## smt_check.py run

- `JointFix.TargetD` → **JOINTLY-INHABITABLE-MODULO-OPAQUE** — witness {SL_hi=0, x13slot=0, slotAddr=0, sp=#xd874fd7ffdf7fdfe), SL_lo=15597370135654427902, sp_n=15597370135654432254}; 3 enc / 1 opaque conjunct(s)

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run


### producer-check (POST) `JointFix.TargetA`
  - `SL.lo + 4352 ≤ sp.toNat` → **HOLDS** (post ⇒ conjunct)
  - `(∃ b, m0[slotAddr]? = some b)` → **HOLDS** (post ⇒ conjunct)
  - `(∀ (a : Nat), sp.toNat - 1120 ≤ a → a < sp.toNat → ∃ b, mcall[a]? = so…` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, sp_n=18446744073709551615, x13slot=0, slotAddr=0, sp=#xffffffffffffffff), SL_lo=18446744073709547263}
  - `(∃ w, mcall[x13slot]? = some w)` → **MODULO-OPAQUE** (conjunct unencodable)

## smt_check.py run


### producer-check (POST) `JointFix.TargetA`
  - `SL.lo + 4352 ≤ sp.toNat` → **HOLDS** (post ⇒ conjunct)
  - `(∃ b, m0[slotAddr]? = some b)` → **HOLDS** (post ⇒ conjunct)
  - `(∀ (a : Nat), sp.toNat - 1120 ≤ a → a < sp.toNat → ∃ b, mcall[a]? = so…` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, sp_n=18446744073709551615, x13slot=0, slotAddr=0, sp=#xffffffffffffffff), SL_lo=18446744073709547263}
  - `(∃ w, mcall[x13slot]? = some w)` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, slotAddr=0, x13slot=0, sp=#xffffffffffffffff), SL_lo=18446744073709547263, sp_n=18446744073709551615}

## smt_check.py run


### consumer-check `JointFix.TargetC`
  - demand `∃ w, mcall[x13slot]? = some w` → **CONSUMER-FAILS** — structure too weak; CTI {SL_hi=0, slotAddr=0, x13slot=0, sp=#x00c382874a020a04), SL_lo=55031138032417028, sp_n=55031138032421380}

## smt_check.py run


## smt_check.py JOINT acceptance run


### producer-check (POST) `JointFix.TargetA`
  - `SL.lo + 4352 ≤ sp.toNat` → **HOLDS** (post ⇒ conjunct)
  - `(∃ b, m0[slotAddr]? = some b)` → **HOLDS** (post ⇒ conjunct)
  - `(∀ (a : Nat), sp.toNat - 1120 ≤ a → a < sp.toNat → ∃ b, mcall[a]? = so…` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, sp_n=18446744073709551615, x13slot=0, slotAddr=0, sp=#xffffffffffffffff), SL_lo=18446744073709547263}
  - `(∃ w, mcall[x13slot]? = some w)` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, slotAddr=0, x13slot=0, sp=#xffffffffffffffff), SL_lo=18446744073709547263, sp_n=18446744073709551615}

### producer-check (POST) `JointFix.TargetB`
  - `SL.lo + 4352 ≤ sp.toNat` → **HOLDS** (post ⇒ conjunct)
  - `(∃ b, m0[slotAddr]? = some b)` → **HOLDS** (post ⇒ conjunct)
  - `(∀ (a : Nat), SL.lo ≤ a → a < sp.toNat → ∃ b, m0[a]? = some b)` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, SL_lo=0, sp=#xfffffffdffffffff), sp_n=18446744065119617023, slotAddr=0}

### consumer-check `JointFix.TargetC`
  - demand `∃ w, mcall[x13slot]? = some w` → **CONSUMER-FAILS** — structure too weak; CTI {SL_hi=0, slotAddr=0, x13slot=0, sp=#x00c382874a020a04), SL_lo=55031138032417028, sp_n=55031138032421380}
- `JointFix.TargetD` → **JOINTLY-INHABITABLE** — witness {SL_hi=0, slotAddr=0, x13slot=0, sp=#xfffffffdffffffff), SL_lo=18446744065119612671, sp_n=18446744065119617023}; 4 enc / 0 opaque conjunct(s)

### producer-check (POST) `JointFix.TargetD`
  - `SL.lo + 4352 ≤ sp.toNat` → **HOLDS** (post ⇒ conjunct)
  - `(∃ b, m0[slotAddr]? = some b)` → **HOLDS** (post ⇒ conjunct)
  - `(∀ (a : Nat), sp.toNat - 1120 ≤ a → a < sp.toNat → ∃ b, mcall[a]? = so…` → **HOLDS** (post ⇒ conjunct)
  - `(∃ w, mcall[x13slot]? = some w)` → **HOLDS** (post ⇒ conjunct)

### consumer-check `JointFix.TargetD`
  - demand `∃ w, mcall[x13slot]? = some w` → **SATISFIED** (structure ⇒ demand)

### JOINT acceptance table
- (a) PASS
- (b) PASS
- (c) PASS
- (d) PASS

**Joint acceptance → PASS**

## smt_check.py run


## smt_check.py acceptance run

  (encoder: lean)
- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615} [enc:lean]
  (encoder: lean)
- `SmtAcc.McallMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=15152151881707510024, sp=#xd24741db5bf15908), SL_lo=0} [enc:lean]
  (encoder: lean)
- `SmtAcc.McallPresence` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=136, sp=#x0000000000000088), SL_lo=0} [enc:lean]
  (encoder: lean)
- `SmtAcc.BinArmMemExt` → **REFUTED-REPLAYED** — axioms=Classical.choice, Quot.sound, propext | model {SL_hi=0, sp_n=15152151881707510024, sp=#xd24741db5bf15908), SL_lo=0} [enc:lean]
  (encoder: python)
- `IoWriteMined.IoWriteInvCandidate` → **VALID-IN-FRAGMENT** [enc:python]
  (encoder: python)
- `SmtAcc.BudgetLadderOk` → **VALID-IN-FRAGMENT** [enc:python]
  (encoder: lean)
- `SmtAcc.CurMemExt` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]
  (encoder: lean)
- `SmtAcc.AmdHeadroom` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

### Acceptance verdicts
- a_headroom: REFUTED-REPLAYED
- b_memext: REFUTED-REPLAYED
- b_presence: REFUTED-REPLAYED
- c_binarm: REFUTED-REPLAYED
- d_io_write_loop.lean: VALID-IN-FRAGMENT
- d_budget: VALID-IN-FRAGMENT
- e_memext: VALID-IN-FRAGMENT
- e_headroom: VALID-IN-FRAGMENT
- REFUTED-REPLAYED count (need ≥2): 4

**Acceptance → PASS** (replayed 4/4, need ≥2)

## smt_check.py run

  (encoder: lean)
- `LiveExtras.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {slotAddr=0, x13slot=0, SL_hi=18446744073709551600, sp_n=18446744073709551600, sp=#xfffffffffffffff0), SL_lo=18446744073709548336} [enc:lean]

## smt_check.py run


### consumer-check `LiveExtras.CegisCand`
  - demand `∃ w, mcall[x13slot]? = some w` → **SATISFIED** (structure ⇒ demand)

## smt_check.py run


### consumer-check `JointFix.TargetC`
  - demand `∃ w, mcall[x13slot]? = some w` → **CONSUMER-FAILS** — structure too weak; CTI {SL_hi=0, slotAddr=0, x13slot=0, sp=#x00c382874a020a04), SL_lo=55031138032417028, sp_n=55031138032421380}

## smt_check.py run


## smt_check.py JOINT acceptance run


### producer-check (POST) `JointFix.TargetA`
  - `SL.lo + 4352 ≤ sp.toNat` → **HOLDS** (post ⇒ conjunct)
  - `(∃ b, m0[slotAddr]? = some b)` → **HOLDS** (post ⇒ conjunct)
  - `(∀ (a : Nat), sp.toNat - 1120 ≤ a → a < sp.toNat → ∃ b, mcall[a]? = so…` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, sp_n=18446744073709551615, x13slot=0, slotAddr=0, sp=#xffffffffffffffff), SL_lo=18446744073709547263}
  - `(∃ w, mcall[x13slot]? = some w)` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, slotAddr=0, x13slot=0, sp=#xffffffffffffffff), SL_lo=18446744073709547263, sp_n=18446744073709551615}

### producer-check (POST) `JointFix.TargetB`
  - `SL.lo + 4352 ≤ sp.toNat` → **HOLDS** (post ⇒ conjunct)
  - `(∃ b, m0[slotAddr]? = some b)` → **HOLDS** (post ⇒ conjunct)
  - `(∀ (a : Nat), SL.lo ≤ a → a < sp.toNat → ∃ b, m0[a]? = some b)` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, SL_lo=0, sp=#xfffffffdffffffff), sp_n=18446744065119617023, slotAddr=0}

### consumer-check `JointFix.TargetC`
  - demand `∃ w, mcall[x13slot]? = some w` → **CONSUMER-FAILS** — structure too weak; CTI {SL_hi=0, slotAddr=0, x13slot=0, sp=#x00c382874a020a04), SL_lo=55031138032417028, sp_n=55031138032421380}
- `JointFix.TargetD` → **JOINTLY-INHABITABLE** — witness {SL_hi=0, slotAddr=0, x13slot=0, sp=#xfffffffdffffffff), SL_lo=18446744065119612671, sp_n=18446744065119617023}; 4 enc / 0 opaque conjunct(s)

### producer-check (POST) `JointFix.TargetD`
  - `SL.lo + 4352 ≤ sp.toNat` → **HOLDS** (post ⇒ conjunct)
  - `(∃ b, m0[slotAddr]? = some b)` → **HOLDS** (post ⇒ conjunct)
  - `(∀ (a : Nat), sp.toNat - 1120 ≤ a → a < sp.toNat → ∃ b, mcall[a]? = so…` → **HOLDS** (post ⇒ conjunct)
  - `(∃ w, mcall[x13slot]? = some w)` → **HOLDS** (post ⇒ conjunct)

### consumer-check `JointFix.TargetD`
  - demand `∃ w, mcall[x13slot]? = some w` → **SATISFIED** (structure ⇒ demand)

### JOINT acceptance table
- (a) PASS
- (b) PASS
- (c) PASS
- (d) PASS

**Joint acceptance → PASS**

## smt_check.py run

  (encoder: lean)
- `CegisAcceptA.CegisCand` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_lo=0, SL_hi=0, sp=#xffffffffffffffff), sp_n=18446744073709551615, op_True=false)} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_hi=0, op_True=false), sp=#xffeffffffff7fffb), SL_lo=0, sp_n=18442240474081656827} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run


### producer-check (APPROX-TRACE) `JointFix.TargetA`
  - `SL.lo + 4352 ≤ sp.toNat` → **HOLDS** (post ⇒ conjunct)
  - `(∃ b, m0[slotAddr]? = some b)` → **HOLDS** (post ⇒ conjunct)
  - `(∀ (a : Nat), sp.toNat - 1120 ≤ a → a < sp.toNat → ∃ b, mcall[a]? = so…` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, sp_n=18446744073709551615, x13slot=0, slotAddr=0, sp=#xffffffffffffffff), SL_lo=18446744073709547263}
  - `(∃ w, mcall[x13slot]? = some w)` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, slotAddr=0, x13slot=0, sp=#xffffffffffffffff), SL_lo=18446744073709547263, sp_n=18446744073709551615}

## smt_check.py run


## smt_check.py JOINT acceptance run


### producer-check (POST) `JointFix.TargetA`
  - `SL.lo + 4352 ≤ sp.toNat` → **HOLDS** (post ⇒ conjunct)
  - `(∃ b, m0[slotAddr]? = some b)` → **HOLDS** (post ⇒ conjunct)
  - `(∀ (a : Nat), sp.toNat - 1120 ≤ a → a < sp.toNat → ∃ b, mcall[a]? = so…` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, sp_n=18446744073709551615, x13slot=0, slotAddr=0, sp=#xffffffffffffffff), SL_lo=18446744073709547263}
  - `(∃ w, mcall[x13slot]? = some w)` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, slotAddr=0, x13slot=0, sp=#xffffffffffffffff), SL_lo=18446744073709547263, sp_n=18446744073709551615}

### producer-check (POST) `JointFix.TargetB`
  - `SL.lo + 4352 ≤ sp.toNat` → **HOLDS** (post ⇒ conjunct)
  - `(∃ b, m0[slotAddr]? = some b)` → **HOLDS** (post ⇒ conjunct)
  - `(∀ (a : Nat), SL.lo ≤ a → a < sp.toNat → ∃ b, m0[a]? = some b)` → **PRODUCER-FAILS** — post does NOT supply it; CTI {SL_hi=0, SL_lo=0, sp=#xfffffffdffffffff), sp_n=18446744065119617023, slotAddr=0}

### consumer-check `JointFix.TargetC`
  - demand `∃ w, mcall[x13slot]? = some w` → **CONSUMER-FAILS** — structure too weak; CTI {SL_hi=0, slotAddr=0, x13slot=0, sp=#x00c382874a020a04), SL_lo=55031138032417028, sp_n=55031138032421380}
- `JointFix.TargetD` → **JOINTLY-INHABITABLE** — witness {SL_hi=0, slotAddr=0, x13slot=0, sp=#xfffffffdffffffff), SL_lo=18446744065119612671, sp_n=18446744065119617023}; 4 enc / 0 opaque conjunct(s)

### producer-check (POST) `JointFix.TargetD`
  - `SL.lo + 4352 ≤ sp.toNat` → **HOLDS** (post ⇒ conjunct)
  - `(∃ b, m0[slotAddr]? = some b)` → **HOLDS** (post ⇒ conjunct)
  - `(∀ (a : Nat), sp.toNat - 1120 ≤ a → a < sp.toNat → ∃ b, mcall[a]? = so…` → **HOLDS** (post ⇒ conjunct)
  - `(∃ w, mcall[x13slot]? = some w)` → **HOLDS** (post ⇒ conjunct)

### consumer-check `JointFix.TargetD`
  - demand `∃ w, mcall[x13slot]? = some w` → **SATISFIED** (structure ⇒ demand)

### JOINT acceptance table
- (a) PASS
- (b) PASS
- (c) PASS
- (d) PASS

**Joint acceptance → PASS**

## smt_check.py run

  (encoder: lean)
- `CegisAcceptA.CegisCand` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_lo=0, SL_hi=0, sp=#xffffffffffffffff), sp_n=18446744073709551615, op_True=false)} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_hi=0, op_True=false), sp=#xffeffffffff7fffb), SL_lo=0, sp_n=18442240474081656827} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptA.CegisCand` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_lo=0, SL_hi=0, sp=#xffffffffffffffff), sp_n=18446744073709551615, op_True=false)} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_hi=0, op_True=false), sp=#xffeffffffff7fffb), SL_lo=0, sp_n=18442240474081656827} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptA.CegisCand` → **NOT-REFUTED / VALID-IN-FRAGMENT** (unsat) [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_lo=0, SL_hi=0, sp=#xffffffffffffffff), sp_n=18446744073709551615, op_True=false)} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptB.CegisCand` → **REFUTED-MODULO-OPAQUE** — model touches opaque ['True']; not auto-replayed | model {SL_hi=0, op_True=false), sp=#xffeffffffff7fffb), SL_lo=0, sp_n=18442240474081656827} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

  (encoder: lean)
- `CegisAcceptC.CegisCand` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplayProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, sp=#xffffffffffffffff), SL_lo=0} [enc:lean]

## smt_check.py run

- `InvGen_crux.minedRecur` → **UNKNOWN-OPAQUE** (all 1 conjuncts opaque/unencodable; opaque=[])

## smt_check.py run

- `InvGen_cruxRelations.minedRecur` → **UNKNOWN-OPAQUE** (all 2 conjuncts opaque/unencodable; opaque=[])

## smt_check.py run

- `InvGen_cruxRelations.minedLadder` → **ENCODE-GAP** (unencodable atom; hyps=[] concl=None)

## smt_check.py run

  (dump path unavailable for Vsa.Sim.ExprResid: dump-error: /Users/kirancodes/Documents/code/verified-semantic-abstraction/experiments/logs/tmpxuozgd9y.lean:479:119: error(lean.unknownIdentifier): Unknown constant `Vsa.Sim.ExprResid` — falling back to Python encoder)
- `Vsa.Sim.ExprResid` → **ENCODE-GAP** (unencodable atom; hyps=[None] concl=None)

## smt_check.py run

  (dump path unavailable for Vsa.Sim.Rows.VarLeafResid: dump-encode-gap — falling back to Python encoder)
- `Vsa.Sim.Rows.VarLeafResid` → **ENCODE-GAP** (unencodable atom; hyps=[None] concl=None)

## smt_check.py run

- `SExprField` → **ENCODE-GAP** (unencodable atom; hyps=[] concl=None)

## smt_check.py run

- `SRetField` → **ENCODE-GAP** (unencodable atom; hyps=[] concl=None)
