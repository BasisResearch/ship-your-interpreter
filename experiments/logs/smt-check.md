
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
