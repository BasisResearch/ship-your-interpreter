
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
