
## smt_check.py run

- `SmtAcc.HeadroomBad` → **REFUTED-REPLAYED** — (axiom-free) | model {SL_hi=0, sp=#xffffffffffffffff), SL_lo=18446744073709548352, sp_n=18446744073709551615}

## smt_check.py run


## smt_check.py run

- `SmtAcc.BinArmMemExt` → **ENCODE-GAP** (unencodable atom; hyps=['(forall ((m_def (Array Int Bool)) (m_val (Array Int (_ BitVec 8)))) (forall ((a Int)) (=> (not (and (<= SL_lo a) (< a sp_n))) (and (= (select m_def a) (select m0_def a)) (= (select m_val a) (select m0_val a))))))'] concl=None)

## smt_check.py run

- `SmtAcc.BinArmMemExt` → **ENCODING-GAP** — Z3 SAT but Lean replay FAILED — translator bug: 'SmtReplay.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] | model {SL_hi=0, sp_n=18446744073709551615, SL_lo=0, sp=#xffffffffffffffff)}
