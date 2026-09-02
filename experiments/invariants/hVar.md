# hVar — mined invariant candidate (invgen.py)

- cluster: `env-seam`  entry: `0x80003434`
- target field: `TermResidualsCore.hVar`
- verdict: **candidate-mined+SURVIVED**

## Mined conjuncts (T1-T5)

```
# mine — 29 events in 1 segments, vocab=['a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'ra', 's0', 's1', 's2', 'sp']

== MINED CANDIDATE CONJUNCTS (intersection across segments) ==
  * T1 m0b1 : per-call constant
  * T1 m0b2 : per-call constant
  * T1 m0b3 : per-call constant
  * T2 m0b0 = m0b1 + 1   (entry offset)
  * T2 m0b0 = m0b2 + 1   (entry offset)
  * T2 m0b0 = m0b3 + 1   (entry offset)
  * T2 m0b1 = m0b0 + -1   (entry offset)
  * T2 m0b1 = m0b2 + m0b3   (entry linear)
  * T2 m0b2 = m0b0 + -1   (entry offset)
  * T2 m0b2 = m0b1 + m0b3   (entry linear)
  * T2 m0b3 = m0b0 + -1   (entry offset)
  * T2 m0b3 = m0b1 + m0b2   (entry linear)
  * T5 m0b1 = 0x0   (mem-window constant / slot pin)
  * T5 m0b2 = 0x0   (mem-window constant / slot pin)
  * T5 m0b3 = 0x0   (mem-window constant / slot pin)

```

## Relational (machine×spec) conjuncts

```
# mine_relational — hVar (stmt side)

machine dispatch events: 29   spec events: 103

kind | name     | machine cnt | spec cnt | agree
-----+----------+-------------+----------+------
   0 | expr     |         13  |      13  | YES
   1 | varDecl  |          9  |       9  | YES
   2 | block    |          5  |       5  | YES
   4 | whileStmt |          1  |       1  | YES
   6 | ret      |          1  |       0  | no

== MINED RELATIONAL CONJUNCTS (per-seam ordinal alignment) ==
  * read32[node] & 0xff = 0 = kindOfStmt (.expr)  [machine 13 = spec 13]  MATCH
  * read32[node] & 0xff = 1 = kindOfStmt (.varDecl)  [machine 9 = spec 9]  MATCH
  * read32[node] & 0xff = 2 = kindOfStmt (.block)  [machine 5 = spec 5]  MATCH
  * read32[node] & 0xff = 4 = kindOfStmt (.whileStmt)  [machine 1 = spec 1]  MATCH

== KIND-COUNT DIVERGENCE (informational; likely call-opacity) ==
  ~ ret: machine 1 vs spec 0

== SUMMARY ==
kinds agreeing (machine==spec count): ['expr', 'varDecl', 'block', 'whileStmt']
VERDICT: candidate-mined

```
