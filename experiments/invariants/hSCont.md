# hSCont — mined invariant candidate (invgen.py)

- cluster: `leaf-slot`  entry: `0x800040b8`
- target field: `TermResidualsCore.hSCont`
- verdict: **candidate-mined+SURVIVED**

## Mined conjuncts (T1-T5)

```
# mine — 636 events in 1 segments, vocab=['a0', 'ra', 's0', 's1', 's2', 's3', 'sp']

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
# mine_relational — hSCont (stmt side)

machine dispatch events: 636   spec events: 2425

kind | name     | machine cnt | spec cnt | agree
-----+----------+-------------+----------+------
   0 | expr     |        195  |     195  | YES
   1 | varDecl  |          9  |       9  | YES
   2 | block    |        174  |     174  | YES
   3 | ifStmt   |        201  |     201  | YES
   4 | whileStmt |          6  |       6  | YES
   7 | brk      |          1  |       1  | YES
   8 | cont     |         50  |      50  | YES

== MINED RELATIONAL CONJUNCTS (per-seam ordinal alignment) ==
  * read32[node] & 0xff = 0 = kindOfStmt (.expr)  [machine 195 = spec 195]  MATCH
  * read32[node] & 0xff = 1 = kindOfStmt (.varDecl)  [machine 9 = spec 9]  MATCH
  * read32[node] & 0xff = 2 = kindOfStmt (.block)  [machine 174 = spec 174]  MATCH
  * read32[node] & 0xff = 3 = kindOfStmt (.ifStmt)  [machine 201 = spec 201]  MATCH
  * read32[node] & 0xff = 4 = kindOfStmt (.whileStmt)  [machine 6 = spec 6]  MATCH
  * read32[node] & 0xff = 7 = kindOfStmt (.brk)  [machine 1 = spec 1]  MATCH
  * read32[node] & 0xff = 8 = kindOfStmt (.cont)  [machine 50 = spec 50]  MATCH
  * dispatch tag 8 -> armPC 0x800040b8  (SlotPinned 8 0x800040b8)  [arm-entry hits 0]

== SUMMARY ==
kinds agreeing (machine==spec count): ['expr', 'varDecl', 'block', 'ifStmt', 'whileStmt', 'brk', 'cont']
VERDICT: candidate-mined

```
