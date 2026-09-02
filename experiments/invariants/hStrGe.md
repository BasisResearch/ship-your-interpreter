# hStrGe — mined invariant candidate (invgen.py)

- cluster: `loop-arm`  entry: `0x800034e8`
- target field: `TermResidualsCore.hStrGe`
- verdict: **candidate-mined+SURVIVED**

## Mined conjuncts (T1-T5)

```
# mine — 100 events in 1 segments, vocab=['a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7', 'ra', 's0', 's1', 's2', 's3', 's5', 's7', 'sp']

== MINED CANDIDATE CONJUNCTS (intersection across segments) ==
  * T1 m0b1 : per-call constant
  * T1 m0b2 : per-call constant
  * T1 m0b3 : per-call constant
  * T2 m0b0 = m0b1 + 9   (entry offset)
  * T2 m0b0 = m0b2 + 9   (entry offset)
  * T2 m0b0 = m0b3 + 9   (entry offset)
  * T2 m0b1 = m0b0 + -9   (entry offset)
  * T2 m0b1 = m0b2 + m0b3   (entry linear)
  * T2 m0b2 = m0b0 + -9   (entry offset)
  * T2 m0b2 = m0b1 + m0b3   (entry linear)
  * T2 m0b3 = m0b0 + -9   (entry offset)
  * T2 m0b3 = m0b1 + m0b2   (entry linear)
  * T5 m0b1 = 0x0   (mem-window constant / slot pin)
  * T5 m0b2 = 0x0   (mem-window constant / slot pin)
  * T5 m0b3 = 0x0   (mem-window constant / slot pin)

```

## Relational (machine×spec) conjuncts

```
# mine_relational — hStrGe (expr side)

machine dispatch events: 100   spec events: 112

kind | name     | machine cnt | spec cnt | agree
-----+----------+-------------+----------+------
   0 | int      |         39  |      39  | YES
   1 | str      |          4  |       4  | YES
   2 | bool     |          4  |       4  | YES
   4 | var      |         12  |      12  | YES
   6 | binary   |         21  |      21  | YES
   7 | logical  |          4  |       4  | YES
   8 | unary    |          4  |       4  | YES
   9 | call     |         12  |      12  | YES

== MINED RELATIONAL CONJUNCTS (per-seam ordinal alignment) ==
  * read32[node] & 0xff = 0 = kindOfExpr (.int)  [machine 39 = spec 39]  MATCH
  * read32[node] & 0xff = 1 = kindOfExpr (.str)  [machine 4 = spec 4]  MATCH
  * read32[node] & 0xff = 2 = kindOfExpr (.bool)  [machine 4 = spec 4]  MATCH
  * read32[node] & 0xff = 4 = kindOfExpr (.var)  [machine 12 = spec 12]  MATCH
  * read32[node] & 0xff = 6 = kindOfExpr (.binary)  [machine 21 = spec 21]  MATCH
  * read32[node] & 0xff = 7 = kindOfExpr (.logical)  [machine 4 = spec 4]  MATCH
  * read32[node] & 0xff = 8 = kindOfExpr (.unary)  [machine 4 = spec 4]  MATCH
  * read32[node] & 0xff = 9 = kindOfExpr (.call)  [machine 12 = spec 12]  MATCH

== SUMMARY ==
kinds agreeing (machine==spec count): ['int', 'str', 'bool', 'var', 'binary', 'logical', 'unary', 'call']
VERDICT: candidate-mined

```
